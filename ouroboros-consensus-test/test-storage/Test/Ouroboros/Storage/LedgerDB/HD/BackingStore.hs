{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE DisambiguateRecordFields   #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Ouroboros.Storage.LedgerDB.HD.BackingStore (
    operations
  , showLabelledExamples
  , tests
  ) where

import           Prelude hiding (minimum)

import           Control.Monad
import           Control.Monad.Catch (MonadMask)
import qualified Control.Monad.Class.MonadSTM as STM
import           Control.Monad.Except hiding (lift)
import           Control.Monad.State hiding (lift)
import           Control.Tracer (nullTracer)
import           Data.Bifunctor
import           Data.Foldable (toList)
import           Data.Functor.Classes
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromJust, mapMaybe)
import           Data.Sequence.NonEmpty (NESeq (..))
import qualified Data.Sequence.NonEmpty as NESeq
import qualified Data.Set as Set
import           GHC.Generics (Generic)
import qualified System.Directory as Dir
import           System.IO.Temp (createTempDirectory)
import           System.Random hiding (next)

import           Cardano.Binary (FromCBOR (..), ToCBOR (..))

import           Test.QuickCheck (Gen)
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Monadic as QC
import qualified Test.QuickCheck.Random as QC
import           Test.StateMachine hiding (showLabelledExamples)
import qualified Test.StateMachine.Labelling as Label
import qualified Test.StateMachine.Types as QSM
import qualified Test.StateMachine.Types.Rank2 as Rank2
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.QuickCheck (testProperty)

import           Ouroboros.Consensus.Block
import           Ouroboros.Consensus.Ledger.Abstract
import           Ouroboros.Consensus.Ledger.Basics ()
import           Ouroboros.Consensus.Storage.FS.API hiding (Handle)
import           Ouroboros.Consensus.Storage.FS.API.Types hiding (Handle)
import           Ouroboros.Consensus.Storage.FS.IO (monadIOHasFS)
import qualified Ouroboros.Consensus.Storage.LedgerDB.HD.BackingStore as BS
import qualified Ouroboros.Consensus.Storage.LedgerDB.HD.DiffSeq as DS
import qualified Ouroboros.Consensus.Storage.LedgerDB.HD.LMDB as LMDB
import           Ouroboros.Consensus.Storage.LedgerDB.OnDisk
import           Ouroboros.Consensus.Util (repeatedly)
import           Ouroboros.Consensus.Util.IOLike hiding (MonadMask (..))

import           Test.Util.Orphans.Slotting.Arbitrary ()
import           Test.Util.Orphans.ToExpr ()
import           Test.Util.TestLedgerState

{------------------------------------------------------------------------------
  Top-level test tree
------------------------------------------------------------------------------}

tests :: TestTree
tests = testGroup "BackingStore" [
    testProperty "InMemory" $ prop_sequential InMemoryBackingStore
  , testProperty "LMDB" $ prop_sequential (LMDBBackingStore testLMDBLimits)
  ]

-- FIXME(jdral): this is specific to the LMDB backing store, but we use it in
-- the precondition. Instead, we should make the precondition parameterised like
-- we did by using @'Operations'@.
maxOpenValueHandles :: Int
maxOpenValueHandles = 16

testLMDBLimits :: LMDB.LMDBLimits
testLMDBLimits = LMDB.LMDBLimits
  { -- 100 MiB should be more than sufficient for the tests we're running here.
    -- If the database were to grow beyond 100 Mebibytes, resulting in a test
    -- error, then something in the LMDB backing store or tests has changed and
    -- we should reconsider this value.
    LMDB.lmdbMapSize = 100 * 1024 * 1024
    -- 3 internal databases: 1 for the settings, 1 for the state, and 1 for the
    -- ledger tables.
  , LMDB.lmdbMaxDatabases = 3
  , LMDB.lmdbMaxReaders = maxOpenValueHandles
  }

{------------------------------------------------------------------------------
  Mock of a @'BackingStore'@: Types
------------------------------------------------------------------------------}

data Mock values = Mock {
    backingValues :: values
  , backingSeqNo  :: WithOrigin SlotNo
  , copies        :: [BS.BackingStorePath]
  , isClosed      :: Bool
  , valueHandles  :: Map MockHandle (MockValueReader values)
  , next          :: MockHandle
  }
  deriving stock (Show, Generic)

data MockValueReader values = MockValueReader {
    vhIsClosed :: Bool
  , values     :: values
  , seqNo      :: WithOrigin SlotNo
  }
  deriving stock (Show, Eq, Generic)

newtype MockHandle = MockHandle Int
  deriving stock (Show, Eq, Ord)
  deriving newtype Num

-- | An empty mock state.
emptyMock :: Operations keys values diff -> Mock values
emptyMock ops = Mock {
    backingValues = emptyValues ops
  , backingSeqNo  = Origin
  , copies        = []
  , isClosed      = False
  , valueHandles  = Map.empty
  , next          = 0
  }

data MockErr values =
    MockErrBackingStoreClosed
  | MockErrCopyPathAlreadyExists BS.BackingStorePath
  | MockErrNoMonotonicSeqNo (WithOrigin SlotNo) (WithOrigin SlotNo)
  | MockErrBSVHClosed MockHandle (Map MockHandle (MockValueReader values))
  | MockErrBSVHDoesNotExist MockHandle (Map MockHandle (MockValueReader values))
  deriving stock (Show, Eq)

-- | State within which the mock runs.
newtype MockState values a =
    MockState (ExceptT (MockErr values) (State (Mock values)) a)
  deriving stock Functor
  deriving newtype ( Applicative, Monad
                   , MonadState (Mock values), MonadError (MockErr values)
                   )

runMockState ::
     MockState values a
  -> Mock values
  -> (Either (MockErr values) a, Mock values)
runMockState (MockState t) = runState (runExceptT t)

-- | Dictionary of functions on keys, values and diffs.
--
-- Since the mock is parameterised over keys, values and diffs, we must pass in
-- a dictionary of functions that defines how values of these types interact.
-- Example: @'applyDiff'@ defines how to apply a @diff@ to @values@.
data Operations keys values diff = Operations {
    applyDiff        :: values -> diff -> values
  , emptyValues      :: values
  , lookupKeysRange  :: Maybe keys -> Int -> values -> values
  , lookupKeys       :: keys -> values -> values
  , genDiff          :: Model values Symbolic -> Gen diff
  , genRangeQuery    :: Model values Symbolic -> Gen (BS.RangeQuery keys)
  , genKeys          :: Model values Symbolic -> Gen keys
  , valuesLength     :: values -> Int
  , shrinkDiff       :: Model values Symbolic -> diff -> [diff]
  , shrinkRangeQuery :: Model values Symbolic -> BS.RangeQuery keys -> [BS.RangeQuery keys]
  , shrinkKeys       :: Model values Symbolic -> keys -> [keys]
  }

{------------------------------------------------------------------------------
  Mock of a @'BackingStore'@: Mocked operations
------------------------------------------------------------------------------}

-- | Throw an error if the backing store has been closed, which prevents any
-- other operations from succeeding.
mGuardBSClosed :: MockState values ()
mGuardBSClosed = do
  closed <- gets isClosed
  when closed $
    throwError MockErrBackingStoreClosed

-- | Close the backing store.
mBSClose :: MockState values ()
mBSClose = do
  mGuardBSClosed
  modify (\m -> m {
      isClosed = True
    })

-- | Copy the contents of the backing store to the given path.
mBSCopy :: BS.BackingStorePath -> MockState values ()
mBSCopy bsp = do
  mGuardBSClosed
  cps <- gets copies
  when (bsp `elem` cps) $
    throwError $ MockErrCopyPathAlreadyExists bsp
  modify (\m -> m {
      copies = bsp : copies m
    })

-- | Open a new value handle, which captures the state of the backing store
-- at the time of opening the handle.
mBSValueHandle :: MockState values (WithOrigin SlotNo, MockHandle)
mBSValueHandle = do
  mGuardBSClosed
  vs <- gets backingValues
  seqNo <- gets backingSeqNo
  nxt <- gets next
  let
    vh = MockValueReader False vs seqNo
  modify (\m -> m {
      valueHandles = Map.insert nxt vh (valueHandles m)
    , next = nxt + 1
    })

  pure (seqNo, nxt)

-- | Write a diff to the backing store.
mBSWrite ::
     Operations keys values diff
  -> SlotNo
  -> diff
  -> MockState values ()
mBSWrite ops sl d = do
  mGuardBSClosed
  vs <- gets backingValues
  seqNo <- gets backingSeqNo
  when (seqNo > NotOrigin sl) $
    throwError $ MockErrNoMonotonicSeqNo seqNo (NotOrigin sl)
  modify (\m -> m {
      backingValues = applyDiff ops vs d
    , backingSeqNo = NotOrigin sl
    })

-- | Throw an error if the required backing store value handle has been closed.
mGuardBSVHClosed :: MockHandle -> MockState values (MockValueReader values)
mGuardBSVHClosed h = do
  vhs <- gets valueHandles
  let vhMay = Map.lookup h vhs
  case vhIsClosed <$> vhMay of
    Nothing    -> throwError $ MockErrBSVHDoesNotExist h vhs
    Just False -> pure $ fromJust vhMay
    Just True  -> throwError $ MockErrBSVHClosed h vhs

-- | Close a backing store value handle.
mBSVHClose :: MockHandle -> MockState values ()
mBSVHClose h = do
  mGuardBSClosed
  void $ mGuardBSVHClosed h
  vhs <- gets valueHandles
  modify (\m -> m {
    valueHandles = Map.adjust (\vh -> vh { vhIsClosed = True }) h vhs
  })

-- | Perform a range read on a backing store value handle.
mBSVHRangeRead ::
     Operations keys values diff
  -> MockHandle
  -> BS.RangeQuery keys
  -> MockState values values
mBSVHRangeRead ops h BS.RangeQuery{rqPrev, rqCount} = do
  mGuardBSClosed
  vh <- mGuardBSVHClosed h
  let
    vs = values vh
  pure $ lookupKeysRange ops rqPrev rqCount vs

-- | Perform a regular read on a backing store value handle
mBSVHRead ::
     Operations keys values diff
  -> MockHandle
  -> keys
  -> MockState values values
mBSVHRead ops h ks = do
  mGuardBSClosed
  vh <- mGuardBSVHClosed h
  let vs = values vh
  pure $ lookupKeys ops ks vs

{------------------------------------------------------------------------------
  Reification of the API
------------------------------------------------------------------------------}

-- | Commands parameterised over the type of handle.
data Cmd keys values diff h =
    BSClose
  | BSCopy BS.BackingStorePath
  | BSValueHandle
  | BSWrite SlotNo diff
  | BSVHClose h
  | BSVHRangeRead h (BS.RangeQuery keys)
  | BSVHRead h keys
  deriving stock (Show, Functor, Foldable, Traversable)

-- | Successful results parameterised over the type of handle.
data Success keys values diff h =
    Unit ()
  | SHandle (WithOrigin SlotNo) h
  | Values values
  deriving stock (Show, Eq, Foldable, Functor, Traversable)

-- | Responses parameterised over the type of handle.
newtype Resp keys values diff h =
    Resp (Either (MockErr values) (Success keys values diff h))
  deriving stock (Show, Eq, Foldable, Functor, Traversable)

{------------------------------------------------------------------------------
  Interpreting the mock
------------------------------------------------------------------------------}

mAPI ::
     Operations keys values diff
  -> Cmd keys values diff MockHandle
  -> MockState values (Success keys values diff MockHandle)
mAPI ops = \case
  BSClose            -> Unit <$> mBSClose
  BSCopy bsp         -> Unit <$> mBSCopy bsp
  BSValueHandle      -> uncurry SHandle <$> mBSValueHandle
  BSWrite sl d       -> Unit <$> mBSWrite ops sl d
  BSVHClose h        -> Unit <$> mBSVHClose h
  BSVHRangeRead h rq -> Values <$> mBSVHRangeRead ops h rq
  BSVHRead h ks      -> Values <$> mBSVHRead ops h ks

runMock ::
     Operations keys values diff
  -> Cmd keys values diff MockHandle
  -> Mock values
  -> ( Resp keys values diff MockHandle
     , Mock values
     )
runMock ops cmd = first Resp . runMockState (mAPI ops cmd)

{------------------------------------------------------------------------------
  Interpreting implementations
------------------------------------------------------------------------------}

newtype Handle = Handle Int
  deriving stock (Show, Eq, Ord)
  deriving newtype Num

runImpl ::
     Monad m
  => SomeHasFS m
  -> BackingStoreWithHandleRegistry m keys values diff
  -> Cmd keys values diff Handle
  -> m (Resp keys values diff Handle)
runImpl sfhs bs cmd = case cmd of
    BSClose            -> mkUnit    <$> bsClose bs
    BSCopy bsp         -> mkUnit    <$> bsCopy bs sfhs bsp
    BSValueHandle      -> mkSHandle <$> bsValueHandle bs
    BSWrite sl d       -> mkUnit    <$> bsWrite bs sl d
    BSVHClose h        -> mkUnit    <$> bsvhClose bs h
    BSVHRangeRead h rq -> mkValues  <$> bsvhRangeRead bs h rq
    BSVHRead h ks      -> mkValues  <$> bsvhRead bs h ks
  where
    mkUnit    = Resp . Right . Unit
    mkSHandle = Resp . Right . uncurry SHandle
    mkValues  = Resp . Right . Values

-- | A wrapper around a backing store that does bookkeeping of value handles.
--
-- The client of a backing store is responsible for keeping track of value
-- handles. To test backing stores here, we define a wrapper around backing
-- stores that should do the accounting.
data BackingStoreWithHandleRegistry m keys values diff =
  BackingStoreWithHandleRegistry {
      bsClose       :: !(m ())
    , bsCopy        :: !(SomeHasFS m -> BS.BackingStorePath -> m ())
    , bsValueHandle :: !(m (WithOrigin SlotNo, Handle))
    , bsWrite       :: !(SlotNo -> diff -> m ())
    , bsvhClose     :: !(Handle -> m ())
    , bsvhRangeRead :: !(Handle -> BS.RangeQuery keys -> m values)
    , bsvhRead      :: !(Handle -> keys -> m values)
    }

-- | Add a handle registry wrapper around a backing store.
--
-- The handle registry uses a @'TVar'@ to keep track of value handles.
withHandleRegistry ::
     forall m. MonadSTM m
  => forall keys values diff .
     BS.BackingStore m keys values diff
  -> m (BackingStoreWithHandleRegistry m keys values diff)
withHandleRegistry bs = do
    ref <- STM.newTVarIO Map.empty
    let
      bs' = BackingStoreWithHandleRegistry {
          bsClose       = BS.bsClose bs
        , bsCopy        = BS.bsCopy bs
        , bsValueHandle = BS.bsValueHandle bs
                          >>= mapM (registerHandle ref)
        , bsWrite       = BS.bsWrite bs
        , bsvhClose     = getHandle ref >=> BS.bsvhClose
        , bsvhRangeRead = \h rq -> getHandle ref h >>= flip BS.bsvhRangeRead rq
        , bsvhRead      = \h ks -> getHandle ref h >>= flip BS.bsvhRead ks
        }
    pure bs'
  where
    registerHandle ::
         STM.TVar m (Map Handle (BS.BackingStoreValueHandle m keys values))
      -> BS.BackingStoreValueHandle m keys values
      -> m Handle
    registerHandle ref bsvh = STM.atomically $ do
      vhs <- STM.readTVar ref
      let
        h    = maybe 0 ((+1) . fst) (Map.lookupMax vhs)
        vhs' = Map.insert h bsvh vhs
      STM.writeTVar ref vhs'
      pure h

    getHandle ::
         STM.TVar m (Map Handle (BS.BackingStoreValueHandle m keys values))
      -> Handle
      -> m (BS.BackingStoreValueHandle m keys values)
    getHandle ref h = STM.atomically $ do
      vhs <- STM.readTVar ref
      pure $ vhs Map.! h

{------------------------------------------------------------------------------
  References
------------------------------------------------------------------------------}

newtype At f r = At (f (Reference Handle r))
type    f :@ r = At f r

deriving instance Show (f (Reference Handle r)) => Show (At f r)

instance Functor f => Rank2.Functor (At f) where
  fmap = \f (At x) -> At $ fmap (lift f) x
    where
      lift :: (r x -> r' x) -> QSM.Reference x r -> QSM.Reference x r'
      lift f (QSM.Reference x) = QSM.Reference (f x)

instance Foldable f => Rank2.Foldable (At f) where
  foldMap = \f (At x) -> foldMap (lift f) x
    where
      lift :: (r x -> m) -> QSM.Reference x r -> m
      lift f (QSM.Reference x) = f x

instance Traversable t => Rank2.Traversable (At t) where
  traverse = \f (At x) -> At <$> traverse (lift f) x
    where
      lift :: Functor f
           => (r x -> f (r' x)) -> QSM.Reference x r -> f (QSM.Reference x r')
      lift f (QSM.Reference x) = QSM.Reference <$> f x

semantics ::
     IOLike m
  => SomeHasFS m
  -> BackingStoreWithHandleRegistry m keys values diff
  -> Cmd keys values diff :@ Concrete
  -> m (Resp keys values diff :@ Concrete)
semantics sfs bswhr (At c) = At . fmap reference <$>
  runImpl sfs bswhr (concrete <$> c)

{------------------------------------------------------------------------------
  Relating implementations
------------------------------------------------------------------------------}

type HandleRefs r = [(Reference Handle r, MockHandle)]

(!) :: Eq k => [(k, a)] -> k -> a
env ! r = fromJust (lookup r env)

data Model values r = Model (Mock values) (HandleRefs r)
  deriving stock Generic

deriving instance (Show (Mock values), Show1 r) => Show (Model values r)

initModel :: Operations keys values diff -> Model values r
initModel ops = Model (emptyMock ops) []

{------------------------------------------------------------------------------
  Stepping the model
------------------------------------------------------------------------------}

transition ::
     Eq1 r
  => Operations keys values diff
  -> Model values r
  -> Cmd keys values diff :@ r
  -> Resp keys values diff :@ r
  -> Model values r
transition ops m c = after . lockstep ops m c

toMock :: (Functor f, Eq1 r) => Model values r -> f :@ r -> f MockHandle
toMock (Model _ hs) (At fr) = (hs !) <$> fr

step ::
     Eq1 r
  => Operations keys values diff
  -> Model values r
  -> Cmd keys values diff :@ r
  -> (Resp keys values diff MockHandle, Mock values)
step ops m@(Model mock _) c = runMock ops (toMock m c) mock

data Event keys values diff r = Event {
    before   :: Model values r
  , cmd      :: Cmd keys values diff :@ r
  , after    :: Model values r
  , mockResp :: Resp keys values diff MockHandle
  }

lockstep ::
     Eq1 r
  => Operations keys values diff
  -> Model values r
  -> Cmd keys values diff :@ r
  -> Resp keys values diff :@ r
  -> Event keys values diff r
lockstep ops m@(Model _ hs) c (At resp) = Event {
      before = m
    , cmd = c
    , after = Model mock' (hs <> hs')
    , mockResp = resp'
    }
  where
    (resp', mock') = step ops m c
    hs' = zip (toList resp) (toList resp')

postcondition ::
     (Show values, Eq values)
  => Operations keys values diff
  -> Model values Concrete
  -> Cmd keys values diff :@ Concrete
  -> Resp keys values diff :@ Concrete
  -> Logic
postcondition ops m c r = toMock (after e) r .== mockResp e
  where
    e = lockstep ops m c r

{------------------------------------------------------------------------------
  Constructing symbolic responses
------------------------------------------------------------------------------}

symbolicResp ::
     Operations keys values diff
  -> Model values Symbolic
  -> Cmd keys values diff :@ Symbolic
  -> GenSym (Resp keys values diff :@ Symbolic)
symbolicResp ops m c = At <$> traverse (const genSym) resp
  where
    (resp, _mock') = step ops m c

{------------------------------------------------------------------------------
  Generating commands
------------------------------------------------------------------------------}

generator ::
     forall keys values diff.
     Operations keys values diff
  -> Model values Symbolic
  -> Maybe (Gen (Cmd keys values diff :@ Symbolic))
generator ops model@(Model mock hs) = Just $ QC.oneof $
      withoutHandle ++ withHandle
  where
    withoutHandle :: [Gen (Cmd keys values diff :@ Symbolic)]
    withoutHandle = fmap At <$> [
          pure BSClose
        , BSCopy <$> genBackingStorePath
        , pure BSValueHandle
        , BSWrite <$> genSlotNo <*> genDiff ops model
        ]

    withHandle :: [Gen (Cmd keys values diff :@ Symbolic)]
    withHandle
      | null hs   = []
      | otherwise = fmap At <$> [
            BSVHClose <$> genHandle
          , BSVHRangeRead <$> genHandle <*> genRangeQuery ops model
          , BSVHRead <$> genHandle <*> genKeys ops model
          ]

    genHandle :: Gen (Reference Handle Symbolic)
    genHandle = QC.elements (map fst hs)

    genBackingStorePath :: Gen BS.BackingStorePath
    genBackingStorePath = do
      file <- genBSPFile
      pure . BS.BackingStorePath . mkFsPath $ ["copies", file]

    genBSPFile :: Gen String
    genBSPFile = QC.elements ["a", "b", "c", "d"]

    genSlotNo :: Gen SlotNo
    genSlotNo = do
        n :: Int <- QC.choose (-5, 5)
        pure $ maybe 0 (+ fromIntegral n) (withOriginToMaybe seqNo)
      where
        seqNo = backingSeqNo mock

shrinker ::
     Operations keys values diff
  -> Model values Symbolic
  -> Cmd keys values diff :@ Symbolic
  -> [Cmd keys values diff :@ Symbolic]
shrinker ops model (At cmd) = case cmd of
  BSWrite sl d       ->
       [At $ BSWrite sl d'  | d' <- shrinkDiff ops model d]
    ++ [At $ BSWrite sl' d  | sl' <- QC.shrink sl]
  BSVHRangeRead h rq -> [At $ BSVHRangeRead h rq' | rq' <- shrinkRangeQuery ops model rq]
  BSVHRead h ks -> [At $ BSVHRead h ks' | ks' <- shrinkKeys ops model ks]
  _ -> []

{------------------------------------------------------------------------------
  Putting it all together
------------------------------------------------------------------------------}

sm ::
     ( IOLike m
     , Show values, Eq values)
  => Operations keys values diff
  -> SomeHasFS m
  -> BackingStoreWithHandleRegistry m keys values diff
  -> m ()
  -> StateMachine
        (Model values)
        (At (Cmd keys values diff))
        m
        (At (Resp keys values diff))
sm ops sfs bs cleanup = StateMachine {
      initModel     = initModel ops
    , transition    = transition ops
    , precondition  = precondition
    , postcondition = postcondition ops
    , invariant     = Nothing
    , generator     = generator ops
    , shrinker      = shrinker ops
    , semantics     = semantics sfs bs
    , mock          = symbolicResp ops
    , cleanup       = \_ -> do
        bsClose bs
        cleanup
    }

-- FIXME(jdral): This precondition currently only tests happy paths where
-- backing stores can not be closed, and we never try to read from closed value
-- handles. It may be useful to liberalise the precondition with respect to the
-- previous, such that we test more unhappy scenarios.
precondition ::
     Model values Symbolic
  -> Cmd keys values diff :@ Symbolic
  -> Logic
precondition (Model mock hs) (At c) =
      forall (toList c) (`member` map fst hs)
  .&& prec
  where
    prec = case c of
      BSClose           -> Boolean False
      BSCopy bsp        -> bsp `notMember` copies mock .&& canOpenReader
      BSWrite sl _      -> backingSeqNo mock .<= NotOrigin sl
      BSValueHandle     -> canOpenReader
      BSVHClose h       -> Boolean $ not (valueHandleIsClosed h)
      BSVHRangeRead h _ -> Boolean $ not (valueHandleIsClosed h)
      BSVHRead h _      -> Boolean $ not (valueHandleIsClosed h)

    canOpenReader         = Map.size openValueHandles .< maxOpenValueHandles
    openValueHandles      = Map.filter (not . vhIsClosed) (valueHandles mock)
    valueHandleIsClosed h = vhIsClosed $ valueHandles mock Map.! (hs ! h)

{------------------------------------------------------------------------------
  Running the tests
------------------------------------------------------------------------------}

prop_sequential :: BackingStoreSelector IO -> QC.Property
prop_sequential bss =
    forAllCommands (sm operations shfsUnused bsUnused cleanupUnused) Nothing $ \cmds ->
      QC.monadicIO $ do
        bsEnv <- QC.run $ setupBSEnv bss
        propCmds bsEnv cmds

data BSEnv m = BSEnv {
    bsSomeHasFS    :: SomeHasFS m
  , bsBackingStore :: BackingStoreWithHandleRegistry m K V D
  , bsCleanup      :: m ()
  }

setupBSEnv :: (MonadIO m, IOLike m) => BackingStoreSelector m -> m (BSEnv m)
setupBSEnv bss = do
  sysTmpDir <- liftIO Dir.getTemporaryDirectory
  qsmTmpDir <- liftIO $ createTempDirectory sysTmpDir "BS_QSM"

  bsSomeHasFS@(SomeHasFS hasFS) <-
    pure (SomeHasFS . monadIOHasFS . MountPoint $ qsmTmpDir)

  createDirectory hasFS (mkFsPath ["copies"])

  LedgerBackingStore bs <-
    newBackingStore
      nullTracer
      bss
      bsSomeHasFS
      polyEmptyLedgerTables

  bsBackingStore <- withHandleRegistry bs

  let bsCleanup = liftIO $ Dir.removeDirectoryRecursive qsmTmpDir

  pure BSEnv {bsSomeHasFS, bsBackingStore, bsCleanup}

propCmds ::
     (MonadIO m, IOLike m, MonadMask m)
  => BSEnv m
  -> QSM.Commands (At (Cmd K V D)) (At (Resp K V D))
  -> QC.PropertyM m ()
propCmds bsEnv cmds = do
  let sm' = sm operations (bsSomeHasFS bsEnv) (bsBackingStore bsEnv) (bsCleanup bsEnv)
  (hist, _model, res) <- runCommands sm' cmds
  prettyCommands sm' hist
    $ checkCommandNames cmds
    $ QC.tabulate "Tags" (map show $ tagEvents operations (execCmds operations cmds))
    $ res QC.=== Ok

bsUnused :: BackingStoreWithHandleRegistry IO K V D
bsUnused = error "Backing store not used during command generation"

shfsUnused :: SomeHasFS IO
shfsUnused = error "SomeHasFS not used during command generation"

cleanupUnused :: m ()
cleanupUnused = error "Cleanup not used during command generation"

operations :: Operations K V D
operations = Operations {
      applyDiff
    , emptyValues
    , lookupKeysRange = \prev n vs ->
        case prev of
          Nothing ->
            mapLedgerTables (rangeRead n) vs
          Just ks ->
            zipLedgerTables (rangeRead' n) ks vs
    , lookupKeys    = zipLedgerTables readKeys
    , genDiff
    , genRangeQuery
    , genKeys       = const QC.arbitrary
    , valuesLength
    , shrinkDiff
    , shrinkRangeQuery
    , shrinkKeys
    }
  where

    applyDiff :: V -> D -> V
    applyDiff = zipLedgerTables rawApplyDiffs

    emptyValues :: V
    emptyValues = polyEmptyLedgerTables

    rangeRead :: Int -> ValuesMK k v -> ValuesMK k v
    rangeRead n (ApplyValuesMK (DS.Values vs)) =
      ApplyValuesMK $ DS.Values $ Map.take n vs

    rangeRead' ::
         Ord k
      => Int
      -> KeysMK k v
      -> ValuesMK k v
      -> ValuesMK k v
    rangeRead' n ksmk vsmk =
        case Set.lookupMax ks of
          Nothing -> ApplyValuesMK $ DS.Values Map.empty
          Just  k -> ApplyValuesMK $ DS.Values $
            Map.take n $ snd $ Map.split k vs
      where
        ApplyKeysMK (DS.Keys ks)     = ksmk
        ApplyValuesMK (DS.Values vs) = vsmk

    readKeys ::
         Ord k
      => KeysMK k v
      -> ValuesMK k v
      -> ValuesMK k v
    readKeys (ApplyKeysMK ks) (ApplyValuesMK vs) =
      ApplyValuesMK $ DS.restrictValues vs ks

    -- FIXME: Generate unhappy paths, like
    -- * Delete key-value pairs that are not in the backing values.
    -- * Add key-value pairs that are already in the backing values.
    genDiff :: Model V Symbolic -> Gen D
    genDiff (Model mock _) = do
        d <- DS.diff vs <$> QC.arbitrary
        pure $ SimpleLedgerTables (ApplyDiffMK d)
      where
        SimpleLedgerTables (ApplyValuesMK vs) = backingValues mock

    genRangeQuery :: Model V Symbolic -> Gen (BS.RangeQuery K)
    genRangeQuery _ =
        BS.RangeQuery
          <$> (($) <$> QC.elements [const Nothing, Just] <*> QC.arbitrary)
          <*> (QC.getPositive <$> QC.arbitrary)

    valuesLength :: V -> Int
    valuesLength (SimpleLedgerTables (ApplyValuesMK (DS.Values m))) = Map.size m

    shrinkDiff :: Model V Symbolic -> D -> [D]
    shrinkDiff _ dmk = QC.shrink dmk

    shrinkRangeQuery :: Model V Symbolic -> BS.RangeQuery K -> [BS.RangeQuery K]
    shrinkRangeQuery _ (BS.RangeQuery ksMay n) =
          BS.RangeQuery
      <$> QC.shrink ksMay
      <*> (QC.getPositive <$> QC.shrink (QC.Positive n))

    shrinkKeys :: Model V Symbolic -> K -> [K]
    shrinkKeys _ ksmk = QC.shrink ksmk

type K = LedgerTables (SimpleLedgerState (Fixed Word) (Fixed Word)) KeysMK
type V = LedgerTables (SimpleLedgerState (Fixed Word) (Fixed Word)) ValuesMK
type D = LedgerTables (SimpleLedgerState (Fixed Word) (Fixed Word)) DiffMK

{------------------------------------------------------------------------------
  Arbitrary instances
------------------------------------------------------------------------------}

newtype Fixed a = Fixed a
  deriving newtype (Show, Eq, Ord)
  deriving newtype (NoThunks, ToCBOR, FromCBOR)

deriving via QC.Fixed a instance QC.Arbitrary a => QC.Arbitrary (Fixed a)

instance QC.Arbitrary v => QC.Arbitrary (DS.DiffEntry v) where
  arbitrary = do
    constr <- QC.elements [
        DS.Insert
      , DS.Delete
      , DS.UnsafeAntiInsert
      , DS.UnsafeAntiDelete
      ]
    constr <$> QC.arbitrary

instance QC.Arbitrary v => QC.Arbitrary (DS.NEDiffHistory v) where
  arbitrary = DS.NEDiffHistory <$> ((:<||) <$> QC.arbitrary <*> QC.arbitrary)
  shrink (DS.NEDiffHistory h) =
    fmap DS.NEDiffHistory $ mapMaybe NESeq.nonEmptySeq $ QC.shrink (NESeq.toSeq h)

deriving newtype instance (Ord k, QC.Arbitrary k, QC.Arbitrary v)
                       => QC.Arbitrary (DS.Values k v)

deriving newtype instance (Ord k, QC.Arbitrary k)
                       => QC.Arbitrary (DS.Keys k v)

deriving newtype instance (Ord k, QC.Arbitrary k, QC.Arbitrary v)
                       => QC.Arbitrary (DS.Diff k v)

instance (Ord k, QC.Arbitrary k)
      => QC.Arbitrary (KeysMK k v) where
  arbitrary = ApplyKeysMK <$> QC.arbitrary
  shrink (ApplyKeysMK ks) = ApplyKeysMK <$> QC.shrink ks

instance (Ord k, QC.Arbitrary k, QC.Arbitrary v)
      => QC.Arbitrary (DiffMK k v) where
  arbitrary = ApplyDiffMK <$> QC.arbitrary
  shrink (ApplyDiffMK d)= ApplyDiffMK <$> QC.shrink d

deriving newtype instance QC.Arbitrary (ApplyMapKind' mk k v)
                       => QC.Arbitrary (
                            LedgerTables
                              (SimpleLedgerState k v)
                              (ApplyMapKind' mk)
                            )

{------------------------------------------------------------------------------
  Labelling
------------------------------------------------------------------------------}

data Tag =
    SimpleWrite
  deriving (Show, Eq)

type EventPred keys values diff =
  Label.Predicate (Event keys values diff Symbolic) Tag

tagEvents ::
     forall keys values diff.
     Operations keys values diff
  -> [Event keys values diff Symbolic]
  -> [Tag]
tagEvents _ops = Label.classify [
      tagSimpleWrite
    ]
  where
    tagSimpleWrite :: EventPred keys values diff
    tagSimpleWrite = Label.predicate go
      where
        go ev = case (cmd ev, mockResp ev) of
          (At (BSWrite _ _), Resp (Right (Unit ()))) ->
            Left SimpleWrite
          _ ->
            Right tagSimpleWrite

execCmd ::
     Operations keys values diff
  -> Model values Symbolic
  -> QSM.Command (At (Cmd keys values diff)) (At (Resp keys values diff))
  -> Event keys values diff Symbolic
execCmd ops model (QSM.Command cmd resp _vars) =
    lockstep ops model cmd resp

execCmds ::
     forall keys values diff.
     Operations keys values diff
  -> QSM.Commands (At (Cmd keys values diff)) (At (Resp keys values diff))
  -> [Event keys values diff Symbolic]
execCmds ops = \(QSM.Commands cs) -> go (initModel ops) cs
  where
    go ::
         Model values Symbolic
      -> [QSM.Command (At (Cmd keys values diff)) (At (Resp keys values diff))]
      -> [Event keys values diff Symbolic]
    go _ []       = []
    go m (c : cs) = e : go (after e) cs
      where
        e = execCmd ops m c

{------------------------------------------------------------------------------
  Inspecting the labelling function
------------------------------------------------------------------------------}

showLabelledExamples :: Maybe Int -> IO ()
showLabelledExamples mReplay = do
    replaySeed <- case mReplay of
                    Nothing   -> getStdRandom $ randomR (1, 999999)
                    Just seed -> return seed

    putStrLn $ "Using replaySeed " ++ show replaySeed

    let args = QC.stdArgs {
            QC.maxSuccess = 10000
          , QC.replay     = Just (QC.mkQCGen replaySeed, 0)
          }

    QC.labelledExamplesWith args $
      forAllCommands (sm operations shfsUnused bsUnused cleanupUnused) Nothing $ \cmds ->
        repeatedly QC.collect (tagEvents operations . execCmds operations $ cmds) $
          QC.property True

{------------------------------------------------------------------------------
  Aux
------------------------------------------------------------------------------}

instance CommandNames (At (Cmd keys values diff)) where
  cmdName (At BSClose{})       = "BSClose"
  cmdName (At BSCopy{})        = "BSCopy"
  cmdName (At BSValueHandle{}) = "BSValueHandle"
  cmdName (At BSWrite{})       = "BSWrite"
  cmdName (At BSVHClose{})     = "BSVHClose"
  cmdName (At BSVHRangeRead{}) = "BSVHRangeRead"
  cmdName (At BSVHRead{})      = "BSVHRead"

  cmdNames _ = [
      "BSClose"
    , "BSCopy"
    , "BSValueHandle"
    , "BSWrite"
    , "BSVHClose"
    , "BSVHRangeRead"
    , "BSVHRead"
    ]

deriving newtype instance ToExpr Handle
deriving newtype instance ToExpr MockHandle
deriving anyclass instance ToExpr values => ToExpr (MockValueReader values)
deriving anyclass instance ToExpr values => ToExpr (Mock values)
deriving anyclass instance (ToExpr (r Handle), ToExpr values)
                        => ToExpr (Model values r)
deriving anyclass instance ToExpr FsPath
deriving newtype instance ToExpr BS.BackingStorePath
deriving newtype instance (ToExpr k, ToExpr v)
                       => (ToExpr (LedgerTables (SimpleLedgerState k v) ValuesMK))
deriving newtype instance ToExpr a => ToExpr (Fixed a)
