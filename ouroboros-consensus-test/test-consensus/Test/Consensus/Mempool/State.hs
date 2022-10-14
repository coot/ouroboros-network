{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -Wno-partial-fields -Wno-incomplete-record-updates -Wno-orphans #-}

module Test.Consensus.Mempool.State where

import Control.Monad.Trans.Reader
import Data.IORef
import Data.Proxy (Proxy (..))

import Ouroboros.Consensus.Ledger.Basics
import Ouroboros.Consensus.Ledger.SupportsMempool
import Ouroboros.Consensus.Ledger.SupportsProtocol
import Ouroboros.Consensus.Mempool

import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.StateMachine
import Test.StateMachine.Types (
  History(..), HistoryEvent(..),
  ParallelCommandsF(..), ParallelCommands, Command(..), Commands(..), Pair(..))

import Cardano.Slotting.Time

import Test.Consensus.Mempool.State.Model
import Test.Consensus.Mempool.State.SUT
import Test.Consensus.Mempool.State.Types
import Test.Consensus.Mempool.Block

import qualified Data.List.NonEmpty as NE
import Cardano.Slotting.Slot
import Data.List (sort, intercalate)
import Ouroboros.Consensus.Storage.LedgerDB.HD (extendSeqUtxoDiff)
import Data.Foldable
import Ouroboros.Network.Block (pointSlot)
import NoThunks.Class
import GHC.Generics (Generic)
import Test.Util.TestBlock hiding (TestBlock)
import Control.Monad.Except (throwError)
import Ouroboros.Consensus.HardFork.History (defaultEraParams)
import Ouroboros.Consensus.Config.SecurityParam (SecurityParam(..))
import qualified Data.Map.Strict as Map
import qualified Ouroboros.Consensus.Storage.LedgerDB.HD as HD
import Control.Monad (foldM)
import Data.Maybe (fromJust)
import qualified Ouroboros.Consensus.Util.MonadSTM.RAWLock as RAWLock
import Debug.Trace
import Control.Monad.IO.Class (MonadIO(liftIO))

import Text.Layout.Table

{-------------------------------------------------------------------------------
  Generation
-------------------------------------------------------------------------------}

genListOfStates :: SlotNo
                  -> LedgerState TestBlock ValuesMK
                  -> Gen [(SlotNo, LedgerState TestBlock DiffMK)]
genListOfStates anchorSlot firstState = do
  slots <- listOf1 (fmap SlotNo $ arbitrary `suchThat` (> unSlotNo anchorSlot))
  traceM $ show slots
  valueChangelog <- snd <$> foldM (\(lastValues, acc) s ->  do
                                      nextValues <- nextRandomState lastValues
                                      let diffed = nextValues `withLedgerTables` zipLedgerTables (\a b -> rawForgetValues $ rawCalculateDifference a b) (projectLedgerTables lastValues) (projectLedgerTables nextValues)
                                      pure (nextValues, (withOrigin' $ getTipSlot nextValues, diffed):acc)) (firstState, []) (sort slots)
  pure $ reverse valueChangelog

foo st mch = pure $ GetSnapshotFor st mch

thd (_, _, c) = c

generator ::
  ( Arbitrary (GenTx TestBlock)
  , TableStuff (LedgerState TestBlock)
  )
  => LedgerConfig TestBlock
  -> Model TestBlock Symbolic
  -> Maybe (Gen (Action TestBlock Symbolic))
generator lcfg = \case
  NeedsInit -> Just $ Init <$> initialState
  model     -> Just $ frequency $
   [ (2, fmap TryAddTxs $ listOf $ oneof
         [ arbitrary
         , TestGenTx <$> genSucceedingTransaction (mockTip (modelBackingStore model) `withLedgerTables` thd (NE.last (mockTables (modelBackingStore model)))) <*> fmap TestTxId arbitrary
         ])
   , (1, pure GetSnapshot)
   , (1, do
         let (anchorSlot, anchorSt, anchorValues) = NE.head $ mockTables $ modelBackingStore model
             pds = anchorSt { payloadDependentState  = UTxTok anchorValues $ utxhist $ payloadDependentState anchorSt }
             --     ^ This cannot be mockTip? it has to be mockAnchor, but I don't have that one hmm
         valueChangelog <- genListOfStates anchorSlot pds
         let mch = MempoolChangelog (At anchorSlot) $ foldl' (\acc (s, d) -> zipLedgerTables (f s) acc (projectLedgerTables d) ) polyEmptyLedgerTables valueChangelog
         let tip = snd (last valueChangelog)
         let st = applyChainTick lcfg ((+1) . withOrigin' . pointSlot $ getTip tip) (forgetLedgerTables tip)
         foo st mch)
   , (1, do
         case modelNextSync model of
           Nothing -> do
             let (anchorSlot, anchorSt, anchorValues) = NE.head $ mockTables $ modelBackingStore model
                 pds = anchorSt { payloadDependentState  = UTxTok anchorValues $ utxhist $ payloadDependentState anchorSt }
             valueChangelog <- genListOfStates anchorSlot pds
             pure $ UnsyncTip (forgetLedgerTables $ snd (last valueChangelog)) $ fromJust $ NE.nonEmpty $ map (\(s, st) -> (s, forgetLedgerTables st, projectLedgerTables st))  valueChangelog
           Just m -> do
             let (anchorSlot, anchorSt, anchorValues) = NE.head $ mockTables m
                 pds = anchorSt { payloadDependentState  = UTxTok anchorValues $ utxhist $ payloadDependentState anchorSt }
             valueChangelog <- genListOfStates anchorSlot pds
             pure $ UnsyncTip (forgetLedgerTables $ snd (last valueChangelog)) $ fromJust $ NE.nonEmpty $ map (\(s, st) -> (s, forgetLedgerTables st, projectLedgerTables st))  valueChangelog
     )
   , (1, case modelNextSync model of
         Nothing -> UnsyncAnchor   <$> (arbitrary `suchThat` (< fromIntegral (NE.length (mockTables (modelBackingStore model)))))
         Just nx -> UnsyncAnchor   <$> (arbitrary `suchThat` (< fromIntegral (NE.length (mockTables nx)))))
   , (1, pure SyncLedger)
   ]
   where

     f :: Ord k => SlotNo -> SeqDiffMK k v -> DiffMK k v -> SeqDiffMK k v
     f sl (ApplySeqDiffMK sq) (ApplyDiffMK d) = ApplySeqDiffMK $ extendSeqUtxoDiff sq sl d

rawForgetValues :: TrackingMK k v -> DiffMK k v
rawForgetValues (ApplyTrackingMK _ d) = ApplyDiffMK d

-- TODO: @js fill this shrinker
shrinker :: Model blk Symbolic -> Action blk Symbolic -> [Action blk Symbolic]
shrinker _ _ = []

preconditions :: Model blk Symbolic -> Action blk Symbolic -> Logic
-- When need init, only init
preconditions NeedsInit Init{} = Top
preconditions NeedsInit _      = Bot
-- Do not re-init
preconditions Model{}   Init{} = Bot
preconditions Model{}   _      = Top

-- TODO: @js Add postconditions
postconditions :: p -> p1 -> p2 -> Logic
postconditions _ _ _ = Top

sm :: ( LedgerSupportsMempool TestBlock
      , LedgerSupportsProtocol TestBlock
      , HasTxId (GenTx TestBlock)
      , SufficientSerializationForAnyBackingStore (LedgerState TestBlock)
      --  Can I use the test block with payload for this?
      , Eq (GenTx TestBlock)
      )
   => LedgerConfig TestBlock
   -> Bool
   -> StateMachine (Model TestBlock) (Action TestBlock) (ReaderT (IORef (Mempool IO TestBlock TicketNo, TestLedgerDB IO TestBlock, RAWLock.RAWLock IO ())) IO) (Response TestBlock)
sm cfg trc =
  StateMachine
    initModel
    (transitions cfg)
    preconditions
    postconditions
    Nothing
    (generator cfg)
    shrinker
    (semantics cfg trc)
    (mock cfg)
    noCleanup

prop_mempoolParallel :: ( LedgerSupportsMempool TestBlock
      , LedgerSupportsProtocol TestBlock
      , HasTxId (GenTx TestBlock)
      , SufficientSerializationForAnyBackingStore (LedgerState TestBlock)
      ) => Proxy TestBlock -> LedgerConfig TestBlock -> Bool -> Property
prop_mempoolParallel _ lcfg trc = forAllParallelCommands (sm lcfg trc) Nothing $ \cmds ->
    monadic (\p   -> counterexample (treeDraw cmds) $ ioProperty $ do
                -- putStrLn $ treeDraw cmds
                ref <- newIORef undefined
                flip runReaderT ref p
            )
            (runParallelCommandsNTimes 100 (sm lcfg trc) cmds >>= prettyParallelCommands cmds)

treeDraw :: Show (cmd Symbolic) => ParallelCommandsF Pair cmd resp -> String
treeDraw (ParallelCommands prefix suffixes) =
  "TEST CASE\nPrefix\n" ++ (unlines $ map ('\t':) $ lines (tableString [def]
    unicodeRoundS
    def
    (map (\(Command c _ _) -> rowG [head $ words $ show c]) (unCommands prefix))
  )) ++ "\nParallel suffix\n" ++ (unlines $ map ('\t':) $ lines (tableString [def, def]
    unicodeRoundS
    def
    (map (\(Pair p1 p2) -> rowG [ f p1
                                , f p2]) suffixes)))

  where f (Commands cs) = intercalate "," $ map (\(Command c _ _) -> head $ words $ show c) cs

prop_mempoolSequential :: ( LedgerSupportsMempool TestBlock
      , LedgerSupportsProtocol TestBlock
      , HasTxId (GenTx TestBlock)
      , SufficientSerializationForAnyBackingStore (LedgerState TestBlock)
      ) => Proxy TestBlock -> LedgerConfig TestBlock -> Bool -> Property
prop_mempoolSequential _ lcfg trc = forAllCommands (sm lcfg trc) Nothing $ \cmds ->
    monadic (\p   -> ioProperty $ do
                ref <- newIORef undefined
                flip runReaderT ref p
            )
    (do
        let sm' = sm lcfg trc
        (History hist, _model, res) <- runCommands sm' cmds
        case res of
          Ok -> pure ()
          _ -> do
            liftIO $ do
              print res
              putStrLn $ unlines [ head $ words $ show c | (_, Invocation c _)<- hist  ]
              error "STOP")


prop :: Bool -> IO ()
prop = quickCheck . prop_mempoolParallel (Proxy @TestBlock) (defaultEraParams (SecurityParam 2) (slotLengthFromSec 2))

prop' :: Bool -> IO ()
prop' = quickCheck . prop_mempoolSequential (Proxy @TestBlock) (defaultEraParams (SecurityParam 2) (slotLengthFromSec 2))

instance NoThunks (TickedLedgerState TestBlock TrackingMK)

instance Show (MempoolChangelog TestBlock) where
  show (MempoolChangelog a tbs) = "MempoolChangelog " <> show a -- <> " " <> showsLedgerState sMapKind tbs ""
instance IsApplyMapKind mk => Show (TickedLedgerState TestBlock mk) where
  show (TickedTestLedger (TestLedger lap pds) ) = unwords [
    "Ticked"
    , "LedgerState"
    , show lap
--    , showsLedgerState sMapKind (utxtoktables pds) ""
    ]


instance Arbitrary (GenTx TestBlock) where
  arbitrary = TestGenTx <$> (Tx <$> arbitrary <*> arbitrary) <*> fmap TestTxId arbitrary

instance Arbitrary (LedgerState TestBlock mk) => Arbitrary (TickedLedgerState TestBlock mk) where
  arbitrary = TickedTestLedger <$> arbitrary

type instance ApplyTxErr TestBlock = TxErr

instance HasTxId (GenTx TestBlock) where
  txId (TestGenTx _ t) = t

instance Show (ApplyTxErr TestBlock) => LedgerSupportsMempool TestBlock where
  applyTx _ _ _ (TestGenTx tx txid) (TickedTestLedger st@TestLedger{..}) =
    case applyPayload payloadDependentState tx of
        Left err  -> throwError err
        Right st' -> return     $ (,TestValidatedTx tx txid)
                                $ TickedTestLedger
                                $ st {
                                   payloadDependentState = st'
                                  }
  reapplyTx cfg s tx st = fmap fst $ applyTx cfg DoNotIntervene s (txForgetValidated tx) st
  txForgetValidated (TestValidatedTx tx txid) = TestGenTx tx txid

  getTransactionKeySets (TestGenTx tx _) = getPayloadKeySets tx
  txsMaxBytes = const 1
  txInBlockSize = const 1


data instance GenTx TestBlock = TestGenTx Tx (GenTxId TestBlock)
  deriving (Generic, NoThunks, Show, Eq)

data instance Validated (GenTx TestBlock) = TestValidatedTx Tx (GenTxId TestBlock)
  deriving (Generic, NoThunks, Show)

newtype instance TxId (GenTx TestBlock) = TestTxId Word
  deriving (Generic, NoThunks, Show, Ord, Eq)

instance Show (PayloadDependentState Tx mk) where
  show = const "PDS"
