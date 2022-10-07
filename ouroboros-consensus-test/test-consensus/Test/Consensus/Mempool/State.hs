{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Test.Consensus.Mempool.State (sm) where

import           Control.Monad.Class.MonadSTM.Strict
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.State hiding (state)
import           Control.Tracer
import           Data.Foldable
import           Data.Kind
import           Data.Maybe (fromJust)
import           Data.Proxy

import           Cardano.Slotting.Slot

import           Ouroboros.Consensus.Ledger.Basics
import           Ouroboros.Consensus.Ledger.Extended
import           Ouroboros.Consensus.Ledger.SupportsMempool
import           Ouroboros.Consensus.Ledger.SupportsProtocol
import           Ouroboros.Consensus.Mempool
import           Ouroboros.Consensus.Mempool.TxSeq (TxSeq)
import qualified Ouroboros.Consensus.Mempool.TxSeq as TxSeq
import           Ouroboros.Consensus.Storage.LedgerDB.HD
import           Ouroboros.Consensus.Storage.LedgerDB.HD.BackingStore
import           Ouroboros.Consensus.Storage.LedgerDB.OnDisk
import           Ouroboros.Consensus.Util.IOLike

import           Ouroboros.Network.Block

import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import           Test.StateMachine

{-------------------------------------------------------------------------------
  Actions
-------------------------------------------------------------------------------}
data Action blk (r :: Type -> Type)
  = -- | Initialize the mempool and mock ledger DB with this state
    Init !(LedgerState blk ValuesMK)

  | -- | Try to add the given transactions into the mempool
    TryAddTxs ![GenTx blk]

  | -- | Perform a sync with the mock ledger DB
    SyncLedger

  | -- | Request a snapshot to the current mempool
    GetSnapshot

  | -- | Request a snapshot for a specific ledger state
    GetSnapshotFor
      !(TickedLedgerState blk ValuesMK)
      !Bool  -- ^ Should this command fail or should it succeed?

  | -- | Make the ledger go out of sync with the mempool by giving a new tip
    Unsync !(LedgerState blk ValuesMK)

deriving instance ( Show (LedgerState blk ValuesMK)
                  , Show (TickedLedgerState blk ValuesMK)
                  , Show (GenTx blk)
                  ) => Show (Action blk r)

{-------------------------------------------------------------------------------
  Response
-------------------------------------------------------------------------------}

data MempoolAddTxResultPlus blk =
    MempoolTxAddedPlus !(TxSeq.TxTicket (Validated (GenTx blk)))
  | MempoolTxRejectedPlus !(GenTx blk)

deriving instance ( Show (Validated (GenTx blk))
                  , Show (GenTx blk)
                  ) => Show (MempoolAddTxResultPlus blk)

data Response blk (r :: Type -> Type)
  = -- | Initialization was performed
    InitOk

  | -- | Transactions were pushed onto the mempool
    RespTryAddTxs
      !(TickedLedgerState blk ValuesMK) -- ^ The resulting ledger state after
                                        -- the transactions

      !TicketNo                         -- ^ The last ticket number

      ![MempoolAddTxResultPlus blk]     -- ^ The list of results of processing
                                        -- the transactions

      ![GenTx blk]                      -- ^ The list of transactions that
                                        -- couldn't be processed because of lack
                                        -- of space in the mempool

      !(Maybe [GenTx blk])              -- ^ If this had to trigger a resync,
                                        -- then these are the txs that were
                                        -- dropped by the resync

  | -- | A Sync was performed
    SyncOk
      !(TickedLedgerState blk ValuesMK) -- ^ The resulting ledger state after syncing
      ![GenTx blk]                      -- ^ The transactions that were dropped

  | -- | A snapshot was taken
    Snapshot
      ![(Validated (GenTx blk), TicketNo)] -- ^ The transactions in the snapshot

  | -- | A snapshot for a specific state was requested
    SnapshotFor
      !(Maybe [Validated (GenTx blk)]) -- ^ Nothing if the query fails,
                                       -- otherwise the list of valid
                                       -- transactions for the given ledger
                                       -- state
  | -- | An Unsync was performed
    UnsyncOk

deriving instance ( Show (TickedLedgerState blk ValuesMK)
                  , Show (Validated (GenTx blk))
                  , Show (GenTx blk)
                  ) => Show (Response blk r)

withOrigin' :: WithOrigin b -> b
withOrigin' = withOrigin undefined id

{-------------------------------------------------------------------------------
  Model
-------------------------------------------------------------------------------}

data Model blk (r :: Type -> Type) =
    -- | The model is yet to be initialized
    NeedsInit
  | -- | The model is initialized
    Model
      !(TxSeq (Validated (GenTx blk)))    -- ^ The current sequence of validated
                                          -- transactions

      !(TickedLedgerState blk ValuesMK)   -- ^ The ledger state after applying all
                                          -- the transactions

      !TicketNo                           -- ^ The next ticket

      !(Maybe (LedgerState blk ValuesMK)) -- ^ 'Just' holds the state we have to
                                          -- revalidate against

deriving instance ( Eq (TickedLedgerState blk ValuesMK)
                  , Eq (LedgerState blk ValuesMK)
                  , Eq (TxSeq (Validated (GenTx blk)))
                  ) => Eq (Model blk r)
deriving instance ( Show (TickedLedgerState blk ValuesMK)
                  , Show (LedgerState blk ValuesMK)
                  , Show (TxSeq (Validated (GenTx blk)))
                  ) => Show (Model blk r)

initModel :: Model blk r
initModel = NeedsInit

{-------------------------------------------------------------------------------
  Generation
-------------------------------------------------------------------------------}

generator :: ( Arbitrary (LedgerState blk ValuesMK)
             , Arbitrary (TickedLedgerState blk ValuesMK)
             , Arbitrary (GenTx blk)
             )
          => Model blk Symbolic
          -> Maybe (Gen (Action blk Symbolic))
generator NeedsInit = Just $ Init <$> arbitrary
generator (Model _ _ _ sync) = Just $ frequency $
   [ (2, TryAddTxs <$> arbitrary)
   , (1, pure GetSnapshot)
   , (1, do
         st <- arbitrary
         -- If we have to revalidate, then signal that this command should fail
         pure $ GetSnapshotFor st $ maybe True (const False) sync)
   , (1, Unsync <$> arbitrary)
   ]
   ++
   -- Don't try to sync if we don't have to sync
   maybe [] (const [(1, pure SyncLedger)]) sync

shrinker :: Model blk Symbolic -> Action blk Symbolic -> [Action blk Symbolic]
shrinker _ _ = []

preconditions :: Model blk Symbolic -> Action blk Symbolic -> Logic
-- When need init, only init
preconditions NeedsInit             Init{}     = Top
preconditions NeedsInit              _         = Bot
-- Do not re-init
preconditions Model{}               Init{}     = Bot
-- Do not try to sync if we don't need
preconditions (Model _ _ _ Nothing) SyncLedger = Bot
preconditions (Model _ _ _ _) _                = Top

{-------------------------------------------------------------------------------
  Model transition
-------------------------------------------------------------------------------}
transitions :: ( IsLedger (LedgerState blk)
               , TickedTableStuff (LedgerState blk)
               )
            => LedgerConfig blk
            -> Model blk r
            -> Action blk r
            -> Response blk r
            -> Model blk r
transitions cfg model cmd resp = case (model, cmd, resp) of
  (NeedsInit, Init st, _) ->
    let st' = tickSt cfg (succ $ withOrigin' (pointSlot $ getTip st)) st
    in Model TxSeq.Empty st' TxSeq.zeroTicketNo Nothing

  (Model txs _ tk _, SyncLedger, SyncOk st' _) -> Model txs st' tk Nothing

  (Model txs _ _ _, TryAddTxs _, RespTryAddTxs resState tk' processed _ _) ->
        let txs'' = foldl' (TxSeq.:>) txs [ tx | MempoolTxAddedPlus tx <- processed ]
        in Model txs'' resState tk' Nothing -- FIXME unsure about succ tk

  (Model txs st tk _, Unsync st', _) -> Model txs st tk (Just st')

  _ -> model

postconditions :: p -> p1 -> p2 -> Logic
postconditions _ _ _ = Top

{-------------------------------------------------------------------------------
  Model semantics
-------------------------------------------------------------------------------}
mock :: ( LedgerSupportsMempool blk )
     => LedgerConfig blk
     -> Model blk Symbolic
     -> Action blk Symbolic
     -> GenSym (Response blk Symbolic)
mock cfg model action = case (model, action) of

  (NeedsInit, Init _) -> pure InitOk

  (Model txs _ _ (Just st), SyncLedger) ->
    -- Sync with the ledger is achieved by ticking the state we have to resync
    -- with and then reapplying the transactions. This should not increment the
    -- ticket on the transactions.
    let st' = tickSt cfg (succ $ withOrigin' (pointSlot $ getTip st)) st
        (st'', processed) = foldTxs' cfg (st', []) [ txForgetValidated $ TxSeq.txTicketTx tx | tx <- TxSeq.toList txs ]
    in pure $ SyncOk st'' [ tx | MempoolTxRejected tx _ <- processed ]

  (m@(Model _ mstate tk toSync), TryAddTxs txs') -> do
    -- If we need to resync, perform a resync and store the result
    (st', removed) <- maybe (pure $ (mstate, Nothing))
                            (const $ (\case
                                         (SyncOk a b) -> (a, Just b)
                                         _ -> error "unreachable")
                              <$> mock cfg m SyncLedger)
                            toSync
    -- Trying to add transactions is just applying them while incrementing the ticket number
    -- TODO This doesn't account for capacity in the mempool
    let (tk', st'', processed, pending) = foldTxs cfg (tk, st', [], []) txs'
    pure $ RespTryAddTxs st'' tk' processed pending removed

  (Model txs _ _ _, GetSnapshot) ->
    pure $ Snapshot [ (TxSeq.txTicketTx tx, TxSeq.txTicketNo tx) | tx <- TxSeq.toList txs]

  (Model txs _ _ needsSync, GetSnapshotFor st' _) ->
    case needsSync of
      -- In this case it should fail
      Just{} -> pure $ SnapshotFor Nothing
      -- Here it should not fail but instead reapply all the transactions onto
      -- the given ledger state
      Nothing ->
        let (_, processed) = foldTxs' cfg (st', []) [ txForgetValidated $ TxSeq.txTicketTx tx | tx <- TxSeq.toList txs ]
        in pure $ SnapshotFor $ Just [ tx | MempoolTxAdded tx <- processed ]

  (Model{}, Unsync{}) -> pure UnsyncOk

  _ -> error "Unreachable!"

{-------------------------------------------------------------------------------
  Interfacing the ledger in the model
-------------------------------------------------------------------------------}
tickSt :: ( IsLedger (LedgerState blk)
          , TickedTableStuff (LedgerState blk)
          )
       => LedgerConfig blk
       -> SlotNo
       -> LedgerState blk ValuesMK
       -> TickedLedgerState blk ValuesMK
tickSt cfg s st = zipOverLedgerTablesTicked f st' (projectLedgerTables st)
  where
    st' = applyChainTick cfg s (forgetLedgerTables st)

    f :: Ord k => DiffMK k v -> ValuesMK k v -> ValuesMK k v
    f (ApplyDiffMK d) (ApplyValuesMK v) = ApplyValuesMK (forwardValues v d)

-- | Increments the ticket number on each valid transaction. More or less equivalent to 'fold extendVRNew'
foldTxs :: LedgerSupportsMempool blk
        => LedgerConfig blk
        -> ( TicketNo
           , TickedLedgerState blk ValuesMK
           , [MempoolAddTxResultPlus blk]
           , [GenTx blk]
           )
        -> [GenTx blk]
        -> ( TicketNo
           , TickedLedgerState blk ValuesMK
           , [MempoolAddTxResultPlus blk]
           , [GenTx blk]
           )
foldTxs _ st [] = st
foldTxs cfg (tk, st, processed, pending) (tx:txs) =
  case runExcept (applyTx cfg DoNotIntervene (withOrigin' $ pointSlot $ getTip st) tx st) of
    Left _ -> foldTxs cfg (tk, st, processed ++ [MempoolTxRejectedPlus tx], pending) txs
    Right (st', vtx) -> foldTxs cfg ( succ tk
                                    , forgetLedgerTablesDiffsTicked st'
                                    , processed ++ [MempoolTxAddedPlus (TxSeq.TxTicket vtx tk (txInBlockSize tx))]
                                    , pending) txs

-- | More or less equivalent to 'fold extendVRPrevApplied'
foldTxs' :: LedgerSupportsMempool blk
         => LedgerConfig blk
         -> (TickedLedgerState blk ValuesMK, [MempoolAddTxResult blk])
         -> [GenTx blk]
         -> (TickedLedgerState blk ValuesMK, [MempoolAddTxResult blk])
foldTxs' _ st [] = st -- FIXME mempool full is not contemplated
foldTxs' cfg (st, processed) (tx:txs) =
  case runExcept (applyTx cfg DoNotIntervene (withOrigin' $ pointSlot $ getTip st) tx st) of
    Left e -> foldTxs' cfg (st, processed ++ [MempoolTxRejected tx e]) txs
    Right (st', vtx) -> foldTxs' cfg ( forgetLedgerTablesDiffsTicked st'
                                     , processed ++ [MempoolTxAdded vtx]
                                     ) txs

{-------------------------------------------------------------------------------
  SUT semantics
-------------------------------------------------------------------------------}

-- | A mock LedgerDB that has the bare minimum to fulfill the LedgerInterface
data TestLedgerDB m blk =
  TestLedgerDB
    !(LedgerBackingStore m (ExtLedgerState blk))
    !(StrictTMVar m (LedgerState blk EmptyMK, MempoolChangelog blk))
    !(m (Maybe (WithOrigin SlotNo, LedgerTables (ExtLedgerState blk) ValuesMK)))

newLedgerInterface :: ( IOLike m
                      , LedgerSupportsProtocol blk
                      , SufficientSerializationForAnyBackingStore (LedgerState blk)
                      )
                   => LedgerState blk ValuesMK
                   -> m ( LedgerBackingStore m (ExtLedgerState blk)
                        , StrictTMVar m (LedgerState blk EmptyMK, MempoolChangelog blk)
                        , m (Maybe (WithOrigin SlotNo, LedgerTables (ExtLedgerState blk) ValuesMK))
                        , LedgerInterface m blk
                        )
newLedgerInterface st = do
  (q, bkst) <- createTVarBackingStore (ExtLedgerStateTables $ projectLedgerTables st)
  ledger <- newTMVarIO (forgetLedgerTables st, MempoolChangelog Origin polyEmptyLedgerTables)
  pure $ (bkst, ledger, q, LedgerInterface {
               getCurrentLedgerAndChangelog = readTMVar ledger
             , getBackingStore = pure bkst
             , withReadLock = id
             })

type MyMonad m blk = StateT (Mempool m blk TicketNo, TestLedgerDB m blk) m

semantics :: ( IOLike m
             , LedgerSupportsMempool blk
             , LedgerSupportsProtocol blk
             , HasTxId (GenTx blk)
             , Eq (GenTx blk)
             , SufficientSerializationForAnyBackingStore (LedgerState blk)
             )
          => LedgerConfig blk
          -> Action blk Concrete
          -> MyMonad m blk (Response blk Concrete)
semantics cfg = \case
  Init st -> do
    -- Initialize the mock LedgerDB
    (bkst, ldb, q, lif) <- lift $ newLedgerInterface st
    -- The mempool has to be opened without the sync thread so that we are the
    -- ones that perform the sync manually
    mp <- lift $ openMempoolWithoutSyncThread lif cfg NoMempoolCapacityBytesOverride nullTracer txInBlockSize
    put (mp, TestLedgerDB bkst ldb q)
    pure InitOk

  TryAddTxs txs -> do
    (mp, TestLedgerDB _ stv q) <- get
    -- Get the transactions before this call
    txsOld <- snapshotTxs <$> (lift $ atomically $ getSnapshot mp)
    -- Process the transactions
    (processed, pending) <- lift $ tryAddTxs mp DoNotIntervene txs
    -- Get the transactions after
    snap <- (lift $ atomically $ getSnapshot mp)
    let txsNew = snapshotTxs snap
    -- Fill up the state with the whole backing store and forward
    st' <- lift $ reconstruct mp stv q
    -- The transactions removed are the ones that are missing in the txsNew
    -- It cannot be the case that a transactions that is removed is then added again, so we should be fine.
    let removed = [ t' | t <- map fst txsOld
                      , let t' = txForgetValidated t
                      , not (elem t' $ map (txForgetValidated . fst) txsNew)
                      ]
    -- The transactions that were processed succesfully necesarily must appear
    -- in the later snapshot with a ticket number, so we can safely search for
    -- it.
        processedPlus = [ case t of
                            MempoolTxAdded t' -> MempoolTxAddedPlus
                                                    (TxSeq.TxTicket t'
                                                                    ( snd
                                                                      $ fromJust
                                                                      $ find (\(ntx, _) -> txForgetValidated ntx == txForgetValidated t') txsNew
                                                                    )
                                                                    (txInBlockSize (txForgetValidated t'))
                                                    )
                            MempoolTxRejected t' _ -> MempoolTxRejectedPlus t'
                        | t <- processed
                        ]
    -- The new ticket is the maximum of the added transactions + 1
    pure $ RespTryAddTxs st' (snapshotNextTicket snap) processedPlus pending $ Just removed

  SyncLedger -> do
    (mp, TestLedgerDB _ stv q) <- get
    -- Getting the transactions before
    txs <- snapshotTxs <$> (lift $ atomically $ getSnapshot mp)
    -- Peforming the sync with ledger, which happens to return the resulting snapshot, so we extract the new transactions
    txs' <- map (txForgetValidated . fst) . snapshotTxs <$> (lift $ syncWithLedger mp)
    -- Bring the whole backing store forwarded into the state
    st' <- lift $ reconstruct mp stv q
    -- The difference are the transactions that have been removed
    pure $ SyncOk st' [ t' | (t, _) <- txs, let t' = txForgetValidated t, not (elem t' txs')]

  GetSnapshot -> do
    (mp, _) <- get
    -- Easy, just get the transactions in the mempool
    Snapshot . snapshotTxs <$> (lift $ atomically $ getSnapshot mp)

  GetSnapshotFor st mustSucceed -> do
    (mp, TestLedgerDB _ svt q) <- get
    (_, mch) <- lift $ atomically $ readTMVar svt
    slot <- withOrigin' . fst . fromJust <$> lift q
    -- First I need to create an artificial extension from my db to that state
    -- that I'm given. For that first I fill the state in my mempool.
    st'' <- lift $ reconstruct mp svt q
    -- Then I calculate the differences that take me from the filled state of
    -- the mempool to the one requested. Extending the mempool changelog with
    -- these differences produces a changelog that indeed allows me to forward
    -- to the state I'm given.
    let diffs = projectLedgerTablesTicked
                $ forgetLedgerTablesValuesTicked
                $ zipOverLedgerTablesTicked rawCalculateDifference st'' $ (projectLedgerTablesTicked st)
        f :: Ord k => SeqDiffMK k v -> DiffMK k v -> SeqDiffMK k v
        f (ApplySeqDiffMK s) (ApplyDiffMK d) = ApplySeqDiffMK $ extendSeqUtxoDiff s (succ slot) d

    -- Now I produce the changelog and if this has to fail I mangle the anchor
    -- to +1 of what it should be, to ensure that it will fail.
    let mch' = mch { mcDifferences = zipLedgerTables f (mcDifferences mch) diffs }
        mch'' = if mustSucceed
                then mch'
                else mch' {mcAnchor = At $ succ slot}
    -- Calling `getSnapshotFor` with the given state emptied plus the custom
    -- mempool changelog should work as expected.
    snap <- lift $ getSnapshotFor mp (withOrigin' $ pointSlot $ getTip st) (st `withLedgerTablesTicked` polyEmptyLedgerTables) mch''
    -- In the end just take out the transactions.
    pure $ SnapshotFor $ fmap (fmap fst . snapshotTxs) snap
  Unsync st' -> do
    (_, TestLedgerDB (LedgerBackingStore bs) stv q) <- get
    lift $ do
      (state, chlog) <- atomically $ takeTMVar stv
      slot <- withOrigin' . fst . fromJust <$> q
      -- I write the current differences into the backing store and update the slot number
      bsWrite bs slot $ mapLedgerTables prj $ ExtLedgerStateTables $ mcDifferences chlog

      -- I then construct the current filled state in the mempool to compute what is
      -- needed for the differences.
      state' <- populate state chlog q
      let newDiffs = projectLedgerTables
                $ mapOverLedgerTables (\(ApplyDiffMK d) -> ApplySeqDiffMK $ extendSeqUtxoDiff emptySeqUtxoDiff (succ slot) d)
                $ forgetLedgerTablesValues
                $ zipOverLedgerTables rawCalculateDifference state'
                $ projectLedgerTables st'

      -- And I replace the state with this new data
      atomically $ putTMVar stv (forgetLedgerTables st', MempoolChangelog (At $ succ slot) newDiffs)
      pure UnsyncOk

 where
    prj ::
         Ord k
      => ApplyMapKind SeqDiffMK k v
      -> ApplyMapKind DiffMK k v
    prj (ApplySeqDiffMK sq) = ApplyDiffMK (cumulativeDiffSeqUtxoDiff sq)


reconstruct :: ( TickedTableStuff (LedgerState blk)
               , IOLike m
               )
            => Mempool m blk idx
            -> StrictTMVar m (LedgerState blk EmptyMK, MempoolChangelog blk)
            -> m (Maybe (WithOrigin SlotNo, LedgerTables (ExtLedgerState blk) ValuesMK))
            -> m (TickedLedgerState blk ValuesMK)
reconstruct mp stv q = do
    st' <- unsafeGetMempoolState mp
    (st, ch) <- atomically $ readTMVar stv
    st'' <- populate st ch q
    let f :: Ord k => DiffMK k v -> ValuesMK k v -> ValuesMK k v
        f (ApplyDiffMK d) (ApplyValuesMK v) = ApplyValuesMK (forwardValues v d)
    pure $ zipOverLedgerTablesTicked f st' (projectLedgerTables st'')

populate :: ( IOLike m
            , TableStuff (LedgerState blk)
            )
         => LedgerState blk EmptyMK
         -> MempoolChangelog blk
         -> m (Maybe (WithOrigin SlotNo, LedgerTables (ExtLedgerState blk) ValuesMK))
         -> m (LedgerState blk ValuesMK)
populate st ch q = do
  (_, ExtLedgerStateTables vs) <- fromJust <$> q
  pure $ st `withLedgerTables` (zipLedgerTables f (mcDifferences ch) vs)
 where
   f :: Ord k => SeqDiffMK k v -> ValuesMK k v -> ValuesMK k v
   f (ApplySeqDiffMK d) (ApplyValuesMK v) = ApplyValuesMK (forwardValues v (cumulativeDiffSeqUtxoDiff d))

sm :: forall m blk. ( LedgerSupportsMempool blk
      , LedgerSupportsProtocol blk
      , IOLike m
      , HasTxId (GenTx blk)
      , SufficientSerializationForAnyBackingStore (LedgerState blk)
      --  Can I use the test block with payload for this?
      , Eq (GenTx blk)
      , Arbitrary (TickedLedgerState blk ValuesMK)
      , Arbitrary (LedgerState blk ValuesMK)
      , Arbitrary (GenTx blk)
      )
   => LedgerConfig blk
   -> StateMachine (Model blk) (Action blk) (MyMonad m blk) (Response blk)
sm cfg =
  StateMachine
    initModel
    (transitions cfg)
    preconditions
    postconditions
    Nothing
    generator
    shrinker
    (semantics cfg)
    (mock cfg)
    noCleanup

prop_ticketDispenserParallel :: forall blk. Proxy blk -> LedgerConfig blk -> Property
prop_ticketDispenserParallel _ lcfg =
  forAllParallelCommands (sm @(MyMonad IO blk) @blk lcfg) Nothing $ \cmds -> monadic (ioProperty . flip evalStateT undefined) $ do
      r <- runParallelCommandsNTimes 100 (sm lcfg) cmds
      prettyParallelCommands cmds r
