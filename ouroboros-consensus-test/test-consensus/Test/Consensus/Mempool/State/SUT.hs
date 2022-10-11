{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}

module Test.Consensus.Mempool.State.SUT (semantics) where

import           Control.Monad (void)
import           Control.Monad.Class.MonadSTM.Strict
import           Control.Tracer
import           Data.Bifunctor (Bifunctor(bimap))
import           Data.Foldable
import           Data.IORef
import           Data.Maybe (fromJust)

import           Cardano.Slotting.Slot

import           Ouroboros.Consensus.Ledger.Basics
import           Ouroboros.Consensus.Ledger.Extended
import           Ouroboros.Consensus.Ledger.SupportsMempool
import           Ouroboros.Consensus.Ledger.SupportsProtocol
import           Ouroboros.Consensus.Mempool
import qualified Ouroboros.Consensus.Mempool.TxSeq as TxSeq
import           Ouroboros.Consensus.Storage.LedgerDB.HD
import           Ouroboros.Consensus.Storage.LedgerDB.HD.BackingStore
import           Ouroboros.Consensus.Storage.LedgerDB.OnDisk
import           Ouroboros.Consensus.Util.IOLike

import           Ouroboros.Network.Block

import           Test.StateMachine

import           Test.Consensus.Mempool.State.Types

-- | A mock LedgerDB that has the bare minimum to fulfill the LedgerInterface
data TestLedgerDB m blk =
  TestLedgerDB
    !(LedgerBackingStore m (ExtLedgerState blk))
    !(StrictTMVar m (LedgerState blk EmptyMK, MempoolChangelog blk))

newLedgerInterface ::
  ( IOLike m
  , LedgerSupportsProtocol blk
  , SufficientSerializationForAnyBackingStore (LedgerState blk)
  )
  => LedgerState blk ValuesMK
 -> m ( TestLedgerDB m blk
      , LedgerInterface m blk
      )
newLedgerInterface st = do
  bkst   <- snd <$> createTVarBackingStore (ExtLedgerStateTables $ projectLedgerTables st)
  ledger <- newTMVarIO (forgetLedgerTables st, MempoolChangelog Origin polyEmptyLedgerTables)
  pure $ ( TestLedgerDB bkst ledger
         , LedgerInterface {
               getCurrentLedgerAndChangelog = readTMVar ledger
             , getBackingStore              = pure bkst
             , withReadLock                 = id
             })

semantics ::
  ( LedgerSupportsMempool blk
  , LedgerSupportsProtocol blk
  , HasTxId (GenTx blk)
  , Eq (GenTx blk)
  , SufficientSerializationForAnyBackingStore (LedgerState blk)
  )
  => LedgerConfig blk
  -> IORef (Mempool IO blk TicketNo, TestLedgerDB IO blk)
  -> Action blk Concrete
  -> IO (Response blk Concrete)
semantics cfg ref = \case
  Init st -> do
    (testDb, iface) <- newLedgerInterface st
    -- The mempool has to be opened without the sync thread so that we are the
    -- ones that perform the sync manually
    mp <- openMempoolWithoutSyncThread iface cfg NoMempoolCapacityBytesOverride nullTracer txInBlockSize
    atomicWriteIORef ref (mp, testDb)
    pure ResponseOk

  TryAddTxs txs -> do
    (mp, _) <- readIORef ref
    -- Get the transactions before this call
    txsOld <- atomically $ snapshotTxs <$> getSnapshot mp
    -- Process the transactions
    (processed, pending) <- tryAddTxs mp DoNotIntervene txs
    -- Get the transactions after
    snap <- atomically $ getSnapshot mp
    let txsNew = snapshotTxs snap
        -- The transactions removed are the ones that are missing in the txsNew
        -- It cannot be the case that a transactions that is removed is then added again, so we should be fine.
        removed = [ t' | t <- map fst txsOld
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
    st <- unsafeGetMempoolState mp
    pure $ RespTryAddTxs st (snapshotNextTicket snap) processedPlus pending removed

  SyncLedger -> do
    (mp, _) <- readIORef ref
    -- Getting the transactions before
    txs <- atomically $ snapshotTxs <$> getSnapshot mp
    -- Peforming the sync with ledger, which happens to return the resulting snapshot, so we extract the new transactions
    txs' <- map (txForgetValidated . fst) . snapshotTxs <$> syncWithLedger mp

    st' <- unsafeGetMempoolState mp
    -- The difference are the transactions that have been removed
    pure $ SyncOk st' [ t' | (t, _) <- txs
                           , let t' = txForgetValidated t
                           , not (elem t' txs')
                           ]

  GetSnapshot -> do
    (mp, _) <- readIORef ref
    atomically $ Snapshot . snapshotTxs <$> getSnapshot mp

  GetSnapshotFor st ch -> do
    (mp, _) <- readIORef ref
    snap <- getSnapshotFor mp (withOrigin' $ pointSlot $ getTip st) st ch
    pure $ SnapshotFor $ fmap (fmap fst . snapshotTxs) snap

  UnsyncAnchor w -> do
    (_, TestLedgerDB (LedgerBackingStore bs) stv) <- readIORef ref
    (s, chlog) <- atomically $ takeTMVar stv
    let split :: Ord k => SeqDiffMK k v -> (SeqDiffMK k v, SeqDiffMK k v)
        split (ApplySeqDiffMK sq)       = bimap ApplySeqDiffMK ApplySeqDiffMK $ splitAtSeqUtxoDiff (fromIntegral w) sq
        toFlush                         = mapLedgerTables (fst . split) $ mcDifferences chlog
        toKeep                          = mapLedgerTables (snd . split) $ mcDifferences chlog
        getLastSlot :: Ord k => SeqDiffMK k v -> [SlotNo]
        getLastSlot (ApplySeqDiffMK sq) = [fromJust $ slotSeqUtxoDiff sq]
        slot                            = head $ foldLedgerTables getLastSlot toKeep
        prj :: Ord k => SeqDiffMK k v -> DiffMK k v
        prj (ApplySeqDiffMK sq) = ApplyDiffMK $ cumulativeDiffSeqUtxoDiff sq

    bsWrite bs slot $ mapLedgerTables prj $ ExtLedgerStateTables toFlush
    atomically $ putTMVar stv (s, MempoolChangelog (At slot) toKeep)
    pure ResponseOk

  UnsyncTip t diffs -> do
    (_, TestLedgerDB _ stv) <- readIORef ref
    let ext :: Ord k => SlotNo -> SeqDiffMK k v -> DiffMK k v -> SeqDiffMK k v
        ext sl (ApplySeqDiffMK sq) (ApplyDiffMK d) = ApplySeqDiffMK $ extendSeqUtxoDiff sq sl d
    void $ atomically $ swapTMVar stv (t, MempoolChangelog (pointSlot $ getTip t) $ foldl' (\a (b, c) -> zipLedgerTables (ext b) a c) polyEmptyLedgerTables diffs)
    pure ResponseOk
