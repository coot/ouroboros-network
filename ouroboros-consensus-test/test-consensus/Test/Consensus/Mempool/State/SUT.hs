{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Consensus.Mempool.State.SUT (semantics, TestLedgerDB) where

import           Control.Monad (void, when)
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
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class (lift)
import qualified Ouroboros.Consensus.Util.MonadSTM.RAWLock as RAWLock
import Ouroboros.Consensus.Util.MonadSTM.RAWLock (withWriteAccess)
import Debug.Trace
import Control.Exception (ErrorCall, throw)

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
      , RAWLock.RAWLock m ()
      )
newLedgerInterface st = do
  bkst   <- snd <$> createTVarBackingStore (ExtLedgerStateTables $ projectLedgerTables st)
  ledger <- newTMVarIO (forgetLedgerTables st, MempoolChangelog Origin polyEmptyLedgerTables)
  rw <- RAWLock.new ()
  pure $ ( TestLedgerDB bkst ledger
         , LedgerInterface {
               getCurrentLedgerAndChangelog = readTMVar ledger
             , getBackingStore              = pure bkst
             , withReadLock                 = \m -> RAWLock.withReadAccess rw (\() -> m)
             }
         , rw)

semantics ::
  ( LedgerSupportsMempool blk
  , LedgerSupportsProtocol blk
  , HasTxId (GenTx blk)
  , Eq (GenTx blk)
  , SufficientSerializationForAnyBackingStore (LedgerState blk)
  )
  => LedgerConfig blk
  -> Bool
  -> Action blk Concrete
  -> ReaderT (IORef (Mempool IO blk TicketNo, TestLedgerDB IO blk, RAWLock.RAWLock IO ())) IO (Response blk Concrete)
semantics cfg trc action = do
  ref <- ask
  lift $ do
   myId <- myThreadId
   case action of
    Init st -> do
      when trc $ traceM $ "START " <> show myId <> " INIT"
      (testDb, iface, rwl) <- newLedgerInterface st
      -- The mempool has to be opened without the sync thread so that we are the
      -- ones that perform the sync manually
      mp <- openMempoolWithoutSyncThread iface cfg NoMempoolCapacityBytesOverride nullTracer txInBlockSize
      atomicWriteIORef ref (mp, testDb, rwl)
      when trc $ traceM $ "END " <> show myId <> " INIT"
      pure ResponseOk

    TryAddTxs txs -> do
      when trc $ traceM $ "START " <> show myId <> " TRYADDTXS"
      (mp, _, _) <- readIORef ref
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
      when trc $ traceM $ "END " <> show myId <> " TRYADDTXS"
      pure $ RespTryAddTxs st (snapshotNextTicket snap) processedPlus pending removed

    SyncLedger -> do
      when trc $ traceM $ "START " <> show myId <> " SYNCLEDGER"
      (mp, _, _) <- readIORef ref
      -- Getting the transactions before
      txs <- atomically $ snapshotTxs <$> getSnapshot mp
      -- Peforming the sync with ledger, which happens to return the resulting snapshot, so we extract the new transactions
      txs' <- map (txForgetValidated . fst) . snapshotTxs <$> syncWithLedger mp

      st' <- unsafeGetMempoolState mp
      -- The difference are the transactions that have been removed
      when trc $ traceM $ "END " <> show myId <> " SYNCLEDGER"
      pure $ SyncOk st' [ t' | (t, _) <- txs
                             , let t' = txForgetValidated t
                             , not (elem t' txs')
                             ]

    GetSnapshot -> do
      when trc $ traceM $ "START " <> show myId <> " GETSNAP"
      (mp, _, _) <- readIORef ref
      t <- atomically $ Snapshot . snapshotTxs <$> getSnapshot mp
      when trc $ traceM $ "END " <> show myId <> " GETSNAP"
      pure t

    GetSnapshotFor st ch -> do
      when trc $ traceM $ "START " <> show myId <> " GETSNAPFOR"
      (mp, _, rwl) <- readIORef ref
      let !slot = withOrigin' $ pointSlot $ getTip st
      when trc $ traceM $ "For slot " <> show slot
      snap <- RAWLock.withReadAccess rwl (\() -> getSnapshotFor mp slot st ch)
      when trc $ traceM $ "END " <> show myId <> " GETSNAPFOR"
      pure $ SnapshotFor $ fmap (fmap fst . snapshotTxs) snap

    UnsyncAnchor w ->

     if w == 0 then pure ResponseOk
     else do
      when trc $ traceM $ "START " <> show myId <> " UnsyncAnchor"
      (_, TestLedgerDB (LedgerBackingStore bs) stv, rwl) <- readIORef ref
      (s, chlog) <- atomically $ takeTMVar stv
      let split :: Ord k => SeqDiffMK k v -> (SeqDiffMK k v, SeqDiffMK k v)
          split (ApplySeqDiffMK sq)       = bimap ApplySeqDiffMK ApplySeqDiffMK $ splitAtSeqUtxoDiff (fromIntegral w) sq
          toFlush                         = mapLedgerTables (fst . split) $ mcDifferences chlog
          toKeep                          = mapLedgerTables (snd . split) $ mcDifferences chlog
          getLastSlot :: Ord k => SeqDiffMK k v -> [Maybe SlotNo]
          getLastSlot (ApplySeqDiffMK sq) = [slotSeqUtxoDiff sq] -- failing!!
          slot                            = case head $ foldLedgerTables getLastSlot toFlush of
            Nothing -> withOrigin' (getTipSlot s)
            Just v -> v
          prj :: Ord k => SeqDiffMK k v -> DiffMK k v
          prj (ApplySeqDiffMK sq) = ApplyDiffMK $ cumulativeDiffSeqUtxoDiff sq

      eio <- try (withWriteAccess rwl (\() -> do
                              ((),) <$> (bsWrite bs slot $ mapLedgerTables prj $ ExtLedgerStateTables toFlush)
                          ))
      case eio of
        Left (e :: ErrorCall) -> do
          print $ "ToFlush: " <> showsLedgerState sMapKind toFlush ""
          print $ "ToKeep: " <> showsLedgerState sMapKind toKeep ""
          print $ "Cur Chlog: " <> showsLedgerState sMapKind (mcDifferences chlog) ""
          print $ "Flushing: " <> show w
          throw e
        Right () -> do
          atomically $ putTMVar stv (s, MempoolChangelog (At slot) toKeep)
          when trc $ traceM $ "END " <> show myId <> " UnsyncAnchor"
          pure ResponseOk

    UnsyncTip t diffs -> do
      when trc $ traceM $  "START " <> show myId <> " UnsyncTip"
      (_, TestLedgerDB _ stv, _) <- readIORef ref
      let ext :: Ord k => SlotNo -> SeqDiffMK k v -> DiffMK k v -> SeqDiffMK k v
          ext sl (ApplySeqDiffMK sq) (ApplyDiffMK d) = ApplySeqDiffMK $ extendSeqUtxoDiff sq sl d
      anch <- atomically $ mcAnchor . snd <$> readTMVar stv
      void $ atomically $ swapTMVar stv (t, MempoolChangelog anch $ foldl' (\a (b, _, c) -> zipLedgerTables (ext b) a c) polyEmptyLedgerTables diffs)
      when trc $ traceM $  "END " <> show myId <> " UnsyncTip"
      pure ResponseOk
