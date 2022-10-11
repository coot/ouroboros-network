{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}

{-# OPTIONS_GHC -Wno-incomplete-record-updates #-}

-- |

module Test.Consensus.Mempool.State.Model (mock, transitions) where

import           Control.Monad.Trans.Except (runExcept)
import           Data.Foldable
import qualified Data.List.NonEmpty as NE
import           Data.Maybe (fromJust)
import           Data.Word

import           Cardano.Slotting.Slot

import           Ouroboros.Consensus.Ledger.Basics
import           Ouroboros.Consensus.Ledger.SupportsMempool
import           Ouroboros.Consensus.Mempool
import           Ouroboros.Consensus.Mempool.TxSeq (TxTicket (..))
import qualified Ouroboros.Consensus.Mempool.TxSeq as TxSeq
import           Ouroboros.Consensus.Storage.LedgerDB.HD

import           Ouroboros.Network.Block

import           Test.StateMachine

import           Test.Consensus.Mempool.State.Types

{-------------------------------------------------------------------------------
  Model transition
-------------------------------------------------------------------------------}
transitions :: ( IsLedger (LedgerState blk)
               , TickedTableStuff (LedgerState blk)
               , LedgerSupportsMempool blk
               , Eq (GenTx blk)
               )
            => LedgerConfig blk
 -> Model blk r
 -> Action blk r
 -> Response blk r
 -> Model blk r
transitions cfg model cmd resp =
  case (model, cmd, resp) of
    (NeedsInit, Init st, ResponseOk) ->
      let slot = withOrigin' (pointSlot $ getTip st)
          st'  = tickSt cfg (slot + 1) st
      in Model TxSeq.Empty st' TxSeq.zeroTicketNo (MockLedgerDB (forgetLedgerTables st) ((slot, projectLedgerTables st) NE.:| [])) (computeMempoolCapacity st' NoMempoolCapacityBytesOverride) Nothing

    (NeedsInit, _, _)        -> error "unreachable"

    (_, GetSnapshot, _)      -> model
    (_, GetSnapshotFor{}, _) -> model

    (Model _ _ _ _ _ Nothing, SyncLedger, ResponseOk)  -> model
    (Model _ _ _ _ _ (Just m), SyncLedger, ResponseOk) -> model { modelBackingStore = m }
    (Model txs _ _ _ _ (Just m), SyncLedger, SyncOk st' removed) ->
      let txs' = TxSeq.fromList [ t | t <- TxSeq.toList txs, txForgetValidated (txTicketTx t) `notElem` removed ]
          st'' = st' `withLedgerTablesTicked` zfwd (snd $ NE.last $ mockTables m) (projectLedgerTablesTicked st')
      in model { modelTxs = txs'
               , modelState = st''
               , modelBackingStore = m
               , modelNextSync = Nothing
               , modelCapacity = computeMempoolCapacity st'' NoMempoolCapacityBytesOverride
               }

    (Model _ _ _ _ _ s, TryAddTxs _, RespTryAddTxs st' tk' added _ removed) ->
      let model' = case s of
                     Nothing                                             -> model
                     Just s'
                       | mockTip s' == mockTip (modelBackingStore model) -> model
                       | otherwise                                       -> transitions cfg model SyncLedger (SyncOk st' removed)
          txs'             = foldl' (TxSeq.:>) (modelTxs model') [ t | MempoolTxAddedPlus t <- added ]
      in model' { modelTxs = txs', modelTicket = tk' }

    (Model _ _ _ _ _ Nothing, UnsyncAnchor w, ResponseOk) ->
      let newTables = fromJust $ NE.nonEmpty $ NE.drop (fromIntegral w) $ mockTables $ modelBackingStore model
      in model { modelNextSync = Just $ (modelBackingStore model) { mockTables = newTables } }
    (Model _ _ _ _ _ (Just s), UnsyncAnchor w, ResponseOk) ->
      let newTables = fromJust $ NE.nonEmpty $ NE.drop (fromIntegral w) $ mockTables s
      in model { modelNextSync = Just $ (modelBackingStore model) { mockTables = newTables } }
    (Model _ _ _ _ _ Nothing, UnsyncTip tip diffs, ResponseOk) ->
      let newTables = NE.reverse $ foldl' (\acc (s, d)  -> (s, zfwd (snd $ NE.head acc) d) NE.<| acc) (NE.head (mockTables $ modelBackingStore model) NE.:| []) (NE.toList diffs)
      in model { modelNextSync = Just $ MockLedgerDB tip newTables }
    (Model _ _ _ _ _ (Just s), UnsyncTip tip diffs, ResponseOk) ->
      let newTables = NE.reverse $ foldl' (\acc (sl, d) -> (sl, zfwd (snd $ NE.head acc) d) NE.<| acc) (NE.head (mockTables s) NE.:| []) (NE.toList diffs)
      in model { modelNextSync = Just $ MockLedgerDB tip newTables }

    (Model{}, _, _) -> error "unreachable"

mock :: LedgerSupportsMempool blk
     => LedgerConfig blk
     -> Model blk Symbolic
     -> Action blk Symbolic
     -> GenSym (Response blk Symbolic)
mock cfg model action = case (model, action) of
  (NeedsInit, Init _) -> pure ResponseOk

  (Model _ _ _ _ _ Nothing, SyncLedger) -> pure ResponseOk
  (Model txs _ _ (MockLedgerDB oldTip _) _ (Just (MockLedgerDB tip tbs)), SyncLedger) ->
    if oldTip == tip
    then pure ResponseOk
    else do
      let slot                 = withOrigin' (pointSlot $ getTip tip)
          ticked               = tickSt cfg (slot + 1) (tip `withLedgerTables` snd (NE.last tbs))
          (applied, processed) = foldTxs' cfg (ticked, []) [ txForgetValidated $ TxSeq.txTicketTx tx | tx <- TxSeq.toList txs ]
          diffed               = forgetLedgerTablesValuesTicked $ calculateDifferenceTicked ticked applied
      pure $ SyncOk diffed [ tx | MempoolTxRejected tx _                                                  <- processed ]

  (Model txs st tk bkst cap toSync, TryAddTxs txs')                -> do
    resp <- mock cfg model SyncLedger
    let cap' = getMempoolCapacityBytes cap - sum [ txInBlockSize t | t' <- TxSeq.toList txs, let t = txForgetValidated $ txTicketTx t' ]
    case (resp, toSync) of
      (ResponseOk, _)                                          -> do
        let (tk', st', processed, pending)     = foldTxs cfg cap' (tk, st, []) txs'
            st''                               = st' `withLedgerTablesTicked` zdiff (snd $ NE.last $ mockTables bkst) (projectLedgerTablesTicked st')
        pure $ RespTryAddTxs st'' tk' processed pending []
      (SyncOk synced removed, Just (MockLedgerDB _ newTables)) -> do
        let synced'                            = synced `withLedgerTablesTicked` zfwd (snd $ NE.last newTables) (projectLedgerTablesTicked synced)
            cap'' = cap' + sum [ txInBlockSize t | t <- removed ]
            (tk', applied, processed, pending) = foldTxs cfg cap'' (tk, synced', []) txs'
            diffed = applied `withLedgerTablesTicked` zdiff (snd $ NE.last newTables) (projectLedgerTablesTicked applied)
        pure $ RespTryAddTxs diffed tk' processed pending removed
      _ -> error "unreachable"

  (Model txs _ _ _ _ _, GetSnapshot) ->
    pure $ Snapshot [ (TxSeq.txTicketTx tx, TxSeq.txTicketNo tx) | tx <- TxSeq.toList txs]

  (Model txs _ _ m _ Nothing, GetSnapshotFor st mch) -> do
    let st' = st `withLedgerTablesTicked` zipLedgerTables fwd' (snd $ NE.head $ mockTables m) (mcDifferences mch)
        (_, processed) = foldTxs' cfg (st', []) [ txForgetValidated $ TxSeq.txTicketTx tx | tx <- TxSeq.toList txs ]
    pure $ SnapshotFor $ Just [ tx | MempoolTxAdded tx                                         <- processed ]
  (Model _ _ _ _ _ _, GetSnapshotFor{}) -> pure $ SnapshotFor Nothing

  (Model{}, UnsyncTip{})    -> pure ResponseOk
  (Model{}, UnsyncAnchor{}) -> pure ResponseOk

  _ -> error "unreachable"

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
        -> Word32
        -> ( TicketNo
           , TickedLedgerState blk ValuesMK
           , [MempoolAddTxResultPlus blk]
           )
        -> [GenTx blk]
        -> ( TicketNo
           , TickedLedgerState blk ValuesMK
           , [MempoolAddTxResultPlus blk]
           , [GenTx blk]
           )
foldTxs _ _ (tk, st, processed) [] = (tk, st, processed, [])
foldTxs cfg cap (tk, st, processed) (tx:txs) =
  if cap < txInBlockSize tx then (tk, st, processed, tx:txs)
  else
  case runExcept (applyTx cfg DoNotIntervene (withOrigin' $ pointSlot $ getTip st) tx st) of
    Left _ -> foldTxs cfg cap (tk, st, processed ++ [MempoolTxRejectedPlus tx]) txs
    Right (st', vtx) -> foldTxs cfg (cap - txInBlockSize tx) ( succ tk
                                    , forgetLedgerTablesDiffsTicked st'
                                    , processed ++ [MempoolTxAddedPlus (TxSeq.TxTicket vtx tk (txInBlockSize tx))]
                                    ) txs

-- | More or less equivalent to 'fold extendVRPrevApplied'
foldTxs' :: LedgerSupportsMempool blk
         => LedgerConfig blk
         -> (TickedLedgerState blk ValuesMK, [MempoolAddTxResult blk])
         -> [GenTx blk]
         -> (TickedLedgerState blk ValuesMK, [MempoolAddTxResult blk])
foldTxs' _ st [] = st
foldTxs' cfg (st, processed) (tx:txs) =
  case runExcept (applyTx cfg DoNotIntervene (withOrigin' $ pointSlot $ getTip st) tx st) of
    Left e -> foldTxs' cfg (st, processed ++ [MempoolTxRejected tx e]) txs
    Right (st', vtx) -> foldTxs' cfg ( forgetLedgerTablesDiffsTicked st'
                                     , processed ++ [MempoolTxAdded vtx]
                                     ) txs

{-------------------------------------------------------------------------------
  Helpers
-------------------------------------------------------------------------------}
fwd :: Ord k => ValuesMK k v -> DiffMK k v -> ValuesMK k v
fwd (ApplyValuesMK v) (ApplyDiffMK d) = ApplyValuesMK (forwardValues v d)

fwd' :: Ord k => ValuesMK k v -> SeqDiffMK k v -> ValuesMK k v
fwd' v (ApplySeqDiffMK d) = fwd v (ApplyDiffMK (cumulativeDiffSeqUtxoDiff d))

diff :: Ord k => ValuesMK k v -> ValuesMK k v -> DiffMK k v
diff (ApplyValuesMK v1) (ApplyValuesMK v2) = ApplyDiffMK (differenceUtxoValues v1 v2)

zdiff :: TableStuff blk
      => LedgerTables blk ValuesMK
      -> LedgerTables blk ValuesMK
      -> LedgerTables blk DiffMK
zdiff = zipLedgerTables diff

zfwd :: TableStuff blk
     => LedgerTables blk ValuesMK
     -> LedgerTables blk DiffMK
     -> LedgerTables blk ValuesMK
zfwd = zipLedgerTables fwd
