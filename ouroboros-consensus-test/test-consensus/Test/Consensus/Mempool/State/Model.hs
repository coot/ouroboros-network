{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}

{-# OPTIONS_GHC -Wno-incomplete-record-updates #-}

-- |

module Test.Consensus.Mempool.State.Model (mock, transitions, zdiff) where

import           Control.Monad.Trans.Except (runExcept)
import           Data.Foldable
import qualified Data.List.NonEmpty as NE
import           Data.Word

import           Cardano.Slotting.Slot

import           Ouroboros.Consensus.Ledger.Basics
import           Ouroboros.Consensus.Ledger.SupportsMempool
import           Ouroboros.Consensus.Mempool
import           Ouroboros.Consensus.Mempool.TxSeq (TxTicket (..))
import qualified Ouroboros.Consensus.Mempool.TxSeq as TxSeq
import           Ouroboros.Consensus.Storage.LedgerDB.HD.DiffSeq

import           Ouroboros.Network.Block

import           Test.StateMachine

import           Test.Consensus.Mempool.State.Types

{-------------------------------------------------------------------------------
  Model transition
-------------------------------------------------------------------------------}
transitions :: ( IsLedger (LedgerState blk)
               , TickedTableStuff (LedgerState blk)
               , LedgerSupportsMempool blk
               , Show (Action blk r)
               , Show (Response blk r)
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
      let st'  = tickSt cfg 1 st
      in Model TxSeq.Empty st' TxSeq.zeroTicketNo (st NE.:| []) (computeMempoolCapacity st' NoMempoolCapacityBytesOverride) Nothing

    (NeedsInit, _, _)        -> error "unreachable"

    (_, GetSnapshot, _)      -> model
    (_, GetSnapshotFor{}, _) -> model

    (Model _ _ _ _ _ Nothing, SyncLedger, ResponseOk)  -> model
    (Model _ _ _ _ _ (Just nldb), SyncLedger, ResponseOk) -> model { modelLedgerDB = nldb
                                                                   , modelNextSync = Nothing
                                                                   }
    (Model _ _ _ _ _ Nothing, SyncLedger, SyncOk _ _)  -> model
    (Model txs _ _ _ _ (Just nldb), SyncLedger, SyncOk st' removed) ->
      let txs' = TxSeq.fromList [ t | t <- TxSeq.toList txs, txForgetValidated (txTicketTx t) `notElem` removed ]
          st'' = st' `withLedgerTablesTicked` zfwd (projectLedgerTables $ NE.last nldb) (projectLedgerTablesTicked st')
      in model { modelTxs = txs'
               , modelState = st''
               , modelLedgerDB = nldb
               , modelNextSync = Nothing
               , modelCapacity = computeMempoolCapacity st'' NoMempoolCapacityBytesOverride
               }

    (Model _ _ _ ldb _ s, TryAddTxs _, RespTryAddTxs st' tk' added _ removed) ->
      let model' = case s of
                     Nothing -> model { modelState = st'  `withLedgerTablesTicked` zfwd (projectLedgerTables $ NE.last ldb) (projectLedgerTablesTicked st')  }
                     Just nldb
                       | NE.last nldb == NE.last ldb
                       -> model { modelLedgerDB = nldb
                                , modelState = st'  `withLedgerTablesTicked` zfwd (projectLedgerTables $ NE.last nldb) (projectLedgerTablesTicked st')
                                }
                       | otherwise
                       -> transitions cfg model SyncLedger (SyncOk st' removed)
          txs'   = foldl' (TxSeq.:>) (modelTxs model') [ t | MempoolTxAddedPlus t <- added ]
      in model' { modelTxs = txs'
                , modelTicket = tk'
                }

    (Model _ _ _ ldb _ Nothing, UnsyncAnchor, ResponseOk) ->
      let newTables = maybe ldb id $ NE.nonEmpty $ NE.tail ldb
      in model { modelNextSync = Just newTables }
    (Model _ _ _ _ _ (Just nldb), UnsyncAnchor, ResponseOk) ->
      let newTables = maybe nldb id $ NE.nonEmpty $ NE.tail nldb
      in model { modelNextSync = Just newTables }
    (Model _ _ _ ldb _ Nothing, UnsyncTip states, ResponseOk) ->
      let newTables = NE.head ldb NE.:| NE.toList states
      in model { modelNextSync = Just newTables }
    (Model _ _ _ _ _ (Just nldb), UnsyncTip states, ResponseOk) ->
      let newTables = NE.head nldb NE.:| NE.toList states
      in model { modelNextSync = Just newTables }

    (Model{}, c, r) -> error $ "unreachable " <> show c <> " " <> show r

mock :: LedgerSupportsMempool blk
     => LedgerConfig blk
     -> Model blk Symbolic
     -> Action blk Symbolic
     -> GenSym (Response blk Symbolic)
mock cfg model action = case (model, action) of
  (NeedsInit, Init _) -> pure ResponseOk

  (Model _ _ _ _ _ Nothing, SyncLedger) -> pure ResponseOk
  (Model txs _ _ states _ (Just states'), SyncLedger) ->
    if
      NE.last states == NE.last states'
    then
      pure ResponseOk
    else do
      let slot                 = withOrigin 1 (+1) (pointSlot $ getTip $ NE.last states')
          ticked               = tickSt cfg slot (NE.last states')
          (applied, processed) = foldTxs' cfg (ticked, []) [ txForgetValidated $ TxSeq.txTicketTx tx | tx <- TxSeq.toList txs ]
          diffed               = forgetLedgerTablesValuesTicked $ calculateDifferenceTicked ticked applied
      pure $ SyncOk diffed [ tx | MempoolTxRejected tx _ <- processed ]

  (Model txs st tk ldb cap toSync, TryAddTxs txs') -> do
    resp <- mock cfg model SyncLedger
    let cap' = getMempoolCapacityBytes cap - sum [ txInBlockSize t | t' <- TxSeq.toList txs, let t = txForgetValidated $ txTicketTx t' ]
    case (resp, toSync) of
      (ResponseOk, _) -> do
        let (tk', st', processed, pending) = foldTxs cfg cap' (tk, st, []) txs'
            st'' = st' `withLedgerTablesTicked` zdiff (projectLedgerTables $ NE.last ldb) (projectLedgerTablesTicked st')
        pure $ RespTryAddTxs st'' tk' processed pending []
      (SyncOk st' removed, Just states) -> do
        let st'' = st' `withLedgerTablesTicked` zfwd (projectLedgerTables $ NE.last states) (projectLedgerTablesTicked st')
            cap'' = cap' + sum [ txInBlockSize t | t <- removed ]
            (tk', applied, processed, pending) = foldTxs cfg cap'' (tk, st'', []) txs'
            diffed = applied `withLedgerTablesTicked` zdiff (projectLedgerTables $ NE.last states) (projectLedgerTablesTicked applied)
        pure $ RespTryAddTxs diffed tk' processed pending removed
      _ -> error "unreachable"

  (Model txs _ _ _ _ _, GetSnapshot) ->
    pure $ Snapshot [ (TxSeq.txTicketTx tx, TxSeq.txTicketNo tx) | tx <- TxSeq.toList txs]

  (Model txs _ _ ldb _ Nothing, GetSnapshotFor st states) -> do
    let st' = st `withLedgerTablesTicked` zfwd (projectLedgerTables $ if null states then NE.last ldb else last states) (projectLedgerTablesTicked st)
        (_, processed) = foldTxs' cfg (st', []) [ txForgetValidated $ TxSeq.txTicketTx tx | tx <- TxSeq.toList txs ]
    pure $ SnapshotFor $ Just [ tx | MempoolTxAdded tx <- processed ]
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
    f (ApplyDiffMK d) (ApplyValuesMK v) = ApplyValuesMK (applyDiff v d)

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
fwd (ApplyValuesMK v) (ApplyDiffMK d) = ApplyValuesMK (applyDiff v d)

doDiff :: (Ord k, Eq v) => ValuesMK k v -> ValuesMK k v -> DiffMK k v
doDiff (ApplyValuesMK v1) (ApplyValuesMK v2) = ApplyDiffMK (diff v1 v2)

zdiff :: TableStuff blk
      => LedgerTables blk ValuesMK
      -> LedgerTables blk ValuesMK
      -> LedgerTables blk DiffMK
zdiff = zipLedgerTables doDiff

zfwd :: TableStuff blk
     => LedgerTables blk ValuesMK
     -> LedgerTables blk DiffMK
     -> LedgerTables blk ValuesMK
zfwd = zipLedgerTables fwd
