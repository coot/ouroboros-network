{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Test.Util.Orphans.ToExpr () where

import           Data.Foldable (toList)
import           Data.TreeDiff (Expr (App), ToExpr (..), genericToExpr)

import           Cardano.Slotting.Slot

import           Ouroboros.Network.Block
import           Ouroboros.Network.Point

import           Ouroboros.Consensus.Block
import           Ouroboros.Consensus.HeaderValidation
import           Ouroboros.Consensus.Ledger.Abstract
import           Ouroboros.Consensus.Ledger.Extended
import           Ouroboros.Consensus.Protocol.Abstract
import qualified Ouroboros.Consensus.Storage.LedgerDB.HD.DiffSeq as DS

{-------------------------------------------------------------------------------
  ouroboros-network
-------------------------------------------------------------------------------}

instance ToExpr SlotNo
instance ToExpr BlockNo

instance ToExpr t => ToExpr (WithOrigin t)
instance ToExpr (HeaderHash blk) => ToExpr (Point blk)
instance ToExpr (HeaderHash blk) => ToExpr (RealPoint blk)
instance (ToExpr slot, ToExpr hash) => ToExpr (Block slot hash)

{-------------------------------------------------------------------------------
  ouroboros-consensus
-------------------------------------------------------------------------------}

deriving anyclass instance ( ToExpr (ChainDepState (BlockProtocol blk))
                           , ToExpr (TipInfo blk)
                           , ToExpr (LedgerState blk mk)
                           ) => ToExpr (ExtLedgerState blk mk)

instance ( ToExpr (ChainDepState (BlockProtocol blk))
         , ToExpr (TipInfo blk)
         ) => ToExpr (HeaderState blk)

instance ( ToExpr (TipInfo blk)
         ) => ToExpr (AnnTip blk)

{-------------------------------------------------------------------------------
  ouroboros-consensus: UTxO HD
-------------------------------------------------------------------------------}

instance (ToExpr k, ToExpr v) => ToExpr (ApplyMapKind' mk' k v) where
  toExpr ApplyEmptyMK =
    App "ApplyEmptyMK"     []
  toExpr (ApplyDiffMK diffs) =
    App "ApplyDiffMK"      [genericToExpr diffs]
  toExpr (ApplyKeysMK keys) =
    App "ApplyKeysMK"      [genericToExpr keys]
  toExpr (ApplySeqDiffMK (DS.UnsafeDiffSeq seqdiff)) =
    App "ApplySeqDiffMK"   [genericToExpr $ toList seqdiff]
  toExpr (ApplyTrackingMK vals diffs) =
    App "ApplyTrackingMK"  [
        genericToExpr vals
      , genericToExpr diffs
      ]
  toExpr (ApplyValuesMK vals) =
    App "ApplyValuesMK"    [genericToExpr vals]
  toExpr ApplyQueryAllMK =
    App "ApplyQueryAllMK"  []
  toExpr (ApplyQuerySomeMK keys) =
    App "ApplyQuerySomeMK" [genericToExpr keys]

deriving anyclass instance ToExpr v => ToExpr (DS.DiffEntry v)
deriving anyclass instance (ToExpr k, ToExpr v) => ToExpr (DS.Diff k v)
deriving anyclass instance (ToExpr k, ToExpr v) => ToExpr (DS.Values k v)
deriving anyclass instance (ToExpr k, ToExpr v) => ToExpr (DS.Keys k v)
deriving anyclass instance (ToExpr k, ToExpr v) => ToExpr (DS.RootMeasure k v)
deriving anyclass instance (ToExpr k, ToExpr v) => ToExpr (DS.InternalMeasure k v)
deriving anyclass instance (ToExpr k, ToExpr v) => ToExpr (DS.Element k v)
deriving anyclass instance ToExpr DS.Length
deriving anyclass instance ToExpr DS.SlotNoUB
deriving anyclass instance ToExpr DS.SlotNoLB

instance ToExpr v => ToExpr (DS.DiffHistory v) where
  toExpr h = App "DiffHistory" [genericToExpr . toList $ h]

instance ToExpr v => ToExpr (DS.NEDiffHistory v) where
  toExpr h = App "NEDiffHistory" [genericToExpr . toList $ h]

