{-# OPTIONS_GHC -Wno-orphans #-}
module Ouroboros.Consensus.HardFork.Combinator.Ledger.PeerSelection () where

import           Data.SOP.Strict

import           Ouroboros.Consensus.Ledger.SupportsPeerSelection

import           Ouroboros.Consensus.HardFork.Combinator.Abstract
import           Ouroboros.Consensus.HardFork.Combinator.Basics
import           Ouroboros.Consensus.HardFork.Combinator.Ledger ()
import qualified Ouroboros.Consensus.HardFork.Combinator.State as State
import           Ouroboros.Consensus.HardFork.Combinator.Util.Functors (Flip (..))

instance CanHardFork xs => LedgerSupportsPeerSelection (HardForkBlock xs) where
  getPeers =
        hcollapse
      . hcmap proxySingle (K . getPeers . unFlip)
      . State.tip
      . hardForkLedgerStatePerEra
