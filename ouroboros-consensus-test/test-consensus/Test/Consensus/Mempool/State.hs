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

{-# OPTIONS_GHC -Wno-partial-fields -Wno-incomplete-record-updates #-}

module Test.Consensus.Mempool.State (prop_mempoolParallel) where

import Control.Monad.Trans.Reader
import Data.IORef
import Data.Proxy (Proxy)

import Ouroboros.Consensus.Ledger.Basics
import Ouroboros.Consensus.Ledger.SupportsMempool
import Ouroboros.Consensus.Ledger.SupportsProtocol
import Ouroboros.Consensus.Mempool

import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.StateMachine

import Test.Consensus.Mempool.State.Model
import Test.Consensus.Mempool.State.SUT
import Test.Consensus.Mempool.State.Types

{-------------------------------------------------------------------------------
  Generation
-------------------------------------------------------------------------------}

generator ::
  ( Arbitrary (LedgerState blk EmptyMK)
  , Arbitrary (LedgerState blk ValuesMK)
  , Arbitrary (TickedLedgerState blk DiffMK)
  , Arbitrary (GenTx blk)
  , Arbitrary (MempoolChangelog blk)
  )
  => Model blk Symbolic
  -> Maybe (Gen (Action blk Symbolic))
  -- FIXME: @js redo these generators
generator = \case
  NeedsInit -> Just $ Init <$> arbitrary
  Model{}   -> Just $ frequency $
   [ (2, TryAddTxs      <$> arbitrary)
   , (1, pure GetSnapshot)
   , (1, GetSnapshotFor <$> arbitrary <*> arbitrary)
   , (1, UnsyncTip      <$> arbitrary <*> undefined)
   , (1, UnsyncAnchor   <$> (arbitrary `suchThat` (<= undefined)))
   , (1, pure SyncLedger)
   ]

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

sm :: forall blk.
      ( LedgerSupportsMempool blk
      , LedgerSupportsProtocol blk
      , HasTxId (GenTx blk)
      , SufficientSerializationForAnyBackingStore (LedgerState blk)
      --  Can I use the test block with payload for this?
      , Eq (GenTx blk)
      , Arbitrary (TickedLedgerState blk DiffMK)
      , Arbitrary (LedgerState blk ValuesMK)
      , Arbitrary (LedgerState blk EmptyMK)
      , Arbitrary (MempoolChangelog blk)
      , Arbitrary (GenTx blk)
      )
   => LedgerConfig blk
   -> StateMachine (Model blk) (Action blk) (TestEnv IO blk) (Response blk)
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

prop_mempoolParallel :: forall blk.
      ( LedgerSupportsMempool blk
      , LedgerSupportsProtocol blk
      , HasTxId (GenTx blk)
      , SufficientSerializationForAnyBackingStore (LedgerState blk)
      --  Can I use the test block with payload for this?
      , Show (TickedLedgerState blk ValuesMK)
      , Show (LedgerState blk ValuesMK)
      , Show (TickedLedgerState blk DiffMK)
      , Show (TickedLedgerState blk EmptyMK)
      , Show (LedgerState blk EmptyMK)
      , Show (LedgerTables (LedgerState blk) DiffMK)
      , Show (LedgerTables (LedgerState blk) ValuesMK)
      , Show (MempoolChangelog blk)
      , Eq (GenTx blk)
      , Arbitrary (TickedLedgerState blk DiffMK)
      , Arbitrary (LedgerState blk ValuesMK)
      , Arbitrary (LedgerState blk EmptyMK)
      , Arbitrary (MempoolChangelog blk)
      , Arbitrary (GenTx blk)
      ) => Proxy blk -> LedgerConfig blk -> Property
prop_mempoolParallel _ lcfg = forAllParallelCommands (sm @blk lcfg) Nothing $ \cmds ->
    monadic (\prop   -> ioProperty $ do
                ref <- newIORef undefined
                flip runReaderT ref prop
            )
            (runParallelCommandsNTimes 100 (sm @blk lcfg) cmds >>= prettyParallelCommands cmds)
