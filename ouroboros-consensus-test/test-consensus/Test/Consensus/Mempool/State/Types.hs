{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-partial-fields #-}
-- |

module Test.Consensus.Mempool.State.Types (
    -- * Actions
    Action (..)
  , Response (..)
    -- * Model
  , MempoolAddTxResultPlus (..)
  , MockLedgerDB(..)
  , Model (..)
  , initModel
    -- * Helpers
  , withOrigin'
  ) where

import           Data.Kind
import           Data.List.NonEmpty (NonEmpty)
import           GHC.Generics
                   (Generic1)

import           Cardano.Slotting.Slot

import           Ouroboros.Consensus.Ledger.Basics
import           Ouroboros.Consensus.Ledger.SupportsMempool
import           Ouroboros.Consensus.Mempool
import           Ouroboros.Consensus.Mempool.TxSeq (TxSeq)
import qualified Ouroboros.Consensus.Mempool.TxSeq as TxSeq

import           Test.StateMachine
import qualified Test.StateMachine.Types.Rank2 as Rank2

{-------------------------------------------------------------------------------
  Actions
-------------------------------------------------------------------------------}
data Action blk (r     :: Type -> Type)
    -- | Initialize the mempool and mock ledger DB with this state
 = Init { stateForInit :: !(LedgerState blk ValuesMK) }

    -- | Try to add the given transactions into the mempool
  | TryAddTxs { txsToAdd :: ![GenTx blk] }

    -- | Perform a sync with the mock ledger DB
  | SyncLedger

    -- | Request a snapshot to the current mempool
  | GetSnapshot

    -- | Request a snapshot for a specific ledger state
  | GetSnapshotFor
      { snapshotState     :: !(TickedLedgerState blk DiffMK),
        snapshotChangelog :: !(MempoolChangelog blk)
      }

    -- | Make the ledger go out of sync with the mempool by giving a new tip + diffs
    --
    -- This means @switchToFork@
  | UnsyncTip
      { unsyncTip   :: !(LedgerState blk EmptyMK),
        unsyncDiffs :: !(NonEmpty (SlotNo, LedgerTables (LedgerState blk) DiffMK))
      }

    -- | Make the ledger go out of sync moving the anchor forward
    --
    -- This means @flush@
  | UnsyncAnchor { moveAnchor :: !Word }

  deriving stock Generic1
  deriving anyclass (Rank2.Functor, Rank2.Foldable, Rank2.Traversable, CommandNames)

deriving instance ( Show (LedgerState blk EmptyMK)
                  , Show (TickedLedgerState blk DiffMK)
                  , Show (LedgerState blk ValuesMK)
                  , Show (TickedLedgerState blk EmptyMK)
                  , Show (GenTx blk)
                  , Show (LedgerTables (LedgerState blk) DiffMK)
                  , Show (MempoolChangelog blk)
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
 = -- | There's nothing to tell
    ResponseOk

  | -- | Transactions were pushed onto the mempool
    RespTryAddTxs
      !(TickedLedgerState blk DiffMK) -- ^ The resulting ledger state after
                                        -- the transactions (and ticking if a resync was needed)

      !TicketNo                         -- ^ The last ticket number

      ![MempoolAddTxResultPlus blk]     -- ^ The list of results of processing
                                        -- the transactions

      ![GenTx blk]                      -- ^ The list of transactions that
                                        -- couldn't be processed because of lack
                                        -- of space in the mempool

      ![GenTx blk]                      -- ^ If this had to trigger a resync,
                                        -- then these are the txs that were
                                        -- dropped by the resync

  | -- | A Sync with a new state was performed
    SyncOk
      !(TickedLedgerState blk DiffMK)   -- ^ The resulting ledger state after syncing
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
  deriving stock (Generic1)
  deriving anyclass Rank2.Foldable

deriving instance ( Show (Validated (GenTx blk))
                  , Show (GenTx blk)
                  , Show (TickedLedgerState blk DiffMK)
                  ) => Show (Response blk r)

{-------------------------------------------------------------------------------
  Model
-------------------------------------------------------------------------------}

-- | Mock a minimal LedgerDB for the model
--
-- This mock contains both the tip state and the sequence of slot x tables that
-- are represented by the db changelog. In particular, the list of tables has to
-- be sorted and the last one corresponds to the values for the tip. It is as if
-- we applied each table of differences to the backing store values.
--
-- Invariants:
--
--  * fst (NE.last mockTables) = slot mockTip
--
--  * sorted (NE.map fst mockTables)
data MockLedgerDB blk          = MockLedgerDB
  { mockTip    :: !(LedgerState blk EmptyMK)
  , mockTables :: !(NonEmpty (SlotNo, LedgerTables (LedgerState blk) ValuesMK))
  }

deriving instance ( Eq (LedgerState blk EmptyMK)
                  , Eq (LedgerTables (LedgerState blk) ValuesMK)
                  ) => Eq (MockLedgerDB blk)
deriving instance ( Show (LedgerState blk EmptyMK)
                  , Show (LedgerTables (LedgerState blk) ValuesMK)
                  ) => Show (MockLedgerDB blk)

data Model blk (r :: Type -> Type) =
    -- | The model is yet to be initialized
    NeedsInit
  | -- | The model is initialized
    Model
      { -- | The current sequence of validated transactions
        modelTxs  :: !(TxSeq (Validated (GenTx blk)))

        -- | The ledger state after applying all the transactions
      , modelState :: !(TickedLedgerState blk ValuesMK)

        -- | The next ticket number [need ref]
      , modelTicket :: !TicketNo

        -- | A mocking backing store
      , modelBackingStore :: !(MockLedgerDB blk)

      , modelCapacity     :: !MempoolCapacityBytes
        -- | This might hols a new LedgerDB if we have to resync. Further
        -- unsyncs will modify this value.
      , modelNextSync :: !(Maybe (MockLedgerDB blk))
      }

deriving instance ( Eq (TickedLedgerState blk ValuesMK)
                  , Eq (MockLedgerDB blk)
                  , Eq (TxSeq (Validated (GenTx blk)))
                  ) => Eq (Model blk r)
deriving instance ( Show (TickedLedgerState blk ValuesMK)
                  , Show (MockLedgerDB blk)
                  , Show (Validated (GenTx blk))
                  ) => Show (Model blk r)

initModel :: Model blk r
initModel = NeedsInit

{-------------------------------------------------------------------------------
  Helpers
-------------------------------------------------------------------------------}

withOrigin' :: WithOrigin b -> b
withOrigin' = withOrigin undefined id
