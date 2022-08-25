{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Queries
module Ouroboros.Consensus.Storage.ChainDB.Impl.Query (
    -- * Queries
    getBlockComponent
  , getCurrentChain
  , getIsFetched
  , getIsInvalidBlock
  , getIsValid
  , getLedgerBackingStoreValueHandle
  , getLedgerDB
  , getLedgerStateForKeys
  , getMaxSlotNo
  , getTipBlock
  , getTipHeader
  , getTipPoint
    -- * Low-level queries
  , getAnyBlockComponent
  , getAnyKnownBlock
  , getAnyKnownBlockComponent
  ) where

import           Data.Functor (void)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import           Ouroboros.Network.AnchoredFragment (AnchoredFragment)
import qualified Ouroboros.Network.AnchoredFragment as AF
import           Ouroboros.Network.Block (MaxSlotNo, maxSlotNoFromWithOrigin)

import           Ouroboros.Consensus.Block
import           Ouroboros.Consensus.Config
import           Ouroboros.Consensus.Ledger.Basics
import           Ouroboros.Consensus.Ledger.Extended (ExtLedgerState)
import           Ouroboros.Consensus.Ledger.SupportsProtocol
                     (LedgerSupportsProtocol)
import           Ouroboros.Consensus.Protocol.Abstract
import           Ouroboros.Consensus.Util (StaticEither (..), eitherToMaybe)
import           Ouroboros.Consensus.Util.IOLike
import qualified Ouroboros.Consensus.Util.ResourceRegistry as RR
import           Ouroboros.Consensus.Util.STM (WithFingerprint (..))

import           Ouroboros.Consensus.Storage.ChainDB.API (BlockComponent (..),
                     ChainDbFailure (..), InvalidBlockReason)
import qualified Ouroboros.Consensus.Storage.ChainDB.Impl.LgrDB as LgrDB
import           Ouroboros.Consensus.Storage.ChainDB.Impl.Types
import           Ouroboros.Consensus.Storage.ImmutableDB (ImmutableDB)
import qualified Ouroboros.Consensus.Storage.ImmutableDB as ImmutableDB
import qualified Ouroboros.Consensus.Storage.LedgerDB.HD.BackingStore as BackingStore
import qualified Ouroboros.Consensus.Storage.LedgerDB.InMemory as LedgerDB
import qualified Ouroboros.Consensus.Storage.LedgerDB.OnDisk as LedgerDB
import           Ouroboros.Consensus.Storage.VolatileDB (VolatileDB)
import qualified Ouroboros.Consensus.Storage.VolatileDB as VolatileDB

-- | Return the last @k@ headers.
--
-- While the in-memory fragment ('cdbChain') might temporarily be longer than
-- @k@ (until the background thread has copied those blocks to the
-- ImmutableDB), this function will never return a fragment longer than @k@.
--
-- The anchor point of the returned fragment will be the most recent
-- \"immutable\" block, i.e. a block that cannot be rolled back. In
-- ChainDB.md, we call this block @i@.
--
-- Note that the returned fragment may be shorter than @k@ in case the whole
-- chain itself is shorter than @k@ or in case the VolatileDB was corrupted.
-- In the latter case, we don't take blocks already in the ImmutableDB into
-- account, as we know they /must/ have been \"immutable\" at some point, and,
-- therefore, /must/ still be \"immutable\".
getCurrentChain
  :: forall m blk wt.
     ( IOLike m
     , HasHeader (Header blk)
     , ConsensusProtocol (BlockProtocol blk)
     )
  => ChainDbEnv m blk wt
  -> STM m (AnchoredFragment (Header blk))
getCurrentChain CDB{..} =
    AF.anchorNewest k <$> readTVar cdbChain
  where
    SecurityParam k = configSecurityParam cdbTopLevelConfig

getLedgerDB ::
     IOLike m
  => ChainDbEnv m blk wt -> STM m (LgrDB.LedgerDB' blk wt)
getLedgerDB CDB{..} = LgrDB.getCurrent cdbLgrDB

getTipBlock
  :: forall m blk wt.
     ( IOLike m
     , HasHeader blk
     , HasHeader (Header blk)
     )
  => ChainDbEnv m blk wt
  -> m (Maybe blk)
getTipBlock cdb@CDB{..} = do
    tipPoint <- atomically $ getTipPoint cdb
    case pointToWithOriginRealPoint tipPoint of
      Origin      -> return Nothing
      NotOrigin p -> Just <$> getAnyKnownBlock cdbImmutableDB cdbVolatileDB p

getTipHeader
  :: forall m blk wt.
     ( IOLike m
     , HasHeader blk
     , HasHeader (Header blk)
     )
  => ChainDbEnv m blk wt
  -> m (Maybe (Header blk))
getTipHeader CDB{..} = do
    anchorOrHdr <- AF.head <$> atomically (readTVar cdbChain)
    case anchorOrHdr of
      Right hdr   -> return $ Just hdr
      Left anchor ->
        case pointToWithOriginRealPoint (castPoint (AF.anchorToPoint anchor)) of
          Origin      -> return Nothing
          NotOrigin p ->
            -- In this case, the fragment is empty but the anchor point is not
            -- genesis. It must be that the VolatileDB got emptied and that our
            -- current tip is now the tip of the ImmutableDB.

            -- Note that we can't use 'getBlockAtTip' because a block might have
            -- been appended to the ImmutableDB since we obtained 'anchorOrHdr'.
            Just <$> ImmutableDB.getKnownBlockComponent cdbImmutableDB GetHeader p

getTipPoint
  :: forall m blk wt. (IOLike m, HasHeader (Header blk))
  => ChainDbEnv m blk wt -> STM m (Point blk)
getTipPoint CDB{..} =
    castPoint . AF.headPoint <$> readTVar cdbChain

getBlockComponent ::
     forall m blk b wt. IOLike m
  => ChainDbEnv m blk wt
  -> BlockComponent blk b
  -> RealPoint blk -> m (Maybe b)
getBlockComponent CDB{..} = getAnyBlockComponent cdbImmutableDB cdbVolatileDB

getIsFetched ::
     forall m blk wt. IOLike m
  => ChainDbEnv m blk wt -> STM m (Point blk -> Bool)
getIsFetched CDB{..} = basedOnHash <$> VolatileDB.getIsMember cdbVolatileDB
  where
    -- The volatile DB indexes by hash only, not by points. However, it should
    -- not be possible to have two points with the same hash but different
    -- slot numbers.
    basedOnHash :: (HeaderHash blk -> Bool) -> Point blk -> Bool
    basedOnHash f p =
        case pointHash p of
          BlockHash hash -> f hash
          GenesisHash    -> False

getIsInvalidBlock ::
     forall m blk wt. (IOLike m, HasHeader blk)
  => ChainDbEnv m blk wt
  -> STM m (WithFingerprint (HeaderHash blk -> Maybe (InvalidBlockReason blk)))
getIsInvalidBlock CDB{..} =
  fmap (fmap (fmap invalidBlockReason) . flip Map.lookup) <$> readTVar cdbInvalid

getIsValid ::
     forall m blk wt. (IOLike m, HasHeader blk)
  => ChainDbEnv m blk wt
  -> STM m (RealPoint blk -> Maybe Bool)
getIsValid CDB{..} = do
    prevApplied <- LgrDB.getPrevApplied cdbLgrDB
    invalid     <- forgetFingerprint <$> readTVar cdbInvalid
    return $ \pt@(RealPoint _ hash) ->
      -- Blocks from the future that were valid according to the ledger but
      -- that exceeded the max clock skew will be in 'prevApplied' *and*
      -- 'invalid'. So we first check 'invalid' before 'prevApplied'. See
      -- #2413.
      if | Map.member hash invalid   -> Just False
         | Set.member pt prevApplied -> Just True
         | otherwise                 -> Nothing

getMaxSlotNo ::
     forall m blk wt. (IOLike m, HasHeader (Header blk))
  => ChainDbEnv m blk wt -> STM m MaxSlotNo
getMaxSlotNo CDB{..} = do
    -- Note that we need to look at both the current chain and the VolatileDB
    -- in all cases (even when the VolatileDB is not empty), because the
    -- VolatileDB might have been corrupted.
    --
    -- For example, imagine the VolatileDB has been corrupted so that it only
    -- contains block 9'. The ImmutableDB contains blocks 1-10. The max slot
    -- of the current chain will be 10 (being the anchor point of the empty
    -- current chain), while the max slot of the VolatileDB will be 9.
    curChainMaxSlotNo <- maxSlotNoFromWithOrigin . AF.headSlot
                     <$> readTVar cdbChain
    volatileDbMaxSlotNo    <- VolatileDB.getMaxSlotNo cdbVolatileDB
    return $ curChainMaxSlotNo `max` volatileDbMaxSlotNo

getLedgerStateForKeys :: forall m blk b a wt.
     ( IOLike m
     , LedgerSupportsProtocol blk
     , GetTip (LedgerState blk), TableStuff (LedgerTablesGADT (LedgerTables' (ExtLedgerState blk)) wt))
  => ChainDbEnv m blk wt
  -> StaticEither b () (Point blk)
  -> (ExtLedgerState blk -> m (a, LedgerTables (ExtLedgerState blk) wt KeysMK))
  -> m (StaticEither
         b
         (a, LedgerTables (ExtLedgerState blk) wt ValuesMK)
         (Maybe (a, LedgerTables (ExtLedgerState blk) wt ValuesMK))
       )
getLedgerStateForKeys CDB{..} seP m = LgrDB.withReadLock cdbLgrDB $ do
    ldb0 <- atomically $ LgrDB.getCurrent cdbLgrDB
    case seP of
      StaticLeft () -> StaticLeft <$> do
        (a, ks) <- m (LedgerDB.ledgerDbCurrent ldb0)
        finish a ks ldb0
      StaticRight p -> StaticRight <$> case LedgerDB.ledgerDbPrefix p ldb0 of
        Nothing  -> pure Nothing
        Just ldb -> Just <$> do
          (a, ks) <- m (LedgerDB.ledgerDbCurrent ldb)
          finish a ks ldb
  where
    finish ::
         a
      -> LedgerTables (ExtLedgerState blk) wt KeysMK
      -> LedgerDB.LedgerDB' blk wt
      -> m (a, LedgerTables (ExtLedgerState blk) wt ValuesMK)
    finish a ks ldb = (,) a <$> do
      let chlog :: DbChangelog (ExtLedgerState blk) wt
          chlog = LedgerDB.ledgerDbChangelog ldb

          rew :: LedgerDB.RewoundTableKeySets (ExtLedgerState blk) wt
          rew = LedgerDB.rewindTableKeySets chlog ks

      ufs <- LedgerDB.readKeySets (LgrDB.lgrBackingStore cdbLgrDB) rew
      let _ = ufs :: LedgerDB.UnforwardedReadSets (ExtLedgerState blk) wt
      case LedgerDB.forwardTableKeySets chlog ufs of
        Left err     -> error $ "getLedgerStateForKeys: rewind;read;forward failed " <> show err
        Right values -> pure values

getLedgerBackingStoreValueHandle :: forall b m blk wt.
     ( IOLike m
     , LedgerSupportsProtocol blk
     , GetTip (LedgerState blk), TableStuff (LedgerTablesGADT (LedgerTables' (ExtLedgerState blk)) wt))
  => ChainDbEnv m blk wt
  -> RR.ResourceRegistry m
  -> StaticEither b () (Point blk)
  -> m (StaticEither
         b
         ( LedgerDB.LedgerBackingStoreValueHandle m (ExtLedgerState blk) wt
         , LedgerDB.LedgerDB' blk wt
         , m ()
         )
         (Either
            (Point blk)
            ( LedgerDB.LedgerBackingStoreValueHandle m (ExtLedgerState blk) wt
            , LedgerDB.LedgerDB' blk wt
            , m ()
            )
         )
       )
getLedgerBackingStoreValueHandle CDB{..} rreg seP = LgrDB.withReadLock cdbLgrDB $ do
    ldb0 <- atomically $ LgrDB.getCurrent cdbLgrDB
    case seP of
      StaticLeft () -> StaticLeft  <$> finish ldb0
      StaticRight p -> StaticRight <$> case LedgerDB.ledgerDbPrefix p ldb0 of
        Nothing  -> pure $ Left $ castPoint $ getTip $ LedgerDB.ledgerDbAnchor ldb0
        Just ldb -> Right <$> finish ldb
  where
    finish ::
         LedgerDB.LedgerDB' blk wt
      -> m ( LedgerDB.LedgerBackingStoreValueHandle m (ExtLedgerState blk) wt
           , LedgerDB.LedgerDB' blk wt
           , m ()
           )
    finish ldb = do
      (key, (seqNo, vh)) <- RR.allocate
        rreg
        (\_key -> do
            let LedgerDB.LedgerBackingStore store =
                  LgrDB.lgrBackingStore cdbLgrDB
            BackingStore.bsValueHandle store
            -- TODO assert seqno is correct (b/c of lock)
        )
        (\(_seqNo, vh) -> BackingStore.bsvhClose vh)
      pure
        ( LedgerDB.LedgerBackingStoreValueHandle seqNo vh
        , ldb
        , void $ RR.release key
        )

{-------------------------------------------------------------------------------
  Unifying interface over the immutable DB and volatile DB, but independent
  of the ledger DB. These functions therefore do not require the entire
  Chain DB to have been initialized.
-------------------------------------------------------------------------------}

-- | Variant of 'getAnyBlockComponent' instantiated with 'GetBlock'.
getAnyKnownBlock ::
     forall m blk.
     ( IOLike m
     , HasHeader blk
     )
  => ImmutableDB m blk
  -> VolatileDB m blk
  -> RealPoint blk
  -> m blk
getAnyKnownBlock immutableDB volatileDB =
    getAnyKnownBlockComponent immutableDB volatileDB GetBlock

-- | Wrapper around 'getAnyBlockComponent' for blocks we know should exist.
--
-- If the block does not exist, this indicates disk failure.
getAnyKnownBlockComponent ::
     forall m blk b.
     ( IOLike m
     , HasHeader blk
     )
  => ImmutableDB m blk
  -> VolatileDB m blk
  -> BlockComponent blk b
  -> RealPoint blk
  -> m b
getAnyKnownBlockComponent immutableDB volatileDB blockComponent p = do
    mBlock <-
      mustExist p <$>
        getAnyBlockComponent immutableDB volatileDB blockComponent p
    case mBlock of
      Right b  -> return b
      Left err -> throwIO err

-- | Get a block component from either the immutable DB or volatile DB.
--
-- Returns 'Nothing' if the 'Point' is unknown.
-- Throws 'NoGenesisBlockException' if the 'Point' refers to the genesis block.
getAnyBlockComponent ::
     forall m blk b. IOLike m
  => ImmutableDB m blk
  -> VolatileDB m blk
  -> BlockComponent blk b
  -> RealPoint blk
  -> m (Maybe b)
getAnyBlockComponent immutableDB volatileDB blockComponent p = do
    -- Note: to determine whether a block is in the ImmutableDB, we can
    -- look at the slot of its tip, which we'll call @immTipSlot@. If the
    -- slot of the requested point > @immTipSlot@, then the block will not
    -- be in the ImmutableDB but in the VolatileDB. However, there is a
    -- race condition here: if between the time we got @immTipSlot@ and
    -- the time we look up the block in the VolatileDB the block was moved
    -- from the VolatileDB to the ImmutableDB, and it was deleted from the
    -- VolatileDB, we won't find the block, even though it is in the
    -- ChainDB.
    --
    -- Therefore, we first query the VolatileDB and if the block is not in
    -- it, then we can get @immTipSlot@ and compare it to the slot of the
    -- requested point. If the slot <= @immTipSlot@ it /must/ be in the
    -- ImmutableDB (no race condition here).
    mbVolatileB <- VolatileDB.getBlockComponent
                     volatileDB
                     blockComponent
                     hash
    case mbVolatileB of
      Just b -> return $ Just b
      Nothing    -> do
        -- ImmutableDB will throw an exception if we ask for a block past the tip
        immTipSlot <- atomically $ ImmutableDB.getTipSlot immutableDB
        if NotOrigin (realPointSlot p) > immTipSlot then
          -- It's not supposed to be in the ImmutableDB and the VolatileDB
          -- didn't contain it, so return 'Nothing'.
          return Nothing
        else
          eitherToMaybe <$>
            ImmutableDB.getBlockComponent immutableDB blockComponent p
  where
    hash = realPointHash p

mustExist :: RealPoint blk -> Maybe b -> Either (ChainDbFailure blk) b
mustExist p Nothing  = Left  $ ChainDbMissingBlock p
mustExist _ (Just b) = Right b
