{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE NumericUnderscores         #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
-- |

module Test.Consensus.Mempool.Block where


import           Prelude hiding (elem)

import qualified Codec.CBOR.Decoding as CBOR
import qualified Codec.CBOR.Encoding as CBOR
import           Codec.Serialise (Serialise)
import qualified Codec.Serialise as S
import           Data.Foldable (toList)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.TreeDiff.Class (genericToExpr)
import           Data.TreeDiff.Expr (Expr (App))
import           Data.Word
import           GHC.Generics (Generic)

import           Test.QuickCheck
import           Test.StateMachine

import           Cardano.Binary (FromCBOR (..), ToCBOR (..))

import           Ouroboros.Consensus.Block
import           Ouroboros.Consensus.Config
import           Ouroboros.Consensus.Ledger.Abstract
import           Ouroboros.Consensus.Ledger.Extended
import           Ouroboros.Consensus.Util.IOLike

import qualified Ouroboros.Consensus.Storage.LedgerDB.HD as HD
import qualified Ouroboros.Consensus.Storage.LedgerDB.HD.DiffSeq as DS
import           Ouroboros.Consensus.Storage.LedgerDB.InMemory
import           Test.Util.TestBlock hiding (TestBlock, TestBlockCodecConfig,
                     TestBlockStorageConfig)

import Ouroboros.Network.Block
import Cardano.Slotting.Slot
import Ouroboros.Network.Point

import NoThunks.Class
import qualified Data.List.NonEmpty as NE

{-------------------------------------------------------------------------------
  TestBlock
-------------------------------------------------------------------------------}

type TestBlock = TestBlockWith Tx

-- | Mock of a UTxO transaction where exactly one (transaction) input is
-- consumed and exactly one output is produced.
--
data Tx = Tx {
    -- | Input that the transaction consumes.
    consumed :: Token
    -- | Ouptupt that the transaction produces.
  , produced :: (Token, TValue)
  }
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass (Serialise, NoThunks, ToExpr)

-- | A token is an identifier for the values produced and consumed by the
-- 'TestBlock' transactions.
--
-- This is analogous to @TxId@: it's how we identify what's in the table. It's
-- also analogous to @TxIn@, since we trivially only have one output per 'Tx'.
newtype Token = Token { unToken :: Word64 }
  deriving stock (Show, Eq, Ord, Generic)
  deriving newtype (Serialise, NoThunks, ToExpr)

instance Arbitrary Token where
  arbitrary = Token . fromIntegral <$> (arbitrary @Word16)

-- | Unit of value associated with the output produced by a transaction.
--
-- This is analogous to @TxOut@: it's what the table maps 'Token's to.
newtype TValue = TValue Word64
  deriving stock (Show, Eq, Ord, Generic)
  deriving newtype (Serialise, NoThunks, ToExpr)

instance Arbitrary TValue where
  arbitrary = TValue . fromIntegral <$> (arbitrary @Word16)

{-------------------------------------------------------------------------------
  A ledger semantics for TestBlock
-------------------------------------------------------------------------------}

data TxErr
  = TokenWasAlreadyCreated Token
  | TokenDoesNotExist      Token
  deriving stock (Generic, Eq, Show)
  deriving anyclass (NoThunks, Serialise, ToExpr)

instance PayloadSemantics Tx where
  data PayloadDependentState Tx mk =
    UTxTok { utxtoktables :: LedgerTables (LedgerState TestBlock) mk
             -- | All the tokens that ever existed. We use this to
             -- make sure a token is not created more than once. See
             -- the definition of 'applyPayload' in the
             -- 'PayloadSemantics' of 'Tx'.
           , utxhist      :: Set Token
           }
    deriving stock    (Generic)

  type PayloadDependentError Tx = TxErr

  -- We need to exercise the HD backend. This requires that we store key-values
  -- ledger tables and the block application semantics satisfy:
  --
  -- * a key is deleted at most once
  -- * a key is inserted at most once
  --
  applyPayload st Tx{consumed, produced} =
      fmap track $ delete consumed st >>= uncurry insert produced
    where
      insert ::
           Token
        -> TValue
        -> PayloadDependentState Tx ValuesMK
        -> Either TxErr (PayloadDependentState Tx ValuesMK)
      insert tok val st'@UTxTok{utxtoktables, utxhist} =
          if tok `Set.member` utxhist
          then Left  $ TokenWasAlreadyCreated tok
          else Right $ st' { utxtoktables = Map.insert tok val `onValues` utxtoktables
                           , utxhist      = Set.insert tok utxhist
                           }
      delete ::
           Token
        -> PayloadDependentState Tx ValuesMK
        -> Either TxErr (PayloadDependentState Tx ValuesMK)
      delete tok st'@UTxTok{utxtoktables} =
          if Map.member tok `queryKeys` utxtoktables
          then Right $ st' { utxtoktables = Map.delete tok `onValues` utxtoktables
                           }
          else Left  $ TokenDoesNotExist tok

      track :: PayloadDependentState Tx ValuesMK -> PayloadDependentState Tx TrackingMK
      track stAfter =
          stAfter { utxtoktables =
                      TokenToTValue $ rawCalculateDifference utxtokBefore utxtokAfter
                  }
        where
          utxtokBefore = testUtxtokTable $ utxtoktables st
          utxtokAfter  = testUtxtokTable $ utxtoktables stAfter

  getPayloadKeySets Tx{consumed} =
    TokenToTValue $ ApplyKeysMK $ DS.Keys $ Set.singleton consumed

deriving stock    instance (Eq        (PayloadDependentState Tx EmptyMK))
deriving stock    instance (Eq        (PayloadDependentState Tx DiffMK))
deriving stock    instance (Eq        (PayloadDependentState Tx ValuesMK))
deriving stock    instance (Show      (PayloadDependentState Tx (ApplyMapKind' mk)))
deriving anyclass instance (Serialise (PayloadDependentState Tx EmptyMK))
deriving anyclass instance (ToExpr    (PayloadDependentState Tx ValuesMK))
deriving anyclass instance (NoThunks  (PayloadDependentState Tx EmptyMK))
deriving anyclass instance (NoThunks  (PayloadDependentState Tx TrackingMK))
deriving anyclass instance (NoThunks  (PayloadDependentState Tx DiffMK))
deriving anyclass instance (NoThunks  (PayloadDependentState Tx ValuesMK))
deriving anyclass instance (NoThunks  (PayloadDependentState Tx SeqDiffMK))

onValues ::
     (Map Token TValue -> Map Token TValue)
  -> LedgerTables (LedgerState TestBlock) ValuesMK
  -> LedgerTables (LedgerState TestBlock) ValuesMK
onValues f TokenToTValue {testUtxtokTable} = TokenToTValue $ updateMap testUtxtokTable
  where
    updateMap :: ApplyMapKind ValuesMK Token TValue -> ApplyMapKind ValuesMK Token TValue
    updateMap (ApplyValuesMK (DS.Values utxovals)) =
      ApplyValuesMK $ DS.Values $ f utxovals

queryKeys ::
     (Map Token TValue -> a)
  -> LedgerTables (LedgerState TestBlock) ValuesMK
  -> a
queryKeys f (TokenToTValue (ApplyValuesMK (DS.Values utxovals))) = f utxovals

{-------------------------------------------------------------------------------
  Instances required for HD storage of ledger state tables
-------------------------------------------------------------------------------}

instance TableStuff (LedgerState TestBlock) where
  newtype LedgerTables (LedgerState TestBlock) mk =
    TokenToTValue { testUtxtokTable :: mk Token TValue }
    deriving stock (Generic)

  projectLedgerTables st       = utxtoktables $ payloadDependentState st
  withLedgerTables    st table = st { payloadDependentState =
                                        (payloadDependentState st) {utxtoktables = table}
                                    }

  pureLedgerTables = TokenToTValue

  mapLedgerTables      f                                     (TokenToTValue x) = TokenToTValue    (f x)
  traverseLedgerTables f                                     (TokenToTValue x) = TokenToTValue <$> f x
  zipLedgerTables      f                   (TokenToTValue x) (TokenToTValue y) = TokenToTValue    (f x y)
  zipLedgerTables2     f (TokenToTValue x) (TokenToTValue y) (TokenToTValue z) = TokenToTValue    (f x y z)
  zipLedgerTablesA     f                   (TokenToTValue x) (TokenToTValue y) = TokenToTValue <$> f x y
  zipLedgerTables2A    f (TokenToTValue x) (TokenToTValue y) (TokenToTValue z) = TokenToTValue <$> f x y z
  foldLedgerTables     f                                     (TokenToTValue x) =                   f x
  foldLedgerTables2    f                   (TokenToTValue x) (TokenToTValue y) =                   f x y
  namesLedgerTables                                                            = TokenToTValue $ NameMK "testblocktables"

deriving newtype  instance Eq       (LedgerTables (LedgerState TestBlock) EmptyMK)
deriving newtype  instance Eq       (LedgerTables (LedgerState TestBlock) DiffMK)
deriving newtype  instance Eq       (LedgerTables (LedgerState TestBlock) ValuesMK)
deriving newtype  instance Show     (LedgerTables (LedgerState TestBlock) (ApplyMapKind' mk))
deriving anyclass instance NoThunks (LedgerTables (LedgerState TestBlock) EmptyMK)
deriving anyclass instance NoThunks (LedgerTables (LedgerState TestBlock) ValuesMK)
deriving anyclass instance NoThunks (LedgerTables (LedgerState TestBlock) DiffMK)
deriving anyclass instance NoThunks (LedgerTables (LedgerState TestBlock) TrackingMK)
deriving anyclass instance NoThunks (LedgerTables (LedgerState TestBlock) SeqDiffMK)

instance SufficientSerializationForAnyBackingStore (LedgerState TestBlock) where
  codecLedgerTables = TokenToTValue $ CodecMK toCBOR toCBOR fromCBOR fromCBOR

instance Serialise (LedgerTables (LedgerState TestBlock) EmptyMK) where
  encode (TokenToTValue (_ :: EmptyMK Token TValue))
         = CBOR.encodeNull
  decode = TokenToTValue ApplyEmptyMK <$ CBOR.decodeNull

instance ToCBOR Token where
  toCBOR (Token pt) = S.encode pt

instance FromCBOR Token where
  fromCBOR = fmap Token S.decode

instance ToCBOR TValue where
  toCBOR (TValue v) = S.encode v

instance FromCBOR TValue where
  fromCBOR = fmap TValue S.decode

instance TickedTableStuff (LedgerState TestBlock) where
  projectLedgerTablesTicked (TickedTestLedger st)        = projectLedgerTables st
  withLedgerTablesTicked    (TickedTestLedger st) tables =
    TickedTestLedger $ withLedgerTables st tables

instance ShowLedgerState (LedgerTables (LedgerState TestBlock)) where
  showsLedgerState _sing = shows

instance StowableLedgerTables (LedgerState TestBlock) where
  stowLedgerTables     = stowErr "stowLedgerTables"
  unstowLedgerTables   = stowErr "unstowLedgerTables"

stowErr :: String -> a
stowErr fname = error $ "Function " <> fname <> " should not be used in these tests."

instance Show (ApplyMapKind' mk' Token TValue) where
  show ap = showsApplyMapKind ap ""

instance ToExpr (ApplyMapKind' mk' Token TValue) where
  toExpr ApplyEmptyMK                 = App "ApplyEmptyMK"     []
  toExpr (ApplyDiffMK diffs)          = App "ApplyDiffMK"      [genericToExpr diffs]
  toExpr (ApplyKeysMK keys)           = App "ApplyKeysMK"      [genericToExpr keys]
  toExpr (ApplySeqDiffMK (DS.UnsafeDiffSeq seqdiff))
                                      = App "ApplySeqDiffMK"   [genericToExpr $ toList seqdiff]
  toExpr (ApplyTrackingMK vals diffs) = App "ApplyTrackingMK"  [ genericToExpr vals
                                                               , genericToExpr diffs
                                                               ]
  toExpr (ApplyValuesMK vals)         = App "ApplyValuesMK"    [genericToExpr vals]
  toExpr ApplyQueryAllMK              = App "ApplyQueryAllMK"  []
  toExpr (ApplyQuerySomeMK keys)      = App "ApplyQuerySomeMK" [genericToExpr keys]

-- About this instance: we have that the use of
--
-- > genericToExpr UtxoDiff
--
-- in instance ToExpr (ApplyMapKind mk Token TValue) requires
--
-- >  ToExpr Map k (UtxoEntryDiff v )
--
-- requires
--
-- > ToExpr (UtxoEntryDiff v )
--
-- requires
--
-- > ToExpr UtxoEntryDiffState
--
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

instance ToExpr (ExtLedgerState TestBlock ValuesMK) where
  toExpr = genericToExpr

instance ToExpr (LedgerState (TestBlockWith Tx) ValuesMK) where
  toExpr = genericToExpr


instance ToExpr (LedgerTables (LedgerState TestBlock) ValuesMK) where
  toExpr = genericToExpr

{-------------------------------------------------------------------------------
 -------------------------------------------------------------------------------}

initialPDS :: Gen (PayloadDependentState Tx ValuesMK)
initialPDS = do
  m <- arbitrary `suchThat` (not . Map.null)
  pure $ UTxTok {
    utxtoktables = TokenToTValue . ApplyValuesMK . DS.Values $ m
  , utxhist      = Map.keysSet m
  }

utxoMap :: PayloadDependentState Tx ValuesMK -> Map Token TValue
utxoMap (UTxTok (TokenToTValue (ApplyValuesMK (DS.Values tbs))) _) = tbs

nextPDS :: PayloadDependentState Tx ValuesMK -> Gen (PayloadDependentState Tx ValuesMK)
nextPDS pds@(UTxTok _ hist) = do
  m <- arbitrary `suchThat` (\x -> (not $ Map.null x) && (Set.null . Set.intersection hist . Map.keysSet $ x))
  n <- Map.fromList <$> (sublistOf (Map.toList $ utxoMap pds) `suchThat` (not . null))
  let
  pure $ UTxTok {
      utxtoktables = TokenToTValue . ApplyValuesMK . DS.Values $ m `Map.union` n
    , utxhist = hist `Set.union` Map.keysSet m
    }

initialState :: Gen (LedgerState TestBlock ValuesMK)
initialState = TestLedger (Point Origin) <$> initialPDS

nextRandomState :: LedgerState TestBlock ValuesMK -> Gen (LedgerState TestBlock ValuesMK)
nextRandomState (TestLedger lap pds) = do
  let sl = SlotNo $ withOrigin 1 ((+1) . unSlotNo) (pointSlot lap) :: SlotNo
  -- Use a fixed testhash, we don't care about it
  let lap' = Point (At (Block sl (TestHash $ 0 NE.:| [])))
  TestLedger lap' <$> nextPDS pds

genSucceedingTransaction :: LedgerState TestBlock ValuesMK -> Gen Tx
genSucceedingTransaction (TestLedger _ pds) = do
  consume <- elements $ Set.toList $ Map.keysSet $ utxoMap pds
  producedKey <- arbitrary `suchThat` (flip notElem $ utxhist pds)
  producedValue <- arbitrary
  pure $ Tx consume (producedKey, producedValue)

-- | TODO: for the time being 'TestBlock' does not have any codec config
data instance CodecConfig TestBlock = TestBlockCodecConfig
  deriving (Show, Generic, NoThunks)

-- | TODO: for the time being 'TestBlock' does not have any storage config
data instance StorageConfig TestBlock = TestBlockStorageConfig
  deriving (Show, Generic, NoThunks)
