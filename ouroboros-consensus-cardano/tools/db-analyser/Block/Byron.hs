{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TypeFamilies      #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Block.Byron (
    Args (..)
  , ByronBlockArgs
  , openGenesisByron
  ) where

import           Control.Monad.Except
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import           Data.Foldable (asum, toList)
import qualified Data.Map as Map
import           Data.Maybe (mapMaybe)
import           Options.Applicative

import           Cardano.Binary (Raw, serialize', unAnnotated)

import           Cardano.Crypto (RequiresNetworkMagic (..))
import qualified Cardano.Crypto as Crypto

import qualified Cardano.Chain.Block as Chain
import qualified Cardano.Chain.Genesis as Genesis
import qualified Cardano.Chain.UTxO as Chain
import qualified Cardano.Chain.Update as Update

import           Ouroboros.Consensus.Block (IsEBB (..))
import qualified Ouroboros.Consensus.Mempool.TxLimits as TxLimits
import           Ouroboros.Consensus.Node.ProtocolInfo

import           Ouroboros.Consensus.Byron.Ledger (ByronBlock)
import qualified Ouroboros.Consensus.Byron.Ledger as Byron
import           Ouroboros.Consensus.Byron.Node (PBftSignatureThreshold (..),
                     ProtocolParamsByron (..), protocolInfoByron)

import           HasAnalysis

instance HasAnalysis ByronBlock where
    countTxOutputs = aBlockOrBoundary (const 0) countTxOutputsByron
    extractTxOutputIdDelta = aBlockOrBoundary (const (IsEBB, 0, [], [])) extractTxOutputIdDeltaByron
    genesisTxOutputIds st =
        (Map.size txs, txOutputIds)
      where
        utxo :: Chain.UTxO
        utxo = Chain.cvsUtxo $ Byron.byronLedgerState st

        txs =
          Map.fromListWith (Map.unionWith (error "collision!"))
          $ [ (h, Map.singleton i $ toEnum $ BS.length $ serialize' txout)
            | (txin, txout) <- Map.toList $ Chain.unUTxO utxo
            , let TxIn h i = cnvTxIn $ Chain.fromCompactTxIn txin
            ]

        txOutputIds :: [TxOutputIds]
        txOutputIds =
            map (\(h, m) -> TxOutputIds h (Map.elems m))
          $ Map.toList txs
    blockTxSizes = aBlockOrBoundary (const []) blockTxSizesByron
    knownEBBs = const Byron.knownEBBs
    emitTraces _ = []

instance HasProtocolInfo ByronBlock where
    data Args ByronBlock =
      ByronBlockArgs {
          configFileByron      :: FilePath
        , requiresNetworkMagic :: RequiresNetworkMagic
        , genesisHash          :: Maybe (Crypto.Hash Raw)
        , threshold            :: Maybe PBftSignatureThreshold
        }
    argsParser _ = parseByronArgs
    mkProtocolInfo ByronBlockArgs {..} = do
      config <- openGenesisByron configFileByron genesisHash requiresNetworkMagic
      return $ mkByronProtocolInfo config threshold

type ByronBlockArgs = Args ByronBlock

parseByronArgs :: Parser ByronBlockArgs
parseByronArgs = ByronBlockArgs
    <$> strOption (mconcat [
            long "configByron"
          , help "Path to config file"
          , metavar "PATH"
          ])
    <*> flag RequiresNoMagic RequiresMagic (mconcat [
            long "requires-magic"
          , help "The DB contains blocks from a testnet, requiring network magic, rather than mainnet"
          ])
    <*> parseMaybe (option auto (mconcat [
            long "genesisHash"
          , help "Expected genesis hash"
          , metavar "HASH"
          ]))
    <*> parseMaybe (PBftSignatureThreshold <$> thresholdParser)
  where
    thresholdParser = option auto (mconcat [
            long "threshold"
          , help "PBftSignatureThreshold"
          , metavar "THRESHOLD"
          ])

parseMaybe ::  Parser a -> Parser (Maybe a)
parseMaybe parser = asum [Just <$> parser, pure Nothing]

-- | Equivalent of 'either' for 'ABlockOrBoundary'.
aBlockOrBoundary :: (Chain.ABoundaryBlock ByteString -> a)
                 -> (Chain.ABlock ByteString -> a)
                 -> ByronBlock -> a
aBlockOrBoundary fromBoundary fromRegular blk = case blk of
    Byron.ByronBlock (Chain.ABOBBoundary boundaryBlock) _ _
      -> fromBoundary boundaryBlock
    Byron.ByronBlock (Chain.ABOBBlock regularBlk) _ _
      -> fromRegular regularBlk

countTxOutputsByron :: Chain.ABlock ByteString -> Int
countTxOutputsByron Chain.ABlock{..} = countTxPayload bodyTxPayload
  where
    Chain.ABody { bodyTxPayload } = blockBody

    countTxPayload :: Chain.ATxPayload a -> Int
    countTxPayload = sum
                   . map (countTx . unAnnotated . Chain.aTaTx)
                   . Chain.aUnTxPayload

    countTx :: Chain.Tx -> Int
    countTx = length . Chain.txOutputs

extractTxOutputIdDeltaByron :: Chain.ABlock ByteString -> (IsEBB, Int, [TxIn], [TxOutputIds])
extractTxOutputIdDeltaByron Chain.ABlock{..} =
    ( IsNotEBB
    , length txs
    , foldMap  inputs  txs
    , mapMaybe outputs txs
    )
  where
    Chain.ABody { bodyTxPayload } = blockBody

    txs :: [Chain.ATxAux ByteString]
    txs = Chain.aUnTxPayload bodyTxPayload

    inputs :: Chain.ATxAux ByteString -> [TxIn]
    inputs atx =
        map cnvTxIn $ toList $ Chain.txInputs tx
      where
        tx = unAnnotated $ Chain.aTaTx atx

    outputs :: Chain.ATxAux ByteString -> Maybe TxOutputIds
    outputs atx =
        mkTxOutputIds (Crypto.abstractHashToShort txid) lens
      where
        txid = Crypto.hashDecoded $ Chain.aTaTx $ atx
        lens =
            map (toEnum . BS.length . serialize')
          $ toList
          $ Chain.txOutputs $ unAnnotated $ Chain.aTaTx atx

cnvTxIn :: Chain.TxIn -> TxIn
cnvTxIn (Chain.TxInUtxo txid nat) =
    TxIn (Crypto.abstractHashToShort txid) (fromInteger $ toInteger nat)

blockTxSizesByron :: Chain.ABlock ByteString -> [SizeInBytes]
blockTxSizesByron block =
    map (fromIntegral . BL.length . BL.fromStrict . Chain.aTaAnnotation) blockTxAuxs
  where
    Chain.ABlock{ blockBody } = block
    Chain.ABody{ bodyTxPayload } = blockBody
    Chain.ATxPayload{ aUnTxPayload = blockTxAuxs } = bodyTxPayload

openGenesisByron ::
     FilePath
  -> Maybe (Crypto.Hash Raw)
  -> RequiresNetworkMagic
  -> IO Genesis.Config
openGenesisByron configFile mHash requiresNetworkMagic = do
    genesisHash <- case mHash of
      Nothing -> either (error . show) return =<< runExceptT
        (Genesis.unGenesisHash . snd <$> Genesis.readGenesisData configFile)
      Just hash -> return hash
    genesisConfig <- either (error . show) return =<< runExceptT
      (Genesis.mkConfigFromFile
        requiresNetworkMagic
        configFile
        genesisHash)
    return genesisConfig

mkByronProtocolInfo :: Genesis.Config
                    -> Maybe PBftSignatureThreshold
                    -> ProtocolInfo IO ByronBlock
mkByronProtocolInfo genesisConfig signatureThreshold =
    protocolInfoByron $ ProtocolParamsByron {
        byronGenesis                = genesisConfig
      , byronPbftSignatureThreshold = signatureThreshold
      , byronProtocolVersion        = Update.ProtocolVersion 1 0 0
      , byronSoftwareVersion        = Update.SoftwareVersion (Update.ApplicationName "db-analyser") 2
      , byronLeaderCredentials      = Nothing
      , byronMaxTxCapacityOverrides = TxLimits.mkOverrides TxLimits.noOverridesMeasure
      }
