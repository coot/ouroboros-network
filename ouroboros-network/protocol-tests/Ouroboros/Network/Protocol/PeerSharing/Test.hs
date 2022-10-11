{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE NamedFieldPuns    #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE PolyKinds         #-}

module Ouroboros.Network.Protocol.PeerSharing.Test where

import qualified Codec.Serialise as CBOR
import           Control.Monad.Class.MonadAsync (MonadAsync)
import           Control.Monad.Class.MonadST (MonadST)
import           Control.Monad.Class.MonadThrow (MonadCatch)
import           Control.Monad.IOSim (runSimOrThrow)
import           Control.Monad.ST (runST)
import           Control.Tracer (nullTracer)
import           Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as BL
import           Network.TypedProtocol.Codec (AnyMessage (..),
                     AnyMessageAndAgency (..), Codec (..), PeerHasAgency (..),
                     prop_codecM, prop_codec_splitsM)
import           Network.TypedProtocol.Proofs (TerminalStates (..), connect)
import           Ouroboros.Network.Channel (createConnectedChannels)
import           Ouroboros.Network.Driver.Limits (ProtocolSizeLimits (..))
import           Ouroboros.Network.Driver.Simple (runConnectedPeers)
import           Ouroboros.Network.Protocol.PeerSharing.Client
                     (peerSharingClientPeer)
import           Ouroboros.Network.Protocol.PeerSharing.Codec
                     (byteLimitsPeerSharing, codecPeerSharing)
import           Ouroboros.Network.Protocol.PeerSharing.Direct (direct)
import           Ouroboros.Network.Protocol.PeerSharing.Examples
                     (peerSharingClientCollect, peerSharingServerReplicate)
import           Ouroboros.Network.Protocol.PeerSharing.Server
                     (peerSharingServerPeer)
import           Ouroboros.Network.Protocol.PeerSharing.Type
                     (ClientHasAgency (..), Message (..), NobodyHasAgency (..),
                     PeerSharing, PeerSharingAmount (..), ServerHasAgency (..))
import           Test.Ouroboros.Network.Testing.Utils (prop_codec_cborM,
                     prop_codec_valid_cbor_encoding, splits2, splits3)
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.QuickCheck (Arbitrary (..), Property, ioProperty,
                     oneof, testProperty, withMaxSuccess, (===))

tests :: TestTree
tests =
  testGroup "Ouroboros.Network.Protocol"
    [ testGroup "PeerSharing"
        [ testProperty "direct"           prop_direct
        , testProperty "connect"          prop_connect
        , testProperty "channel ST"       prop_channel_ST
        , testProperty "channel IO"       prop_channel_IO
        , testProperty "codec"            prop_codec
        , testProperty "codec cbor"       prop_codec_cbor
        , testProperty "codec valid cbor" prop_codec_valid_cbor
        , testProperty "codec 2-splits"   prop_codec_splits2
        , testProperty "codec 3-splits"   (withMaxSuccess 33 prop_codec_splits3)
        , testProperty "byteLimits"       prop_byteLimits
        ]
    ]

instance Arbitrary PeerSharingAmount where
  arbitrary = PeerSharingAmount <$> arbitrary
  shrink (PeerSharingAmount amount) = PeerSharingAmount <$> shrink amount

--
-- Properties going directly, not via Peer.
--

prop_direct :: [PeerSharingAmount] -> Property
prop_direct l =
  runSimOrThrow
    (direct peerSharingServerReplicate
            (peerSharingClientCollect l))
  === foldl (\(n, r) amount -> (n + 1, replicate (fromIntegral amount) n ++ r))
            (0, [])
            l

--
-- Properties using connect
--

prop_connect :: [PeerSharingAmount] -> Property
prop_connect l =
   case runSimOrThrow
          (connect
            (peerSharingClientPeer (peerSharingClientCollect l))
            (peerSharingServerPeer peerSharingServerReplicate)) of
     (ns, n, TerminalStates TokDone TokDone) ->
       let lengthL = length l
           compute = foldl (\(x, r) amount
                              -> (x + 1, replicate (fromIntegral amount) x ++ r))
                           (0, [])
                           l
        in (ns, n) === (snd compute, lengthL)


--
-- Properties using channels, codecs and drivers.
--

prop_channel :: ( MonadST    m
                , MonadAsync m
                , MonadCatch m
                )
             => [PeerSharingAmount]
             -> m Property
prop_channel l = do
    (s, c) <- runConnectedPeers createConnectedChannels
                                nullTracer
                                codecPeerSharing
                                client server
    let lengthL = length l
        compute = foldl (\(x, r) amount
                           -> (x + 1, replicate (fromIntegral amount) x ++ r))
                        (0, [])
                        l
    return ((s, c) === (snd compute, lengthL))
  where
    client = peerSharingClientPeer (peerSharingClientCollect l)
    server = peerSharingServerPeer peerSharingServerReplicate

prop_channel_ST :: [PeerSharingAmount]
                -> Property
prop_channel_ST l =
  runSimOrThrow (prop_channel l)

prop_channel_IO :: [PeerSharingAmount]
                -> Property
prop_channel_IO l =
  ioProperty (prop_channel l)

--
-- Codec tests
--

instance Arbitrary peer => Arbitrary (AnyMessageAndAgency (PeerSharing peer)) where
  arbitrary = do
    amount <- arbitrary
    resp <- arbitrary
    oneof
      [ pure $ AnyMessageAndAgency (ClientAgency TokIdle) (MsgShareRequest amount)
      , pure $ AnyMessageAndAgency (ServerAgency TokBusy) (MsgSharePeers resp)
      , pure $ AnyMessageAndAgency (ClientAgency TokIdle) MsgDone
      ]

instance Eq peer => Eq (AnyMessage (PeerSharing peer)) where
    AnyMessage (MsgShareRequest amountA) == AnyMessage (MsgShareRequest amountB) = amountA == amountB
    AnyMessage (MsgSharePeers respA)     == AnyMessage (MsgSharePeers respB)     = respA   == respB
    AnyMessage MsgDone                   == AnyMessage MsgDone                   = True
    _ == _                                                                      = False

prop_codec :: AnyMessageAndAgency (PeerSharing Int)
           -> Bool
prop_codec msg =
  runST (prop_codecM codecPeerSharing msg)

prop_codec_cbor
  :: AnyMessageAndAgency (PeerSharing Int)
  -> Bool
prop_codec_cbor msg =
  runST (prop_codec_cborM codecPeerSharing msg)

prop_codec_valid_cbor :: AnyMessageAndAgency (PeerSharing Int) -> Property
prop_codec_valid_cbor = prop_codec_valid_cbor_encoding codecPeerSharing

-- | Check for data chunk boundary problems in the codec using 2 chunks.
--
prop_codec_splits2 :: AnyMessageAndAgency (PeerSharing Int) -> Bool
prop_codec_splits2 msg =
  runST (prop_codec_splitsM splits2 codecPeerSharing msg)

-- | Check for data chunk boundary problems in the codec using 3 chunks.
--
prop_codec_splits3 :: AnyMessageAndAgency (PeerSharing Int) -> Bool
prop_codec_splits3 msg =
  runST (prop_codec_splitsM splits3 codecPeerSharing msg)

prop_byteLimits :: AnyMessageAndAgency (PeerSharing Int)
                -> Bool
prop_byteLimits (AnyMessageAndAgency agency msg) =
        dataSize (encode agency msg)
     <= sizeLimitForState agency
  where
    Codec { encode } = codecPeerSharing :: Codec (PeerSharing Int) CBOR.DeserialiseFailure IO ByteString
    ProtocolSizeLimits { sizeLimitForState, dataSize } = byteLimitsPeerSharing (fromIntegral . BL.length)
