{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Ouroboros.Network.Protocol.PeerSharing.Examples where

import           Ouroboros.Network.Protocol.PeerSharing.Client
                     (PeerSharingClient (..))
import           Ouroboros.Network.Protocol.PeerSharing.Server
                     (PeerSharingServer (..))
import           Ouroboros.Network.Protocol.PeerSharing.Type (PeerSharingAmount)


-- | A client which collects answers whenever it receives
-- 'MsgSharePeers' and returns the result.
--
peerSharingClientCollect :: forall peer m . Monad m
                         => [PeerSharingAmount]
                         -> PeerSharingClient peer m [peer]
peerSharingClientCollect = go []
  where
    go :: [peer] -> [PeerSharingAmount] -> PeerSharingClient peer m [peer]
    go acc []    = SendMsgDone (pure acc)
    go acc (h:t) = SendMsgShareRequest h (\r -> return (go (r ++ acc) t))


-- | A server which counts number received of 'MsgKeepAlive'.
--
peerSharingServerReplicate :: forall m . Monad m
                           => PeerSharingServer Int m Int
peerSharingServerReplicate = go 0
  where
    go :: Int -> PeerSharingServer Int m Int
    go n =
      PeerSharingServer
        { recvMsgShareRequest = \ amount -> do
            let r = replicate (fromIntegral amount) n
            return (r, go (n + 1)),
          recvMsgDone = pure n
        }
