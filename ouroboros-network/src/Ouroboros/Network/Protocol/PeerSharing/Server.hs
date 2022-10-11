{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE RecordWildCards #-}

module Ouroboros.Network.Protocol.PeerSharing.Server where

import           Network.TypedProtocol.Core (Peer (..), PeerHasAgency (..),
                     PeerRole (..))
import           Ouroboros.Network.Protocol.PeerSharing.Type
                     (ClientHasAgency (..), Message (..), NobodyHasAgency (..),
                     PeerSharing (..), PeerSharingAmount, ServerHasAgency (..))

data PeerSharingServer peerAddress m a = PeerSharingServer {
  -- | The client sent us a 'MsgShareRequest'. We have need to compute the
  -- response.
  --
  recvMsgShareRequest :: PeerSharingAmount
                      -> m ( [peerAddress]
                           , PeerSharingServer peerAddress m a),

  -- | The client terminated. We can perform some action in 'm' if needed.
  --
  recvMsgDone :: m a
  }

peerSharingServerPeer :: Monad m
                      => PeerSharingServer peerAddress m a
                      -> Peer (PeerSharing peerAddress) AsServer StIdle m a
peerSharingServerPeer PeerSharingServer{..} =
  -- Await receival of a message from the client
  Await (ClientAgency TokIdle) $ \msg ->
    -- Can be either 'MsgShareRequest' or 'MsgDone'
    case msg of
      -- Compute the response and send 'MsgSharePeers' message
      MsgShareRequest amount -> Effect $ do
        (resp, server) <- recvMsgShareRequest amount
        return $
          Yield (ServerAgency TokBusy)
                (MsgSharePeers resp)
                (peerSharingServerPeer server)
      -- Nothing to do.
      MsgDone -> Effect $ Done TokDone <$> recvMsgDone
