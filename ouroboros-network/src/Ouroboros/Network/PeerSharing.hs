{-# LANGUAGE NamedFieldPuns #-}

module Ouroboros.Network.PeerSharing where

import           Control.Concurrent.Class.MonadSTM.Strict (MonadSTM, StrictTVar,
                     atomically, modifyTVar, newTVarIO)
import           Control.Monad.Class.MonadMVar (MVar,
                     MonadMVar (newEmptyMVar, putMVar), takeMVar)
import           Control.Monad.Class.MonadThrow (MonadThrow, bracket)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Ouroboros.Network.Protocol.PeerSharing.Client
                     (PeerSharingClient (..))
import           Ouroboros.Network.Protocol.PeerSharing.Server
                     (PeerSharingServer (..))
import           Ouroboros.Network.Protocol.PeerSharing.Type (PeerSharingAmount)

data PeerSharingController peer m = PeerSharingController {
  requestQueue :: MVar m PeerSharingAmount,
  resultQueue  :: MVar m [peer]
}

newtype PeerSharingRegistry peer m = PeerSharingRegistry {
  getPeerSharingRegistry :: StrictTVar m (Map peer (PeerSharingController peer m))
}

newPeerSharingRegistry :: (MonadSTM m, Ord peer) => m (PeerSharingRegistry peer m)
newPeerSharingRegistry = PeerSharingRegistry <$> newTVarIO mempty

bracketPeerSharingClient :: (Ord peer, MonadSTM m, MonadThrow m, MonadMVar m)
                         => PeerSharingRegistry peer m
                         -> peer
                         -> (PeerSharingController peer m -> m a) -> m a
bracketPeerSharingClient (PeerSharingRegistry registry) peer k = do
  newPSController <- PeerSharingController <$> newEmptyMVar <*> newEmptyMVar
  bracket (atomically (modifyTVar registry (Map.insert peer newPSController)))
          (\_ -> atomically (modifyTVar registry (Map.delete peer)))
          (\_ -> k newPSController)

peerSharingClient :: MonadMVar m => PeerSharingController peer m -> m (PeerSharingClient peer m ())
peerSharingClient psc@PeerSharingController { requestQueue, resultQueue } = do
  amount <- takeMVar requestQueue
  return $
    SendMsgShareRequest amount $ \result -> do
      putMVar resultQueue result
      peerSharingClient psc


peerSharingServer :: Monad m
                  => (PeerSharingAmount -> m [peer])
                  -> PeerSharingServer peer m ()
peerSharingServer computePeersToShare =
  PeerSharingServer
    { recvMsgShareRequest = \amount -> do
        peers <- computePeersToShare amount
        return (peers, peerSharingServer computePeersToShare),
      recvMsgDone = return ()
    }
