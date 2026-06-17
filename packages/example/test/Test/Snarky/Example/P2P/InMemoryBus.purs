-- | An in-process message bus that hands out `Transport`s — the test stand-in
-- | for BroadcastChannel / WebRTC / trystero. Several nodes connect to one bus in
-- | a single Node process; `broadcast`/`sendTo` route messages between them
-- | synchronously, and `onPeer` fires as nodes appear (existing nodes are told of
-- | a newcomer; the newcomer replays existing peers when it registers its
-- | handler — the same presence model the real transports use).
-- |
-- | `connect`/`disconnect` are the levers for participation scenarios:
-- |   * late join  — `connect` a node after the coordinator is already running;
-- |   * quit       — `disconnect` a node: it then neither sends nor receives;
-- |   * rejoin     — `connect` again.
-- | A disconnected node's `Transport` goes inert (its `broadcast`/`sendTo` become
-- | no-ops and it receives nothing), so a dropped peer can't keep talking.
module Test.Snarky.Example.P2P.InMemoryBus
  ( Bus
  , newBus
  , connect
  , disconnect
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Snarky.Example.P2P.Transport (Transport, fromImpl)

type Node =
  { id :: String
  , onMsg :: Ref (Maybe (String -> String -> Effect Unit))
  , onPeer :: Ref (Maybe (String -> Effect Unit))
  }

newtype Bus = Bus (Ref (Array Node))

newBus :: Effect Bus
newBus = Bus <$> Ref.new []

-- | Connect a node by id and get its `Transport`.
connect :: Bus -> String -> Effect Transport
connect (Bus ref) self = do
  onMsgRef <- Ref.new Nothing
  onPeerRef <- Ref.new Nothing
  -- announce the newcomer to the already-connected nodes
  existing <- Ref.read ref
  for_ existing \n -> Ref.read n.onPeer >>= \h -> for_ h \fn -> fn self
  Ref.modify_ (\ns -> Array.snoc ns { id: self, onMsg: onMsgRef, onPeer: onPeerRef }) ref
  let
    connected from = Ref.read ref <#> Array.any (\n -> n.id == from)
    callMsg from msg n = Ref.read n.onMsg >>= \h -> for_ h \fn -> fn from msg
    deliver from keep msg = do
      live <- connected from -- a disconnected node can't send
      when live do
        ns <- Ref.read ref
        for_ ns \n -> when (n.id /= from && keep n.id) (callMsg from msg n)
  pure $ fromImpl
    { myId: self
    , broadcast: \msg -> deliver self (const true) msg
    , sendTo: \peer msg -> deliver self (_ == peer) msg
    , onMessage: \fn -> Ref.write (Just fn) onMsgRef
    , onPeer: \fn -> do
        Ref.write (Just fn) onPeerRef
        ns <- Ref.read ref
        for_ ns \n -> when (n.id /= self) (fn n.id)
    }

-- | Disconnect a node (simulate a quit): its `Transport` goes inert.
disconnect :: Bus -> String -> Effect Unit
disconnect (Bus ref) self = Ref.modify_ (Array.filter (\n -> n.id /= self)) ref
