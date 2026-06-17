-- | Abstract peer transport. The gossip `Node` speaks only this interface, so
-- | the same mesh logic runs over any signaling/connectivity backend:
-- |   * BroadcastChannel — same-origin, same-browser multi-tab (also the
-- |     headless test vehicle); zero infra.
-- |   * manual SDP        — a single WebRTC data channel wired by copy-paste;
-- |     zero infra, 2 peers, cross-machine.
-- |   * Trystero          — WebRTC mesh discovered over public Nostr/trackers;
-- |     cross-machine, many peers.
-- |
-- | A `Transport` is a JS object `{ myId, broadcast, sendTo, onMessage, onPeer }`;
-- | these are the typed accessors.
module Snarky.Example.P2P.Transport
  ( Transport
  , TransportImpl
  , fromImpl
  , myId
  , broadcast
  , sendTo
  , onMessage
  , onPeer
  , onPeerLeave
  ) where

import Prelude

import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, runEffectFn2)

-- | Opaque handle constructed by a backend's JS (`mkBroadcastTransport`, …).
foreign import data Transport :: Type

-- | A PureScript-side implementation of the transport interface — the same five
-- | operations the JS factories provide, but as ordinary PureScript functions.
-- | `fromImpl` wraps one into a `Transport`, so an in-memory transport (e.g. a
-- | test bus connecting several nodes in one process) can be built without any
-- | JS factory. The accessors below work on it identically.
type TransportImpl =
  { myId :: String
  , broadcast :: String -> Effect Unit
  , sendTo :: String -> String -> Effect Unit
  , onMessage :: (String -> String -> Effect Unit) -> Effect Unit
  , onPeer :: (String -> Effect Unit) -> Effect Unit
  , onPeerLeave :: (String -> Effect Unit) -> Effect Unit
  }

-- | Build a `Transport` from a PureScript implementation (adapts the curried
-- | `Effect` functions to the JS object the accessors expect).
foreign import fromImpl :: TransportImpl -> Transport

foreign import _myId :: Transport -> String
foreign import _broadcast :: EffectFn2 Transport String Unit
foreign import _sendTo :: EffectFn2 Transport { peer :: String, msg :: String } Unit
foreign import _onMessage :: EffectFn2 Transport (EffectFn2 String String Unit) Unit
foreign import _onPeer :: EffectFn2 Transport (EffectFn1 String Unit) Unit
foreign import _onPeerLeave :: EffectFn2 Transport (EffectFn1 String Unit) Unit

-- | This peer's stable id within the room.
myId :: Transport -> String
myId = _myId

-- | Send a raw message string to every connected peer.
broadcast :: Transport -> String -> Effect Unit
broadcast = runEffectFn2 _broadcast

-- | Send a raw message string to one peer.
sendTo :: Transport -> String -> String -> Effect Unit
sendTo t peer msg = runEffectFn2 _sendTo t { peer, msg }

-- | Register the `(fromPeerId, raw) -> Effect Unit` message handler.
onMessage :: Transport -> (String -> String -> Effect Unit) -> Effect Unit
onMessage t f = runEffectFn2 _onMessage t (mkHandler2 f)

-- | Register the peer-joined handler (fires once the channel to a peer opens).
onPeer :: Transport -> (String -> Effect Unit) -> Effect Unit
onPeer t f = runEffectFn2 _onPeer t (mkHandler1 f)

-- | Register the peer-left handler (fires when a peer's connection drops —
-- | natively for the WebRTC transports; never for BroadcastChannel, which has no
-- | connection and relies on the cooperative `Leave` message instead).
onPeerLeave :: Transport -> (String -> Effect Unit) -> Effect Unit
onPeerLeave t f = runEffectFn2 _onPeerLeave t (mkHandler1 f)

foreign import mkHandler2 :: (String -> String -> Effect Unit) -> EffectFn2 String String Unit
foreign import mkHandler1 :: (String -> Effect Unit) -> EffectFn1 String Unit
