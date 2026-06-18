-- | The wire protocol between a prover Web Worker and the main thread, as a single
-- | typed sum instead of ad-hoc `{ tag, value }` / `{ _t, … }` objects decoded with
-- | `unsafeFromForeign`. Two families travel the same `postMessage` channel:
-- |
-- |   * UI events  — the engine/peer callbacks the worker reports (`tag` + `value`);
-- |   * transport  — the worker's bridged transport relaying a `broadcast`/`send`
-- |                  back onto the main-thread transport (`_t` + `msg`/`peer`).
-- |
-- | `encodeWorkerMsg`/`decodeWorkerMsg` are pure `Foreign` codecs (no browser), so
-- | the round-trip is unit-testable in Node. The browser worker encodes with these;
-- | the main thread decodes with `decodeWorkerMsg`.
module Snarky.Example.P2P.WorkerMsg
  ( WorkerMsg(..)
  , encodeWorkerMsg
  , decodeWorkerMsg
  ) where

import Prelude

import Data.Either (hush)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Foreign (Foreign, unsafeToForeign)
import Simple.JSON (class ReadForeign, read)
import Snarky.Example.Engine (ScanView, TxView)
import Snarky.Example.P2P.Coordinator (PeerView)
import Snarky.Example.P2P.Types (Frame(..), PeerId(..))

-- | A message from a prover worker to the main thread.
data WorkerMsg
  -- UI events (the engine / peer callbacks):
  = WLog { severity :: String, text :: String }
  | WPhase String
  | WTxs (Array TxView)
  | WScan ScanView
  | WVerified Boolean
  | WPeers (Array PeerView)
  -- Transport relay (the worker's bridged transport → the main transport):
  | WBroadcast Frame
  | WSend PeerId Frame

derive instance Eq WorkerMsg
derive instance Generic WorkerMsg _
instance Show WorkerMsg where
  show = genericShow

-- | The flat envelope on the wire. The two families have disjoint fields, so every
-- | field is optional (`read` accepts whichever shape arrives).
type Envelope =
  { "_t" :: Maybe String
  , tag :: Maybe String
  , value :: Maybe Foreign
  , msg :: Maybe String
  , peer :: Maybe String
  }

-- | Build the wire object for a worker message.
encodeWorkerMsg :: WorkerMsg -> Foreign
encodeWorkerMsg = case _ of
  WLog v -> event "log" (unsafeToForeign v)
  WPhase p -> event "phase" (unsafeToForeign p)
  WTxs txs -> event "txs" (unsafeToForeign txs)
  WScan s -> event "scan" (unsafeToForeign s)
  WVerified b -> event "verified" (unsafeToForeign b)
  WPeers ps -> event "peers" (unsafeToForeign ps)
  WBroadcast (Frame f) -> unsafeToForeign { "_t": "broadcast", msg: f }
  WSend (PeerId p) (Frame f) -> unsafeToForeign { "_t": "send", peer: p, msg: f }
  where
  event tag value = unsafeToForeign { tag, value }

-- | Parse a wire object into a worker message (`Nothing` if malformed / unknown).
decodeWorkerMsg :: Foreign -> Maybe WorkerMsg
decodeWorkerMsg f = do
  m <- hush (read f) :: Maybe Envelope
  case m."_t" of
    Just "broadcast" -> WBroadcast <<< Frame <$> m.msg
    Just "send" -> WSend <$> (PeerId <$> m.peer) <*> (Frame <$> m.msg)
    _ -> case m.tag of
      Just "log" -> WLog <$> decodeValue m
      Just "phase" -> WPhase <$> decodeValue m
      Just "txs" -> WTxs <$> decodeValue m
      Just "scan" -> WScan <$> decodeValue m
      Just "verified" -> WVerified <$> decodeValue m
      Just "peers" -> WPeers <$> decodeValue m
      _ -> Nothing
  where
  decodeValue :: forall a. ReadForeign a => Envelope -> Maybe a
  decodeValue m = m.value >>= (hush <<< read)
