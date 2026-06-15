-- | The gossip wire protocol. Every message is a tagged JSON envelope
-- | `{ tag, body }` where `body` is the constructor's own JSON. Payloads are
-- | only `String` proofs (`wire`), statement strings, and content-address keys
-- | — never a witness, so the privacy boundary is structural.
module Snarky.Example.P2P.Protocol
  ( Msg(..)
  , encodeMsg
  , decodeMsg
  ) where

import Prelude

import Data.Either (Either(..))
import Data.List.NonEmpty as NEL
import Foreign (ForeignError(..), MultipleErrors)
import Simple.JSON (readJSON, writeJSON)

data Msg
  -- announce presence: peer id, role ("base"/"merge"), build fingerprint, and
  -- the proof keys I hold
  = Hello { peerId :: String, role :: String, fingerprint :: String, haveKeys :: Array String }
  -- one block's structure (leaf statements). Many blocks may coexist in a
  -- session (one per base prover); a block is identified by its root key.
  | BlockAnnounce { n :: Int, leafStmts :: Array { slot :: Int, stmt :: String } }
  -- a proof for this content-address key was produced by `by` (block-agnostic —
  -- keys are globally unique across blocks)
  | Have { key :: String, by :: String }
  -- soft claim of a node by its key (peerId + timestamp for tiebreak/TTL)
  | Claim { key :: String, peerId :: String, ts :: Number }
  -- please send me the proof for this key
  | Request { key :: String }
  -- here is the proof wire for this key
  | Deliver { key :: String, wire :: String }

encodeMsg :: Msg -> String
encodeMsg = case _ of
  Hello r -> env "hello" (writeJSON r)
  BlockAnnounce r -> env "block" (writeJSON r)
  Have r -> env "have" (writeJSON r)
  Claim r -> env "claim" (writeJSON r)
  Request r -> env "request" (writeJSON r)
  Deliver r -> env "deliver" (writeJSON r)
  where
  env tag body = writeJSON { tag, body }

decodeMsg :: String -> Either MultipleErrors Msg
decodeMsg s = do
  e :: { tag :: String, body :: String } <- readJSON s
  case e.tag of
    "hello" -> Hello <$> readJSON e.body
    "block" -> BlockAnnounce <$> readJSON e.body
    "have" -> Have <$> readJSON e.body
    "claim" -> Claim <$> readJSON e.body
    "request" -> Request <$> readJSON e.body
    "deliver" -> Deliver <$> readJSON e.body
    other -> Left (NEL.singleton (ForeignError ("unknown msg tag: " <> other)))
