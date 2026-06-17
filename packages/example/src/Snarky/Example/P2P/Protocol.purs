-- | The star worker-pool dispatch protocol: the messages a coordinator and its
-- | worker peers exchange over a `Transport`.
-- |
-- |   * `Join`   worker → coordinator: "I am available" (broadcast on startup
-- |              and whenever a peer is discovered).
-- |   * `Assign` coordinator → worker: "prove this" (`work` = an encoded job).
-- |   * `Result` worker → coordinator: "here is the proof" (`proof` = an encoded
-- |              proof).
-- |   * `Reject` worker → coordinator: "I could not do it" (decode/prove failed).
-- |   * `Leave`  worker → coordinator: "I am going away" (broadcast on page
-- |              unload) so the coordinator drops it and reassigns its in-flight
-- |              job at once, rather than waiting out the job timeout.
-- |
-- | `jobId` correlates an `Assign` with its `Result`/`Reject`; it is the
-- | coordinator's transport-level id, independent of the snark manager's slot id.
module Snarky.Example.P2P.Protocol
  ( Msg(..)
  , encodeMsg
  , decodeMsg
  ) where

import Prelude

import Data.Either (Either(..))
import Foreign (ForeignError(..), MultipleErrors)
import Safe.Coerce (coerce)
import Simple.JSON (readJSON, writeJSON)
import Snarky.Example.P2P.Types (Frame(..), JobId(..), Payload(..), PeerId(..))

data Msg
  = Join { peerId :: PeerId }
  | Assign { jobId :: JobId, work :: Payload }
  | Result { jobId :: JobId, proof :: Payload }
  | Reject { jobId :: JobId, reason :: String }
  | Leave { peerId :: PeerId }

-- | Serialize a message: a `tag` field plus the variant's own fields. The
-- | decoder reads the tag first, then the matching shape (extra fields ignored).
encodeMsg :: Msg -> Frame
encodeMsg = Frame <<< case _ of
  Join r -> writeJSON { tag: "join", peerId: coerce r.peerId :: String }
  Assign r -> writeJSON { tag: "assign", jobId: coerce r.jobId :: String, work: coerce r.work :: String }
  Result r -> writeJSON { tag: "result", jobId: coerce r.jobId :: String, proof: coerce r.proof :: String }
  Reject r -> writeJSON { tag: "reject", jobId: coerce r.jobId :: String, reason: r.reason }
  Leave r -> writeJSON { tag: "leave", peerId: coerce r.peerId :: String }

decodeMsg :: Frame -> Either MultipleErrors Msg
decodeMsg (Frame s) = do
  tagged <- readJSON s :: Either MultipleErrors { tag :: String }
  case tagged.tag of
    "join" -> readJSON s <#> \(r :: { peerId :: String }) -> Join { peerId: coerce r.peerId }
    "assign" -> readJSON s <#> \(r :: { jobId :: String, work :: String }) -> Assign { jobId: coerce r.jobId, work: coerce r.work }
    "result" -> readJSON s <#> \(r :: { jobId :: String, proof :: String }) -> Result { jobId: coerce r.jobId, proof: coerce r.proof }
    "reject" -> readJSON s <#> \(r :: { jobId :: String, reason :: String }) -> Reject { jobId: coerce r.jobId, reason: r.reason }
    "leave" -> readJSON s <#> \(r :: { peerId :: String }) -> Leave { peerId: coerce r.peerId }
    other -> Left (pure (ForeignError ("Msg: unknown tag " <> other)))
