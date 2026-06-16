-- | The star worker-pool dispatch protocol: the four messages a coordinator and
-- | its worker peers exchange over a `Transport`. This replaces #148's 6-variant
-- | decentralized gossip vocabulary (Hello/BlockAnnounce/Have/Claim/Request/
-- | Deliver) — there is no claim/TTL/DAG here, only a hub assigning jobs.
-- |
-- |   * `Join`   worker → coordinator: "I am available" (broadcast on startup
-- |              and whenever a peer is discovered). `fingerprint` lets the
-- |              coordinator reject a peer built against an incompatible circuit.
-- |   * `Assign` coordinator → worker: "prove this" (`work` = `encodeWorkItem`).
-- |   * `Result` worker → coordinator: "here is the proof" (`proof` =
-- |              `encodeCompiledProof`).
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
  , fingerprint
  ) where

import Prelude

import Data.Either (Either(..))
import Foreign (ForeignError(..), MultipleErrors)
import Simple.JSON (readJSON, writeJSON)

data Msg
  = Join { peerId :: String, fingerprint :: String }
  | Assign { jobId :: String, work :: String }
  | Result { jobId :: String, proof :: String }
  | Reject { jobId :: String, reason :: String }
  | Leave { peerId :: String }

-- | A coarse build/circuit-compatibility tag. v1 uses a fixed constant shared by
-- | both ends (the coordinator drops a `Join` whose fingerprint differs); a
-- | later version can derive it from the compiled verification key so peers on a
-- | stale build are turned away rather than producing unverifiable proofs.
fingerprint :: String
fingerprint = "snarky-p2p-star-v1"

-- | Serialize a message: a `tag` field plus the variant's own fields. The
-- | decoder reads the tag first, then the matching shape (extra fields ignored).
encodeMsg :: Msg -> String
encodeMsg = case _ of
  Join r -> writeJSON { tag: "join", peerId: r.peerId, fingerprint: r.fingerprint }
  Assign r -> writeJSON { tag: "assign", jobId: r.jobId, work: r.work }
  Result r -> writeJSON { tag: "result", jobId: r.jobId, proof: r.proof }
  Reject r -> writeJSON { tag: "reject", jobId: r.jobId, reason: r.reason }
  Leave r -> writeJSON { tag: "leave", peerId: r.peerId }

decodeMsg :: String -> Either MultipleErrors Msg
decodeMsg s = do
  tagged <- readJSON s :: Either MultipleErrors { tag :: String }
  case tagged.tag of
    "join" -> readJSON s <#> \(r :: { peerId :: String, fingerprint :: String }) -> Join r
    "assign" -> readJSON s <#> \(r :: { jobId :: String, work :: String }) -> Assign r
    "result" -> readJSON s <#> \(r :: { jobId :: String, proof :: String }) -> Result r
    "reject" -> readJSON s <#> \(r :: { jobId :: String, reason :: String }) -> Reject r
    "leave" -> readJSON s <#> \(r :: { peerId :: String }) -> Leave r
    other -> Left (pure (ForeignError ("Msg: unknown tag " <> other)))
