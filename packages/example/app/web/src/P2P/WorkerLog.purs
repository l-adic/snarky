-- | A colog `Logger` for a prover worker: each message is forwarded to the
-- | worker's host as a `WorkerMsg` `WLog` (via the shared `post`). Used by both
-- | prover workers — the peer worker's host is the main thread (rendered by
-- | `P2P.Main`), and the coordinator's nested prover's host is the coordinator
-- | worker (relayed to its UI by `P2P.Backend`). This lets `buildProver`'s
-- | env-init logging (SRS build, circuit compile) and the worker's per-job
-- | logging share the same typed wire protocol as every other worker→host event.
module Snarky.Example.Web.P2P.WorkerLog
  ( mkPostLogger
  ) where

import Prelude

import Colog (LogAction(..), Msg(..), Severity(..))
import Effect (Effect)
import Snarky.Example.Log (Logger)
import Snarky.Example.P2P.WorkerMsg (WorkerMsg(WLog), encodeWorkerMsg)
import Snarky.Example.Web.P2P.Post (post)

severityLabel :: Severity -> String
severityLabel = case _ of
  Debug -> "debug"
  Info -> "info"
  Warning -> "warning"
  Error -> "error"

mkPostLogger :: Effect Logger
mkPostLogger = pure $ LogAction \(Msg { severity, text }) ->
  post (encodeWorkerMsg (WLog { severity: severityLabel severity, text }))
