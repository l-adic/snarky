-- | Where the snark worker threads send their logs. A worker shares the host's
-- | stdout, where a live progress tree is pinned, so it must never write to the
-- | console (that would corrupt the display). Instead every worker appends to
-- | this one shared file — `richMessageFile` is a synchronous, line-atomic
-- | append (`fs.appendFileSync`), so concurrent workers interleave cleanly.
-- | `tail -f` it to watch SRS build + lagrange + compile progress per worker.
module Snarky.Example.Terminal.WorkerLog
  ( workerLogPath
  , workerLogger
  ) where

import Colog (richMessageFile)
import Snarky.Example.Log (Logger)

-- | The shared worker-log file, relative to the run's cwd (the repo root).
workerLogPath :: String
workerLogPath = "snark-worker.log"

-- | Timestamped, plain-text (no ANSI) file logger over `workerLogPath`.
workerLogger :: Logger
workerLogger = richMessageFile workerLogPath
