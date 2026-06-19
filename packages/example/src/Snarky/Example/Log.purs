-- | A thin, monad-agnostic logging utility over colog. The app's logger is a
-- | plain value — `LogAction Effect Message` — carried in the `Env` (or handed
-- | to a subsystem directly), and these helpers apply it from any
-- | `MonadEffect` context (`Effect`, `Aff`, the manager's fibers, ...).
-- |
-- | No reader machinery, no app monad: a `LogAction` is just `msg -> m Unit`,
-- | so logging is `Log.logInfo logger "..."` wherever you hold the logger.
-- | Construct one from any colog action instantiated at `Effect` —
-- | e.g. `richMessageStdout` (coloured severity + UTC timestamp).
module Snarky.Example.Log
  ( Logger
  , logAt
  , logDebug
  , logInfo
  , logWarning
  , logError
  , severityFromTag
  ) where

import Prelude

import Colog (LogAction, Message, Msg(..), Severity(..), unLogAction)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)

-- | The application logger: a colog action over `Effect`.
type Logger = LogAction Effect Message

-- | Log `text` at an arbitrary `Severity` (the level-generic primitive the
-- | fixed-level helpers below are built on).
logAt :: forall m. MonadEffect m => Logger -> Severity -> String -> m Unit
logAt logger severity text = liftEffect $ unLogAction logger (Msg { severity, text })

logDebug :: forall m. MonadEffect m => Logger -> String -> m Unit
logDebug logger = logAt logger Debug

logInfo :: forall m. MonadEffect m => Logger -> String -> m Unit
logInfo logger = logAt logger Info

logWarning :: forall m. MonadEffect m => Logger -> String -> m Unit
logWarning logger = logAt logger Warning

logError :: forall m. MonadEffect m => Logger -> String -> m Unit
logError logger = logAt logger Error

-- | Parse a severity tag (as a colog logger renders it) back to a `Severity`;
-- | anything unrecognized is treated as `Info`.
severityFromTag :: String -> Severity
severityFromTag = case _ of
  "debug" -> Debug
  "warning" -> Warning
  "error" -> Error
  _ -> Info
