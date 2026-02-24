module Test.Pickles.TestLog
  ( TestLogMessage
  , RichMessage
  , TestM(..)
  , TestEnv
  , runTestM
  , defaultEnv
  , toRich
  , withContext
  , renderPretty
  ) where

import Prelude

import Colog.Core (class HasLog, LogAction(..), Severity(..), WithSeverity, logStringStderr)
import Control.Monad.Reader.Class (class MonadAsk, class MonadReader)
import Control.Monad.Reader.Trans (ReaderT(..), runReaderT)
import Data.Array as Array
import Data.Functor.Contravariant (cmap)
import Data.Lens (lens)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Foreign.Object (Object)
import Foreign.Object as Object

type RichMessage = { text :: String, context :: Object String }

type TestLogMessage = WithSeverity RichMessage

type TestEnv = { logger :: LogAction TestM TestLogMessage }

newtype TestM a = TestM (ReaderT TestEnv Aff a)

derive newtype instance Functor TestM
derive newtype instance Apply TestM
derive newtype instance Applicative TestM
derive newtype instance Bind TestM
derive newtype instance Monad TestM
derive newtype instance MonadEffect TestM
derive newtype instance MonadAff TestM
derive newtype instance MonadAsk TestEnv TestM
derive newtype instance MonadReader TestEnv TestM

instance HasLog TestEnv TestLogMessage TestM where
  logActionL = lens _.logger (_ { logger = _ })

runTestM :: forall a. TestEnv -> TestM a -> Aff a
runTestM env (TestM m) = runReaderT m env

toRich :: String -> RichMessage
toRich text = { text, context: Object.empty }

renderPretty :: TestLogMessage -> String
renderPretty { severity, msg } =
  let
    sevStr = case severity of
      Debug -> "Debug"
      Info -> "Info"
      Warning -> "Warn"
      Error -> "Error"
    ctxStr =
      if Object.isEmpty msg.context then ""
      else " " <> showContext msg.context
  in
    "[" <> sevStr <> "] " <> msg.text <> ctxStr
  where
  showContext :: Object String -> String
  showContext obj =
    let
      pairs :: Array (Tuple String String)
      pairs = Object.toUnfoldable obj
      showPair (Tuple k v) = show k <> ":" <> show v
    in
      "{" <> Array.intercalate ", " (map showPair pairs) <> "}"

defaultEnv :: TestEnv
defaultEnv = { logger: cmap renderPretty logStringStderr }

withContext :: forall a. String -> String -> TestM a -> TestM a
withContext key value (TestM m) = TestM $ ReaderT \env ->
  let
    addCtx :: LogAction TestM TestLogMessage -> LogAction TestM TestLogMessage
    addCtx (LogAction act) = LogAction \msg ->
      act (msg { msg = msg.msg { context = Object.insert key value msg.msg.context } })
    env' = env { logger = addCtx env.logger }
  in
    runReaderT m env'
