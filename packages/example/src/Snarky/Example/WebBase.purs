-- | Browser base-prover for the privacy split: the client generates its own
-- | block of transactions and proves the per-transaction BASE proofs LOCALLY —
-- | the private transaction witnesses never leave the device. It then ships
-- | only the proofs + public statements (`encodeLeaf`) to the server, which
-- | merges them into a verified block root. This is the privacy-preserving
-- | inverse of `Snarky.Example.Server` (server base) / `WebMerge` (client merge).
module Snarky.Example.WebBase
  ( baseMain
  ) where

import Prelude

import Colog (LogAction(..), Msg(..), Severity(..))
import Data.Array as Array
import Data.Traversable (sequence)
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Effect.Class (liftEffect)
import Mina.ChainId (ChainId(..))
import Pickles.Prove.SerializeProof (toSerializableCompiledProof)
import Snarky.Example.Block (processBlock)
import Snarky.Example.Env (mkEnv)
import Snarky.Example.Log as Log
import Snarky.Example.Merge (Depth)
import Snarky.Example.Simulation (generateBlock)
import Snarky.Example.Simulation.Genesis (genGenesisLedger)
import Snarky.Example.Snark.LeafCodec (encodeLeaf)
import Snarky.Example.SrsCache (buildCachedConfig)
import Test.QuickCheck.Gen (randomSampleOne)

-- | A base proof finished locally (its heap leaf slot, for the tree UI).
foreign import postLeaf :: { total :: Int, slot :: Int } -> Effect Unit
foreign import postStatus :: String -> Effect Unit
-- | One structured log line to the page (clean severity + text, no ANSI /
-- | timestamps — the page tags severity itself).
foreign import postLog :: { severity :: String, text :: String } -> Effect Unit

severityLabel :: Severity -> String
severityLabel = case _ of
  Debug -> "debug"
  Info -> "info"
  Warning -> "warning"
  Error -> "error"
-- | POST { n, leaves } to the server's /merge endpoint; resolves to whether
-- | the server's merged root verified.
foreign import _postBaseProofs :: Int -> Array String -> EffectFnAff Boolean

postBaseProofs :: Int -> Array String -> Aff Boolean
postBaseProofs n leaves = fromEffectFnAff (_postBaseProofs n leaves)

baseMain :: Effect Unit
baseMain = launchAff_ do
  -- The rayon thread pool is initialized by the worker JS (initThreadPool)
  -- before this entry runs; nothing to do here.
  -- Structured logger (same shape as the full-app engine): emit clean
  -- {severity, text} to the page instead of colog's ANSI rich stdout.
  let logger = LogAction \(Msg { severity, text }) -> postLog { severity: severityLabel severity, text }
  liftEffect $ postStatus "building SRS (lagrange cache) + compiling…"
  config <- buildCachedConfig Testnet
  env <- liftEffect $ mkEnv @Depth logger config

  { ledger, keys } <- liftEffect $ randomSampleOne (genGenesisLedger 10)
  block <- liftEffect $ generateBlock env.chainId keys ledger
  { snarkWork } <- liftEffect $ processBlock env.chainId ledger block
  let n = Array.length snarkWork

  Log.logInfo logger $ "[WebBase] proving " <> show n <> " base proofs locally (private inputs stay on-device)…"
  liftEffect $ postStatus ("proving " <> show n <> " base proofs locally…")
  leaves <- liftEffect $ sequence $ Array.mapWithIndex
    ( \j job -> do
        proof <- env.compiledTx.baseProver
          { env: { mask: job.mask, tx: job.tx }, statement: job.statement }
        postLeaf { total: n, slot: n + j }
        pure (encodeLeaf (toSerializableCompiledProof proof))
    )
    snarkWork

  liftEffect $ postStatus "sending proofs to server for merging…"
  Log.logInfo logger "[WebBase] base proofs done; POSTing to server /merge…"
  accepted <- postBaseProofs n leaves
  liftEffect do
    Log.logInfo logger $
      if accepted then "[WebBase] server merged + verified the block root ✓"
      else "[WebBase] server reported verification FAILURE"
    postStatus (if accepted then "server merged + verified root" else "server verification failed")
