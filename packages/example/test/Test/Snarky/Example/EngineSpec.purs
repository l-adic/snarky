-- | The one-block engine pipeline (`Snarky.Example.Engine.runEngine`) run in Node,
-- | with REAL proofs but no browser. We build a `Simulation` from the shared suite
-- | `Env` (reuse the compiled program — no recompile) over the in-process
-- | `localSnarkBackend`, capture the `EngineCallbacks` events, and assert the whole
-- | coordinator behavior the headless browser used to be the only check for: the
-- | phase sequence, the block's transactions surfaced, the scan tree advancing,
-- | and the root proof verifying.
module Test.Snarky.Example.EngineSpec
  ( spec
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Snarky.Example.Engine (TxView, engineOnProgress, runEngine)
import Snarky.Example.Env (Env)
import Snarky.Example.Simulation (genGenesisLedger)
import Snarky.Example.Snark.Manager (mkManager)
import Snarky.Example.Snark.Pool (PoolSize(Fixed))
import Snarky.Example.Snark.Worker (localSnarkBackend)
import Test.QuickCheck.Gen (randomSampleOne)
import Test.Snarky.Example.Config (Depth)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT Aff (Env Depth) Aff Unit
spec = describe "Snarky.Example.Engine" do
  it "runs a one-block pipeline to a verified root in Node, emitting the event sequence" \env -> do
    -- A Simulation from the shared Env: seed the genesis ledger into the env's ref
    -- and start a manager over the in-process local backend. Same shape as
    -- `mkSimulation`, minus the (already-done) SRS build + compile.
    { ledger: l0, keys } <- liftEffect $ randomSampleOne (genGenesisLedger 10)
    liftEffect $ Ref.write l0 env.ledger

    phasesRef <- liftEffect $ Ref.new ([] :: Array String)
    txsRef <- liftEffect $ Ref.new ([] :: Array TxView)
    scansRef <- liftEffect $ Ref.new 0
    verifiedRef <- liftEffect $ Ref.new (Nothing :: Maybe Boolean)
    let
      cb =
        { onLog: \_ -> pure unit
        , onPhase: \p -> Ref.modify_ (\xs -> Array.snoc xs p) phasesRef
        , onTxs: \txs -> Ref.write txs txsRef
        , onScan: \_ -> Ref.modify_ (_ + 1) scansRef
        , onVerified: \ok -> Ref.write (Just ok) verifiedRef
        }
    manager <- mkManager
      { logger: env.logger
      , onProgress: Just (engineOnProgress cb)
      , poolSize: Fixed 1
      , jobTimeout: Milliseconds 120000.0
      , backend: localSnarkBackend
      }
      env
    runEngine { env, keys, manager } cb

    -- The full event protocol fired in order, the block's transactions surfaced,
    -- the scan tree advanced as the manager proved, and the root proof verified.
    liftEffect (Ref.read phasesRef) >>= \ps -> ps `shouldEqual` [ "block", "proving", "done" ]
    liftEffect (Ref.read txsRef) >>= \txs -> (Array.length txs > 0) `shouldEqual` true
    liftEffect (Ref.read scansRef) >>= \n -> (n > 0) `shouldEqual` true
    liftEffect (Ref.read verifiedRef) >>= \v -> v `shouldEqual` Just true
