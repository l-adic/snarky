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
    { keys, phasesRef, txsRef, scansRef, verifiedRef } <- liftEffect do
      { ledger: l0, keys } <- randomSampleOne (genGenesisLedger 10)
      Ref.write l0 env.ledger
      phasesRef <- Ref.new ([] :: Array String)
      txsRef <- Ref.new ([] :: Array TxView)
      scansRef <- Ref.new 0
      verifiedRef <- Ref.new (Nothing :: Maybe Boolean)
      pure { keys, phasesRef, txsRef, scansRef, verifiedRef }
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
    { phases, txs, scans, verified } <- liftEffect do
      phases <- Ref.read phasesRef
      txs <- Ref.read txsRef
      scans <- Ref.read scansRef
      verified <- Ref.read verifiedRef
      pure { phases, txs, scans, verified }
    phases `shouldEqual` [ "block", "proving", "done" ]
    (Array.length txs > 0) `shouldEqual` true
    (scans > 0) `shouldEqual` true
    verified `shouldEqual` Just true
