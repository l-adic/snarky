module Pickles.CircuitDiffs.PureScript.StepVerifyN2
  ( compileStepVerifyN2
  ) where

-- | Step_verifier.verify circuit with N2 (2 previous proofs): `step_verify_circuit`'s
-- | pipeline, the per-proof witness carrying two previous challenge vectors and `sg`s, the
-- | `sg`s the `sg_old` bases.

import Prelude

import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.CircuitDiffs.PureScript.PerProofWitness (PerProofWitnessInput(..))
import Pickles.CircuitDiffs.PureScript.StepVerify (StepVerifyInput(..), StepVerifyParams, stepVerifyBody)
import Pickles.Field (StepField)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (BoolVar, F, FVar, Snarky, UnChecked(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

stepVerifyN2Circuit
  :: forall r
   . StepVerifyParams
  -> UnChecked (StepVerifyInput 2 (FVar StepField) (BoolVar StepField) (AffinePoint (FVar StepField)))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
stepVerifyN2Circuit params (UnChecked input@(StepVerifyInput i)) =
  let
    PerProofWitnessInput witness = i.witness
  in
    stepVerifyBody params witness.prevSgs input

compileStepVerifyN2 :: StepVerifyParams -> Effect (CompiledCircuit StepField)
compileStepVerifyN2 srsData =
  compile noAdvice
    (Proxy @(UnChecked (StepVerifyInput 2 (F StepField) Boolean (AffinePoint StepField))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    (stepVerifyN2Circuit srsData)
