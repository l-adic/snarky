module Pickles.CircuitDiffs.PureScript.StepMainSimpleChainN2
  ( compileStepMainSimpleChainN2
  , StepMainSimpleChainN2Params
  ) where

-- | step_main circuit for the Simple_Chain N2 rule (2 previous proofs).
-- | Delegates to the generic Pickles.Step.Main.stepMain.
-- |
-- | Reference: mina/src/lib/crypto/pickles/dump_circuit_impl.ml (step_main_simple_chain_n2)

import Prelude

import Data.Vector ((:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyWrapSg)
import Pickles.PublicInputCommit (LagrangeBase)
import Pickles.Step.Main (RuleOutput, advice, compileStepMain)
import Pickles.Types (StepField)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, assertAny_, const_, equals_, exists, not_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Data.EllipticCurve (AffinePoint)

type StepMainSimpleChainN2Params =
  { lagrangeComms :: Array (LagrangeBase StepField)
  , blindingH :: AffinePoint (F StepField)
  }

-- | Simple_Chain N2 rule: self_correct = (1 + prev1 + prev2 == self)
-- | Both proofs have the same proof_must_verify = not is_base_case.
-- | Reference: dump_circuit_impl.ml:4533-4566
simpleChainN2Rule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => FVar StepField
  -> Snarky (KimchiConstraint StepField) t m (RuleOutput 2 StepField)
simpleChainN2Rule appState = do
  prev1 <- exists (advice :: _ (F StepField))
  -- proof1 = exists (Typ.prover_value ()) — no circuit effect
  prev2 <- exists (advice :: _ (F StepField))
  -- proof2 = exists (Typ.prover_value ()) — no circuit effect
  isBaseCase <- equals_ (const_ zero) appState
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (CVar.add_ (const_ one) prev1) prev2) appState
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev1 :< prev2 :< Vector.nil
    , proofMustVerify: proofMustVerify :< proofMustVerify :< Vector.nil
    }

compileStepMainSimpleChainN2 :: StepMainSimpleChainN2Params -> CompiledCircuit StepField
compileStepMainSimpleChainN2 params =
  compileStepMain @2 @67 simpleChainN2Rule params dummyWrapSg
