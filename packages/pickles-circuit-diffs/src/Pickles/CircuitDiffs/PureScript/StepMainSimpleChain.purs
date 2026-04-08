module Pickles.CircuitDiffs.PureScript.StepMainSimpleChain
  ( compileStepMainSimpleChain
  , StepMainSimpleChainParams
  ) where

-- | step_main circuit for the Simple_Chain inductive rule (N1, 1 previous proof).
-- | Delegates to the generic Pickles.Step.Main.stepMain.
-- |
-- | Reference: mina/src/lib/crypto/pickles/dump_circuit_impl.ml (step_main_simple_chain)

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

type StepMainSimpleChainParams =
  { lagrangeComms :: Array (LagrangeBase StepField)
  , blindingH :: AffinePoint (F StepField)
  }

-- | Simple_Chain N1 rule: self_correct = (1 + prev == self)
-- | Reference: dump_circuit_impl.ml:4390-4413
simpleChainRule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => FVar StepField
  -> Snarky (KimchiConstraint StepField) t m (RuleOutput 1 StepField)
simpleChainRule appState = do
  prev <- exists (advice :: _ (F StepField))
  -- proof = exists (Typ.prover_value ()) — no circuit effect
  isBaseCase <- equals_ (const_ zero) appState
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) appState
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev :< Vector.nil
    , proofMustVerify: proofMustVerify :< Vector.nil
    }

compileStepMainSimpleChain :: StepMainSimpleChainParams -> CompiledCircuit StepField
compileStepMainSimpleChain params =
  compileStepMain @1 @34 simpleChainRule params dummyWrapSg
