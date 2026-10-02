module Pickles.CircuitDiffs.PureScript.Pow2Pow
  ( pow2PowCircuit
  , compilePow2Pow
  ) where

import Prelude

import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (StepField)
import Pickles.FinalizeOtherProof (pow2PowSquare)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F, FVar, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

pow2PowCircuit
  :: forall r
   . PrimeField StepField
  => FVar StepField
  -> Snarky StepField (KimchiConstraint StepField) r (FVar StepField)
pow2PowCircuit x = pow2PowSquare x 16

compilePow2Pow :: Effect (CompiledCircuit StepField)
compilePow2Pow =
  compile noAdvice (Proxy @(F StepField)) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (void <<< pow2PowCircuit)
