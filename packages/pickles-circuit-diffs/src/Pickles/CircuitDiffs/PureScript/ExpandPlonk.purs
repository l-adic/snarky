module Pickles.CircuitDiffs.PureScript.ExpandPlonk
  ( compileExpandPlonkStep
  , compileExpandPlonkWrap
  ) where

import Prelude

import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, domainLog2, stepEndo, unsafeIdx, wrapDomainLog2, wrapEndo)
import Pickles.Field (StepField, WrapField)
import Pickles.Linearization.FFI (domainGenerator)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F, FVar, Snarky, const_, mul_)
import Snarky.Circuit.Kimchi (toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

-- | `expand_plonk_{step,wrap}_circuit` (OCaml `dump_circuit_impl.ml`): alpha at 0 and
-- | zeta at 3 as 128-bit scalar challenges, beta and gamma at 1-2 untouched. Expand
-- | alpha then zeta through the endomorphism, then `zetaw = generator * zeta` at the
-- | side's constant domain generator.
-- |
-- | Layout only: the rows are the library's `toField` (the `EndoScalar` gadget the
-- | verifiers expand every challenge with), twice; the product with a constant
-- | generator folds to no row, as in the dump.
expandPlonkStepCircuit
  :: forall r
   . Vector 4 (FVar StepField)
  -> Snarky StepField (KimchiConstraint StepField) r Unit
expandPlonkStepCircuit inputs = do
  let
    at = unsafeIdx inputs
    endoVar = const_ stepEndo :: FVar StepField
  _alpha <- toField @8 (asSizedF128 (at 0)) endoVar
  zeta <- toField @8 (asSizedF128 (at 3)) endoVar
  void $ mul_ (const_ (domainGenerator @StepField domainLog2)) zeta

expandPlonkWrapCircuit
  :: forall r
   . Vector 4 (FVar WrapField)
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
expandPlonkWrapCircuit inputs = do
  let
    at = unsafeIdx inputs
    endoVar = const_ wrapEndo :: FVar WrapField
  _alpha <- toField @8 (asSizedF128 (at 0)) endoVar
  zeta <- toField @8 (asSizedF128 (at 3)) endoVar
  void $ mul_ (const_ (domainGenerator @WrapField wrapDomainLog2)) zeta

compileExpandPlonkStep :: Effect (CompiledCircuit StepField)
compileExpandPlonkStep =
  compile noAdvice (Proxy @(Vector 4 (F StepField))) (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    expandPlonkStepCircuit

compileExpandPlonkWrap :: Effect (CompiledCircuit WrapField)
compileExpandPlonkWrap =
  compile noAdvice (Proxy @(Vector 4 (F WrapField))) (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    expandPlonkWrapCircuit
