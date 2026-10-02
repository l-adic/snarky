module Pickles.CircuitDiffs.PureScript.ExpandPlonk
  ( compileExpandPlonkStep
  , compileExpandPlonkWrap
  ) where

import Prelude

import Data.Tuple.Nested (Tuple4, tuple4, uncurry4)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, domainLog2, stepEndo, wrapDomainLog2, wrapEndo)
import Pickles.Field (StepField, WrapField)
import Pickles.Linearization.FFI (domainGenerator)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, F, FVar, SizedF, Snarky, UnChecked(..), const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, mul_)
import Snarky.Circuit.Kimchi (toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

-- | `expand_plonk_{step,wrap}_circuit`'s input (OCaml `dump_circuit_impl.ml`): the four plonk
-- | challenges as 128-bit scalar challenges.
newtype ExpandPlonkInput f = ExpandPlonkInput
  { alpha :: SizedF 128 f
  , beta :: SizedF 128 f
  , gamma :: SizedF 128 f
  , zeta :: SizedF 128 f
  }

-- | The wire order.
type ExpandPlonkTuple f = Tuple4 (SizedF 128 f) (SizedF 128 f) (SizedF 128 f) (SizedF 128 f)

toTuple :: forall f. ExpandPlonkInput f -> ExpandPlonkTuple f
toTuple (ExpandPlonkInput i) = tuple4 i.alpha i.beta i.gamma i.zeta

fromTuple :: forall f. ExpandPlonkTuple f -> ExpandPlonkInput f
fromTuple = uncurry4 \alpha beta gamma zeta -> ExpandPlonkInput { alpha, beta, gamma, zeta }

instance CircuitType f fa fv => CircuitType f (ExpandPlonkInput fa) (ExpandPlonkInput fv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(ExpandPlonkTuple fa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(ExpandPlonkTuple fa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(ExpandPlonkTuple fa)

-- | Expand alpha then zeta through the endomorphism, beta and gamma untouched, then
-- | `zetaw = generator * zeta` at the side's constant domain generator.
-- |
-- | Layout only: the rows are the library's `toField` (the `EndoScalar` gadget the
-- | verifiers expand every challenge with), twice; the product with a constant
-- | generator folds to no row, as in the dump.
expandPlonkStepCircuit
  :: forall r
   . UnChecked (ExpandPlonkInput (FVar StepField))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
expandPlonkStepCircuit (UnChecked (ExpandPlonkInput i)) = do
  let endoVar = const_ stepEndo :: FVar StepField
  _alpha <- toField @8 i.alpha endoVar
  zeta <- toField @8 i.zeta endoVar
  void $ mul_ (const_ (domainGenerator @StepField domainLog2)) zeta

expandPlonkWrapCircuit
  :: forall r
   . UnChecked (ExpandPlonkInput (FVar WrapField))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
expandPlonkWrapCircuit (UnChecked (ExpandPlonkInput i)) = do
  let endoVar = const_ wrapEndo :: FVar WrapField
  _alpha <- toField @8 i.alpha endoVar
  zeta <- toField @8 i.zeta endoVar
  void $ mul_ (const_ (domainGenerator @WrapField wrapDomainLog2)) zeta

compileExpandPlonkStep :: Effect (CompiledCircuit StepField)
compileExpandPlonkStep =
  compile noAdvice (Proxy @(UnChecked (ExpandPlonkInput (F StepField)))) (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    expandPlonkStepCircuit

compileExpandPlonkWrap :: Effect (CompiledCircuit WrapField)
compileExpandPlonkWrap =
  compile noAdvice (Proxy @(UnChecked (ExpandPlonkInput (F WrapField)))) (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    expandPlonkWrapCircuit
