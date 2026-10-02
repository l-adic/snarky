module Pickles.CircuitDiffs.PureScript.PlonkChecksPassed
  ( compilePlonkChecksPassedStep
  , compilePlonkChecksPassedWrap
  ) where

import Prelude

import Data.Tuple.Nested (Tuple8, tuple8, uncurry8)
import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (StepField, WrapField)
import Pickles.PlonkChecks (permScalarCircuit)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, F, FVar, Snarky, UnChecked(..), genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, pow_)
import Snarky.Circuit.Kimchi (Type1, Type2, shiftedEqualType1, shiftedEqualType2)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

-- | `plonk_checks_passed_{step,wrap}_circuit`'s input (OCaml `dump_circuit_impl.ml`): the
-- | claimed perm is a Type1 (step) or Type2 (wrap) shifted value. `sigma` and `w` are the
-- | first six columns' evaluations at zeta.
newtype PlonkChecksPassedInput f s = PlonkChecksPassedInput
  { alpha :: f
  , beta :: f
  , gamma :: f
  , zkPolynomial :: f
  , zOmega :: f
  , sigma :: Vector 6 f
  , w :: Vector 6 f
  , claimedPerm :: s
  }

-- | The wire order.
type PlonkChecksPassedTuple f s = Tuple8 f f f f f (Vector 6 f) (Vector 6 f) s

toTuple :: forall f s. PlonkChecksPassedInput f s -> PlonkChecksPassedTuple f s
toTuple (PlonkChecksPassedInput i) =
  tuple8 i.alpha i.beta i.gamma i.zkPolynomial i.zOmega i.sigma i.w i.claimedPerm

fromTuple :: forall f s. PlonkChecksPassedTuple f s -> PlonkChecksPassedInput f s
fromTuple = uncurry8 \alpha beta gamma zkPolynomial zOmega sigma w claimedPerm ->
  PlonkChecksPassedInput { alpha, beta, gamma, zkPolynomial, zOmega, sigma, w, claimedPerm }

instance
  ( CircuitType f fa fv
  , CircuitType f sa sv
  ) =>
  CircuitType f (PlonkChecksPassedInput fa sa) (PlonkChecksPassedInput fv sv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(PlonkChecksPassedTuple fa sa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(PlonkChecksPassedTuple fa sa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(PlonkChecksPassedTuple fa sa)

-- | `alpha^21` is computed by `pow_` as the dump does, then the library's `permScalarCircuit`
-- | (the verifiers' perm scalar).
permScalarOf
  :: forall f s r
   . PrimeField f
  => PlonkChecksPassedInput (FVar f) s
  -> Snarky f (KimchiConstraint f) r (FVar f)
permScalarOf (PlonkChecksPassedInput i) = do
  alphaPow21 <- pow_ i.alpha 21
  permScalarCircuit
    { w: i.w
    , sigma: i.sigma
    , zOmega: i.zOmega
    , beta: i.beta
    , gamma: i.gamma
    , zkPolynomial: i.zkPolynomial
    , alphaPow21
    }

-- | The perm scalar against the claim, through the library's shifted equality.
plonkChecksPassedStepCircuit
  :: forall r
   . UnChecked (PlonkChecksPassedInput (FVar StepField) (Type1 (FVar StepField)))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
plonkChecksPassedStepCircuit (UnChecked input@(PlonkChecksPassedInput i)) = do
  actual <- permScalarOf input
  void $ shiftedEqualType1 i.claimedPerm actual

plonkChecksPassedWrapCircuit
  :: forall r
   . UnChecked (PlonkChecksPassedInput (FVar WrapField) (Type2 (FVar WrapField)))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
plonkChecksPassedWrapCircuit (UnChecked input@(PlonkChecksPassedInput i)) = do
  actual <- permScalarOf input
  void $ shiftedEqualType2 i.claimedPerm actual

compilePlonkChecksPassedStep :: Effect (CompiledCircuit StepField)
compilePlonkChecksPassedStep =
  compile noAdvice (Proxy @(UnChecked (PlonkChecksPassedInput (F StepField) (Type1 (F StepField)))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    plonkChecksPassedStepCircuit

compilePlonkChecksPassedWrap :: Effect (CompiledCircuit WrapField)
compilePlonkChecksPassedWrap =
  compile noAdvice (Proxy @(UnChecked (PlonkChecksPassedInput (F WrapField) (Type2 (F WrapField)))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    plonkChecksPassedWrapCircuit
