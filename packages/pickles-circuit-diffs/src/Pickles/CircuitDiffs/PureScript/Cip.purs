module Pickles.CircuitDiffs.PureScript.Cip
  ( compileCipStep
  , compileCipWrap
  ) where

import Prelude

import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (Tuple10, Tuple2, Tuple3, tuple10, tuple2, tuple3, uncurry10, uncurry2, uncurry3)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (StepField, WrapField)
import Pickles.IPA (challengePolyEvals) as IPA
import Pickles.Linearization.FFI (PointEval)
import Pickles.PlonkChecks (buildEvalList, buildEvalListUnmasked, combinedInnerProduct)
import Pickles.Types (evalPair, pairEval)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, BoolVar, F, FVar, Snarky, UnChecked(..), equals_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (Type1, Type2, fromShiftedType1Circuit, fromShiftedType2Circuit)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

-- | The inputs both sides share, mirroring OCaml `dump_circuit_impl.ml`'s `cip_circuit` /
-- | `cip_wrap_circuit`. The challenges are already expanded to full field elements; each
-- | 43-entry evaluation block is in `Evals.In_circuit.to_list` order (z, 6 selectors, 15 w,
-- | 15 coeff, 6 s), which is `extractEvalFields`'s.
newtype CipInput f = CipInput
  { prevChallenges :: Vector 2 (Vector 16 f)
  , zeta :: f
  , zetaw :: f
  , xi :: f
  , r :: f
  , ftEval0 :: f
  , ftEval1 :: f
  , publicEvals :: PointEval f
  , evalsZeta :: Vector 43 f
  , evalsZetaw :: Vector 43 f
  }

-- | The wire order.
type CipTuple f =
  Tuple10 (Vector 2 (Vector 16 f)) f f f f f f (Tuple2 f f) (Vector 43 f) (Vector 43 f)

cipToTuple :: forall f. CipInput f -> CipTuple f
cipToTuple (CipInput i) =
  tuple10 i.prevChallenges i.zeta i.zetaw i.xi i.r i.ftEval0 i.ftEval1 (evalPair i.publicEvals)
    i.evalsZeta
    i.evalsZetaw

cipFromTuple :: forall f. CipTuple f -> CipInput f
cipFromTuple = uncurry10 \prevChallenges zeta zetaw xi r ftEval0 ftEval1 publicEvals evalsZeta evalsZetaw ->
  CipInput
    { prevChallenges
    , zeta
    , zetaw
    , xi
    , r
    , ftEval0
    , ftEval1
    , publicEvals: pairEval publicEvals
    , evalsZeta
    , evalsZetaw
    }

instance CircuitType f fa fv => CircuitType f (CipInput fa) (CipInput fv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(CipTuple fa))
  valueToFields = genericValueToFields <<< cipToTuple
  fieldsToValue = cipFromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(CipTuple fa) <<< cipToTuple
  fieldsToVar = cipFromTuple <<< genericFieldsToVar @(CipTuple fa)

-- | `cip_step_circuit`'s input: two mask booleans (`Boolean.Unsafe.of_cvar` in OCaml), the
-- | shared inputs, and the claimed value as a Type1 shifted value.
newtype CipStepInput b f = CipStepInput
  { mask :: Vector 2 b
  , shared :: CipInput f
  , claimed :: Type1 f
  }

-- | The wire order.
type CipStepTuple b f = Tuple3 (Vector 2 b) (CipInput f) (Type1 f)

stepToTuple :: forall b f. CipStepInput b f -> CipStepTuple b f
stepToTuple (CipStepInput i) = tuple3 i.mask i.shared i.claimed

stepFromTuple :: forall b f. CipStepTuple b f -> CipStepInput b f
stepFromTuple = uncurry3 \mask shared claimed -> CipStepInput { mask, shared, claimed }

instance
  ( CircuitType f ba bv
  , CircuitType f fa fv
  , CircuitType f (Type1 fa) (Type1 fv)
  ) =>
  CircuitType f (CipStepInput ba fa) (CipStepInput bv fv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(CipStepTuple ba fa))
  valueToFields = genericValueToFields <<< stepToTuple
  fieldsToValue = stepFromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(CipStepTuple ba fa) <<< stepToTuple
  fieldsToVar = stepFromTuple <<< genericFieldsToVar @(CipStepTuple ba fa)

-- | `cip_wrap_circuit`'s input: the shared inputs and the claimed value as a Type2 shifted
-- | value.
newtype CipWrapInput f = CipWrapInput
  { shared :: CipInput f
  , claimed :: Type2 f
  }

-- | The wire order.
type CipWrapTuple f = Tuple2 (CipInput f) (Type2 f)

wrapToTuple :: forall f. CipWrapInput f -> CipWrapTuple f
wrapToTuple (CipWrapInput i) = tuple2 i.shared i.claimed

wrapFromTuple :: forall f. CipWrapTuple f -> CipWrapInput f
wrapFromTuple = uncurry2 \shared claimed -> CipWrapInput { shared, claimed }

instance CircuitType f fa fv => CircuitType f (CipWrapInput fa) (CipWrapInput fv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(CipWrapTuple fa))
  valueToFields = genericValueToFields <<< wrapToTuple
  fieldsToValue = wrapFromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(CipWrapTuple fa) <<< wrapToTuple
  fieldsToVar = wrapFromTuple <<< genericFieldsToVar @(CipWrapTuple fa)

cipStepCircuit
  :: forall r
   . UnChecked (CipStepInput (BoolVar StepField) (FVar StepField))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
cipStepCircuit (UnChecked (CipStepInput input)) = do
  let
    CipInput c = input.shared

    masked :: Vector 2 (FVar StepField) -> Vector 2 (Tuple (BoolVar StepField) (FVar StepField))
    masked = Vector.zipWith Tuple input.mask
  sgZeta <- IPA.challengePolyEvals c.prevChallenges c.zeta
  sgZetaw <- IPA.challengePolyEvals c.prevChallenges c.zetaw
  actual <- combinedInnerProduct
    { xi: c.xi
    , r: c.r
    , evalsZeta: buildEvalList
        { sgEvals: masked sgZeta
        , publicInput: c.publicEvals.zeta
        , ftEval: c.ftEval0
        , evals: c.evalsZeta
        }
    , evalsZetaw: buildEvalList
        { sgEvals: masked sgZetaw
        , publicInput: c.publicEvals.omegaTimesZeta
        , ftEval: c.ftEval1
        , evals: c.evalsZetaw
        }
    }
  void $ equals_ (fromShiftedType1Circuit input.claimed) actual

cipWrapCircuit
  :: forall r
   . UnChecked (CipWrapInput (FVar WrapField))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
cipWrapCircuit (UnChecked (CipWrapInput input)) = do
  let
    CipInput c = input.shared
  sgZeta <- IPA.challengePolyEvals c.prevChallenges c.zeta
  sgZetaw <- IPA.challengePolyEvals c.prevChallenges c.zetaw
  actual <- combinedInnerProduct
    { xi: c.xi
    , r: c.r
    , evalsZeta: buildEvalListUnmasked
        { sgEvals: sgZeta
        , publicInput: c.publicEvals.zeta
        , ftEval: c.ftEval0
        , evals: c.evalsZeta
        }
    , evalsZetaw: buildEvalListUnmasked
        { sgEvals: sgZetaw
        , publicInput: c.publicEvals.omegaTimesZeta
        , ftEval: c.ftEval1
        , evals: c.evalsZetaw
        }
    }
  void $ equals_ (fromShiftedType2Circuit input.claimed) actual

compileCipStep :: Effect (CompiledCircuit StepField)
compileCipStep =
  compile noAdvice
    (Proxy @(UnChecked (CipStepInput Boolean (F StepField))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    cipStepCircuit

compileCipWrap :: Effect (CompiledCircuit WrapField)
compileCipWrap =
  compile noAdvice
    (Proxy @(UnChecked (CipWrapInput (F WrapField))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    cipWrapCircuit
