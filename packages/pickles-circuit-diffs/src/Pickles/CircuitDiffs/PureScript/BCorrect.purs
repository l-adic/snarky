module Pickles.CircuitDiffs.PureScript.BCorrect
  ( compileBCorrect
  , compileBCorrectWrap
  ) where

import Prelude

import Data.Tuple.Nested (Tuple5, tuple5, uncurry5)
import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, stepEndo, wrapEndo)
import Pickles.Field (StepField, WrapField)
import Pickles.IPA (bCorrectCircuit, computeChallenges) as IPA
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, F, FVar, SizedF, Snarky, UnChecked(..), const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (Type1, Type2, fromShiftedType1Circuit, fromShiftedType2Circuit)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

-- | `b_correct_{step,wrap}_circuit`'s input (OCaml `dump_circuit_impl.ml`): the claimed `b`
-- | is a Type1 (step) or Type2 (wrap) shifted value.
newtype BCorrectInput f s = BCorrectInput
  { challenges :: Vector 16 (SizedF 128 f) -- the raw 128-bit bulletproof challenges
  , zeta :: f
  , zetaOmega :: f
  , evalscale :: f
  , b :: s
  }

-- | The wire order.
type BCorrectTuple f s = Tuple5 (Vector 16 (SizedF 128 f)) f f f s

toTuple :: forall f s. BCorrectInput f s -> BCorrectTuple f s
toTuple (BCorrectInput i) = tuple5 i.challenges i.zeta i.zetaOmega i.evalscale i.b

fromTuple :: forall f s. BCorrectTuple f s -> BCorrectInput f s
fromTuple = uncurry5 \challenges zeta zetaOmega evalscale b ->
  BCorrectInput { challenges, zeta, zetaOmega, evalscale, b }

instance
  ( CircuitType f fa fv
  , CircuitType f sa sv
  ) =>
  CircuitType f (BCorrectInput fa sa) (BCorrectInput fv sv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(BCorrectTuple fa sa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(BCorrectTuple fa sa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(BCorrectTuple fa sa)

-- | Expand the challenges through the endomorphism, then check
-- | `b = b(zeta) + evalscale * b(zetaw)` against the unshifted claim.
bCorrectStepCircuit
  :: forall r
   . UnChecked (BCorrectInput (FVar StepField) (Type1 (FVar StepField)))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
bCorrectStepCircuit (UnChecked (BCorrectInput i)) = do
  expanded <- IPA.computeChallenges i.challenges (const_ stepEndo)
  void $ IPA.bCorrectCircuit
    { challenges: expanded
    , zeta: i.zeta
    , zetaOmega: i.zetaOmega
    , evalscale: i.evalscale
    , expectedB: fromShiftedType1Circuit i.b
    }

bCorrectWrapCircuit
  :: forall r
   . UnChecked (BCorrectInput (FVar WrapField) (Type2 (FVar WrapField)))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
bCorrectWrapCircuit (UnChecked (BCorrectInput i)) = do
  expanded <- IPA.computeChallenges i.challenges (const_ wrapEndo)
  void $ IPA.bCorrectCircuit
    { challenges: expanded
    , zeta: i.zeta
    , zetaOmega: i.zetaOmega
    , evalscale: i.evalscale
    , expectedB: fromShiftedType2Circuit i.b
    }

compileBCorrect :: Effect (CompiledCircuit StepField)
compileBCorrect =
  compile noAdvice (Proxy @(UnChecked (BCorrectInput (F StepField) (Type1 (F StepField)))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    bCorrectStepCircuit

compileBCorrectWrap :: Effect (CompiledCircuit WrapField)
compileBCorrectWrap =
  compile noAdvice (Proxy @(UnChecked (BCorrectInput (F WrapField) (Type2 (F WrapField)))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    bCorrectWrapCircuit
