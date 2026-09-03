module Pickles.CircuitDiffs.PureScript.BCorrect
  ( compileBCorrect
  , compileBCorrectWrap
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, stepEndo, unsafeIdx, wrapEndo)
import Pickles.Field (StepField, WrapField)
import Pickles.IPA (bCorrectCircuit, computeChallenges) as IPA
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (F, FVar, SizedF, Snarky, const_)
import Snarky.Circuit.Kimchi (Type1(..), Type2(..), fromShiftedType1Circuit, fromShiftedType2Circuit)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

-- | `b_correct_{step,wrap}_circuit` (OCaml `dump_circuit_impl.ml`): 16 raw 128-bit
-- | bulletproof challenges at 0-15, zeta at 16, zetaw at 17, evalscale at 18, and
-- | the claimed `b` at 19 as a Type1 (step) or Type2 (wrap) shifted value.
-- | Expand the challenges through the endomorphism, then check
-- | `b = b(zeta) + evalscale * b(zetaw)` against the unshifted claim.
bCorrectStepCircuit
  :: forall r
   . Vector 20 (FVar StepField)
  -> Snarky StepField (KimchiConstraint StepField) r Unit
bCorrectStepCircuit inputs = do
  let
    at = unsafeIdx inputs

    raw :: Vector 16 (SizedF 128 (FVar StepField))
    raw = Vector.generate \j -> asSizedF128 (at (getFinite j))
  expanded <- IPA.computeChallenges raw (const_ stepEndo)
  void $ IPA.bCorrectCircuit
    { challenges: expanded
    , zeta: at 16
    , zetaOmega: at 17
    , evalscale: at 18
    , expectedB: fromShiftedType1Circuit (Type1 (at 19))
    }

bCorrectWrapCircuit
  :: forall r
   . Vector 20 (FVar WrapField)
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
bCorrectWrapCircuit inputs = do
  let
    at = unsafeIdx inputs

    raw :: Vector 16 (SizedF 128 (FVar WrapField))
    raw = Vector.generate \j -> asSizedF128 (at (getFinite j))
  expanded <- IPA.computeChallenges raw (const_ wrapEndo)
  void $ IPA.bCorrectCircuit
    { challenges: expanded
    , zeta: at 16
    , zetaOmega: at 17
    , evalscale: at 18
    , expectedB: fromShiftedType2Circuit (Type2 (at 19))
    }

compileBCorrect :: Effect (CompiledCircuit StepField)
compileBCorrect =
  compile noAdvice (Proxy @(Vector 20 (F StepField))) (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    bCorrectStepCircuit

compileBCorrectWrap :: Effect (CompiledCircuit WrapField)
compileBCorrectWrap =
  compile noAdvice (Proxy @(Vector 20 (F WrapField))) (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    bCorrectWrapCircuit
