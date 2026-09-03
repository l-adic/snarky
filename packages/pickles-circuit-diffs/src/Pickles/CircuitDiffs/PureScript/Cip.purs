module Pickles.CircuitDiffs.PureScript.Cip
  ( compileCipStep
  , compileCipWrap
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, unsafeIdx)
import Pickles.Field (StepField, WrapField)
import Pickles.IPA (challengePolyEvals) as IPA
import Pickles.PlonkChecks.CombinedInnerProduct (buildEvalList, buildEvalListUnmasked, combinedInnerProduct)
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (Bool(..), BoolVar, F, FVar, Snarky, equals_)
import Snarky.Circuit.Kimchi (Type1(..), Type2(..), fromShiftedType1Circuit, fromShiftedType2Circuit)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

-- | The inputs both sides share, mirroring OCaml `dump_circuit_impl.ml`'s
-- | `cip_circuit` / `cip_wrap_circuit` layouts from `base` on: two 16-entry
-- | previous-challenge vectors, zeta, zetaw, xi, r (both already expanded to
-- | full field elements), ft_eval0, ft_eval1, the public evaluations, and the
-- | 43-entry evaluation block at each point (z, 6 selectors, 15 w, 15 coeff,
-- | 6 s — `Evals.In_circuit.to_list` order, which is `extractEvalFields`'s).
type CipInput f =
  { prevChallenges :: Vector 2 (Vector 16 (FVar f))
  , zeta :: FVar f
  , zetaw :: FVar f
  , xi :: FVar f
  , r :: FVar f
  , ftEval0 :: FVar f
  , ftEval1 :: FVar f
  , publicZeta :: FVar f
  , publicZetaw :: FVar f
  , evalsZeta :: Vector 43 (FVar f)
  , evalsZetaw :: Vector 43 (FVar f)
  }

parseCipInput :: forall n f. Vector n (FVar f) -> Int -> CipInput f
parseCipInput inputs base =
  let
    at i = unsafeIdx inputs (base + i)
  in
    { prevChallenges: Vector.generate \j ->
        Vector.generate \k -> at (16 * getFinite j + getFinite k)
    , zeta: at 32
    , zetaw: at 33
    , xi: at 34
    , r: at 35
    , ftEval0: at 36
    , ftEval1: at 37
    , publicZeta: at 38
    , publicZetaw: at 39
    , evalsZeta: Vector.generate \j -> at (40 + getFinite j)
    , evalsZetaw: Vector.generate \j -> at (83 + getFinite j)
    }

-- | `cip_step_circuit`: the step-side check — two mask booleans first
-- | (`Boolean.Unsafe.of_cvar`, an unchecked coercion here too), the shared
-- | layout from index 2, and the claimed value as a Type1 shifted value at 128.
cipStepCircuit
  :: forall r
   . Vector 129 (FVar StepField)
  -> Snarky StepField (KimchiConstraint StepField) r Unit
cipStepCircuit inputs = do
  let
    mask :: Vector 2 (BoolVar StepField)
    mask = Vector.generate \j -> coerce (unsafeIdx inputs (getFinite j))
    c = parseCipInput inputs 2
    claimed = Type1 (unsafeIdx inputs 128)

    masked :: Vector 2 (FVar StepField) -> Vector 2 (Tuple (BoolVar StepField) (FVar StepField))
    masked = Vector.zipWith Tuple mask
  sgZeta <- IPA.challengePolyEvals c.prevChallenges c.zeta
  sgZetaw <- IPA.challengePolyEvals c.prevChallenges c.zetaw
  actual <- combinedInnerProduct
    { xi: c.xi
    , r: c.r
    , evalsZeta: buildEvalList
        { sgEvals: masked sgZeta
        , publicInput: c.publicZeta
        , ftEval: c.ftEval0
        , evals: c.evalsZeta
        }
    , evalsZetaw: buildEvalList
        { sgEvals: masked sgZetaw
        , publicInput: c.publicZetaw
        , ftEval: c.ftEval1
        , evals: c.evalsZetaw
        }
    }
  void $ equals_ (fromShiftedType1Circuit claimed) actual

-- | `cip_wrap_circuit`: the wrap-side check — no mask, the shared layout from
-- | index 0, and the claimed value as a Type2 shifted value at 126.
cipWrapCircuit
  :: forall r
   . Vector 127 (FVar WrapField)
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
cipWrapCircuit inputs = do
  let
    c = parseCipInput inputs 0
    claimed = Type2 (unsafeIdx inputs 126)
  sgZeta <- IPA.challengePolyEvals c.prevChallenges c.zeta
  sgZetaw <- IPA.challengePolyEvals c.prevChallenges c.zetaw
  actual <- combinedInnerProduct
    { xi: c.xi
    , r: c.r
    , evalsZeta: buildEvalListUnmasked
        { sgEvals: sgZeta
        , publicInput: c.publicZeta
        , ftEval: c.ftEval0
        , evals: c.evalsZeta
        }
    , evalsZetaw: buildEvalListUnmasked
        { sgEvals: sgZetaw
        , publicInput: c.publicZetaw
        , ftEval: c.ftEval1
        , evals: c.evalsZetaw
        }
    }
  void $ equals_ (fromShiftedType2Circuit claimed) actual

compileCipStep :: Effect (CompiledCircuit StepField)
compileCipStep =
  compile noAdvice
    (Proxy @(Vector 129 (F StepField)))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    cipStepCircuit

compileCipWrap :: Effect (CompiledCircuit WrapField)
compileCipWrap =
  compile noAdvice
    (Proxy @(Vector 127 (F WrapField)))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    cipWrapCircuit
