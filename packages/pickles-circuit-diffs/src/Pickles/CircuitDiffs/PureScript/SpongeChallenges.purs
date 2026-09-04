module Pickles.CircuitDiffs.PureScript.SpongeChallenges
  ( compileChallengeDigestStep
  , compileChallengeDigestWrap
  , compileSpongeAndChallengesStep
  , compileSpongeAndChallengesWrap
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, stepEndo, unsafeIdx, wrapEndo)
import Pickles.Field (StepField, WrapField)
import Pickles.PlonkChecks (AllEvals, challengeDigest, maskedChallengeDigest, squeezeXiR)
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (Bool(..), BoolVar, F, FVar, Snarky, const_)
import Snarky.Circuit.Kimchi (toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

-- | Layout only, throughout this module: the rows are the library's
-- | `maskedChallengeDigest` / `challengeDigest`, `squeezeXiR` (the verifiers' whole
-- | fr-sponge schedule) and `toField`; the helpers below only index the inputs.

-- | The two 16-entry previous-challenge vectors from index `base` of the inputs.
prevChallengesFrom :: forall n f. Vector n (FVar f) -> Int -> Vector 2 (Vector 16 (FVar f))
prevChallengesFrom inputs base = Vector.generate \j ->
  Vector.generate \k -> unsafeIdx inputs (base + 16 * getFinite j + getFinite k)

-- | The proofs-verified mask at indices 0-1 (`Boolean.Unsafe.of_cvar`, an
-- | unchecked coercion here too).
maskFrom :: forall n f. Vector n (FVar f) -> Vector 2 (BoolVar f)
maskFrom inputs = Vector.generate \j -> coerce (unsafeIdx inputs (getFinite j))

-- | The evaluations from index `base` of the inputs, the dumps' layout: the digest
-- | before evaluations, ft_eval1, the public pair, then 15 w pairs, 15 coefficient
-- | pairs, the z pair, 6 s pairs and 6 selector pairs.
allEvalsFrom
  :: forall n f
   . Vector n (FVar f)
  -> Int
  -> { spongeDigest :: FVar f, allEvals :: AllEvals (FVar f) }
allEvalsFrom inputs base =
  let
    at i = unsafeIdx inputs (base + i)
    pair i = { zeta: at i, omegaTimesZeta: at (i + 1) }
  in
    { spongeDigest: at 0
    , allEvals:
        { ftEval1: at 1
        , publicEvals: pair 2
        , witnessEvals: Vector.generate \j -> pair (4 + 2 * getFinite j)
        , coeffEvals: Vector.generate \j -> pair (34 + 2 * getFinite j)
        , zEvals: pair 64
        , sigmaEvals: Vector.generate \j -> pair (66 + 2 * getFinite j)
        , indexEvals: Vector.generate \j -> pair (78 + 2 * getFinite j)
        }
    }

-- | `challenge_digest_step_circuit`: the masked digest of the previous challenges.
challengeDigestStepCircuit
  :: forall r
   . Vector 34 (FVar StepField)
  -> Snarky StepField (KimchiConstraint StepField) r Unit
challengeDigestStepCircuit inputs =
  void $ maskedChallengeDigest (maskFrom inputs) (prevChallengesFrom inputs 2)

-- | `challenge_digest_wrap_circuit`: the plain digest of the previous challenges.
challengeDigestWrapCircuit
  :: forall r
   . Vector 32 (FVar WrapField)
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
challengeDigestWrapCircuit inputs =
  void $ challengeDigest (prevChallengesFrom inputs 0)

-- | `sponge_and_challenges_step_circuit`: mask at 0-1, previous challenges at 2-33,
-- | the evaluations from 34; xi and r both by `squeeze_challenge`.
spongeAndChallengesStepCircuit
  :: forall r
   . Vector 124 (FVar StepField)
  -> Snarky StepField (KimchiConstraint StepField) r Unit
spongeAndChallengesStepCircuit inputs = do
  let
    endoVar = const_ stepEndo :: FVar StepField
    evals = allEvalsFrom inputs 34
  { xi, r } <- squeezeXiR
    { spongeDigestBeforeEvaluations: evals.spongeDigest
    , challengeDigest: maskedChallengeDigest (maskFrom inputs) (prevChallengesFrom inputs 2)
    , allEvals: evals.allEvals
    , endo: endoVar
    , xiConstrainLowBits: true
    }
  _ <- toField @8 xi endoVar
  void $ toField @8 r endoVar

-- | `sponge_and_challenges_wrap_circuit`: previous challenges at 0-31, the
-- | evaluations from 32; xi by `squeeze_scalar`, r by `squeeze_challenge`.
spongeAndChallengesWrapCircuit
  :: forall r
   . Vector 122 (FVar WrapField)
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
spongeAndChallengesWrapCircuit inputs = do
  let
    endoVar = const_ wrapEndo :: FVar WrapField
    evals = allEvalsFrom inputs 32
  { xi, r } <- squeezeXiR
    { spongeDigestBeforeEvaluations: evals.spongeDigest
    , challengeDigest: challengeDigest (prevChallengesFrom inputs 0)
    , allEvals: evals.allEvals
    , endo: endoVar
    , xiConstrainLowBits: false
    }
  _ <- toField @8 xi endoVar
  void $ toField @8 r endoVar

compileChallengeDigestStep :: Effect (CompiledCircuit StepField)
compileChallengeDigestStep =
  compile noAdvice (Proxy @(Vector 34 (F StepField))) (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    challengeDigestStepCircuit

compileChallengeDigestWrap :: Effect (CompiledCircuit WrapField)
compileChallengeDigestWrap =
  compile noAdvice (Proxy @(Vector 32 (F WrapField))) (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    challengeDigestWrapCircuit

compileSpongeAndChallengesStep :: Effect (CompiledCircuit StepField)
compileSpongeAndChallengesStep =
  compile noAdvice (Proxy @(Vector 124 (F StepField))) (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    spongeAndChallengesStepCircuit

compileSpongeAndChallengesWrap :: Effect (CompiledCircuit WrapField)
compileSpongeAndChallengesWrap =
  compile noAdvice (Proxy @(Vector 122 (F WrapField))) (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    spongeAndChallengesWrapCircuit
