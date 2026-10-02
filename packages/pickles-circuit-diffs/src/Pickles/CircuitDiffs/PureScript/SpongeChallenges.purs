module Pickles.CircuitDiffs.PureScript.SpongeChallenges
  ( compileChallengeDigestStep
  , compileChallengeDigestWrap
  , compileSpongeAndChallengesStep
  , compileSpongeAndChallengesWrap
  ) where

import Prelude

import Data.Tuple.Nested (Tuple2, Tuple3, Tuple7, tuple2, tuple3, tuple7, uncurry2, uncurry3, uncurry7)
import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, stepEndo, wrapEndo)
import Pickles.Field (StepField, WrapField)
import Pickles.PlonkChecks (challengeDigest, maskedChallengeDigest, squeezeXiR)
import Pickles.Types (Evals, evalPair, pairEval)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, BoolVar, F, FVar, Snarky, UnChecked(..), const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Type.Proxy (Proxy(..))

-- | Layout only, throughout this module: the rows are the library's
-- | `maskedChallengeDigest` / `challengeDigest`, `squeezeXiR` (the verifiers' whole
-- | fr-sponge schedule) and `toField`.

-- | `challenge_digest_step_circuit`'s input (OCaml `dump_circuit_impl.ml`): the
-- | proofs-verified mask (`Boolean.Unsafe.of_cvar` there) and the two 16-entry
-- | previous-challenge vectors.
newtype ChallengeDigestStepInput b f = ChallengeDigestStepInput
  { mask :: Vector 2 b
  , prevChallenges :: Vector 2 (Vector 16 f)
  }

-- | The wire order.
type ChallengeDigestStepTuple b f = Tuple2 (Vector 2 b) (Vector 2 (Vector 16 f))

digestToTuple :: forall b f. ChallengeDigestStepInput b f -> ChallengeDigestStepTuple b f
digestToTuple (ChallengeDigestStepInput i) = tuple2 i.mask i.prevChallenges

digestFromTuple :: forall b f. ChallengeDigestStepTuple b f -> ChallengeDigestStepInput b f
digestFromTuple = uncurry2 \mask prevChallenges -> ChallengeDigestStepInput { mask, prevChallenges }

instance
  ( CircuitType f ba bv
  , CircuitType f fa fv
  ) =>
  CircuitType f (ChallengeDigestStepInput ba fa) (ChallengeDigestStepInput bv fv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(ChallengeDigestStepTuple ba fa))
  valueToFields = genericValueToFields <<< digestToTuple
  fieldsToValue = digestFromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(ChallengeDigestStepTuple ba fa) <<< digestToTuple
  fieldsToVar = digestFromTuple <<< genericFieldsToVar @(ChallengeDigestStepTuple ba fa)

-- | The sponge-and-challenges inputs both sides share (OCaml `dump_circuit_impl.ml`): the two
-- | previous-challenge vectors, the digest before evaluations, and the evaluations, which
-- | the dumps lay out ft_eval1 first, then the public pair, 15 w pairs, 15 coefficient
-- | pairs, the z pair, 6 s pairs and 6 selector pairs.
newtype SpongeInput f = SpongeInput
  { prevChallenges :: Vector 2 (Vector 16 f)
  , spongeDigest :: f
  , allEvals :: Evals f
  }

-- | The evaluations in the dumps' order, each as its `(zeta, zetaw)` pair.
type EvalsTuple f =
  Tuple7 f (Tuple2 f f) (Vector 15 (Tuple2 f f)) (Vector 15 (Tuple2 f f)) (Tuple2 f f)
    (Vector 6 (Tuple2 f f))
    (Vector 6 (Tuple2 f f))

-- | The wire order.
type SpongeTuple f = Tuple3 (Vector 2 (Vector 16 f)) f (EvalsTuple f)

spongeToTuple :: forall f. SpongeInput f -> SpongeTuple f
spongeToTuple (SpongeInput i) =
  tuple3 i.prevChallenges i.spongeDigest
    ( tuple7 e.ftEval1 (evalPair e.publicEvals) (map evalPair e.witnessEvals)
        (map evalPair e.coeffEvals)
        (evalPair e.zEvals)
        (map evalPair e.sigmaEvals)
        (map evalPair e.indexEvals)
    )
  where
  e = i.allEvals

spongeFromTuple :: forall f. SpongeTuple f -> SpongeInput f
spongeFromTuple = uncurry3 \prevChallenges spongeDigest evals ->
  SpongeInput
    { prevChallenges
    , spongeDigest
    , allEvals: evals # uncurry7 \ftEval1 publicEvals witnessEvals coeffEvals zEvals sigmaEvals indexEvals ->
        { ftEval1
        , publicEvals: pairEval publicEvals
        , witnessEvals: map pairEval witnessEvals
        , coeffEvals: map pairEval coeffEvals
        , zEvals: pairEval zEvals
        , sigmaEvals: map pairEval sigmaEvals
        , indexEvals: map pairEval indexEvals
        }
    }

instance CircuitType f fa fv => CircuitType f (SpongeInput fa) (SpongeInput fv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(SpongeTuple fa))
  valueToFields = genericValueToFields <<< spongeToTuple
  fieldsToValue = spongeFromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(SpongeTuple fa) <<< spongeToTuple
  fieldsToVar = spongeFromTuple <<< genericFieldsToVar @(SpongeTuple fa)

-- | `sponge_and_challenges_step_circuit`'s input: the proofs-verified mask, then the shared
-- | inputs.
newtype SpongeStepInput b f = SpongeStepInput
  { mask :: Vector 2 b
  , shared :: SpongeInput f
  }

-- | The wire order.
type SpongeStepTuple b f = Tuple2 (Vector 2 b) (SpongeInput f)

stepToTuple :: forall b f. SpongeStepInput b f -> SpongeStepTuple b f
stepToTuple (SpongeStepInput i) = tuple2 i.mask i.shared

stepFromTuple :: forall b f. SpongeStepTuple b f -> SpongeStepInput b f
stepFromTuple = uncurry2 \mask shared -> SpongeStepInput { mask, shared }

instance
  ( CircuitType f ba bv
  , CircuitType f fa fv
  ) =>
  CircuitType f (SpongeStepInput ba fa) (SpongeStepInput bv fv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(SpongeStepTuple ba fa))
  valueToFields = genericValueToFields <<< stepToTuple
  fieldsToValue = stepFromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(SpongeStepTuple ba fa) <<< stepToTuple
  fieldsToVar = stepFromTuple <<< genericFieldsToVar @(SpongeStepTuple ba fa)

-- | `challenge_digest_step_circuit`: the masked digest of the previous challenges.
challengeDigestStepCircuit
  :: forall r
   . UnChecked (ChallengeDigestStepInput (BoolVar StepField) (FVar StepField))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
challengeDigestStepCircuit (UnChecked (ChallengeDigestStepInput i)) =
  void $ maskedChallengeDigest i.mask i.prevChallenges

-- | `challenge_digest_wrap_circuit`: the plain digest of the two 16-entry previous-challenge
-- | vectors, the whole input.
challengeDigestWrapCircuit
  :: forall r
   . UnChecked (Vector 2 (Vector 16 (FVar WrapField)))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
challengeDigestWrapCircuit (UnChecked prevChallenges) =
  void $ challengeDigest prevChallenges

-- | `sponge_and_challenges_step_circuit`: xi and r both by `squeeze_challenge`.
spongeAndChallengesStepCircuit
  :: forall r
   . UnChecked (SpongeStepInput (BoolVar StepField) (FVar StepField))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
spongeAndChallengesStepCircuit (UnChecked (SpongeStepInput input)) = do
  let
    SpongeInput i = input.shared
    endoVar = const_ stepEndo :: FVar StepField
  { xi, r } <- squeezeXiR
    { spongeDigestBeforeEvaluations: i.spongeDigest
    , challengeDigest: maskedChallengeDigest input.mask i.prevChallenges
    , allEvals: i.allEvals
    , endo: endoVar
    }
  _ <- toField @8 xi endoVar
  void $ toField @8 r endoVar

-- | `sponge_and_challenges_wrap_circuit`: xi by `squeeze_scalar`, r by `squeeze_challenge`.
spongeAndChallengesWrapCircuit
  :: forall r
   . UnChecked (SpongeInput (FVar WrapField))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
spongeAndChallengesWrapCircuit (UnChecked (SpongeInput i)) = do
  let
    endoVar = const_ wrapEndo :: FVar WrapField
  { xi, r } <- squeezeXiR
    { spongeDigestBeforeEvaluations: i.spongeDigest
    , challengeDigest: challengeDigest i.prevChallenges
    , allEvals: i.allEvals
    , endo: endoVar
    }
  _ <- toField @8 xi endoVar
  void $ toField @8 r endoVar

compileChallengeDigestStep :: Effect (CompiledCircuit StepField)
compileChallengeDigestStep =
  compile noAdvice (Proxy @(UnChecked (ChallengeDigestStepInput Boolean (F StepField))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    challengeDigestStepCircuit

compileChallengeDigestWrap :: Effect (CompiledCircuit WrapField)
compileChallengeDigestWrap =
  compile noAdvice (Proxy @(UnChecked (Vector 2 (Vector 16 (F WrapField))))) (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    challengeDigestWrapCircuit

compileSpongeAndChallengesStep :: Effect (CompiledCircuit StepField)
compileSpongeAndChallengesStep =
  compile noAdvice (Proxy @(UnChecked (SpongeStepInput Boolean (F StepField)))) (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    spongeAndChallengesStepCircuit

compileSpongeAndChallengesWrap :: Effect (CompiledCircuit WrapField)
compileSpongeAndChallengesWrap =
  compile noAdvice (Proxy @(UnChecked (SpongeInput (F WrapField)))) (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    spongeAndChallengesWrapCircuit
