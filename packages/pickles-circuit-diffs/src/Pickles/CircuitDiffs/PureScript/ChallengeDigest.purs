module Pickles.CircuitDiffs.PureScript.ChallengeDigest
  ( ChallengeDigestInput
  , parseChallengeDigestInput
  , challengeDigestStepCircuit
  , compileChallengeDigest
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, unsafeIdx)
import Pickles.Step.ChallengeDigest (challengeDigestCircuit) as ChallengeDigest
import Pickles.Types (StepField)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F, FVar, SizedF, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

type ChallengeDigestInput f =
  { mask :: Vector 2 (BoolVar f)
  , oldChallenges :: Vector 2 (Vector 16 (SizedF 128 (FVar f)))
  }

parseChallengeDigestInput :: Vector 34 (FVar StepField) -> ChallengeDigestInput StepField
parseChallengeDigestInput inputs =
  let
    at = unsafeIdx inputs
  in
    { mask: Vector.generate \j -> coerce (at (getFinite j))
    , oldChallenges: Vector.generate \j ->
        Vector.generate \k -> asSizedF128 (at (2 + 16 * getFinite j + getFinite k))
    }

challengeDigestStepCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => ChallengeDigestInput StepField
  -> Snarky (KimchiConstraint StepField) t m (FVar StepField)
challengeDigestStepCircuit = ChallengeDigest.challengeDigestCircuit

compileChallengeDigest :: CompiledCircuit StepField
compileChallengeDigest =
  compilePure (Proxy @(Vector 34 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> void $ challengeDigestStepCircuit (parseChallengeDigestInput inputs))
    Kimchi.initialState
