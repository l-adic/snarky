-- | The chunked app body (`chunks2Body`) proved by the bare kimchi
-- | prover, with no pickles step or wrap around it, so that
-- | `KIMCHI_WITNESS_DUMP` captures only the body's witness.
-- | `tools/witness_diff.sh app_circuit_chunks2` diffs it against OCaml's
-- | `dump_app_circuit_chunks2_witness.exe`; without the variable the
-- | test does nothing.
module Test.Pickles.KimchiAppWitness
  ( spec
  ) where

import Prelude

import Colog (LoggerT, Message)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Int.Bits as Bits
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Node.Process (lookupEnv)
import Pickles (StepField)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Builder (constraintsToArray)
import Snarky.Backend.Compile (Solver, compile, makeSolver, runSolver)
import Snarky.Backend.Kimchi (makeConstraintSystemWithPrevChallenges, makeWitness)
import Snarky.Backend.Kimchi.Class (createProverIndex)
import Snarky.Backend.Kimchi.Proof (createProof)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
import Snarky.Curves.Pasta (VestaG)
import Test.Pickles.Prove.Chunks2 (chunks2Body)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Type.Proxy (Proxy(..))

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Kimchi app-body witness" do
  it "proves the two-chunk app body when KIMCHI_WITNESS_DUMP is set" \{ vestaSrs } ->
    liftEffect $ lookupEnv "KIMCHI_WITNESS_DUMP" >>= case _ of
      Nothing -> pure unit
      Just _ -> proveAppBody vestaSrs

-- | Prove the app body at `max_poly_size` 2^16, OCaml's default
-- | (`Tick.set_urs_info []`): its 2^16 + 1 rows round the domain up to
-- | 2^17, so the prover runs at two chunks. The proof is discarded; the
-- | prove is what fires the dump hook in kimchi's
-- | `ProverProof::create_recursive`.
proveAppBody :: CRS VestaG -> Effect Unit
proveAppBody crs = do
  builtState <- compile @StepField noAdvice (Proxy @Unit) (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    (const chunks2Body)
  let
    kimchiRows = Array.concatMap (toKimchiRows <<< _.constraint)
      (constraintsToArray builtState.constraints)
    maxPolySize = 1 `Bits.shl` 16
  csResult <- makeConstraintSystemWithPrevChallenges @StepField
    { constraints: kimchiRows
    , publicInputs: builtState.publicInputs
    , unionFind: (un AuxState builtState.aux).wireState.unionFind
    , prevChallengesCount: 0
    , maxPolySize
    }
  let
    proverIndex = createProverIndex @StepField @VestaG
      { gates: csResult.gates
      , publicInputSize: csResult.publicInputSize
      , prevChallengesCount: csResult.prevChallengesCount
      , maxPolySize: csResult.maxPolySize
      , crs
      }

    solver :: Solver StepField (KimchiConstraint StepField) Unit Unit
    solver = makeSolver (Proxy @(KimchiConstraint StepField)) (const chunks2Body)
  runSolver solver unit >>= case _ of
    Left e -> throw $ "app body solver: " <> show e
    Right (Tuple _ assignments) -> do
      let
        { witness } = makeWitness
          { assignments
          , constraints: map _.variables csResult.constraints
          , publicInputs: builtState.publicInputs
          }
        _proof = createProof { proverIndex, witness }
      pure unit
