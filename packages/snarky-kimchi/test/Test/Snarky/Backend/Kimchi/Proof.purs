-- | End-to-end smoke test for the kimchi proof FFI:
-- |
-- |   1. Build a tiny circuit (`y = x²`) via `compile`.
-- |   2. Run the kimchi pipeline: constraint-system → prover index →
-- |      verifier index.
-- |   3. Solve for a witness with `x = 7` (so `y = 49`).
-- |   4. `createProof` ⇒ verify ⇒ should accept.
-- |   5. Serde JSON round-trip both the VK and the proof, then verify
-- |      again — confirms the codecs land at the same kimchi-napi
-- |      objects on both ends.
-- |
-- | The polynomial-commitment / opening-proof internals (oracles,
-- | bulletproof challenges, IPA fold) are exercised transitively by
-- | the verifier; we don't separately assert on them here.
module Test.Snarky.Backend.Kimchi.Proof
  ( spec
  ) where

import Prelude

import Data.Array (concatMap)
import Data.Either (Either(..))
import Data.Int as Int
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Builder (constraintsToArray)
import Snarky.Backend.Compile (Solver, compile, makeSolver, runSolver)
import Snarky.Backend.Kimchi (makeConstraintSystemWithPrevChallenges, makeWitness)
import Snarky.Backend.Kimchi.Class (createProverIndex, createVerifierIndex)
import Snarky.Backend.Kimchi.Impl.Vesta (vestaCrsCreate)
import Snarky.Backend.Kimchi.Proof (createProof, pallasProofFromSerdeJson, pallasProofToSerdeJson, pallasVerifierIndexFromSerdeJson, pallasVerifierIndexToSerdeJson, verifyOpeningProof)
import Snarky.Circuit.DSL (F(..), FVar, Snarky, assertSquare_, exists, readCVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
import Snarky.Curves.Class (class PrimeField, fromInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (VestaG)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

-- | Tiny circuit: input `x`, output `x²`. Allocates `y` as a witness
-- | (so the prover supplies it) and constrains `x² = y` via the kimchi
-- | `assertSquare_` gate. The output `y` becomes part of the public
-- | input on the verifier side.
squareCircuit
  :: PrimeField Pallas.BaseField
  => FVar Pallas.BaseField
  -> Snarky Pallas.BaseField (KimchiConstraint Pallas.BaseField) () (FVar Pallas.BaseField)
squareCircuit x = do
  y <- exists do
    F xv <- readCVar x
    pure (F (xv * xv) :: F Pallas.BaseField)
  assertSquare_ x y
  pure y

spec :: Spec Unit
spec = describe "Snarky.Backend.Kimchi.Proof (end-to-end FFI)" do

  it "creates, verifies, and JSON-round-trips a real kimchi proof" do
    liftEffect runProofRoundtrip

runProofRoundtrip :: Effect Unit
runProofRoundtrip = do
  -- 1. Compile the squaring circuit.
  builtState <- compile @Pallas.BaseField noAdvice
    (Proxy @(F Pallas.BaseField))
    (Proxy @(F Pallas.BaseField))
    (Proxy @(KimchiConstraint Pallas.BaseField))
    squareCircuit
  -- 2. Constraint-system + prover-index + verifier-index.
  let
    kimchiRows =
      concatMap
        (toKimchiRows <<< _.constraint)
        (constraintsToArray builtState.constraints)
    maxPolySize = Int.pow 2 16
    crs = vestaCrsCreate maxPolySize
  csResult <-
    makeConstraintSystemWithPrevChallenges @Pallas.BaseField
      { constraints: kimchiRows
      , publicInputs: builtState.publicInputs
      , unionFind: (un AuxState builtState.aux).wireState.unionFind
      , prevChallengesCount: 0
      , maxPolySize
      }
  let
    proverIndex =
      createProverIndex @Pallas.BaseField @VestaG
        { gates: csResult.gates
        , publicInputSize: csResult.publicInputSize
        , prevChallengesCount: csResult.prevChallengesCount
        , maxPolySize: csResult.maxPolySize
        , crs
        }
    verifierIndex = createVerifierIndex @Pallas.BaseField @VestaG proverIndex

    -- 3. Solve for x = 7 (so y = 49).
    solver :: Solver Pallas.BaseField (KimchiConstraint Pallas.BaseField) (F Pallas.BaseField) (F Pallas.BaseField)
    solver = makeSolver (Proxy @(KimchiConstraint Pallas.BaseField)) squareCircuit
  runSolver solver (F (fromInt 7)) >>= case _ of
    Left e -> throw $ "Squaring-circuit solver failed: " <> show e
    Right (Tuple _output assignments) -> do
      let
        -- 4. Build the kimchi witness from solver assignments.
        { witness, publicInputs } =
          makeWitness
            { assignments
            , constraints: map _.variables csResult.constraints
            , publicInputs: builtState.publicInputs
            }

        -- 5. Real kimchi proof, then verify.
        proof = createProof @Pallas.BaseField @VestaG @Pallas.ScalarField { proverIndex, witness }
        ok = verifyOpeningProof @Pallas.BaseField @VestaG @Pallas.ScalarField verifierIndex
          { proof, publicInput: publicInputs }
      ok `shouldEqual` true

      let
        -- 6. JSON-round-trip the VK + proof, then verify again.
        vkJson = pallasVerifierIndexToSerdeJson verifierIndex
        verifierIndex' = pallasVerifierIndexFromSerdeJson vkJson crs
        proofJson = pallasProofToSerdeJson proof
        proof' = pallasProofFromSerdeJson proofJson
        okRoundtrip =
          verifyOpeningProof @Pallas.BaseField @VestaG @Pallas.ScalarField verifierIndex'
            { proof: proof', publicInput: publicInputs }
      okRoundtrip `shouldEqual` true
