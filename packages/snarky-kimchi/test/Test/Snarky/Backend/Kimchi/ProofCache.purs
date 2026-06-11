-- | End-to-end smoke test for `Snarky.Backend.Kimchi.ProofCache`:
-- |
-- |   1. Empty store — `getPallasProof` ⇒ `Nothing` (cache miss).
-- |   2. Build a real kimchi proof (same `y = x²` shape as the
-- |      Proof-FFI test), store it via `setPallasProof`, retrieve via
-- |      `getPallasProof`, and verify the retrieved proof actually
-- |      verifies (round-trip is byte-faithful w.r.t. the kimchi
-- |      verifier).
-- |   3. Garbled-JSON resilience — overwrite the cache file with
-- |      non-JSON, confirm `getPallasProof` quietly returns `Nothing`
-- |      (mirrors OCaml `proof_cache.ml`'s graceful-degrade contract).
module Test.Snarky.Backend.Kimchi.ProofCache
  ( spec
  ) where

import Prelude

import Data.Array (concatMap)
import Data.Either (Either(..))
import Data.Int as Int
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Unsafe (unsafePerformEffect)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Run (EFFECT)
import Run as Run
import Snarky.Backend.Builder (CircuitBuilderState, constraintsToArray)
import Snarky.Backend.Compile (Solver, compile, makeSolver, runSolver)
import Snarky.Backend.Kimchi (makeConstraintSystemWithPrevChallenges, makeWitness)
import Snarky.Backend.Kimchi.Class (createProverIndex, createVerifierIndex)
import Snarky.Backend.Kimchi.Impl.Vesta (vestaCrsCreate)
import Snarky.Backend.Kimchi.Proof (createProof, verifyOpeningProof)
import Snarky.Backend.Kimchi.ProofCache (getPallasProof, mkProofCache, setPallasProof)
import Snarky.Circuit.DSL (F(..), FVar, Snarky, assertSquare_, exists, readCVar)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate, initialState)
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
import Snarky.Curves.Class (class PrimeField, fromInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (VestaG)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

squareCircuit
  :: PrimeField Pallas.BaseField
  => FVar Pallas.BaseField
  -> Snarky Pallas.BaseField (KimchiConstraint Pallas.BaseField) (EFFECT + ()) (FVar Pallas.BaseField)
squareCircuit x = do
  y <- exists do
    F xv <- readCVar x
    pure (F (xv * xv) :: F Pallas.BaseField)
  assertSquare_ x y
  pure y

-- | Cache file lives under /tmp so tests don't litter the workspace.
cachePath :: String
cachePath = "/tmp/snarky-kimchi-proofcache-test.json"

removeIfExists :: String -> Effect Unit
removeIfExists p = do
  present <- FS.exists p
  when present $ FS.unlink p

spec :: Spec Unit
spec = describe "Snarky.Backend.Kimchi.ProofCache (round-trip)" do

  it "miss-then-hit round-trip preserves a real kimchi proof" do
    liftEffect do
      removeIfExists cachePath
      let cache = mkProofCache cachePath

      -- Build the FFI machinery once for both arms of the test.
      let
        builtState =
          unsafePerformEffect $ Run.runBaseEffect $ compile @Pallas.BaseField
            (Proxy @(F Pallas.BaseField))
            (Proxy @(F Pallas.BaseField))
            (Proxy @(KimchiConstraint Pallas.BaseField))
            squareCircuit
            (initialState :: CircuitBuilderState (KimchiGate Pallas.BaseField) (AuxState Pallas.BaseField))
        kimchiRows =
          concatMap
            (toKimchiRows <<< _.constraint)
            (constraintsToArray builtState.constraints)
        maxPolySize = Int.pow 2 16
        crs = vestaCrsCreate maxPolySize
        csResult =
          makeConstraintSystemWithPrevChallenges @Pallas.BaseField
            { constraints: kimchiRows
            , publicInputs: builtState.publicInputs
            , unionFind: (un AuxState builtState.aux).wireState.unionFind
            , prevChallengesCount: 0
            , maxPolySize
            }
        proverIndex =
          createProverIndex @Pallas.BaseField @VestaG
            { gates: csResult.gates
            , publicInputSize: csResult.publicInputSize
            , prevChallengesCount: csResult.prevChallengesCount
            , maxPolySize: csResult.maxPolySize
            , crs
            }
        verifierIndex = createVerifierIndex @Pallas.BaseField @VestaG proverIndex

        solver :: Solver Pallas.BaseField (KimchiConstraint Pallas.BaseField) (F Pallas.BaseField) (F Pallas.BaseField)
        solver = makeSolver (Proxy @(KimchiConstraint Pallas.BaseField)) squareCircuit

      runSolver solver (F (fromInt 7)) >>= case _ of
        Left e -> throw $ "Squaring-circuit solver failed: " <> show e
        Right (Tuple _output assignments) -> do
          let
            { witness, publicInputs } =
              makeWitness
                { assignments
                , constraints: map _.variables csResult.constraints
                , publicInputs: builtState.publicInputs
                }
            proof = createProof @Pallas.BaseField @VestaG @Pallas.ScalarField
              { proverIndex, witness }

          -- 1. Cold cache ⇒ miss.
          missBefore <- getPallasProof cache verifierIndex publicInputs
          isNothing missBefore `shouldEqual` true

          -- 2. Set then get ⇒ hit, and the retrieved proof verifies.
          setPallasProof cache verifierIndex publicInputs proof
          hit <- getPallasProof cache verifierIndex publicInputs
          isJust hit `shouldEqual` true
          case hit of
            Nothing -> throw "cache hit promised by isJust but pattern was Nothing"
            Just proof' -> do
              let
                ok = verifyOpeningProof @Pallas.BaseField @VestaG @Pallas.ScalarField
                  verifierIndex
                  { proof: proof', publicInput: publicInputs }
              ok `shouldEqual` true

          -- 3. Garbled store ⇒ silent miss (mirrors OCaml proof_cache.ml
          --    "any decode drift => empty store").
          FS.writeTextFile UTF8 cachePath "{ not valid json"
          garbled <- getPallasProof cache verifierIndex publicInputs
          isNothing garbled `shouldEqual` true

          removeIfExists cachePath
