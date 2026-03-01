-- | Circuit JSON comparison test for FinalizeOtherProof.
-- |
-- | Tests the library's `finalizeOtherProofCircuit` by compiling it with a
-- | thin wrapper that unpacks a flat 151-element public input vector into the
-- | typed record structure the library expects, then compares the resulting
-- | constraint system against the OCaml fixture.
-- |
-- | OCaml reference: dump_circuit_impl.ml:1090-1226 (input layout),
-- |                  step_verifier.ml:828-1165 (computation)
module Test.Pickles.CircuitJson (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (getFinite)
import Data.Foldable (foldl, intercalate)
import Data.Map as Map
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console (log)
import Effect.Exception (throw)
import Foreign (MultipleErrors)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Partial.Unsafe (unsafePartial)
import Pickles.IPA (bCorrectCircuit, type1ScalarOps)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.Step.ChallengeDigest as ChallengeDigest
import Pickles.Step.Domain (pow2PowSquare)
import Pickles.Step.FinalizeOtherProof (finalizeOtherProofCircuit)
import Pickles.Types (StepField)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Backend.Kimchi.CircuitJson (CircuitData, CircuitGateData, circuitToJson, diffCircuits, formatGate, readCircuitJson)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F, FVar, SizedF, Snarky, const_)
import Snarky.Circuit.Kimchi (Type1(..), fromShiftedType1Circuit, toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (EndoScalar(..), endoScalar)
import Snarky.Curves.Vesta as Vesta
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

-------------------------------------------------------------------------------
-- | Constants
-------------------------------------------------------------------------------

-- | Domain log2 for the Step circuit (matches OCaml: Pow_2_roots_of_unity 16)
domainLog2 :: Int
domainLog2 = 16

-- | Endo coefficient for scalar challenge expansion (= Wrap_inner_curve.scalar)
stepEndo :: StepField
stepEndo = let EndoScalar e = endoScalar @Vesta.BaseField @StepField in e

-- | srs_length_log2 = Max_degree.step_log2 = Nat.to_int Tick.Rounds.n = 16
srsLengthLog2 :: Int
srsLengthLog2 = 16

-------------------------------------------------------------------------------
-- | Input parsing helpers
-------------------------------------------------------------------------------

-- | Unsafe array index into a Vector (for compile-time circuit building only)
unsafeIdx :: forall n f. Vector n f -> Int -> f
unsafeIdx v i =
  let
    arr = Vector.toUnfoldable v :: Array f
  in
    unsafePartial $ Array.unsafeIndex arr i

-- | Treat a field variable as a 128-bit scalar challenge (for circuit compilation)
asSizedF128 :: forall f. FVar f -> SizedF 128 (FVar f)
asSizedF128 = unsafeCoerce

-------------------------------------------------------------------------------
-- | Full FinalizeOtherProof Step circuit
-- |
-- | Thin wrapper that unpacks a flat 151-input vector into the typed records
-- | expected by the library's `finalizeOtherProofCircuit`, then calls it.
-- |
-- | Input layout (151 fields):
-- |   0: alpha, 1: beta, 2: gamma, 3: zeta (scalar challenges)
-- |   4: zeta_to_srs_length, 5: zeta_to_domain_size, 6: perm (Type1)
-- |   7: combined_inner_product, 8: b (Type1)
-- |   9: xi (scalar_challenge inner)
-- |   10-25: bulletproof_challenges[0..15]
-- |   26-27: proofs_verified_mask[0..1]
-- |   28: domain_log2
-- |   29-30: public_input (zeta, zetaw)
-- |   31-60: w[0..14] pairs, 61-90: coeff[0..14] pairs
-- |   91-92: z pair, 93-104: s[0..5] pairs, 105-116: selectors[0..5] pairs
-- |   117: ft_eval1
-- |   118-133: prev_challenges[0], 134-149: prev_challenges[1]
-- |   150: sponge_digest_before_evaluations
-------------------------------------------------------------------------------

finalizeOtherProofStepCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 151 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
finalizeOtherProofStepCircuit inputs = do
  let
    at i = unsafeIdx inputs i

    -- PlonkInCircuit: scalar challenges + shifted values
    plonk =
      { alpha: asSizedF128 (at 0)
      , beta: asSizedF128 (at 1)
      , gamma: asSizedF128 (at 2)
      , zeta: asSizedF128 (at 3)
      , zetaToSrsLength: Type1 (at 4)
      , zetaToDomainSize: Type1 (at 5)
      , perm: Type1 (at 6)
      }

    -- DeferredValues
    deferredValues =
      { plonk
      , combinedInnerProduct: Type1 (at 7)
      , b: Type1 (at 8)
      , xi: asSizedF128 (at 9)
      , bulletproofChallenges:
          (Vector.generate \j -> asSizedF128 (at (10 + getFinite j))) :: Vector 16 _
      }

    -- UnfinalizedProof
    unfinalized =
      { deferredValues
      , shouldFinalize: coerce (const_ one :: FVar StepField)
      , spongeDigestBeforeEvaluations: at 150
      }

    -- Mask (2 booleans)
    mask :: Vector 2 (BoolVar StepField)
    mask = Vector.generate \j -> coerce (at (26 + getFinite j))

    -- AllEvals (polynomial evaluations witness)
    allEvals =
      { ftEval1: at 117
      , publicEvals: { zeta: at 29, omegaTimesZeta: at 30 }
      , witnessEvals:
          ( Vector.generate \j ->
              { zeta: at (31 + 2 * getFinite j)
              , omegaTimesZeta: at (31 + 2 * getFinite j + 1)
              }
          ) :: Vector 15 _
      , coeffEvals:
          ( Vector.generate \j ->
              { zeta: at (61 + 2 * getFinite j)
              , omegaTimesZeta: at (61 + 2 * getFinite j + 1)
              }
          ) :: Vector 15 _
      , zEvals: { zeta: at 91, omegaTimesZeta: at 92 }
      , sigmaEvals:
          ( Vector.generate \j ->
              { zeta: at (93 + 2 * getFinite j)
              , omegaTimesZeta: at (93 + 2 * getFinite j + 1)
              }
          ) :: Vector 6 _
      , indexEvals:
          ( Vector.generate \j ->
              { zeta: at (105 + 2 * getFinite j)
              , omegaTimesZeta: at (105 + 2 * getFinite j + 1)
              }
          ) :: Vector 6 _
      }

    witness = { allEvals }

    -- Previous challenges (2 proofs × 16 challenges)
    prevChallenges :: Vector 2 (Vector 16 (FVar StepField))
    prevChallenges = Vector.generate \j ->
      Vector.generate \k ->
        at (118 + 16 * getFinite j + getFinite k)

    -- Build input record
    input =
      { unfinalized
      , witness
      , mask
      , prevChallenges
      , domainLog2Var: at 28
      }

    -- Build compile-time params
    params =
      { domain:
          { generator: LinFFI.domainGenerator @StepField domainLog2
          , shifts: LinFFI.domainShifts @StepField domainLog2
          }
      , domainLog2
      , srsLengthLog2
      , endo: stepEndo
      , linearizationPoly: Linearization.pallas
      }

  void $ finalizeOtherProofCircuit type1ScalarOps params input

-------------------------------------------------------------------------------
-- | pow2PowSquare sub-circuit
-- |
-- | 1 input → compute x^(2^16) via Square constraints.
-- | OCaml reference: dump_circuit_impl.ml pow2_pow_circuit
-------------------------------------------------------------------------------

pow2PowCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 1 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
pow2PowCircuit inputs = do
  let at i = unsafeIdx inputs i
  void $ pow2PowSquare (at 0) 16

-------------------------------------------------------------------------------
-- | bCorrect sub-circuit
-- |
-- | 20 inputs: 0-15 raw scalar challenges, 16 zeta, 17 zetaw, 18 r,
-- | 19 claimedB (Type1 shifted).
-- | OCaml reference: dump_circuit_impl.ml b_correct_circuit
-------------------------------------------------------------------------------

bCorrectTestCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 20 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
bCorrectTestCircuit inputs = do
  let
    at i = unsafeIdx inputs i
    endoVar = const_ stepEndo :: FVar StepField

    rawChallenges :: Vector 16 (SizedF 128 (FVar StepField))
    rawChallenges = Vector.generate \j -> asSizedF128 (at (getFinite j))
  -- Expand challenges in reverse order (OCaml right-to-left evaluation)
  expandedRev <- for (Vector.reverse rawChallenges) \c -> toField @8 c endoVar
  let expanded = Vector.reverse expandedRev
  void $ bCorrectCircuit
    { challenges: expanded
    , zeta: at 16
    , zetaOmega: at 17
    , evalscale: at 18
    , expectedB: fromShiftedType1Circuit (Type1 (at 19))
    }

-------------------------------------------------------------------------------
-- | challengeDigest sub-circuit
-- |
-- | 34 inputs: 0-1 mask booleans, 2-33 prev_challenges (2×16 scalar challenges).
-- | OCaml reference: dump_circuit_impl.ml challenge_digest_circuit
-------------------------------------------------------------------------------

challengeDigestTestCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 34 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
challengeDigestTestCircuit inputs = do
  let
    at i = unsafeIdx inputs i

    mask :: Vector 2 (BoolVar StepField)
    mask = Vector.generate \j -> coerce (at (getFinite j))

    oldChallenges :: Vector 2 (Vector 16 (SizedF 128 (FVar StepField)))
    oldChallenges = Vector.generate \j ->
      Vector.generate \k -> asSizedF128 (at (2 + 16 * getFinite j + getFinite k))
  void $ ChallengeDigest.challengeDigestCircuit { mask, oldChallenges }

-------------------------------------------------------------------------------
-- | Test infrastructure
-------------------------------------------------------------------------------

fixtureDir :: String
fixtureDir = "packages/snarky-kimchi/test/fixtures/"

-- | Count gates by kind
gateTypeSummary :: forall f. Array (CircuitGateData f) -> String
gateTypeSummary gates =
  let
    counts = foldl (\m g -> Map.insertWith (+) (show g.kind) 1 m) Map.empty gates
    lines = map (\(Tuple k v) -> "  " <> k <> ": " <> show v)
      (Map.toUnfoldable counts :: Array (Tuple String Int))
  in
    intercalate "\n" lines

-- | Generic comparison test: compile PS circuit, load OCaml fixture, compare.
compareCircuit
  :: String -- fixture name (without .json)
  -> String -- compiled PS circuit JSON
  -> Either MultipleErrors (CircuitData StepField)
  -> Aff Unit
compareCircuit name psJson ocamlResult = do
  let
    psCircuit :: Either MultipleErrors (CircuitData StepField)
    psCircuit = readCircuitJson psJson
  case ocamlResult, psCircuit of
    Right ocaml, Right ps -> do
      let
        ocamlLen = Array.length ocaml.gates
        psLen = Array.length ps.gates
      log $ name <> " OCaml: pi=" <> show ocaml.publicInputSize <> ", gates=" <> show ocamlLen
      log $ name <> " PS:    pi=" <> show ps.publicInputSize <> ", gates=" <> show psLen
      log $ "OCaml gate types:\n" <> gateTypeSummary ocaml.gates
      log $ "PS gate types:\n" <> gateTypeSummary ps.gates
      ps.publicInputSize `shouldEqual` ocaml.publicInputSize
      -- Check gate count match first — don't silently drop gates
      if ocamlLen /= psLen then
        log $ "Gate count mismatch: OCaml=" <> show ocamlLen <> " PS=" <> show psLen
      else pure unit
      -- Compare gates that exist in both, report first divergence
      let diffs = diffCircuits ocaml ps
      log $ "Differing gate indices: " <> intercalate ", "
        (map (\d -> show d.index <> "(" <> show d.ocaml.kind <> ")") diffs)
      if Array.length diffs > 0 then do
        let
          first = unsafePartial $ Array.unsafeIndex diffs 0
          msg = "First divergence at gate " <> show first.index <> ":\n"
            <> "  OCaml: "
            <> formatGate first.index first.ocaml
            <> "\n"
            <> "  PS:    "
            <> formatGate first.index first.ps
            <> "\n"
            <> "Total differences: "
            <> show (Array.length diffs)
            <> " / "
            <> show (max ocamlLen psLen)
        liftEffect $ throw msg
      else pure unit
      -- If all zipped gates match but lengths differ, that's still a failure
      if ocamlLen /= psLen then
        liftEffect $ throw $ "Gate count mismatch: OCaml=" <> show ocamlLen <> " PS=" <> show psLen
          <> ". All "
          <> show (min ocamlLen psLen)
          <> " shared gates match."
      else pure unit
    Left e, _ -> liftEffect $ throw $ "Failed to parse OCaml JSON: " <> show e
    _, Left e -> liftEffect $ throw $ "Failed to parse PureScript JSON: " <> show e

loadFixture :: String -> Aff (Either MultipleErrors (CircuitData StepField))
loadFixture name = liftEffect do
  buf <- FS.readFile (fixtureDir <> name <> ".json")
  json <- Buffer.toString UTF8 buf
  pure (readCircuitJson json :: Either _ (CircuitData StepField))

-------------------------------------------------------------------------------
-- | Compiled circuit
-------------------------------------------------------------------------------

type V1 = Vector 1 (F StepField)
type V20 = Vector 20 (F StepField)
type V34 = Vector 34 (F StepField)
type V151 = Vector 151 (F StepField)

compilePow2Pow :: String
compilePow2Pow = circuitToJson @StepField $
  compilePure (Proxy @V1) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    pow2PowCircuit
    Kimchi.initialState

compileBCorrect :: String
compileBCorrect = circuitToJson @StepField $
  compilePure (Proxy @V20) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    bCorrectTestCircuit
    Kimchi.initialState

compileChallengeDigest :: String
compileChallengeDigest = circuitToJson @StepField $
  compilePure (Proxy @V34) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    challengeDigestTestCircuit
    Kimchi.initialState

compileFopStep :: String
compileFopStep = circuitToJson @StepField $
  compilePure (Proxy @V151) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    finalizeOtherProofStepCircuit
    Kimchi.initialState

-------------------------------------------------------------------------------
-- | Spec
-------------------------------------------------------------------------------

spec :: Spec Unit
spec =
  describe "FinalizeOtherProof CircuitJson" do
    it "pow2PowSquare sub-circuit" do
      ocaml <- loadFixture "pow2_pow_circuit"
      compareCircuit "pow2_pow" compilePow2Pow ocaml
    it "bCorrect sub-circuit" do
      ocaml <- loadFixture "b_correct_circuit"
      compareCircuit "b_correct" compileBCorrect ocaml
    it "challengeDigest sub-circuit" do
      ocaml <- loadFixture "challenge_digest_circuit"
      compareCircuit "challenge_digest" compileChallengeDigest ocaml
    it "Full: finalize_other_proof Step circuit" do
      ocaml <- loadFixture "finalize_other_proof_circuit"
      compareCircuit "full_fop" compileFopStep ocaml
