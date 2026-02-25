-- | Circuit JSON comparison tests for FinalizeOtherProof sub-circuits.
-- |
-- | Each sub-circuit matches a specific step of OCaml's
-- | `Step_verifier.finalize_other_proof` (step_verifier.ml:828-1165).
-- | The corresponding OCaml dumps are in dump_circuit_impl.ml.
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
import Pickles.IPA as IPA
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (PointEval)
import Pickles.Linearization.FFI as LinFFI
import Pickles.PlonkChecks (AllEvals, absorbAllEvals, plonkArithmeticCheckCircuit)
import Pickles.PlonkChecks.CombinedInnerProduct (combinedInnerProductCheckCircuitM)
import Pickles.PlonkChecks.GateConstraints (GateConstraintInput)
import Pickles.PlonkChecks.Permutation (PermutationInput)
import Pickles.Sponge (absorb, evalSpongeM, initialSpongeCircuit, liftSnarky, squeezeScalarChallenge)
import Pickles.Step.ChallengeDigest (challengeDigestCircuit)
import Pickles.Types (StepField)
import Pickles.Verify.Types (expandPlonkMinimalCircuit)
import Snarky.Backend.Compile (compilePure)
import Snarky.Backend.Kimchi.CircuitJson (CircuitData, CircuitGateData, circuitToJson, diffCircuits, formatGate, readCircuitJson)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, SizedF, Snarky, and_, const_, equals_, isEqual, mul_)
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

-- | Domain generator for the step domain
domainGenerator :: StepField
domainGenerator = LinFFI.domainGenerator domainLog2

-- | Domain shifts (7 permutation shifts)
domainShifts :: Vector 7 StepField
domainShifts = LinFFI.domainShifts domainLog2

-- | Endo coefficient for scalar challenge expansion (= Wrap_inner_curve.scalar)
stepEndo :: StepField
stepEndo = let EndoScalar e = endoScalar @Vesta.BaseField @StepField in e

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

-- | Parse a PointEval from two consecutive array positions
pointEval :: forall n f. Vector n f -> Int -> PointEval f
pointEval inputs i =
  { zeta: unsafeIdx inputs i
  , omegaTimesZeta: unsafeIdx inputs (i + 1)
  }

-- | Treat a field variable as a 128-bit scalar challenge (for circuit compilation)
asSizedF128 :: forall f. FVar f -> SizedF 128 (FVar f)
asSizedF128 = unsafeCoerce

-- | Treat a field variable as a boolean (for circuit compilation)
asBool :: forall f. FVar f -> BoolVar f
asBool = unsafeCoerce

-------------------------------------------------------------------------------
-- | Sub-circuit 1: expand_plonk (Steps 2+4)
-- |
-- | Expands scalar challenges alpha, zeta via endo.
-- | Computes zetaw = domain#generator * zeta.
-- |
-- | OCaml reference: step_verifier.ml:867-889
-- |   let scalar = SC.to_field_checked ~endo:Endo.Wrap_inner_curve.scalar in
-- |   let plonk = map_challenges ~f:Fn.id ~scalar plonk in
-- |   let zetaw = Field.mul domain#generator plonk.zeta in
-- |
-- | Input layout (4 fields):
-- |   0: alpha (scalar_challenge inner)
-- |   1: beta (plain field, passed through)
-- |   2: gamma (plain field, passed through)
-- |   3: zeta (scalar_challenge inner)
-------------------------------------------------------------------------------

expandPlonkCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 4 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
expandPlonkCircuit inputs = do
  let
    endoVar = const_ stepEndo
    rawAlpha = asSizedF128 $ unsafeIdx inputs 0
    rawZeta = asSizedF128 $ unsafeIdx inputs 3

  -- Step 2: scalar challenge expansion (only alpha and zeta go through endo)
  _alpha <- toField rawAlpha endoVar
  zeta <- toField rawZeta endoVar

  -- Step 4: zetaw = generator * zeta
  void $ mul_ (const_ domainGenerator) zeta

-------------------------------------------------------------------------------
-- | Sub-circuit 2: challenge_digest (Step 7a)
-- |
-- | Computes challenge digest from prev_challenges using opt_sponge.
-- |
-- | OCaml reference: step_verifier.ml:923-933
-- |   let opt_sponge = Opt_sponge.create sponge_params in
-- |   Vector.iter2 actual_width_mask prev_challenges
-- |     ~f:(fun keep chals ->
-- |       Vector.iter chals ~f:(fun chal ->
-- |         Opt_sponge.absorb opt_sponge (keep, chal))) ;
-- |   Opt_sponge.squeeze opt_sponge
-- |
-- | Input layout (34 fields):
-- |   0-1:   mask (2 booleans)
-- |   2-17:  prev_challenges[0] (16 fields)
-- |   18-33: prev_challenges[1] (16 fields)
-------------------------------------------------------------------------------

challengeDigestStandaloneCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 34 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
challengeDigestStandaloneCircuit inputs = do
  let
    mask :: Vector 2 (BoolVar StepField)
    mask = Vector.generate \j -> asBool $ unsafeIdx inputs (getFinite j)

    prevChallenges :: Vector 2 (Vector 16 (SizedF 128 (FVar StepField)))
    prevChallenges = Vector.generate \j ->
      Vector.generate \k ->
        asSizedF128 $ unsafeIdx inputs (2 + 16 * getFinite j + getFinite k)

  -- Run opt_sponge in a fresh sponge (OCaml creates a new Opt_sponge here)
  evalSpongeM initialSpongeCircuit do
    void $ challengeDigestCircuit { mask, oldChallenges: prevChallenges }

-------------------------------------------------------------------------------
-- | Sub-circuit 3: b_correct (Step 12)
-- |
-- | Expands 16 bulletproof challenges via endo, builds challenge polynomial,
-- | evaluates at zeta and zetaw, checks b = b(zeta) + r * b(zetaw).
-- |
-- | OCaml reference: step_verifier.ml:1126-1141
-- |   let bulletproof_challenges = compute_challenges ~scalar bulletproof_challenges in
-- |   let challenge_poly = unstage (challenge_polynomial (...)) in
-- |   let b_actual = challenge_poly zeta + (r * challenge_poly zetaw) in
-- |   let b_used = Shifted_value.Type1.to_field ~shift:shift1 b in
-- |   equal b_used b_actual
-- |
-- | Input layout (20 fields):
-- |   0-15:  bulletproof_challenges (16 scalar_challenge inners)
-- |   16:    zeta (already expanded)
-- |   17:    zetaw (already expanded)
-- |   18:    r (already expanded)
-- |   19:    claimed_b (Type1 shifted value)
-------------------------------------------------------------------------------

bCorrectStandaloneCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 20 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
bCorrectStandaloneCircuit inputs = do
  let
    endoVar = const_ stepEndo

    -- Parse 16 scalar challenge inners
    rawChallenges :: Vector 16 (SizedF 128 (FVar StepField))
    rawChallenges = Vector.generate \j ->
      asSizedF128 $ unsafeIdx inputs (getFinite j)

    zeta = unsafeIdx inputs 16
    zetaw = unsafeIdx inputs 17
    r = unsafeIdx inputs 18
    claimedB = unsafeIdx inputs 19

  -- OCaml's Vector.map evaluates side effects in reverse order (right-to-left
  -- :: evaluation), so toField constraints for challenge[15] are emitted first.
  -- We reverse before expanding, then reverse back, to match constraint order
  -- while preserving the correct mathematical ordering for bPoly.
  expandedChallengesRev <- for (Vector.reverse rawChallenges) \c -> toField c endoVar
  let expandedChallenges = Vector.reverse expandedChallengesRev

  void $ IPA.bCorrectCircuit
    { challenges: expandedChallenges
    , zeta
    , zetaOmega: zetaw
    , evalscale: r
    , expectedB: fromShiftedType1Circuit (Type1 claimedB)
    }

-------------------------------------------------------------------------------
-- | Full FinalizeOtherProof wrapper circuit (for reference)
-------------------------------------------------------------------------------

-- | Parse the 151-field flat array into AllEvals.
parseAllEvals :: forall n f. Vector n f -> AllEvals f
parseAllEvals inputs =
  { ftEval1: unsafeIdx inputs 117
  , publicEvals: pointEval inputs 29
  , zEvals: pointEval inputs 91
  , indexEvals: Vector.generate \j -> pointEval inputs (105 + 2 * getFinite j)
  , witnessEvals: Vector.generate \j -> pointEval inputs (31 + 2 * getFinite j)
  , coeffEvals: Vector.generate \j -> pointEval inputs (61 + 2 * getFinite j)
  , sigmaEvals: Vector.generate \j -> pointEval inputs (93 + 2 * getFinite j)
  }

finalizeOtherProofWrapperCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 151 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
finalizeOtherProofWrapperCircuit inputs = do
  let
    endoVar = const_ stepEndo
    rawAlpha = asSizedF128 $ unsafeIdx inputs 0
    rawBeta = asSizedF128 $ unsafeIdx inputs 1
    rawGamma = asSizedF128 $ unsafeIdx inputs 2
    rawZeta = asSizedF128 $ unsafeIdx inputs 3
    claimedPerm = Type1 $ unsafeIdx inputs 6
    claimedCIP = Type1 $ unsafeIdx inputs 7
    claimedB = Type1 $ unsafeIdx inputs 8
    rawXi = asSizedF128 $ unsafeIdx inputs 9

    bulletproofChallenges :: Vector 16 (SizedF 128 (FVar StepField))
    bulletproofChallenges = Vector.generate \j ->
      asSizedF128 $ unsafeIdx inputs (10 + getFinite j)

    mask :: Vector 2 (BoolVar StepField)
    mask = Vector.generate \j -> asBool $ unsafeIdx inputs (26 + getFinite j)

    allEvals = parseAllEvals inputs

    prevChallenges :: Vector 2 (Vector 16 (SizedF 128 (FVar StepField)))
    prevChallenges = Vector.generate \j ->
      Vector.generate \k ->
        asSizedF128 $ unsafeIdx inputs (118 + 16 * getFinite j + getFinite k)

    spongeDigest = unsafeIdx inputs 150

  plonk <- expandPlonkMinimalCircuit endoVar
    { alpha: rawAlpha, beta: rawBeta, gamma: rawGamma, zeta: rawZeta }

  evalSpongeM initialSpongeCircuit do
    absorb spongeDigest
    challengeDigest <- challengeDigestCircuit { mask, oldChallenges: prevChallenges }
    absorb challengeDigest
    absorbAllEvals allEvals
    squeezedXi <- squeezeScalarChallenge
    xiCorrect <- liftSnarky $ isEqual squeezedXi rawXi
    rawR <- squeezeScalarChallenge
    polyscale <- liftSnarky $ toField squeezedXi endoVar
    evalscale <- liftSnarky $ toField rawR endoVar
    zetaOmega <- liftSnarky $ mul_ plonk.zeta (const_ domainGenerator)

    let
      permInput :: PermutationInput (FVar StepField)
      permInput =
        { w: map _.zeta (Vector.take @7 allEvals.witnessEvals)
        , sigma: map _.zeta allEvals.sigmaEvals
        , z: allEvals.zEvals
        , shifts: map const_ domainShifts
        , alpha: plonk.alpha
        , beta: plonk.beta
        , gamma: plonk.gamma
        , zkPolynomial: const_ zero
        , zetaToNMinus1: const_ zero
        , omegaToMinusZkRows: const_ zero
        , zeta: plonk.zeta
        }

      gateInput :: GateConstraintInput (FVar StepField)
      gateInput =
        { witnessEvals: allEvals.witnessEvals
        , coeffEvals: map _.zeta allEvals.coeffEvals
        , indexEvals: allEvals.indexEvals
        , alpha: plonk.alpha
        , beta: plonk.beta
        , gamma: plonk.gamma
        , jointCombiner: const_ zero
        , vanishesOnZk: const_ zero
        , lagrangeFalse0: const_ zero
        , lagrangeTrue1: const_ zero
        }

    computedCIP <- liftSnarky $
      combinedInnerProductCheckCircuitM Linearization.pallas domainLog2 plonk.zeta
        { polyscale, evalscale }
        { permInput
        , gateInput
        , publicEvalForFt: const_ zero
        , publicPointEval: allEvals.publicEvals
        , ftEval1: allEvals.ftEval1
        , zEvals: allEvals.zEvals
        , indexEvals: allEvals.indexEvals
        , witnessEvals: allEvals.witnessEvals
        , coeffEvals: allEvals.coeffEvals
        , sigmaEvals: allEvals.sigmaEvals
        }
    cipCorrect <- liftSnarky $
      equals_ (fromShiftedType1Circuit claimedCIP) computedCIP

    expandedChallenges <- liftSnarky $
      for bulletproofChallenges \c -> toField c endoVar
    bOk <- liftSnarky $ IPA.bCorrectCircuit
      { challenges: expandedChallenges
      , zeta: plonk.zeta
      , zetaOmega
      , evalscale
      , expectedB: fromShiftedType1Circuit claimedB
      }

    permOk <- liftSnarky $ plonkArithmeticCheckCircuit { unshift: fromShiftedType1Circuit }
      { claimedPerm, permInput }

    liftSnarky do
      a <- and_ xiCorrect cipCorrect
      b <- and_ bOk permOk
      void $ and_ a b

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
-- | Compiled circuits
-------------------------------------------------------------------------------

type V4 = Vector 4 (F StepField)
type V20 = Vector 20 (F StepField)
type V34 = Vector 34 (F StepField)
type V151 = Vector 151 (F StepField)

compileExpandPlonk :: String
compileExpandPlonk = circuitToJson @StepField $
  compilePure (Proxy @V4) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    expandPlonkCircuit
    Kimchi.initialState

compileChallengeDigest :: String
compileChallengeDigest = circuitToJson @StepField $
  compilePure (Proxy @V34) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    challengeDigestStandaloneCircuit
    Kimchi.initialState

compileBCorrect :: String
compileBCorrect = circuitToJson @StepField $
  compilePure (Proxy @V20) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    bCorrectStandaloneCircuit
    Kimchi.initialState

compileFopStep :: String
compileFopStep = circuitToJson @StepField $
  compilePure (Proxy @V151) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    finalizeOtherProofWrapperCircuit
    Kimchi.initialState

-------------------------------------------------------------------------------
-- | Spec
-------------------------------------------------------------------------------

spec :: Spec Unit
spec =
  describe "FinalizeOtherProof CircuitJson" do
    it "Sub-circuit 1: expand_plonk (Steps 2+4)" do
      ocaml <- loadFixture "expand_plonk_circuit"
      compareCircuit "expand_plonk" compileExpandPlonk ocaml

    it "Sub-circuit 2: challenge_digest (Step 7a)" do
      ocaml <- loadFixture "challenge_digest_circuit"
      compareCircuit "challenge_digest" compileChallengeDigest ocaml

    it "Sub-circuit 3: b_correct (Step 12)" do
      ocaml <- loadFixture "b_correct_circuit"
      compareCircuit "b_correct" compileBCorrect ocaml

    it "Full: Step (Tick/Fp) circuit structure comparison" do
      ocaml <- loadFixture "finalize_other_proof_circuit"
      compareCircuit "full_fop" compileFopStep ocaml
