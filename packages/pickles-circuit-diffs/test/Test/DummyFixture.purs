module Test.DummyFixture (spec) where

-- | Compare PureScript dummy values against OCaml fixture.
-- | Fixture: packages/pickles-circuit-diffs/test/fixtures/dummy_values.txt
-- | Generator: mina/src/lib/crypto/pickles/dump_dummy/dump_dummy.ml

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Data.String as String
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import JS.BigInt as BigInt
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Pickles.Dummy (computeDummySgValues, stepDummyUnfinalizedProof, wrapDummyUnfinalizedProof)
import Pickles.Dummy.SimpleChain (simpleChainDummyPlonk, simpleChainDummyPrevEvals, simpleChainDummySpongeDigest)
import Pickles.PlonkChecks (AllEvals) as PC
import Pickles.Types (StepField, WrapField)
import Pickles.Verify.Types (UnfinalizedProof)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Impl.Vesta as VestaImpl
import Snarky.Circuit.DSL (F(..))
import Snarky.Circuit.DSL.SizedF (toField, unwrapF) as SizedF
import Snarky.Circuit.Kimchi (Type1(..), toFieldPure)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, toBigInt)
import Snarky.Curves.Pallas (ScalarField) as Pallas
import Snarky.Curves.Vesta (ScalarField) as Vesta
import Snarky.Types.Shifted (Type2(..))
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | Parse the fixture file into (key, value) pairs
parseFixture :: String -> Array (Tuple String String)
parseFixture content =
  Array.mapMaybe parseLine (String.split (String.Pattern "\n") content)
  where
  parseLine line =
    case String.indexOf (String.Pattern ": ") line of
      Nothing -> Nothing
      Just idx ->
        let
          key = String.take idx line
          val = String.drop (idx + 2) line
        in
          if String.take 1 key == "#" || String.null key then Nothing
          else Just (Tuple key (String.trim val))

lookupFixture :: String -> Array (Tuple String String) -> Maybe String
lookupFixture key entries = do
  Tuple _ v <- Array.find (\(Tuple k _) -> k == key) entries
  pure v

-- | Assert a fixture value matches and record the key as checked.
assertField :: Ref (Set.Set String) -> String -> String -> Array (Tuple String String) -> Aff Unit
assertField checkedRef label expected entries = do
  liftEffect $ Ref.modify_ (Set.insert label) checkedRef
  case lookupFixture label entries of
    Nothing -> liftEffect $ throw ("Missing fixture key: " <> label)
    Just val -> expected `shouldEqual` val

-- | Load fixture and create a checked-keys ref. Returns (entries, checkedRef).
loadFixture :: Aff { entries :: Array (Tuple String String), checked :: Ref (Set.Set String) }
loadFixture = do
  buf <- liftEffect $ FS.readFile "packages/pickles-circuit-diffs/test/fixtures/dummy_values.txt"
  content <- liftEffect $ Buffer.toString UTF8 buf
  checked <- liftEffect $ Ref.new Set.empty
  pure { entries: parseFixture content, checked }

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Dummy fixture comparison" do
  -- Shared ref tracks which fixture keys have been asserted across all tests
  checkedRef <- liftEffect $ Ref.new Set.empty

  let
    assert _entries = assertField checkedRef

  it "all dummy values match OCaml dump_dummy fixture" do
    { entries } <- loadFixture
    let a = assert entries

    -- Create SRS for sg computation
    let pallasSrs = PallasImpl.pallasCrsCreate (2 `pow` 15) -- Tock/Wrap SRS
    let vestaSrs = VestaImpl.vestaCrsCreate (2 `pow` 16) -- Tick/Step SRS

    let dv = computeDummySgValues pallasSrs vestaSrs

    -- Wrap IPA challenges expanded
    for_ (Array.zip (Array.range 0 14) (Vector.toUnfoldable dv.ipa.wrap.challengesExpanded)) \(Tuple i v) ->
      a ("wrap_challenge_expanded_" <> show i) (showFq v) entries

    -- Step IPA challenges expanded
    for_ (Array.zip (Array.range 0 15) (Vector.toUnfoldable dv.ipa.step.challengesExpanded)) \(Tuple i v) ->
      a ("step_challenge_expanded_" <> show i) (showFp v) entries

    -- Wrap sg
    a "wrap_sg_x" (showFp dv.ipa.wrap.sg.x) entries
    a "wrap_sg_y" (showFp dv.ipa.wrap.sg.y) entries

    -- Step sg
    a "step_sg_x" (showFq dv.ipa.step.sg.x) entries
    a "step_sg_y" (showFq dv.ipa.step.sg.y) entries

    -- Unfinalized intermediate values
    a "unfinalized.zeta_expanded" (showFq dv.unfinalized.zetaExpanded) entries
    a "unfinalized.alpha_expanded" (showFq dv.unfinalized.alphaExpanded) entries

    -- Unfinalized plonk derived values
    let unwrapType2 (Type2 (F x)) = x
    a "unfinalized.plonk.perm" (showFq (unwrapType2 dv.unfinalized.plonk.perm)) entries
    a "unfinalized.plonk.zeta_to_srs_length" (showFq (unwrapType2 dv.unfinalized.plonk.zetaToSrsLength)) entries
    a "unfinalized.plonk.zeta_to_domain_size" (showFq (unwrapType2 dv.unfinalized.plonk.zetaToDomainSize)) entries

    -- Unfinalized other values
    a "unfinalized.combined_inner_product" (showFq dv.unfinalized.combinedInnerProduct) entries
    a "unfinalized.b" (showFq dv.unfinalized.b) entries
    a "unfinalized.sponge_digest" (showFq dv.unfinalized.spongeDigest) entries

  it "wrapDummyUnfinalizedProof matches OCaml Unfinalized.Constant.dummy" do
    { entries } <- loadFixture
    let a = assert entries

    let
      du = wrapDummyUnfinalizedProof
      df = du.deferredValues
      unwrapType2 (Type2 (F x)) = x
      EndoScalar wrapEndo = (endoScalar :: EndoScalar Pallas.ScalarField)
      expandChal c = toFieldPure (SizedF.unwrapF c) wrapEndo

    -- Bulletproof challenges must equal the wrap IPA challenges (expanded)
    for_ (Array.zip (Array.range 0 14) (Vector.toUnfoldable df.bulletproofChallenges)) \(Tuple i c) ->
      a ("wrap_challenge_expanded_" <> show i) (showFq (expandChal c)) entries

    -- Plonk scalar challenges (expanded) must match fixture
    a "unfinalized.zeta_expanded" (showFq (expandChal df.plonk.zeta)) entries
    a "unfinalized.alpha_expanded" (showFq (expandChal df.plonk.alpha)) entries

    -- Plonk shifted scalars
    a "unfinalized.plonk.perm" (showFq (unwrapType2 df.plonk.perm)) entries
    a "unfinalized.plonk.zeta_to_srs_length" (showFq (unwrapType2 df.plonk.zetaToSrsLength)) entries
    a "unfinalized.plonk.zeta_to_domain_size" (showFq (unwrapType2 df.plonk.zetaToDomainSize)) entries

    -- CIP and b
    a "unfinalized.combined_inner_product" (showFq (unwrapType2 df.combinedInnerProduct)) entries
    a "unfinalized.b" (showFq (unwrapType2 df.b)) entries

    -- Sponge digest
    let F spongeDigest = du.spongeDigestBeforeEvaluations
    a "unfinalized.sponge_digest" (showFq spongeDigest) entries

  it "stepDummyUnfinalizedProof matches OCaml expand_deferred fixture" do
    { entries } <- loadFixture
    let a = assert entries

    let
      du :: UnfinalizedProof _ (F StepField) (Type1 (F StepField)) Boolean
      du = stepDummyUnfinalizedProof
      df = du.deferredValues
      unwrapType1 (Type1 (F x)) = x
      EndoScalar stepEndo = (endoScalar :: EndoScalar Vesta.ScalarField)
      expandChal c = toFieldPure (SizedF.unwrapF c) stepEndo

    -- Plonk shifted scalars (Type1)
    a "step_deferred.plonk.perm" (showFp (unwrapType1 df.plonk.perm)) entries
    a "step_deferred.plonk.zeta_to_srs_length" (showFp (unwrapType1 df.plonk.zetaToSrsLength)) entries
    a "step_deferred.plonk.zeta_to_domain_size" (showFp (unwrapType1 df.plonk.zetaToDomainSize)) entries

    -- CIP and b (Type1)
    a "step_deferred.combined_inner_product" (showFp (unwrapType1 df.combinedInnerProduct)) entries
    a "step_deferred.b" (showFp (unwrapType1 df.b)) entries

    -- xi
    a "step_deferred.xi_packed" (showFp (SizedF.toField (SizedF.unwrapF df.xi))) entries
    a "step_deferred.xi_expanded" (showFp (expandChal df.xi)) entries

    -- Sponge digest
    let F spongeDigest = du.spongeDigestBeforeEvaluations
    a "step_deferred.sponge_digest" (showFp spongeDigest) entries

  it "every fixture output key is checked" do
    { entries } <- loadFixture
    checked <- liftEffect $ Ref.read checkedRef
    -- Input keys (prev_evals.*, step_input.*, step_deferred.ft_eval0) are intermediate
    -- values used by stepDummyUnfinalizedProof internally. They're verified indirectly
    -- through the final output values that depend on them.
    let
      isInputKey k =
        String.take 11 k == "prev_evals."
          || String.take 11 k == "step_input."
          || k == "step_deferred.ft_eval0"
    let outputKeys = Set.fromFoldable $ Array.filter (not <<< isInputKey) $ map (\(Tuple k _) -> k) entries
    let unchecked = Set.difference outputKeys checked
    when (not $ Set.isEmpty unchecked) do
      liftEffect $ throw $ "Unchecked fixture keys: " <> show (Set.toUnfoldable unchecked :: Array String)

  -- Second fixture: Simple_chain dummy proof values (from
  -- `dump_simple_chain_dummy.ml`, consumed by
  -- `Pickles.Dummy.SimpleChain`).
  describe "Pickles.Dummy.SimpleChain fixture comparison" do
    scCheckedRef <- liftEffect $ Ref.new Set.empty
    let scAssert = assertField scCheckedRef

    let
      loadScFixture :: Aff (Array (Tuple String String))
      loadScFixture = do
        buf <- liftEffect $ FS.readFile
          "packages/pickles-circuit-diffs/test/fixtures/simple_chain_dummy.txt"
        content <- liftEffect $ Buffer.toString UTF8 buf
        pure (parseFixture content)

    it "simpleChainDummyPlonk matches Proof.dummy N1 statement.plonk fixture" do
      entries <- loadScFixture
      -- Compare 128-bit challenge as Fp bigint (mirrors how
      -- dump_simple_chain_dummy.ml emits them via
      -- `Challenge.Constant.to_tick_field`).
      scAssert "simple_chain_dummy.plonk.alpha.raw"
        (showFp (SizedF.toField simpleChainDummyPlonk.alpha))
        entries
      scAssert "simple_chain_dummy.plonk.beta"
        (showFp (SizedF.toField simpleChainDummyPlonk.beta))
        entries
      scAssert "simple_chain_dummy.plonk.gamma"
        (showFp (SizedF.toField simpleChainDummyPlonk.gamma))
        entries
      scAssert "simple_chain_dummy.plonk.zeta.raw"
        (showFp (SizedF.toField simpleChainDummyPlonk.zeta))
        entries
      scAssert "simple_chain_dummy.sponge_digest"
        (showFq simpleChainDummySpongeDigest)
        entries

    it "simpleChainDummyPrevEvals matches Proof.dummy N1 prev_evals fixture" do
      entries <- loadScFixture
      let pe = (simpleChainDummyPrevEvals :: PC.AllEvals StepField)
      scAssert "simple_chain_dummy.prev_evals.ft_eval1" (showFp pe.ftEval1) entries
      scAssert "simple_chain_dummy.prev_evals.public_input.zeta.0"
        (showFp pe.publicEvals.zeta)
        entries
      scAssert "simple_chain_dummy.prev_evals.public_input.omega_zeta.0"
        (showFp pe.publicEvals.omegaTimesZeta)
        entries
      scAssert "simple_chain_dummy.prev_evals.z.zeta.0" (showFp pe.zEvals.zeta) entries
      scAssert "simple_chain_dummy.prev_evals.z.omega_zeta.0"
        (showFp pe.zEvals.omegaTimesZeta)
        entries

      let
        selectorNames =
          [ "generic_selector"
          , "poseidon_selector"
          , "complete_add_selector"
          , "mul_selector"
          , "emul_selector"
          , "endomul_scalar_selector"
          ]
        indexEvalsArr = (Vector.toUnfoldable pe.indexEvals :: Array _)
        witnessEvalsArr = (Vector.toUnfoldable pe.witnessEvals :: Array _)
        coeffEvalsArr = (Vector.toUnfoldable pe.coeffEvals :: Array _)
        sigmaEvalsArr = (Vector.toUnfoldable pe.sigmaEvals :: Array _)
      for_ (Array.zip selectorNames indexEvalsArr) \(Tuple name e) -> do
        scAssert ("simple_chain_dummy.prev_evals." <> name <> ".zeta.0")
          (showFp e.zeta)
          entries
        scAssert ("simple_chain_dummy.prev_evals." <> name <> ".omega_zeta.0")
          (showFp e.omegaTimesZeta)
          entries

      for_ (Array.zip (Array.range 0 14) witnessEvalsArr) \(Tuple i e) -> do
        scAssert ("simple_chain_dummy.prev_evals.w." <> show i <> ".zeta.0")
          (showFp e.zeta)
          entries
        scAssert ("simple_chain_dummy.prev_evals.w." <> show i <> ".omega_zeta.0")
          (showFp e.omegaTimesZeta)
          entries

      for_ (Array.zip (Array.range 0 14) coeffEvalsArr) \(Tuple i e) -> do
        scAssert ("simple_chain_dummy.prev_evals.coefficients." <> show i <> ".zeta.0")
          (showFp e.zeta)
          entries
        scAssert ("simple_chain_dummy.prev_evals.coefficients." <> show i <> ".omega_zeta.0")
          (showFp e.omegaTimesZeta)
          entries

      for_ (Array.zip (Array.range 0 5) sigmaEvalsArr) \(Tuple i e) -> do
        scAssert ("simple_chain_dummy.prev_evals.s." <> show i <> ".zeta.0")
          (showFp e.zeta)
          entries
        scAssert ("simple_chain_dummy.prev_evals.s." <> show i <> ".omega_zeta.0")
          (showFp e.omegaTimesZeta)
          entries

    it "every simple_chain fixture key is checked" do
      entries <- loadScFixture
      checked <- liftEffect $ Ref.read scCheckedRef
      let outputKeys = Set.fromFoldable $ map (\(Tuple k _) -> k) entries
      let unchecked = Set.difference outputKeys checked
      when (not $ Set.isEmpty unchecked) do
        liftEffect $ throw $ "Unchecked simple_chain fixture keys: "
          <> show (Set.toUnfoldable unchecked :: Array String)

  where
  showFp :: StepField -> String
  showFp = BigInt.toString <<< toBigInt

  showFq :: WrapField -> String
  showFq = BigInt.toString <<< toBigInt

  pow :: Int -> Int -> Int
  pow _ 0 = 1
  pow b n = b * pow b (n - 1)
