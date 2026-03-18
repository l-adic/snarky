module Test.DummyFixture (spec) where

-- | Compare PureScript dummy values against OCaml fixture.
-- | Fixture: packages/pickles-circuit-diffs/test/fixtures/dummy_values.txt
-- | Generator: mina/src/lib/crypto/pickles/dump_dummy/dump_dummy.ml

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import JS.BigInt as BigInt
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Pickles.Dummy (computeDummySgValues, stepDummyUnfinalizedProof, wrapDummyUnfinalizedProof)
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

assertField :: String -> String -> Array (Tuple String String) -> Aff Unit
assertField label expected entries =
  case lookupFixture label entries of
    Nothing -> liftEffect $ throw ("Missing fixture key: " <> label)
    Just val -> expected `shouldEqual` val

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Dummy fixture comparison" do
  it "all dummy values match OCaml dump_dummy fixture" do
    buf <- liftEffect $ FS.readFile "packages/pickles-circuit-diffs/test/fixtures/dummy_values.txt"
    content <- liftEffect $ Buffer.toString UTF8 buf
    let entries = parseFixture content

    -- Create SRS for sg computation
    let pallasSrs = PallasImpl.pallasCrsCreate (2 `pow` 15) -- Tock/Wrap SRS
    let vestaSrs = VestaImpl.vestaCrsCreate (2 `pow` 16) -- Tick/Step SRS

    let dv = computeDummySgValues pallasSrs vestaSrs

    -- Wrap IPA challenges expanded
    for_ (Array.zip (Array.range 0 14) (Vector.toUnfoldable dv.ipa.wrap.challengesExpanded)) \(Tuple i v) ->
      assertField ("wrap_challenge_expanded_" <> show i) (showFq v) entries

    -- Step IPA challenges expanded
    for_ (Array.zip (Array.range 0 15) (Vector.toUnfoldable dv.ipa.step.challengesExpanded)) \(Tuple i v) ->
      assertField ("step_challenge_expanded_" <> show i) (showFp v) entries

    -- Wrap sg
    assertField "wrap_sg_x" (showFp dv.ipa.wrap.sg.x) entries
    assertField "wrap_sg_y" (showFp dv.ipa.wrap.sg.y) entries

    -- Step sg
    assertField "step_sg_x" (showFq dv.ipa.step.sg.x) entries
    assertField "step_sg_y" (showFq dv.ipa.step.sg.y) entries

    -- Unfinalized intermediate values
    assertField "unfinalized.zeta_expanded" (showFq dv.unfinalized.zetaExpanded) entries
    assertField "unfinalized.alpha_expanded" (showFq dv.unfinalized.alphaExpanded) entries

    -- Unfinalized plonk derived values
    let unwrapType2 (Type2 (F x)) = x
    assertField "unfinalized.plonk.perm" (showFq (unwrapType2 dv.unfinalized.plonk.perm)) entries
    assertField "unfinalized.plonk.zeta_to_srs_length" (showFq (unwrapType2 dv.unfinalized.plonk.zetaToSrsLength)) entries
    assertField "unfinalized.plonk.zeta_to_domain_size" (showFq (unwrapType2 dv.unfinalized.plonk.zetaToDomainSize)) entries

    -- Unfinalized other values
    assertField "unfinalized.combined_inner_product" (showFq dv.unfinalized.combinedInnerProduct) entries
    assertField "unfinalized.b" (showFq dv.unfinalized.b) entries
    assertField "unfinalized.sponge_digest" (showFq dv.unfinalized.spongeDigest) entries

  it "wrapDummyUnfinalizedProof matches OCaml Unfinalized.Constant.dummy" do
    buf <- liftEffect $ FS.readFile "packages/pickles-circuit-diffs/test/fixtures/dummy_values.txt"
    content <- liftEffect $ Buffer.toString UTF8 buf
    let entries = parseFixture content

    let
      du = wrapDummyUnfinalizedProof
      df = du.deferredValues
      unwrapType2 (Type2 (F x)) = x
      EndoScalar wrapEndo = (endoScalar :: EndoScalar Pallas.ScalarField)
      expandChal c = toFieldPure (SizedF.unwrapF c) wrapEndo

    -- Bulletproof challenges must equal the wrap IPA challenges (expanded)
    for_ (Array.zip (Array.range 0 14) (Vector.toUnfoldable df.bulletproofChallenges)) \(Tuple i c) ->
      assertField ("wrap_challenge_expanded_" <> show i) (showFq (expandChal c)) entries

    -- Plonk scalar challenges (expanded) must match fixture
    assertField "unfinalized.zeta_expanded" (showFq (expandChal df.plonk.zeta)) entries
    assertField "unfinalized.alpha_expanded" (showFq (expandChal df.plonk.alpha)) entries

    -- Plonk shifted scalars
    assertField "unfinalized.plonk.perm" (showFq (unwrapType2 df.plonk.perm)) entries
    assertField "unfinalized.plonk.zeta_to_srs_length" (showFq (unwrapType2 df.plonk.zetaToSrsLength)) entries
    assertField "unfinalized.plonk.zeta_to_domain_size" (showFq (unwrapType2 df.plonk.zetaToDomainSize)) entries

    -- CIP and b
    assertField "unfinalized.combined_inner_product" (showFq (unwrapType2 df.combinedInnerProduct)) entries
    assertField "unfinalized.b" (showFq (unwrapType2 df.b)) entries

    -- Sponge digest
    let F spongeDigest = du.spongeDigestBeforeEvaluations
    assertField "unfinalized.sponge_digest" (showFq spongeDigest) entries

  it "stepDummyUnfinalizedProof matches OCaml expand_deferred fixture" do
    buf <- liftEffect $ FS.readFile "packages/pickles-circuit-diffs/test/fixtures/dummy_values.txt"
    content <- liftEffect $ Buffer.toString UTF8 buf
    let entries = parseFixture content

    let
      du :: UnfinalizedProof _ (F StepField) (Type1 (F StepField)) Boolean
      du = stepDummyUnfinalizedProof
      df = du.deferredValues
      unwrapType1 (Type1 (F x)) = x
      EndoScalar stepEndo = (endoScalar :: EndoScalar Vesta.ScalarField)
      expandChal c = toFieldPure (SizedF.unwrapF c) stepEndo

    -- Plonk shifted scalars (Type1)
    assertField "step_deferred.plonk.perm" (showFp (unwrapType1 df.plonk.perm)) entries
    assertField "step_deferred.plonk.zeta_to_srs_length" (showFp (unwrapType1 df.plonk.zetaToSrsLength)) entries
    assertField "step_deferred.plonk.zeta_to_domain_size" (showFp (unwrapType1 df.plonk.zetaToDomainSize)) entries

    -- CIP and b (Type1)
    assertField "step_deferred.combined_inner_product" (showFp (unwrapType1 df.combinedInnerProduct)) entries
    assertField "step_deferred.b" (showFp (unwrapType1 df.b)) entries

    -- xi
    assertField "step_deferred.xi_packed" (showFp (SizedF.toField (SizedF.unwrapF df.xi))) entries
    assertField "step_deferred.xi_expanded" (showFp (expandChal df.xi)) entries

    -- Sponge digest
    let F spongeDigest = du.spongeDigestBeforeEvaluations
    assertField "step_deferred.sponge_digest" (showFp spongeDigest) entries

  where
  showFp :: StepField -> String
  showFp = BigInt.toString <<< toBigInt

  showFq :: WrapField -> String
  showFq = BigInt.toString <<< toBigInt

  pow :: Int -> Int -> Int
  pow _ 0 = 1
  pow b n = b * pow b (n - 1)
