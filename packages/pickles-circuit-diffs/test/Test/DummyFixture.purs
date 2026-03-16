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
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Pickles.Dummy (computeDummyValues)
import Pickles.Types (StepField, WrapField)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Impl.Vesta as VestaImpl
import Snarky.Circuit.DSL (F(..))
import Snarky.Curves.Class (toBigInt)
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
    Nothing -> liftEffect $ pure unit -- skip missing keys
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

    let dv = computeDummyValues pallasSrs vestaSrs

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

  where
  showFp :: StepField -> String
  showFp = BigInt.toString <<< toBigInt

  showFq :: WrapField -> String
  showFq = BigInt.toString <<< toBigInt

  pow :: Int -> Int -> Int
  pow _ 0 = 1
  pow b n = b * pow b (n - 1)
