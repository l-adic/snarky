module Test.Poseidon.Main where

import Prelude

import Data.Either (Either(..))
import Data.Traversable (for_)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Poseidon (getMdsMatrix, getNumRounds, hash)
import Simple.JSON as JSON
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (vestaScalarFieldFromHexLe, vestaScalarFieldToHexLe)
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck ((/==), (===))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

-- | Test vector format from kimchi_test_vectors.json
type TestVector =
  { input :: Array String
  , output :: String
  }

type TestVectors =
  { name :: String
  , test_vectors :: Array TestVector
  }

-- | Load and parse test vectors from JSON file
loadTestVectors :: String -> Aff TestVectors
loadTestVectors path = liftEffect do
  buf <- FS.readFile path
  str <- Buffer.toString UTF8 buf
  case JSON.readJSON str of
    Left _ -> do
      -- Return empty on error, tests will fail appropriately
      pure { name: "error", test_vectors: [] }
    Right vectors -> pure vectors

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] spec

spec :: Spec Unit
spec = do
  describe "Poseidon Parameters" do
    it "should have 55 rounds for both curves" do
      getNumRounds (Proxy :: Proxy Pallas.BaseField) `shouldEqual` 55
      getNumRounds (Proxy :: Proxy Vesta.BaseField) `shouldEqual` 55

    it "should have 3x3 MDS matrix for both curves" do
      let pallasMds = getMdsMatrix (Proxy :: Proxy Pallas.BaseField)
      let vestaMds = getMdsMatrix (Proxy :: Proxy Vesta.BaseField)
      Vector.length pallasMds `shouldEqual` 3
      Vector.length vestaMds `shouldEqual` 3

  describe "Variable-Length Hash Properties" do
    it "hash function is deterministic (Pallas)" do
      quickCheck \(inputs :: Array Pallas.BaseField) ->
        let
          result1 = hash inputs
          result2 = hash inputs
        in
          result1 === result2

    it "hash function is deterministic (Vesta)" do
      quickCheck \(inputs :: Array Vesta.BaseField) ->
        let
          result1 = hash inputs
          result2 = hash inputs
        in
          result1 === result2

  describe "Zero-padding equivalence" do
    it "hash [], [zero], and [zero,zero] are all equal (Pallas)" do
      let
        h0 = hash ([] :: Array Pallas.BaseField)
        h1 = hash [ zero :: Pallas.BaseField ]
        h2 = hash [ zero, zero :: Pallas.BaseField ]
      h0 `shouldEqual` h1
      h1 `shouldEqual` h2

    it "hash [], [zero], and [zero,zero] are all equal (Vesta)" do
      let
        h0 = hash ([] :: Array Vesta.BaseField)
        h1 = hash [ zero :: Vesta.BaseField ]
        h2 = hash [ zero, zero :: Vesta.BaseField ]
      h0 `shouldEqual` h1
      h1 `shouldEqual` h2

    it "hash [x] == hash [x, zero] for any x (Pallas)" do
      quickCheck \(x :: Pallas.BaseField) ->
        hash [ x ] === hash [ x, zero ]

    it "hash [x] == hash [x, zero] for any x (Vesta)" do
      quickCheck \(x :: Vesta.BaseField) ->
        hash [ x ] === hash [ x, zero ]

    it "hash [x, zero] /= hash [x, zero, zero] (Pallas)" do
      quickCheck \(x :: Pallas.BaseField) ->
        hash [ x, zero ] /== hash [ x, zero, zero ]

    it "hash [x, zero] /= hash [x, zero, zero] (Vesta)" do
      quickCheck \(x :: Vesta.BaseField) ->
        hash [ x, zero ] /== hash [ x, zero, zero ]

    it "hash [a, b, c] == hash [a, b, c, zero] for any a, b, c (Pallas)" do
      quickCheck \(a :: Pallas.BaseField) (b :: Pallas.BaseField) (c :: Pallas.BaseField) ->
        hash [ a, b, c ] === hash [ a, b, c, zero ]

    it "hash [a, b, c] == hash [a, b, c, zero] for any a, b, c (Vesta)" do
      quickCheck \(a :: Vesta.BaseField) (b :: Vesta.BaseField) (c :: Vesta.BaseField) ->
        hash [ a, b, c ] === hash [ a, b, c, zero ]

  -- Test vectors from proof-systems/poseidon/export_test_vectors/test_vectors/hex_kimchi.json
  -- These use Pallas base field (= Vesta scalar field) with Kimchi parameters (55 rounds)
  describe "Kimchi Test Vectors (Pallas BaseField)" do
    it "matches reference implementation" do
      vectors <- loadTestVectors "packages/poseidon/test/fixtures/kimchi_test_vectors.json"
      vectors.name `shouldEqual` "kimchi"
      for_ vectors.test_vectors \tv -> do
        let
          input = map vestaScalarFieldFromHexLe tv.input
          result = hash input
          resultHex = vestaScalarFieldToHexLe result
        resultHex `shouldEqual` tv.output
