module Test.Poseidon.Main where

import Prelude

import Data.Vector as Vector
import Effect (Effect)
import Poseidon.Class (getMdsMatrix, getNumRounds, hash)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck ((/==), (===))
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
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