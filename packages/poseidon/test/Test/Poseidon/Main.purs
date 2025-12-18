module Test.Poseidon.Main where

import Prelude

import Effect (Effect)
import Test.Spec (describe, it)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck)
import Type.Proxy (Proxy(..))
import Poseidon.Class (getNumRounds, getMdsMatrix, hash)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.Vector as Vector
import Test.QuickCheck ((===))

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