module Test.Poseidon.Main where

import Prelude

import Data.Array (length)
import Data.Maybe (fromJust)
import Data.Int (hexadecimal)
import Effect (Effect)
import Test.Spec (describe, it)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck)
import Poseidon as Poseidon
import Snarky.Curves.Pasta (PallasBaseField, VestaBaseField)
import Test.QuickCheck (Result, (===))

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  describe "Poseidon Parameters" do
    it "should have 55 rounds for both curves" do
      Poseidon.pallasPoseidonGetNumRounds `shouldEqual` 55
      Poseidon.vestaPoseidonGetNumRounds `shouldEqual` 55

    it "should have 3x3 MDS matrix for both curves" do
      let pallasMds = Poseidon.pallasPoseidonGetMdsMatrix
      let vestaMds = Poseidon.vestaPoseidonGetMdsMatrix
      length pallasMds `shouldEqual` 3
      length vestaMds `shouldEqual` 3

  describe "Variable-Length Hash Properties" do
    it "hash function is deterministic (Pallas)" do
      quickCheck \(inputs :: Array PallasBaseField) ->
        let
          result1 = Poseidon.pallasPoseidonHash inputs
          result2 = Poseidon.pallasPoseidonHash inputs
        in
          result1 === result2

    it "hash function is deterministic (Vesta)" do
      quickCheck \(inputs :: Array VestaBaseField) ->
        let
          result1 = Poseidon.vestaPoseidonHash inputs
          result2 = Poseidon.vestaPoseidonHash inputs
        in
          result1 === result2