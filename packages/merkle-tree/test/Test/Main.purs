module Test.Main where

import Prelude

import Data.Identity (Identity(..))
import Data.Newtype (un)
import Effect (Effect)
import Effect.Aff (Aff)
import Test.Data.MerkleTree as DynamicMerkleTree
import Test.Data.MerkleTree.Sized as SizedMerkleTree
import Test.Snarky.Circuit.MerkleTree as CircuitMerkleTree
import Test.Spec (mapSpec)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Cfg

main :: Effect Unit
main = runSpecAndExitProcess'
  { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
  [ consoleReporter ]
  do
    mapSpec nat do
      DynamicMerkleTree.spec
      SizedMerkleTree.spec
    CircuitMerkleTree.spec
  where
  nat :: Identity ~> Aff
  nat x = pure $ un Identity x