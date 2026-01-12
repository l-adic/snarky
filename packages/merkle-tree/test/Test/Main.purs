module Test.Main where

import Prelude

import Effect (Effect)
import Test.Data.MerkleTree as DynamicMerkleTree
import Test.Data.MerkleTree.Sized as SizedMerkleTree
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] do
  DynamicMerkleTree.spec
  SizedMerkleTree.spec