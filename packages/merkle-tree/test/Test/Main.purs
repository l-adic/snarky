module Test.Main where

import Prelude

import Data.Identity (Identity(..))
import Data.Newtype (un)
import Effect (Effect)
import Effect.Aff (Aff)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiGate, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Test.Data.MerkleTree as DynamicMerkleTree
import Test.Data.MerkleTree.Sized as SizedMerkleTree
import Test.Data.MerkleTree.Sparse as SparseMerkleTree
import Test.Snarky.Circuit.MerkleTree as CircuitMerkleTree
import Test.Snarky.Circuit.SparseMerkleTree as CircuitSparseMerkleTree
import Test.Snarky.Circuit.Utils (TestConfig)
import Test.Spec (mapSpec)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Cfg

kimchiTestConfig :: forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)
kimchiTestConfig = { checker: eval, postCondition: Kimchi.postCondition, initState: Kimchi.initialState }

main :: Effect Unit
main = runSpecAndExitProcess'
  { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
  [ consoleReporter ]
  do
    mapSpec nat do
      DynamicMerkleTree.spec
      SizedMerkleTree.spec
      SparseMerkleTree.spec
    CircuitMerkleTree.spec kimchiTestConfig
    CircuitSparseMerkleTree.spec kimchiTestConfig
  where
  nat :: Identity ~> Aff
  nat x = pure $ un Identity x
