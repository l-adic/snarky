module Test.Pickles.Main where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Test.Pickles.Prove.NoRecursionReturn as NoRecursionReturn
import Test.Pickles.Prove.SimpleChain as SimpleChain
import Test.Pickles.Prove.TreeProofReturn as TreeProofReturn
import Test.Pickles.Verify.ExpandDeferredEq as ExpandDeferredEq
import Test.Spec (SpecT)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Cfg

-- | Pickles test suite.
-- |
-- | Each test runs a full prove flow (step compile → step solve+prove →
-- | wrap compile → wrap solve+prove, iterated for multi-step cases) and
-- | asserts that every produced proof validates via
-- | `ProofFFI.verifyOpeningProof` (kimchi batch_verify). That's the
-- | actual correctness check.
-- |
-- | Historical note: during byte-identity convergence with OCaml, these
-- | tests also emitted a `Pickles.Trace` transcript compared against a
-- | committed OCaml fixture. That scaffolding is now diagnostic — the
-- | trace fixtures live outside the git tree, regenerable via
-- | `tools/regen-fixtures.sh`, and only consumed by the manual diff
-- | scripts in `tools/`. Tests don't depend on any `.trace` files.
spec :: SpecT Aff Unit Aff Unit
spec = do
  NoRecursionReturn.spec
  SimpleChain.spec
  TreeProofReturn.spec
  ExpandDeferredEq.spec

main :: Effect Unit
main = runSpecAndExitProcess'
  { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
  [ consoleReporter ]
  spec
