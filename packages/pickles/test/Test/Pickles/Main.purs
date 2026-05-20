module Test.Pickles.Main where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Test.Pickles.Prove.Chunks2 as Chunks2
import Test.Pickles.Prove.Chunks4 as Chunks4
import Test.Pickles.Prove.CompileValidation as CompileValidation
import Test.Pickles.Prove.NoRecursionReturn as NoRecursionReturn
import Test.Pickles.Prove.SideLoadedMain as SideLoadedMain
import Test.Pickles.Prove.SimpleChain as SimpleChain
import Test.Pickles.Prove.TreeProofReturn as TreeProofReturn
import Test.Pickles.Prove.TwoPhaseChain as TwoPhaseChain
import Test.Pickles.SharedSrs (buildSharedSrs)
import Test.Pickles.Sideload.DigestEqNrrSpec as SideloadDigestEqNrr
import Test.Pickles.Sideload.RoundTripMainChildSpec as SideloadRoundTripMainChild
import Test.Pickles.Sideload.RoundTripNrrSpec as SideloadRoundTripNrr
import Test.Pickles.Sideload.VerifyNrrSpec as SideloadVerifyNrr
import Test.Spec (SpecT, beforeAll)
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
-- | Specs that take a `SharedSrs` per-test value get the SRS built once
-- | via `beforeAll buildSharedSrs` (memoized for the whole pickles suite —
-- | the lagrange-basis cache attached to each SRS is then populated once
-- | and reused across every test, saving ~tens of seconds per run).
-- | Specs that don't need the SRS sit outside the `beforeAll` block.
spec :: SpecT Aff Unit Aff Unit
spec = beforeAll buildSharedSrs do
  CompileValidation.spec
  NoRecursionReturn.spec
  SimpleChain.spec
  Chunks2.spec
  Chunks4.spec
  SideLoadedMain.spec
  TreeProofReturn.spec
  TwoPhaseChain.spec
  SideloadRoundTripNrr.spec
  SideloadRoundTripMainChild.spec
  SideloadDigestEqNrr.spec
  SideloadVerifyNrr.spec

main :: Effect Unit
main = runSpecAndExitProcess'
  { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
  [ consoleReporter ]
  spec
