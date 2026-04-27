-- | PureScript-side analog of OCaml's `No_recursion_return` test
-- | (`mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:100-126`).
-- |
-- | The simplest pickles rule: `max_proofs_verified = N0`, no prevs,
-- | Output mode (input = Unit, output = Field), constant output `0`.
-- | Exercised here via the `Pickles.Prove.Compile` API end-to-end:
-- | one `compile` call returns a `prover.step` closure; one
-- | invocation produces a single proof; `verify` checks it.
-- |
-- | This is the minimal "happy path" for the compile + prover + verify
-- | flow. Heavier shapes (Simple_chain inductive, Tree heterogeneous)
-- | live in `Test.Pickles.Prove.SimpleChain` and
-- | `Test.Pickles.Prove.TreeProofReturn`; this module fills in the
-- | N0 case so all three pickles rule shapes have parallel test
-- | coverage.
-- |
-- | `nrrRule` is exported because `Test.Pickles.Verify.ExpandDeferredEq`
-- | reuses it to build a real NRR `CompiledProof` and feed
-- | `compiledProof.wrapDv` / `wrapDvInput` to its self-consistency check.
module Test.Pickles.Prove.NoRecursionReturn
  ( nrrRule
  , spec
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Data.Either (Either(..))
import Data.Int.Bits as Int
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles.Prove.Compile (Tag(..), compile, verify)
import Pickles.Prove.Step (StepRule)
import Pickles.Step.Prevs (PrevsSpecNil)
import Pickles.Types (StepField)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F, FVar, const_)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | The NRR inductive rule — Output mode, N=0, returns `F zero`.
-- | Reference: `mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:100-107`.
nrrRule :: StepRule 0 Unit Unit Unit (F StepField) (FVar StepField) Unit Unit
nrrRule _ = pure
  { prevPublicInputs: Vector.nil
  , proofMustVerify: Vector.nil
  , publicOutput: const_ zero
  }

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.NoRecursionReturn" do
  it "compile + prover.step end-to-end verify returns true" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    { prover, tag } <- liftEffect $ compile @PrevsSpecNil @Unit @(F StepField) @Unit @Effect
      { srs: { vestaSrs, pallasSrs }
      , perSlotImportedVKs: unit
      , debug: false
      , wrapDomainOverride: Nothing
      }
      nrrRule

    eResult <- liftEffect $ runExceptT $ prover.step { appInput: unit, prevs: unit }
    case eResult of
      Left e -> liftEffect $ Exc.throw ("prover.step: " <> show e)
      Right compiledProof ->
        verify (un Tag tag).verifier [ compiledProof ] `shouldEqual` true
