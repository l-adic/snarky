-- | PureScript-side analog of OCaml's `Simple_chain` test
-- | (`mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:128-205`).
-- |
-- | Runs the inductive rule (`prev + 1`) at `max_proofs_verified = N1`
-- | through five iterations (b0..b4) via the `Pickles.Prove.Compile`
-- | API: a single `compile` call returns a `prover.step` closure that
-- | gets invoked once per iteration with the previous proof threaded
-- | as `InductivePrev`. The full chain is then handed to `verify` for
-- | end-to-end Pickles verification (stage 1 deferred-values expand,
-- | stage 2 IPA accumulator check, stage 3 kimchi `batch_verify`).
-- |
-- | The previous producer-style implementation (~2300 lines of manual
-- | step/wrap advice construction + trace emission) has been replaced
-- | with this compile-API-driven version. Producer-style scaffolding
-- | survives in `Test.Pickles.Prove.SimpleChain.B0Producer` /
-- | `B1Producer` (used by `Test.Pickles.Verify.VerifySmoke` and
-- | `Test.Pickles.Verify.ExpandDeferredEq` for byte-equality
-- | regression checks); those modules will be migrated once Tree-side
-- | callers also move to compile.
module Test.Pickles.Prove.SimpleChain
  ( spec
  , simpleChainRule
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Control.Monad.Trans.Class (lift) as MT
import Data.Either (Either(..))
import Data.Int.Bits as Int
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles.Prove.Compile (CompiledProof, PrevSlot(..), SlotWrapKey(..), Tag(..), compile, verify)
import Pickles.Prove.Step (StepRule)
import Pickles.Step.Advice (getPrevAppStates)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Types (StatementIO(..), StepField)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, assertAny_, const_, equals_, exists, not_)
import Snarky.Curves.Class (fromInt)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | Simple_chain inductive rule (verbatim from OCaml `dump_simple_chain.ml:62-82`).
-- |
-- | Asserts `self == prev + 1` OR `is_base_case (self == 0)`. Reads
-- | the prev's app-state value via `getPrevAppStates` (= OCaml's
-- | `Req.Prev_input` handler), so the same compiled rule serves
-- | every iteration: b0 supplies `BasePrev { dummyStatement }`,
-- | b_{k+1} supplies `InductivePrev compiledProof_b_k tag` whose
-- | `compiledProof.statement.input` is `b_k`'s self.
simpleChainRule
  :: StepRule 1
       (Tuple (StatementIO (F StepField) Unit) Unit)
       (F StepField)
       (FVar StepField)
       Unit
       Unit
       (F StepField)
       (FVar StepField)
simpleChainRule self = do
  prev <- exists $ MT.lift do
    Tuple stmt _ <- getPrevAppStates unit
    let StatementIO { input } = stmt
    pure input
  isBaseCase <- equals_ (const_ zero) self
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) self
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev :< Vector.nil
    , proofMustVerify: proofMustVerify :< Vector.nil
    , publicOutput: unit
    }

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.SimpleChain" do
  it "5-iteration step+wrap chain (b0..b4) proves end-to-end" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    { prover, tag } <- liftEffect $ compile
      @(PrevsSpecCons 1 (StatementIO (F StepField) Unit) PrevsSpecNil)
      @(F StepField)
      @Unit
      @(F StepField)
      @Effect
      { srs: { vestaSrs, pallasSrs }
      , perSlotImportedVKs: Tuple Self unit
      , debug: false
      }
      simpleChainRule

    let
      runStep
        :: PrevSlot (F StepField) 1 (StatementIO (F StepField) Unit) Unit
        -> F StepField
        -> Aff (CompiledProof 1 (StatementIO (F StepField) Unit) Unit Unit)
      runStep prevSlot appInput = do
        eRes <- liftEffect $ runExceptT $ prover.step
          { appInput, prevs: Tuple prevSlot unit }
        case eRes of
          Left e -> liftEffect $ Exc.throw ("prover.step: " <> show e)
          Right p -> pure p

      basePrev = BasePrev
        { dummyStatement: StatementIO { input: F (negate one), output: unit } }

    b0 <- runStep basePrev (F zero)
    b1 <- runStep (InductivePrev b0 tag) (F one)
    b2 <- runStep (InductivePrev b1 tag) (F (fromInt 2 :: StepField))
    b3 <- runStep (InductivePrev b2 tag) (F (fromInt 3 :: StepField))
    b4 <- runStep (InductivePrev b3 tag) (F (fromInt 4 :: StepField))

    verify (un Tag tag).verifier [ b0, b1, b2, b3, b4 ] `shouldEqual` true
