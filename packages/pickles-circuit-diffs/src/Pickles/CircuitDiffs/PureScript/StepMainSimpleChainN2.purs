module Pickles.CircuitDiffs.PureScript.StepMainSimpleChainN2
  ( compileStepMainSimpleChainN2
  , StepMainSimpleChainN2Params
  , class SimpleChainN2Advice
  , getSimpleChainN2Prev1
  , getSimpleChainN2Prev2
  ) where

-- | step_main circuit for the Simple_Chain N2 rule (2 previous proofs).
-- | Delegates to the generic Pickles.Step.Main.stepMain.
-- |
-- | Reference: mina/src/lib/crypto/pickles/dump_circuit_impl.ml (step_main_simple_chain_n2)

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Tuple.Nested (Tuple2, tuple2, (/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import Pickles.CircuitDiffs.PureScript.Common (StepArtifact, dummyWrapSg, mkStepArtifact, preComputeSelfStepDomainLog2)
import Pickles.Field (StepField)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Slots (Compiled, Slot)
import Pickles.Step.Main (RuleOutput, SlotVkBlueprintCompiled(..), stepMain)
import Pickles.Types (StatementIO)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, assertAny_, const_, equals_, exists, not_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type StepMainSimpleChainN2Params =
  { lagrangeAt :: LagrangeBaseLookup StepField
  , blindingH :: AffinePoint (F StepField)
  }

-- | Application-specific advice for the Simple_Chain N2 rule.
-- |
-- | The rule allocates two previous-proof app_state fields. In OCaml each
-- | is `exists StepField.typ ~compute:(fun () -> StepField.Constant.zero)`. We
-- | route them through this typeclass so the SAME rule definition serves
-- | both compilation (Effect throws) and proving.
class Monad m <= SimpleChainN2Advice m where
  getSimpleChainN2Prev1 :: Unit -> m (F StepField)
  getSimpleChainN2Prev2 :: Unit -> m (F StepField)

-- | Compilation instance: throws if evaluated. `exists` in CircuitBuilderT
-- | discards the AsProverT entirely so the throw never fires.
instance SimpleChainN2Advice Effect where
  getSimpleChainN2Prev1 _ = throw "SimpleChainN2Advice.getSimpleChainN2Prev1: not available during compilation"
  getSimpleChainN2Prev2 _ = throw "SimpleChainN2Advice.getSimpleChainN2Prev2: not available during compilation"

-- | Simple_Chain N2 rule: self_correct = (1 + prev1 + prev2 == self)
-- | Both proofs have the same proof_must_verify = not is_base_case.
-- | Reference: dump_circuit_impl.ml:4533-4566
simpleChainN2Rule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => SimpleChainN2Advice m
  => FVar StepField
  -> Snarky (KimchiConstraint StepField) t m (RuleOutput 2 (FVar StepField) Unit)
simpleChainN2Rule appState = do
  prev1 <- exists $ lift $ getSimpleChainN2Prev1 unit
  prev2 <- exists $ lift $ getSimpleChainN2Prev2 unit
  isBaseCase <- equals_ (const_ zero) appState
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (CVar.add_ (const_ one) prev1) prev2) appState
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev1 :< prev2 :< Vector.nil
    , proofMustVerify: proofMustVerify :< proofMustVerify :< Vector.nil
    , publicOutput: unit
    }

compileStepMainSimpleChainN2
  :: StepMainSimpleChainN2Params -> Effect StepArtifact
compileStepMainSimpleChainN2 params = do
  -- Both prev slots are self → both FOP domain log2s = this rule's own
  -- step domain log2. Resolved via two-pass compile (mirrors OCaml
  -- `Fix_domains.domains`).
  selfLog2 <- preComputeSelfStepDomainLog2 (runStepCompile 1)
  mkStepArtifact <$> runStepCompile selfLog2
  where
  runStepCompile selfLog2 =
    compile (Proxy @Unit) (Proxy @(Vector 67 (F StepField))) (Proxy @(KimchiConstraint StepField))
      -- Single-rule: mpvMax = len = 2, mpvPad = 0.
      ( \_ -> stepMain
          @(Tuple2 (Slot Compiled 2 1 (StatementIO (F StepField) Unit)) (Slot Compiled 2 1 (StatementIO (F StepField) Unit)))
          @(F StepField)
          @Unit
          @(F StepField)
          @( Tuple2 (StatementIO (F StepField) Unit) (StatementIO (F StepField) Unit)
          )
          @2
          @1
          @Unit
          @1
          simpleChainN2Rule
          { perSlotLagrangeAt: params.lagrangeAt :< params.lagrangeAt :< Vector.nil
          , blindingH: params.blindingH
          , perSlotFopDomainLog2s:
              (selfLog2 :< Vector.nil) :< (selfLog2 :< Vector.nil) :< Vector.nil
          , perSlotVkBlueprints: VkBlueprintShared /\ VkBlueprintShared /\ unit
          }
          dummyWrapSg
          -- Side-loaded VK carrier: two Cons slots,
          -- both compiled; carrier = `Unit /\ Unit /\ Unit`.
          (tuple2 unit unit)
      )
      Kimchi.initialState
