module Pickles.CircuitDiffs.PureScript.StepMainTreeProofReturn
  ( compileStepMainTreeProofReturn
  , StepMainTreeProofReturnParams
  ) where

-- | step_main circuit for the Tree_proof_return rule.
-- |
-- | **N = 2**, **Output mode**, **heterogeneous prevs** at the rule
-- | level but homogeneous at the value-type level: both prev
-- | `public_input` slots are `StepField.typ` even though the first prev's
-- | rule has `max_proofs_verified = N0` (No_recursion_return) and the
-- | second is `self` with `max_proofs_verified = N2`. Our
-- | `Vector n (FVar StepField)` `prevPublicInputs` field handles this
-- | shape without needing an HList.
-- |
-- | Rule body computes `self = if is_base_case then 0 else 1 + prev`
-- | and exposes it as `publicOutput`.
-- |
-- | Reference: mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:315-392
-- |            (Tree_proof_return).
-- | OCaml dump target: `step_main_tree_proof_return_circuit.json`.

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple)
import Data.Tuple.Nested (Tuple2, tuple2, (/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Ref as Ref
import Pickles.CircuitDiffs.PureScript.Common (StepArtifact, dummyWrapSg, mkStepArtifact, preComputeSelfStepDomainLog2)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.CircuitDiffs.PureScript.StepMainNoRecursionReturn (StepMainNoRecursionReturnParams)
import Pickles.CircuitDiffs.PureScript.WrapMainNoRecursionReturn (compileWrapMainNoRecursionReturn)
import Pickles.Field (StepField)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Slots (Compiled, Slot)
import Pickles.Step.Advice (StepAdvice)
import Pickles.Step.Main (RuleOutput, SlotVkBlueprintCompiled(..), stepMain)
import Pickles.Step.Types (PerProofWitness)
import Pickles.Types (StatementIO(..), StepIPARounds, WrapIPARounds)
import Run as Run
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (AsProver, Bool(..), BoolVar, F(..), FVar, Snarky, const_, exists, if_, not_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (SplitField, Type2)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

-- | Tree_proof_return has HETEROGENEOUS prev wrap_domains (slot 0: 2^13
-- | from No_recursion_return; slot 1: 2^14 from self @
-- | override_wrap_domain:N1). Each slot needs its own lagrange lookup
-- | keyed on the slot's domain size.
type StepMainTreeProofReturnParams =
  { perSlotLagrangeAt :: Vector 2 (LagrangeBaseLookup 1 StepField)
  , blindingH :: AffinePoint (F StepField)
  -- SRS data for compiling NRR's wrap circuit (used to derive slot 0's
  -- known wrap key).
  , nrrWrapSrsData :: IvpWrapParams
  , nrrStepSrsData :: StepMainNoRecursionReturnParams
  }

-- | Tree_proof_return rule:
-- |   `self = if is_base_case then 0 else 1 + prev`
-- |   prev[0].public_input = no_recursive_input (always verified)
-- |   prev[1].public_input = prev (verified unless base case)
-- |   public_output = self
-- |
-- | Both prev app-states are read from the deferred prev-states getter
-- | (the prevs' `output` fields — Output mode); `is_base_case` is the
-- | `prev[1].output == -1` sentinel, matching the migrated
-- | `Test.Pickles.Prove.TreeProofReturn` rule. Reference:
-- | test_no_sideloaded.ml:354-390.
treeProofReturnRule
  :: forall r
   . PrimeField StepField
  => AsProver StepField r
       (Tuple2 (StatementIO Unit (F StepField)) (StatementIO Unit (F StepField)))
  -> Unit
  -> Snarky StepField (KimchiConstraint StepField) r
       (RuleOutput 2 (FVar StepField) (FVar StepField))
treeProofReturnRule getPrevStates _ = do
  no_recursive_input <- exists $ getPrevStates <#> \(StatementIO p1 /\ _) -> p1.output
  prev <- exists $ getPrevStates <#> \(_ /\ StatementIO p2 /\ _) -> p2.output
  is_base_case <- exists $ getPrevStates <#> \(_ /\ StatementIO p2 /\ _) -> p2.output == F (negate one)
  let proofMustVerify = not_ is_base_case
  self <- if_ is_base_case (const_ zero) (CVar.add_ (const_ one) prev)
  pure
    { prevPublicInputs: no_recursive_input :< prev :< Vector.nil
    -- prev[0] always verifies (Boolean.true_ in OCaml);
    -- prev[1] verifies iff not base case.
    , proofMustVerify:
        (coerce (const_ one :: FVar StepField) :: BoolVar StepField)
          :< proofMustVerify
          :< Vector.nil
    , publicOutput: self
    }

compileStepMainTreeProofReturn
  :: StepMainTreeProofReturnParams -> Effect StepArtifact
compileStepMainTreeProofReturn params = do
  nrrArt <- compileWrapMainNoRecursionReturn
    params.nrrWrapSrsData
    params.nrrStepSrsData
  selfLog2 <- preComputeSelfStepDomainLog2 (runStepCompile nrrArt 1)
  mkStepArtifact <$> runStepCompile nrrArt selfLog2
  where
  runStepCompile nrrArt selfLog2 = do
    throwawayCaptureRef <- Ref.new Nothing
    let
      dummyAdvice
        :: StepAdvice _ _ _ _ _ _
             ( Tuple
                 ( PerProofWitness 0 1 StepIPARounds WrapIPARounds (F StepField)
                     (Type2 (SplitField (F StepField) Boolean))
                     Boolean
                 )
                 ( Tuple
                     ( PerProofWitness 2 1 StepIPARounds WrapIPARounds (F StepField)
                         (Type2 (SplitField (F StepField) Boolean))
                         Boolean
                     )
                     Unit
                 )
             )
             _
             _
      dummyAdvice = unsafeCoerce unit
    Run.runBaseEffect $ compile (Proxy @Unit) (Proxy @(Vector 67 (F StepField))) (Proxy @(KimchiConstraint StepField))
      ( \_ -> stepMain
          @(Tuple2 (Slot Compiled 0 1 (StatementIO Unit (F StepField))) (Slot Compiled 2 1 (StatementIO Unit (F StepField))))
          @Unit
          @(F StepField)
          @(F StepField)
          @(Tuple2 (StatementIO Unit (F StepField)) (StatementIO Unit (F StepField)))
          @2
          @1
          @Unit
          @1
          treeProofReturnRule
          { perSlotLagrangeAt: params.perSlotLagrangeAt
          , blindingH: params.blindingH
          , perSlotFopDomainLog2s:
              (nrrArt.stepDomainLog2 :< Vector.nil)
                :< (selfLog2 :< Vector.nil)
                :< Vector.nil
          , perSlotVkBlueprints:
              VkBlueprintConst nrrArt.wrapVk /\ VkBlueprintShared /\ unit
          }
          dummyWrapSg
          (tuple2 unit unit)
          dummyAdvice
          throwawayCaptureRef
      )
