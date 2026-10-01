module Pickles.CircuitDiffs.PureScript.StepMainImportTwoPhaseChain
  ( compileStepMainImportTwoPhaseChain
  , compileStepMainImportTwoPhaseChainWithConstants
  , StepMainImportTwoPhaseChainParams
  ) where

-- | step_main circuit for an `External` slot over a two-domain import,
-- | beside a `Self` slot: the blockchain shape.
-- |
-- | **N = 2**, **Output mode**. Slot 0 verifies a proof of the separately
-- | compiled `two_phase_chain` (width 1), whose `make_zero` and
-- | `increment` branches run at different step domains, so its finalize
-- | dispatches over both (`domain_for_compiled`). Slot 1 is `self`
-- | (width 2), verified unless the base case.
-- |
-- | Rule body computes `self = if is_base_case then tx else prev + tx`
-- | and exposes it as `publicOutput`.
-- |
-- | OCaml reference: `dump_import_two_phase_chain.ml`. OCaml dump
-- | target: `step_main_import_two_phase_chain_circuit.json`. The prove
-- | test is `Test.Pickles.Prove.ImportTwoPhaseChain`.

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (Tuple2, (/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Ref as Ref
import Pickles.CircuitDiffs.PureScript.Common (DerivedKey, StepArtifact, WrapArtifact, dummyWrapSg, mkStepArtifact, preComputeSelfStepDomainLog2)
import Pickles.CircuitDiffs.PureScript.StepMainConstants (stepMainConstants)
import Pickles.CircuitDiffs.PureScript.StepMainTwoPhaseChainMakeZero (compileStepMainTwoPhaseChainMakeZero)
import Pickles.CircuitDiffs.PureScript.WrapMainTwoPhaseChain (WrapMainTwoPhaseChainParams, compileWrapMainTwoPhaseChain)
import Pickles.CircuitDiffs.Types (Constants)
import Pickles.Field (StepField, WrapField)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Slots (Slot)
import Pickles.Step.Main (RuleOutput, SlotVkBlueprint(..), StepMainSrsData, stepMain)
import Pickles.Step.Slots (PrevStatement(..), PrevValues, prevValues, slotWidthInt, slotWidthsOf, toPrevs)
import Pickles.Types (StatementIO(..))
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (AsProver, Bool(..), BoolVar, F(..), FVar, Snarky, const_, exists, if_, not_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

-- | Both slots read the Lagrange basis at 2^14: `two_phase_chain`'s wrap
-- | domain (N1), and self's at `override_wrap_domain:N1`.
type StepMainImportTwoPhaseChainParams =
  { slot0LagrangeAt :: LagrangeBaseLookup 1 StepField
  , slot1LagrangeAt :: LagrangeBaseLookup 1 StepField
  , blindingH :: AffinePoint (F StepField)
  -- SRS data for compiling `two_phase_chain`'s step and wrap circuits
  -- (slot 0's known wrap key and candidate step domains).
  , twoPhaseChainSrsData :: WrapMainTwoPhaseChainParams
  }

-- | Slot 0: a `two_phase_chain` proof, whose input is its value (width 1);
-- | slot 1: self (width 2), whose output is the state.
type ChainPrevsSpec =
  Tuple2 (Slot 1 (StatementIO (F StepField) Unit)) (Slot 2 (StatementIO Unit (F StepField)))

-- | The chain rule:
-- |   `self = if is_base_case then tx else prev + tx`
-- |   prev[0].public_input = tx (always verified)
-- |   prev[1].public_input = prev (verified unless base case)
-- |   public_output = self
chainRule
  :: forall r
   . PrimeField StepField
  => AsProver StepField r (PrevValues ChainPrevsSpec)
  -> Unit
  -> Snarky StepField (KimchiConstraint StepField) r
       (RuleOutput ChainPrevsSpec (FVar StepField))
chainRule getPrevStates _ = do
  tx <- exists $ getPrevStates <#> prevValues <#> \(StatementIO p1 /\ _) -> p1.input
  prev <- exists $ getPrevStates <#> prevValues <#> \(_ /\ StatementIO p2 /\ _) -> p2.output
  is_base_case <- exists $ getPrevStates <#> prevValues <#> \(_ /\ StatementIO p2 /\ _) -> p2.output == F (negate one)
  let proofMustVerify = not_ is_base_case
  self <- if_ is_base_case tx (CVar.add_ prev tx)
  pure
    -- prev[0] always verifies (Boolean.true_ in OCaml);
    -- prev[1] verifies iff not base case.
    { prevs: toPrevs $
        PrevStatement
          { publicInput: StatementIO { input: tx, output: unit }
          , proofMustVerify: (coerce (const_ one :: FVar StepField) :: BoolVar StepField)
          }
          /\ PrevStatement { publicInput: StatementIO { input: unit, output: prev }, proofMustVerify }
          /\ unit
    , publicOutput: self
    }

-- | The tag's width: `self` verifies two proofs, so `mpvMax = len = 2`.
type Mpv = 2

-- | The chain's step circuit.
compileStepMainImportTwoPhaseChain
  :: StepMainImportTwoPhaseChainParams -> Effect StepArtifact
compileStepMainImportTwoPhaseChain params =
  _.art <$> compileStepMainImportTwoPhaseChainWithConstants params

-- | The chain's step circuit, with the constants it bakes in
-- | (`stepMainConstants`) for the Lean `check_cs` harness.
compileStepMainImportTwoPhaseChainWithConstants
  :: StepMainImportTwoPhaseChainParams
  -> Effect { art :: StepArtifact, constants :: DerivedKey PallasG WrapField -> Effect Constants }
compileStepMainImportTwoPhaseChainWithConstants params = do
  -- `two_phase_chain`'s wrap artifact carries its key and `increment`'s
  -- step domain; `make_zero`'s comes from its own step compile.
  tpcArt <- compileWrapMainTwoPhaseChain params.twoPhaseChainSrsData
  makeZeroArt <- compileStepMainTwoPhaseChainMakeZero
    params.twoPhaseChainSrsData.makeZeroStepSrsData
  selfLog2 <- preComputeSelfStepDomainLog2
    (runStepCompile (srsData tpcArt makeZeroArt 1))
  art <- mkStepArtifact <$> runStepCompile (srsData tpcArt makeZeroArt selfLog2)
  pure
    { art
    , constants: \selfWrapKey -> do
        pallasSrs <- createCRS @WrapField
        stepMainConstants
          (map slotWidthInt (slotWidthsOf (Proxy @ChainPrevsSpec)))
          (srsData tpcArt makeZeroArt selfLog2)
          pallasSrs
          (Just tpcArt.wrapKey :< Just selfWrapKey :< Vector.nil)
    }
  where
  srsData :: WrapArtifact -> StepArtifact -> Int -> StepMainSrsData 2
  srsData tpcArt makeZeroArt selfLog2 =
    { blindingH: params.blindingH
    , perSlotFopDomainLog2s:
        -- slot 0: the import's step domains, in its branch order
        -- (make_zero, increment); slot 1: this compile's own
        (NEA.cons' makeZeroArt.stepDomainLog2 [ tpcArt.stepDomainLog2 ])
          :< (NEA.singleton selfLog2)
          :< Vector.nil
    , perSlotNumChunks: 1 :< 1 :< Vector.nil
    , perSlotVkBlueprints:
        BlueprintExternal params.slot0LagrangeAt tpcArt.wrapVk
          :< BlueprintSelf params.slot1LagrangeAt
          :< Vector.nil
    }

  runStepCompile srs = do
    throwawayCaptureRef <- Ref.new Nothing
    let
      dummyAdvice = unsafeCoerce unit
    compile noAdvice (Proxy @Unit) (Proxy @(Vector 67 (F StepField))) (Proxy @(KimchiConstraint StepField))
      ( \_ -> stepMain
          @ChainPrevsSpec
          @Unit
          @(F StepField)
          @(Tuple2 (StatementIO (F StepField) Unit) (StatementIO Unit (F StepField)))
          @Mpv
          chainRule
          srs
          dummyWrapSg
          dummyAdvice
          throwawayCaptureRef
      )
