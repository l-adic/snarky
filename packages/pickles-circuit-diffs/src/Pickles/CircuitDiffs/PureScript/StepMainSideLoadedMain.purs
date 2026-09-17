module Pickles.CircuitDiffs.PureScript.StepMainSideLoadedMain
  ( compileStepMainSideLoadedMain
  , StepMainSideLoadedMainParams
  ) where

-- | step_main circuit for the side-loaded variant of Simple_chain
-- | (parent rule: mpv=N1, single side-loaded prev with mpv=N2).
-- |
-- | Reference: OCaml `dump_side_loaded_main.ml`. Fixture:
-- | `step_main_side_loaded_main_circuit.json` — 11862 gates, pi=34.
-- |
-- | Same rule body as `StepMainSimpleChain.simpleChainRule`; the only
-- | difference is the slot's blueprint (`BlueprintSideLoaded` instead
-- | of `BlueprintSelf`), which routes the slot's wrap-VK, step-domain,
-- | and max-proofs-verified through the runtime side-loaded VK.

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple)
import Data.Tuple.Nested (Tuple1, tuple1, (/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Ref as Ref
import Pickles.CircuitDiffs.PureScript.Common (StepArtifact, dummyWrapSg, mkStepArtifact)
import Pickles.Constants (zkRowsByDefault)
import Pickles.Field (StepField)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Sideload.BoundVk.Internal (unsafeUnboundVk)
import Pickles.Slots (SideLoadedSlot)
import Pickles.Step.Advice (StepAdvice)
import Pickles.Step.Main (RuleOutput, SlotVkBlueprint(..), stepMain)
import Pickles.Step.Slots (PrevValues, SideLoadedPrevStatement(..), SideLoadedPrevValue, prevValues, toPrevs)
import Pickles.Step.Types (PerProofWitness)
import Pickles.Types (StatementIO(..), StepIPARounds, WrapIPARounds)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (AsProver, F, FVar, Snarky, assertAny_, const_, equals_, exists, true_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (SplitField, Type2)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

-- | Parameters for the side-loaded main fixture.
-- |
-- | * `lagrangeAt` — placeholder per-slot table; ignored by
-- |   `Step.Main` on the side-loaded path (only consumed for
-- |   compiled slots).
-- | * `sideloadedPerDomainLagrangeAt` — three SRS lagrange lookups
-- |   at log2 ∈ {13, 14, 15} (= the wrap-domain log2s for
-- |   `actualWrapDomainSize ∈ {N0, N1, N2}`). `Step.Main`
-- |   one-hot-muxes among them at runtime.
type StepMainSideLoadedMainParams =
  { lagrangeAt :: LagrangeBaseLookup 1 StepField
  , sideloadedPerDomainLagrangeAt ::
      Vector 3 (Int -> Vector 1 (AffinePoint (F StepField)))
  , blindingH :: AffinePoint (F StepField)
  }

-- | Side-loaded main rule body: same as `simpleChainRule` —
-- | `selfCorrect = (1 + prev == self) || isBaseCase`. The side-loaded
-- | distinction shows up in the spec / vkCarrier, not the rule body.
sideLoadedMainRule
  :: forall r
   . PrimeField StepField
  => AsProver StepField r (PrevValues SideLoadedMainPrevsSpec)
  -> FVar StepField
  -> Snarky StepField (KimchiConstraint StepField) r
       (RuleOutput SideLoadedMainPrevsSpec Unit)
sideLoadedMainRule getPrevStates appState = do
  prev <- exists $ getPrevStates <#> prevValues <#> \(slot /\ _) ->
    let StatementIO p1 = slot.statement in p1.input
  -- The OCaml rule allocates the key here, between the prev statement
  -- and the base-case comparison, and hands it to
  -- `Side_loaded.in_circuit` without binding it to anything.
  vk <- exists $ getPrevStates <#> prevValues <#> \(slot /\ _) -> slot.verificationKey
  isBaseCase <- equals_ (const_ zero) appState
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) appState
  assertAny_ [ selfCorrect, isBaseCase ]
  -- `proofMustVerify = true_` (constant) is required for byte-parity:
  -- a non-constant Cvar makes downstream `if_ proofMustVerify ...`
  -- emit ~25 extra Generic gates that vanish under `true_` constant-
  -- folding. Reference: OCaml `dump_side_loaded_main.ml:179`.
  pure
    { prevs: toPrevs $
        SideLoadedPrevStatement
          { publicInput: StatementIO { input: prev, output: unit }
          , proofMustVerify: true_
          -- The OCaml rule binds nothing, and this harness reproduces
          -- its constraint system.
          , verificationKey: unsafeUnboundVk vk
          }
          /\ unit
    , publicOutput: unit
    }

-- | The rule's one side-loaded prev slot, at the tag's compile-time
-- | upper bound `N2`.
type SideLoadedMainPrevsSpec = Tuple1 (SideLoadedSlot 2 (StatementIO (F StepField) Unit))

compileStepMainSideLoadedMain
  :: StepMainSideLoadedMainParams -> Effect StepArtifact
compileStepMainSideLoadedMain params = do
  throwawayCaptureRef <- Ref.new Nothing
  -- `carrier` (value-side per-proof witness carrier) is not determined
  -- by `stepMain`'s var-side `StepSlotsCarrier` constraint; pin it here.
  -- Side-loaded slot's compile-time upper bound is N2 ⇒ `PerProofWitness 2 …`.
  let
    dummyAdvice
      :: StepAdvice _ _ _ _ _ _
           ( Tuple
               ( PerProofWitness 1 StepIPARounds WrapIPARounds (F StepField)
                   (Type2 (SplitField (F StepField) Boolean))
                   Boolean
               )
               Unit
           )
           _
           _
    dummyAdvice = unsafeCoerce unit
  mkStepArtifact <$> do
    compile noAdvice (Proxy @Unit) (Proxy @(Vector 34 (F StepField)))
      (Proxy @(KimchiConstraint StepField))
      -- Parent N=1, pi=34 (1 input + 33 output = 1*32 unfp + 1 digest
      -- + 1 msgs_wrap). The spec sizes the slot at the side-loaded
      -- tag's compile-time upper bound (`N2`). vkCarrier =
      -- `VerificationKey /\ Unit` (from `SideloadedVKsCarrier`).
      ( \_ -> stepMain
          @SideLoadedMainPrevsSpec
          @(F StepField)
          @Unit
          @(Tuple1 (SideLoadedPrevValue (StatementIO (F StepField) Unit)))
          @1
          @1
          sideLoadedMainRule
          -- This circuit-diff harness builds `perSlotLagrangeAt` /
          -- `perSlotVkBlueprints` / `perSlotFopDomainLog2s` inline rather
          -- than going through `Pickles.Prove.Compile.shapeCompileData`.
          -- The side-loaded slot ignores `perSlotLagrangeAt` (Step.Main
          -- reads the per-domain tables from `SlotVkBlueprintSideLoaded` instead);
          -- it's still required to satisfy the Vector shape.
          { blindingH: params.blindingH
          -- Side-loaded slots ignore this Vector —
          -- `Step.FinalizeOtherProof`'s `SideLoadedMode` synthesises
          -- the `Vector 17 [0..16]` universe from
          -- `branch_data.domain_log2`. The `Vector 1 [0]` placeholder
          -- here matches `nd = 1` for a single-rule side-loaded
          -- compile.
          , perSlotFopDomainLog2s:
              (0 :< Vector.nil) :< Vector.nil
          , perSlotFopZkRows: zkRowsByDefault :< Vector.nil
          , perSlotVkBlueprints:
              BlueprintSideLoaded params.sideloadedPerDomainLagrangeAt /\ unit
          }
          dummyWrapSg
          dummyAdvice
          throwawayCaptureRef
      )
