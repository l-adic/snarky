module Pickles.CircuitDiffs.PureScript.StepMainSideLoadedMain
  ( compileStepMainSideLoadedMain
  , StepMainSideLoadedMainParams
  , class SideLoadedMainAdvice
  , getSideLoadedMainPrev
  ) where

-- | step_main circuit for the side-loaded variant of Simple_chain
-- | (parent rule: mpv=N1, single side-loaded prev with mpv=N2).
-- |
-- | Reference: OCaml `dump_side_loaded_main.ml`. Fixture:
-- | `step_main_side_loaded_main_circuit.json` — 11862 gates, pi=34.
-- |
-- | Same rule body as `StepMainSimpleChain.simpleChainRule`; the only
-- | difference is the spec's prev tag (`Slot SideLoaded`
-- | instead of `Slot Compiled`), which routes the slot's wrap-VK,
-- | step-domain, and max-proofs-verified through the runtime
-- | side-loaded VK.

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Tuple.Nested (Tuple1, tuple1, (/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import Pickles.CircuitDiffs.PureScript.Common (StepArtifact, dummyWrapSg, mkStepArtifact)
import Pickles.Field (StepField)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Sideload.VerificationKey (VerificationKey, compileDummy) as SLVK
import Pickles.Slots (SideLoaded, Slot)
import Pickles.Step.Main (RuleOutput, stepMain)
import Pickles.Types (StatementIO)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, assertAny_, const_, equals_, exists, true_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

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

-- | Application-specific advice for the side-loaded main rule. Same
-- | shape as `StepMainSimpleChain.SimpleChainAdvice`: one
-- | previous-proof public-input field. The side-loaded distinction
-- | shows up in the spec / vkCarrier, not the rule body.
class Monad m <= SideLoadedMainAdvice m where
  getSideLoadedMainPrev :: Unit -> m (F StepField)

-- | Compilation instance: throws if evaluated. `exists` in
-- | `CircuitBuilderT` discards the `AsProverT` so the throw never
-- | fires.
instance SideLoadedMainAdvice Effect where
  getSideLoadedMainPrev _ =
    throw "SideLoadedMainAdvice.getSideLoadedMainPrev: not available during compilation"

-- | Side-loaded main rule body: same as `simpleChainRule` —
-- | `selfCorrect = (1 + prev == self) || isBaseCase`.
sideLoadedMainRule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => SideLoadedMainAdvice m
  => FVar StepField
  -> Snarky (KimchiConstraint StepField) t m
       (RuleOutput 1 (FVar StepField) Unit)
sideLoadedMainRule appState = do
  prev <- exists $ lift $ getSideLoadedMainPrev unit
  isBaseCase <- equals_ (const_ zero) appState
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) appState
  assertAny_ [ selfCorrect, isBaseCase ]
  -- `proofMustVerify = true_` (constant) is required for byte-parity:
  -- a non-constant Cvar makes downstream `if_ proofMustVerify ...`
  -- emit ~25 extra Generic gates that vanish under `true_` constant-
  -- folding. Reference: OCaml `dump_side_loaded_main.ml:179`.
  pure
    { prevPublicInputs: prev :< Vector.nil
    , proofMustVerify: true_ :< Vector.nil
    , publicOutput: unit
    }

compileStepMainSideLoadedMain
  :: StepMainSideLoadedMainParams -> Effect StepArtifact
compileStepMainSideLoadedMain params =
  mkStepArtifact <$>
    compile (Proxy @Unit) (Proxy @(Vector 34 (F StepField)))
      (Proxy @(KimchiConstraint StepField))
      -- Parent N=1, pi=34 (1 input + 33 output = 1*32 unfp + 1 digest
      -- + 1 msgs_wrap). The spec sizes the slot at the side-loaded
      -- tag's compile-time upper bound (`N2`). vkCarrier =
      -- `VerificationKey /\ Unit` (from `SideloadedVKsCarrier`).
      ( \_ -> stepMain
          @(Tuple1 (Slot SideLoaded 2 1 (StatementIO (F StepField) Unit)))
          @(F StepField)
          @Unit
          @(F StepField)
          @(Tuple1 (StatementIO (F StepField) Unit))
          @1
          @1
          @(SLVK.VerificationKey 1 (F StepField) Boolean)
          @1
          sideLoadedMainRule
          -- This circuit-diff harness builds `perSlotLagrangeAt` /
          -- `perSlotVkBlueprints` / `perSlotFopDomainLog2s` inline rather
          -- than going through `Pickles.Prove.Compile.shapeCompileData`.
          -- The side-loaded slot ignores `perSlotLagrangeAt` (Step.Main
          -- reads the per-domain tables from `SlotVkBlueprintSideLoaded` instead);
          -- it's still required to satisfy the Vector shape.
          { perSlotLagrangeAt: params.lagrangeAt :< Vector.nil
          , blindingH: params.blindingH
          -- Side-loaded slots ignore this Vector —
          -- `Step.FinalizeOtherProof`'s `SideLoadedMode` synthesises
          -- the `Vector 17 [0..16]` universe from
          -- `branch_data.domain_log2`. The `Vector 1 [0]` placeholder
          -- here matches `nd = 1` for a single-rule side-loaded
          -- compile.
          , perSlotFopDomainLog2s:
              (0 :< Vector.nil) :< Vector.nil
          , perSlotVkBlueprints:
              params.sideloadedPerDomainLagrangeAt /\ unit
          }
          dummyWrapSg
          -- Single side-loaded slot with the dummy VK.
          (tuple1 SLVK.compileDummy)
      )
      Kimchi.initialState
