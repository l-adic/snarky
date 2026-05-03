module Pickles.CircuitDiffs.PureScript.StepMainSideLoadedMain
  ( compileStepMainSideLoadedMain
  , StepMainSideLoadedMainParams
  , class SideLoadedMainAdvice
  , getSideLoadedMainPrev
  ) where

-- | step_main circuit for the side-loaded variant of Simple_chain
-- | (parent rule: mpv=N1, single side-loaded prev with mpv=N2).
-- |
-- | Reference: mina/src/lib/crypto/pickles/dump_circuit_impl.ml
-- |   (`step_main_side_loaded_main`, mirroring
-- |   dump_side_loaded_main.ml's `Simple_chain` rule).
-- |
-- | OCaml fixture:
-- |   `step_main_side_loaded_main_circuit.json` — 11862 gates, pi=34.
-- |
-- | The rule body is structurally identical to
-- | `StepMainSimpleChain.simpleChainRule`; the only difference is the
-- | spec's prev tag — `PrevsSpecSideLoadedCons` instead of
-- | `PrevsSpecCons` — which routes the slot's wrap-VK / step-domain
-- | / max-proofs-verified through the runtime side-loaded VK
-- | (β2/β3/β4 paths in `Pickles.Step.Main`'s slot dispatch).

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import Partial.Unsafe (unsafeCrashWith)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyWrapSg)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Sideload.VerificationKey as Sideload
import Pickles.Step.Main (RuleOutput, SlotVkSource(..), stepMain)
import Pickles.Step.Prevs (PrevsSpecNil, PrevsSpecSideLoadedCons)
import Pickles.Types (StatementIO, StepField)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, assertAny_, const_, equals_, exists, not_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | Parameters for the side-loaded main fixture.
-- |
-- |   * `lagrangeAt` — placeholder per-slot table (`Step.Main` ignores
-- |     it on the side-loaded path; only consumed for compiled
-- |     slots, of which the side-loaded fixture has none).
-- |   * `sideloadedPerDomainLagrangeAt` — three SRS lagrange lookups
-- |     at log2 ∈ {13, 14, 15} (= wrap-domain log2s for `actual_wrap_domain_size
-- |     ∈ {N0, N1, N2}` per `common.ml:25-29`). `Step.Main` muxes
-- |     among these via the runtime one-hot bits — exactly what
-- |     `Pickles.Prove.Compile.shapeCompileData` would emit for
-- |     `PrevsSpecSideLoadedCons`.
type StepMainSideLoadedMainParams =
  { lagrangeAt :: LagrangeBaseLookup StepField
  , sideloadedPerDomainLagrangeAt ::
      Vector 3 (Int -> AffinePoint (F StepField))
  , blindingH :: AffinePoint (F StepField)
  }

-- | Application-specific advice for the side-loaded main rule.
-- |
-- | Identical shape to `StepMainSimpleChain.SimpleChainAdvice`: one
-- | previous-proof public-input field. The side-loaded distinction
-- | shows up only in the spec / vkCarrier, not in the rule body.
class Monad m <= SideLoadedMainAdvice m where
  getSideLoadedMainPrev :: Unit -> m (F StepField)

-- | Compilation instance: throws if evaluated. `exists` in
-- | CircuitBuilderT discards the AsProverT entirely so the throw
-- | never fires.
instance SideLoadedMainAdvice Effect where
  getSideLoadedMainPrev _ =
    throw "SideLoadedMainAdvice.getSideLoadedMainPrev: not available during compilation"

-- | Side-loaded main rule body. Mirrors
-- | `StepMainSimpleChain.simpleChainRule` exactly:
-- |   self_correct = (1 + prev == self) || is_base_case.
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
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) appState
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev :< Vector.nil
    , proofMustVerify: proofMustVerify :< Vector.nil
    , publicOutput: unit
    }

compileStepMainSideLoadedMain
  :: StepMainSideLoadedMainParams -> Effect (CompiledCircuit StepField)
compileStepMainSideLoadedMain params =
  compile (Proxy @Unit) (Proxy @(Vector 34 (F StepField)))
    (Proxy @(KimchiConstraint StepField))
    -- Parent N=1, public input/output sizes match SimpleChain N1
    -- (pi=34: 1 input field + 33 output = 1*18 unfp + 13 digest + 2
    -- msgs_wrap). Spec encodes the slot's mpv at the side-loaded
    -- tag's compile-time upper bound (= N2 from
    -- `Side_loaded.create ~max_proofs_verified:N2` in
    -- dump_side_loaded_main.ml:120). vkCarrier = `VerificationKey /\
    -- Unit` per the `SideloadedVKsCarrier
    -- (PrevsSpecSideLoadedCons …) (VerificationKey /\ rest)`
    -- instance in `Pickles.Sideload.Advice`.
    --
    -- `shapeCompileData` for `PrevsSpecSideLoadedCons` (in
    -- Pickles.Prove.Compile) emits `SideloadedExistsVk` with three
    -- per-domain lagrange tables (Step 2d-β2). Step.Main's per-slot
    -- dispatch then reads the slot's `actualWrapDomainSize` one-hot
    -- and muxes among them.
    ( \_ -> stepMain
        @( PrevsSpecSideLoadedCons 2 (StatementIO (F StepField) Unit)
            PrevsSpecNil
        )
        @34
        @(F StepField)
        @(FVar StepField)
        @Unit
        @Unit
        @(F StepField)
        @(FVar StepField)
        @(Tuple (StatementIO (F StepField) Unit) Unit)
        @1
        @0
        sideLoadedMainRule
        -- The compile-time SRS data lookup is unused for the
        -- side-loaded slot's lagrange (Step.Main reads from
        -- `SideloadedExistsVk`'s carried per-domain tables instead).
        -- We still need to populate `perSlotLagrangeAt` with
        -- something Vector-shaped. The `lagrangeAt` param flows
        -- through; the side-loaded slot ignores it.
        --
        -- NOTE: this `perSlotLagrangeAt` / `perSlotVkSources` /
        -- `perSlotFopDomainLog2s` triple is what
        -- `Pickles.Prove.Compile.shapeCompileData` populates for
        -- regular compilation. For the CircuitDiffs harness we
        -- bypass `compileMulti` and call `stepMain` directly with
        -- inlined SRS data — that's why the `SideloadedExistsVk`
        -- variant is constructed here at the test site rather than
        -- coming from `shapeCompileData`. The carrier with three
        -- per-domain lagrange tables is the same `vestaSrsLagrange`
        -- closure family
        -- `Pickles.Prove.Compile.shapeCompileData` would emit at
        -- log2 ∈ {13, 14, 15}; we pass `params.lagrangeAt`
        -- (single-domain) for all three because the test fixture
        -- doesn't exercise the runtime mux yet.
        { perSlotLagrangeAt: params.lagrangeAt :< Vector.nil
        , blindingH: params.blindingH
        , perSlotFopDomainLog2s: (14 :< Vector.nil) :< Vector.nil
        , perSlotVkSources:
            SideloadedExistsVk params.sideloadedPerDomainLagrangeAt
              :< Vector.nil
        , dummyUnfp: \_ -> unsafeCrashWith "dummyUnfp: unused at mpvPad=0"
        }
        dummyWrapSg
        -- Side-loaded VK carrier: one slot with the dummy VK,
        -- mirroring OCaml's `exists Side_loaded_verification_key.typ
        -- ~compute:(... .dummy)` allocation.
        (Sideload.dummy /\ unit)
    )
    Kimchi.initialState
