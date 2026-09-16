-- | Per-slot wrap-VK source / blueprint types.
-- |
-- | Extracted from `Pickles.Step.Main` so that `Pickles.Step.Slots`
-- | (which defines the spec-indexed carrier traversal that walks
-- | these alongside `PerProofWitness`) can import them without
-- | creating a module cycle through `Step.Main`.
-- |
-- | Each cell is parameterized by `nc` — the chunks count of that
-- | particular slot's wrap VK (the slot's own `nc` from
-- | `Slot n nc statement`). Heterogeneous per-slot chunks: each
-- | slot's wrap VK carries the chunks count of *its* producing
-- | compile, not a shared homogenized value.
module Pickles.Step.VkSource
  ( SlotVkBlueprint(..)
  , SlotVkBlueprintSideLoaded
  , SlotVkSource(..)
  ) where

import Data.Vector (Vector)
import Pickles.Field (StepField)
import Pickles.ProofsVerified (ProofsVerifiedCount)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Sideload.VerificationKey as SLVK
import Pickles.VerificationKey (VerificationKey)
import Snarky.Circuit.DSL (BoolVar, F, FVar)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint)

-- | Compile-time blueprint for one slot's wrap-VK source: where the
-- | step circuit gets the verification key it verifies this slot's
-- | previous proof against.
-- |
-- | One constructor per `Pickles.Prove.Slot.SlotSource`, named to match
-- | it. A self slot reads the shared key from advice (the wrap circuit
-- | does not exist yet at step-compile time), an external slot has its
-- | source's key baked in as a constant, and a side-loaded slot carries
-- | the per-domain lagrange tables that `Pickles.Step.Main` one-hot
-- | muxes over against the runtime key's `actualWrapDomainSize`.
-- |
-- | `nc` is the chunks count of the producing compile's wrap VK.
-- | The compiled cases carry the slot's lagrange basis, at *this
-- | slot's* chunk count: the basis is read at the slot source's wrap
-- | domain, so it belongs to the slot, not to the enclosing compile.
-- | The side-loaded case has no compile-time domain to read one at —
-- | it carries the three per-domain tables instead and muxes among
-- | them in-circuit.
data SlotVkBlueprint :: Int -> Type
data SlotVkBlueprint slotVkChunks
  = BlueprintSelf (LagrangeBaseLookup slotVkChunks StepField)
  | BlueprintExternal
      (LagrangeBaseLookup slotVkChunks StepField)
      (VerificationKey slotVkChunks (WeierstrassAffinePoint PallasG (F StepField)))
  | BlueprintSideLoaded (SlotVkBlueprintSideLoaded slotVkChunks)

-- | The side-loaded case's payload — the
-- | per-domain × per-chunk lagrange tables. Each domain entry returns
-- | a `Vector nc (AffinePoint _)` (the SRS lagrange commitment split
-- | over `nc` chunks), and `Step.Main` muxes 1-hot over domains
-- | per-chunk to produce the chunked `LagrangeBaseLookup nc _`.
-- |
-- | Mirrors OCaml's `wrap_verifier.ml:334-356` pattern where each
-- | domain contributes a full chunks-array.
-- |
-- | The runtime VK is allocated in-circuit by `BuildSlotVkSources`
-- | and bundled alongside this into `SlotVkSource.SideloadedExistsVk`.
type SlotVkBlueprintSideLoaded :: Int -> Type
type SlotVkBlueprintSideLoaded slotVkChunks =
  Vector ProofsVerifiedCount (Int -> Vector slotVkChunks (AffinePoint (F StepField)))

-- | Post-walk per-slot wrap-VK dispatch type. `SideloadedExistsVk`
-- | bundles BOTH the compile-time per-domain lagrange tables and the
-- | in-circuit-allocated side-loaded VK descriptor so the Step.Main
-- | dispatch loop has everything in one place — no parallel
-- | `Vector len (Maybe …)` lookup required.
-- |
-- | `nc` is the slot's own wrap-VK chunks count (heterogeneous —
-- | each slot in a rule's spec can carry its own chunks count).
data SlotVkSource :: Int -> Type
data SlotVkSource slotVkChunks
  = ConstVk
      (LagrangeBaseLookup slotVkChunks StepField)
      (VerificationKey slotVkChunks (WeierstrassAffinePoint PallasG (F StepField)))
  | SharedExistsVk (LagrangeBaseLookup slotVkChunks StepField)
  | SideloadedExistsVk
      (SlotVkBlueprintSideLoaded slotVkChunks)
      (SLVK.VerificationKey slotVkChunks (FVar StepField) (BoolVar StepField))
