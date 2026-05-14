-- | Per-slot wrap-VK source / blueprint types.
-- |
-- | Extracted from `Pickles.Step.Main` so that `Pickles.Step.Slots`
-- | (which defines the spec-indexed carrier traversal that walks
-- | these alongside `PerProofWitness`) can import them without
-- | creating a module cycle through `Step.Main`.
-- |
-- | Each cell is parameterized by `nc` — the chunks count of that
-- | particular slot's wrap VK (the slot's own `nc` from
-- | `Slot k n nc statement`). Heterogeneous per-slot chunks: each
-- | slot's wrap VK carries the chunks count of *its* producing
-- | compile, not a shared homogenized value.
module Pickles.Step.VkSource
  ( SlotVkBlueprintCompiled(..)
  , SlotVkBlueprintSideLoaded
  , SlotVkSource(..)
  ) where

import Pickles.Field (StepField)
import Pickles.ProofsVerified (ProofsVerifiedCount)
import Pickles.Sideload.VerificationKey as SLVK
import Pickles.VerificationKey (VerificationKey)
import Snarky.Circuit.DSL (BoolVar, F, FVar)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint)
import Data.Vector (Vector)

-- | Compile-time blueprint for a `Slot Compiled` slot. Two inhabitants
-- | only — `BuildSlotVkSources`'s Compiled instance pattern-matches
-- | exhaustively without an "impossible" fallthrough.
-- |
-- | `nc` is the chunks count of the producing compile's wrap VK.
data SlotVkBlueprintCompiled :: Int -> Type
data SlotVkBlueprintCompiled nc
  = VkBlueprintConst (VerificationKey nc (WeierstrassAffinePoint PallasG (F StepField)))
  | VkBlueprintShared

-- | Compile-time blueprint for a `Slot SideLoaded` slot — the
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
type SlotVkBlueprintSideLoaded nc =
  Vector ProofsVerifiedCount (Int -> Vector nc (AffinePoint (F StepField)))

-- | Post-walk per-slot wrap-VK dispatch type. `SideloadedExistsVk`
-- | bundles BOTH the compile-time per-domain lagrange tables and the
-- | in-circuit-allocated side-loaded VK descriptor so the Step.Main
-- | dispatch loop has everything in one place — no parallel
-- | `Vector len (Maybe …)` lookup required.
-- |
-- | `nc` is the slot's own wrap-VK chunks count (heterogeneous —
-- | each slot in a rule's spec can carry its own chunks count).
data SlotVkSource :: Int -> Type
data SlotVkSource nc
  = ConstVk (VerificationKey nc (WeierstrassAffinePoint PallasG (F StepField)))
  | SharedExistsVk
  | SideloadedExistsVk
      (SlotVkBlueprintSideLoaded nc)
      (SLVK.VerificationKey nc (FVar StepField) (BoolVar StepField))
