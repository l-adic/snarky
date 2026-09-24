-- | Where the step circuit gets the wrap verification key for each of
-- | its previous-proof slots: the compile-time blueprint, and the
-- | value `Pickles.Step.Main` dispatches on.
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

-- | Compile-time blueprint for one slot's wrap-VK source.
-- |
-- | One constructor per slot source: `Self`, `External`, or a
-- | side-loaded slot. A self slot reads the shared key from advice, because the
-- | wrap circuit does not exist yet at step-compile time; an external
-- | slot has its source's key baked in as a constant; a side-loaded
-- | slot carries the per-domain lagrange tables that
-- | `Pickles.Step.Main` one-hot muxes over against the runtime key's
-- | `actualWrapDomainSize`.
-- |
-- | `slotVkChunks` is the chunk count of the producing compile's wrap
-- | VK. The compiled cases carry their lagrange basis at that count,
-- | since the basis is read at the slot source's own wrap domain; the
-- | side-loaded case has no compile-time domain to read one at.
data SlotVkBlueprint :: Int -> Type
data SlotVkBlueprint slotVkChunks
  = BlueprintSelf (LagrangeBaseLookup slotVkChunks StepField)
  | BlueprintExternal
      (LagrangeBaseLookup slotVkChunks StepField)
      (VerificationKey slotVkChunks (WeierstrassAffinePoint PallasG (F StepField)))
  | BlueprintSideLoaded (SlotVkBlueprintSideLoaded slotVkChunks)

-- | The side-loaded case's payload: one lagrange table per candidate
-- | wrap domain, each returning that domain's SRS lagrange commitment
-- | split over `slotVkChunks` chunks. `Pickles.Step.Main` muxes 1-hot
-- | over domains, per chunk, to get a `LagrangeBaseLookup`.
type SlotVkBlueprintSideLoaded :: Int -> Type
type SlotVkBlueprintSideLoaded slotVkChunks =
  Vector ProofsVerifiedCount (Int -> Vector slotVkChunks (AffinePoint (F StepField)))

-- | One slot's wrap VK as `Pickles.Step.Main` dispatches on it, built
-- | from that slot's `SlotVkBlueprint` by `buildSlotVkSources`.
-- | `SideloadedExistsVk` carries the compile-time per-domain lagrange
-- | tables and the in-circuit-allocated VK descriptor together, so the
-- | dispatch loop needs no parallel lookup.
data SlotVkSource :: Int -> Type
data SlotVkSource slotVkChunks
  = ConstVk
      (LagrangeBaseLookup slotVkChunks StepField)
      (VerificationKey slotVkChunks (WeierstrassAffinePoint PallasG (F StepField)))
  | SharedExistsVk (LagrangeBaseLookup slotVkChunks StepField)
  | SideloadedExistsVk
      (SlotVkBlueprintSideLoaded slotVkChunks)
      (SLVK.VerificationKey slotVkChunks (FVar StepField) (BoolVar StepField))
