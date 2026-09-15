-- | Prove-time pairing of a child's wrap VK in its two views.
-- |
-- | * `vk` — the circuit-representable side-loaded VK shape that the
-- |   parent's step circuit walks (feeds `exists` for in-circuit
-- |   allocation).
-- |
-- | * `verifierIndex` — the kimchi runtime handle. No circuit
-- |   representation; used only by prover machinery that computes
-- |   oracles or runs kimchi verify against the child's wrap proof.
-- |
-- | Constructor is hidden; construct via `mkBundle`. The smart
-- | constructor derives `vk`'s commitments from `verifierIndex` so the
-- | two halves are guaranteed consistent.
module Pickles.Sideload.Bundle
  ( Bundle
  , SlotProveVk(..)
  , class HasSideLoadedVk
  , projectVk
  , mkBundle
  , requireBundle
  , verifierIndex
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Effect.Exception.Unsafe (unsafeThrow)
import Pickles.Field (StepField, WrapField)
import Pickles.ProofsVerified (ProofsVerified)
import Pickles.Sideload.VerificationKey (mkVerificationKey)
import Pickles.Sideload.VerificationKey as SLVK
import Pickles.VerificationKey (extractWrapVKComms)
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Circuit.DSL (F)
import Snarky.Curves.Pallas as Pallas

-- | Prove-time bundle: side-loaded VK descriptor + kimchi runtime
-- | handle. See module doc for the role of each half. Polymorphic on
-- | `nc` so the bundle's circuit-side VK shape tracks the
-- | child's compile-time chunk count.
newtype Bundle :: Int -> Type
newtype Bundle slotVkChunks = Bundle
  { vk :: SLVK.VerificationKey slotVkChunks (F StepField) Boolean
  , verifierIndex :: VerifierIndex Pallas.G WrapField
  }

-- | Uniformly project the side-loaded VK descriptor out of a carrier
-- | cell regardless of phase: compile-time cells (the VK descriptor
-- | itself) project as identity; prove-time cells (`Bundle`) project
-- | to the `.vk` field. `nc` is the chunk count of the
-- | wrapped child's VK.
class HasSideLoadedVk slotVkChunks cell | cell -> slotVkChunks where
  projectVk :: cell -> SLVK.VerificationKey slotVkChunks (F StepField) Boolean

instance HasSideLoadedVk slotVkChunks (SLVK.VerificationKey slotVkChunks (F StepField) Boolean) where
  projectVk = identity

instance HasSideLoadedVk slotVkChunks (Bundle slotVkChunks) where
  projectVk (Bundle r) = r.vk

-- | What one prove call supplies for one slot's wrap verification key.
-- |
-- | The constructors pair with `Pickles.Prove.Compile.SlotWrapKey`,
-- | which is where the slot's source is actually decided:
-- |
-- | * `Self` / `External` ⇒ `NoSideLoadedVk` — the key is baked into
-- |   the step circuit at compile time, so a prove call has nothing to
-- |   add.
-- | * `SideLoadedKey` ⇒ `SideLoadedVk bundle` — the key is this
-- |   witness, allocated in-circuit by `buildSlotVkSources`.
-- |
-- | This is `Maybe (Bundle nc)` with the two cases named after what
-- | they assert, because at a call site the bare `Nothing` of a
-- | compiled slot says nothing about why it is empty.
data SlotProveVk :: Int -> Type
data SlotProveVk slotVkChunks
  = NoSideLoadedVk
  | SideLoadedVk (Bundle slotVkChunks)

instance HasSideLoadedVk slotVkChunks (SlotProveVk slotVkChunks) where
  projectVk = projectVk <<< requireBundle

-- | The bundle of a slot that must have one.
-- |
-- | Every caller of this is on a path already taken because the slot's
-- | key is `SideLoadedKey` (or its blueprint `BlueprintSideLoaded`), so
-- | `NoSideLoadedVk` means the caller declared a side-loaded slot and
-- | then supplied no runtime verification key for it in
-- | `sideloadedVKs`. There is no sound default for that, hence the
-- | throw rather than a dummy: the slot's whole job is to verify
-- | against the key that is missing.
requireBundle :: forall slotVkChunks. SlotProveVk slotVkChunks -> Bundle slotVkChunks
requireBundle = case _ of
  SideLoadedVk b -> b
  NoSideLoadedVk -> unsafeThrow
    "requireBundle: a side-loaded slot was declared with no runtime \
    \verification key in this rule's `sideloadedVKs`"

-- | Build a `Bundle` from a kimchi `VerifierIndex` and the user-side
-- | `ProofsVerified` tags. Derives `vk`'s commitments from the
-- | `verifierIndex` so the bundle's two halves are always consistent.
mkBundle
  :: forall @slotVkChunks
   . Reflectable slotVkChunks Int
  => { verifierIndex :: VerifierIndex Pallas.G WrapField
     , maxProofsVerified :: ProofsVerified
     , actualWrapDomainSize :: ProofsVerified
     }
  -> Bundle slotVkChunks
mkBundle r = Bundle
  { vk: mkVerificationKey
      { maxProofsVerified: r.maxProofsVerified
      , actualWrapDomainSize: r.actualWrapDomainSize
      , wrapIndex: extractWrapVKComms @slotVkChunks r.verifierIndex
      }
  , verifierIndex: r.verifierIndex
  }

-- | Access the kimchi runtime handle.
verifierIndex :: forall slotVkChunks. Bundle slotVkChunks -> VerifierIndex Pallas.G WrapField
verifierIndex (Bundle r) = r.verifierIndex
