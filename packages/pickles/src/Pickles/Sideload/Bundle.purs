-- | A child's wrap VK in its two prove-time views: `vk`, the
-- | circuit-representable descriptor the parent's step circuit walks,
-- | and `verifierIndex`, the kimchi runtime handle, which has no
-- | circuit representation and is read only by the prover machinery
-- | that computes oracles or verifies the child's wrap proof.
-- |
-- | The constructor is hidden. `mkBundle` derives `vk`'s commitments
-- | from `verifierIndex`, so the two halves cannot disagree.
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

-- | `slotVkChunks` is the chunk count of the child's compile, so the
-- | descriptor half is shaped by it.
newtype Bundle :: Int -> Type
newtype Bundle slotVkChunks = Bundle
  { vk :: SLVK.VerificationKey slotVkChunks (F StepField) Boolean
  , verifierIndex :: VerifierIndex Pallas.G WrapField
  }

-- | The side-loaded VK descriptor inside a carrier cell, whichever
-- | phase the cell comes from: a compile-time cell is the descriptor
-- | already, a `Bundle` yields its `vk` half.
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
-- | `Maybe (Bundle slotVkChunks)` with the two cases named after what
-- | they assert, because at a call site a bare `Nothing` says nothing
-- | about why the slot is empty.
data SlotProveVk :: Int -> Type
data SlotProveVk slotVkChunks
  = NoSideLoadedVk
  | SideLoadedVk (Bundle slotVkChunks)

instance HasSideLoadedVk slotVkChunks (SlotProveVk slotVkChunks) where
  projectVk = projectVk <<< requireBundle

-- | The bundle of a slot that must have one.
-- |
-- | Every caller is on a path taken because the slot's key is
-- | `SideLoadedKey`, or its blueprint `BlueprintSideLoaded`, so
-- | `NoSideLoadedVk` here means a side-loaded slot was declared with
-- | nothing supplied for it in `sideloadedVKs`. It throws rather than
-- | substituting a dummy: the slot's whole job is to verify against
-- | the key that is missing.
requireBundle :: forall slotVkChunks. SlotProveVk slotVkChunks -> Bundle slotVkChunks
requireBundle = case _ of
  SideLoadedVk b -> b
  NoSideLoadedVk -> unsafeThrow
    "requireBundle: a side-loaded slot was declared with no runtime \
    \verification key in this rule's `sideloadedVKs`"

-- | A `Bundle` from a kimchi `VerifierIndex` and the two
-- | `ProofsVerified` tags.
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

verifierIndex :: forall slotVkChunks. Bundle slotVkChunks -> VerifierIndex Pallas.G WrapField
verifierIndex (Bundle r) = r.verifierIndex
