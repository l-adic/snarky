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
  , class HasSideLoadedVk
  , projectVk
  , mkBundle
  , verifierIndex
  ) where

import Data.Reflectable (class Reflectable)
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

-- | The side-loaded VK descriptor inside a prove-time cell: a
-- | `Bundle`'s `vk` half.
class HasSideLoadedVk slotVkChunks cell | cell -> slotVkChunks where
  projectVk :: cell -> SLVK.VerificationKey slotVkChunks (F StepField) Boolean

instance HasSideLoadedVk slotVkChunks (Bundle slotVkChunks) where
  projectVk (Bundle r) = r.vk

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
