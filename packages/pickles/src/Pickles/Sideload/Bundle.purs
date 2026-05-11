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
  , class HasSideLoadedVk
  , projectVk
  , mkBundle
  , verifierIndex
  ) where

import Prelude

import Pickles.ProofsVerified (ProofsVerified)
import Pickles.Sideload.VerificationKey (mkVerificationKey)
import Pickles.Sideload.VerificationKey as SLVK
import Pickles.Step.Types as Step
import Pickles.VerificationKey (extractWrapVKComms)
import Pickles.Wrap.Types as Wrap
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Circuit.DSL (F)
import Snarky.Curves.Pallas as Pallas

-- | Prove-time bundle: side-loaded VK descriptor + kimchi runtime
-- | handle. See module doc for the role of each half.
newtype Bundle = Bundle
  { vk :: SLVK.VerificationKey (F Step.Field) Boolean
  , verifierIndex :: VerifierIndex Pallas.G Wrap.Field
  }

-- | Uniformly project the side-loaded VK descriptor out of a carrier
-- | cell regardless of phase: compile-time cells (the VK descriptor
-- | itself) project as identity; prove-time cells (`Bundle`) project
-- | to the `.vk` field.
class HasSideLoadedVk cell where
  projectVk :: cell -> SLVK.VerificationKey (F Step.Field) Boolean

instance HasSideLoadedVk (SLVK.VerificationKey (F Step.Field) Boolean) where
  projectVk = identity

instance HasSideLoadedVk Bundle where
  projectVk (Bundle r) = r.vk

-- | Build a `Bundle` from a kimchi `VerifierIndex` and the user-side
-- | `ProofsVerified` tags. Derives `vk`'s commitments from the
-- | `verifierIndex` so the bundle's two halves are always consistent.
mkBundle
  :: { verifierIndex :: VerifierIndex Pallas.G Wrap.Field
     , maxProofsVerified :: ProofsVerified
     , actualWrapDomainSize :: ProofsVerified
     }
  -> Bundle
mkBundle r = Bundle
  { vk: mkVerificationKey
      { maxProofsVerified: r.maxProofsVerified
      , actualWrapDomainSize: r.actualWrapDomainSize
      , wrapIndex: extractWrapVKComms r.verifierIndex
      }
  , verifierIndex: r.verifierIndex
  }

-- | Access the kimchi runtime handle.
verifierIndex :: Bundle -> VerifierIndex Pallas.G Wrap.Field
verifierIndex (Bundle r) = r.verifierIndex
