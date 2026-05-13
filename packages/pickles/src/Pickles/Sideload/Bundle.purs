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

import Data.Reflectable (class Reflectable)
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
newtype Bundle nc = Bundle
  { vk :: SLVK.VerificationKey nc (F StepField) Boolean
  , verifierIndex :: VerifierIndex Pallas.G WrapField
  }

-- | Uniformly project the side-loaded VK descriptor out of a carrier
-- | cell regardless of phase: compile-time cells (the VK descriptor
-- | itself) project as identity; prove-time cells (`Bundle`) project
-- | to the `.vk` field. `nc` is the chunk count of the
-- | wrapped child's VK.
class HasSideLoadedVk nc cell | cell -> nc where
  projectVk :: cell -> SLVK.VerificationKey nc (F StepField) Boolean

instance HasSideLoadedVk nc (SLVK.VerificationKey nc (F StepField) Boolean) where
  projectVk = identity

instance HasSideLoadedVk nc (Bundle nc) where
  projectVk (Bundle r) = r.vk

-- | Build a `Bundle` from a kimchi `VerifierIndex` and the user-side
-- | `ProofsVerified` tags. Derives `vk`'s commitments from the
-- | `verifierIndex` so the bundle's two halves are always consistent.
mkBundle
  :: forall @nc
   . Reflectable nc Int
  => { verifierIndex :: VerifierIndex Pallas.G WrapField
     , maxProofsVerified :: ProofsVerified
     , actualWrapDomainSize :: ProofsVerified
     }
  -> Bundle nc
mkBundle r = Bundle
  { vk: mkVerificationKey
      { maxProofsVerified: r.maxProofsVerified
      , actualWrapDomainSize: r.actualWrapDomainSize
      , wrapIndex: extractWrapVKComms @nc r.verifierIndex
      }
  , verifierIndex: r.verifierIndex
  }

-- | Access the kimchi runtime handle.
verifierIndex :: forall nc. Bundle nc -> VerifierIndex Pallas.G WrapField
verifierIndex (Bundle r) = r.verifierIndex
