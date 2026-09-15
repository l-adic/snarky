-- | The runtime compiler's per-slot data, computed by folding over an
-- | `Array Slot` instead of dispatching through one type-class instance
-- | per slot shape.
-- |
-- | This is the first of the three functions of
-- | `docs/pickles-rule-dsl-simplification-plan.md` §3.2: the value-level
-- | replacement for `CompilableSpec`'s `shapeCompileData`. It produces
-- | exactly what that method's `srsData` record carried, one entry per
-- | slot, in slot order.
-- |
-- | The chunk counts stay type-level, as the plan says: `nc` here is the
-- | compile-wide wrap-VK chunk count, a protocol constant. What became
-- | runtime is the slot list itself.
module Pickles.Prove.SlotCompile
  ( SlotCompileConfig
  , SlotCompileEntry
  , slotCompileData
  , slotCompileEntry
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Newtype (over)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Exception.Unsafe (unsafeThrow)
import Pickles.Constants (zkRowsForNumChunks)
import Pickles.Field (StepField, WrapField)
import Pickles.Prove.Slot (Slot, SlotSource(..), slotNumChunks, slotSourceDomainLog2s, slotWrapDomainLog2)
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Step.VkSource (SlotVkBlueprint(..))
import Pickles.VerificationKey (VerificationKey(..), vestaVerifierIndexCommitments)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Commitment (ChunkedCommitment(..))
import Snarky.Backend.Kimchi.Proof (srsLagrangeCommitmentChunksAt) as ProofFFI
import Snarky.Backend.Kimchi.Types (CRS, VerifierIndex)
import Snarky.Circuit.DSL (F(..))
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..), WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))

-- | What one slot contributes to the step prover's `srsData`.
-- |
-- | Everything here is at `slotNc`, the chunk count of the compile that
-- | produced *this* slot's previous proofs — including the lagrange
-- | basis, which is read at the slot source's own wrap domain. The
-- | enclosing compile's wrap-VK chunk count is a different axis (the
-- | Phase 0 inventory's OQ-8) and does not appear here at all.
type SlotCompileEntry :: Int -> Type
type SlotCompileEntry slotNc =
  { fopDomainLog2s :: Array Int
  , fopZkRows :: Int
  , vkBlueprint :: SlotVkBlueprint slotNc
  }

-- | The compile-wide inputs the per-slot fold needs. This is the subset
-- | of `CompileConfig` that `shapeCompileData` actually read, with the
-- | wrap-domain override already resolved.
type SlotCompileConfig =
  { pallasSrs :: CRS PallasG
  -- | The enclosing compile's declared `num_chunks`; `Self` slots read
  -- | their previous step proof's `zk_rows` from it.
  , stepNumChunks :: Int
  -- | The enclosing rule's wrap domain log2, already resolved against
  -- | `wrapDomainOverride`. `Self` slots use it directly.
  , outerWrapDomainLog2 :: Int
  -- | The number of branches the enclosing compile has, which is the
  -- | width of every slot's `fopDomainLog2s`.
  , branchCount :: Int
  }

-- | The per-slot lagrange basis of a wrap VK at one domain, chunked at
-- | the compile-wide `nc`. At `nc = 1` the chunks array has length one
-- | and this is byte-identical to the single-chunk path.
lagrangeAtDomain
  :: forall @nc
   . Reflectable nc Int
  => CRS PallasG
  -> Int
  -> (Int -> Vector nc (AffinePoint (F StepField)))
lagrangeAtDomain pallasSrs domainLog2 = \i ->
  let
    chunksArr = ProofFFI.srsLagrangeCommitmentChunksAt pallasSrs domainLog2 i
  in
    case Vector.toVector @nc (map coerce chunksArr) of
      Just v -> v
      Nothing -> unsafeThrow
        $ "lagrangeAtDomain: the SRS returned "
            <> show (Array.length chunksArr)
            <> " lagrange chunks at domainLog2="
            <> show domainLog2
            <> ", but this basis is declared at "
            <> show (reflectType (Proxy @nc))

-- | An external source's wrap verification key, in the commitment
-- | shape the step advice uses. Same body as
-- | `Pickles.Prove.Step.extractWrapVKCommsAdvice`, repeated here so
-- | this module does not import the step prover.
externalWrapVk
  :: forall @nc
   . Reflectable nc Int
  => VerifierIndex PallasG WrapField
  -> VerificationKey nc (WeierstrassAffinePoint PallasG (F StepField))
externalWrapVk vk = VerificationKey
  { sigma: map chunked comms.sigma
  , coeff: map chunked comms.coeff
  , index: map chunked comms.index
  }
  where
  comms = vestaVerifierIndexCommitments @nc vk

  wrapPt :: AffinePoint StepField -> WeierstrassAffinePoint PallasG (F StepField)
  wrapPt (AffinePoint pt) = WeierstrassAffinePoint { x: F pt.x, y: F pt.y }

  chunked = over ChunkedCommitment (map wrapPt)

-- | One slot's contribution. The `selfStepDomainLog2s` argument is the
-- | enclosing compile's own per-branch step domains, which only exist
-- | after the pre-pass; `Self` slots take it verbatim.
slotCompileEntry
  :: forall @slotNc
   . Reflectable slotNc Int
  => SlotCompileConfig
  -> Array Int
  -> Slot
  -> SlotCompileEntry slotNc
slotCompileEntry cfg selfStepDomainLog2s slot =
  { fopDomainLog2s: slotSourceDomainLog2s cfg.branchCount selfStepDomainLog2s slot
  , fopZkRows: zkRowsForNumChunks (slotNumChunks cfg.stepNumChunks slot)
  , vkBlueprint: blueprint
  }
  where
  outer = cfg.outerWrapDomainLog2

  -- This slot's lagrange basis, at its own wrap domain and its own
  -- chunk count. Both belong to the slot: the domain is the source's,
  -- and a chunked source has a chunked basis.
  lagrangeAt :: Int -> Int -> Vector slotNc (AffinePoint (F StepField))
  lagrangeAt = lagrangeAtDomain cfg.pallasSrs

  slotLagrange = mkConstLagrangeBaseLookup (lagrangeAt (slotWrapDomainLog2 outer slot))

  blueprint = case slot.source of
    SelfSource -> BlueprintSelf slotLagrange
    ExternalSource d ->
      BlueprintExternal slotLagrange (externalWrapVk @slotNc d.wrapVerifierIndex)
    -- A side-loaded slot's wrap domain is not known until prove time,
    -- so it carries all three bases and muxes in-circuit instead.
    SideLoadedSource ->
      BlueprintSideLoaded (map lagrangeAt (13 :< 14 :< 15 :< Vector.nil))

-- | The whole slot list, in order. `CompilableRulesSpec`'s recursion
-- | becomes this `map`.
slotCompileData
  :: forall @slotNc
   . Reflectable slotNc Int
  => SlotCompileConfig
  -> Array Int
  -> Array Slot
  -> Array (SlotCompileEntry slotNc)
slotCompileData cfg selfStepDomainLog2s =
  map (slotCompileEntry @slotNc cfg selfStepDomainLog2s)
