-- | Runtime slot data: what the compiler needs to know about a rule's
-- | previous-proof slots, carrying no type-level parameters, so a
-- | `Slot` is a plain `Type` and a rule's slot list an `Array Slot`.
-- |
-- | Lengths fixed by kimchi or pickles — `Vector 15` of columns,
-- | `Vector 32` of unfinalized fields, chunk counts — stay type-level;
-- | lengths that vary per application — slot count, `mpv`, branch
-- | count — live here.
module Pickles.Prove.Slot
  ( CompiledTagData
  , Slot
  , SlotSource(..)
  , slotNumChunks
  , slotSourceDomainLog2s
  , slotStepDomainLog2
  , slotWrapDomainLog2
  , slotWrapVerifierIndex
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Pickles.Field (WrapField)
import Pickles.Step.Dummy (wrapDomainLog2ForProofsVerified)
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Curves.Pasta (PallasG)

-- | The compile-time constants a previously-compiled tag contributes to
-- | a slot that verifies its proofs.
-- |
-- | A wrap verification key alone is not enough: the step circuit also
-- | bakes in the source's wrap domain (which fixes the per-slot
-- | lagrange basis), its per-branch step domains (which drive
-- | `perSlotFopDomainLog2s`), and its chunk count (which fixes
-- | `zk_rows`).
-- |
-- | The wrap verification key stays a raw `VerifierIndex` rather than
-- | an extracted `VerificationKey wrapVkChunks _` so that `Slot` keeps
-- | no type-level parameters; the extraction to commitments happens at
-- | the use site, where `wrapVkChunks` is pinned.
type CompiledTagData =
  { wrapVerifierIndex :: VerifierIndex PallasG WrapField
  -- | The imported system's wrap domain log2: 13 for 0 proofs
  -- | verified, 14 for 1, 15 for 2.
  , wrapDomainLog2 :: Int
  -- | The imported system's realized step-domain log2, one per branch
  -- | of that system, deduplicated. Non-empty because a system with no
  -- | branches has no step circuit and so no domain.
  , stepDomainLog2s :: NonEmptyArray Int
  -- | The imported system's compile-time `num_chunks`. `zk_rows`
  -- | follows from it.
  , numChunks :: Int
  }

-- | Where a slot's previous proofs come from: the rule currently being
-- | compiled, another already-compiled proof system, or a verification
-- | key supplied at prove time.
-- |
-- | `SelfSource` and `ExternalSource` are both compiled sources; what
-- | separates them is which verification key the step circuit reads —
-- | one shared from advice, one a baked-in constant.
data SlotSource
  -- | The rule being compiled. Its wrap verification key is read from
  -- | advice at prove time, because at step-compile time the wrap
  -- | circuit does not exist yet.
  = SelfSource
  -- | A previously-compiled proof system, whose constants are baked
  -- | into the step circuit.
  | ExternalSource CompiledTagData
  -- | A verification key arriving as a runtime witness at prove time,
  -- | bounded at compile time by the slot's `localMpv`.
  | SideLoadedSource

-- | One previous-proof slot of one rule.
-- |
-- | There is no statement-size field: nothing in the compiler reads a
-- | statement's length. What it needs is the statement's `CircuitType`
-- | dictionary, to serialize a dummy or real statement, and the
-- | statement values, which arrive with the previous proofs at the
-- | prove call.
type Slot =
  { -- | The slot's own `max_proofs_verified` — how many proofs the
    -- | proof being verified here itself verified. This is the tag's
    -- | `n`, not the enclosing rule's, and every per-slot width on the
    -- | wrap side keys on it.
    localMpv :: Int
  , source :: SlotSource
  }

-- | The slot's wrap domain log2, which fixes its lagrange basis.
-- |
-- | A `SelfSource` slot uses the enclosing rule's own wrap domain, so
-- | the caller supplies it, already resolved against
-- | `wrapDomainOverride`; an `ExternalSource` slot carries its
-- | source's.
-- |
-- | A side-loaded slot's real wrap domain is selected in-circuit from
-- | the runtime key, so the value here only fills the per-slot lagrange
-- | vector: it comes from the slot's own compile-time bound and ignores
-- | the enclosing override.
slotWrapDomainLog2 :: Int -> Slot -> Int
slotWrapDomainLog2 outerWrapDomainLog2 slot = case slot.source of
  SelfSource -> outerWrapDomainLog2
  ExternalSource d -> d.wrapDomainLog2
  SideLoadedSource -> wrapDomainLog2ForProofsVerified slot.localMpv

-- | The step-domain log2s of the slot's source, one per branch of that
-- | source. Drives `perSlotFopDomainLog2s`.
-- |
-- | A `SelfSource` slot takes the enclosing compile's own domains,
-- | which are only known after the pre-pass, so the caller supplies
-- | them — which is why this is derived rather than stored on the slot.
-- | A side-loaded slot has no compile-time step domain at all; it
-- | borrows the same array, and the real dispatch happens in
-- | `Pickles.Step.FinalizeOtherProof`'s side-loaded mode.
-- |
-- | `branchCount` is the width the result must have, the array being
-- | indexed by the enclosing compile's branches. Only single-branch
-- | external sources are supported: their one domain is replicated
-- | across the width.
slotSourceDomainLog2s :: Int -> Array Int -> Slot -> Array Int
slotSourceDomainLog2s branchCount selfStepDomainLog2s slot = case slot.source of
  SelfSource -> selfStepDomainLog2s
  SideLoadedSource -> selfStepDomainLog2s
  ExternalSource d
    | NEA.length d.stepDomainLog2s == 1 ->
        Array.replicate branchCount (NEA.head d.stepDomainLog2s)
    | otherwise -> NEA.toArray d.stepDomainLog2s

-- | The slot source's compile-time `num_chunks`, from which `zk_rows`
-- | follows. A `SelfSource` slot takes the enclosing compile's declared
-- | value; side-loaded previous proofs are single-chunk.
slotNumChunks :: Int -> Slot -> Int
slotNumChunks selfNumChunks slot = case slot.source of
  SelfSource -> selfNumChunks
  ExternalSource d -> d.numChunks
  SideLoadedSource -> 1

-- | The wrap verification key the slot verifies its previous proof
-- | against. A `SelfSource` slot takes the enclosing compile's own,
-- | which the caller supplies because at step-compile time it is read
-- | from advice; a side-loaded slot takes it too, its real key arriving
-- | as a runtime witness.
slotWrapVerifierIndex
  :: VerifierIndex PallasG WrapField -> Slot -> VerifierIndex PallasG WrapField
slotWrapVerifierIndex selfWrapVerifierIndex slot = case slot.source of
  SelfSource -> selfWrapVerifierIndex
  ExternalSource d -> d.wrapVerifierIndex
  SideLoadedSource -> selfWrapVerifierIndex

-- | The single step-domain log2 of the slot's source, for the places
-- | that need one scalar rather than the per-branch vector: the dummy
-- | wrap public input's `branch_data.domain_log2`, and the deferred
-- | values the slot finalizes.
-- |
-- | A `SelfSource` slot takes the enclosing compile's own realized
-- | domain, which only exists after its step circuit is built, so the
-- | caller supplies it. Only single-branch external sources are
-- | supported, so their one domain is the head of the array.
slotStepDomainLog2 :: Int -> Slot -> Int
slotStepDomainLog2 selfStepDomainLog2 slot = case slot.source of
  SelfSource -> selfStepDomainLog2
  SideLoadedSource -> selfStepDomainLog2
  ExternalSource d -> NEA.head d.stepDomainLog2s
