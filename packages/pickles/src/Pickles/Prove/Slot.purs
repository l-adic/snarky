-- | Runtime slot data — the value-level replacement for the
-- | type-level shape machinery of `Pickles.Prove.Compile`.
-- |
-- | Everything a pickles compiler needs to know about a rule's
-- | previous-proof slot is runtime data. OCaml stores it that way too:
-- | `inductive_rule.ml` holds `prevs : H4.T(Tag).t`, an H-list of
-- | runtime `Tag.t` values, and `step_main.ml` folds over it. The GADT
-- | indices make the H-list well typed; they carry no data the fold
-- | does not also have at runtime.
-- |
-- | This module is that data, with no type-level parameters, so a
-- | `Slot` is a plain `Type` and a rule's slot list is an `Array Slot`.
-- | Lengths fixed by kimchi or pickles (`Vector 15` of columns,
-- | `Vector 32` of unfinalized fields, chunk counts) stay type-level;
-- | lengths that vary per application (slot count, `mpv`, branch
-- | count) live here.
module Pickles.Prove.Slot
  ( CompiledTagData
  , Slot
  , SlotSource(..)
  , AppSpec
  , RuleSpec
  , appMpv
  , isSelf
  , isSideLoaded
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
import Data.Semigroup.Foldable (maximum)
import Pickles.Field (WrapField)
import Pickles.Step.Dummy (wrapDomainLog2ForProofsVerified)
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Curves.Pasta (PallasG)

-- | The constants a previously-compiled tag contributes to a slot that
-- | verifies its proofs. Mirrors OCaml `Types_map.Compiled.t`
-- | (`mina/src/lib/crypto/pickles/types_map.ml:100-112`), narrowed to
-- | the fields the step circuit actually bakes in.
-- |
-- | A wrap verification key alone is not enough: the step circuit also
-- | bakes in the source's wrap domain (which fixes the per-slot
-- | lagrange basis), its per-branch step domains (which drive
-- | `perSlotFopDomainLog2s`), and its chunk count (which fixes
-- | `zk_rows`). All four are compile-time constants of the imported
-- | proof system.
-- |
-- | The wrap verification key is kept as the raw `VerifierIndex` rather
-- | than an extracted `VerificationKey wrapVkChunks _` so that `Slot`
-- | stays free of type-level parameters. The extraction to commitments
-- | happens at the use site, where `wrapVkChunks` is pinned.
type CompiledTagData =
  { wrapVerifierIndex :: VerifierIndex PallasG WrapField
  -- | OCaml `wrap_domains.h` of the imported system: 13 for 0 proofs
  -- | verified, 14 for 1, 15 for 2 (`common.ml`).
  , wrapDomainLog2 :: Int
  -- | The imported system's realized step-domain log2, one per branch
  -- | of that system, deduplicated. Non-empty for the same reason
  -- | `AppSpec.rules` is: a system with no branches has no step circuit
  -- | and so no domain.
  , stepDomainLog2s :: NonEmptyArray Int
  -- | The imported system's compile-time `num_chunks`. `zk_rows`
  -- | follows from it.
  , numChunks :: Int
  }

-- | Where a slot's previous proofs come from. The three cases are
-- | exactly OCaml's: the rule currently being compiled, another
-- | already-compiled proof system, or a verification key supplied at
-- | prove time.
-- |
-- | `Self` and `External` are both *compiled* sources in the sense of
-- | `Pickles.Slots.Compiled` — the distinction between them is which
-- | verification key the step circuit reads (shared from advice, or a
-- | baked-in constant), and OCaml makes it at runtime too, via
-- | `Type_equal.Id.same_witness self.id tag.id` (`step_main.ml`).
data SlotSource
  -- | The slot points at the rule being compiled. The wrap
  -- | verification key is read from advice at prove time, because at
  -- | step-compile time the wrap circuit does not exist yet.
  = SelfSource
  -- | The slot points at a previously-compiled proof system, whose
  -- | constants are baked into the step circuit.
  | ExternalSource CompiledTagData
  -- | The slot's verification key arrives as a runtime witness at
  -- | prove time, bounded at compile time by the slot's `localMpv`.
  | SideLoadedSource

-- | One previous-proof slot of one rule.
-- |
-- | There is deliberately no statement-size field. Nothing in the
-- | compiler reads a statement's length: what it needs is the
-- | statement's `CircuitType` dictionary (to serialize a dummy or real
-- | statement) and the statement *values*, which arrive with the
-- | previous proofs at the prove call. See the Phase 0 inventory, OQ-5.
type Slot =
  { -- | The slot's own `max_proofs_verified` — how many proofs the
    -- | proof being verified here itself verified. This is the tag's
    -- | `n`, not the enclosing rule's. Every per-slot width on the wrap
    -- | side keys on it, and mina PR #19235 keys its branch-data mask
    -- | width on `max 2 localMpv`.
    localMpv :: Int
  , source :: SlotSource
  }

-- | One rule of an application: its previous-proof slots in order.
-- | A rule may have none, which is the base case of every application,
-- | so the slots are a plain `Array`.
-- |
-- | The rule body itself (`StepRuleAt`) is not stored here in Phase 1;
-- | it stays where the existing `RuleEntry` holds it, so that no caller
-- | changes. Phase 3 merges the two.
type RuleSpec =
  { name :: String
  , slots :: Array Slot
  }

-- | An application: its rules, in branch order.
-- |
-- | Non-empty because an application with no branches has no step
-- | circuit to compile and no verification key to produce.
-- | `compileMulti` already states this at the type level, as
-- | `Add 1 branchesPred branches`.
type AppSpec = { rules :: NonEmptyArray RuleSpec }

-- | The application's `max_proofs_verified` — the widest rule's slot
-- | count. OCaml's `Max_proofs_verified.n`, and the width every
-- | branch's step statement is padded to.
-- |
-- | Total, with no default: `maximum` on a `Foldable1` is
-- | `ala Max foldMap1`, and the max-semigroup needs no identity. An
-- | identity would be wrong here anyway, since `Monoid (Max Int)` comes
-- | from `Bounded` and would fold an empty application to `bottom`.
appMpv :: AppSpec -> Int
appMpv spec = maximum (map (Array.length <<< _.slots) spec.rules)

isSelf :: Slot -> Boolean
isSelf slot = case slot.source of
  SelfSource -> true
  _ -> false

isSideLoaded :: Slot -> Boolean
isSideLoaded slot = case slot.source of
  SideLoadedSource -> true
  _ -> false

-- | The slot's wrap domain log2, which fixes its lagrange basis.
-- |
-- | `Self` slots use the enclosing rule's own wrap domain, so the
-- | caller supplies it (already resolved against `wrapDomainOverride`).
-- | `External` slots carry their source's.
-- |
-- | A side-loaded slot's real wrap domain is selected in-circuit from
-- | the runtime key, so the value here is only a placeholder that fills
-- | the per-slot lagrange vector; it is derived from the slot's own
-- | compile-time bound and ignores the enclosing override. See the
-- | Phase 0 inventory, OQ-8.
slotWrapDomainLog2 :: Int -> Slot -> Int
slotWrapDomainLog2 outerWrapDomainLog2 slot = case slot.source of
  SelfSource -> outerWrapDomainLog2
  ExternalSource d -> d.wrapDomainLog2
  SideLoadedSource -> wrapDomainLog2ForProofsVerified slot.localMpv

-- | The step-domain log2s of the slot's source, one per branch of that
-- | source. Drives `perSlotFopDomainLog2s`.
-- |
-- | `Self` slots take the enclosing compile's own domains, which are
-- | only known after the pre-pass, so the caller supplies them. This is
-- | why the value is derived here rather than stored on the slot.
-- | A side-loaded slot has no compile-time step domain at all; it
-- | borrows the same array as a placeholder, and the real dispatch
-- | happens in `Pickles.Step.FinalizeOtherProof`'s side-loaded mode.
-- |
-- | `branchCount` is the width the result must have, because the array
-- | indexes the enclosing compile's branches. Only single-branch
-- | external sources are supported: their one domain is replicated
-- | across the width, which is what the type-level code did.
slotSourceDomainLog2s :: Int -> Array Int -> Slot -> Array Int
slotSourceDomainLog2s branchCount selfStepDomainLog2s slot = case slot.source of
  SelfSource -> selfStepDomainLog2s
  SideLoadedSource -> selfStepDomainLog2s
  ExternalSource d
    | NEA.length d.stepDomainLog2s == 1 ->
        Array.replicate branchCount (NEA.head d.stepDomainLog2s)
    | otherwise -> NEA.toArray d.stepDomainLog2s

-- | The slot source's compile-time `num_chunks`, from which `zk_rows`
-- | follows. `Self` slots take the enclosing compile's declared value.
-- | Side-loaded previous proofs are single-chunk, matching OCaml's
-- | side-loaded `For_step` at `zk_rows_by_default`.
slotNumChunks :: Int -> Slot -> Int
slotNumChunks selfNumChunks slot = case slot.source of
  SelfSource -> selfNumChunks
  ExternalSource d -> d.numChunks
  SideLoadedSource -> 1

-- | The wrap verification key the slot verifies its previous proof
-- | against. `Self` slots take the enclosing compile's own, which the
-- | caller supplies because at step-compile time it is read from advice.
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
-- | `Self` slots take the enclosing compile's own realized domain,
-- | which only exists after its step circuit is built, so the caller
-- | supplies it. Only single-branch external sources are supported, so
-- | their one domain is the head of the array.
slotStepDomainLog2 :: Int -> Slot -> Int
slotStepDomainLog2 selfStepDomainLog2 slot = case slot.source of
  SelfSource -> selfStepDomainLog2
  SideLoadedSource -> selfStepDomainLog2
  ExternalSource d -> NEA.head d.stepDomainLog2s
