-- | Type-level slot descriptors shared between step- and wrap-side
-- | per-slot carriers. The descriptor encodes how a parent rule
-- | identifies each prev slot:
-- |
-- |   * `SlotKind` distinguishes a `Compiled` prev (whose wrap VK is
-- |     baked into the parent's compile output at step-compile time)
-- |     from a `SideLoaded` prev (whose wrap VK is supplied at prove
-- |     time).
-- |   * `Slot k n stmt` carries the kind tag, the slot's
-- |     `max_proofs_verified`, and the prev's statement type.
-- |
-- | Pure phantom types — no value-level inhabitants. The spec for a
-- | rule's prevs is the tuple chain
-- | `Slot k₁ n₁ s₁ /\ Slot k₂ n₂ s₂ /\ … /\ Unit`.
-- |
-- | Step- and wrap-side carriers (`Pickles.Step.Slots`,
-- | `Pickles.Wrap.Slots`) parameterise their type classes by these
-- | descriptors so both sides agree on the slot shape.
module Pickles.Slots
  ( SlotKind
  , Compiled
  , SideLoaded
  , Slot
  ) where

-- | Kind for a slot's source: a `Compiled` slot is a previously-
-- | compiled rule whose wrap VK is baked into the parent's compile
-- | output; a `SideLoaded` slot's wrap VK is supplied at prove time.
data SlotKind

-- | Phantom inhabitant of `SlotKind` — wrap VK + step-domain log2 are
-- | known at compile time.
foreign import data Compiled :: SlotKind

-- | Phantom inhabitant of `SlotKind` — wrap VK + step-domain log2 are
-- | sourced at runtime from a `Pickles.Sideload.VerificationKey`.
foreign import data SideLoaded :: SlotKind

-- | A type-level slot descriptor: kind tag, `max_proofs_verified` (or
-- | for side-loaded slots, the compile-time upper bound on the
-- | side-loaded tag's mpv), `num_chunks` of the prev's compile, and
-- | the prev's statement type.
-- |
-- | `stepChunks` is the third axis because `num_chunks` is per-compile
-- | in OCaml Pickles — each prev tag was produced by some
-- | `Pickles.compile_promise ~num_chunks:N` call, and the step circuit
-- | that verifies that prev needs to allocate FFI commitments at THAT
-- | num_chunks. Self-recursive prevs in a compile with `@stepChunks:k`
-- | conventionally have `stepChunks=k`. External-tag prevs can have a
-- | different `stepChunks` than the current compile.
-- |
-- | Pure phantom; no value-level inhabitants. The spec is the tuple
-- | chain `Slot k₁ n₁ nc₁ s₁ /\ Slot k₂ n₂ nc₂ s₂ /\ … /\ Unit` — `Unit`
-- | terminates the chain (the empty-prev list).
foreign import data Slot :: SlotKind -> Int -> Int -> Type -> Type
