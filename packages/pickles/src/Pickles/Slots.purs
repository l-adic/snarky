-- | Type-level slot descriptors shared between step- and wrap-side
-- | per-slot carriers. The descriptor encodes what a parent rule needs
-- | from each prev slot at the type level: the slot's
-- | `max_proofs_verified`, the `num_chunks` of the compile that produced
-- | the prev, and the prev's statement type.
-- |
-- | Pure phantom types — no value-level inhabitants. The spec for a
-- | rule's prevs is the tuple chain
-- | `Slot n₁ nc₁ s₁ /\ Slot n₂ nc₂ s₂ /\ … /\ Unit`.
-- |
-- | The step-side carrier (`Pickles.Step.Slots`) parameterises its
-- | type classes by these descriptors. The wrap side takes its slot
-- | widths as a runtime `Vector mpv Int` instead.
-- |
-- | **Where the kind went.** This type used to carry a `SlotKind` tag
-- | distinguishing a compiled prev, whose wrap VK is baked in at
-- | step-compile time, from a side-loaded one, whose wrap VK arrives at
-- | prove time. That tag forced every class on this path into two
-- | near-identical instances, one per kind, and forced the value-level
-- | three-case slot source to be narrowed to one case at each of them —
-- | narrowings whose impossible branches were filled with `unsafeThrow`.
-- | The distinction is now carried where it already existed as data: the
-- | slot's key (`Pickles.Prove.Compile.SlotWrapKey`) says which kind it
-- | is, and the one place that needs to know dispatches on it.
module Pickles.Slots
  ( Slot
  ) where

-- | A type-level slot descriptor: `max_proofs_verified` (or, for a
-- | side-loaded slot, the compile-time upper bound on the side-loaded
-- | tag's mpv), `num_chunks` of the prev's compile, and the prev's
-- | statement type.
-- |
-- | `stepChunks` is an axis of its own because `num_chunks` is
-- | per-compile in OCaml Pickles — each prev tag was produced by some
-- | `Pickles.compile_promise ~num_chunks:N` call, and the step circuit
-- | that verifies that prev needs to allocate FFI commitments at THAT
-- | num_chunks. Self-recursive prevs in a compile with `@stepChunks:k`
-- | conventionally have `stepChunks=k`. External-tag prevs can have a
-- | different `stepChunks` than the current compile.
-- |
-- | Pure phantom; no value-level inhabitants. The spec is the tuple
-- | chain `Slot n₁ nc₁ s₁ /\ Slot n₂ nc₂ s₂ /\ … /\ Unit` — `Unit`
-- | terminates the chain (the empty-prev list).
foreign import data Slot :: Int -> Int -> Type -> Type
