import Snarky.Encoding
import Snarky.Kimchi.Constraint.AddComplete
import Snarky.Kimchi.Constraint.Reduction

/-!
# The EndoMul reducer

Port of `Snarky.Constraint.Kimchi.EndoMul`
(packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/EndoMul.purs): the per-round GLV
window payload and `reduce` — one `endoMul` row per round plus a trailing `zero` row
carrying the FINAL accumulator and scalar, which the last round's two-row gate reads
as its next-row outputs.

The reduction ORDER is the byte contract. The final accumulator `s` and scalar
`nAcc` reduce FIRST (PS binds them before the round traverse), then each round in row
order: `t` and `p` pointwise x-first, `nAcc`, `r` pointwise, `s1`, `s3`, the four
bits in index order, `inv` last.

Name map: PS `Round` becomes `EndoMulRound` (the bare name is too generic for
the flat namespace); `EndoMul` and `reduce` keep their names; `finalZeroRow` stays
the named helper.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- The round's `s` and `nAccNext` fields are carried but NOT reduced, exactly as in
  PS: the gate is two-row, and a round's outputs are read from the NEXT row (the
  following round's `p`/`nAcc` cells, or the trailing `zero` row).
- PS `NonEmptyArray` renders as the plain list (a nonempty invariant carried by the
  emitters, not the type); the width-4 bit vector as named fields `bit0 … bit3`
  (the step-6 budget lesson); the `traverse` as the structural fold.
- The payload carries the endomorphism coefficient `endo` (in PS it is ambient, a
  curve constant the verifier knows): the Poseidon payload-data deviation, so the
  semantics can read the gate at it. `reduce` ignores the field — the row has no
  coefficient cells — so the corpus is untouched.
-/

namespace Snarky.Kimchi

open Snarky

/-- One GLV window round (PS `Round`): base `T`, input accumulator `P`, intermediate
`R`, output `S`, the two slopes, the scalar registers, four bits, and the
distinct-point inverse. -/
structure EndoMulRound (F : Type u) where
  /-- The base point `T`. -/
  t : AffinePoint (FVar F)
  /-- The input accumulator `P`. -/
  p : AffinePoint (FVar F)
  /-- The intermediate accumulator `R = (P + Q₁) + P`. -/
  r : AffinePoint (FVar F)
  /-- The output accumulator `S = (R + Q₂) + R` — carried, not reduced (the next
  row's `p` cells hold it). -/
  s : AffinePoint (FVar F)
  /-- The first window's slope. -/
  s1 : FVar F
  /-- The second window's slope. -/
  s3 : FVar F
  /-- The input scalar register. -/
  nAcc : FVar F
  /-- The output scalar register — carried, not reduced (the next row's `nAcc` cell
  holds it). -/
  nAccNext : FVar F
  /-- Window bit `b₁` (first window's base choice). -/
  bit0 : FVar F
  /-- Window bit `b₂` (first window's sign). -/
  bit1 : FVar F
  /-- Window bit `b₃` (second window's base choice). -/
  bit2 : FVar F
  /-- Window bit `b₄` (second window's sign). -/
  bit3 : FVar F
  /-- The witnessed distinct-point inverse. -/
  inv : FVar F
  deriving Repr, DecidableEq

/-- An endomorphism-optimized scalar multiplication (PS `EndoMul`): the rounds, the
final accumulator and scalar the trailing `zero` row carries, and the endomorphism
coefficient (the payload-data deviation in the module docstring). -/
structure EndoMul (F : Type u) where
  /-- The rounds, in row order. -/
  state : List (EndoMulRound F)
  /-- The final output accumulator. -/
  s : AffinePoint (FVar F)
  /-- The final scalar register. -/
  nAcc : FVar F
  /-- The endomorphism coefficient `β`: parameter data, not a wire — `reduce`
  ignores it (the row has no coefficient cells), and the semantics reads the gate
  at it. -/
  endo : F
  deriving Repr, DecidableEq

variable {F : Type} {m : Type → Type}

/-- Reduce one round to its `endoMul` row (PS `reduceRound` + `endoMulRound`): `t`,
`p` (x-first), `nAcc`, `r`, `s1`, `s3`, the bits, `inv`; cells
`[xT yT inv _ xP yP n xR yR s1 s3 b₁ b₂ b₃ b₄]`. -/
def EndoMulRound.reduce [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] (c : EndoMulRound F) : m (KimchiRow F) := do
  let vtx ← reduceToVariable c.t.x
  let vty ← reduceToVariable c.t.y
  let vpx ← reduceToVariable c.p.x
  let vpy ← reduceToVariable c.p.y
  let vn ← reduceToVariable c.nAcc
  let vrx ← reduceToVariable c.r.x
  let vry ← reduceToVariable c.r.y
  let vs1 ← reduceToVariable c.s1
  let vs3 ← reduceToVariable c.s3
  let vb1 ← reduceToVariable c.bit0
  let vb2 ← reduceToVariable c.bit1
  let vb3 ← reduceToVariable c.bit2
  let vb4 ← reduceToVariable c.bit3
  let vinv ← reduceToVariable c.inv
  pure { kind := .endoMul,
         vars := ⟨⟨[some vtx, some vty, some vinv, none, some vpx, some vpy,
                    some vn, some vrx, some vry, some vs1, some vs3,
                    some vb1, some vb2, some vb3, some vb4]⟩, by simp⟩,
         coeffs := [] }

/-- The trailing `zero` row (PS `finalZeroRow`): the final accumulator and scalar in
the next-row output cells `4, 5, 6` the last `endoMul` row reads. -/
private def EndoMul.finalZeroRow (xs ys nAcc : Variable) : KimchiRow F :=
  { kind := .zero,
    vars := ⟨⟨[none, none, none, none, some xs, some ys, some nAcc, none, none,
               none, none, none, none, none, none]⟩, by simp⟩,
    coeffs := [] }

/-- Reduce the rounds in row order (the PS `traverse` as the structural fold). -/
private def EndoMul.reduceRounds [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] : List (EndoMulRound F) → m (List (KimchiRow F))
  | [] => pure []
  | c :: cs => do
    let row ← c.reduce
    let rest ← EndoMul.reduceRounds cs
    pure (row :: rest)

/-- Reduce a multiplication (PS `reduce`): the final accumulator and scalar FIRST,
then the rounds, then the trailing `zero` row. -/
def EndoMul.reduce [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] (c : EndoMul F) : m (List (KimchiRow F)) := do
  let xs ← reduceToVariable c.s.x
  let ys ← reduceToVariable c.s.y
  let nAcc ← reduceToVariable c.nAcc
  let rows ← EndoMul.reduceRounds c.state
  pure (rows ++ [EndoMul.finalZeroRow xs ys nAcc])

/-- The round reducer is a seam: fourteen pinned operands, one row. -/
private theorem EndoMulRound.reduce_seam [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F]
    [DecidableEq F] (c : EndoMulRound F) :
    Seam (EndoMulRound.reduce (m := PlonkBuilder F) c)
      (EndoMulRound.reduce (m := PlonkProver F) c) := by
  unfold EndoMulRound.reduce
  repeat first
    | exact Seam.pure _
    | refine Seam.bind (reduceToVariable_seam _) fun _ => ?_

/-- `reduceRounds` is a seam: the structural fold composes. -/
private theorem EndoMul.reduceRounds_seam [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F]
    [DecidableEq F]
    (cs : List (EndoMulRound F)) :
    Seam (EndoMul.reduceRounds (m := PlonkBuilder F) cs)
      (EndoMul.reduceRounds (m := PlonkProver F) cs) := by
  induction cs with
  | nil =>
    simp only [EndoMul.reduceRounds]
    exact Seam.pure _
  | cons c cs ih =>
    simp only [EndoMul.reduceRounds]
    refine Seam.bind (EndoMulRound.reduce_seam c) fun _ => ?_
    refine Seam.bind ih fun _ => ?_
    exact Seam.pure _

/-- The endomorphism-multiplication reducer is a seam: the final accumulator and
scalar first, then the rounds, then the trailing row, purely. -/
theorem EndoMul.reduce_seam [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F]
    [DecidableEq F] (c : EndoMul F) :
    Seam (EndoMul.reduce (m := PlonkBuilder F) c)
      (EndoMul.reduce (m := PlonkProver F) c) := by
  unfold EndoMul.reduce
  repeat first
    | exact Seam.pure _
    | refine Seam.bind (reduceToVariable_seam _) fun _ => ?_
    | refine Seam.bind (EndoMul.reduceRounds_seam _) fun _ => ?_

end Snarky.Kimchi
