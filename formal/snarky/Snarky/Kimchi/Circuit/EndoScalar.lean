import Snarky.Circuit.DSL.Field
import Snarky.Circuit.DSL.Assert
import Snarky.Circuit.DSL.Bits
import Snarky.Kimchi.Semantics
import Snarky.Kimchi.Circuit.Utils

/-!
# The EndoScalar gadget

Port of `Snarky.Circuit.Kimchi.EndoScalar`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/EndoScalar.purs): the GLV challenge
decomposition. `toFieldChecked'` witnesses the scalar's 2-bit crumbs in ONE bulk
`exists` — eight per row, MSB-first — then threads the three accumulators through
`mapAccumM`, one `(a8, b8, n8)` witness per row, and emits the `endoScalar` round
list; `toField` pins the reconstruction `n` to the scalar and returns the affine
`a·endo + b`. `toFieldPure` is the constant-space model of the same fold.

Name map: `toField`, `toFieldChecked'`, `toFieldPure` keep their names, namespaced
`EndoScalar` after the PS module's qualified use. `expandToEndoScalar` is
pickles-layer (cross-field transport) and is not ported.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS's type-level `SizedF nBits` sizing renders as the explicit `rows` parameter
  with `16 · rows` bits, and the bit reads go through `[ToNat F]`.
- PS's record `exists` allocates its fields alphabetically; the per-row witness is
  the ordered triple `(a8, b8, n8)`, the same allocation spelled explicitly.
- PS's `aF`/`bF` throw on impossible crumbs; `aDigit`/`bDigit` render the dead
  branches as `0`.
- `toFieldPure` is generalized from PS's pinned 128 bits to `16 · rows`.
-/

namespace Snarky.Kimchi.EndoScalar

open Snarky

variable {F c : Type}

/-- The crumb-to-`a`-digit map (PS `aF`). -/
private def aDigit [Field F] [DecidableEq F] (x : F) : F :=
  if x = 2 then -1 else if x = 3 then 1 else 0

/-- The crumb-to-`b`-digit map (PS `bF`). -/
private def bDigit [Field F] [DecidableEq F] (x : F) : F :=
  if x = 0 then -1 else if x = 1 then 1 else 0

/-- The scalar's MSB-first 2-bit crumbs, eight per row (PS `toBits` reversed and
paired): crumb `i` is `2·bit(16·rows − 1 − 2i) + bit(16·rows − 2 − 2i)`. -/
private def crumbsWit [Field F] [ToNat F] (rows : ℕ) (scalar : FVar F) :
    AsProver F (Vector (Vector F 8) rows) := do
  let v ← AsProver.readCVar scalar
  let n := ToNat.toNat v
  pure (Vector.ofFn fun r => Vector.ofFn fun j =>
    let i := 8 * r.1 + j.1
    ((2 * (if n.testBit (16 * rows - 1 - 2 * i) then 1 else 0)
      + (if n.testBit (16 * rows - 2 - 2 * i) then 1 else 0) : F)))

/-- One row's accumulator witness: fold the row's eight crumbs into the three
accumulators, returned in the allocation order `(a8, b8, n8)`. -/
private def rowWit [Field F] [DecidableEq F] (xs : Vector (FVar F) 8)
    (st : FVar F × FVar F × FVar F) : AsProver F (F × F × F) := do
  let a0 ← AsProver.readCVar st.1
  let b0 ← AsProver.readCVar st.2.1
  let n0 ← AsProver.readCVar st.2.2
  let vals ← xs.toList.mapM AsProver.readCVar
  pure (vals.foldl (fun acc x => 2 * acc + aDigit x) a0,
        vals.foldl (fun acc x => 2 * acc + bDigit x) b0,
        vals.foldl (fun acc x => 4 * acc + x) n0)

/-- The gate emitter (PS `toFieldChecked'`; OCaml
`Pickles.Scalar_challenge.to_field_checked'`): the bulk crumb witness, the
accumulator rounds, one `endoScalar` constraint — returning the raw `(a, b, n)`
accumulators with no wrapper constraints. -/
def toFieldChecked' [Field F] [DecidableEq F] [ToNat F] [KimchiSystem F c]
    (rows : ℕ) (scalar : FVar F) :
    CircuitM F c (FVar F × FVar F × FVar F) := do
  let crumbs ← witness (val := Vector (Vector F 8) rows) (crumbsWit rows scalar)
  let (rounds, fin) ← mapAccumM
    (fun (st : FVar F × FVar F × FVar F) (xs : Vector (FVar F) 8) => do
      let w ← witness (val := F × F × F) (rowWit xs st)
      pure (({ n0 := st.2.2, n8 := w.2.2, a0 := st.1, a8 := w.1,
               b0 := st.2.1, b8 := w.2.1, xs } : EndoScalarRound F),
            (w.1, w.2.1, w.2.2)))
    (.const 2, .const 2, .const 0) crumbs.toList
  addConstraint (KimchiSystem.endoScalar rounds)
  pure fin

/-- The checked decomposition (PS `toField`; OCaml `to_field_checked`): the gate,
the pin `n = scalar`, and the affine reconstruction `a·endo + b` — folded
constraint-free when the endo coefficient is a constant. -/
def toField [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]
    (rows : ℕ) (scalar endo : FVar F) : CircuitM F c (FVar F) := do
  let (a, b, n) ← toFieldChecked' (c := c) rows scalar
  assertEqual n scalar
  match endo with
  | .const e => pure (CVar.add_ (CVar.scale_ e a) b)
  | _ => do
    let p ← mul a endo
    pure (CVar.add_ b p)

/-- The pure model (PS `toFieldPure`): the same MSB-first bit-pair fold on values,
from the accumulator seeds `(2, 2)`. -/
def toFieldPure [Field F] [ToNat F] (rows : ℕ) (scalar endo : F) : F :=
  let n := ToNat.toNat scalar
  let acc := (List.range (8 * rows)).foldl
    (fun (st : F × F) i =>
      let s : F := if n.testBit (16 * rows - 2 - 2 * i) then 1 else -1
      if n.testBit (16 * rows - 1 - 2 * i) then (2 * st.1 + s, 2 * st.2)
      else (2 * st.1, 2 * st.2 + s))
    (2, 2)
  acc.1 * endo + acc.2

end Snarky.Kimchi.EndoScalar
