import Snarky.DSL.Field
import Snarky.DSL.Assert
import Snarky.DSL.Bits
import Snarky.DSL.Boolean
import Snarky.Types.Shifted
import Snarky.Kimchi.Circuit.AddComplete
import Snarky.Traverse
import Kimchi.Gate.VarBaseMul
import Kimchi.Gate.Semantics.VarBaseMul
import Snarky.Kimchi.Circuit.Curve
import Kimchi.Gate.Semantics.EndoMul
import Snarky.Prover.StdWP
import Mathlib.Util.CountHeartbeats

/-!
# The VarBaseMul gadget

Port of `packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/VarBaseMul.purs`, itself after
`plonk_curve_ops.ml`. `varBaseMul` is the double-add ladder: it witnesses the scalar's bits,
walks `acc' = 2·acc + Q` per bit with `Q = (xT, (2b−1)·yT)` in 5-bit rows, pins the running
scalar register, and emits one `varBaseMul` constraint. Its consumers are `scaleFast1`
(`Type1` scalars), `scaleFast2` and `scaleFast2'` (split scalars, for a scalar field larger
than the circuit field), and `splitFieldVar`.

The emitted circuits of `scaleFast1` at the full 255-bit ladder and of `scaleFast2'` at the
128-bit split are checked against recorded fixtures (`formal/scripts/check_cs.lean`).

Each section holds one circuit, its soundness spec and its completeness law at the prover's
reading, and seals the circuit `irreducible`: later sections reach it only through those
laws. The ladders
`varBaseMul`, `scaleFast2` and `scaleFast2'` also state their scalar side alone, for any base
(`*_spec_scalar`): the decomposition and booleanity rows never read the base.

## Deviations from the original

- The original computes the whole witness chain in one batch (a projective walk with batch
  inversion). Here each bit step is computed from the threaded variables by the gate model's
  `Kimchi.Gate.VarBaseMul.stepBit`. The advice values agree; the circuit is untouched.
- The original aborts the prover on a degenerate step. Here the advice is total: division
  by zero returns junk. The two agree on non-degenerate inputs.
- The original allocates each bit step's five advice values through five witness calls, and
  walks a round's five bits with a loop. Here one call witnesses the five values, and the
  round is unrolled into five calls. Variable ids and the circuit are unchanged, but each
  round's law pays for the five steps separately rather than once against an invariant.
- Two of each step's five advice values are never read back; they are kept so the variable
  ids agree with the original.
- The original's type-level widths become the parameters `(n chunks : ℕ)`, with `5 * chunks`
  bits walked; the laws state the bounds the types enforced.
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

open Std.Do WeierstrassCurve.Affine

/-! ## The round

One 5-bit row. Its soundness law is the wiring (`Threads`); its completeness law adds that
the round's cells are in scope and read as the gate's canonical row. -/

/-- The scalar's `n` bits LSB-first as field values, in one witness. -/
private def lsbBitsWit [Field F] [ToNat F] (n : ℕ) (scalar : FVar F) :
    AsProver F (Vector F n) := do
  let v ← AsProver.readCVar scalar
  pure (Vector.ofFn fun i => if (ToNat.toNat v).testBit i.1 then 1 else 0)

/-- The scalar-register advice: fold `2a + b` over the row's five bits, from the previous
register. -/
private def nAccWit [Field F] (nPrev : FVar F) (bs : Vector (FVar F) 5) :
    AsProver F F := do
  let a ← AsProver.readCVar nPrev
  let b0 ← AsProver.readCVar bs[0]
  let b1 ← AsProver.readCVar bs[1]
  let b2 ← AsProver.readCVar bs[2]
  let b3 ← AsProver.readCVar bs[3]
  let b4 ← AsProver.readCVar bs[4]
  pure (b4 + 2 * (b3 + 2 * (b2 + 2 * (b1 + 2 * (b0 + 2 * a)))))

/-- One bit step's five advice values `(s1, s1Sq, s2, xRes, yRes)`: the slope and result
from the gate model's `stepBit`, plus two values nothing reads. -/
private def bitWit [Field F] [DecidableEq F] (t : AffinePoint (FVar F))
    (b : FVar F) (acc : AffinePoint (FVar F)) :
    AsProver F (F × F × F × F × F) := do
  let xb ← AsProver.readCVar t.x
  let yb ← AsProver.readCVar t.y
  let xi ← AsProver.readCVar acc.x
  let yi ← AsProver.readCVar acc.y
  let bv ← AsProver.readCVar b
  let (s1, xo, yo) := Kimchi.Gate.VarBaseMul.stepBit bv xb yb xi yi
  let s1Sq := s1 * s1
  let s2 := 2 * yi / (2 * xi + xb - s1Sq) - s1
  pure (s1, s1Sq, s2, xo, yo)

/-- One 5-bit round: the register advice, then five bit steps threaded through the
accumulator, returned as the gate's `ScaleRound` record and the next `(acc, register)` pair.
A named circuit, so the ladder's loop walks one spec per round. -/
def scaleRound [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (base : AffinePoint (FVar F)) (st : AffinePoint (FVar F) × FVar F)
    (bs : Vector (FVar F) 5) :
    CircuitM F c (ScaleRound F × (AffinePoint (FVar F) × FVar F)) := do
  let nAcc ← witness (val := F) (nAccWit st.2 bs)
  let w0 ← witness (val := F × F × F × F × F) (bitWit base bs[0] st.1)
  let a1 : AffinePoint (FVar F) := ⟨w0.2.2.2.1, w0.2.2.2.2⟩
  let w1 ← witness (val := F × F × F × F × F) (bitWit base bs[1] a1)
  let a2 : AffinePoint (FVar F) := ⟨w1.2.2.2.1, w1.2.2.2.2⟩
  let w2 ← witness (val := F × F × F × F × F) (bitWit base bs[2] a2)
  let a3 : AffinePoint (FVar F) := ⟨w2.2.2.2.1, w2.2.2.2.2⟩
  let w3 ← witness (val := F × F × F × F × F) (bitWit base bs[3] a3)
  let a4 : AffinePoint (FVar F) := ⟨w3.2.2.2.1, w3.2.2.2.2⟩
  let w4 ← witness (val := F × F × F × F × F) (bitWit base bs[4] a4)
  let a5 : AffinePoint (FVar F) := ⟨w4.2.2.2.1, w4.2.2.2.2⟩
  pure (({ acc0 := st.1, acc1 := a1, acc2 := a2, acc3 := a3, acc4 := a4, acc5 := a5,
           bit0 := bs[0], bit1 := bs[1], bit2 := bs[2], bit3 := bs[3], bit4 := bs[4],
           slope0 := w0.1, slope1 := w1.1, slope2 := w2.1, slope3 := w3.1,
           slope4 := w4.1,
           nPrev := st.2, nNext := nAcc, base } : ScaleRound F),
         (a5, nAcc))

namespace VarBaseMul

variable {F c : Type}

/-- A round against its row: it reads the base and the row's five bits. -/
private def RowIn (base : AffinePoint (FVar F)) (bs : Vector (FVar F) 5) (r : ScaleRound F) :
    Prop :=
  r.base = base ∧ r.bit0 = bs[0] ∧ r.bit1 = bs[1] ∧ r.bit2 = bs[2] ∧ r.bit3 = bs[3] ∧
    r.bit4 = bs[4]

/-- The round reads the accumulator `st`, writes `st'`, and is wired to the base and the row's
five bits. No valuation appears. -/
private def Threads (base : AffinePoint (FVar F)) (st : AffinePoint (FVar F) × FVar F)
    (bs : Vector (FVar F) 5) (r : ScaleRound F)
    (st' : AffinePoint (FVar F) × FVar F) : Prop :=
  (r.acc0, r.nPrev) = st ∧ (r.acc5, r.nNext) = st' ∧ RowIn base bs r

open Std.Do in
/-- The round a call returns is wired to its inputs and outputs (`Threads`). -/
@[spec] private theorem scaleRound_spec {V : Valuation F} [Field F] [DecidableEq F]
    (base : AffinePoint (FVar F)) (st : AffinePoint (FVar F) × FVar F)
    (bs : Vector (FVar F) 5) :
    ⦃⌜True⌝⦄
    scaleRound (c := Builder V (KimchiConstraint F)) base st bs
    ⦃⇓ p _ => ⌜Threads base st bs p.1 p.2⌝⦄ := by
  simp only [scaleRound, Threads]
  mvcgen

/-- A round's cells. -/
private def cells [Field F] (r : ScaleRound F) : List (CVar F) :=
  [r.base.x, r.base.y, r.acc0.x, r.acc0.y, r.acc1.x, r.acc1.y, r.acc2.x, r.acc2.y,
    r.acc3.x, r.acc3.y, r.acc4.x, r.acc4.y, r.acc5.x, r.acc5.y,
    r.bit0, r.bit1, r.bit2, r.bit3, r.bit4,
    r.slope0, r.slope1, r.slope2, r.slope3, r.slope4, r.nPrev, r.nNext]

end VarBaseMul

/-! ### The round at the prover's reading

The round's step fact in `Prover.ScanStep` shape, at readings and conditions named once, and
the loop's instance of `Prover.mapAccumM_scan_spec` registered: the ladder's loop is then a
spec-table hit whose transports are grind lines, and its rows read as the gate's canonical
rows at the per-round prefix folds. -/

namespace VarBaseMul

/-- The register advice's value. -/
private def nAccVal [Field F] (a b0 b1 b2 b3 b4 : F) : F :=
  b4 + 2 * (b3 + 2 * (b2 + 2 * (b1 + 2 * (b0 + 2 * a))))

/-- One bit step's five advice values from the readings. -/
private def bitVal [Field F] (xb yb xi yi bv : F) : F × F × F × F × F :=
  let (s1, xo, yo) := Kimchi.Gate.VarBaseMul.stepBit bv xb yb xi yi
  (s1, s1 * s1, 2 * yi / (2 * xi + xb - s1 * s1) - s1, xo, yo)

/-- The round's canonical row from the per-bit values: what `Kimchi.Gate.VarBaseMul.build`
computes, in the witnesses' own vocabulary, so a round's reading is this record by unfolding
alone. -/
private def roundVal [Field F] (xb yb x0 y0 n b0 b1 b2 b3 b4 : F) :
    Kimchi.Gate.VarBaseMul.Witness F :=
  let v0 := bitVal xb yb x0 y0 b0
  let v1 := bitVal xb yb v0.2.2.2.1 v0.2.2.2.2 b1
  let v2 := bitVal xb yb v1.2.2.2.1 v1.2.2.2.2 b2
  let v3 := bitVal xb yb v2.2.2.2.1 v2.2.2.2.2 b3
  let v4 := bitVal xb yb v3.2.2.2.1 v3.2.2.2.2 b4
  { xT := xb, yT := yb, x0 := x0, y0 := y0,
    x1 := v0.2.2.2.1, y1 := v0.2.2.2.2, x2 := v1.2.2.2.1, y2 := v1.2.2.2.2,
    x3 := v2.2.2.2.1, y3 := v2.2.2.2.2, x4 := v3.2.2.2.1, y4 := v3.2.2.2.2,
    x5 := v4.2.2.2.1, y5 := v4.2.2.2.2, n := n, nPrime := nAccVal n b0 b1 b2 b3 b4,
    b0 := b0, b1 := b1, b2 := b2, b3 := b3, b4 := b4,
    s0 := v0.1, s1 := v1.1, s2 := v2.1, s3 := v3.1, s4 := v4.1 }

/-- The per-bit chain is the gate's canonical row. -/
private theorem roundVal_eq_build [Field F] (xb yb x0 y0 n b0 b1 b2 b3 b4 : F) :
    roundVal xb yb x0 y0 n b0 b1 b2 b3 b4 =
      Kimchi.Gate.VarBaseMul.build xb yb x0 y0 n b0 b1 b2 b3 b4 := rfl

/-- A row's five bits in scope. -/
private def bitsScoped (st : ProverState F) (b : Vector (FVar F) 5) : Prop :=
  ∀ (i : ℕ) (hi : i < 5), (b[i]'hi).Scoped st

private theorem nAccWit_run [Field F] {s : ProverState F} {nPrev : FVar F}
    {bs : Vector (FVar F) 5} (hn : nPrev.Scoped s) (hb : bitsScoped s bs) :
    (nAccWit nPrev bs).run s.env = .ok (nAccVal (nPrev.val s.env.get) (bs[0].val s.env.get)
      (bs[1].val s.env.get) (bs[2].val s.env.get) (bs[3].val s.env.get) (bs[4].val s.env.get)) := by
  simp [nAccWit, nAccVal, AsProver.readCVar_run hn, AsProver.readCVar_run (hb 0 (by omega)),
    AsProver.readCVar_run (hb 1 (by omega)), AsProver.readCVar_run (hb 2 (by omega)),
    AsProver.readCVar_run (hb 3 (by omega)), AsProver.readCVar_run (hb 4 (by omega))]

private theorem bitWit_run [Field F] [DecidableEq F] {s : ProverState F}
    {t : AffinePoint (FVar F)} {b : FVar F} {acc : AffinePoint (FVar F)} (htx : t.x.Scoped s)
    (hty : t.y.Scoped s) (hax : acc.x.Scoped s) (hay : acc.y.Scoped s) (hb : b.Scoped s) :
    (bitWit t b acc).run s.env = .ok (bitVal (t.x.val s.env.get) (t.y.val s.env.get)
      (acc.x.val s.env.get) (acc.y.val s.env.get) (b.val s.env.get)) := by
  simp [bitWit, bitVal, AsProver.readCVar_run htx, AsProver.readCVar_run hty,
    AsProver.readCVar_run hax, AsProver.readCVar_run hay, AsProver.readCVar_run hb]

/-- The threaded pair's condition: the base and the accumulator in scope. -/
private def accScoped (base : AffinePoint (FVar F)) (st : ProverState F)
    (a : AffinePoint (FVar F) × FVar F) : Prop :=
  base.x.Scoped st ∧ base.y.Scoped st ∧ a.1.x.Scoped st ∧ a.1.y.Scoped st ∧ a.2.Scoped st

/-- A round's cells in scope. -/
private def rowScoped [Field F] (st : ProverState F) (r : ScaleRound F) : Prop :=
  ∀ cv ∈ cells r, cv.Scoped st

/-- The threaded pair's reading: the base's, the accumulator's, the register's. -/
private def accRead [Field F] (base : AffinePoint (FVar F)) (st : ProverState F)
    (a : AffinePoint (FVar F) × FVar F) : (F × F) × (F × F) × F :=
  ((st.read base.x, st.read base.y), (st.read a.1.x, st.read a.1.y), st.read a.2)

/-- A row's bits' readings. -/
private def bitsRead [Field F] (st : ProverState F) (b : Vector (FVar F) 5) : F × F × F × F × F :=
  (st.read b[0], st.read b[1], st.read b[2], st.read b[3], st.read b[4])

/-- The row a round produces, from the pair's and the bits' readings. -/
private def rowStep [Field F] (a : (F × F) × (F × F) × F) (x : F × F × F × F × F) :
    Kimchi.Gate.VarBaseMul.Witness F :=
  roundVal a.1.1 a.1.2 a.2.1.1 a.2.1.2 a.2.2 x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- The pair's reading after a round: the base unchanged, the row's outputs. -/
private def accStep [Field F] (a : (F × F) × (F × F) × F) (x : F × F × F × F × F) :
    (F × F) × (F × F) × F :=
  (a.1, ((rowStep a x).x5, (rowStep a x).y5), (rowStep a x).nPrime)

set_option Elab.async false in
#count_heartbeats in
/-- The round's chain of states and every entry cell's reading along it, the one place the
chain is known: from the run's links, the entry lies below every state and each witness state
below the exit, and an entry cell in scope reads, at every state past the entry, what it read
at the entry. A step spec rewrites with the readings alone; the template a ladder's step spec
copies, with its own cells. -/
private theorem round_readings [Field F] {base : AffinePoint (FVar F)}
    {s₆ s₅ s₄ s₃ s₂ s₁ s : ProverState F} {acc : AffinePoint (FVar F) × FVar F}
    {bs : Vector (FVar F) 5} (hl5 : s₆ ≤ s₅) (hl0 : s₅ ≤ s₄) (hl1 : s₄ ≤ s₃) (hl2 : s₃ ≤ s₂)
    (hl3 : s₂ ≤ s₁) (hl4 : s₁ ≤ s) (hacc : accScoped base s₆ acc) (hbs : bitsScoped s₆ bs) :
    (s₆ ≤ s₅ ∧ s₆ ≤ s₄ ∧ s₆ ≤ s₃ ∧ s₆ ≤ s₂ ∧ s₆ ≤ s₁ ∧ s₆ ≤ s) ∧
      (s₅ ≤ s ∧ s₄ ≤ s ∧ s₃ ≤ s ∧ s₂ ≤ s) ∧
      ∀ t, s₆ ≤ t →
        base.x.val t.env.get = base.x.val s₆.env.get ∧
        base.y.val t.env.get = base.y.val s₆.env.get ∧
        acc.1.x.val t.env.get = acc.1.x.val s₆.env.get ∧
        acc.1.y.val t.env.get = acc.1.y.val s₆.env.get ∧
        acc.2.val t.env.get = acc.2.val s₆.env.get ∧
        ∀ (i : ℕ) (hi : i < 5), (bs[i]'hi).val t.env.get = (bs[i]'hi).val s₆.env.get := by
  have e4 : s₆ ≤ s₄ := hl5.trans hl0
  have e3 : s₆ ≤ s₃ := e4.trans hl1
  have e2 : s₆ ≤ s₂ := e3.trans hl2
  have e1 : s₆ ≤ s₁ := e2.trans hl3
  refine ⟨⟨hl5, e4, e3, e2, e1, e1.trans hl4⟩,
    ⟨hl0.trans (hl1.trans (hl2.trans (hl3.trans hl4))), hl1.trans (hl2.trans (hl3.trans hl4)),
      hl2.trans (hl3.trans hl4), hl3.trans hl4⟩, fun t hle => ?_⟩
  exact ⟨CVar.val_of_le hle hacc.1, CVar.val_of_le hle hacc.2.1, CVar.val_of_le hle hacc.2.2.1,
    CVar.val_of_le hle hacc.2.2.2.1, CVar.val_of_le hle hacc.2.2.2.2,
    fun i hi => CVar.val_of_le hle (hbs i hi)⟩

set_option Elab.async false in
#count_heartbeats in
/-- A round's reading survives the state's growth when its cells are in scope. -/
private theorem scaleRound_read_of_le [Field F] [DecidableEq F] {st st' : ProverState F}
    (hle : st ≤ st') {r : ScaleRound F} (h : ∀ cv ∈ cells r, cv.Scoped st) :
    ScaleRound.read st'.env.get r = ScaleRound.read st.env.get r := by
  simp (disch := (apply h; simp [cells])) only [ScaleRound.read, CVar.val_of_le hle]

end VarBaseMul

open VarBaseMul in
/-- `nAccWit` returns the register's value. -/
@[spec] private def Prover.nAccWit_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (nPrev : FVar F) (bs : Vector (FVar F) 5) :=
  Prover.register (Prover.witness_of_run (c := c) (nAccWit nPrev bs)
    (fun st => nPrev.Scoped st ∧ bitsScoped st bs)
    (fun st => nAccVal (st.read nPrev) (st.read bs[0]) (st.read bs[1]) (st.read bs[2])
      (st.read bs[3]) (st.read bs[4]))
    (fun _ h => nAccWit_run h.1 h.2) fun _ _ => by simp)

open VarBaseMul in
/-- `bitWit` returns the bit step's values. -/
@[spec] private def Prover.bitWit_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (t : AffinePoint (FVar F)) (b : FVar F) (acc : AffinePoint (FVar F)) :=
  Prover.register (Prover.witness_of_run (c := c) (bitWit t b acc)
    (fun st => t.x.Scoped st ∧ t.y.Scoped st ∧ acc.x.Scoped st ∧ acc.y.Scoped st ∧ b.Scoped st)
    (fun st => bitVal (st.read t.x) (st.read t.y) (st.read acc.x) (st.read acc.y) (st.read b))
    (fun _ h => bitWit_run h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) fun _ _ => by simp)

open VarBaseMul in
set_option Elab.async false in
#count_heartbeats in
/-- The round's step fact: its cells in scope, the next accumulator in scope, the round reading
as the gate's canonical row at the entry readings, and the accumulator reading as that row's
outputs. -/
private theorem Prover.scaleRound_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (base : AffinePoint (FVar F)) (st : ProverState F)
    (acc : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 5) :
    ⦃fun s => ⌜s = st ∧ accScoped base st acc ∧ bitsScoped st bs ∧ True⌝⦄
    scaleRound (c := Prover c) base acc bs
    ⦃⇓ p s' => ⌜Prover.ScanStep (accScoped base) rowScoped (accRead base) bitsRead
      (fun st r => ScaleRound.read st.env.get r) accStep rowStep st acc bs p.1 p.2 s'⌝⦄ := by
  unfold scaleRound
  mvcgen
  all_goals (try grind [Prover.Reg.iff, CircuitType.ReadsAs, CircuitType.scoped_fvar,
    CircuitType.scoped_prod', CVar.Scoped.of_le, accScoped, bitsScoped])
  -- the step fact
  rename_i s₆ nAcc s₅ hn w0 a1 s₄ h0 w1 a2 s₃ h1 w2 a3 s₂ h2 w3 a4 s₁ h3 w4 a5 s h4 hpre
  simp only [Prover.Reg.iff, a1, a2, a3, a4] at hn h0 h1 h2 h3 h4
  simp only [a1, a2, a3, a4, a5]
  obtain ⟨rfl, hacc, hbs⟩ := hpre
  obtain ⟨hnb, hl5⟩ := hn
  obtain ⟨hb0, hl0⟩ := h0
  obtain ⟨hb1, hl1⟩ := h1
  obtain ⟨hb2, hl2⟩ := h2
  obtain ⟨hb3, hl3⟩ := h3
  obtain ⟨hb4, hl4⟩ := h4
  -- the chain and the entry cells' readings along it, from the one lemma that knows it
  obtain ⟨⟨e5, e4, e3, e2, e1, e0⟩, ⟨l5, l4, l3, l2⟩, hrd⟩ :=
    round_readings hl5 hl0 hl1 hl2 hl3 hl4 hacc hbs
  -- the bundles at the final state
  have b0 := hb0.of_le l4
  have b1 := hb1.of_le l3
  have b2 := hb2.of_le l2
  have b3 := hb3.of_le hl4
  have b4 := hb4
  simp only [CircuitType.ReadsAs, CircuitType.scoped_prod', CircuitType.scoped_fvar,
    CircuitType.reads_prod', CircuitType.reads_fvar] at hnb b0 b1 b2 b3 b4 hb0 hb1 hb2 hb3
  obtain ⟨hnsc, hnrd⟩ := hnb
  refine ⟨?_, ?_, ?_, ?_, e0⟩
  · simp only [rowScoped, cells, List.forall_mem_cons]
    grind [CVar.Scoped.of_le, accScoped, bitsScoped]
  · exact ⟨hacc.1.of_le e0, hacc.2.1.of_le e0, b4.1.2.2.2.1, b4.1.2.2.2.2, hnsc.of_le l5⟩
  -- the two equations: the vocabulary, the witnesses' readings at the exit and where each later
  -- witness read them, and the entry cells' readings, the chain's links found in the context
  · simp (disch := assumption) only [ScaleRound.read, ProverState.read, accRead, bitsRead,
      rowStep, b0.2, b1.2, b2.2, b3.2, b4.2, CVar.val_of_le l5 hnsc, hnrd, hb0.2, hb1.2, hb2.2,
      hb3.2, hrd]
    exact rfl
  · simp (disch := assumption) only [ProverState.read, accRead, bitsRead, accStep, rowStep, b4.2,
      CVar.val_of_le l5 hnsc, hnrd, hb0.2, hb1.2, hb2.2, hb3.2, hrd]
    exact rfl

open VarBaseMul in
set_option Elab.async false in
#count_heartbeats in
/-- The ladder's loop, registered: the scan corollary at the round, its transports discharged. -/
@[spec] private def Prover.scaleLoop_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (base : AffinePoint (FVar F)) (init : AffinePoint (FVar F) × FVar F)
    (xs : List (Vector (FVar F) 5)) :=
  Prover.register (Prover.mapAccumM_scan_spec (accScoped base) bitsScoped rowScoped (accRead base)
    bitsRead (fun st r => ScaleRound.read st.env.get r) accStep rowStep
    (scaleRound (c := Prover c) base) (fun _ => True)
    (fun _ _ _ hle h i hi => (h i hi).of_le hle)
    (fun _ _ _ hle h cv hcv => (h cv hcv).of_le hle)
    (fun _ _ x hle h => by
      simp only [bitsRead, ProverState.read, CVar.val_of_le hle (h 0 (by omega)),
        CVar.val_of_le hle (h 1 (by omega)), CVar.val_of_le hle (h 2 (by omega)),
        CVar.val_of_le hle (h 3 (by omega)), CVar.val_of_le hle (h 4 (by omega))])
    (fun _ _ _ hle h => scaleRound_read_of_le hle h)
    (fun st acc x => Prover.scaleRound_spec base st acc x) init xs)

attribute [irreducible] nAccWit bitWit scaleRound

end Snarky.Kimchi

/-! ## EXPERIMENT (Q4): the round under `vcgen` and the cells frame -/

namespace Snarky.Kimchi

open Snarky Lean.Order Std.WP VarBaseMul

variable {F c : Type}

set_option experimental.vcgen true

/-- `bitsScoped` as its five cells. -/
theorem bitsScoped_iff' {st : ProverState F} {b : Vector (FVar F) 5} :
    bitsScoped st b ↔
      b[0].Scoped st ∧ b[1].Scoped st ∧ b[2].Scoped st ∧ b[3].Scoped st ∧ b[4].Scoped st := by
  constructor
  · intro h
    exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega)⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i hi
    match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4

/-- A pair literal's projections, for `vcgen`'s split tuple binders. -/
theorem tuple_fst {α β : Type} (a : α) (b : β) : (a, b).1 = a := rfl

theorem tuple_snd {α β : Type} (a : α) (b : β) : (a, b).2 = b := rfl

/-- `witness (nAccWit …)` under a name of its own. -/
def nAccWitQ [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (nPrev : FVar F) (bs : Vector (FVar F) 5) : CircuitM F c (FVar F) :=
  witness (val := F) (nAccWit nPrev bs)

/-- `witness (bitWit …)` under a name of its own. -/
def bitWitQ [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (t : AffinePoint (FVar F)) (b : FVar F) (acc : AffinePoint (FVar F)) :
    CircuitM F c (FVar F × FVar F × FVar F × FVar F × FVar F) :=
  witness (val := F × F × F × F × F) (bitWit t b acc)

/-- The register advice's law, without `st₀ ≤ s'`. -/
@[spec] theorem Prover.nAccWitQ_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (nPrev : FVar F) (bs : Vector (FVar F) 5) (st₀ : ProverState F) :
    ⦃fun s => s = st₀ ∧ (nPrev.Scoped st₀ ∧ bitsScoped st₀ bs)⦄
    nAccWitQ (c := Prover c) nPrev bs
    ⦃fun r s' => CircuitType.ReadsAs (val := F) s' r (nAccVal (st₀.read nPrev) (st₀.read bs[0])
      (st₀.read bs[1]) (st₀.read bs[2]) (st₀.read bs[3]) (st₀.read bs[4]))⦄ :=
  Prover.std_witness_of_run (nAccWit nPrev bs) (fun st => nPrev.Scoped st ∧ bitsScoped st bs)
    (fun st => nAccVal (st.read nPrev) (st.read bs[0]) (st.read bs[1]) (st.read bs[2])
      (st.read bs[3]) (st.read bs[4]))
    (fun _ h => nAccWit_run h.1 h.2) (fun _ _ => by simp) st₀

/-- The bit step's law, without `st₀ ≤ s'`. -/
@[spec] theorem Prover.bitWitQ_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (t : AffinePoint (FVar F)) (b : FVar F) (acc : AffinePoint (FVar F))
    (st₀ : ProverState F) :
    ⦃fun s => s = st₀ ∧
      (t.x.Scoped st₀ ∧ t.y.Scoped st₀ ∧ acc.x.Scoped st₀ ∧ acc.y.Scoped st₀ ∧ b.Scoped st₀)⦄
    bitWitQ (c := Prover c) t b acc
    ⦃fun r s' => CircuitType.ReadsAs (val := F × F × F × F × F) s' r
      (bitVal (st₀.read t.x) (st₀.read t.y) (st₀.read acc.x) (st₀.read acc.y) (st₀.read b))⦄ :=
  Prover.std_witness_of_run (bitWit t b acc)
    (fun st => t.x.Scoped st ∧ t.y.Scoped st ∧ acc.x.Scoped st ∧ acc.y.Scoped st ∧ b.Scoped st)
    (fun st => bitVal (st.read t.x) (st.read t.y) (st.read acc.x) (st.read acc.y) (st.read b))
    (fun _ h => bitWit_run h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2) (fun _ _ => by simp) st₀

/-- `scaleRound`, verbatim, over the restated leaves. -/
def scaleRoundQ [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (base : AffinePoint (FVar F)) (st : AffinePoint (FVar F) × FVar F)
    (bs : Vector (FVar F) 5) :
    CircuitM F c (ScaleRound F × (AffinePoint (FVar F) × FVar F)) := do
  let nAcc ← nAccWitQ st.2 bs
  let w0 ← bitWitQ base bs[0] st.1
  let a1 : AffinePoint (FVar F) := ⟨w0.2.2.2.1, w0.2.2.2.2⟩
  let w1 ← bitWitQ base bs[1] a1
  let a2 : AffinePoint (FVar F) := ⟨w1.2.2.2.1, w1.2.2.2.2⟩
  let w2 ← bitWitQ base bs[2] a2
  let a3 : AffinePoint (FVar F) := ⟨w2.2.2.2.1, w2.2.2.2.2⟩
  let w3 ← bitWitQ base bs[3] a3
  let a4 : AffinePoint (FVar F) := ⟨w3.2.2.2.1, w3.2.2.2.2⟩
  let w4 ← bitWitQ base bs[4] a4
  let a5 : AffinePoint (FVar F) := ⟨w4.2.2.2.1, w4.2.2.2.2⟩
  pure (({ acc0 := st.1, acc1 := a1, acc2 := a2, acc3 := a3, acc4 := a4, acc5 := a5,
           bit0 := bs[0], bit1 := bs[1], bit2 := bs[2], bit3 := bs[3], bit4 := bs[4],
           slope0 := w0.1, slope1 := w1.1, slope2 := w2.1, slope3 := w3.1,
           slope4 := w4.1,
           nPrev := st.2, nNext := nAcc, base } : ScaleRound F),
         (a5, nAcc))

set_option Elab.async false in
#count_heartbeats in
/-- The round's law without its order conjunct, by `vcgen` under the cells frame. -/
theorem Prover.scaleRoundQ_spec₀ [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (base : AffinePoint (FVar F)) (st : ProverState F)
    (acc : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 5) :
    ⦃fun s => s = st ∧ (accScoped base st acc ∧ bitsScoped st bs ∧ True)⦄
    scaleRoundQ (c := Prover c) base acc bs
    ⦃fun p s' => Prover.ScanStep₀ (accScoped base) rowScoped (accRead base) bitsRead
      (fun st r => ScaleRound.read st.env.get r) accStep rowStep st acc bs p.1 p.2 s'⦄ := by
  refine ⟨fun s hs => ?_⟩
  obtain ⟨rfl, hacc, hbs, -⟩ := hs
  simp only [accScoped, bitsScoped_iff'] at hacc hbs
  unfold scaleRoundQ
  vcgen simplifying_assumptions [CircuitType.ReadsAs.eq_1, CircuitType.scoped_prod',
    CircuitType.reads_prod', CircuitType.scoped_fvar, CircuitType.reads_fvar, tuple_fst,
    tuple_snd]
  all_goals first
    | exact Prover.frames_cellsAt _ _ _
    | ((try simp only [CellsAt, rowScoped, cells, List.forall_mem_cons, List.forall_mem_nil,
          accScoped, ScaleRound.read, accRead, bitsRead, rowStep, accStep, roundVal,
          Kimchi.Gate.VarBaseMul.Witness.mk.injEq, Prod.mk.injEq, and_true] at *)
       grind [bitsScoped_iff', bitVal, nAccVal])

/-- The round's law as written (`Prover.ScanStep`, order conjunct included): the conjunct is a
property of every run. -/
@[spec] theorem Prover.scaleRoundQ_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (base : AffinePoint (FVar F)) (st : ProverState F)
    (acc : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 5) :
    ⦃fun s => s = st ∧ (accScoped base st acc ∧ bitsScoped st bs ∧ True)⦄
    scaleRoundQ (c := Prover c) base acc bs
    ⦃fun p s' => Prover.ScanStep (accScoped base) rowScoped (accRead base) bitsRead
      (fun st r => ScaleRound.read st.env.get r) accStep rowStep st acc bs p.1 p.2 s'⦄ :=
  Prover.std_scanStep _ _ _ _ _ _ _ (Prover.scaleRoundQ_spec₀ base st acc bs)

open Std.Do in
set_option Elab.async false in
#count_heartbeats in
/-- The loop's instance, as written: the scan corollary at the round, the round's law through
the bridge back, the four transports as in the tree. -/
def Prover.scaleLoopQ [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (base : AffinePoint (FVar F)) (init : AffinePoint (FVar F) × FVar F)
    (xs : List (Vector (FVar F) 5)) (st₀ : ProverState F) :=
  Prover.mapAccumM_scan_spec (accScoped base) bitsScoped rowScoped (accRead base)
    bitsRead (fun st r => ScaleRound.read st.env.get r) accStep rowStep
    (scaleRoundQ (c := Prover c) base) (fun _ => True)
    (fun _ _ _ hle h i hi => (h i hi).of_le hle)
    (fun _ _ _ hle h cv hcv => (h cv hcv).of_le hle)
    (fun _ _ x hle h => by
      simp only [bitsRead, ProverState.read, CVar.val_of_le hle (h 0 (by omega)),
        CVar.val_of_le hle (h 1 (by omega)), CVar.val_of_le hle (h 2 (by omega)),
        CVar.val_of_le hle (h 3 (by omega)), CVar.val_of_le hle (h 4 (by omega))])
    (fun _ _ _ hle h => scaleRound_read_of_le hle h)
    (fun st acc x => Prover.do_of_std (Prover.scaleRoundQ_spec base st acc x)) init xs st₀

end Snarky.Kimchi
