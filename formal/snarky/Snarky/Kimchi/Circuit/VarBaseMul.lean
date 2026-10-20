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

/-! ## The ladder

A `ScaleRound` carries all 26 of its cells, outputs included, so the constraint reads each
round on its own. The trace only has to say that every round shares the base, opens where the
previous one closed, and starts at the doubled seed: what `Kimchi.Gate.VarBaseMul.varBaseMul_off`
asks of its run.

The loop emits no row of its own; every row is judged at the one `varBaseMul` constraint
after it. On the honest side that constraint holds by the model's `chain_complete`, since the
rounds read as the model's honest walk. -/

/-- What `varBaseMul` returns: the scalar multiple and the scalar's bits, which
`scaleFast1` and `scaleFast2` pin. -/
structure VarBaseMulResult (n : ℕ) (F : Type) where
  /-- The computed multiple. -/
  g : AffinePoint (FVar F)
  /-- The scalar's `n` witnessed bits, LSB-first. -/
  lsbBits : Vector (FVar F) n

/-- The variable-base scalar multiplication: seal the base, witness the scalar's `n` bits
LSB-first, build `acc = [2]·T` with one `addFast`, walk the low `5 * chunks` bits MSB-first in
5-bit rounds, emit one `varBaseMul` constraint, and pin the final register to the scalar. -/
def varBaseMul [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [ConstraintHolds F c]
    [KimchiSystem F c] (n chunks : ℕ) (base' : AffinePoint (FVar F))
    (scalar : Type1 (FVar F)) : CircuitM F c (VarBaseMulResult n F) := do
  let base ← sealPoint base'
  let lsbBits ← witness (val := Vector F n) (lsbBitsWit n scalar.val)
  let p ← addFast .checkFinite base base
  let msb : List (FVar F) := (lsbBits.toList.take (5 * chunks)).reverse
  let window : ℕ → Vector (FVar F) 5 := fun i =>
    Vector.ofFn fun j => msb.getD (5 * i + j.1) (.const 0)
  let (rounds, fin) ← mapAccumM (scaleRound base)
    (p.p, .const 0) ((List.range chunks).map window)
  addConstraint (KimchiSystem.varBaseMul rounds)
  assertEqual fin.2 scalar.val
  pure ⟨fin.1, lsbBits⟩

namespace VarBaseMul

variable {F c : Type}

/-- A trace, read through `chain_iff`: each round against its row, adjacent rounds linking,
and the ends. -/
private theorem threads_facts {base : AffinePoint (FVar F)}
    {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 5)}
    {rounds : List (ScaleRound F)} (h : Chain (Threads base) st pref rounds fin) :
    List.Forall₂ (RowIn base) pref rounds ∧
      rounds.IsChain (fun y y' => (y'.acc0, y'.nPrev) = (y.acc5, y.nNext)) ∧
      (∀ y ∈ rounds.head?, (y.acc0, y.nPrev) = st) ∧
      (rounds.getLast?.map fun r => (r.acc5, r.nNext)).getD st = fin :=
  (chain_iff (fun r : ScaleRound F => (r.acc0, r.nPrev)) (fun r => (r.acc5, r.nNext))
    (RowIn base) fun _ _ _ _ => Iff.rfl).mp h

/-- Every round of a trace reads the same base. -/
private theorem threads_base {base : AffinePoint (FVar F)} {st fin : AffinePoint (FVar F) × FVar F}
    {pref : List (Vector (FVar F) 5)} {rounds : List (ScaleRound F)}
    (h : Chain (Threads base) st pref rounds fin) : ∀ r ∈ rounds, r.base = base := by
  have hF := (threads_facts h).1
  clear h
  induction hF with
  | nil => simp
  | cons hq _ ih => simpa [hq.1] using ih

/-- A trace's first round opens at the seed accumulators. -/
private theorem threads_head {base : AffinePoint (FVar F)} {st fin : AffinePoint (FVar F) × FVar F}
    {pref : List (Vector (FVar F) 5)} {r₀ : ScaleRound F} {rs : List (ScaleRound F)}
    (h : Chain (Threads base) st pref (r₀ :: rs) fin) : r₀.acc0 = st.1 ∧ r₀.nPrev = st.2 :=
  Prod.ext_iff.mp ((threads_facts h).2.2.1 r₀ (by simp))

/-- A trace's rounds link: each opens where the previous closed. -/
private theorem threads_link {base : AffinePoint (FVar F)} {st fin : AffinePoint (FVar F) × FVar F}
    {pref : List (Vector (FVar F) 5)} {rounds : List (ScaleRound F)}
    (h : Chain (Threads base) st pref rounds fin) :
    rounds.IsChain fun a b => b.acc0 = a.acc5 ∧ b.nPrev = a.nNext :=
  (threads_facts h).2.1.imp fun _ _ e => Prod.ext_iff.mp e

/-- A trace closes at its last round's outputs. -/
private theorem threads_last {base : AffinePoint (FVar F)} {st fin : AffinePoint (FVar F) × FVar F}
    {pref : List (Vector (FVar F) 5)} {r₀ : ScaleRound F} {rs : List (ScaleRound F)}
    (h : Chain (Threads base) st pref (r₀ :: rs) fin) :
    ((r₀ :: rs).getLast (by simp)).acc5 = fin.1
      ∧ ((r₀ :: rs).getLast (by simp)).nNext = fin.2 := by
  have hL := (threads_facts h).2.2.2
  simp only [List.getLast?_eq_some_getLast (l := r₀ :: rs) (by simp), Option.map_some,
    Option.getD_some] at hL
  exact Prod.ext_iff.mp hL

/-- A trace's rounds are as many as the rows it traversed. -/
private theorem threads_length {base : AffinePoint (FVar F)}
    {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 5)}
    {rounds : List (ScaleRound F)} (h : Chain (Threads base) st pref rounds fin) :
    rounds.length = pref.length :=
  (threads_facts h).1.length_eq.symm

/-- A trace's rounds, read at a valuation, link as the model's rows. -/
private theorem threads_link_read [Field F] [DecidableEq F] {V : Valuation F}
    {base : AffinePoint (FVar F)} {st fin : AffinePoint (FVar F) × FVar F}
    {pref : List (Vector (FVar F) 5)} {rounds : List (ScaleRound F)}
    (h : Chain (Threads base) st pref rounds fin) :
    (rounds.map (ScaleRound.read V)).IsChain
      fun a b => (b.x0 = a.x5 ∧ b.y0 = a.y5) ∧ b.n = a.nPrime := by
  refine (List.isChain_map _).mpr ?_
  refine (threads_link h).imp fun a b hab => ?_
  exact ⟨⟨congrArg (·.val V) (congrArg AffinePoint.x hab.1),
    congrArg (·.val V) (congrArg AffinePoint.y hab.1)⟩,
    congrArg (·.val V) hab.2⟩

/-- Flattening a list's five-wide windows recovers the list. -/
private theorem flatMap_window {α : Type} (dflt : α) (c : ℕ) (l : List α)
    (hl : l.length = 5 * c) :
    (List.range c).flatMap (fun i =>
      [l.getD (5 * i) dflt, l.getD (5 * i + 1) dflt, l.getD (5 * i + 2) dflt,
       l.getD (5 * i + 3) dflt, l.getD (5 * i + 4) dflt]) = l := by
  rw [Kimchi.Gate.VarBaseMul.flatMap_range_window (fun i => l.getD i dflt) c]
  refine List.ext_getElem (by simp [hl]) (fun i h1 h2 => ?_)
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa [hl] using h1)]

/-- The bit stream a round list carries, MSB-first: the rounds' five bits, read and
concatenated. -/
private def roundBits [Field F] (V : Valuation F) (rounds : List (ScaleRound F)) : List F :=
  rounds.flatMap fun r =>
    [r.bit0.val V, r.bit1.val V, r.bit2.val V, r.bit3.val V, r.bit4.val V]

/-- Flattening a list's five-wide windows, read entrywise, recovers the readings. -/
private theorem flatMap_window_map {α β : Type} (f : α → β) (dflt : α) (c : ℕ)
    (l : List α) (hl : l.length = 5 * c) :
    (List.range c).flatMap (fun i =>
      [f (l.getD (5 * i) dflt), f (l.getD (5 * i + 1) dflt), f (l.getD (5 * i + 2) dflt),
       f (l.getD (5 * i + 3) dflt), f (l.getD (5 * i + 4) dflt)]) = l.map f := by
  rw [show (fun i => [f (l.getD (5 * i) dflt), f (l.getD (5 * i + 1) dflt),
        f (l.getD (5 * i + 2) dflt), f (l.getD (5 * i + 3) dflt),
        f (l.getD (5 * i + 4) dflt)])
      = (fun i => ([l.getD (5 * i) dflt, l.getD (5 * i + 1) dflt, l.getD (5 * i + 2) dflt,
        l.getD (5 * i + 3) dflt, l.getD (5 * i + 4) dflt]).map f) from rfl,
    ← List.map_flatMap, flatMap_window dflt c l hl]

/-- A trace's rounds carry the bits of the rows it traversed. -/
private theorem threads_rows [Field F] {base : AffinePoint (FVar F)} {V : Valuation F}
    {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 5)}
    {rounds : List (ScaleRound F)} (h : Chain (Threads base) st pref rounds fin) :
    roundBits V rounds
      = pref.flatMap fun w => [w[0].val V, w[1].val V, w[2].val V, w[3].val V, w[4].val V] := by
  have hF := (threads_facts h).1
  clear h
  induction hF with
  | nil => rfl
  | cons hq _ ih =>
    obtain ⟨-, hb0, hb1, hb2, hb3, hb4⟩ := hq
    rw [roundBits, List.flatMap_cons, ← roundBits, ih, List.flatMap_cons, hb0, hb1, hb2, hb3,
      hb4]

open Kimchi.Gate.VarBaseMul (runBits bitsRegister bitsVal accX accY accN gateLadder) in
/-- The trace's scalar side, for any base: the rounds' bits are boolean, `5` per round, and the
final register is their value (`chain_accN`). Only the decomposition and booleanity rows are
read. -/
private theorem run_sound_scalar [Field F] [DecidableEq F] (V : Valuation F)
    {base P0 : AffinePoint (FVar F)} {pref : List (Vector (FVar F) 5)}
    {rounds : List (ScaleRound F)} {fin : AffinePoint (FVar F) × FVar F}
    (hthr : Chain (Threads base) (P0, .const 0) pref rounds fin)
    (hpay : ∀ r ∈ rounds, Kimchi.Gate.VarBaseMul.Holds (ScaleRound.read V r)) :
    (∀ b ∈ roundBits V rounds, b = 0 ∨ b = 1) ∧
      (roundBits V rounds).length = 5 * pref.length ∧
      fin.2.val V = bitsRegister (roundBits V rounds) := by
  match hround : rounds, hthr with
  | [], hthr' =>
    obtain ⟨rfl, rfl⟩ := Chain.of_nil_out hthr'
    exact ⟨by simp [roundBits], by simp [roundBits], by simp [roundBits, bitsRegister, CVar.val]⟩
  | r₀ :: rs, hthr' =>
    subst hround
    set l := (r₀ :: rs).map (ScaleRound.read V) with hl
    set dflt := ScaleRound.read V r₀ with hdflt
    set g : ℕ → Kimchi.Gate.VarBaseMul.Witness F := fun i => l.getD i dflt with hg
    have hlink : l.IsChain fun a b => (b.x0 = a.x5 ∧ b.y0 = a.y5) ∧ b.n = a.nPrime :=
      threads_link_read (V := V) hthr'
    have hgH : ∀ i, i < l.length → Kimchi.Gate.VarBaseMul.Holds (g i) := by
      intro i hi
      show Kimchi.Gate.VarBaseMul.Holds (l.getD i dflt)
      rw [List.getD_eq_getElem _ _ hi]
      have hmem : l[i] ∈ (r₀ :: rs).map (ScaleRound.read V) := hl ▸ List.getElem_mem hi
      obtain ⟨r, hr, hrw⟩ := List.mem_map.mp hmem
      rw [← hrw]
      exact hpay r hr
    have hgN : ∀ i, i + 1 < l.length → (g (i + 1)).n = (g i).nPrime := by
      intro i hi
      show (l.getD (i + 1) dflt).n = (l.getD i dflt).nPrime
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)]
      exact (hlink.getElem i hi).2
    -- the run's bit stream is the rounds'
    have hbits : runBits g l.length = roundBits V (r₀ :: rs) := by
      rw [hg, Kimchi.Gate.VarBaseMul.runBits_getD, hl, roundBits, List.flatMap_map]
      rfl
    obtain ⟨-, -, han⟩ :=
      Kimchi.Gate.VarBaseMul.acc_getD_length l (by simp [hl]) dflt
    obtain ⟨-, hlastN⟩ := VarBaseMul.threads_last hthr'
    have hlastl : l.getLast (by simp [hl])
        = ScaleRound.read V ((r₀ :: rs).getLast (by simp)) := List.getLast_map _
    have hfinn : accN g l.length = fin.2.val V := by
      rw [hg, han, hlastl]
      show ((r₀ :: rs).getLast (by simp)).nNext.val V = _
      rw [hlastN]
    -- the register, from the run's own fold
    have hzero : accN g 0 = 0 := by
      obtain ⟨-, hn0⟩ := VarBaseMul.threads_head hthr'
      show (l.getD 0 dflt).n = 0
      rw [hl]
      show r₀.nPrev.val V = 0
      rw [hn0]
      simp [CVar.val]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hbits]
      exact Kimchi.Gate.VarBaseMul.runBits_bool l.length g hgH
    · rw [← VarBaseMul.threads_length hthr', roundBits, List.length_flatMap]
      simp
      omega
    · rw [← hfinn, Kimchi.Gate.VarBaseMul.chain_accN l.length g hgH hgN, hzero, mul_zero,
        zero_add, hbits]

open Kimchi.Gate.VarBaseMul (runBits bitsRegister bitsVal accX accY accN gateLadder) in
/-- A satisfied trace from the doubled seed is one of the model's runs (`isChain_getD`): under
the regime the result is the base times its bits' Type1 decode (`varBaseMul_off`). The bits
themselves are `run_sound_scalar`'s. -/
private theorem run_sound [Field F] [DecidableEq F] (d : HasCurve F) (V : Valuation F)
    {base P0 : AffinePoint (FVar F)} {pref : List (Vector (FVar F) 5)}
    {rounds : List (ScaleRound F)} {fin : AffinePoint (FVar F) × FVar F}
    (T : d.W.Point)
    (hthr : Chain (Threads base) (P0, .const 0) pref rounds fin)
    (hpay : ∀ r ∈ rounds, Kimchi.Gate.VarBaseMul.Holds (ScaleRound.read V r))
    (hT : OnCurveAt d.W V base T)
    (hP0 : OnCurveAt d.W V P0 ((2 : ℤ) • T)) :
    ∀ _ : d.LadderRegime (5 * pref.length)
        (Pasta.Shifted.unshiftType1 (5 * pref.length) (bitsVal (roundBits V rounds))),
      OnCurveAt d.W V fin.1
        ((Pasta.Shifted.unshiftType1 (5 * pref.length) (bitsVal (roundBits V rounds))) • T) := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  match hround : rounds, hthr with
  | [], hthr' =>
    obtain ⟨rfl, rfl⟩ := Chain.of_nil_out hthr'
    intro _
    simpa [roundBits, bitsVal, Pasta.Shifted.unshiftType1] using hP0
  | r₀ :: rs, hthr' =>
    subst hround
    set l := (r₀ :: rs).map (ScaleRound.read V) with hl
    set dflt := ScaleRound.read V r₀ with hdflt
    set g : ℕ → Kimchi.Gate.VarBaseMul.Witness F := fun i => l.getD i dflt with hg
    have hlen : l.length = pref.length := by
      rw [hl, List.length_map]
      exact VarBaseMul.threads_length hthr'
    have hbaseAll : ∀ w ∈ dflt :: l, Kimchi.Gate.AddComplete.IsPoint d.W w.xT w.yT T := by
      intro w hw
      have hmem : ∃ r ∈ (r₀ :: rs), w = ScaleRound.read V r := by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact ⟨r₀, by simp, rfl⟩
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (hl ▸ hw)
          exact ⟨r, hr, rfl⟩
      obtain ⟨r, hr, rfl⟩ := hmem
      show Kimchi.Gate.AddComplete.IsPoint d.W (r.base.x.val V) (r.base.y.val V) T
      rw [VarBaseMul.threads_base hthr' r hr]
      exact hT
    obtain ⟨hgH, hgB, hgL, -⟩ :=
      Kimchi.Gate.VarBaseMul.isChain_getD d.W T l dflt
        (fun w hw => by
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (hl ▸ hw)
          exact hpay r hr)
        hbaseAll (threads_link_read (V := V) hthr')
    have hgI : Kimchi.Gate.AddComplete.IsPoint d.W (g 0).x0 (g 0).y0 ((2 : ℤ) • T) := by
      obtain ⟨hp0, -⟩ := VarBaseMul.threads_head hthr'
      show Kimchi.Gate.AddComplete.IsPoint d.W (r₀.acc0.x.val V) (r₀.acc0.y.val V) _
      rw [hp0]
      exact hP0
    -- the run's bit stream is the rounds'
    have hbits : runBits g l.length = roundBits V (r₀ :: rs) := by
      rw [hg, Kimchi.Gate.VarBaseMul.runBits_getD, hl, roundBits, List.flatMap_map]
      rfl
    -- the run closes where the trace does
    obtain ⟨hax, hay, -⟩ :=
      Kimchi.Gate.VarBaseMul.acc_getD_length l (by simp [hl]) dflt
    obtain ⟨hlast5, -⟩ := VarBaseMul.threads_last hthr'
    have hlastl : l.getLast (by simp [hl])
        = ScaleRound.read V ((r₀ :: rs).getLast (by simp)) := List.getLast_map _
    have hfinx : accX g l.length = fin.1.x.val V := by
      rw [hg, hax, hlastl]
      show ((r₀ :: rs).getLast (by simp)).acc5.x.val V = _
      rw [hlast5]
    have hfiny : accY g l.length = fin.1.y.val V := by
      rw [hg, hay, hlastl]
      show ((r₀ :: rs).getLast (by simp)).acc5.y.val V = _
      rw [hlast5]
    intro hregime
    rw [← hlen] at hregime ⊢
    simp only [HasCurve.LadderRegime] at hregime
    have hs : gateLadder g (5 * l.length)
        = Pasta.Shifted.unshiftType1 (5 * l.length)
          (bitsVal (roundBits V (r₀ :: rs))) := by
      rw [Pasta.Shifted.unshiftType1]
      rw [Kimchi.Gate.VarBaseMul.gateLadder_eq_register,
        Kimchi.Gate.VarBaseMul.gateRegister_eq_bitsVal, hbits]
    obtain ⟨hfin', hpt, -⟩ :=
      Kimchi.Gate.VarBaseMul.varBaseMul_off d.W l.length g T
        (gateLadder g (5 * l.length)) hgH hgB hgL hgI d.two_ne d.odd rfl
        (by
          rw [hs]
          rcases hregime with h | h
          · exact Or.inl h
          · exact Or.inr h)
    have hns : d.W.Nonsingular (fin.1.x.val V) (fin.1.y.val V) := by
      rw [← hfinx, ← hfiny]
      exact hfin'
    refine ⟨hns, ?_⟩
    rw [← hs, ← hpt]
    congr 1

/-- The returned bits, read off a satisfied trace: the first `5 * chunks` cells are the bits
`bs` of the rounds (read MSB-first through the windows), whose LSB-first value is the rounds'
`bitsVal` and, the final register reading as their `bitsRegister` (`hreg`), its value. -/
private theorem lsbBits_of_run [Field F] [DecidableEq F] (V : Valuation F) {n chunks : ℕ}
    (hn : 5 * chunks ≤ n) {bits : Vector (FVar F) n} {base P0 : AffinePoint (FVar F)}
    {loop : List (ScaleRound F) × (AffinePoint (FVar F) × FVar F)}
    (hchain : Chain (Threads base) (P0, .const 0)
      ((List.range chunks).map fun i => Vector.ofFn fun j : Fin 5 =>
        ((bits.toList.take (5 * chunks)).reverse).getD (5 * i + j.1) (.const 0))
      loop.1 loop.2)
    (hbool : ∀ b ∈ roundBits V loop.1, b = 0 ∨ b = 1)
    (hreg : loop.2.2.val V = Kimchi.Gate.VarBaseMul.bitsRegister (roundBits V loop.1)) :
    ∃ bs : Vector Bool (5 * chunks),
      (∀ i (hi : i < 5 * chunks), (bits[i]'(Nat.lt_of_lt_of_le hi hn)).val V = bit bs[i]) ∧
      Kimchi.Gate.VarBaseMul.bitsVal (roundBits V loop.1) = (Kimchi.natLsbVal bs.toList : ℤ) ∧
      loop.2.2.val V = ((Kimchi.natLsbVal bs.toList : ℕ) : F) := by
  -- the rounds' bits are the windows', and the windows flatten to the reversed prefix
  have hmsb : ((bits.toList.take (5 * chunks)).reverse).length = 5 * chunks := by
    simp only [List.length_reverse, List.length_take, Vector.length_toList]
    omega
  have hbits : roundBits V loop.1
      = (((bits.toList.take (5 * chunks)).reverse).map (·.val V)) := by
    rw [threads_rows hchain, List.flatMap_map]
    exact flatMap_window_map (·.val V) (CVar.const 0) chunks _ hmsb
  -- the cells, decided as bits: the gate's rows make each one `0` or `1`
  have hcell : ∀ i (hi : i < 5 * chunks),
      (bits[i]'(Nat.lt_of_lt_of_le hi hn)).val V = 0 ∨
        (bits[i]'(Nat.lt_of_lt_of_le hi hn)).val V = 1 := by
    intro i hi
    refine hbool _ ?_
    rw [hbits]
    refine List.mem_map.mpr ⟨bits[i]'(Nat.lt_of_lt_of_le hi hn), ?_, rfl⟩
    rw [List.mem_reverse]
    have hidx : (bits.toList.take (5 * chunks))[i]'(by simp; omega)
        = bits[i]'(Nat.lt_of_lt_of_le hi hn) := by
      simp [List.getElem_take]
    exact hidx ▸ List.getElem_mem _
  set bs : Vector Bool (5 * chunks) :=
    Vector.ofFn fun i : Fin (5 * chunks) =>
      decide ((bits[i.1]'(Nat.lt_of_lt_of_le i.isLt hn)).val V = 1) with hbsdef
  have hread : ∀ i (hi : i < 5 * chunks),
      (bits[i]'(Nat.lt_of_lt_of_le hi hn)).val V = bit bs[i] := by
    intro i hi
    simp only [hbsdef, Vector.getElem_ofFn]
    rcases hcell i hi with h0 | h1
    · simp [h0, bit]
    · simp [h1, bit]
  have hdec : ((roundBits V loop.1).map fun b => decide (b = 1)).reverse = bs.toList := by
    rw [hbits, List.map_map, ← List.map_reverse, List.reverse_reverse]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, Vector.length_toList, hbsdef,
        Vector.length_toList]
      omega
    · intro i h1 _
      have hi : i < 5 * chunks := by simp only [List.length_map, List.length_take,
        Vector.length_toList, lt_min_iff] at h1; omega
      simp only [hbsdef, Vector.getElem_toList, Vector.getElem_ofFn, List.getElem_map,
        List.getElem_take, Function.comp_apply, Vector.getElem_toList]
  have hbn : Kimchi.Gate.VarBaseMul.bitsVal (roundBits V loop.1)
      = (Kimchi.natLsbVal bs.toList : ℤ) := by
    rw [Kimchi.Gate.VarBaseMul.bitsVal_eq_natLsbVal, hdec]
  refine ⟨bs, hread, hbn, ?_⟩
  rw [hreg, Kimchi.Gate.VarBaseMul.bitsRegister_eq_cast (roundBits V loop.1) hbool, hbn]
  push_cast
  ring

end VarBaseMul

open Std.Do WeierstrassCurve.Affine in
/-- **Soundness.** Under any satisfying valuation the first `5 * chunks` returned bits read
as bits whose LSB-first value the scalar reads as, and, under the ladder's regime, the result
is the base times that value's Type1 decode. -/
theorem varBaseMul_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (d : HasCurve F) (n chunks : ℕ) (hn : 5 * chunks ≤ n)
    (base : AffinePoint (FVar F)) (scalar : Type1 (FVar F)) :
    ⦃⌜True⌝⦄
    varBaseMul (c := Builder V (KimchiConstraint F)) n chunks base scalar
    ⦃⇓ r _ => ⌜∀ T : d.W.Point, OnCurveAt d.W V base T →
      ∃ bs : Vector Bool (5 * chunks),
        (∀ i (hi : i < 5 * chunks),
          (r.lsbBits[i]'(Nat.lt_of_lt_of_le hi hn)).val V = bit bs[i]) ∧
        scalar.val.val V = ((Kimchi.natLsbVal bs.toList : ℕ) : F) ∧
        ∀ _ : d.LadderRegime (5 * chunks)
            (Pasta.Shifted.unshiftType1 (5 * chunks) (Kimchi.natLsbVal bs.toList : ℤ)),
          OnCurveAt d.W V r.g
            ((Pasta.Shifted.unshiftType1 (5 * chunks)
              (Kimchi.natLsbVal bs.toList : ℤ)) • T)⌝⦄ := by
  have hloop := fun (b : AffinePoint (FVar F)) =>
    mapAccumM_spec (V := V) (c := KimchiConstraint F) (scaleRound b) (VarBaseMul.Threads b)
      (fun st bs => VarBaseMul.scaleRound_spec b st bs)
  unfold varBaseMul
  mvcgen [hloop]
  case vc1.W => exact d.W
  case vc2.ha => exact d.short
  case vc3.htwo => exact d.two_ne
  rename_i _ sealed _ hseal bits _ _ p _ loop _ hchain _ _ hpay _ _ hpin hadd
  intro T hT
  obtain ⟨hTns, hTeq⟩ := hT
  have hTs : OnCurveAt d.W V sealed T := by
    show ∃ h : d.W.Nonsingular (sealed.x.val V) (sealed.y.val V), _
    rw [hseal.1, hseal.2]
    exact ⟨hTns, hTeq⟩
  have h2T : T + T ≠ 0 :=
    d.two_torsion_free T (by rw [hTeq]; exact Point.some_ne_zero _)
  have hP0 : OnCurveAt d.W V p.p ((2 : ℤ) • T) := by
    rw [two_zsmul]
    rcases hadd.2 T T hTs hTs h2T with ⟨hinf, -⟩ | ⟨-, h3⟩
    · exact absurd (hadd.1.symm.trans hinf) (by norm_num)
    · exact h3
  obtain ⟨hbool, -, hreg⟩ := VarBaseMul.run_sound_scalar V hchain hpay
  have hpoint := VarBaseMul.run_sound d V T hchain hpay hTs hP0
  obtain ⟨bs, hread, hbn, hval⟩ := VarBaseMul.lsbBits_of_run V hn hchain hbool hreg
  have hpreflen : ((List.range chunks).map fun i =>
      (Vector.ofFn fun j : Fin 5 =>
        ((bits.toList.take (5 * chunks)).reverse).getD (5 * i + j.1)
          (CVar.const 0))).length = chunks := by simp
  refine ⟨bs, hread, by rw [← hpin]; exact hval, ?_⟩
  rw [hpreflen, hbn] at hpoint
  exact hpoint

open Std.Do in
/-- **Soundness, the scalar side.** For any base, under any satisfying valuation the first
`5 * chunks` returned bits read as bits whose LSB-first value the scalar reads as: the
decomposition and booleanity rows never read the base. -/
theorem varBaseMul_spec_scalar {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (n chunks : ℕ) (hn : 5 * chunks ≤ n) (base : AffinePoint (FVar F))
    (scalar : Type1 (FVar F)) :
    ⦃⌜True⌝⦄
    varBaseMul (c := Builder V (KimchiConstraint F)) n chunks base scalar
    ⦃⇓ r _ => ⌜∃ bs : Vector Bool (5 * chunks),
        (∀ i (hi : i < 5 * chunks),
          (r.lsbBits[i]'(Nat.lt_of_lt_of_le hi hn)).val V = bit bs[i]) ∧
        scalar.val.val V = ((Kimchi.natLsbVal bs.toList : ℕ) : F)⌝⦄ := by
  have hloop := fun (b : AffinePoint (FVar F)) =>
    mapAccumM_spec (V := V) (c := KimchiConstraint F) (scaleRound b) (VarBaseMul.Threads b)
      (fun st bs => VarBaseMul.scaleRound_spec b st bs)
  have hadd := fun (a b : AffinePoint (FVar F)) =>
    builder_spec_true (addFast (c := Builder V (KimchiConstraint F)) .checkFinite a b)
  unfold varBaseMul
  mvcgen [hloop, hadd, -Snarky.Kimchi.addFast_spec]
  rename_i _ _ _ _ bits _ _ _ _ loop _ hchain _ _ hpay _ _ hpin
  obtain ⟨hbool, -, hreg⟩ := VarBaseMul.run_sound_scalar V hchain hpay
  obtain ⟨bs, hread, -, hval⟩ := VarBaseMul.lsbBits_of_run V hn hchain hbool hreg
  exact ⟨bs, hread, by rw [← hpin]; exact hval⟩

/-! ### The ladder at the prover's reading

`varBaseMul`'s law. The loop is the registered scan instance, whose rows are `rowStep` along
the prefix folds from the doubled seed; `scan_rows` and `scan_fold` read those folds as the
model's honest walk (`Kimchi.Gate.VarBaseMul.chainBuild`), `walk_facts` is the model's side
(the rows hold by `chain_complete`, the final register is the scalar by `chain_accN`, the final
accumulator names the multiple by `varBaseMul_off`), and `exit_facts` states the exit in the
law's vocabulary, so each of the law's conditions is one projection of it. -/

namespace VarBaseMul

open Kimchi.Gate.VarBaseMul (chainBuild accX accY accN)

/-- The scalar's `n` bits LSB-first as field values: `lsbBitsWit`'s value. -/
private def lsbBitsVal [Field F] [ToNat F] (n : ℕ) (v : F) : Vector F n :=
  Vector.ofFn fun i => if (ToNat.toNat v).testBit i.1 then 1 else 0

private theorem lsbBitsWit_run [Field F] [ToNat F] {s : ProverState F} {n : ℕ} {scalar : FVar F}
    (h : scalar.Scoped s) :
    (lsbBitsWit n scalar).run s.env = .ok (lsbBitsVal n (scalar.val s.env.get)) := by
  simp [lsbBitsWit, lsbBitsVal, AsProver.readCVar_run h]

/-- The bits bundle, as the boolean vector the ladder returns. -/
private theorem reads_bits [Field F] [DecidableEq F] [ToNat F] {n : ℕ} {st : ProverState F}
    {bits : Vector (FVar F) n} {v : F}
    (h : CircuitType.ReadsAs (val := Vector F n) st bits (lsbBitsVal n v)) :
    CircuitType.ReadsAs (val := Vector Bool n) st (mapVec BoolVar.unchecked bits)
      (unpackPure v n) := by
  refine ⟨CircuitType.scoped_vector.mpr fun i hi => ?_,
    CircuitType.reads_vector.mpr fun i hi => ?_⟩
  · rw [getElem_mapVec]
    exact CircuitType.scoped_boolVar.mpr
      (CircuitType.scoped_fvar.mp (CircuitType.scoped_vector.mp h.1 i hi))
  · rw [getElem_mapVec]
    refine CircuitType.reads_boolVar.mpr ?_
    have hr := CircuitType.reads_fvar.mp (CircuitType.reads_vector.mp h.2 i hi)
    simp only [lsbBitsVal, Vector.getElem_ofFn] at hr
    show (bits[i]'hi).val st.env.get = _
    rw [hr]
    simp [bit]

/-- The rounds' bit stream, MSB-first off the scalar's bits: entry `k` is bit
`5 · chunks − 1 − k`. -/
private def bsOf [Field F] [ToNat F] (v : F) (chunks k : ℕ) : F :=
  if (ToNat.toNat v).testBit (5 * chunks - 1 - k) then 1 else 0

/-- A window of five entries off a stream, as a round's bits reading. -/
private def bitsAt (bs : ℕ → F) (i : ℕ) : F × F × F × F × F :=
  (bs (5 * i), bs (5 * i + 1), bs (5 * i + 2), bs (5 * i + 3), bs (5 * i + 4))

/-- The reversed prefix's entries are the bits, reflected. -/
private theorem msb_entry [Zero F] {n chunks : ℕ} (hn : 5 * chunks ≤ n) (bits : Vector (FVar F) n)
    (k : ℕ) (hk : k < 5 * chunks) :
    ((bits.toList.take (5 * chunks)).reverse).getD k (CVar.const 0)
      = bits[5 * chunks - 1 - k]'(by omega) := by
  have hlen : ((bits.toList.take (5 * chunks)).reverse).length = 5 * chunks := by
    simp only [List.length_reverse, List.length_take, Vector.length_toList]
    omega
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hk)]
  simp only [List.getElem_reverse, List.getElem_take, Vector.getElem_toList, List.length_take,
    Vector.length_toList]
  congr 1
  omega

/-- A window is in scope and reads the stream's window, off the bits' reading. -/
private theorem window_facts [Field F] [DecidableEq F] [ToNat F] {n chunks : ℕ}
    (hn : 5 * chunks ≤ n) {st : ProverState F} {bits : Vector (FVar F) n} {v : F}
    (h : CircuitType.ReadsAs (val := Vector F n) st bits (lsbBitsVal n v)) (i : ℕ)
    (hi : i < chunks) :
    bitsScoped st (Vector.ofFn fun j : Fin 5 =>
        ((bits.toList.take (5 * chunks)).reverse).getD (5 * i + j.1) (CVar.const 0)) ∧
      bitsRead st (Vector.ofFn fun j : Fin 5 =>
        ((bits.toList.take (5 * chunks)).reverse).getD (5 * i + j.1) (CVar.const 0))
        = bitsAt (bsOf v chunks) i := by
  have hsc := CircuitType.scoped_vector.mp h.1
  have hrd : ∀ (m : ℕ) (hm : m < n), (bits[m]'hm).val st.env.get =
      if (ToNat.toNat v).testBit m then 1 else 0 := fun m hm => by
    have := CircuitType.reads_fvar.mp (CircuitType.reads_vector.mp h.2 m hm)
    simpa only [lsbBitsVal, Vector.getElem_ofFn] using this
  refine ⟨fun j hj => ?_, ?_⟩
  · simp only [Vector.getElem_ofFn]
    rw [msb_entry hn bits (5 * i + j) (by omega)]
    exact CircuitType.scoped_fvar.mp (hsc _ _)
  · simp only [bitsRead, bitsAt, bsOf, ProverState.read, Vector.getElem_ofFn, Nat.add_zero]
    rw [msb_entry hn bits (5 * i) (by omega), msb_entry hn bits (5 * i + 1) (by omega),
      msb_entry hn bits (5 * i + 2) (by omega), msb_entry hn bits (5 * i + 3) (by omega),
      msb_entry hn bits (5 * i + 4) (by omega), hrd, hrd, hrd, hrd, hrd]

/-- Along windows reading a stream, each `rowStep` at the prefix fold is the walk's row. -/
private theorem scan_rows [Field F] (xT yT : F) :
    ∀ (ws : List (F × F × F × F × F)) (x0 y0 n0 : F) (bs : ℕ → F)
      (d : (F × F) × (F × F) × F),
      (∀ (i : ℕ) (hi : i < ws.length), ws[i] = bitsAt bs i) →
      ∀ (i : ℕ) (hi : i < ws.length),
        rowStep ((ws.scanl accStep ((xT, yT), (x0, y0), n0)).getD i d) ws[i]
          = chainBuild xT yT x0 y0 n0 bs i
  | [], _, _, _, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | w :: ws, x0, y0, n0, bs, d, hws, i, hi => by
    have hw : w = bitsAt bs 0 := hws 0 (by simp)
    have hstep : accStep ((xT, yT), (x0, y0), n0) w
        = ((xT, yT), ((chainBuild xT yT x0 y0 n0 bs 0).x5, (chainBuild xT yT x0 y0 n0 bs 0).y5),
            (chainBuild xT yT x0 y0 n0 bs 0).nPrime) := by
      rw [hw]
      simp only [accStep, rowStep, bitsAt]
      rw [roundVal_eq_build]
      simp only [chainBuild, Nat.mul_zero, Nat.zero_add]
    have hws' : ∀ (k : ℕ) (hk : k < ws.length), ws[k] = bitsAt (fun m => bs (m + 5)) k := by
      intro k hk
      have h := hws (k + 1) (by simpa using hk)
      simp only [List.getElem_cons_succ] at h
      rw [h]
      simp only [bitsAt]
      ring_nf
    cases i with
    | zero =>
      simp only [List.scanl_cons, List.getD_cons_zero, List.getElem_cons_zero]
      rw [hw]
      simp only [rowStep, bitsAt]
      rw [roundVal_eq_build]
      simp only [chainBuild, Nat.mul_zero, Nat.zero_add]
    | succ j =>
      have hj : j < ws.length := by simpa using hi
      simp only [List.scanl_cons, List.getD_cons_succ, List.getElem_cons_succ]
      rw [hstep, scan_rows xT yT ws _ _ _ (fun m => bs (m + 5)) d hws' j hj,
        Kimchi.Gate.VarBaseMul.chainBuild_shift]

/-- The walk from row `0`'s outputs, `m` rows on, closes where the walk closes `m + 1` rows
on. -/
private theorem acc_shift [Field F] (xT yT x0 y0 n0 : F) (bs : ℕ → F) (m : ℕ) :
    ((accX (chainBuild xT yT (chainBuild xT yT x0 y0 n0 bs 0).x5
          (chainBuild xT yT x0 y0 n0 bs 0).y5 (chainBuild xT yT x0 y0 n0 bs 0).nPrime
          (fun k => bs (k + 5))) m,
        accY (chainBuild xT yT (chainBuild xT yT x0 y0 n0 bs 0).x5
          (chainBuild xT yT x0 y0 n0 bs 0).y5 (chainBuild xT yT x0 y0 n0 bs 0).nPrime
          (fun k => bs (k + 5))) m),
      accN (chainBuild xT yT (chainBuild xT yT x0 y0 n0 bs 0).x5
          (chainBuild xT yT x0 y0 n0 bs 0).y5 (chainBuild xT yT x0 y0 n0 bs 0).nPrime
          (fun k => bs (k + 5))) m)
      = ((accX (chainBuild xT yT x0 y0 n0 bs) (m + 1), accY (chainBuild xT yT x0 y0 n0 bs) (m + 1)),
          accN (chainBuild xT yT x0 y0 n0 bs) (m + 1)) := by
  cases m with
  | zero => rfl
  | succ k =>
    simp only [accX, accY, accN]
    rw [Kimchi.Gate.VarBaseMul.chainBuild_shift xT yT x0 y0 n0 bs k]

/-- Along windows reading a stream, the fold from the seed is the walk's final accumulator. -/
private theorem scan_fold [Field F] (xT yT : F) :
    ∀ (ws : List (F × F × F × F × F)) (x0 y0 n0 : F) (bs : ℕ → F),
      (∀ (i : ℕ) (hi : i < ws.length), ws[i] = bitsAt bs i) →
      ws.foldl accStep ((xT, yT), (x0, y0), n0)
        = ((xT, yT), (accX (chainBuild xT yT x0 y0 n0 bs) ws.length,
            accY (chainBuild xT yT x0 y0 n0 bs) ws.length),
          accN (chainBuild xT yT x0 y0 n0 bs) ws.length)
  | [], _, _, _, _, _ => rfl
  | w :: ws, x0, y0, n0, bs, hws => by
    have hw : w = bitsAt bs 0 := hws 0 (by simp)
    have hstep : accStep ((xT, yT), (x0, y0), n0) w
        = ((xT, yT), ((chainBuild xT yT x0 y0 n0 bs 0).x5, (chainBuild xT yT x0 y0 n0 bs 0).y5),
            (chainBuild xT yT x0 y0 n0 bs 0).nPrime) := by
      rw [hw]
      simp only [accStep, rowStep, bitsAt]
      rw [roundVal_eq_build]
      simp only [chainBuild, Nat.mul_zero, Nat.zero_add]
    have hws' : ∀ (k : ℕ) (hk : k < ws.length), ws[k] = bitsAt (fun m => bs (m + 5)) k := by
      intro k hk
      have h := hws (k + 1) (by simpa using hk)
      simp only [List.getElem_cons_succ] at h
      rw [h]
      simp only [bitsAt]
      ring_nf
    rw [List.foldl_cons, hstep, scan_fold xT yT ws _ _ _ (fun m => bs (m + 5)) hws',
      List.length_cons, acc_shift]

/-- The model's side of the ladder: at the entry readings, the walk's rows hold, its final
register is the scalar, and its final accumulator names the multiple. -/
private theorem walk_facts [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F] (d : HasCurve F)
    (chunks : ℕ) {xT yT x0 y0 : F} {T : d.W.Point}
    (hT : Kimchi.Gate.AddComplete.IsPoint d.W xT yT T)
    (hP0 : Kimchi.Gate.AddComplete.IsPoint d.W x0 y0 (T + T)) (v : F)
    (hfits : ToNat.toNat v < 2 ^ (5 * chunks))
    (hregime : d.LadderCompleteRegime (5 * chunks)
      (Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat v : ℤ))) :
    (∀ i, i < chunks →
        Kimchi.Gate.VarBaseMul.Holds (chainBuild xT yT x0 y0 0 (bsOf v chunks) i)) ∧
      accN (chainBuild xT yT x0 y0 0 (bsOf v chunks)) chunks = v ∧
      ∃ hfin : d.W.Nonsingular (accX (chainBuild xT yT x0 y0 0 (bsOf v chunks)) chunks)
          (accY (chainBuild xT yT x0 y0 0 (bsOf v chunks)) chunks),
        Point.some _ _ hfin =
          (Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat v : ℤ)) • T := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  obtain ⟨hTns, rfl⟩ := hT
  obtain ⟨hP0ns, hP0eq⟩ := hP0
  have hbsbool : ∀ j : ℕ, j < 5 * chunks → bsOf v chunks j = 0 ∨ bsOf v chunks j = 1 := by
    intro j _
    simp only [bsOf]
    split <;> simp
  have hgl : Kimchi.Gate.VarBaseMul.gateLadder (chainBuild xT yT x0 y0 0 (bsOf v chunks))
      (5 * chunks) = Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat v : ℤ) := by
    rw [Pasta.Shifted.unshiftType1, Kimchi.Gate.VarBaseMul.gateLadder_eq_register,
      Kimchi.Gate.VarBaseMul.gateRegister_eq_bitsVal, Kimchi.Gate.VarBaseMul.runBits_chainBuild]
    unfold bsOf
    rw [Kimchi.Gate.VarBaseMul.bitsVal_testBit (ToNat.toNat v) (5 * chunks) hfits]
  have hholds : ∀ i, i < chunks →
      Kimchi.Gate.VarBaseMul.Holds (chainBuild xT yT x0 y0 0 (bsOf v chunks) i) :=
    Kimchi.Gate.VarBaseMul.chain_complete d.W d.two_ne d.odd chunks hTns (bsOf v chunks) hbsbool
      0 hP0ns (by rw [two_zsmul]; exact hP0eq.symm) (by
        rw [hgl]
        rcases hregime with h | h
        · exact Or.inl h
        · exact Or.inr h)
  refine ⟨hholds, ?_, ?_⟩
  · rw [Kimchi.Gate.VarBaseMul.chain_accN chunks _ hholds (fun _ _ => rfl),
      Kimchi.Gate.VarBaseMul.runBits_chainBuild,
      Kimchi.Gate.VarBaseMul.bitsRegister_eq_cast _ (fun b hb => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
        exact hbsbool j (List.mem_range.mp hj)),
      show accN (chainBuild xT yT x0 y0 0 (bsOf v chunks)) 0 = 0 from rfl, mul_zero, zero_add]
    unfold bsOf
    rw [Kimchi.Gate.VarBaseMul.bitsVal_testBit (ToNat.toNat v) (5 * chunks) hfits,
      Int.cast_natCast, LawfulToNat.cast_toNat]
  · obtain ⟨hfin, hpt, -⟩ := Kimchi.Gate.VarBaseMul.varBaseMul_off d.W chunks
      (chainBuild xT yT x0 y0 0 (bsOf v chunks)) (Point.some xT yT hTns) _ hholds
      (fun i _ => by
        rw [(Kimchi.Gate.VarBaseMul.chainBuild_fields xT yT x0 y0 0 (bsOf v chunks) i).1,
          (Kimchi.Gate.VarBaseMul.chainBuild_fields xT yT x0 y0 0 (bsOf v chunks) i).2.1]
        exact ⟨hTns, rfl⟩)
      (fun _ _ => ⟨rfl, rfl⟩) ⟨hP0ns, by rw [two_zsmul]; exact hP0eq⟩ d.two_ne d.odd rfl
      (by
        rw [hgl]
        rcases hregime.toLadderRegime with h | h
        · exact Or.inl h
        · exact Or.inr h)
    rw [hgl] at hpt
    exact ⟨hfin, hpt⟩

/-- A curve point a cell pair names is not `0`, so its double is not either. -/
private theorem two_T_ne [Field F] [DecidableEq F] (d : HasCurve F) {V : Valuation F}
    {p : AffinePoint (FVar F)} {T : d.W.Point} (h : OnCurveAt d.W V p T) : T + T ≠ 0 :=
  d.two_torsion_free T (by
    obtain ⟨_, rfl⟩ := h
    exact Point.some_ne_zero _)

/-- The ladder's exit, off what the run leaves at the loop's entry and exit: every round holds,
the final register reads the scalar, the final point names the multiple, and the bits bundle
reads the scalar's bits. The loop's fold and rows are read as the walk by `scan_fold` and
`scan_rows`; the walk's facts are `walk_facts`'s. -/
private theorem exit_facts [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F] (d : HasCurve F)
    {n chunks : ℕ} (hn : 5 * chunks ≤ n) {s₀ s₁ s₂ s₃ s₄ : ProverState F}
    {base' base p : AffinePoint (FVar F)} {scalar : FVar F} {bits : Vector (FVar F) n}
    {T : d.W.Point} {loop : List (ScaleRound F) × AffinePoint (FVar F) × FVar F}
    (hbase : OnCurveAt d.W s₀.env.get base' T) (hsc : scalar.Scoped s₀)
    (hfits : ToNat.toNat (s₀.read scalar) < 2 ^ (5 * chunks))
    (hregime : d.LadderCompleteRegime (5 * chunks)
      (Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat (s₀.read scalar) : ℤ)))
    (h1 : CircuitType.ReadsAs (val := AffinePoint F) s₁ base
      ⟨s₀.read base'.x, s₀.read base'.y⟩ ∧ s₀ ≤ s₁)
    (h2 : CircuitType.ReadsAs (val := Vector F n) s₂ bits (lsbBitsVal n (s₁.read scalar)) ∧
      s₁ ≤ s₂)
    (hP : T + T ≠ 0 → OnCurveAs d.W s₃ p (T + T)) (hle3 : s₂ ≤ s₃)
    {xs : List (Vector (FVar F) 5)}
    (hxs : xs = (List.range chunks).map fun i => Vector.ofFn fun j : Fin 5 =>
      ((bits.toList.take (5 * chunks)).reverse).getD (5 * i + j.1) (CVar.const 0))
    (hfold : accRead base s₄ loop.2 =
      (xs.map (bitsRead s₃)).foldl accStep (accRead base s₃ (p, CVar.const 0)))
    (hlen : loop.1.length = xs.length)
    (hrows : ∀ (i : ℕ) (hi : i < xs.length) (hi' : i < loop.1.length),
      rowScoped s₄ loop.1[i] ∧ ScaleRound.read s₄.env.get loop.1[i] =
        rowStep (((xs.map (bitsRead s₃)).scanl accStep (accRead base s₃ (p, CVar.const 0))).getD
          i (accRead base s₃ (p, CVar.const 0))) (bitsRead s₃ xs[i]))
    (hle4 : s₃ ≤ s₄) :
    (∀ r ∈ loop.1, Kimchi.Gate.VarBaseMul.Holds (ScaleRound.read s₄.env.get r)) ∧
      s₄.read loop.2.2 = s₀.read scalar ∧
      Kimchi.Gate.AddComplete.IsPoint d.W (s₄.read loop.2.1.x) (s₄.read loop.2.1.y)
        ((Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat (s₀.read scalar) : ℤ)) • T) ∧
      CircuitType.ReadsAs (val := Vector Bool n) s₄ (mapVec BoolVar.unchecked bits)
        (unpackPure (s₀.read scalar) n) := by
  obtain ⟨hseal, hle1⟩ := h1
  obtain ⟨hbits, hle2⟩ := h2
  rw [ProverState.read_of_le hle1 hsc] at hbits
  have hbits₃ := hbits.of_le hle3
  have hT : Kimchi.Gate.AddComplete.IsPoint d.W (s₃.read base.x) (s₃.read base.y) T := by
    have hr := reads_affinePoint.mp (hseal.of_le (hle2.trans hle3)).2
    show Kimchi.Gate.AddComplete.IsPoint d.W (base.x.val s₃.env.get) (base.y.val s₃.env.get) T
    rw [hr.1, hr.2]
    exact hbase
  have hP0 : Kimchi.Gate.AddComplete.IsPoint d.W (s₃.read p.x) (s₃.read p.y) (T + T) :=
    (hP (two_T_ne d hbase)).2
  have hws : ∀ (k : ℕ) (hk : k < (xs.map (bitsRead s₃)).length),
      (xs.map (bitsRead s₃))[k] = bitsAt (bsOf (s₀.read scalar) chunks) k := by
    intro k hk
    have hk' : k < chunks := by simpa [hxs] using hk
    simp only [hxs, List.getElem_map, List.getElem_range]
    exact (window_facts hn hbits₃ k hk').2
  have hlenw : (xs.map (bitsRead s₃)).length = chunks := by simp [hxs]
  have hinit : accRead base s₃ (p, CVar.const 0)
      = ((s₃.read base.x, s₃.read base.y), (s₃.read p.x, s₃.read p.y), 0) := rfl
  obtain ⟨hholds, hreg, hfin, hpt⟩ :=
    walk_facts d chunks hT hP0 (s₀.read scalar) hfits hregime
  rw [hinit, scan_fold _ _ _ _ _ _ _ hws, hlenw] at hfold
  simp only [accRead, Prod.mk.injEq] at hfold
  refine ⟨fun r hr => ?_, ?_, ?_, reads_bits (hbits₃.of_le hle4)⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    have hi' : i < xs.length := by rw [← hlen]; exact hi
    have h := scan_rows (s₃.read base.x) (s₃.read base.y) _ (s₃.read p.x) (s₃.read p.y) 0
      (bsOf (s₀.read scalar) chunks)
      ((s₃.read base.x, s₃.read base.y), (s₃.read p.x, s₃.read p.y), 0) hws i
      (by simpa using hi')
    rw [List.getElem_map] at h
    rw [(hrows i hi' hi).2, hinit, h]
    exact hholds i (by simpa [hxs] using hi')
  · rw [hfold.2.2]
    exact hreg
  · rw [hfold.2.1.1, hfold.2.1.2]
    exact ⟨hfin, hpt.symm⟩

end VarBaseMul

open VarBaseMul in
/-- `lsbBitsWit` returns the scalar's bits. -/
@[spec] private def Prover.lsbBitsWit_reg [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [ConstraintHolds F c] (n : ℕ) (scalar : FVar F) :=
  Prover.register (Prover.witness_of_run (c := c) (lsbBitsWit n scalar)
    (fun st => scalar.Scoped st) (fun st => lsbBitsVal n (st.read scalar))
    (fun _ h => lsbBitsWit_run h) fun _ _ => by simp)

open VarBaseMul in
/-- **`varBaseMul`'s state-relative completeness.** From a base in scope reading as a curve
point and a scalar in scope reading within the ladder's width, under the regime, the run
succeeds: the returned bits read as the scalar's, and the result as the base times the scalar's
Type1 decode. The loop is the registered scan instance; `exit_facts` reads its post. -/
theorem Prover.varBaseMul_spec [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (d : HasCurve F) (n chunks : ℕ) (hn : 5 * chunks ≤ n) (base' : AffinePoint (FVar F))
    (scalar : Type1 (FVar F)) (T : d.W.Point) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ OnCurveAs d.W st₀ base' T ∧ scalar.val.Scoped st₀ ∧
      ToNat.toNat (st₀.read scalar.val) < 2 ^ (5 * chunks) ∧
      d.LadderCompleteRegime (5 * chunks)
        (Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat (st₀.read scalar.val) : ℤ))⌝⦄
    varBaseMul (c := Prover (KimchiConstraint F)) n chunks base' scalar
    ⦃⇓ r s' => ⌜CircuitType.ReadsAs (val := Vector Bool n) s' (mapVec BoolVar.unchecked r.lsbBits)
        (unpackPure (st₀.read scalar.val) n) ∧
      OnCurveAs d.W s' r.g
        ((Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat (st₀.read scalar.val) : ℤ)) • T) ∧
      st₀ ≤ s'⌝⦄ := by
  have hadd := fun a b : AffinePoint (FVar F) =>
    Prover.register (Prover.addFast_spec .checkFinite d.W d.short d.two_ne a b T T)
  unfold varBaseMul
  mvcgen [hadd]
  all_goals (try grind [Prover.Reg.iff, CircuitType.ReadsAs, CircuitType.scoped_fvar,
    scoped_affinePoint, reads_affinePoint, CVar.Scoped.of_le, ProverState.read_of_le, OnCurveAs,
    OnCurveAt, accScoped, bitsScoped, CVar.scoped_const])
  -- the doubled seed: the sealed base reads the base's curve point
  · rename_i s₀ h₀ base s₁ h1 bits s h2
    simp only [Prover.Reg.iff] at h1 h2
    obtain ⟨rfl, ⟨-, hbase⟩, -, -, -⟩ := h₀
    have hT2 := two_T_ne d hbase
    have hon : OnCurveAs d.W s base T := by
      refine ⟨(h1.1.of_le h2.2).1, ?_⟩
      have hr := reads_affinePoint.mp (h1.1.of_le h2.2).2
      show Kimchi.Gate.AddComplete.IsPoint d.W (base.x.val s.env.get) (base.y.val s.env.get) T
      rw [hr.1, hr.2]
      exact hbase
    exact ⟨trivial, hon, hon, hT2, hT2⟩
  -- the loop's entry: the seed and every window in scope
  · rename_i s₀ h₀ base s₂ h1 bits s₁ h2 p s h3
    simp only [Prover.Reg.iff] at h1 h2 h3
    obtain ⟨rfl, -, -, -, -⟩ := h₀
    have hbs := scoped_affinePoint.mp (h1.1.of_le (h2.2.trans h3.2.2.2)).1
    have hps := scoped_affinePoint.mp h3.1
    refine ⟨trivial, ⟨hbs.1, hbs.2, hps.1, hps.2, CVar.scoped_const _ _⟩, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact (window_facts hn (h2.1.of_le h3.2.2.2) i (List.mem_range.mp hi)).1
  -- the one `varBaseMul` row: every round holds, its cells in scope after the loop
  · rename_i s₀ h₀ base s₃ h1 bits s₂ h2 p s₁ h3 loop s h4
    simp only [Prover.Reg.iff] at h1 h2 h3 h4
    obtain ⟨rfl, ⟨-, hbase⟩, hsc, hfits, hregime⟩ := h₀
    refine ⟨trivial, (exit_facts d hn hbase hsc hfits hregime h1 h2 h3.2.2.1 h3.2.2.2 rfl h4.2.1
      h4.2.2.1 h4.2.2.2.1 h4.2.2.2.2).1, fun y hy => ?_⟩
    change y ∈ loop.1.flatMap (fun r => (r.cellsA ++ r.cellsB).filterMap id) at hy
    rw [List.mem_flatMap] at hy
    obtain ⟨r, hr, hy⟩ := hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    have hs := (h4.2.2.2.1 i (h4.2.2.1 ▸ hi) hi).1
    simp only [rowScoped, cells, List.forall_mem_cons] at hs
    revert y
    simp [ScaleRound.cellsA, ScaleRound.cellsB, hs]
  -- the register pin: the final register reads the scalar
  · rename_i s₀ h₀ base s₄ h1 bits s₃ h2 p s₂ h3 loop s₁ h4 u s h5
    simp only [Prover.Reg.iff] at h1 h2 h3 h4
    obtain ⟨rfl, -⟩ := h5
    obtain ⟨rfl, ⟨-, hbase⟩, hsc, hfits, hregime⟩ := h₀
    obtain ⟨-, hreg, -, -⟩ := exit_facts d hn hbase hsc hfits hregime h1 h2 h3.2.2.1 h3.2.2.2 rfl
      h4.2.1 h4.2.2.1 h4.2.2.2.1 h4.2.2.2.2
    have hle : s₀ ≤ s := h1.2.trans (h2.2.trans (h3.2.2.2.trans h4.2.2.2.2))
    refine ⟨trivial, h4.1.2.2.2.2, hsc.of_le hle, ?_⟩
    rw [ProverState.read_of_le hle hsc]
    exact hreg
  -- the result: the bits read as the scalar's, the point as the multiple
  · rename_i s₀ h₀ base s₅ h1 bits s₄ h2 p s₃ h3 loop s₂ h4 u₁ s₁ h5 u₂ s h6
    simp only [Prover.Reg.iff] at h1 h2 h3 h4 h6
    obtain ⟨rfl, -⟩ := h5
    obtain ⟨rfl, ⟨-, hbase⟩, hsc, hfits, hregime⟩ := h₀
    obtain ⟨-, -, hpt, hbits⟩ := exit_facts d hn hbase hsc hfits hregime h1 h2 h3.2.2.1 h3.2.2.2
      rfl h4.2.1 h4.2.2.1 h4.2.2.2.1 h4.2.2.2.2
    refine ⟨hbits.of_le h6, ?_, (h1.2.trans (h2.2.trans (h3.2.2.2.trans h4.2.2.2.2))).trans h6⟩
    refine ⟨scoped_affinePoint.mpr ⟨h4.1.2.2.1.of_le h6, h4.1.2.2.2.1.of_le h6⟩, ?_⟩
    show Kimchi.Gate.AddComplete.IsPoint d.W (s.read loop.2.1.x) (s.read loop.2.1.y) _
    rw [ProverState.read_of_le h6 h4.1.2.2.1, ProverState.read_of_le h6 h4.1.2.2.2.1]
    exact hpt

attribute [irreducible] lsbBitsWit varBaseMul

/-! ## `scaleFast1` -/

/-- The `Type1` path, for a scalar field no larger than the circuit field: `varBaseMul`,
dropping the bits. When the ladder covers all `n` bits it pins the top bit to zero: an
`n`-bit string decomposes the scalar uniquely only below the modulus, and both `t` and
`t + modulus` fit below `2ⁿ` for almost every `t`. -/
def scaleFast1 [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [ConstraintHolds F c]
    [KimchiSystem F c] (n chunks : ℕ) (p : AffinePoint (FVar F))
    (t : Type1 (FVar F)) : CircuitM F c (AffinePoint (FVar F)) := do
  let r ← varBaseMul n chunks p t
  if n ≤ 5 * chunks then
    (r.lsbBits.toList.drop (5 * chunks - 1)).forM fun bit => assertEqual bit (.const 0)
  pure r.g

open Std.Do WeierstrassCurve.Affine in
/-- **Soundness** (`scaleFast1`). The result is the base times the Type1 decode of an
integer in the ladder's range that the scalar reads as, one bit narrower at the full width.
The bits that pin the integer are dropped, so the law speaks of the integer alone. -/
theorem scaleFast1_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (d : HasCurve F) (n chunks : ℕ) (hn : 5 * chunks ≤ n)
    (base : AffinePoint (FVar F)) (scalar : Type1 (FVar F)) :
    ⦃⌜True⌝⦄
    scaleFast1 (c := Builder V (KimchiConstraint F)) n chunks base scalar
    ⦃⇓ r _ => ⌜∀ T : d.W.Point, OnCurveAt d.W V base T →
      ∃ z : ℤ, 0 ≤ z ∧ z < 2 ^ (5 * chunks) ∧ (n ≤ 5 * chunks → z < 2 ^ (5 * chunks - 1)) ∧
        (z : F) = scalar.val.val V ∧
        ∀ _ : d.LadderRegime (5 * chunks) (Pasta.Shifted.unshiftType1 (5 * chunks) z),
          OnCurveAt d.W V r ((Pasta.Shifted.unshiftType1 (5 * chunks) z) • T)⌝⦄ := by
  have hvbm := fun (V : Valuation F) => varBaseMul_spec (V := V) d n chunks hn base scalar
  have hpin := forM_spec (V := V) (c := KimchiConstraint F)
    (fun b : FVar F => assertEqual (c := Builder V (KimchiConstraint F)) b (CVar.const 0))
    (fun b : FVar F => b.val V = (CVar.const 0 : FVar F).val V)
    (fun b => assertEqual_spec (V := V) b (CVar.const 0))
  unfold scaleFast1
  mvcgen [hvbm, hpin]
  · -- the full width: the pinned top bit halves the ladder's range
    rename_i r _ _ _ hr _ _ hpin0
    intro T hT
    obtain ⟨bs, hread, hreg, hpoint⟩ := hr T hT
    have hzeros : ∀ b ∈ bs.toList.drop (5 * chunks - 1), b = false := by
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
      have hi' : 5 * chunks - 1 + i < 5 * chunks := by
        simp only [List.length_drop, Vector.length_toList] at hi
        omega
      have hidx : 5 * chunks - 1 + i < n := Nat.lt_of_lt_of_le hi' hn
      have hmem : r.lsbBits.toList[5 * chunks - 1 + i]'(by simpa using hidx)
          ∈ r.lsbBits.toList.drop (5 * chunks - 1) := by
        have heq : (r.lsbBits.toList.drop (5 * chunks - 1))[i]'(by
            simp only [List.length_drop, Vector.length_toList]; omega)
            = r.lsbBits.toList[5 * chunks - 1 + i]'(by simpa using hidx) := List.getElem_drop ..
        rw [← heq]
        exact List.getElem_mem _
      have hb0 : bit bs[5 * chunks - 1 + i] = (0 : F) := by
        rw [← hread (5 * chunks - 1 + i) hi',
          show r.lsbBits[5 * chunks - 1 + i]'hidx
            = r.lsbBits.toList[5 * chunks - 1 + i]'(by simpa using hidx) from rfl,
          hpin0 _ hmem]
        simp [CVar.val]
      rw [List.getElem_drop, Vector.getElem_toList]
      cases hbb : bs[5 * chunks - 1 + i] with
      | false => rfl
      | true => rw [hbb] at hb0; simp [bit] at hb0
    refine ⟨(Kimchi.natLsbVal bs.toList : ℤ), Int.natCast_nonneg _, ?_, fun _ => ?_, ?_, hpoint⟩
    · exact_mod_cast (by simpa using Kimchi.natLsbVal_lt bs.toList :
        Kimchi.natLsbVal bs.toList < 2 ^ (5 * chunks))
    · exact_mod_cast Kimchi.natLsbVal_lt_of_drop_false hzeros
    · rw [hreg]
      push_cast
      ring
  · -- below the full width: no pin, the bound is vacuous
    rename_i r _ hnle _ hr
    intro T hT
    obtain ⟨bs, -, hreg, hpoint⟩ := hr T hT
    refine ⟨(Kimchi.natLsbVal bs.toList : ℤ), Int.natCast_nonneg _, ?_, fun h => absurd h hnle,
      ?_, hpoint⟩
    · exact_mod_cast (by simpa using Kimchi.natLsbVal_lt bs.toList :
        Kimchi.natLsbVal bs.toList < 2 ^ (5 * chunks))
    · rw [hreg]
      push_cast
      ring

attribute [irreducible] scaleFast1

/-- The zero pins after a ladder, registered: `List.forM`'s law at `assertEqual` against `0`,
each pinned cell in scope and reading `0`. -/
@[spec] private def Prover.pinLoop_reg [Field F] [DecidableEq F] (l : List (FVar F)) :=
  Prover.register (Prover.forM_spec (c := KimchiConstraint F)
    (fun b : FVar F => assertEqual b (CVar.const 0))
    (fun st b => b.Scoped st ∧ (CVar.const 0 : FVar F).Scoped st ∧
      st.read b = st.read (CVar.const 0))
    (by grind [ProverState.read_of_le, CVar.Scoped.of_le])
    (fun st b => Prover.assertEqual_spec b (CVar.const 0) st) l)

/-- The honest ladder's bits from `k` on read `0` where the scalar's representative is below
`2 ^ k`: the pinned cells' entry to `Prover.pinLoop_reg`. -/
private theorem pins_read_zero [Field F] [DecidableEq F] [ToNat F] {st : ProverState F}
    {n k : ℕ} {bits : Vector (FVar F) n} {v : F}
    (h : CircuitType.ReadsAs (val := Vector Bool n) st (mapVec BoolVar.unchecked bits)
      (unpackPure v n))
    (hfits : ToNat.toNat v < 2 ^ k) :
    ∀ x ∈ bits.toList.drop k, x.Scoped st ∧ (CVar.const 0 : FVar F).Scoped st ∧
      st.read x = st.read (CVar.const 0) := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hi' : k + i < n := by
    simp only [List.length_drop, Vector.length_toList] at hi
    omega
  have hbit : (ToNat.toNat v).testBit (k + i) = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hfits (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hsc := CircuitType.scoped_vector.mp h.1 (k + i) hi'
  have hrd := CircuitType.reads_vector.mp h.2 (k + i) hi'
  rw [getElem_mapVec] at hsc hrd
  simp only [List.getElem_drop, Vector.getElem_toList]
  refine ⟨CircuitType.scoped_boolVar.mp hsc, trivial, ?_⟩
  have hv := CircuitType.reads_boolVar.mp hrd
  rw [BoolVar.coe_unchecked, getElem_unpackPure, hbit] at hv
  simpa [ProverState.read, bit, CVar.val] using hv

/-- **`scaleFast1`'s state-relative completeness.** `varBaseMul`'s, with the bits dropped: at
the full width the scalar's representative is one bit narrower, so the pinned top bit reads
`0`. -/
theorem Prover.scaleFast1_spec [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (d : HasCurve F) (n chunks : ℕ) (hn : 5 * chunks ≤ n) (base : AffinePoint (FVar F))
    (scalar : Type1 (FVar F)) (T : d.W.Point) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ OnCurveAs d.W st₀ base T ∧ scalar.val.Scoped st₀ ∧
      ToNat.toNat (st₀.read scalar.val) < 2 ^ (5 * chunks) ∧
      (n ≤ 5 * chunks → ToNat.toNat (st₀.read scalar.val) < 2 ^ (5 * chunks - 1)) ∧
      d.LadderCompleteRegime (5 * chunks)
        (Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat (st₀.read scalar.val) : ℤ))⌝⦄
    scaleFast1 (c := Prover (KimchiConstraint F)) n chunks base scalar
    ⦃⇓ r s' => ⌜OnCurveAs d.W s' r
        ((Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat (st₀.read scalar.val) : ℤ)) • T) ∧
      st₀ ≤ s'⌝⦄ := by
  have hvbm := Prover.register (Prover.varBaseMul_spec d n chunks hn base scalar T)
  unfold scaleFast1
  mvcgen [hvbm]
  -- the pins: at the full width the honest scalar leaves the bits from `5 * chunks - 1` clear
  case vc2.post.success.isTrue.pre =>
    rename_i s₀ h₀ r _ hle s h
    obtain ⟨rfl, -, -, -, hfits1, -⟩ := h₀
    exact ⟨trivial, pins_read_zero (Prover.Reg.iff.mp h).1 (hfits1 hle)⟩
  all_goals grind [Prover.Reg.iff, OnCurveAs, OnCurveAt, scoped_affinePoint,
    reads_affinePoint, CVar.Scoped.of_le, ProverState.read_of_le]

/-! ## `scaleFast2` -/

/-- The split path, `[2·sDiv2 + sOdd + 2^(5·chunks)]·g`, for a scalar field larger than
the circuit field: run the ladder on `sDiv2`, pin its bits from `sDiv2Bits` up to zero, and
fold the parity in by subtracting the base when `sOdd` is clear. -/
def scaleFast2 [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [ConstraintHolds F c]
    [KimchiSystem F c] (n chunks sDiv2Bits : ℕ) (base : AffinePoint (FVar F))
    (sDiv2 : FVar F) (sOdd : BoolVar F) : CircuitM F c (AffinePoint (FVar F)) := do
  let r ← varBaseMul n chunks base ⟨sDiv2⟩
  (r.lsbBits.toList.drop sDiv2Bits).forM fun bit => assertEqual bit (.const 0)
  -- the `sOdd`-clear branch first: `g − base`, by the pure negation
  let negBase : AffinePoint (FVar F) := ⟨base.x, CVar.negate_ base.y⟩
  let q ← addFast .checkFinite r.g negBase
  -- the point conditional selects `y` before `x`: the fixture pins that emission order
  let y ← select sOdd r.g.y q.p.y
  let x ← select sOdd r.g.x q.p.x
  pure ⟨x, y⟩

/-- The pinned high bits: bits reading as `bs` whose cells from `sDiv2Bits` on are pinned to
`0` have LSB-first value below `2 ^ sDiv2Bits`. -/
private theorem natLsbVal_lt_of_pinned [Field F] {V : Valuation F} {n chunks sDiv2Bits : ℕ}
    (hn : 5 * chunks ≤ n) (lsbBits : Vector (FVar F) n) (bs : Vector Bool (5 * chunks))
    (hread : ∀ i (hi : i < 5 * chunks),
      (lsbBits[i]'(Nat.lt_of_lt_of_le hi hn)).val V = bit bs[i])
    (hpin0 : ∀ x ∈ lsbBits.toList.drop sDiv2Bits, x.val V = (CVar.const 0 : FVar F).val V) :
    (Kimchi.natLsbVal bs.toList : ℤ) < 2 ^ sDiv2Bits := by
  have hzeros : ∀ b ∈ bs.toList.drop sDiv2Bits, b = false := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have hi' : sDiv2Bits + i < 5 * chunks := by
      simp only [List.length_drop, Vector.length_toList] at hi
      omega
    have hidx : sDiv2Bits + i < n := Nat.lt_of_lt_of_le hi' hn
    have hmem : lsbBits.toList[sDiv2Bits + i]'(by simpa using hidx)
        ∈ lsbBits.toList.drop sDiv2Bits := by
      have heq : (lsbBits.toList.drop sDiv2Bits)[i]'(by
          simp only [List.length_drop, Vector.length_toList]; omega)
          = lsbBits.toList[sDiv2Bits + i]'(by simpa using hidx) := List.getElem_drop ..
      rw [← heq]
      exact List.getElem_mem _
    have hb0 : bit bs[sDiv2Bits + i] = (0 : F) := by
      rw [← hread (sDiv2Bits + i) hi',
        show lsbBits[sDiv2Bits + i]'hidx
          = lsbBits.toList[sDiv2Bits + i]'(by simpa using hidx) from rfl,
        hpin0 _ hmem]
      simp [CVar.val]
    rw [List.getElem_drop, Vector.getElem_toList]
    cases hbb : bs[sDiv2Bits + i] with
    | false => rfl
    | true => rw [hbb] at hb0; simp [bit] at hb0
  exact_mod_cast Kimchi.natLsbVal_lt_of_drop_false hzeros

open Std.Do WeierstrassCurve.Affine in
/-- **Soundness** (`scaleFast2`). -/
theorem scaleFast2_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (d : HasCurve F) (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n)
    (base : AffinePoint (FVar F)) (sDiv2 : FVar F) (sOdd : BoolVar F) :
    ⦃⌜True⌝⦄
    scaleFast2 (c := Builder V (KimchiConstraint F)) n chunks sDiv2Bits base sDiv2 sOdd
    ⦃⇓ r _ => ⌜∀ T : d.W.Point, OnCurveAt d.W V base T → ∀ bb : Bool,
      (↑sOdd : CVar F).val V = bit bb →
      ∃ z : ℤ, 0 ≤ z ∧ z < 2 ^ sDiv2Bits ∧ (z : F) = sDiv2.val V ∧
        ∀ _ : d.LadderRegime (5 * chunks) (Pasta.Shifted.unshiftType1 (5 * chunks) z),
          OnCurveAt d.W V r
            ((Pasta.Shifted.unshiftType2 (5 * chunks) z (if bb then 1 else 0)) • T)⌝⦄ := by
  have hvbm := fun (V : Valuation F) =>
    varBaseMul_spec (V := V) d n chunks hn base ⟨sDiv2⟩
  have hpin := forM_spec (V := V) (c := KimchiConstraint F)
    (fun b : FVar F => assertEqual (c := Builder V (KimchiConstraint F)) b (CVar.const 0))
    (fun b : FVar F => b.val V = (CVar.const 0 : FVar F).val V)
    (fun b => assertEqual_spec (V := V) b (CVar.const 0))
  have hsel := fun (t e : FVar F) =>
    selectField_spec (V := V) (c := KimchiConstraint F) sOdd t e
  simp only [scaleFast2, select_fvar]
  mvcgen [hvbm, hpin, hsel]
  case vc1.W => exact d.W
  case vc2.ha => exact d.short
  case vc3.htwo => exact d.two_ne
  rename_i _ rvb _ hvb _ _ hpin0 q _ yr _ hyr xr _ hxr hadd
  intro T hT bb hbb
  obtain ⟨bs, hread, hreg, hpoint⟩ := hvb T hT
  have hltSplit := natLsbVal_lt_of_pinned hn rvb.lsbBits bs hread hpin0
  refine ⟨(Kimchi.natLsbVal bs.toList : ℤ), Int.natCast_nonneg _, hltSplit, ?_, ?_⟩
  · rw [hreg]
    push_cast
    ring
  · intro hregime
    have hG := hpoint hregime
    obtain ⟨hGns, hGeq⟩ := hG
    have hPne : ((Pasta.Shifted.unshiftType1 (5 * chunks)
        ((Kimchi.natLsbVal bs.toList : ℤ))) • T) ≠ 0 := by
      rw [hGeq]
      exact Point.some_ne_zero hGns
    have hnegT : OnCurveAt d.W V ⟨base.x, CVar.negate_ base.y⟩ (-T) :=
      OnCurveAt.neg ⟨d.short.1, d.short.2.2.1⟩ hT
    rcases hadd.2 _ _ ⟨hGns, hGeq⟩ hnegT (d.two_torsion_free _ hPne) with
      ⟨hinf, -⟩ | ⟨-, hq⟩
    · exact absurd (hadd.1.symm.trans hinf) (by norm_num)
    · cases bb with
      | false =>
        show Kimchi.Gate.AddComplete.IsPoint d.W (xr.val V) (yr.val V)
          ((2 * (Kimchi.natLsbVal bs.toList : ℤ) + 0 + 2 ^ (5 * chunks)) • T)
        rw [hxr false hbb, hyr false hbb,
          show ((2 * (Kimchi.natLsbVal bs.toList : ℤ) + 0 + 2 ^ (5 * chunks)) • T)
            = ((Pasta.Shifted.unshiftType1 (5 * chunks) ((Kimchi.natLsbVal bs.toList : ℤ)))
                • T + -T)
            from by rw [Pasta.Shifted.unshiftType1]; module]
        exact hq
      | true =>
        show Kimchi.Gate.AddComplete.IsPoint d.W (xr.val V) (yr.val V)
          ((2 * (Kimchi.natLsbVal bs.toList : ℤ) + 1 + 2 ^ (5 * chunks)) • T)
        rw [hxr true hbb, hyr true hbb,
          show ((2 * (Kimchi.natLsbVal bs.toList : ℤ) + 1 + 2 ^ (5 * chunks)) • T)
            = ((Pasta.Shifted.unshiftType1 (5 * chunks) ((Kimchi.natLsbVal bs.toList : ℤ))) • T)
            from by rw [Pasta.Shifted.unshiftType1]; module]
        exact ⟨hGns, hGeq⟩

open Std.Do in
/-- **Soundness, the scalar side** (`scaleFast2`). For any base, the half is an integer below
`2 ^ sDiv2Bits`: the ladder's bits and the pinned high bits never read the base. -/
theorem scaleFast2_spec_scalar {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n) (base : AffinePoint (FVar F))
    (sDiv2 : FVar F) (sOdd : BoolVar F) :
    ⦃⌜True⌝⦄
    scaleFast2 (c := Builder V (KimchiConstraint F)) n chunks sDiv2Bits base sDiv2 sOdd
    ⦃⇓ _ _ => ⌜∃ z : ℤ, 0 ≤ z ∧ z < 2 ^ sDiv2Bits ∧ (z : F) = sDiv2.val V⌝⦄ := by
  have hvbm := varBaseMul_spec_scalar (V := V) n chunks hn base ⟨sDiv2⟩
  have hpin := forM_spec (V := V) (c := KimchiConstraint F)
    (fun b : FVar F => assertEqual (c := Builder V (KimchiConstraint F)) b (CVar.const 0))
    (fun b : FVar F => b.val V = (CVar.const 0 : FVar F).val V)
    (fun b => assertEqual_spec (V := V) b (CVar.const 0))
  have hadd := fun (a b : AffinePoint (FVar F)) =>
    builder_spec_true (addFast (c := Builder V (KimchiConstraint F)) .checkFinite a b)
  have hsel := fun (t e : FVar F) =>
    builder_spec_true (Snarky.selectField (c := Builder V (KimchiConstraint F)) sOdd t e)
  simp only [scaleFast2, select_fvar]
  mvcgen [hvbm, hpin, hadd, hsel, -Snarky.Kimchi.addFast_spec]
  rename_i _ rvb _ hvb _ _ hpin0 _ _ _ _ _ _ _ _
  obtain ⟨bs, hread, hreg⟩ := hvb
  exact ⟨(Kimchi.natLsbVal bs.toList : ℤ), Int.natCast_nonneg _,
    natLsbVal_lt_of_pinned hn rvb.lsbBits bs hread hpin0, by rw [hreg]; push_cast; ring⟩

attribute [irreducible] scaleFast2

/-- The parity fold's subtraction is finite: under the regime the ladder's multiple of a nonzero
base is not the base. -/
private theorem scaleFast2_sub_ne_zero [Field F] [DecidableEq F] (d : HasCurve F) {chunks sv : ℕ}
    {T : d.W.Point} (hT : T ≠ 0) (hfits : sv < 2 ^ (5 * chunks))
    (hregime : d.LadderCompleteRegime (5 * chunks)
      (Pasta.Shifted.unshiftType1 (5 * chunks) (sv : ℤ))) :
    (Pasta.Shifted.unshiftType1 (5 * chunks) (sv : ℤ)) • T + -T ≠ 0 := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have hoff : ((2 * (sv : ℤ) + 2 ^ (5 * chunks)) • T) ≠ 0 :=
    Kimchi.Gate.VarBaseMul.ladder_off_base d.W hT (5 * chunks) sv (by positivity)
      (by exact_mod_cast hfits) (by
        rcases hregime with h | ⟨hL, h1, h2, -, -, h5, -, h7, -⟩
        · exact Or.inl h
        · refine Or.inr ⟨by omega, h1, h2, ?_, ?_⟩ <;>
            simpa only [Pasta.Shifted.unshiftType1] using ‹_›)
  rwa [show (Pasta.Shifted.unshiftType1 (5 * chunks) (sv : ℤ)) • T + -T
      = (2 * (sv : ℤ) + 2 ^ (5 * chunks)) • T from by
    rw [Pasta.Shifted.unshiftType1]; module]

/-- The parity fold's branches as multiples: a set bit keeps the ladder's point, a clear one
subtracts the base. -/
private theorem unshiftType2_smul [Field F] [DecidableEq F] (d : HasCurve F) (k : ℕ) (z : ℤ)
    (T : d.W.Point) :
    (Pasta.Shifted.unshiftType2 k z 1) • T = (Pasta.Shifted.unshiftType1 k z) • T ∧
      (Pasta.Shifted.unshiftType2 k z 0) • T = (Pasta.Shifted.unshiftType1 k z) • T + -T := by
  constructor <;> rw [Pasta.Shifted.unshiftType2, Pasta.Shifted.unshiftType1] <;> module

/-- **`scaleFast2`'s state-relative completeness.** The ladder on the half, whose high bits
vanish because it fits `sDiv2Bits`, then the parity fold: the regime keeps the subtraction of the
base finite, and the select picks the ladder's point or the difference by the parity bit. -/
theorem Prover.scaleFast2_spec [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (d : HasCurve F) (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n)
    (hsplit : sDiv2Bits ≤ 5 * chunks) (base : AffinePoint (FVar F)) (sDiv2 : FVar F)
    (sOdd : BoolVar F) (T : d.W.Point) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ OnCurveAs d.W st₀ base T ∧ sDiv2.Scoped st₀ ∧
      (↑sOdd : CVar F).Scoped st₀ ∧ (st₀.read sOdd = 0 ∨ st₀.read sOdd = 1) ∧
      ToNat.toNat (st₀.read sDiv2) < 2 ^ sDiv2Bits ∧
      d.LadderCompleteRegime (5 * chunks)
        (Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat (st₀.read sDiv2) : ℤ))⌝⦄
    scaleFast2 (c := Prover (KimchiConstraint F)) n chunks sDiv2Bits base sDiv2 sOdd
    ⦃⇓ r s' => ⌜OnCurveAs d.W s' r
        ((Pasta.Shifted.unshiftType2 (5 * chunks) (ToNat.toNat (st₀.read sDiv2) : ℤ)
          (if st₀.read sOdd = 1 then 1 else 0)) • T) ∧
      st₀ ≤ s'⌝⦄ := by
  have hvbm := Prover.register (Prover.varBaseMul_spec d n chunks hn base ⟨sDiv2⟩ T)
  have hadd := fun a b : AffinePoint (FVar F) => Prover.register
    (Prover.addFast_spec .checkFinite d.W d.short d.two_ne a b
      ((Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat (st₀.read sDiv2) : ℤ)) • T) (-T))
  have hwidth : ToNat.toNat (st₀.read sDiv2) < 2 ^ sDiv2Bits →
      ToNat.toNat (st₀.read sDiv2) < 2 ^ (5 * chunks) :=
    fun h => lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hsplit)
  have hT0 : OnCurveAs d.W st₀ base T → T ≠ 0 := by
    rintro ⟨-, hns, hTeq⟩
    rw [hTeq]
    exact Point.some_ne_zero hns
  obtain ⟨hk1, hk0⟩ := unshiftType2_smul d (5 * chunks) (ToNat.toNat (st₀.read sDiv2) : ℤ) T
  unfold scaleFast2
  simp only [select_fvar]
  mvcgen [hvbm, hadd]
  -- the ladder runs on the half, which fits the ladder's width
  case vc1.pre =>
    rename_i s h
    obtain ⟨rfl, hb, hsc, -, -, hfits, hreg⟩ := h
    exact ⟨trivial, hb, hsc, hwidth hfits, hreg⟩
  -- the pins: the half leaves the bits from `sDiv2Bits` clear
  case vc2.post.success.pre =>
    rename_i s₀ h₀ r s h
    obtain ⟨rfl, -, -, -, -, hfits, -⟩ := h₀
    exact ⟨trivial, pins_read_zero (Prover.Reg.iff.mp h).1 hfits⟩
  -- the subtraction: the negated base, the ladder's point off 2-torsion, and a finite sum
  case vc3.post.success.post.success.pre =>
    rename_i s₀ h₀ r s₁ h₁ u s h
    obtain ⟨rfl, hb, -, -, -, hfits, hreg⟩ := h₀
    obtain ⟨-, hg, hle₁⟩ := Prover.Reg.iff.mp h₁
    have hle := Prover.Reg.iff.mp h
    have hG0 : (Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat (s₀.read sDiv2) : ℤ)) • T
        ≠ 0 := by
      obtain ⟨-, hns, hGeq⟩ := hg
      rw [hGeq]
      exact Point.some_ne_zero hns
    have hb' := monotone_onCurveAs (hle₁.trans hle) hb
    obtain ⟨hbx, hby⟩ := scoped_affinePoint.mp hb'.1
    exact ⟨trivial, monotone_onCurveAs hle hg,
      ⟨scoped_affinePoint.mpr ⟨hbx, CVar.Scoped.scale_ hby⟩,
        OnCurveAt.neg ⟨d.short.1, d.short.2.2.1⟩ hb'.2⟩,
      d.two_torsion_free _ hG0, scaleFast2_sub_ne_zero d (hT0 hb) (hwidth hfits) hreg⟩
  -- the result: the select picks the ladder's point or the difference by the parity bit
  case vc6.post.success.post.success.post.success.post.success.post.success =>
    rename_i s₀ h₀ r s₁ h₁ u s₂ h₂ q s₃ h₃ y s₄ h₄ x s h
    obtain ⟨rfl, hb, -, hosc, hbool, hfits, hreg⟩ := h₀
    have hsum := scaleFast2_sub_ne_zero d (hT0 hb) (hwidth hfits) hreg
    grind [Prover.Reg.iff, OnCurveAs, OnCurveAt, scoped_affinePoint, reads_affinePoint,
      CVar.Scoped.of_le, ProverState.read_of_le]
  all_goals grind [Prover.Reg.iff, OnCurveAs, OnCurveAt, scoped_affinePoint,
    reads_affinePoint, CVar.Scoped.of_le, ProverState.read_of_le]

/-! ## The parity split -/

/-- The parity split of a field value: `s = 2·sDiv2 + sOdd`. -/
def splitField [Field F] [ToNat F] (s : F) : F × Bool :=
  let odd := (ToNat.toNat s) % 2 = 1
  ((if odd then s - 1 else s) / 2, odd)

private def splitFieldWit [Field F] [ToNat F] (s : FVar F) : AsProver F (F × Bool) := do
  let v ← AsProver.readCVar s
  pure (splitField v)

/-- Witness a parity split and assert `s = 2·sDiv2 + sOdd`. -/
def splitFieldVar [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c]
    (s : FVar F) : CircuitM F c (FVar F × BoolVar F) := do
  let r ← witness (val := F × Bool) (splitFieldWit s)
  assertEqual s (CVar.add_ (CVar.scale_ 2 r.1) ↑r.2)
  pure r

open Std.Do in
/-- **Soundness** (`splitFieldVar`). The witnessed pair is a bit and a half that join to
the scalar. -/
theorem splitFieldVar_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (s : FVar F) :
    ⦃⌜True⌝⦄
    splitFieldVar (c := Builder V c) s
    ⦃⇓ r _ => ⌜∃ bb : Bool, (↑r.2 : CVar F).val V = bit bb ∧
      s.val V = 2 * r.1.val V + bit bb⌝⦄ := by
  unfold splitFieldVar
  mvcgen
  rename_i r _ hpost _ _ hrow
  obtain ⟨-, bb, hbb⟩ := hpost
  refine ⟨bb, hbb, ?_⟩
  rw [hrow, CVar.val_add_, CVar.val_scale_, hbb]

attribute [irreducible] splitFieldWit splitFieldVar

/-- The split rejoins: twice the half plus the parity bit is the value. -/
private theorem splitField_join [Field F] [ToNat F] (h2 : (2 : F) ≠ 0) (v : F) :
    2 * (splitField v).1 + (if (splitField v).2 then 1 else 0) = v := by
  simp only [splitField, decide_eq_true_eq]
  split <;> field_simp <;> ring

/-- `splitFieldWit` returns the split of the operand's reading. -/
@[spec] private def Prover.splitFieldWit_reg [Field F] [DecidableEq F] [ToNat F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (s : FVar F) :=
  Prover.register (Prover.witness_of_run (c := c) (splitFieldWit s) (fun st => s.Scoped st)
    (fun st => splitField (st.read s))
    (fun _ h => by simp [splitFieldWit, AsProver.readCVar_run h]) fun _ _ => by simp)

/-- `splitFieldVar`'s state-relative completeness: the half and the parity bit read the split
of the operand's entry reading. -/
theorem Prover.splitFieldVar_spec [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (h2 : (2 : F) ≠ 0) (s : FVar F)
    (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ s.Scoped st₀⌝⦄
    splitFieldVar (c := Prover c) s
    ⦃⇓ r s' => ⌜r.1.Scoped s' ∧ (↑r.2 : CVar F).Scoped s' ∧
      s'.read r.1 = (splitField (st₀.read s)).1 ∧
      s'.read r.2 = (if (splitField (st₀.read s)).2 then 1 else 0) ∧ st₀ ≤ s'⌝⦄ := by
  have hjoin := splitField_join (F := F) h2
  unfold splitFieldVar
  mvcgen
  all_goals grind [Prover.Reg.iff, CircuitType.ReadsAs, CircuitType.scoped_prod,
    CircuitType.reads_prod, CircuitType.scoped_fvar, CircuitType.reads_fvar,
    CircuitType.scoped_boolVar, CircuitType.reads_boolVar, bit, ProverState.read_of_le,
    CVar.Scoped.of_le, CVar.Scoped.add_, CVar.Scoped.scale_, CVar.val_add_, CVar.val_scale_]

/-- Registered. -/
@[spec] private def Prover.splitFieldVar_reg [Field F] [DecidableEq F] [ToNat F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (h2 : (2 : F) ≠ 0)
    (s : FVar F) :=
  Prover.register (Prover.splitFieldVar_spec (c := c) h2 s)

/-! ## `scaleFast2'` -/

/-- The width `scaleFast2'` runs `scaleFast2` at: `sDiv2Bits - 1` at the full field width
(`n ≤ sDiv2Bits + 1`), pinning one more bit of the half; `sDiv2Bits` otherwise. -/
def scaleFast2'Width (n sDiv2Bits : ℕ) : ℕ :=
  if n ≤ sDiv2Bits + 1 then sDiv2Bits - 1 else sDiv2Bits

/-- `[s + 2^(5·chunks)]·g`: split the raw scalar, then `scaleFast2` at `scaleFast2'Width`.
At the full field width the split is an equation in the circuit field that both `s` and
`s + modulus` solve for almost every `s`, decoding to different multiples of the base; the
one bit less of `sDiv2` makes the decomposition canonical. -/
def scaleFast2' [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c]
    [KimchiSystem F c] (n chunks sDiv2Bits : ℕ) (base : AffinePoint (FVar F))
    (s : FVar F) : CircuitM F c (AffinePoint (FVar F)) := do
  let (sDiv2, sOdd) ← splitFieldVar s
  scaleFast2 n chunks (scaleFast2'Width n sDiv2Bits) base sDiv2 sOdd

/-- The split's reading of `scaleFast2'`: a half `z` below the ladder's width and a parity bit
joining to `s` read as a half below `2 ^ sDiv2Bits`, one bit narrower at the full width. -/
private theorem scaleFast2'_join [Field F] {V : Valuation F} {n sDiv2Bits : ℕ}
    {s sDiv2 : FVar F} {z : ℤ} {bb : Bool}
    (hpin : s.val V = 2 * sDiv2.val V + bit bb) (h0 : 0 ≤ z)
    (hlt : z < 2 ^ scaleFast2'Width n sDiv2Bits) (hzval : (z : F) = sDiv2.val V) :
    0 ≤ z ∧ z < 2 ^ sDiv2Bits ∧ (n ≤ sDiv2Bits + 1 → z < 2 ^ (sDiv2Bits - 1)) ∧
      ((2 * z + (if bb then 1 else 0) : ℤ) : F) = s.val V := by
  have hw : 2 ^ scaleFast2'Width n sDiv2Bits ≤ (2 : ℤ) ^ sDiv2Bits := by
    apply pow_le_pow_right₀ (by norm_num)
    unfold scaleFast2'Width; split_ifs <;> omega
  refine ⟨h0, lt_of_lt_of_le hlt hw, fun hfull => ?_, ?_⟩
  · rwa [scaleFast2'Width, if_pos hfull] at hlt
  · push_cast
    rw [hpin, hzval]
    cases bb <;> simp [bit]

open Std.Do WeierstrassCurve.Affine in
/-- **Soundness** (`scaleFast2'`). A half and a parity bit that join to the scalar, the
half one bit narrower at the full width, and the result is the multiple they name. -/
theorem scaleFast2'_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (d : HasCurve F) (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n) (base : AffinePoint (FVar F))
    (s : FVar F) :
    ⦃⌜True⌝⦄
    scaleFast2' (c := Builder V (KimchiConstraint F)) n chunks sDiv2Bits base s
    ⦃⇓ r _ => ⌜∀ T : d.W.Point, OnCurveAt d.W V base T →
      ∃ (z : ℤ) (bb : Bool), 0 ≤ z ∧ z < 2 ^ sDiv2Bits ∧
        (n ≤ sDiv2Bits + 1 → z < 2 ^ (sDiv2Bits - 1)) ∧
        ((2 * z + (if bb then 1 else 0) : ℤ) : F) = s.val V ∧
        ∀ _ : d.LadderRegime (5 * chunks) (Pasta.Shifted.unshiftType1 (5 * chunks) z),
          OnCurveAt d.W V r
            ((Pasta.Shifted.unshiftType2 (5 * chunks) z (if bb then 1 else 0)) • T)⌝⦄ := by
  have hsplitV := fun (V : Valuation F) =>
    splitFieldVar_spec (c := KimchiConstraint F) (V := V) s
  have hsf2 := fun (V : Valuation F) (sDiv2 : FVar F) (sOdd : BoolVar F) =>
    scaleFast2_spec (V := V) d n chunks (scaleFast2'Width n sDiv2Bits) hn base sDiv2 sOdd
  simp only [scaleFast2']
  mvcgen [hsplitV, hsf2]
  rename_i hsp _ _
  intro hq T hT
  obtain ⟨bb, hbit, hpin⟩ := hsp
  obtain ⟨z, h0, hlt, hzval, hpoint⟩ := hq T hT bb hbit
  obtain ⟨h0', hlt', hfull, hjoin⟩ := scaleFast2'_join hpin h0 hlt hzval
  exact ⟨z, bb, h0', hlt', hfull, hjoin, hpoint⟩

open Std.Do in
/-- **Soundness, the scalar side** (`scaleFast2'`). For any base, a half and a parity bit join
to the scalar, the half below `2 ^ sDiv2Bits` and one bit narrower at the full width. -/
theorem scaleFast2'_spec_scalar {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n) (base : AffinePoint (FVar F))
    (s : FVar F) :
    ⦃⌜True⌝⦄
    scaleFast2' (c := Builder V (KimchiConstraint F)) n chunks sDiv2Bits base s
    ⦃⇓ _ _ => ⌜∃ (z : ℤ) (bb : Bool), 0 ≤ z ∧ z < 2 ^ sDiv2Bits ∧
        (n ≤ sDiv2Bits + 1 → z < 2 ^ (sDiv2Bits - 1)) ∧
        ((2 * z + (if bb then 1 else 0) : ℤ) : F) = s.val V⌝⦄ := by
  have hsplitV := splitFieldVar_spec (c := KimchiConstraint F) (V := V) s
  have hsf2 := fun (sDiv2 : FVar F) (sOdd : BoolVar F) =>
    scaleFast2_spec_scalar (V := V) n chunks (scaleFast2'Width n sDiv2Bits) hn base sDiv2 sOdd
  simp only [scaleFast2']
  mvcgen [hsplitV, hsf2]
  rename_i hsp _ _
  intro hq
  obtain ⟨bb, -, hpin⟩ := hsp
  obtain ⟨z, h0, hlt, hzval⟩ := hq
  exact ⟨z, bb, scaleFast2'_join hpin h0 hlt hzval⟩


attribute [irreducible] scaleFast2'

/-- **`scaleFast2'`'s state-relative completeness.** The honest split of the scalar, then
`scaleFast2`'s run on the half and the parity bit. -/
theorem Prover.scaleFast2'_spec [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (d : HasCurve F) (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n)
    (hsplit : sDiv2Bits ≤ 5 * chunks) (base : AffinePoint (FVar F)) (s : FVar F) (T : d.W.Point)
    (st₀ : ProverState F) :
    ⦃fun st => ⌜st = st₀ ∧ OnCurveAs d.W st₀ base T ∧ s.Scoped st₀ ∧
      ToNat.toNat (splitField (st₀.read s)).1 < 2 ^ scaleFast2'Width n sDiv2Bits ∧
      d.LadderCompleteRegime (5 * chunks)
        (Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat (splitField (st₀.read s)).1 : ℤ))⌝⦄
    scaleFast2' (c := Prover (KimchiConstraint F)) n chunks sDiv2Bits base s
    ⦃⇓ r s' => ⌜OnCurveAs d.W s' r
        ((2 * (ToNat.toNat (splitField (st₀.read s)).1 : ℤ)
            + (if (splitField (st₀.read s)).2 then 1 else 0) + 2 ^ (5 * chunks)) • T) ∧
      st₀ ≤ s'⌝⦄ := by
  have hsplit' : scaleFast2'Width n sDiv2Bits ≤ 5 * chunks := by
    unfold scaleFast2'Width; split_ifs <;> omega
  have hsf2 := fun (a : FVar F) (b : BoolVar F) => Prover.register
    (Prover.scaleFast2_spec d n chunks (scaleFast2'Width n sDiv2Bits) hn hsplit' base a b T)
  unfold scaleFast2'
  mvcgen [hsf2]
  case vc1.h2 => exact d.two_ne
  -- the result: `scaleFast2`'s multiple, its parity read back through the bit's field value
  case vc4.post.success.post.success =>
    rename_i s₀ h₀ w s₁ h₁ r s₂
    obtain ⟨rfl, -, -, -, -⟩ := h₀
    obtain ⟨-, -, hd, ho, hle₁⟩ := Prover.Reg.iff.mp h₁
    intro h
    obtain ⟨hr, hle⟩ := Prover.Reg.iff.mp h
    refine ⟨?_, hle₁.trans hle⟩
    rw [hd, ho] at hr
    convert hr using 2
    rw [Pasta.Shifted.unshiftType2]
    cases (splitField (s₀.read s)).2 <;> simp
  all_goals grind [Prover.Reg.iff, OnCurveAs, OnCurveAt, scoped_affinePoint,
    reads_affinePoint, CVar.Scoped.of_le, ProverState.read_of_le]

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta Kimchi.Gate.VarBaseMul in
/-- **Soundness at Vesta.** From `varBaseMul_spec`'s output on a `Type1` carrier whose
witnessed bits read as a value below the scalar order, the result is the base times the
carrier's decode. The bit bound makes the ladder's integer the carrier's canonical
representative, which is a field element and so below the regime's bound. Stated on the law's
output, as `vesta_endoMul_read` is: a consumer holds that output. -/
theorem vesta_varBaseMul_read {V : Valuation Fq} {base : AffinePoint (FVar Fq)}
    {sv : Type1 (FVar Fq)} {r : VarBaseMulResult 255 Fq} {Z : Type1 Fq}
    (hread : sv.val.val V = Z.val)
    (h : ∀ T : HasCurve.vesta.W.Point, OnCurveAt HasCurve.vesta.W V base T →
      ∃ bs : Vector Bool (5 * 51),
        (∀ i (hi : i < 5 * 51), (r.lsbBits[i]'(by omega)).val V = bit bs[i]) ∧
        sv.val.val V = ((Kimchi.natLsbVal bs.toList : ℕ) : Fq) ∧
        ∀ _ : HasCurve.vesta.LadderRegime (5 * 51)
            (Pasta.Shifted.unshiftType1 (5 * 51) (Kimchi.natLsbVal bs.toList : ℤ)),
          OnCurveAt HasCurve.vesta.W V r.g
            ((Pasta.Shifted.unshiftType1 (5 * 51)
              (Kimchi.natLsbVal bs.toList : ℤ)) • T)) :
    ∀ T : Vesta.curve.toAffine.Point, OnCurveAt Vesta.curve.toAffine V base T →
      (∀ bs : Vector Bool 255,
        (∀ i (hi : i < 255), ((mapVec BoolVar.unchecked r.lsbBits)[i]).toCVar.val V
          = bit bs[i]) → Kimchi.natLsbVal bs.toList < PALLAS_SCALAR_CARD) →
      OnCurveAt Vesta.curve.toAffine V r.g (Z.toScalarZ • T) := by
  intro T hT hlock
  obtain ⟨bs, hbs, hpin, hact⟩ := h T hT
  have hlt : Kimchi.natLsbVal bs.toList < PALLAS_SCALAR_CARD :=
    hlock bs (fun i hi => by simpa using hbs i hi)
  -- the ladder's integer is the carrier's canonical representative
  have hval : Z.val.val = Kimchi.natLsbVal bs.toList :=
    toNat_eq_of_natCast_eq (F := Fq) (by rw [← hread, hpin]) hlt
  have hZ : Z.toScalarZ
      = Pasta.Shifted.unshiftType1 (5 * 51) (Kimchi.natLsbVal bs.toList : ℤ) := by
    simp only [Type1.toScalarZ, Type1.fromShifted, Pasta.Shifted.unshiftType1, hval]
  have hzb : Z.toScalarZ < 4 * PALLAS_BASE_CARD - 4 := by
    have hv : ((Z.val.val : ℕ) : ℤ) < PALLAS_SCALAR_CARD := by exact_mod_cast ZMod.val_lt Z.val
    simp only [Type1.toScalarZ, Type1.fromShifted, Pasta.Shifted.unshiftType1]
    norm_num [PALLAS_BASE_CARD, PALLAS_SCALAR_CARD] at hv ⊢
    omega
  rw [hZ]
  exact hact (hZ ▸ HasCurve.vesta_ladderRegime Z.toScalarZ hzb)

end Snarky.Kimchi
