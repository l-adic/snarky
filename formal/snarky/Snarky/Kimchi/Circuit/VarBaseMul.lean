import Snarky.DSL.Field
import Snarky.DSL.Assert
import Snarky.DSL.Bits
import Snarky.DSL.Boolean
import Snarky.Types.Shifted
import Snarky.Kimchi.Circuit.AddComplete
import Snarky.Traverse
import Kimchi.Gate.VarBaseMul
import Kimchi.Gate.Semantics.VarBaseMul
import Kimchi.Gate.Semantics.EndoMul

/-!
# The VarBaseMul gadget

Port of `Snarky.Circuit.Kimchi.VarBaseMul`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/VarBaseMul.purs; OCaml
`Pickles.Plonk_curve_ops.scale_fast`): the double-add ladder `varBaseMul` — witness
the scalar's bits, walk `acc' = 2·acc + Q` per bit with `Q = (xT, (2b−1)·yT)` in
5-bit rows, pin the running scalar register, emit one `varBaseMul` constraint — and
its consumers `scaleFast1` (`Type1` scalars), `scaleFast2`/`scaleFast2'` (split
scalars for the larger-scalar-field case), and `splitFieldVar`.

The byte contract (allocation order, row shapes) is oracle-checked by the corpus:
`var_base_mul_step_circuit` (`scaleFast1` at the full 255-bit ladder) and
`scale_fast2_128_step_circuit` (`scaleFast2'` through `splitFieldVar`). The
downstream VarBaseMul-consuming fixtures (`ftcomm`, `xhat`, the mains) stay deferred
to the pickles buildout.

One section per circuit: the definition, its soundness spec, its completeness law, and
then the definition is sealed `irreducible`. Nothing below a section reasons about that
circuit's body — the round reaches the ladder as `scaleRound_spec`/`scaleRound_complete`,
the ladder reaches the wrappers as `varBaseMul_spec`/`varBaseMul_complete`.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS batches the whole witness chain through `mkWitnessTable`/`computeVbmChain`
  (`doubleAddChain`'s projective walk with Montgomery batch inversion); the port
  computes each bit step sequentially from the threaded variables via the gate
  model's `Kimchi.Gate.VarBaseMul.stepBit` — `Projective.purs` certifies the batched
  rows equal the sequential per-step formulas, so the advice values are identical.
  Advice-only: the emitted circuit is untouched.
- PS's chain computation reports degenerate steps (`DivisionByZero`); the port's
  advice is total — field division returns junk on a zero denominator instead of
  aborting the prover run. Identical on non-degenerate inputs.
- PS allocates each bit step's five advice values through five separate `exists`;
  the port witnesses the quintet in one call — five fresh variables in the same
  order, so the variable ids agree.
- PS walks a round's five bits with an inner `mapAccumM`; the port unrolls it into
  five sequential `witness` calls. Same calls in the same order, so the emitted
  circuit is untouched — but the loop rules cannot walk it, so each reading's law
  pays for the five steps separately instead of once against an invariant.
- `s1Sq` and `s2` are witnessed and never read back — dead allocations kept for
  OCaml variable-id parity, exactly as PS keeps them.
- PS's type-level width bookkeeping (`FieldSizeInBits`, `Mul 5 nChunks bitsUsed`)
  renders as the plain parameters `(n chunks : ℕ)` with `bitsUsed := 5 * chunks`;
  the laws state the bounds the types enforced.
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

open Std.Do WeierstrassCurve.Affine

/-! ## The curve dictionary

What every law below closes over. -/

/-- The curve dictionary the VarBaseMul laws close over (the PS ambient
`WeierstrassCurve` class): the curve, its Pasta short shape, and the group facts the
ladder's gate-semantics theorems consume. Like `HasEndo`, the laws stay generic over
it and are concretized only inside a larger circuit's instantiation. -/
structure HasCurve (F : Type) [Field F] [DecidableEq F] where
  /-- The curve the base point and accumulators live on. -/
  W : WeierstrassCurve.Affine F
  /-- The Pasta short-Weierstrass shape. -/
  short : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0
  /-- The group order is prime. -/
  prime : Nat.Prime W.order
  /-- The group order is not `2` — with `prime`, the group has no 2-torsion. -/
  odd : W.order ≠ 2
  /-- The field does not have characteristic `2`. -/
  two_ne : (2 : F) ≠ 0

/-- The regime the ladder's non-degeneracy pricing needs, at `L` bits over the
dictionary's order: EITHER the whole ladder fits below the order (subwrap — no
condition on the scalar), OR the one-wrap band holds and the scalar's Type1 decode
`z` avoids the forbidden residues. `varBaseMul_off`'s dichotomy, at the law's
list-level decode. -/
def HasCurve.LadderRegime [Field F] [DecidableEq F] (d : HasCurve F) (L : ℕ)
    (z : ℤ) : Prop :=
  3 * 2 ^ L ≤ d.W.order ∨
    (2 ^ (L - 1) < d.W.order ∧ d.W.order < 2 ^ L ∧ d.W.order % 4 = 1 ∧
      z ∉ Kimchi.Gate.VarBaseMul.forbiddenValues d.W.order)

open WeierstrassCurve.Affine in
/-- No point of the group is 2-torsion: the order is an odd prime, so doubling kills only
zero. What the addition gadget asks of the base it doubles. -/
theorem HasCurve.two_torsion_free [Field F] [DecidableEq F] (d : HasCurve F)
    (P : d.W.Point) (hne : P ≠ 0) : P + P ≠ 0 := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have hlt : (2 : ℤ) < (d.W.order : ℤ) := by
    have h2 := (Fact.out : Nat.Prime d.W.order).two_le
    have h3 : 3 ≤ d.W.order := by
      rcases Nat.lt_or_ge d.W.order 3 with h | h
      · exact absurd (by omega : d.W.order = 2) d.odd
      · exact h
    exact_mod_cast h3
  intro hzero
  exact Kimchi.Gate.VarBaseMul.smul_ne_zero_of_lt d.W hne (by norm_num) hlt
    (by rw [two_zsmul, hzero])

/-! ## The round

One 5-bit row: the register advice, then five bit-step quintets threaded through the
accumulator. Its laws are the wiring a trace threads (`Threads`) and, for the honest run,
the grant that the round's cells are in scope and its reading is the gate's canonical row.
Sealed after them — the ladder reasons about a round through its laws, never its body. -/

/-- The scalar's `n` bits LSB-first as field values, in ONE witness (PS `unpackPure`
under a single `exists`). -/
private def lsbBitsWit [Field F] [ToNat F] (n : ℕ) (scalar : FVar F) :
    AsProver F (Vector F n) := do
  let v ← AsProver.readCVar scalar
  pure (Vector.ofFn fun i => if (ToNat.toNat v).testBit i.1 then 1 else 0)

/-- Per-chunk scalar-register advice: fold `2a + b` over the chunk's five bits from
the previous register (PS's `foldl (\\a b -> double a + b)`). -/
private def nAccWit [Field F] (nPrev : FVar F) (bs : Vector (FVar F) 5) :
    AsProver F F := do
  let a ← AsProver.readCVar nPrev
  let b0 ← AsProver.readCVar bs[0]
  let b1 ← AsProver.readCVar bs[1]
  let b2 ← AsProver.readCVar bs[2]
  let b3 ← AsProver.readCVar bs[3]
  let b4 ← AsProver.readCVar bs[4]
  pure (b4 + 2 * (b3 + 2 * (b2 + 2 * (b1 + 2 * (b0 + 2 * a)))))

/-- One bit step's advice quintet `(s1, s1Sq, s2, xRes, yRes)`: the wired slope and
result from the gate model's `stepBit`, plus the two dead registers. -/
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

/-- One 5-bit round (PS's `mapAccumM` body): the register advice, then five bit-step
quintets threaded through the accumulator, collected as the gate's `ScaleRound`
record and the next `(acc, register)` pair. Named so it carries its own law per
reading — the caller's loop then walks one registered spec per round. -/
def scaleRound [Field F] [DecidableEq F] [BasicSystem F c]
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

/-- The step's grant: the round is built from the base, the accumulators either side of
it, and the row's five bits. Structural — no valuation appears. -/
private def Threads (base : AffinePoint (FVar F)) (st : AffinePoint (FVar F) × FVar F)
    (bs : Vector (FVar F) 5) (r : ScaleRound F)
    (st' : AffinePoint (FVar F) × FVar F) : Prop :=
  r.base = base ∧ (r.acc0 = st.1 ∧ r.nPrev = st.2) ∧ (r.acc5 = st'.1 ∧ r.nNext = st'.2) ∧
    (r.bit0 = bs[0] ∧ r.bit1 = bs[1] ∧ r.bit2 = bs[2] ∧ r.bit3 = bs[3] ∧ r.bit4 = bs[4])

open Std.Do in
/-- The step's spec: the round it emits is wired to the base, the accumulators either
side, and the row's bits. -/
@[spec] private theorem scaleRound_spec {V : Valuation F} [Field F] [DecidableEq F]
    (base : AffinePoint (FVar F)) (st : AffinePoint (FVar F) × FVar F)
    (bs : Vector (FVar F) 5) :
    ⦃⌜True⌝⦄
    scaleRound (c := Builder V (KimchiConstraint F)) base st bs
    ⦃⇓ p _ => ⌜Threads base st bs p.1 p.2⌝⦄ := by
  simp only [scaleRound, Threads]
  mvcgen

/-- The rows the ladder is handed: five bit variables in scope. -/
private def BitRow [Field F] (st₁ : ProverState F) (bs : Vector (FVar F) 5) : Prop :=
  ∀ v ∈ bs.toList, v.Scoped st₁

/-- The ladder's accumulator invariant: the table has only grown since the bits were
witnessed, and the accumulator's three variables are in scope. -/
private def AccInv [Field F] (st₁ : ProverState F)
    (acc : AffinePoint (FVar F) × FVar F) (st : ProverState F) : Prop :=
  (st₁.nv ≤ st.nv ∧ st₁.env.Le st.env) ∧
    acc.1.x.Scoped st ∧ acc.1.y.Scoped st ∧ acc.2.Scoped st

/-- A round's cells. -/
private def cells [Field F] (r : ScaleRound F) : List (CVar F) :=
  [r.base.x, r.base.y, r.acc0.x, r.acc0.y, r.acc1.x, r.acc1.y, r.acc2.x, r.acc2.y,
    r.acc3.x, r.acc3.y, r.acc4.x, r.acc4.y, r.acc5.x, r.acc5.y,
    r.bit0, r.bit1, r.bit2, r.bit3, r.bit4,
    r.slope0, r.slope1, r.slope2, r.slope3, r.slope4, r.nPrev, r.nNext]

/-- The step's grant at a table: the round is wired to the base, the accumulators either
side and the row's bits; its cells are in scope; and its reading is the gate's canonical
row at its own inputs. -/
private def RowGrant [Field F] [DecidableEq F] (base : AffinePoint (FVar F))
    (acc : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 5) (r : ScaleRound F)
    (acc' : AffinePoint (FVar F) × FVar F) (st : ProverState F) : Prop :=
  Threads base acc bs r acc' ∧ (∀ cv ∈ cells r, cv.Scoped st) ∧
    ScaleRound.read st.env.get r
      = Kimchi.Gate.VarBaseMul.build (base.x.val st.env.get) (base.y.val st.env.get)
          (acc.1.x.val st.env.get) (acc.1.y.val st.env.get) (acc.2.val st.env.get)
          (bs[0].val st.env.get) (bs[1].val st.env.get) (bs[2].val st.env.get)
          (bs[3].val st.env.get) (bs[4].val st.env.get)

/-- Scope and the table's growth survive further growth. -/
private theorem AccInv.mono [Field F] {st₁ : ProverState F}
    (acc : AffinePoint (FVar F) × FVar F) {st st' : ProverState F}
    (hnv : st.nv ≤ st'.nv) (hle : st.env.Le st'.env) (h : AccInv st₁ acc st) :
    AccInv st₁ acc st' :=
  ⟨⟨Nat.le_trans h.1.1 hnv, h.1.2.trans hle⟩,
    h.2.1.mono hnv, h.2.2.1.mono hnv, h.2.2.2.mono hnv⟩

/-- A row's grant survives the table's growth: the wiring says the operands are the
round's own cells, and those are in scope, so nothing in the reading moves. -/
private theorem RowGrant.mono [Field F] [DecidableEq F] (base : AffinePoint (FVar F))
    (acc : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 5) (r : ScaleRound F)
    (acc' : AffinePoint (FVar F) × FVar F) {st st' : ProverState F}
    (hnv : st.nv ≤ st'.nv) (hle : st.env.Le st'.env)
    (h : RowGrant base acc bs r acc' st) : RowGrant base acc bs r acc' st' := by
  obtain ⟨hthr, hsc, hread⟩ := h
  obtain ⟨hb, ⟨ha0, hn0⟩, hout, hb0, hb1, hb2, hb3, hb4⟩ := hthr
  refine ⟨⟨hb, ⟨ha0, hn0⟩, hout, hb0, hb1, hb2, hb3, hb4⟩,
    fun cv hcv => (hsc cv hcv).mono hnv, ?_⟩
  have hcell : ∀ cv ∈ cells r, cv.val st'.env.get = cv.val st.env.get :=
    fun cv hcv => CVar.val_of_le hle (hsc cv hcv)
  have hread' : ScaleRound.read st'.env.get r = ScaleRound.read st.env.get r := by
    simp only [ScaleRound.read, hcell r.base.x (by simp [cells]),
      hcell r.base.y (by simp [cells]),
      hcell r.acc0.x (by simp [cells]),
      hcell r.acc0.y (by simp [cells]),
      hcell r.acc1.x (by simp [cells]),
      hcell r.acc1.y (by simp [cells]),
      hcell r.acc2.x (by simp [cells]),
      hcell r.acc2.y (by simp [cells]),
      hcell r.acc3.x (by simp [cells]),
      hcell r.acc3.y (by simp [cells]),
      hcell r.acc4.x (by simp [cells]),
      hcell r.acc4.y (by simp [cells]),
      hcell r.acc5.x (by simp [cells]),
      hcell r.acc5.y (by simp [cells]),
      hcell r.bit0 (by simp [cells]),
      hcell r.bit1 (by simp [cells]),
      hcell r.bit2 (by simp [cells]),
      hcell r.bit3 (by simp [cells]),
      hcell r.bit4 (by simp [cells]),
      hcell r.slope0 (by simp [cells]),
      hcell r.slope1 (by simp [cells]),
      hcell r.slope2 (by simp [cells]),
      hcell r.slope3 (by simp [cells]),
      hcell r.slope4 (by simp [cells]),
      hcell r.nPrev (by simp [cells]),
      hcell r.nNext (by simp [cells])]
  rw [hread', hread, ← hb, ← ha0, ← hn0, ← hb0, ← hb1, ← hb2, ← hb3, ← hb4,
    hcell r.base.x (by simp [cells]), hcell r.base.y (by simp [cells]),
    hcell r.acc0.x (by simp [cells]), hcell r.acc0.y (by simp [cells]),
    hcell r.nPrev (by simp [cells]), hcell r.bit0 (by simp [cells]),
    hcell r.bit1 (by simp [cells]), hcell r.bit2 (by simp [cells]),
    hcell r.bit3 (by simp [cells]), hcell r.bit4 (by simp [cells])]

/-- One honest round: the register advice then five bit steps, each witnessing the
gate's own `stepBit` at the cells the previous step produced. What comes back is the
walk's row at the round's inputs. -/
private theorem scaleRound_complete [Field F] [DecidableEq F] (st₁ : ProverState F)
    (base : AffinePoint (FVar F)) (hbase : base.x.Scoped st₁ ∧ base.y.Scoped st₁)
    (acc : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 5) (hbs : BitRow st₁ bs) :
    Complete (F := F) (c := KimchiConstraint F) (AccInv st₁ acc)
      (scaleRound (c := KimchiConstraint F) base acc bs)
      (fun p st' => AccInv st₁ p.2 st' ∧ RowGrant base acc bs p.1 p.2 st') := by
  rintro st ⟨⟨hnv, hle⟩, hax, hay, han⟩
  have hbx : base.x.Scoped st := hbase.1.mono hnv
  have hby : base.y.Scoped st := hbase.2.mono hnv
  have hb : ∀ (i : ℕ) (hi : i < 5), (bs[i]'hi).Scoped st :=
    fun i hi => (hbs _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))).mono hnv
  set W := Kimchi.Gate.VarBaseMul.build (base.x.val st.env.get) (base.y.val st.env.get)
    (acc.1.x.val st.env.get) (acc.1.y.val st.env.get) (acc.2.val st.env.get)
    ((bs[0]'(by omega)).val st.env.get) ((bs[1]'(by omega)).val st.env.get)
    ((bs[2]'(by omega)).val st.env.get) ((bs[3]'(by omega)).val st.env.get)
    ((bs[4]'(by omega)).val st.env.get) with hW
  -- the register advice
  obtain ⟨nAcc, t0, R0, S0, N0, E0, C0, D0⟩ :=
    witness_complete (c := KimchiConstraint F) (val := F) (nAccWit acc.2 bs) (st := st)
      (v := W.nPrime)
      (by
        simp only [nAccWit, AsProver.bind_eq, AsProver.run_bind, AsProver.readCVar_run han,
          AsProver.readCVar_run (hb 0 (by omega)), AsProver.readCVar_run (hb 1 (by omega)),
          AsProver.readCVar_run (hb 2 (by omega)), AsProver.readCVar_run (hb 3 (by omega)),
          AsProver.readCVar_run (hb 4 (by omega)), Except.bind]
        rw [hW]
        rfl)
  simp only [CircuitType.scoped_fvar] at C0
  simp only [CircuitType.reads_fvar] at D0
  have LA0 : st.env.Le t0.env := E0
  have NA0 : st.nv ≤ t0.nv := N0
  -- bit step 0
  obtain ⟨w0, t1, R1, S1, N1, E1, C1, D1⟩ :=
    witness_complete (c := KimchiConstraint F) (val := F × F × F × F × F)
      (bitWit base (bs[0]'(by omega)) ⟨acc.1.x, acc.1.y⟩) (st := t0)
      (v := (W.s0, W.s0 * W.s0,
        2 * W.y0 / (2 * W.x0 + W.xT - W.s0 * W.s0) - W.s0, W.x1, W.y1))
      (by
        simp only [bitWit, AsProver.bind_eq, AsProver.run_bind,
          AsProver.readCVar_run (hbx.mono NA0), AsProver.readCVar_run (hby.mono NA0),
          AsProver.readCVar_run (hax.mono NA0), AsProver.readCVar_run (hay.mono NA0),
          AsProver.readCVar_run ((hb 0 (by omega)).mono NA0), Except.bind,
          CVar.val_of_le LA0 hbx, CVar.val_of_le LA0 hby,
          CVar.val_of_le LA0 hax, CVar.val_of_le LA0 hay, CVar.val_of_le LA0 (hb 0 (by omega))]
        rw [hW]
        rfl)
  obtain ⟨sl0, sq0, se0, ox0, oy0⟩ := w0
  simp only [CircuitType.scoped_prod, CircuitType.scoped_fvar] at C1
  simp only [CircuitType.reads_prod, CircuitType.reads_fvar] at D1
  have LA1 : st.env.Le t1.env := LA0.trans E1
  have NA1 : st.nv ≤ t1.nv := Nat.le_trans NA0 N1
  -- bit step 1
  obtain ⟨w1, t2, R2, S2, N2, E2, C2, D2⟩ :=
    witness_complete (c := KimchiConstraint F) (val := F × F × F × F × F)
      (bitWit base (bs[1]'(by omega)) ⟨ox0, oy0⟩) (st := t1)
      (v := (W.s1, W.s1 * W.s1,
        2 * W.y1 / (2 * W.x1 + W.xT - W.s1 * W.s1) - W.s1, W.x2, W.y2))
      (by
        simp only [bitWit, AsProver.bind_eq, AsProver.run_bind,
          AsProver.readCVar_run (hbx.mono NA1), AsProver.readCVar_run (hby.mono NA1),
          AsProver.readCVar_run C1.2.2.2.1, AsProver.readCVar_run C1.2.2.2.2,
          AsProver.readCVar_run ((hb 1 (by omega)).mono NA1), Except.bind,
          CVar.val_of_le LA1 hbx, CVar.val_of_le LA1 hby,
          D1.2.2.2.1, D1.2.2.2.2, CVar.val_of_le LA1 (hb 1 (by omega))]
        rw [hW]
        rfl)
  obtain ⟨sl1, sq1, se1, ox1, oy1⟩ := w1
  simp only [CircuitType.scoped_prod, CircuitType.scoped_fvar] at C2
  simp only [CircuitType.reads_prod, CircuitType.reads_fvar] at D2
  have LA2 : st.env.Le t2.env := LA1.trans E2
  have NA2 : st.nv ≤ t2.nv := Nat.le_trans NA1 N2
  -- bit step 2
  obtain ⟨w2, t3, R3, S3, N3, E3, C3, D3⟩ :=
    witness_complete (c := KimchiConstraint F) (val := F × F × F × F × F)
      (bitWit base (bs[2]'(by omega)) ⟨ox1, oy1⟩) (st := t2)
      (v := (W.s2, W.s2 * W.s2,
        2 * W.y2 / (2 * W.x2 + W.xT - W.s2 * W.s2) - W.s2, W.x3, W.y3))
      (by
        simp only [bitWit, AsProver.bind_eq, AsProver.run_bind,
          AsProver.readCVar_run (hbx.mono NA2), AsProver.readCVar_run (hby.mono NA2),
          AsProver.readCVar_run C2.2.2.2.1, AsProver.readCVar_run C2.2.2.2.2,
          AsProver.readCVar_run ((hb 2 (by omega)).mono NA2), Except.bind,
          CVar.val_of_le LA2 hbx, CVar.val_of_le LA2 hby,
          D2.2.2.2.1, D2.2.2.2.2, CVar.val_of_le LA2 (hb 2 (by omega))]
        rw [hW]
        rfl)
  obtain ⟨sl2, sq2, se2, ox2, oy2⟩ := w2
  simp only [CircuitType.scoped_prod, CircuitType.scoped_fvar] at C3
  simp only [CircuitType.reads_prod, CircuitType.reads_fvar] at D3
  have LA3 : st.env.Le t3.env := LA2.trans E3
  have NA3 : st.nv ≤ t3.nv := Nat.le_trans NA2 N3
  -- bit step 3
  obtain ⟨w3, t4, R4, S4, N4, E4, C4, D4⟩ :=
    witness_complete (c := KimchiConstraint F) (val := F × F × F × F × F)
      (bitWit base (bs[3]'(by omega)) ⟨ox2, oy2⟩) (st := t3)
      (v := (W.s3, W.s3 * W.s3,
        2 * W.y3 / (2 * W.x3 + W.xT - W.s3 * W.s3) - W.s3, W.x4, W.y4))
      (by
        simp only [bitWit, AsProver.bind_eq, AsProver.run_bind,
          AsProver.readCVar_run (hbx.mono NA3), AsProver.readCVar_run (hby.mono NA3),
          AsProver.readCVar_run C3.2.2.2.1, AsProver.readCVar_run C3.2.2.2.2,
          AsProver.readCVar_run ((hb 3 (by omega)).mono NA3), Except.bind,
          CVar.val_of_le LA3 hbx, CVar.val_of_le LA3 hby,
          D3.2.2.2.1, D3.2.2.2.2, CVar.val_of_le LA3 (hb 3 (by omega))]
        rw [hW]
        rfl)
  obtain ⟨sl3, sq3, se3, ox3, oy3⟩ := w3
  simp only [CircuitType.scoped_prod, CircuitType.scoped_fvar] at C4
  simp only [CircuitType.reads_prod, CircuitType.reads_fvar] at D4
  have LA4 : st.env.Le t4.env := LA3.trans E4
  have NA4 : st.nv ≤ t4.nv := Nat.le_trans NA3 N4
  -- bit step 4
  obtain ⟨w4, t5, R5, S5, N5, E5, C5, D5⟩ :=
    witness_complete (c := KimchiConstraint F) (val := F × F × F × F × F)
      (bitWit base (bs[4]'(by omega)) ⟨ox3, oy3⟩) (st := t4)
      (v := (W.s4, W.s4 * W.s4,
        2 * W.y4 / (2 * W.x4 + W.xT - W.s4 * W.s4) - W.s4, W.x5, W.y5))
      (by
        simp only [bitWit, AsProver.bind_eq, AsProver.run_bind,
          AsProver.readCVar_run (hbx.mono NA4), AsProver.readCVar_run (hby.mono NA4),
          AsProver.readCVar_run C4.2.2.2.1, AsProver.readCVar_run C4.2.2.2.2,
          AsProver.readCVar_run ((hb 4 (by omega)).mono NA4), Except.bind,
          CVar.val_of_le LA4 hbx, CVar.val_of_le LA4 hby,
          D4.2.2.2.1, D4.2.2.2.2, CVar.val_of_le LA4 (hb 4 (by omega))]
        rw [hW]
        rfl)
  obtain ⟨sl4, sq4, se4, ox4, oy4⟩ := w4
  simp only [CircuitType.scoped_prod, CircuitType.scoped_fvar] at C5
  simp only [CircuitType.reads_prod, CircuitType.reads_fvar] at D5
  have LA5 : st.env.Le t5.env := LA4.trans E5
  have NA5 : st.nv ≤ t5.nv := Nat.le_trans NA4 N5
  -- the tails
  have M4 : t4.env.Le t5.env := E5
  have M3 : t3.env.Le t5.env := E4.trans M4
  have M2 : t2.env.Le t5.env := E3.trans M3
  have M1 : t1.env.Le t5.env := E2.trans M2
  have M0 : t0.env.Le t5.env := E1.trans M1
  have K4 : t4.nv ≤ t5.nv := N5
  have K3 : t3.nv ≤ t5.nv := Nat.le_trans N4 K4
  have K2 : t2.nv ≤ t5.nv := Nat.le_trans N3 K3
  have K1 : t1.nv ≤ t5.nv := Nat.le_trans N2 K2
  have K0 : t0.nv ≤ t5.nv := Nat.le_trans N1 K1
  refine ⟨(⟨acc.1, ⟨ox0, oy0⟩, ⟨ox1, oy1⟩, ⟨ox2, oy2⟩, ⟨ox3, oy3⟩, ⟨ox4, oy4⟩,
      bs[0], bs[1], bs[2], bs[3], bs[4], sl0, sl1, sl2, sl3, sl4, acc.2, nAcc, base⟩,
      (⟨ox4, oy4⟩, nAcc)), t5,
    R0.bind (R1.bind (R2.bind (R3.bind (R4.bind (R5.bind rfl))))),
    fun hnvF hleF =>
      Sat.bind R0 (S0 (Nat.le_trans K0 hnvF) (M0.trans hleF))
        (Sat.bind R1 (S1 (Nat.le_trans K1 hnvF) (M1.trans hleF))
          (Sat.bind R2 (S2 (Nat.le_trans K2 hnvF) (M2.trans hleF))
            (Sat.bind R3 (S3 (Nat.le_trans K3 hnvF) (M3.trans hleF))
              (Sat.bind R4 (S4 (Nat.le_trans K4 hnvF) (M4.trans hleF))
                (Sat.bind R5 (S5 hnvF hleF) Sat.pure))))),
    ⟨⟨Nat.le_trans hnv NA5, hle.trans LA5⟩, C5.2.2.2.1, C5.2.2.2.2, C0.mono K0⟩,
    ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · intro cv hcv
    simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at hcv
    rcases hcv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hbx.mono NA5
    · exact hby.mono NA5
    · exact hax.mono NA5
    · exact hay.mono NA5
    · exact C1.2.2.2.1.mono K1
    · exact C1.2.2.2.2.mono K1
    · exact C2.2.2.2.1.mono K2
    · exact C2.2.2.2.2.mono K2
    · exact C3.2.2.2.1.mono K3
    · exact C3.2.2.2.2.mono K3
    · exact C4.2.2.2.1.mono K4
    · exact C4.2.2.2.2.mono K4
    · exact C5.2.2.2.1
    · exact C5.2.2.2.2
    · exact (hb 0 (by omega)).mono NA5
    · exact (hb 1 (by omega)).mono NA5
    · exact (hb 2 (by omega)).mono NA5
    · exact (hb 3 (by omega)).mono NA5
    · exact (hb 4 (by omega)).mono NA5
    · exact C1.1.mono K1
    · exact C2.1.mono K2
    · exact C3.1.mono K3
    · exact C4.1.mono K4
    · exact C5.1
    · exact han.mono NA5
    · exact C0.mono K0
  · simp only [ScaleRound.read, CVar.val_of_le LA5 hbx, CVar.val_of_le LA5 hby,
      CVar.val_of_le LA5 hax, CVar.val_of_le LA5 hay, CVar.val_of_le LA5 han,
      CVar.val_of_le LA5 (hb 0 (by omega)), CVar.val_of_le LA5 (hb 1 (by omega)),
      CVar.val_of_le LA5 (hb 2 (by omega)), CVar.val_of_le LA5 (hb 3 (by omega)),
      CVar.val_of_le LA5 (hb 4 (by omega)),
      CVar.val_of_le M0 C0, D0,
      CVar.val_of_le M1 C1.2.2.2.1, CVar.val_of_le M1 C1.2.2.2.2, CVar.val_of_le M1 C1.1,
      CVar.val_of_le M2 C2.2.2.2.1, CVar.val_of_le M2 C2.2.2.2.2, CVar.val_of_le M2 C2.1,
      CVar.val_of_le M3 C3.2.2.2.1, CVar.val_of_le M3 C3.2.2.2.2, CVar.val_of_le M3 C3.1,
      CVar.val_of_le M4 C4.2.2.2.1, CVar.val_of_le M4 C4.2.2.2.2, CVar.val_of_le M4 C4.1,
      D1.2.2.2.1, D1.2.2.2.2, D1.1, D2.2.2.2.1, D2.2.2.2.2, D2.1,
      D3.2.2.2.1, D3.2.2.2.2, D3.1, D4.2.2.2.1, D4.2.2.2.2, D4.1,
      D5.2.2.2.1, D5.2.2.2.2, D5.1]
    rw [hW]
    rfl

end VarBaseMul

attribute [irreducible] nAccWit bitWit scaleRound

/-! ## The ladder

The payload reads each round on its own — a `ScaleRound` carries all 26 cells, its outputs
included — so the trace's job is only to say that every round shares the base, opens where
the previous one closed, and starts at the doubled seed. That is what
`Kimchi.Gate.VarBaseMul.Run` asks for.

The loop emits no row of its own, so the ladder's steps owe nothing but readability, and
every row is judged at the one `varBaseMul` constraint after the loop. What discharges it
is the model's `chain_complete` on the honest walk, which the run's readings are shown to
be. -/

/-- What `varBaseMul` hands back (PS's `{ g, lsbBits }` record): the scalar multiple
and the scalar's full bit decomposition, which `scaleFast2` pins. -/
structure VarBaseMulResult (n : ℕ) (F : Type) where
  /-- The computed multiple. -/
  g : AffinePoint (FVar F)
  /-- The scalar's `n` witnessed bits, LSB-first. -/
  lsbBits : Vector (FVar F) n

/-- The variable-base scalar multiplication (PS `varBaseMul`; OCaml
`scale_fast_unpack`): seal the base, witness the scalar's `n` LSB bits, build
`acc = [2]·T` with one `addFast`, walk the top `5 * chunks` bits MSB-first in 5-bit
rows — per row the register witness then five bit-step quintets — pin the final
register to the scalar, and emit one `varBaseMul` constraint. -/
def varBaseMul [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
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

/-- Every round of a trace reads the same base. -/
private theorem threads_base {base : AffinePoint (FVar F)} :
    ∀ {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 5)}
      {rounds : List (ScaleRound F)},
      Chain (Threads base) st pref rounds fin → ∀ r ∈ rounds, r.base = base
  | _, _, [], _, h, r, hr => by rw [h.1] at hr; simp at hr
  | _, _, _ :: _, _, h, r, hr => by
    obtain ⟨r', tail, mid, rfl, hgrant, hrest⟩ := h
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hgrant.1
    · exact threads_base hrest r hr

/-- A trace's first round opens at the seed accumulators. -/
private theorem threads_head {base : AffinePoint (FVar F)} :
    ∀ {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 5)}
      {r₀ : ScaleRound F} {rs : List (ScaleRound F)},
      Chain (Threads base) st pref (r₀ :: rs) fin → r₀.acc0 = st.1 ∧ r₀.nPrev = st.2
  | _, _, [], _, _, h => absurd h.1 (by simp)
  | _, _, _ :: _, _, _, h => by
    obtain ⟨r', tail, mid, heq, hgrant, -⟩ := h
    injection heq with hr _
    subst hr
    exact hgrant.2.1

/-- A trace's rounds link: each opens where the previous closed. -/
private theorem threads_link {base : AffinePoint (FVar F)} :
    ∀ {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 5)}
      {rounds : List (ScaleRound F)},
      Chain (Threads base) st pref rounds fin →
      rounds.IsChain fun a b => b.acc0 = a.acc5 ∧ b.nPrev = a.nNext
  | _, _, [], _, h => by rw [h.1]; simp
  | _, _, _ :: _, _, h => by
    obtain ⟨r, tail, mid, rfl, hgrant, hrest⟩ := h
    refine (threads_link hrest).cons ?_
    cases tail with
    | nil => simp
    | cons r' ts =>
      obtain ⟨hp, hn⟩ := threads_head hrest
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
      exact ⟨by rw [hp, hgrant.2.2.1.1], by rw [hn, hgrant.2.2.1.2]⟩

/-- A trace closes at its last round's outputs. -/
private theorem threads_last {base : AffinePoint (FVar F)} :
    ∀ {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 5)}
      {r₀ : ScaleRound F} {rs : List (ScaleRound F)},
      Chain (Threads base) st pref (r₀ :: rs) fin →
      ((r₀ :: rs).getLast (by simp)).acc5 = fin.1
        ∧ ((r₀ :: rs).getLast (by simp)).nNext = fin.2
  | _, _, [], _, _, h => absurd h.1 (by simp)
  | _, _, _ :: _, r₀, rs, h => by
    obtain ⟨r, tail, mid, heq, hgrant, hrest⟩ := h
    injection heq with hr ht
    subst hr ht
    cases rs with
    | nil =>
      obtain ⟨-, rfl⟩ := Chain.of_nil_out hrest
      exact hgrant.2.2.1
    | cons r₁ ts =>
      rw [List.getLast_cons (by simp)]
      exact threads_last hrest

/-- A trace's rounds are as many as the rows it traversed. -/
private theorem threads_length {base : AffinePoint (FVar F)} :
    ∀ {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 5)}
      {rounds : List (ScaleRound F)},
      Chain (Threads base) st pref rounds fin → rounds.length = pref.length
  | _, _, [], _, h => by rw [h.1]; rfl
  | _, _, _ :: _, _, h => by
    obtain ⟨r', tail, mid, rfl, -, hrest⟩ := h
    rw [List.length_cons, List.length_cons, threads_length hrest]

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
private theorem threads_rows [Field F] {base : AffinePoint (FVar F)} {V : Valuation F} :
    ∀ {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 5)}
      {rounds : List (ScaleRound F)},
      Chain (Threads base) st pref rounds fin →
      roundBits V rounds
        = pref.flatMap fun w =>
            [w[0].val V, w[1].val V, w[2].val V, w[3].val V, w[4].val V]
  | _, _, [], _, h => by rw [h.1]; rfl
  | _, _, _ :: _, _, h => by
    obtain ⟨r, tail, mid, rfl, hgrant, hrest⟩ := h
    obtain ⟨-, -, -, hb0, hb1, hb2, hb3, hb4⟩ := hgrant
    rw [roundBits, List.flatMap_cons, ← roundBits, threads_rows hrest,
      List.flatMap_cons, hb0, hb1, hb2, hb3, hb4]

open Kimchi.Gate.VarBaseMul (Run runBits bitsRegister bitsVal accX accY accN gateLadder) in
/-- A satisfied trace from the doubled seed is one of the model's runs: `Run.ofList`
takes the trace's readings, `varBaseMul_off` reads the ladder off it under the regime,
and `chain_accN` reads the register. -/
private theorem run_sound [Field F] [DecidableEq F] (d : HasCurve F) (V : Valuation F)
    {base P0 : AffinePoint (FVar F)} {pref : List (Vector (FVar F) 5)}
    {rounds : List (ScaleRound F)} {fin : AffinePoint (FVar F) × FVar F}
    (T : d.W.Point)
    (hthr : Chain (Threads base) (P0, .const 0) pref rounds fin)
    (hpay : ∀ r ∈ rounds, Kimchi.Gate.VarBaseMul.Holds (ScaleRound.read V r))
    (hT : OnCurveAt d.W V base T)
    (hP0 : OnCurveAt d.W V P0 ((2 : ℤ) • T)) :
    (∀ b ∈ roundBits V rounds, b = 0 ∨ b = 1) ∧
      (roundBits V rounds).length = 5 * pref.length ∧
      fin.2.val V = bitsRegister (roundBits V rounds) ∧
      ∀ _ : d.LadderRegime (5 * pref.length)
          (2 * bitsVal (roundBits V rounds) + 2 ^ (5 * pref.length) + 1),
        OnCurveAt d.W V fin.1
          ((2 * bitsVal (roundBits V rounds) + 2 ^ (5 * pref.length) + 1) • T) := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  match hround : rounds, hthr with
  | [], hthr' =>
    obtain ⟨rfl, rfl⟩ := Chain.of_nil_out hthr'
    refine ⟨by simp [roundBits], by simp [roundBits], by simp [roundBits, bitsRegister, CVar.val],
      fun _ => ?_⟩
    simpa [roundBits, bitsVal] using hP0
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
    have hrun : Run d.W T g l.length :=
      Kimchi.Gate.VarBaseMul.Run.ofList d.W T l dflt
        (fun w hw => by
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (hl ▸ hw)
          exact hpay r hr)
        hbaseAll
        (by
          rw [hl]
          refine (List.isChain_map _).mpr ?_
          refine (VarBaseMul.threads_link hthr').imp fun a b hab => ?_
          exact ⟨⟨congrArg (·.val V) (congrArg AffinePoint.x hab.1),
            congrArg (·.val V) (congrArg AffinePoint.y hab.1)⟩,
            congrArg (·.val V) hab.2⟩)
        (by
          obtain ⟨hp0, -⟩ := VarBaseMul.threads_head hthr'
          show Kimchi.Gate.AddComplete.IsPoint d.W (r₀.acc0.x.val V) (r₀.acc0.y.val V) _
          rw [hp0]
          exact hP0)
    -- the run's bit stream is the rounds'
    have hbits : runBits g l.length = roundBits V (r₀ :: rs) := by
      rw [hg, Kimchi.Gate.VarBaseMul.runBits_getD, hl, roundBits, List.flatMap_map]
      rfl
    -- the run closes where the trace does
    obtain ⟨hax, hay, han⟩ :=
      Kimchi.Gate.VarBaseMul.acc_getD_length l (by simp [hl]) dflt
    obtain ⟨hlast5, hlastN⟩ := VarBaseMul.threads_last hthr'
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
    have hreg : fin.2.val V = bitsRegister (roundBits V (r₀ :: rs)) := by
      rw [← hfinn, Kimchi.Gate.VarBaseMul.chain_accN l.length g hrun, hzero, mul_zero,
        zero_add, hbits]
    refine ⟨?_, ?_, hreg, fun hregime => ?_⟩
    · rw [← hbits]
      exact Kimchi.Gate.VarBaseMul.runBits_bool l.length g hrun.holds
    · rw [← VarBaseMul.threads_length hthr', roundBits, List.length_flatMap]
      simp
      omega
    · rw [← hlen] at hregime ⊢
      simp only [HasCurve.LadderRegime] at hregime
      have hs : gateLadder g (5 * l.length)
          = 2 * bitsVal (roundBits V (r₀ :: rs)) + 2 ^ (5 * l.length) + 1 := by
        rw [Kimchi.Gate.VarBaseMul.gateLadder_eq_register,
          Kimchi.Gate.VarBaseMul.gateRegister_eq_bitsVal, hbits]
      obtain ⟨hfin', hpt, -⟩ :=
        Kimchi.Gate.VarBaseMul.varBaseMul_off d.W l.length g T
          (gateLadder g (5 * l.length)) hrun d.two_ne d.odd rfl (by rw [hs]; exact hregime)
      have hns : d.W.Nonsingular (fin.1.x.val V) (fin.1.y.val V) := by
        rw [← hfinx, ← hfiny]
        exact hfin'
      refine ⟨hns, ?_⟩
      rw [← hs, ← hpt]
      congr 1

/-- The trace's readings are the model's honest walk: round `i` reads as `chainBuild`'s
row `i`, from the accumulator the trace opened on and the bits it was handed. -/
private theorem grants_walk [Field F] [DecidableEq F] (base : AffinePoint (FVar F))
    (stf : ProverState F) :
    ∀ {bs : ℕ → F} {acc fin : AffinePoint (FVar F) × FVar F}
      {pref : List (Vector (FVar F) 5)} {rounds : List (ScaleRound F)},
      ChainAt (RowGrant base) stf acc pref rounds fin →
      (∀ i (hi : i < pref.length) (j : ℕ) (hj : j < 5),
        bs (5 * i + j) = ((pref[i]'hi)[j]'hj).val stf.env.get) →
      ∀ i (hi : i < rounds.length),
        ScaleRound.read stf.env.get (rounds[i]'hi)
          = Kimchi.Gate.VarBaseMul.chainBuild (base.x.val stf.env.get)
              (base.y.val stf.env.get) (acc.1.x.val stf.env.get) (acc.1.y.val stf.env.get)
              (acc.2.val stf.env.get) bs i
  | _, _, _, [], _, h, _, i, hi => by
    obtain ⟨rfl, -⟩ := h
    simp at hi
  | bs, acc, fin, x :: rest, rounds, h, hbits, i, hi => by
    obtain ⟨r, tail, mid, rfl, ⟨⟨-, -, ⟨hr5, hrnn⟩, -⟩, -, hread⟩, hrest⟩ := h
    have h0 : ∀ (j : ℕ) (hj : j < 5), bs j = ((x[j]'hj)).val stf.env.get := by
      intro j hj
      have hb := hbits 0 (by simp) j hj
      simpa using hb
    have hrow : ScaleRound.read stf.env.get r
        = Kimchi.Gate.VarBaseMul.chainBuild (base.x.val stf.env.get)
            (base.y.val stf.env.get) (acc.1.x.val stf.env.get) (acc.1.y.val stf.env.get)
            (acc.2.val stf.env.get) bs 0 := by
      rw [hread]
      show _ = Kimchi.Gate.VarBaseMul.build _ _ _ _ _ (bs 0) (bs 1) (bs 2) (bs 3) (bs 4)
      rw [h0 0 (by omega), h0 1 (by omega), h0 2 (by omega), h0 3 (by omega),
        h0 4 (by omega)]
    cases i with
    | zero => exact hrow
    | succ j =>
      have hj : j < tail.length := by simpa using hi
      have hshift := grants_walk base stf (bs := fun n => bs (n + 5)) hrest
        (fun k hk t ht => by
          have hb := hbits (k + 1) (by simpa using hk) t ht
          rw [show 5 * (k + 1) + t = 5 * k + t + 5 from by omega] at hb
          simp only [List.getElem_cons_succ] at hb
          exact hb)
        j hj
      have hmx : mid.1.x.val stf.env.get
          = (Kimchi.Gate.VarBaseMul.chainBuild (base.x.val stf.env.get)
              (base.y.val stf.env.get) (acc.1.x.val stf.env.get) (acc.1.y.val stf.env.get)
              (acc.2.val stf.env.get) bs 0).x5 := by
        rw [← hrow]
        show _ = r.acc5.x.val stf.env.get
        rw [hr5]
      have hmy : mid.1.y.val stf.env.get
          = (Kimchi.Gate.VarBaseMul.chainBuild (base.x.val stf.env.get)
              (base.y.val stf.env.get) (acc.1.x.val stf.env.get) (acc.1.y.val stf.env.get)
              (acc.2.val stf.env.get) bs 0).y5 := by
        rw [← hrow]
        show _ = r.acc5.y.val stf.env.get
        rw [hr5]
      have hmn : mid.2.val stf.env.get
          = (Kimchi.Gate.VarBaseMul.chainBuild (base.x.val stf.env.get)
              (base.y.val stf.env.get) (acc.1.x.val stf.env.get) (acc.1.y.val stf.env.get)
              (acc.2.val stf.env.get) bs 0).nPrime := by
        rw [← hrow]
        show _ = r.nNext.val stf.env.get
        rw [hrnn]
      rw [show ((r :: tail)[j + 1]'hi) = tail[j]'hj from rfl, hshift,
        Kimchi.Gate.VarBaseMul.chainBuild_shift, hmx, hmy, hmn]

/-- A trace's grants carry its wiring: the state-free chain the sound side speaks. -/
private theorem ChainAt.threads [Field F] [DecidableEq F] {base : AffinePoint (FVar F)}
    {stf : ProverState F} :
    ∀ {acc fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 5)}
      {rounds : List (ScaleRound F)},
      ChainAt (RowGrant base) stf acc pref rounds fin →
      Chain (Threads base) acc pref rounds fin
  | _, _, [], _, h => ⟨h.1, h.2⟩
  | _, _, _ :: _, _, h => by
    obtain ⟨r, tail, mid, rfl, hg, hrest⟩ := h
    exact ⟨r, tail, mid, rfl, hg.1, ChainAt.threads hrest⟩

end VarBaseMul

open Std.Do WeierstrassCurve.Affine in
/-- **Soundness.** Any satisfying valuation reads the result as the base multiplied by
the Type1 decode of the scalar's own bits — under the ladder's regime, which is what
prices the ladder's non-degeneracy. -/
theorem varBaseMul_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (d : HasCurve F) (n chunks : ℕ) (hn : 5 * chunks ≤ n)
    (base : AffinePoint (FVar F)) (scalar : Type1 (FVar F)) :
    ⦃⌜True⌝⦄
    varBaseMul (c := Builder V (KimchiConstraint F)) n chunks base scalar
    ⦃⇓ r _ => ⌜∀ T : d.W.Point, OnCurveAt d.W V base T →
      ∃ bits : List F,
        (∀ b ∈ bits, b = 0 ∨ b = 1) ∧ bits.length = 5 * chunks ∧
        bits = ((r.lsbBits.toList.take (5 * chunks)).reverse).map (·.val V) ∧
        scalar.val.val V = Kimchi.Gate.VarBaseMul.bitsRegister bits ∧
        ∀ _ : d.LadderRegime (5 * chunks)
            (2 * Kimchi.Gate.VarBaseMul.bitsVal bits + 2 ^ (5 * chunks) + 1),
          OnCurveAt d.W V r.g
            ((2 * Kimchi.Gate.VarBaseMul.bitsVal bits + 2 ^ (5 * chunks) + 1) • T)⌝⦄ := by
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
  obtain ⟨hbool, hlen, hreg, hpoint⟩ := VarBaseMul.run_sound d V T hchain hpay hTs hP0
  -- the rounds' bits are the windows', and the windows flatten to the reversed prefix
  have hmsb : ((bits.toList.take (5 * chunks)).reverse).length = 5 * chunks := by
    simp only [List.length_reverse, List.length_take, Vector.length_toList]
    omega
  have hbits : VarBaseMul.roundBits V loop.1
      = (((bits.toList.take (5 * chunks)).reverse).map (·.val V)) := by
    rw [VarBaseMul.threads_rows hchain, List.flatMap_map]
    exact VarBaseMul.flatMap_window_map (·.val V) (CVar.const 0) chunks _ hmsb

  have hpreflen : ((List.range chunks).map fun i =>
      (Vector.ofFn fun j : Fin 5 =>
        ((bits.toList.take (5 * chunks)).reverse).getD (5 * i + j.1)
          (CVar.const 0))).length = chunks := by simp
  refine ⟨VarBaseMul.roundBits V loop.1, hbool, ?_, hbits, ?_, ?_⟩
  · rw [hlen, hpreflen]
  · rw [← hpin, hreg]
  · intro hregime
    rw [hpreflen] at hpoint
    exact hpoint hregime

open WeierstrassCurve.Affine in
/-- **Completeness.** From a readable on-curve base and a scalar inside the ladder's
width, the honest run succeeds, its rows hold at every extension, and the result reads
as the base multiplied by the Type1 unshift of the scalar's own bits. -/
theorem varBaseMul_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (d : HasCurve F) (n chunks : ℕ) (hn : 5 * chunks ≤ n)
    (base : AffinePoint (FVar F)) (scalar : Type1 (FVar F))
    (xv yv sv : F) (hT : d.W.Nonsingular xv yv)
    (hfits : ToNat.toNat sv < 2 ^ (5 * chunks))
    (hregime : d.LadderRegime (5 * chunks)
      (2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks) + 1)) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => base.x.Scoped st ∧ base.y.Scoped st ∧ scalar.val.Scoped st ∧
        base.x.val st.env.get = xv ∧ base.y.val st.env.get = yv ∧
        scalar.val.val st.env.get = sv)
      (varBaseMul (c := KimchiConstraint F) n chunks base scalar)
      (fun r st' =>
        (∀ (i : ℕ) (hi : i < n), (r.lsbBits[i]'hi).Scoped st' ∧
          (r.lsbBits[i]'hi).val st'.env.get
            = if (ToNat.toNat sv).testBit i then 1 else 0) ∧
        OnCurve d.W st' r.g
          ((2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks) + 1) • Point.some _ _ hT)) := by
  rintro st ⟨hbx, hby, hscS, hrx, hry, hrs⟩
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  -- the sealed base
  obtain ⟨sealed, st₁, hrun₁, hsat₁, hRx, hRy⟩ :=
    sealPoint_complete (c := KimchiConstraint F) base xv yv st
      ⟨⟨CircuitType.scoped_fvar.mpr hbx, CircuitType.reads_fvar.mpr hrx⟩,
        ⟨CircuitType.scoped_fvar.mpr hby, CircuitType.reads_fvar.mpr hry⟩⟩
  have hle₁ := hrun₁.le
  have hnv₁ := hrun₁.nv_le
  have hsx : sealed.x.Scoped st₁ := CircuitType.scoped_fvar.mp hRx.1
  have hsy : sealed.y.Scoped st₁ := CircuitType.scoped_fvar.mp hRy.1
  have hsxv : sealed.x.val st₁.env.get = xv := CircuitType.reads_fvar.mp hRx.2
  have hsyv : sealed.y.val st₁.env.get = yv := CircuitType.reads_fvar.mp hRy.2
  -- the scalar's bits, in one witness
  obtain ⟨bits, st₂, hrun₂, hsat₂, hnv₂, hle₂, hscB, hrdB⟩ :=
    witness_complete (c := KimchiConstraint F) (val := Vector F n)
      (lsbBitsWit n scalar.val) (st := st₁)
      (v := Vector.ofFn fun i : Fin n => if (ToNat.toNat sv).testBit i.1 then 1 else 0)
      (by
        simp only [lsbBitsWit, AsProver.bind_eq, AsProver.run_bind,
          AsProver.readCVar_run (hscS.mono hnv₁), CVar.val_of_le hle₁ hscS, hrs, Except.bind]
        rfl)
  rw [CircuitType.scoped_vector] at hscB
  rw [CircuitType.reads_vector] at hrdB
  -- the doubled seed
  have hTread : OnCurve d.W st₂ sealed (Point.some _ _ hT) := by
    refine ⟨scoped_affinePoint.mpr ⟨hsx.mono hnv₂, hsy.mono hnv₂⟩, ?_⟩
    show ∃ h : d.W.Nonsingular (sealed.x.val st₂.env.get) (sealed.y.val st₂.env.get), _
    rw [CVar.val_of_le hle₂ hsx, CVar.val_of_le hle₂ hsy, hsxv, hsyv]
    exact ⟨hT, rfl⟩
  have h2T : Point.some _ _ hT + Point.some _ _ hT ≠ 0 :=
    d.two_torsion_free _ (Point.some_ne_zero hT)
  obtain ⟨p, st₃, hrun₃, hsat₃, ⟨hscP, hscI⟩, hadd⟩ :=
    Complete.post (g := addFast (c := KimchiConstraint F) .checkFinite sealed sealed)
      (fun V => addFast_spec (V := V) .checkFinite d.W
        ⟨d.short.1, d.short.2.1, d.short.2.2.1, d.short.2.2.2⟩ d.two_ne sealed sealed)
      (addFast_complete .checkFinite d.W
        ⟨d.short.1, d.short.2.1, d.short.2.2.1, d.short.2.2.2⟩ d.two_ne sealed sealed
        (Point.some _ _ hT) (Point.some _ _ hT)) st₂
      ⟨hTread, hTread, h2T, fun _ => h2T⟩
  have hle₃ := hrun₃.le
  have hnv₃ := hrun₃.nv_le
  have hP0read : OnCurve d.W st₃ p.p ((2 : ℤ) • Point.some _ _ hT) := by
    refine ⟨hscP, ?_⟩
    rw [two_zsmul]
    rcases hadd.2 _ _ (hTread.mono hnv₃ hle₃).2 (hTread.mono hnv₃ hle₃).2 h2T with
      ⟨hinf, -⟩ | ⟨-, h3⟩
    · exact absurd ((hadd.1 rfl).symm.trans hinf) (by norm_num)
    · exact h3
  rw [scoped_affinePoint] at hscP
  obtain ⟨hP0ns, hP0eq⟩ := hP0read.2
  have hsx₃ : sealed.x.Scoped st₃ := hsx.mono (Nat.le_trans hnv₂ hnv₃)
  have hsy₃ : sealed.y.Scoped st₃ := hsy.mono (Nat.le_trans hnv₂ hnv₃)
  have hsxv₃ : sealed.x.val st₃.env.get = xv := by
    rw [CVar.val_of_le (hle₂.trans hle₃) hsx, hsxv]
  have hsyv₃ : sealed.y.val st₃.env.get = yv := by
    rw [CVar.val_of_le (hle₂.trans hle₃) hsy, hsyv]
  -- the rows' bits: the reversed prefix of the scalar's bits, MSB-first
  set bsOf : ℕ → F := fun k =>
    if (ToNat.toNat sv).testBit (5 * chunks - 1 - k) then 1 else 0 with hbsOf
  set msb : List (FVar F) := (bits.toList.take (5 * chunks)).reverse with hmsb
  set window : ℕ → Vector (FVar F) 5 := fun i =>
    Vector.ofFn fun j : Fin 5 => msb.getD (5 * i + j.1) (CVar.const 0) with hwindow
  have hmsblen : msb.length = 5 * chunks := by
    rw [hmsb]
    simp only [List.length_reverse, List.length_take, Vector.length_toList]
    omega
  have hentry : ∀ (k : ℕ) (hk : k < 5 * chunks),
      msb.getD k (CVar.const 0) = bits[5 * chunks - 1 - k]'(by omega) := by
    intro k hk
    rw [List.getD_eq_getElem _ _ (by rw [hmsblen]; exact hk)]
    simp only [hmsb, List.getElem_reverse, List.getElem_take, Vector.getElem_toList,
      List.length_take, Vector.length_toList]
    congr 1
    omega
  have hbitSc : ∀ (k : ℕ), k < 5 * chunks → (msb.getD k (CVar.const 0)).Scoped st₂ := by
    intro k hk
    rw [hentry k hk]
    exact CircuitType.scoped_fvar.mp (hscB _ _)
  have hbitVal : ∀ (stf : ProverState F), st₂.env.Le stf.env →
      ∀ (k : ℕ), k < 5 * chunks →
        (msb.getD k (CVar.const 0)).val stf.env.get = bsOf k := by
    intro stf hlef k hk
    rw [hentry k hk, CVar.val_of_le hlef (CircuitType.scoped_fvar.mp (hscB _ _)),
      CircuitType.reads_fvar.mp (hrdB _ _), hbsOf]
    simp
  -- the ladder
  have hP : ∀ x ∈ (List.range chunks).map window, VarBaseMul.BitRow st₂ x := by
    intro x hx v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hv)
    have hi' : i < chunks := by simpa using hi
    simp only [hwindow, Vector.getElem_ofFn]
    exact hbitSc (5 * i + j) (by omega)
  obtain ⟨loop, st₄, hrun₄, hsat₄, hinv₄, hchainAt⟩ :=
    mapAccumM_complete (F := F) (c := KimchiConstraint F)
      (scaleRound sealed) (VarBaseMul.BitRow st₂) (fun _ => VarBaseMul.AccInv st₂)
      (VarBaseMul.RowGrant sealed) (fun _ => VarBaseMul.AccInv.mono)
      (VarBaseMul.RowGrant.mono sealed)
      (fun acc x _ hx => VarBaseMul.scaleRound_complete st₂ sealed
        ⟨hsx.mono hnv₂, hsy.mono hnv₂⟩ acc x hx)
      (p.p, CVar.const 0) ((List.range chunks).map window) hP st₃
      ⟨⟨hnv₃, hle₃⟩, hscP.1, hscP.2, trivial⟩
  obtain ⟨rounds, fin⟩ := loop
  have hle₄ := hrun₄.le
  have hnv₄ := hrun₄.nv_le
  have hpreflen : ((List.range chunks).map window).length = chunks := by simp
  have hlenR : rounds.length = chunks := by
    rw [ChainAt.length hchainAt, hpreflen]
  -- the honest walk
  set W : ℕ → Kimchi.Gate.VarBaseMul.Witness F :=
    Kimchi.Gate.VarBaseMul.chainBuild xv yv (p.p.x.val st₃.env.get)
      (p.p.y.val st₃.env.get) 0 bsOf with hWdef
  have hWat : ∀ (stf : ProverState F), st₃.env.Le stf.env →
      Kimchi.Gate.VarBaseMul.chainBuild (sealed.x.val stf.env.get)
          (sealed.y.val stf.env.get)
          ((p.p, (CVar.const 0 : FVar F)).1.x.val stf.env.get)
          ((p.p, (CVar.const 0 : FVar F)).1.y.val stf.env.get)
          ((p.p, (CVar.const 0 : FVar F)).2.val stf.env.get) bsOf = W := by
    intro stf hlef
    show Kimchi.Gate.VarBaseMul.chainBuild (sealed.x.val stf.env.get)
      (sealed.y.val stf.env.get) (p.p.x.val stf.env.get) (p.p.y.val stf.env.get)
      ((CVar.const 0 : FVar F).val stf.env.get) bsOf = _
    rw [CVar.val_of_le hlef hsx₃, CVar.val_of_le hlef hsy₃, hsxv₃, hsyv₃,
      CVar.val_of_le hlef hscP.1, CVar.val_of_le hlef hscP.2, hWdef]
    rfl
  have hbsbool : ∀ j : ℕ, j < 5 * chunks → bsOf j = 0 ∨ bsOf j = 1 := by
    intro j _
    simp only [hbsOf]
    split <;> simp
  have hgl : Kimchi.Gate.VarBaseMul.gateLadder W (5 * chunks)
      = 2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks) + 1 := by
    rw [Kimchi.Gate.VarBaseMul.gateLadder_eq_register,
      Kimchi.Gate.VarBaseMul.gateRegister_eq_bitsVal, hWdef,
      Kimchi.Gate.VarBaseMul.runBits_chainBuild, hbsOf,
      Kimchi.Gate.VarBaseMul.bitsVal_testBit (ToNat.toNat sv) (5 * chunks) hfits]
  have hwalkHolds : ∀ i : ℕ, i < chunks → Kimchi.Gate.VarBaseMul.Holds (W i) := by
    have h := Kimchi.Gate.VarBaseMul.chain_complete d.W d.two_ne d.odd chunks hT bsOf
      hbsbool 0 hP0ns hP0eq.symm (by rw [← hWdef, hgl]; exact hregime)
    rw [← hWdef] at h
    exact h
  -- the rounds' readings are the walk's rows, at any table past the bits
  have hbitsRead : ∀ (stf : ProverState F), st₂.env.Le stf.env →
      ∀ (i : ℕ) (hi : i < ((List.range chunks).map window).length) (j : ℕ) (hj : j < 5),
        bsOf (5 * i + j)
          = ((((List.range chunks).map window)[i]'hi)[j]'hj).val stf.env.get := by
    intro stf hlef i hi j hj
    have hi' : i < chunks := by simpa using hi
    have hw : (((List.range chunks).map window)[i]'hi) = window i := by
      simp
    rw [hw]
    simp only [hwindow, Vector.getElem_ofFn]
    exact (hbitVal stf hlef (5 * i + j) (by omega)).symm
  have hpayAt : ∀ (stf : ProverState F), st₄.nv ≤ stf.nv → st₄.env.Le stf.env →
      ∀ r ∈ rounds, Kimchi.Gate.VarBaseMul.Holds (ScaleRound.read stf.env.get r) := by
    intro stf hnvF hleF r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    rw [VarBaseMul.grants_walk sealed stf
        (ChainAt.mono (VarBaseMul.RowGrant.mono sealed) hnvF hleF hchainAt)
        (fun k hk t ht => hbitsRead stf (hle₃.trans (hle₄.trans hleF)) k hk t ht) i hi,
      hWat stf (hle₄.trans hleF)]
    exact hwalkHolds i (by rw [← hlenR]; exact hi)
  -- the trace's wiring, and the register it ends on
  have hchain : Chain (VarBaseMul.Threads sealed) (p.p, CVar.const 0)
      ((List.range chunks).map window) rounds fin := VarBaseMul.ChainAt.threads hchainAt
  have hroundBits : ∀ (stf : ProverState F), st₂.env.Le stf.env →
      VarBaseMul.roundBits stf.env.get rounds = (List.range (5 * chunks)).map bsOf := by
    intro stf hlef
    rw [VarBaseMul.threads_rows hchain, List.flatMap_map,
      ← Kimchi.Gate.VarBaseMul.flatMap_range_window bsOf chunks]
    refine List.flatMap_congr fun i hi => ?_
    have hi' : i < chunks := by simpa using hi
    simp only [hwindow, Vector.getElem_ofFn, Nat.add_zero]
    rw [hbitVal stf hlef (5 * i) (by omega), hbitVal stf hlef (5 * i + 1) (by omega),
      hbitVal stf hlef (5 * i + 2) (by omega), hbitVal stf hlef (5 * i + 3) (by omega),
      hbitVal stf hlef (5 * i + 4) (by omega)]
  have hregSv : Kimchi.Gate.VarBaseMul.bitsRegister ((List.range (5 * chunks)).map bsOf)
      = sv := by
    rw [Kimchi.Gate.VarBaseMul.bitsRegister_eq_cast _ (by
        intro b hb
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
        exact hbsbool j (List.mem_range.mp hj)), hbsOf,
      Kimchi.Gate.VarBaseMul.bitsVal_testBit (ToNat.toNat sv) (5 * chunks) hfits,
      Int.cast_natCast, LawfulToNat.cast_toNat]
  have hTs : ∀ (stf : ProverState F), st₂.nv ≤ stf.nv → st₂.env.Le stf.env →
      OnCurveAt d.W stf.env.get sealed (Point.some _ _ hT) :=
    fun stf hnvF hleF => (hTread.mono hnvF hleF).2
  have hP0s : ∀ (stf : ProverState F), st₃.nv ≤ stf.nv → st₃.env.Le stf.env →
      OnCurveAt d.W stf.env.get p.p ((2 : ℤ) • Point.some _ _ hT) :=
    fun stf hnvF hleF => (hP0read.mono hnvF hleF).2
  obtain ⟨-, -, hreg₄, -⟩ :=
    VarBaseMul.run_sound d st₄.env.get (Point.some _ _ hT) hchain
      (hpayAt st₄ (Nat.le_refl _) (Assignments.Le.refl _))
      (hTs st₄ (Nat.le_trans hnv₃ hnv₄) (hle₃.trans hle₄))
      (hP0s st₄ hnv₄ hle₄)
  -- the register pin
  have hscS₄ : scalar.val.Scoped st₄ :=
    hscS.mono (Nat.le_trans hnv₁ (Nat.le_trans hnv₂ (Nat.le_trans hnv₃ hnv₄)))
  have hpin : fin.2.val st₄.env.get = scalar.val.val st₄.env.get := by
    rw [hreg₄, hroundBits st₄ (hle₃.trans hle₄), hregSv,
      CVar.val_of_le ((hle₁.trans hle₂).trans (hle₃.trans hle₄)) hscS, hrs]
  obtain ⟨u, st₅, hrun₅, hsat₅, -⟩ :=
    assertEqual_complete (c := KimchiConstraint F) fin.2 scalar.val
      (scalar.val.val st₄.env.get) st₄
      ⟨⟨CircuitType.scoped_fvar.mpr hinv₄.2.2.2, CircuitType.reads_fvar.mpr hpin⟩,
        ⟨CircuitType.scoped_fvar.mpr hscS₄, CircuitType.reads_fvar.mpr rfl⟩⟩
  have hle₅ := hrun₅.le
  have hnv₅ := hrun₅.nv_le
  refine ⟨⟨fin.1, bits⟩, st₅,
    hrun₁.bind (hrun₂.bind (hrun₃.bind (hrun₄.bind
      (Runs.addConstraint.bind (hrun₅.bind rfl))))), ?_, ?_, ?_⟩
  · intro stf hnvF hleF
    have hnv₄f : st₄.nv ≤ stf.nv := Nat.le_trans hnv₅ hnvF
    have hle₄f : st₄.env.Le stf.env := hle₅.trans hleF
    refine Sat.bind hrun₁ (hsat₁ ?_ ?_) (Sat.bind hrun₂ (hsat₂ ?_ ?_)
      (Sat.bind hrun₃ (hsat₃ ?_ ?_) (Sat.bind hrun₄ (hsat₄ hnv₄f hle₄f)
        (Sat.bind Runs.addConstraint (Sat.addConstraint (hpayAt stf hnv₄f hle₄f))
          (Sat.bind hrun₅ (hsat₅ hnvF hleF) Sat.pure)))))
    · exact Nat.le_trans (Nat.le_trans hnv₂ (Nat.le_trans hnv₃ hnv₄)) hnv₄f
    · exact ((hle₂.trans hle₃).trans hle₄).trans hle₄f
    · exact Nat.le_trans (Nat.le_trans hnv₃ hnv₄) hnv₄f
    · exact (hle₃.trans hle₄).trans hle₄f
    · exact Nat.le_trans hnv₄ hnv₄f
    · exact hle₄.trans hle₄f
  · -- the bits read as the scalar's own
    intro i hi
    refine ⟨CircuitType.scoped_fvar.mp ((hscB i hi).mono (Nat.le_trans hnv₃
      (Nat.le_trans hnv₄ hnv₅))), ?_⟩
    rw [CVar.val_of_le ((hle₃.trans hle₄).trans hle₅)
      (CircuitType.scoped_fvar.mp (hscB i hi)),
      CircuitType.reads_fvar.mp (hrdB i hi)]
    simp
  · -- the point conclusion, off the sound side's own reading of the trace
    obtain ⟨-, -, -, hpoint⟩ :=
      VarBaseMul.run_sound d st₅.env.get (Point.some _ _ hT) hchain
        (hpayAt st₅ hnv₅ hle₅)
        (hTs st₅ (Nat.le_trans hnv₃ (Nat.le_trans hnv₄ hnv₅))
          (hle₃.trans (hle₄.trans hle₅)))
        (hP0s st₅ (Nat.le_trans hnv₄ hnv₅) (hle₄.trans hle₅))
    rw [hroundBits st₅ (hle₃.trans (hle₄.trans hle₅)), hpreflen] at hpoint
    rw [hbsOf, Kimchi.Gate.VarBaseMul.bitsVal_testBit (ToNat.toNat sv) (5 * chunks) hfits]
      at hpoint
    exact ⟨scoped_affinePoint.mpr ⟨hinv₄.2.1.mono hnv₅, hinv₄.2.2.1.mono hnv₅⟩,
      hpoint hregime⟩

attribute [irreducible] lsbBitsWit varBaseMul

/-! ## `scaleFast1` -/

/-- `scaleFast1 g a ~ [fromShifted a]·g` (PS docstring) — the `Type1` path, for a
scalar field no larger than the circuit field. Drops the bits. -/
def scaleFast1 [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (n chunks : ℕ) (p : AffinePoint (FVar F))
    (t : Type1 (FVar F)) : CircuitM F c (AffinePoint (FVar F)) := do
  let r ← varBaseMul n chunks p t
  pure r.g

open Std.Do WeierstrassCurve.Affine in
/-- **Soundness** (`scaleFast1`). The ladder's statement in scalar currency: the result
is the base multiplied by the Type1 unshift of an integer in the ladder's range that
the scalar reads as. The bit list `varBaseMul` returns is what pins that integer; the
wrapper drops it, so its law speaks of the integer alone. -/
theorem scaleFast1_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (d : HasCurve F) (n chunks : ℕ) (hn : 5 * chunks ≤ n)
    (base : AffinePoint (FVar F)) (scalar : Type1 (FVar F)) :
    ⦃⌜True⌝⦄
    scaleFast1 (c := Builder V (KimchiConstraint F)) n chunks base scalar
    ⦃⇓ r _ => ⌜∀ T : d.W.Point, OnCurveAt d.W V base T →
      ∃ z : ℤ, 0 ≤ z ∧ z < 2 ^ (5 * chunks) ∧ (z : F) = scalar.val.val V ∧
        ∀ _ : d.LadderRegime (5 * chunks) (2 * z + 2 ^ (5 * chunks) + 1),
          OnCurveAt d.W V r ((2 * z + 2 ^ (5 * chunks) + 1) • T)⌝⦄ := by
  have hvbm := fun (V : Valuation F) => varBaseMul_spec (V := V) d n chunks hn base scalar
  unfold scaleFast1
  mvcgen [hvbm]
  rename_i r _ hr
  intro T hT
  obtain ⟨bits, hbool, hlen, -, hreg, hpoint⟩ := hr T hT
  obtain ⟨hlt, hnonneg⟩ := Kimchi.Gate.VarBaseMul.bitsVal_lt bits hbool
  refine ⟨Kimchi.Gate.VarBaseMul.bitsVal bits, hnonneg, by rw [← hlen]; exact hlt, ?_, hpoint⟩
  rw [hreg, Kimchi.Gate.VarBaseMul.bitsRegister_eq_cast bits hbool]

open WeierstrassCurve.Affine in
/-- **Completeness** (`scaleFast1`). `varBaseMul`'s honest run, with the bits dropped. -/
theorem scaleFast1_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (d : HasCurve F) (n chunks : ℕ) (hn : 5 * chunks ≤ n)
    (base : AffinePoint (FVar F)) (scalar : Type1 (FVar F)) (xv yv sv : F)
    (hT : d.W.Nonsingular xv yv) (hfits : ToNat.toNat sv < 2 ^ (5 * chunks))
    (hregime : d.LadderRegime (5 * chunks)
      (2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks) + 1)) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => base.x.Scoped st ∧ base.y.Scoped st ∧ scalar.val.Scoped st ∧
        base.x.val st.env.get = xv ∧ base.y.val st.env.get = yv ∧
        scalar.val.val st.env.get = sv)
      (scaleFast1 (c := KimchiConstraint F) n chunks base scalar)
      (fun r st' => OnCurve d.W st' r
        ((2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks) + 1) • Point.some _ _ hT)) := by
  intro st hst
  obtain ⟨r, st₁, hrun, hsat, -, hpt⟩ :=
    varBaseMul_complete d n chunks hn base scalar xv yv sv hT hfits hregime st hst
  exact ⟨r.g, st₁, hrun.bind rfl, fun hnv hle => Sat.bind hrun (hsat hnv hle) Sat.pure, hpt⟩

attribute [irreducible] scaleFast1

/-! ## `scaleFast2` -/

/-- `scaleFast2 g (sDiv2, sOdd) ~ [2·sDiv2 + sOdd + 2^n]·g` — the split path, for a
scalar field larger than the circuit field: run the ladder on `sDiv2`, pin its high
bits to zero, and fold the parity in by conditionally subtracting the base. -/
def scaleFast2 [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (n chunks sDiv2Bits : ℕ) (base : AffinePoint (FVar F))
    (sDiv2 : FVar F) (sOdd : BoolVar F) : CircuitM F c (AffinePoint (FVar F)) := do
  let r ← varBaseMul n chunks base ⟨sDiv2⟩
  (r.lsbBits.toList.drop sDiv2Bits).forM fun bit => assertEqual bit (.const 0)
  -- the else branch first (PS `if_ sOdd g =<< …`): `g − base` via the pure negation
  let negBase : AffinePoint (FVar F) := ⟨base.x, CVar.negate_ base.y⟩
  let q ← addFast .checkFinite r.g negBase
  -- the point conditional selects coordinatewise, `y` BEFORE `x`: PS's record `if_`
  -- builds right-to-left (the fixture pins the emission order)
  let y ← select sOdd r.g.y q.p.y
  let x ← select sOdd r.g.x q.p.x
  pure ⟨x, y⟩

open Std.Do WeierstrassCurve.Affine in
/-- **Soundness** (`scaleFast2`). -/
theorem scaleFast2_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (d : HasCurve F) (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n)
    (hsplit : sDiv2Bits ≤ 5 * chunks)
    (base : AffinePoint (FVar F)) (sDiv2 : FVar F) (sOdd : BoolVar F) :
    ⦃⌜True⌝⦄
    scaleFast2 (c := Builder V (KimchiConstraint F)) n chunks sDiv2Bits base sDiv2 sOdd
    ⦃⇓ r _ => ⌜∀ T : d.W.Point, OnCurveAt d.W V base T → ∀ bb : Bool,
      (↑sOdd : CVar F).val V = bit bb →
      ∃ z : ℤ, 0 ≤ z ∧ z < 2 ^ sDiv2Bits ∧ (z : F) = sDiv2.val V ∧
        ∀ _ : d.LadderRegime (5 * chunks) (2 * z + 2 ^ (5 * chunks) + 1),
          OnCurveAt d.W V r
            ((2 * z + (if bb then 1 else 0) + 2 ^ (5 * chunks)) • T)⌝⦄ := by
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
  obtain ⟨bits, hbool, hlen, hbitsEq, hreg, hpoint⟩ := hvb T hT
  obtain ⟨hlt, hnonneg⟩ := Kimchi.Gate.VarBaseMul.bitsVal_lt bits hbool
  -- the pinned high bits: the ladder's integer fits the split's width
  have hzeros : ∀ b ∈ bits.take (5 * chunks - sDiv2Bits), b = 0 := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have hik : i < 5 * chunks - sDiv2Bits := by
      simp only [List.length_take, hlen] at hi
      omega
    have hilen : i < bits.length := by rw [hlen]; omega
    simp only [List.getElem_take]
    have hidx : 5 * chunks - 1 - i < n := by omega
    have hge : sDiv2Bits ≤ 5 * chunks - 1 - i := by omega
    have hmem : rvb.lsbBits.toList[5 * chunks - 1 - i]'(by simpa using hidx)
        ∈ rvb.lsbBits.toList.drop sDiv2Bits := by
      have hlend : sDiv2Bits + (5 * chunks - 1 - i - sDiv2Bits) = 5 * chunks - 1 - i := by omega
      have heq : (rvb.lsbBits.toList.drop sDiv2Bits)[5 * chunks - 1 - i - sDiv2Bits]'(by
          simp only [List.length_drop, Vector.length_toList]; omega)
          = rvb.lsbBits.toList[5 * chunks - 1 - i]'(by simpa using hidx) := by
        rw [List.getElem_drop]
        congr 1
      rw [← heq]
      exact List.getElem_mem _
    simp only [hbitsEq, List.getElem_map, List.getElem_reverse, List.length_reverse, List.length_take,
      Vector.length_toList, List.getElem_take]
    simp only [show min (5 * chunks) n = 5 * chunks from by omega]
    rw [hpin0 _ hmem]
    simp [CVar.val]
  have hdroplen : (bits.drop (5 * chunks - sDiv2Bits)).length = sDiv2Bits := by
    rw [List.length_drop, hlen]
    omega
  have hltSplit : Kimchi.Gate.VarBaseMul.bitsVal bits < 2 ^ sDiv2Bits := by
    have h := (Kimchi.Gate.VarBaseMul.bitsVal_lt (bits.drop (5 * chunks - sDiv2Bits))
      (fun b hb => hbool b (List.mem_of_mem_drop hb))).1
    rw [hdroplen] at h
    rw [Kimchi.Gate.VarBaseMul.bitsVal_drop_of_zeros bits _ hzeros]
    exact h
  refine ⟨Kimchi.Gate.VarBaseMul.bitsVal bits, hnonneg, hltSplit, ?_, ?_⟩
  · rw [hreg, Kimchi.Gate.VarBaseMul.bitsRegister_eq_cast bits hbool]
  · intro hregime
    have hG := hpoint hregime
    obtain ⟨hGns, hGeq⟩ := hG
    have hPne : ((2 * Kimchi.Gate.VarBaseMul.bitsVal bits + 2 ^ (5 * chunks) + 1) • T)
        ≠ 0 := by
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
          ((2 * Kimchi.Gate.VarBaseMul.bitsVal bits + 0 + 2 ^ (5 * chunks)) • T)
        rw [hxr false hbb, hyr false hbb,
          show ((2 * Kimchi.Gate.VarBaseMul.bitsVal bits + 0 + 2 ^ (5 * chunks)) • T)
            = ((2 * Kimchi.Gate.VarBaseMul.bitsVal bits + 2 ^ (5 * chunks) + 1) • T + -T)
            from by module]
        exact hq
      | true =>
        show Kimchi.Gate.AddComplete.IsPoint d.W (xr.val V) (yr.val V)
          ((2 * Kimchi.Gate.VarBaseMul.bitsVal bits + 1 + 2 ^ (5 * chunks)) • T)
        rw [hxr true hbb, hyr true hbb,
          show ((2 * Kimchi.Gate.VarBaseMul.bitsVal bits + 1 + 2 ^ (5 * chunks)) • T)
            = ((2 * Kimchi.Gate.VarBaseMul.bitsVal bits + 2 ^ (5 * chunks) + 1) • T)
            from by module]
        exact ⟨hGns, hGeq⟩

open WeierstrassCurve.Affine in
/-- **Completeness** (`scaleFast2`). The honest run of the split path: the ladder on
`sDiv2`, whose high bits vanish because the scalar fits the split's width, then the
parity fold — whose finite subtraction is priced by the same regime, through the
model's `ladder_off_base`. -/
theorem scaleFast2_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (d : HasCurve F) (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n)
    (hsplit : sDiv2Bits ≤ 5 * chunks)
    (base : AffinePoint (FVar F)) (sDiv2 : FVar F) (sOdd : BoolVar F)
    (xv yv sv : F) (bb : Bool) (hT : d.W.Nonsingular xv yv)
    (hfits : ToNat.toNat sv < 2 ^ sDiv2Bits)
    (hregime : d.LadderRegime (5 * chunks)
      (2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks) + 1)) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => base.x.Scoped st ∧ base.y.Scoped st ∧ sDiv2.Scoped st ∧
        (↑sOdd : CVar F).Scoped st ∧ base.x.val st.env.get = xv ∧
        base.y.val st.env.get = yv ∧ sDiv2.val st.env.get = sv ∧
        (↑sOdd : CVar F).val st.env.get = bit bb)
      (scaleFast2 (c := KimchiConstraint F) n chunks sDiv2Bits base sDiv2 sOdd)
      (fun r st' => OnCurve d.W st' r
        ((2 * (ToNat.toNat sv : ℤ) + (if bb then 1 else 0) + 2 ^ (5 * chunks))
          • Point.some _ _ hT)) := by
  rintro st ⟨hbx, hby, hsd, hso, hrx, hry, hrs, hrb⟩
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have hfits' : ToNat.toNat sv < 2 ^ (5 * chunks) :=
    lt_of_lt_of_le hfits (Nat.pow_le_pow_right (by norm_num) hsplit)
  -- the ladder
  obtain ⟨r, st₁, hrun₁, hsat₁, hbits, hG⟩ :=
    varBaseMul_complete d n chunks hn base ⟨sDiv2⟩ xv yv sv hT hfits' hregime st
      ⟨hbx, hby, hsd, hrx, hry, hrs⟩
  have hle₁ := hrun₁.le
  have hnv₁ := hrun₁.nv_le
  -- the high bits the honest scalar leaves clear
  have hpinval : ∀ x ∈ r.lsbBits.toList.drop sDiv2Bits,
      x.Scoped st₁ ∧ x.val st₁.env.get = 0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hi' : sDiv2Bits + i < n := by
      simp only [List.length_drop, Vector.length_toList] at hi
      omega
    have hbit : (ToNat.toNat sv).testBit (sDiv2Bits + i) = false :=
      Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hfits (Nat.pow_le_pow_right (by norm_num) (by omega)))
    obtain ⟨hsc, hval⟩ := hbits (sDiv2Bits + i) hi'
    simp only [List.getElem_drop, Vector.getElem_toList]
    exact ⟨hsc, by rw [hval, hbit]; simp⟩
  obtain ⟨u, st₂, hrun₂, hsat₂, hpin₂⟩ :=
    forM_complete (F := F) (c := KimchiConstraint F)
      (fun b : FVar F => assertEqual b (CVar.const 0))
      (fun b => b ∈ r.lsbBits.toList.drop sDiv2Bits)
      (fun _ st => ∀ x ∈ r.lsbBits.toList.drop sDiv2Bits,
        x.Scoped st ∧ x.val st.env.get = 0)
      (fun b _ hb => by
        intro stc hstc
        obtain ⟨w, stc', hrunc, hsatc, -⟩ :=
          assertEqual_complete (c := KimchiConstraint F) b (CVar.const 0) 0 stc
            ⟨⟨CircuitType.scoped_fvar.mpr (hstc b hb).1,
                CircuitType.reads_fvar.mpr (hstc b hb).2⟩,
              ⟨CircuitType.scoped_fvar.mpr trivial, CircuitType.reads_fvar.mpr rfl⟩⟩
        exact ⟨w, stc', hrunc, hsatc, fun x hx =>
          ⟨(hstc x hx).1.mono hrunc.nv_le,
            by rw [CVar.val_of_le hrunc.le (hstc x hx).1]; exact (hstc x hx).2⟩⟩)
      (r.lsbBits.toList.drop sDiv2Bits) (fun x hx => hx) st₁ hpinval
  have hle₂ := hrun₂.le
  have hnv₂ := hrun₂.nv_le
  -- the ladder's point, and the base's negation
  have hG₂ : OnCurve d.W st₂ r.g
      ((2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks) + 1) • Point.some _ _ hT) :=
    hG.mono hnv₂ hle₂
  obtain ⟨hGns, hGeq⟩ := hG₂.2
  have hGne : ((2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks) + 1) • Point.some _ _ hT)
      ≠ 0 := by rw [hGeq]; exact Point.some_ne_zero hGns
  have hnegT : OnCurve d.W st₂ ⟨base.x, CVar.negate_ base.y⟩ (-Point.some _ _ hT) := by
    refine ⟨scoped_affinePoint.mpr ⟨hbx.mono (Nat.le_trans hnv₁ hnv₂),
      CVar.Scoped.scale_ (hby.mono (Nat.le_trans hnv₁ hnv₂))⟩, ?_⟩
    refine OnCurveAt.neg ⟨d.short.1, d.short.2.2.1⟩ ?_
    show Kimchi.Gate.AddComplete.IsPoint d.W (base.x.val st₂.env.get)
      (base.y.val st₂.env.get) _
    rw [CVar.val_of_le (hle₁.trans hle₂) hbx, CVar.val_of_le (hle₁.trans hle₂) hby,
      hrx, hry]
    exact ⟨hT, rfl⟩
  -- the difference is finite: the regime keeps the result off the base
  have hoff : ((2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks)) • Point.some _ _ hT) ≠ 0 :=
    Kimchi.Gate.VarBaseMul.ladder_off_base d.W (Point.some_ne_zero hT) (5 * chunks)
      (ToNat.toNat sv) (by positivity) (by exact_mod_cast hfits') hregime
  have hsum : ((2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks) + 1) • Point.some _ _ hT
      + -Point.some _ _ hT) ≠ 0 := by
    rw [show ((2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks) + 1) • Point.some _ _ hT
        + -Point.some _ _ hT)
      = ((2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks)) • Point.some _ _ hT) from by module]
    exact hoff
  obtain ⟨q, st₃, hrun₃, hsat₃, ⟨hscQ, hscI⟩, hadd⟩ :=
    Complete.post (g := addFast (c := KimchiConstraint F) .checkFinite r.g
        ⟨base.x, CVar.negate_ base.y⟩)
      (fun V => addFast_spec (V := V) .checkFinite d.W
        ⟨d.short.1, d.short.2.1, d.short.2.2.1, d.short.2.2.2⟩ d.two_ne r.g
        ⟨base.x, CVar.negate_ base.y⟩)
      (addFast_complete .checkFinite d.W
        ⟨d.short.1, d.short.2.1, d.short.2.2.1, d.short.2.2.2⟩ d.two_ne r.g
        ⟨base.x, CVar.negate_ base.y⟩
        ((2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks) + 1) • Point.some _ _ hT)
        (-Point.some _ _ hT)) st₂
      ⟨hG₂, hnegT, d.two_torsion_free _ hGne, fun _ => hsum⟩
  have hle₃ := hrun₃.le
  have hnv₃ := hrun₃.nv_le
  have hscQ' : q.p.x.Scoped st₃ ∧ q.p.y.Scoped st₃ := scoped_affinePoint.mp hscQ
  have hscG : r.g.x.Scoped st₂ ∧ r.g.y.Scoped st₂ := scoped_affinePoint.mp hG₂.1
  have hQ : OnCurveAt d.W st₃.env.get q.p
      ((2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks) + 1) • Point.some _ _ hT
        + -Point.some _ _ hT) := by
    rcases hadd.2 _ _ (hG₂.mono hnv₃ hle₃).2 (hnegT.mono hnv₃ hle₃).2
      (d.two_torsion_free _ hGne) with ⟨hinf, hzero⟩ | ⟨-, h3⟩
    · exact absurd hzero hsum
    · exact h3
  have hQpt : OnCurve d.W st₃ q.p
      ((2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks) + 1) • Point.some _ _ hT
        + -Point.some _ _ hT) := ⟨hscQ, hQ⟩
  -- the parity fold: the point conditional, `y` before `x`
  have hwf : CircuitType.WellFormed (val := Bool) st₃.env.get sOdd := by
    refine ⟨bb, CircuitType.reads_boolVar.mpr ?_⟩
    rw [CVar.val_of_le ((hle₁.trans hle₂).trans hle₃) hso, hrb]
  have hsoS : (↑sOdd : CVar F).Scoped st₃ :=
    hso.mono (Nat.le_trans hnv₁ (Nat.le_trans hnv₂ hnv₃))
  have hbb₃ : (↑sOdd : CVar F).val st₃.env.get = bit bb := by
    rw [CVar.val_of_le ((hle₁.trans hle₂).trans hle₃) hso, hrb]
  obtain ⟨yr, st₄, hrun₄, hsat₄, hRY⟩ :=
    selectField_complete (c := KimchiConstraint F) sOdd r.g.y q.p.y bb
      (r.g.y.val st₃.env.get) (q.p.y.val st₃.env.get) st₃
      ⟨⟨CircuitType.scoped_boolVar.mpr hsoS, CircuitType.reads_boolVar.mpr hbb₃⟩,
        ⟨CircuitType.scoped_fvar.mpr (hscG.2.mono hnv₃), CircuitType.reads_fvar.mpr rfl⟩,
        ⟨CircuitType.scoped_fvar.mpr hscQ'.2, CircuitType.reads_fvar.mpr rfl⟩⟩
  have hscY : yr.Scoped st₄ := CircuitType.scoped_fvar.mp hRY.1
  have hvalY : yr.val st₄.env.get
      = if bb then r.g.y.val st₃.env.get else q.p.y.val st₃.env.get :=
    CircuitType.reads_fvar.mp hRY.2
  have hle₄ := hrun₄.le
  have hnv₄ := hrun₄.nv_le
  have hbb₄ : (↑sOdd : CVar F).val st₄.env.get = bit bb := by
    rw [CVar.val_of_le hle₄ hsoS, hbb₃]
  obtain ⟨xr, st₅, hrun₅, hsat₅, hRX⟩ :=
    selectField_complete (c := KimchiConstraint F) sOdd r.g.x q.p.x bb
      (r.g.x.val st₄.env.get) (q.p.x.val st₄.env.get) st₄
      ⟨⟨CircuitType.scoped_boolVar.mpr (hsoS.mono hnv₄),
          CircuitType.reads_boolVar.mpr hbb₄⟩,
        ⟨CircuitType.scoped_fvar.mpr ((hscG.1.mono hnv₃).mono hnv₄),
          CircuitType.reads_fvar.mpr rfl⟩,
        ⟨CircuitType.scoped_fvar.mpr (hscQ'.1.mono hnv₄), CircuitType.reads_fvar.mpr rfl⟩⟩
  have hscX : xr.Scoped st₅ := CircuitType.scoped_fvar.mp hRX.1
  have hvalX : xr.val st₅.env.get
      = if bb then r.g.x.val st₄.env.get else q.p.x.val st₄.env.get :=
    CircuitType.reads_fvar.mp hRX.2
  have hle₅ := hrun₅.le
  have hnv₅ := hrun₅.nv_le
  have hbb₅ : (↑sOdd : CVar F).val st₅.env.get = bit bb := by
    rw [CVar.val_of_le hle₅ (hsoS.mono hnv₄), hbb₄]
  refine ⟨⟨xr, yr⟩, st₅,
    hrun₁.bind (hrun₂.bind (hrun₃.bind (hrun₄.bind (hrun₅.bind rfl)))), ?_, ?_⟩
  · intro stf hnvF hleF
    refine Sat.bind hrun₁ (hsat₁ ?_ ?_) (Sat.bind hrun₂ (hsat₂ ?_ ?_)
      (Sat.bind hrun₃ (hsat₃ ?_ ?_) (Sat.bind hrun₄ (hsat₄ ?_ ?_)
        (Sat.bind hrun₅ (hsat₅ hnvF hleF) Sat.pure))))
    · exact Nat.le_trans (Nat.le_trans hnv₂ (Nat.le_trans hnv₃ (Nat.le_trans hnv₄ hnv₅)))
        hnvF
    · exact (((hle₂.trans hle₃).trans hle₄).trans hle₅).trans hleF
    · exact Nat.le_trans (Nat.le_trans hnv₃ (Nat.le_trans hnv₄ hnv₅)) hnvF
    · exact ((hle₃.trans hle₄).trans hle₅).trans hleF
    · exact Nat.le_trans (Nat.le_trans hnv₄ hnv₅) hnvF
    · exact (hle₄.trans hle₅).trans hleF
    · exact Nat.le_trans hnv₅ hnvF
    · exact hle₅.trans hleF
  · refine ⟨scoped_affinePoint.mpr ⟨hscX, hscY.mono hnv₅⟩, ?_⟩
    have hy : yr.val st₅.env.get
        = if bb then r.g.y.val st₅.env.get else q.p.y.val st₅.env.get := by
      rw [CVar.val_of_le hle₅ hscY, hvalY,
        CVar.val_of_le (hle₄.trans hle₅) (hscG.2.mono hnv₃),
        CVar.val_of_le (hle₄.trans hle₅) hscQ'.2]
    have hx : xr.val st₅.env.get
        = if bb then r.g.x.val st₅.env.get else q.p.x.val st₅.env.get := by
      rw [hvalX, CVar.val_of_le hle₅ ((hscG.1.mono hnv₃).mono hnv₄),
        CVar.val_of_le hle₅ (hscQ'.1.mono hnv₄)]
    cases bb with
    | false =>
      show Kimchi.Gate.AddComplete.IsPoint d.W (xr.val st₅.env.get) (yr.val st₅.env.get)
        ((2 * (ToNat.toNat sv : ℤ) + 0 + 2 ^ (5 * chunks)) • Point.some _ _ hT)
      rw [hx, hy, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
        show ((2 * (ToNat.toNat sv : ℤ) + 0 + 2 ^ (5 * chunks)) • Point.some _ _ hT)
          = ((2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks) + 1) • Point.some _ _ hT
            + -Point.some _ _ hT) from by module]
      exact (hQpt.mono (Nat.le_trans hnv₄ hnv₅) (hle₄.trans hle₅)).2
    | true =>
      show Kimchi.Gate.AddComplete.IsPoint d.W (xr.val st₅.env.get) (yr.val st₅.env.get)
        ((2 * (ToNat.toNat sv : ℤ) + 1 + 2 ^ (5 * chunks)) • Point.some _ _ hT)
      rw [hx, hy, if_pos rfl, if_pos rfl,
        show ((2 * (ToNat.toNat sv : ℤ) + 1 + 2 ^ (5 * chunks)) • Point.some _ _ hT)
          = ((2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks) + 1) • Point.some _ _ hT)
          from by module]
      exact ((hG₂.mono (Nat.le_trans hnv₃ (Nat.le_trans hnv₄ hnv₅))
        ((hle₃.trans hle₄).trans hle₅)).2)

attribute [irreducible] scaleFast2

/-! ## The parity split -/

/-- The parity split of a field value (PS `splitField`): `s = 2·sDiv2 + sOdd`. -/
def splitField [Field F] [ToNat F] (s : F) : F × Bool :=
  let odd := (ToNat.toNat s) % 2 = 1
  ((if odd then s - 1 else s) / 2, odd)

/-- The joined value of a parity split (PS `joinField`). -/
def joinField [Field F] (sDiv2 : F) (sOdd : Bool) : F :=
  2 * sDiv2 + (if sOdd then 1 else 0)

private def splitFieldWit [Field F] [ToNat F] (s : FVar F) : AsProver F (F × Bool) := do
  let v ← AsProver.readCVar s
  pure (splitField v)

/-- Witness a parity split and constrain it (PS `splitFieldVar`):
`s = 2·sDiv2 + sOdd`, one linear assert. -/
def splitFieldVar [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    (s : FVar F) : CircuitM F c (FVar F × BoolVar F) := do
  let r ← witness (val := F × Bool) (splitFieldWit s)
  assertEqual s (CVar.add_ (CVar.scale_ 2 r.1) ↑r.2)
  pure r

open Std.Do in
/-- **Soundness** (`splitFieldVar`). The witnessed pair is a parity split of the
scalar: a bit, and a half the one linear row pins. -/
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

/-- **Completeness** (`splitFieldVar`). The honest split of the value the scalar reads
as: the row it pins is the split's own equation. -/
theorem splitFieldVar_complete [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (h2 : (2 : F) ≠ 0) (s : FVar F)
    (sval : F) :
    Complete (F := F) (c := c) (fun st => s.Scoped st ∧ s.val st.env.get = sval)
      (splitFieldVar (c := c) s)
      (fun r st' => r.1.Scoped st' ∧ (↑r.2 : CVar F).Scoped st' ∧
        r.1.val st'.env.get = (splitField sval).1 ∧
        (↑r.2 : CVar F).val st'.env.get = bit (splitField sval).2) := by
  rintro st ⟨hsc, hval⟩
  obtain ⟨w, st₁, hrun₁, hsat₁, hnv₁, hle₁, hscW, hrdW⟩ :=
    witness_complete (c := c) (val := F × Bool) (splitFieldWit s) (st := st)
      (v := ((splitField sval).1, (splitField sval).2))
      (by
        simp only [splitFieldWit, AsProver.bind_eq, AsProver.run_bind,
          AsProver.readCVar_run hsc, hval, Except.bind]
        rfl)
  obtain ⟨wD, wO⟩ := w
  simp only [CircuitType.scoped_prod, CircuitType.scoped_fvar,
    CircuitType.scoped_boolVar] at hscW
  simp only [CircuitType.reads_prod, CircuitType.reads_fvar] at hrdW
  have hbb : (↑wO : CVar F).val st₁.env.get = bit (splitField sval).2 :=
    CircuitType.reads_boolVar.mp hrdW.2
  have hpin : s.val st₁.env.get
      = (CVar.add_ (CVar.scale_ 2 wD) ↑wO).val st₁.env.get := by
    rw [CVar.val_add_, CVar.val_scale_, hrdW.1, hbb, CVar.val_of_le hle₁ hsc, hval]
    simp only [splitField, bit, decide_eq_true_eq]
    split <;> field_simp <;> ring
  obtain ⟨u, st₂, hrun₂, hsat₂, -⟩ :=
    assertEqual_complete (c := c) s (CVar.add_ (CVar.scale_ 2 wD) ↑wO)
      (s.val st₁.env.get) st₁
      ⟨⟨CircuitType.scoped_fvar.mpr (hsc.mono hnv₁), CircuitType.reads_fvar.mpr rfl⟩,
        ⟨CircuitType.scoped_fvar.mpr
            (CVar.Scoped.add_ (CVar.Scoped.scale_ hscW.1) hscW.2),
          CircuitType.reads_fvar.mpr hpin.symm⟩⟩
  have hle₂ := hrun₂.le
  have hnv₂ := hrun₂.nv_le
  exact ⟨(wD, wO), st₂, hrun₁.bind (hrun₂.bind rfl), fun hnv hle =>
    Sat.bind hrun₁ (hsat₁ (Nat.le_trans hnv₂ hnv) (hle₂.trans hle))
      (Sat.bind hrun₂ (hsat₂ hnv hle) Sat.pure),
    hscW.1.mono hnv₂, hscW.2.mono hnv₂,
    by rw [CVar.val_of_le hle₂ hscW.1, hrdW.1],
    by rw [CVar.val_of_le hle₂ hscW.2, hbb]⟩

attribute [irreducible] splitFieldWit splitFieldVar

/-! ## `scaleFast2'` -/

/-- `scaleFast2' g s ~ [s + 2^n]·g`: split the raw scalar, then `scaleFast2`. -/
def scaleFast2' [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (n chunks sDiv2Bits : ℕ) (base : AffinePoint (FVar F))
    (s : FVar F) : CircuitM F c (AffinePoint (FVar F)) := do
  let (sDiv2, sOdd) ← splitFieldVar s
  scaleFast2 n chunks sDiv2Bits base sDiv2 sOdd

open Std.Do WeierstrassCurve.Affine in
/-- **Soundness** (`scaleFast2'`). The split path at a raw scalar: the ladder's half,
the parity bit, and the multiple they name — with the scalar pinned to the split. -/
theorem scaleFast2'_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (d : HasCurve F) (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n)
    (hsplit : sDiv2Bits ≤ 5 * chunks) (base : AffinePoint (FVar F)) (s : FVar F) :
    ⦃⌜True⌝⦄
    scaleFast2' (c := Builder V (KimchiConstraint F)) n chunks sDiv2Bits base s
    ⦃⇓ r _ => ⌜∀ T : d.W.Point, OnCurveAt d.W V base T →
      ∃ (z : ℤ) (bb : Bool), 0 ≤ z ∧ z < 2 ^ sDiv2Bits ∧
        ((2 * z + (if bb then 1 else 0) : ℤ) : F) = s.val V ∧
        ∀ _ : d.LadderRegime (5 * chunks) (2 * z + 2 ^ (5 * chunks) + 1),
          OnCurveAt d.W V r
            ((2 * z + (if bb then 1 else 0) + 2 ^ (5 * chunks)) • T)⌝⦄ := by
  have hsplitV := fun (V : Valuation F) =>
    splitFieldVar_spec (c := KimchiConstraint F) (V := V) s
  have hsf2 := fun (V : Valuation F) (sDiv2 : FVar F) (sOdd : BoolVar F) =>
    scaleFast2_spec (V := V) d n chunks sDiv2Bits hn hsplit base sDiv2 sOdd
  simp only [scaleFast2']
  mvcgen [hsplitV, hsf2]
  rename_i hsp _ _
  intro hq T hT
  obtain ⟨bb, hbit, hpin⟩ := hsp
  obtain ⟨z, h0, hlt, hzval, hpoint⟩ := hq T hT bb hbit
  refine ⟨z, bb, h0, hlt, ?_, hpoint⟩
  push_cast
  rw [hpin, hzval]
  cases bb <;> simp [bit]


open WeierstrassCurve.Affine in
/-- **Completeness** (`scaleFast2'`). The honest split of the scalar, then the split
path's honest run. -/
theorem scaleFast2'_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (d : HasCurve F) (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n)
    (hsplit : sDiv2Bits ≤ 5 * chunks) (base : AffinePoint (FVar F)) (s : FVar F)
    (xv yv sval : F) (hT : d.W.Nonsingular xv yv)
    (hfits : ToNat.toNat (splitField sval).1 < 2 ^ sDiv2Bits)
    (hregime : d.LadderRegime (5 * chunks)
      (2 * (ToNat.toNat (splitField sval).1 : ℤ) + 2 ^ (5 * chunks) + 1)) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => base.x.Scoped st ∧ base.y.Scoped st ∧ s.Scoped st ∧
        base.x.val st.env.get = xv ∧ base.y.val st.env.get = yv ∧
        s.val st.env.get = sval)
      (scaleFast2' (c := KimchiConstraint F) n chunks sDiv2Bits base s)
      (fun r st' => OnCurve d.W st' r
        ((2 * (ToNat.toNat (splitField sval).1 : ℤ)
            + (if (splitField sval).2 then 1 else 0) + 2 ^ (5 * chunks))
          • Point.some _ _ hT)) := by
  rintro st ⟨hbx, hby, hs, hrx, hry, hrs⟩
  obtain ⟨w, st₁, hrun₁, hsat₁, hscD, hscO, hvalD, hvalO⟩ :=
    splitFieldVar_complete (c := KimchiConstraint F) d.two_ne s sval st ⟨hs, hrs⟩
  have hle₁ := hrun₁.le
  have hnv₁ := hrun₁.nv_le
  obtain ⟨g, st₂, hrun₂, hsat₂, hpt⟩ :=
    scaleFast2_complete d n chunks sDiv2Bits hn hsplit base w.1 w.2 xv yv
      (splitField sval).1 (splitField sval).2 hT hfits hregime st₁
      ⟨hbx.mono hnv₁, hby.mono hnv₁, hscD, hscO,
        by rw [CVar.val_of_le hle₁ hbx, hrx], by rw [CVar.val_of_le hle₁ hby, hry],
        hvalD, hvalO⟩
  exact ⟨g, st₂, hrun₁.bind hrun₂, fun hnv hle =>
    Sat.bind hrun₁ (hsat₁ (Nat.le_trans hrun₂.nv_le hnv) (hrun₂.le.trans hle))
      (hsat₂ hnv hle), hpt⟩

attribute [irreducible] scaleFast2'

end Snarky.Kimchi
