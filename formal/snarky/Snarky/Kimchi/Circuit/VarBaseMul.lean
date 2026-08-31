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

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- The dictionary at deployed Vesta — the curve the Schnorr statement's points live on
and the ladder's base group. -/
@[reducible] def HasCurve.vesta : HasCurve Fq where
  W := Vesta.curve.toAffine
  short := ⟨rfl, rfl, rfl, rfl⟩
  prime := Fact.out
  odd := by rw [vesta_card]; decide
  two_ne := by decide

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

open CompElliptic.Fields.Pasta Kimchi.Gate.VarBaseMul in
/-- At Vesta, a `Type1` carrier off the ladder's forbidden band is in the one-wrap
regime: the deployed order sits in the band and is `1 mod 4`. -/
private theorem vesta_ladderRegime (t : Type1 Fq)
    (hband : t.toScalarZ ∉ forbiddenValues PALLAS_BASE_CARD) :
    HasCurve.vesta.LadderRegime 255 t.toScalarZ := by
  have hOv : HasCurve.vesta.W.order = PALLAS_BASE_CARD := Pasta.vesta_card
  refine Or.inr ⟨?_, ?_, ?_, ?_⟩ <;> rw [hOv]
  · decide
  · decide
  · decide
  · exact hband

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
  simp only [scaleRound]
  -- the ten cell readings at the entry table index the law
  refine Complete.instantiate
    (ι := F × F × F × F × F × F × F × F × F × F)
    (P := fun v st => (st₁.nv ≤ st.nv ∧ st₁.env.Le st.env) ∧
      CircuitType.ReadsAs (val := F) st base.x v.1 ∧
      CircuitType.ReadsAs (val := F) st base.y v.2.1 ∧
      CircuitType.ReadsAs (val := F) st acc.1.x v.2.2.1 ∧
      CircuitType.ReadsAs (val := F) st acc.1.y v.2.2.2.1 ∧
      CircuitType.ReadsAs (val := F) st acc.2 v.2.2.2.2.1 ∧
      CircuitType.ReadsAs (val := F) st (bs[0]'(by omega)) v.2.2.2.2.2.1 ∧
      CircuitType.ReadsAs (val := F) st (bs[1]'(by omega)) v.2.2.2.2.2.2.1 ∧
      CircuitType.ReadsAs (val := F) st (bs[2]'(by omega)) v.2.2.2.2.2.2.2.1 ∧
      CircuitType.ReadsAs (val := F) st (bs[3]'(by omega)) v.2.2.2.2.2.2.2.2.1 ∧
      CircuitType.ReadsAs (val := F) st (bs[4]'(by omega)) v.2.2.2.2.2.2.2.2.2)
    (fun st h => ?_) fun v => ?_
  · have hb : ∀ (i : ℕ) (hi : i < 5), (bs[i]'hi).Scoped st :=
      fun i hi => (hbs _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))).mono h.1.1
    exact ⟨(base.x.val st.env.get, base.y.val st.env.get, acc.1.x.val st.env.get,
        acc.1.y.val st.env.get, acc.2.val st.env.get, (bs[0]'(by omega)).val st.env.get,
        (bs[1]'(by omega)).val st.env.get, (bs[2]'(by omega)).val st.env.get,
        (bs[3]'(by omega)).val st.env.get, (bs[4]'(by omega)).val st.env.get),
      h.1,
      ⟨CircuitType.scoped_fvar.mpr (hbase.1.mono h.1.1), CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (hbase.2.mono h.1.1), CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr h.2.1, CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr h.2.2.1, CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr h.2.2.2, CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (hb 0 (by omega)), CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (hb 1 (by omega)), CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (hb 2 (by omega)), CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (hb 3 (by omega)), CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (hb 4 (by omega)), CircuitType.reads_fvar.mpr rfl⟩⟩
  obtain ⟨xB, yB, x0, y0, n0, b0, b1, b2, b3, b4⟩ := v
  have hMP : Mono (F := F) fun st => (st₁.nv ≤ st.nv ∧ st₁.env.Le st.env) ∧
      CircuitType.ReadsAs (val := F) st base.x xB ∧
      CircuitType.ReadsAs (val := F) st base.y yB ∧
      CircuitType.ReadsAs (val := F) st acc.1.x x0 ∧
      CircuitType.ReadsAs (val := F) st acc.1.y y0 ∧
      CircuitType.ReadsAs (val := F) st acc.2 n0 ∧
      CircuitType.ReadsAs (val := F) st (bs[0]'(by omega)) b0 ∧
      CircuitType.ReadsAs (val := F) st (bs[1]'(by omega)) b1 ∧
      CircuitType.ReadsAs (val := F) st (bs[2]'(by omega)) b2 ∧
      CircuitType.ReadsAs (val := F) st (bs[3]'(by omega)) b3 ∧
      CircuitType.ReadsAs (val := F) st (bs[4]'(by omega)) b4 :=
    Mono.and (fun _ _ hnv hle h => ⟨Nat.le_trans h.1 hnv, h.2.trans hle⟩)
      (Mono.and Mono.readsAs (Mono.and Mono.readsAs (Mono.and Mono.readsAs
        (Mono.and Mono.readsAs (Mono.and Mono.readsAs (Mono.and Mono.readsAs
          (Mono.and Mono.readsAs (Mono.and Mono.readsAs
            (Mono.and Mono.readsAs Mono.readsAs)))))))))
  set W := Kimchi.Gate.VarBaseMul.build xB yB x0 y0 n0 b0 b1 b2 b3 b4 with hW
  -- the register advice
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?run0, h⟩) (fun _ _ h => h)
      (Complete.frame hMP (Complete.witness (nAccWit acc.2 bs) W.nPrime (by simp))))
    fun nAcc => ?_
  case run0 =>
    obtain ⟨hext, hBX, hBY, hAX, hAY, hRN, hb0, hb1, hb2, hb3, hb4⟩ := h
    simp only [nAccWit, AsProver.bind_eq, AsProver.run_bind,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hRN.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hb0.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hb1.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hb2.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hb3.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hb4.1),
      CircuitType.reads_fvar.mp hRN.2, CircuitType.reads_fvar.mp hb0.2,
      CircuitType.reads_fvar.mp hb1.2, CircuitType.reads_fvar.mp hb2.2,
      CircuitType.reads_fvar.mp hb3.2, CircuitType.reads_fvar.mp hb4.2, Except.bind]
    rw [hW]
    rfl
  -- bit step 0
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?run1, h⟩) (fun _ _ h => h)
      (Complete.frame (Mono.and Mono.readsAs hMP)
        (Complete.witness (bitWit base (bs[0]'(by omega)) acc.1)
          (W.s0, W.s0 * W.s0,
            2 * W.y0 / (2 * W.x0 + W.xT - W.s0 * W.s0) - W.s0, W.x1, W.y1) (by simp))))
    fun w0 => ?_
  case run1 =>
    obtain ⟨hNA, hext, hBX, hBY, hAX, hAY, hRN, hb0, hb1, hb2, hb3, hb4⟩ := h
    simp only [bitWit, AsProver.bind_eq, AsProver.run_bind,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hBX.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hBY.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hAX.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hAY.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hb0.1),
      CircuitType.reads_fvar.mp hBX.2, CircuitType.reads_fvar.mp hBY.2,
      CircuitType.reads_fvar.mp hAX.2, CircuitType.reads_fvar.mp hAY.2,
      CircuitType.reads_fvar.mp hb0.2, Except.bind]
    rw [hW]
    rfl
  obtain ⟨sl0, sq0, se0, ox0, oy0⟩ := w0
  -- bit step 1
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?run2, h⟩) (fun _ _ h => h)
      (Complete.frame (Mono.and Mono.readsAs (Mono.and Mono.readsAs hMP))
        (Complete.witness (bitWit base (bs[1]'(by omega)) ⟨ox0, oy0⟩)
          (W.s1, W.s1 * W.s1,
            2 * W.y1 / (2 * W.x1 + W.xT - W.s1 * W.s1) - W.s1, W.x2, W.y2) (by simp))))
    fun w1 => ?_
  case run2 =>
    obtain ⟨hw0, hNA, hext, hBX, hBY, hAX, hAY, hRN, hb0, hb1, hb2, hb3, hb4⟩ := h
    have hsc := hw0.1
    have hrd := hw0.2
    simp only [CircuitType.scoped_prod, CircuitType.scoped_fvar] at hsc
    simp only [CircuitType.reads_prod, CircuitType.reads_fvar] at hrd
    simp only [bitWit, AsProver.bind_eq, AsProver.run_bind,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hBX.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hBY.1),
      AsProver.readCVar_run hsc.2.2.2.1, AsProver.readCVar_run hsc.2.2.2.2,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hb1.1),
      CircuitType.reads_fvar.mp hBX.2, CircuitType.reads_fvar.mp hBY.2,
      hrd.2.2.2.1, hrd.2.2.2.2, CircuitType.reads_fvar.mp hb1.2, Except.bind]
    rw [hW]
    rfl
  obtain ⟨sl1, sq1, se1, ox1, oy1⟩ := w1
  -- bit step 2
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?run3, h⟩) (fun _ _ h => h)
      (Complete.frame (Mono.and Mono.readsAs (Mono.and Mono.readsAs
          (Mono.and Mono.readsAs hMP)))
        (Complete.witness (bitWit base (bs[2]'(by omega)) ⟨ox1, oy1⟩)
          (W.s2, W.s2 * W.s2,
            2 * W.y2 / (2 * W.x2 + W.xT - W.s2 * W.s2) - W.s2, W.x3, W.y3) (by simp))))
    fun w2 => ?_
  case run3 =>
    obtain ⟨hw1, hw0, hNA, hext, hBX, hBY, hAX, hAY, hRN, hb0, hb1, hb2, hb3, hb4⟩ := h
    have hsc := hw1.1
    have hrd := hw1.2
    simp only [CircuitType.scoped_prod, CircuitType.scoped_fvar] at hsc
    simp only [CircuitType.reads_prod, CircuitType.reads_fvar] at hrd
    simp only [bitWit, AsProver.bind_eq, AsProver.run_bind,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hBX.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hBY.1),
      AsProver.readCVar_run hsc.2.2.2.1, AsProver.readCVar_run hsc.2.2.2.2,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hb2.1),
      CircuitType.reads_fvar.mp hBX.2, CircuitType.reads_fvar.mp hBY.2,
      hrd.2.2.2.1, hrd.2.2.2.2, CircuitType.reads_fvar.mp hb2.2, Except.bind]
    rw [hW]
    rfl
  obtain ⟨sl2, sq2, se2, ox2, oy2⟩ := w2
  -- bit step 3
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?run4, h⟩) (fun _ _ h => h)
      (Complete.frame (Mono.and Mono.readsAs (Mono.and Mono.readsAs
          (Mono.and Mono.readsAs (Mono.and Mono.readsAs hMP))))
        (Complete.witness (bitWit base (bs[3]'(by omega)) ⟨ox2, oy2⟩)
          (W.s3, W.s3 * W.s3,
            2 * W.y3 / (2 * W.x3 + W.xT - W.s3 * W.s3) - W.s3, W.x4, W.y4) (by simp))))
    fun w3 => ?_
  case run4 =>
    obtain ⟨hw2, hw1, hw0, hNA, hext, hBX, hBY, hAX, hAY, hRN, hb0, hb1, hb2, hb3, hb4⟩ := h
    have hsc := hw2.1
    have hrd := hw2.2
    simp only [CircuitType.scoped_prod, CircuitType.scoped_fvar] at hsc
    simp only [CircuitType.reads_prod, CircuitType.reads_fvar] at hrd
    simp only [bitWit, AsProver.bind_eq, AsProver.run_bind,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hBX.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hBY.1),
      AsProver.readCVar_run hsc.2.2.2.1, AsProver.readCVar_run hsc.2.2.2.2,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hb3.1),
      CircuitType.reads_fvar.mp hBX.2, CircuitType.reads_fvar.mp hBY.2,
      hrd.2.2.2.1, hrd.2.2.2.2, CircuitType.reads_fvar.mp hb3.2, Except.bind]
    rw [hW]
    rfl
  obtain ⟨sl3, sq3, se3, ox3, oy3⟩ := w3
  -- bit step 4
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?run5, h⟩) (fun _ _ h => h)
      (Complete.frame (Mono.and Mono.readsAs (Mono.and Mono.readsAs
          (Mono.and Mono.readsAs (Mono.and Mono.readsAs (Mono.and Mono.readsAs hMP)))))
        (Complete.witness (bitWit base (bs[4]'(by omega)) ⟨ox3, oy3⟩)
          (W.s4, W.s4 * W.s4,
            2 * W.y4 / (2 * W.x4 + W.xT - W.s4 * W.s4) - W.s4, W.x5, W.y5) (by simp))))
    fun w4 => Complete.pure_of fun st h => ?post
  case run5 =>
    obtain ⟨hw3, hw2, hw1, hw0, hNA, hext, hBX, hBY, hAX, hAY, hRN,
      hb0, hb1, hb2, hb3, hb4⟩ := h
    have hsc := hw3.1
    have hrd := hw3.2
    simp only [CircuitType.scoped_prod, CircuitType.scoped_fvar] at hsc
    simp only [CircuitType.reads_prod, CircuitType.reads_fvar] at hrd
    simp only [bitWit, AsProver.bind_eq, AsProver.run_bind,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hBX.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hBY.1),
      AsProver.readCVar_run hsc.2.2.2.1, AsProver.readCVar_run hsc.2.2.2.2,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hb4.1),
      CircuitType.reads_fvar.mp hBX.2, CircuitType.reads_fvar.mp hBY.2,
      hrd.2.2.2.1, hrd.2.2.2.2, CircuitType.reads_fvar.mp hb4.2, Except.bind]
    rw [hW]
    rfl
  case post =>
    obtain ⟨sl4, sq4, se4, ox4, oy4⟩ := w4
    obtain ⟨hw4, hw3, hw2, hw1, hw0, hNA, hext, hBX, hBY, hAX, hAY, hRN,
      hb0, hb1, hb2, hb3, hb4⟩ := h
    have hC0 := CircuitType.scoped_fvar.mp hNA.1
    have hD0 := CircuitType.reads_fvar.mp hNA.2
    have hC1 := hw0.1; have hD1 := hw0.2
    have hC2 := hw1.1; have hD2 := hw1.2
    have hC3 := hw2.1; have hD3 := hw2.2
    have hC4 := hw3.1; have hD4 := hw3.2
    have hC5 := hw4.1; have hD5 := hw4.2
    simp only [CircuitType.scoped_prod, CircuitType.scoped_fvar] at hC1 hC2 hC3 hC4 hC5
    simp only [CircuitType.reads_prod, CircuitType.reads_fvar] at hD1 hD2 hD3 hD4 hD5
    refine ⟨⟨hext, hC5.2.2.2.1, hC5.2.2.2.2, hC0⟩,
      ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
    · intro cv hcv
      simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at hcv
      rcases hcv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
      · exact CircuitType.scoped_fvar.mp hBX.1
      · exact CircuitType.scoped_fvar.mp hBY.1
      · exact CircuitType.scoped_fvar.mp hAX.1
      · exact CircuitType.scoped_fvar.mp hAY.1
      · exact hC1.2.2.2.1
      · exact hC1.2.2.2.2
      · exact hC2.2.2.2.1
      · exact hC2.2.2.2.2
      · exact hC3.2.2.2.1
      · exact hC3.2.2.2.2
      · exact hC4.2.2.2.1
      · exact hC4.2.2.2.2
      · exact hC5.2.2.2.1
      · exact hC5.2.2.2.2
      · exact CircuitType.scoped_fvar.mp hb0.1
      · exact CircuitType.scoped_fvar.mp hb1.1
      · exact CircuitType.scoped_fvar.mp hb2.1
      · exact CircuitType.scoped_fvar.mp hb3.1
      · exact CircuitType.scoped_fvar.mp hb4.1
      · exact hC1.1
      · exact hC2.1
      · exact hC3.1
      · exact hC4.1
      · exact hC5.1
      · exact CircuitType.scoped_fvar.mp hRN.1
      · exact hC0
    · simp only [ScaleRound.read,
        CircuitType.reads_fvar.mp hBX.2, CircuitType.reads_fvar.mp hBY.2,
        CircuitType.reads_fvar.mp hAX.2, CircuitType.reads_fvar.mp hAY.2,
        CircuitType.reads_fvar.mp hRN.2,
        CircuitType.reads_fvar.mp hb0.2, CircuitType.reads_fvar.mp hb1.2,
        CircuitType.reads_fvar.mp hb2.2, CircuitType.reads_fvar.mp hb3.2,
        CircuitType.reads_fvar.mp hb4.2,
        hD0, hD1.2.2.2.1, hD1.2.2.2.2, hD1.1, hD2.2.2.2.1, hD2.2.2.2.2, hD2.1,
        hD3.2.2.2.1, hD3.2.2.2.2, hD3.1, hD4.2.2.2.1, hD4.2.2.2.2, hD4.1,
        hD5.2.2.2.1, hD5.2.2.2.2, hD5.1]
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
          (Pasta.Shifted.unshiftType1 (5 * pref.length) (bitsVal (roundBits V rounds))),
        OnCurveAt d.W V fin.1
          ((Pasta.Shifted.unshiftType1 (5 * pref.length) (bitsVal (roundBits V rounds))) • T) := by
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
          = Pasta.Shifted.unshiftType1 (5 * l.length)
            (bitsVal (roundBits V (r₀ :: rs))) := by
        rw [Pasta.Shifted.unshiftType1]
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
/-- **Soundness.** Any satisfying valuation reads the result's cells as bits whose LSB-first
value the scalar reads as, and the result as the base multiplied by that value's Type1
decode — under the ladder's regime, which is what prices the ladder's non-degeneracy. -/
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
  have hdec : ((VarBaseMul.roundBits V loop.1).map fun b => decide (b = 1)).reverse
      = bs.toList := by
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
  have hbn : Kimchi.Gate.VarBaseMul.bitsVal (VarBaseMul.roundBits V loop.1)
      = (Kimchi.natLsbVal bs.toList : ℤ) := by
    rw [Kimchi.Gate.VarBaseMul.bitsVal_eq_natLsbVal, hdec]
  refine ⟨bs, hread, ?_, ?_⟩
  · rw [← hpin, hreg,
      Kimchi.Gate.VarBaseMul.bitsRegister_eq_cast (VarBaseMul.roundBits V loop.1) hbool, hbn]
    push_cast
    ring
  · rw [hpreflen, hbn] at hpoint
    exact hpoint

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
      (Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat sv : ℤ))) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => OnCurveAs d.W st base (Point.some _ _ hT) ∧
        CircuitType.ReadsAs (val := F) st scalar.val sv)
      (varBaseMul (c := KimchiConstraint F) n chunks base scalar)
      (fun r st' =>
        CircuitType.ReadsAs (val := Vector Bool n) st'
          (mapVec BoolVar.unchecked r.lsbBits) (unpackPure sv n) ∧
        OnCurveAs d.W st' r.g
          ((Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat sv : ℤ))
            • Point.some _ _ hT)) := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have h2T : Point.some _ _ hT + Point.some _ _ hT ≠ 0 :=
    d.two_torsion_free _ (Point.some_ne_zero hT)
  -- the base's canonical reading, off any on-curve state
  have hbread : ∀ {st : ProverState F}, OnCurveAs d.W st base (Point.some _ _ hT) →
      CircuitType.ReadsAs (val := AffinePoint F) st base ⟨xv, yv⟩ := fun h =>
    ⟨h.1, reads_affinePoint.mpr (Kimchi.Gate.AddComplete.IsPoint.coords_eq h.2 ⟨hT, rfl⟩)⟩
  simp only [varBaseMul]
  complete_walk
  -- the base base's coordinates, and the base as a curve point, off any reading state
  have hscoords : ∀ {st : ProverState F},
      CircuitType.ReadsAs (val := AffinePoint F) st base ⟨xv, yv⟩ →
        base.x.val st.env.get = xv ∧ base.y.val st.env.get = yv :=
    fun h => reads_affinePoint.mp h.2
  have hTread : ∀ {st : ProverState F},
      CircuitType.ReadsAs (val := AffinePoint F) st base ⟨xv, yv⟩ →
        OnCurveAs d.W st base (Point.some _ _ hT) := fun h =>
    ⟨h.1, OnCurveAt.of_reads (p := base) (hscoords h).1 (hscoords h).2 hT⟩
  -- the scalar's lsbBits, in one witness
  refine Complete.seq (by complete_mono_tac)
    (Complete.imp
      (fun st h => by
        simp only [lsbBitsWit, AsProver.bind_eq, AsProver.run_bind,
          AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.1.2.1),
          CircuitType.reads_fvar.mp h.1.2.2, Except.bind]
        rfl)
      (fun _ _ h => h)
      (Complete.witness (lsbBitsWit n scalar.val)
        (Vector.ofFn fun i : Fin n => if (ToNat.toNat sv).testBit i.1 then 1 else 0)
        (by simp)))
    fun lsbBits => ?_
  -- the lsbBits' landing table indexes the rest: the index carries the bit cells' scope
  -- and canonical readings, and the base base's scope
  refine Complete.instantiate
    (ι := {st₂ : ProverState F // (∀ (i : ℕ) (hi : i < n),
        (lsbBits[i]'hi).Scoped st₂ ∧
          (lsbBits[i]'hi).val st₂.env.get
            = if (ToNat.toNat sv).testBit i then 1 else 0) ∧
      base.x.Scoped st₂ ∧ base.y.Scoped st₂})
    (P := fun i st => (i.1.nv ≤ st.nv ∧ i.1.env.Le st.env) ∧
      CircuitType.ReadsAs (val := AffinePoint F) st base ⟨xv, yv⟩ ∧
      CircuitType.ReadsAs (val := F) st scalar.val sv)
    (fun st h => ⟨⟨st, fun i hi =>
        ⟨CircuitType.scoped_fvar.mp (CircuitType.scoped_vector.mp h.2.1 i hi),
          by simpa using
            CircuitType.reads_fvar.mp (CircuitType.reads_vector.mp h.2.2 i hi)⟩,
        (scoped_affinePoint.mp h.1.2.1).1, (scoped_affinePoint.mp h.1.2.1).2⟩,
      ⟨Nat.le_refl _, Assignments.Le.refl _⟩, h.1.2, h.1.1.2⟩)
    fun i => ?_
  obtain ⟨st₂, hbitfacts, hsx₂, hsy₂⟩ := i
  have hextM : Mono (F := F) fun st => st₂.nv ≤ st.nv ∧ st₂.env.Le st.env :=
    fun _ _ hnv hle h => ⟨Nat.le_trans h.1 hnv, h.2.trans hle⟩
  -- the doubled seed: the finiteness and torsion side conditions are content the
  -- adapter search must not invent, so this step stays on the combinators
  refine Complete.bind
    (Complete.imp
      (fun st h => ⟨⟨hTread h.2.1, hTread h.2.1, h2T, fun _ => h2T⟩, h⟩)
      (fun _ _ h => h)
      (Complete.frame (Mono.and hextM (Mono.and Mono.readsAs Mono.readsAs))
        (addFast_complete .checkFinite d.W
          ⟨d.short.1, d.short.2.1, d.short.2.2.1, d.short.2.2.2⟩ d.two_ne base base
          (Point.some _ _ hT) (Point.some _ _ hT))))
    fun p => ?_
  -- the seed's coordinates index the rest, with the point they name on the index
  refine Complete.instantiate
    (ι := {q : F × F // ∃ h : d.W.Nonsingular q.1 q.2,
      Point.some _ _ hT + Point.some _ _ hT = Point.some q.1 q.2 h})
    (P := fun q st => (st₂.nv ≤ st.nv ∧ st₂.env.Le st.env) ∧
      CircuitType.ReadsAs (val := F) st p.p.x q.1.1 ∧
      CircuitType.ReadsAs (val := F) st p.p.y q.1.2 ∧
      CircuitType.ReadsAs (val := AffinePoint F) st base ⟨xv, yv⟩ ∧
      CircuitType.ReadsAs (val := F) st scalar.val sv)
    (fun st h => ⟨⟨(p.p.x.val st.env.get, p.p.y.val st.env.get), (h.1.2.2 h2T).2⟩,
      h.2.1,
      ⟨CircuitType.scoped_fvar.mpr (scoped_affinePoint.mp (h.1.2.2 h2T).1).1,
        CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (scoped_affinePoint.mp (h.1.2.2 h2T).1).2,
        CircuitType.reads_fvar.mpr rfl⟩,
      h.2.2.1, h.2.2.2⟩)
    fun q => ?_
  obtain ⟨⟨x0, y0⟩, hP0ns, hP0eq'⟩ := q
  have hP0eq : (2 : ℤ) • Point.some _ _ hT = Point.some x0 y0 hP0ns := by
    rw [two_zsmul]; exact hP0eq'
  have hP0at : ∀ {st : ProverState F},
      CircuitType.ReadsAs (val := F) st p.p.x x0 →
      CircuitType.ReadsAs (val := F) st p.p.y y0 →
      OnCurveAt d.W st.env.get p.p ((2 : ℤ) • Point.some _ _ hT) := by
    intro st hx hy
    rw [hP0eq]
    exact OnCurveAt.of_reads (p := p.p) (CircuitType.reads_fvar.mp hx.2)
      (CircuitType.reads_fvar.mp hy.2) hP0ns
  -- the rows' lsbBits: the reversed prefix of the scalar's lsbBits, MSB-first
  set bsOf : ℕ → F := fun k =>
    if (ToNat.toNat sv).testBit (5 * chunks - 1 - k) then 1 else 0 with hbsOf
  set msb : List (FVar F) := (lsbBits.toList.take (5 * chunks)).reverse with hmsb
  set window : ℕ → Vector (FVar F) 5 := fun i =>
    Vector.ofFn fun j : Fin 5 => msb.getD (5 * i + j.1) (CVar.const 0) with hwindow
  have hmsblen : msb.length = 5 * chunks := by
    rw [hmsb]
    simp only [List.length_reverse, List.length_take, Vector.length_toList]
    omega
  have hentry : ∀ (k : ℕ) (hk : k < 5 * chunks),
      msb.getD k (CVar.const 0) = lsbBits[5 * chunks - 1 - k]'(by omega) := by
    intro k hk
    rw [List.getD_eq_getElem _ _ (by rw [hmsblen]; exact hk)]
    simp only [hmsb, List.getElem_reverse, List.getElem_take, Vector.getElem_toList,
      List.length_take, Vector.length_toList]
    congr 1
    omega
  have hbitSc : ∀ (k : ℕ), k < 5 * chunks → (msb.getD k (CVar.const 0)).Scoped st₂ := by
    intro k hk
    rw [hentry k hk]
    exact (hbitfacts _ (by omega)).1
  have hbitVal : ∀ (stf : ProverState F), st₂.env.Le stf.env →
      ∀ (k : ℕ), k < 5 * chunks →
        (msb.getD k (CVar.const 0)).val stf.env.get = bsOf k := by
    intro stf hlef k hk
    rw [hentry k hk, CVar.val_of_le hlef (hbitfacts _ (by omega)).1,
      (hbitfacts _ (by omega)).2]
  -- the ladder
  have hP : ∀ x ∈ (List.range chunks).map window, VarBaseMul.BitRow st₂ x := by
    intro x hx v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hv)
    have hi' : i < chunks := by simpa using hi
    simp only [hwindow, Vector.getElem_ofFn]
    exact hbitSc (5 * i + j) (by omega)
  refine Complete.bind
    (Complete.imp
      (fun st h => ⟨⟨h.1, CircuitType.scoped_fvar.mp h.2.1.1,
        CircuitType.scoped_fvar.mp h.2.2.1.1, trivial⟩, h⟩)
      (fun _ _ h => h)
      (Complete.frame
        (Mono.and hextM (Mono.and Mono.readsAs (Mono.and Mono.readsAs
          (Mono.and Mono.readsAs Mono.readsAs))))
        (mapAccumM_complete (F := F) (c := KimchiConstraint F)
          (scaleRound base) (VarBaseMul.BitRow st₂) (fun _ => VarBaseMul.AccInv st₂)
          (VarBaseMul.RowGrant base) (fun _ => VarBaseMul.AccInv.mono)
          (VarBaseMul.RowGrant.mono base)
          (fun acc x _ hx =>
            VarBaseMul.scaleRound_complete st₂ base ⟨hsx₂, hsy₂⟩ acc x hx)
          (p.p, CVar.const 0) ((List.range chunks).map window) hP)))
    fun loop => ?_
  obtain ⟨rounds, fin⟩ := loop
  have hpreflen : ((List.range chunks).map window).length = chunks := by simp
  -- the honest walk
  set W : ℕ → Kimchi.Gate.VarBaseMul.Witness F :=
    Kimchi.Gate.VarBaseMul.chainBuild xv yv x0 y0 0 bsOf with hWdef
  have hWat : ∀ (stf : ProverState F), base.x.val stf.env.get = xv →
      base.y.val stf.env.get = yv → p.p.x.val stf.env.get = x0 →
      p.p.y.val stf.env.get = y0 →
      Kimchi.Gate.VarBaseMul.chainBuild (base.x.val stf.env.get)
          (base.y.val stf.env.get)
          ((p.p, (CVar.const 0 : FVar F)).1.x.val stf.env.get)
          ((p.p, (CVar.const 0 : FVar F)).1.y.val stf.env.get)
          ((p.p, (CVar.const 0 : FVar F)).2.val stf.env.get) bsOf = W := by
    intro stf h1 h2 h3 h4
    show Kimchi.Gate.VarBaseMul.chainBuild (base.x.val stf.env.get)
      (base.y.val stf.env.get) (p.p.x.val stf.env.get) (p.p.y.val stf.env.get)
      ((CVar.const 0 : FVar F).val stf.env.get) bsOf = _
    rw [h1, h2, h3, h4, hWdef]
    rfl
  have hbsbool : ∀ j : ℕ, j < 5 * chunks → bsOf j = 0 ∨ bsOf j = 1 := by
    intro j _
    simp only [hbsOf]
    split <;> simp
  have hgl : Kimchi.Gate.VarBaseMul.gateLadder W (5 * chunks)
      = Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat sv : ℤ) := by
    rw [Pasta.Shifted.unshiftType1, Kimchi.Gate.VarBaseMul.gateLadder_eq_register,
      Kimchi.Gate.VarBaseMul.gateRegister_eq_bitsVal, hWdef,
      Kimchi.Gate.VarBaseMul.runBits_chainBuild, hbsOf,
      Kimchi.Gate.VarBaseMul.bitsVal_testBit (ToNat.toNat sv) (5 * chunks) hfits]
  have hwalkHolds : ∀ i : ℕ, i < chunks → Kimchi.Gate.VarBaseMul.Holds (W i) := by
    have h := Kimchi.Gate.VarBaseMul.chain_complete d.W d.two_ne d.odd chunks hT bsOf
      hbsbool 0 hP0ns hP0eq.symm (by rw [← hWdef, hgl]; exact hregime)
    rw [← hWdef] at h
    exact h
  -- the rounds' readings are the walk's rows, at any table past the lsbBits
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
  -- every row of a granting trace holds, at any env-extension of its table
  have hpayAt : ∀ (st stf : ProverState F), st.env.Le stf.env →
      (st₂.nv ≤ st.nv ∧ st₂.env.Le st.env) →
      CircuitType.ReadsAs (val := AffinePoint F) st base ⟨xv, yv⟩ →
      CircuitType.ReadsAs (val := F) st p.p.x x0 →
      CircuitType.ReadsAs (val := F) st p.p.y y0 →
      ChainAt (VarBaseMul.RowGrant base) st (p.p, CVar.const 0)
        ((List.range chunks).map window) rounds fin →
      ∀ r ∈ rounds, Kimchi.Gate.VarBaseMul.Holds (ScaleRound.read stf.env.get r) := by
    intro st stf hle hext hseal hp2x hp2y hchain r hr
    have hnv := ProverState.nv_le_of_env_le hle
    have hlenR : rounds.length = chunks := by rw [ChainAt.length hchain, hpreflen]
    have hchain' := ChainAt.mono (VarBaseMul.RowGrant.mono base) hnv hle hchain
    have hseal' := CircuitType.ReadsAs.mono hnv hle hseal
    have hp2x' := CircuitType.ReadsAs.mono hnv hle hp2x
    have hp2y' := CircuitType.ReadsAs.mono hnv hle hp2y
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    rw [VarBaseMul.grants_walk base stf hchain'
        (fun k hk t ht => hbitsRead stf (hext.2.trans hle) k hk t ht) i hi,
      hWat stf (hscoords hseal').1 (hscoords hseal').2
        (CircuitType.reads_fvar.mp hp2x'.2) (CircuitType.reads_fvar.mp hp2y'.2)]
    exact hwalkHolds i (by rw [← hlenR]; exact hi)
  -- the bit stream a granting trace carries
  have hroundBits : ∀ (stf : ProverState F), st₂.env.Le stf.env →
      Chain (VarBaseMul.Threads base) (p.p, CVar.const 0)
        ((List.range chunks).map window) rounds fin →
      VarBaseMul.roundBits stf.env.get rounds = (List.range (5 * chunks)).map bsOf := by
    intro stf hlef hchain
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
  -- the one `varBaseMul` row
  refine Complete.bind (Complete.addConstraint ?row) fun _ => ?_
  case row =>
    rintro st ⟨⟨-, hchain⟩, hext, hp2x, hp2y, hseal, -⟩ stf hle
    exact hpayAt st stf hle hext hseal hp2x hp2y hchain
  -- the register pin, and the returned point
  refine Complete.bind
    (Complete.imp
      (fun st h => ⟨⟨⟨CircuitType.scoped_fvar.mpr h.1.1.2.2.2,
          CircuitType.reads_fvar.mpr ?pin⟩, h.2.2.2.2.2⟩, h⟩)
      (fun _ _ h => h)
      (Complete.frame
        (Mono.and (Mono.and (fun _ _ hnv hle h => VarBaseMul.AccInv.mono _ hnv hle h)
            (fun _ _ hnv hle h =>
              ChainAt.mono (VarBaseMul.RowGrant.mono base) hnv hle h))
          (Mono.and hextM (Mono.and Mono.readsAs (Mono.and Mono.readsAs
            (Mono.and Mono.readsAs Mono.readsAs)))))
        (assertEqual_complete (c := KimchiConstraint F) fin.2 scalar.val sv)))
    fun _ => Complete.pure_of fun st h => ?post
  case pin =>
    obtain ⟨⟨-, hchain⟩, hext, hp2x, hp2y, hseal, -⟩ := h
    obtain ⟨-, -, hreg, -⟩ :=
      VarBaseMul.run_sound d st.env.get (Point.some _ _ hT)
        (VarBaseMul.ChainAt.threads hchain)
        (hpayAt st st (Assignments.Le.refl _) hext hseal hp2x hp2y hchain)
        (hTread hseal).2 (hP0at hp2x hp2y)
    rw [hreg, hroundBits st hext.2 (VarBaseMul.ChainAt.threads hchain), hregSv]
  case post =>
    obtain ⟨-, ⟨hinv, hchain⟩, hext, hp2x, hp2y, hseal, -⟩ := h
    refine ⟨?_, ?_⟩
    · -- the lsbBits read as the scalar's own, as one bundle
      refine ⟨CircuitType.scoped_vector.mpr fun i hi => ?_,
        CircuitType.reads_vector.mpr fun i hi => ?_⟩
      · rw [getElem_mapVec]
        exact CircuitType.scoped_boolVar.mpr ((hbitfacts i hi).1.mono hext.1)
      · rw [getElem_mapVec]
        refine CircuitType.reads_boolVar.mpr ?_
        show (lsbBits[i]'hi).val st.env.get = _
        rw [CVar.val_of_le hext.2 (hbitfacts i hi).1, (hbitfacts i hi).2]
        simp [bit]
    · -- the point conclusion, off the sound side's own reading of the trace
      obtain ⟨-, -, -, hpoint⟩ :=
        VarBaseMul.run_sound d st.env.get (Point.some _ _ hT)
          (VarBaseMul.ChainAt.threads hchain)
          (hpayAt st st (Assignments.Le.refl _) hext hseal hp2x hp2y hchain)
          (hTread hseal).2 (hP0at hp2x hp2y)
      rw [hroundBits st hext.2 (VarBaseMul.ChainAt.threads hchain), hpreflen] at hpoint
      rw [hbsOf,
        Kimchi.Gate.VarBaseMul.bitsVal_testBit (ToNat.toNat sv) (5 * chunks) hfits]
        at hpoint
      exact ⟨scoped_affinePoint.mpr ⟨hinv.2.1, hinv.2.2.1⟩, hpoint hregime⟩

attribute [irreducible] lsbBitsWit varBaseMul

/-! ## `scaleFast1` -/

/-- `scaleFast1 g a ~ [fromShifted a]·g` (PS docstring) — the `Type1` path, for a
scalar field no larger than the circuit field. Drops the lsbBits. -/


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
        ∀ _ : d.LadderRegime (5 * chunks) (Pasta.Shifted.unshiftType1 (5 * chunks) z),
          OnCurveAt d.W V r ((Pasta.Shifted.unshiftType1 (5 * chunks) z) • T)⌝⦄ := by
  have hvbm := fun (V : Valuation F) => varBaseMul_spec (V := V) d n chunks hn base scalar
  unfold scaleFast1
  mvcgen [hvbm]
  rename_i r _ hr
  intro T hT
  obtain ⟨bs, -, hreg, hpoint⟩ := hr T hT
  refine ⟨(Kimchi.natLsbVal bs.toList : ℤ), Int.natCast_nonneg _, ?_, ?_, hpoint⟩
  · exact_mod_cast (by simpa using Kimchi.natLsbVal_lt bs.toList :
      Kimchi.natLsbVal bs.toList < 2 ^ (5 * chunks))
  · rw [hreg]
    push_cast
    ring

open WeierstrassCurve.Affine in
/-- **Completeness** (`scaleFast1`). `varBaseMul`'s honest run, with the bits dropped. -/
theorem scaleFast1_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (d : HasCurve F) (n chunks : ℕ) (hn : 5 * chunks ≤ n)
    (base : AffinePoint (FVar F)) (scalar : Type1 (FVar F)) (xv yv sv : F)
    (hT : d.W.Nonsingular xv yv) (hfits : ToNat.toNat sv < 2 ^ (5 * chunks))
    (hregime : d.LadderRegime (5 * chunks)
      (Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat sv : ℤ))) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => OnCurveAs d.W st base (Point.some _ _ hT) ∧
        CircuitType.ReadsAs (val := F) st scalar.val sv)
      (scaleFast1 (c := KimchiConstraint F) n chunks base scalar)
      (fun r st' => OnCurveAs d.W st' r
        ((Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat sv : ℤ)) • Point.some _ _ hT)) := by
  simp only [scaleFast1]
  refine Complete.bind
    (varBaseMul_complete d n chunks hn base scalar xv yv sv hT hfits hregime)
    fun r => Complete.pure_of fun _ h => h.2

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
  -- the pinned high bits: the ladder's integer fits the split's width
  have hzeros : ∀ b ∈ bs.toList.drop sDiv2Bits, b = false := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have hi' : sDiv2Bits + i < 5 * chunks := by
      simp only [List.length_drop, Vector.length_toList] at hi
      omega
    have hidx : sDiv2Bits + i < n := Nat.lt_of_lt_of_le hi' hn
    have hmem : rvb.lsbBits.toList[sDiv2Bits + i]'(by simpa using hidx)
        ∈ rvb.lsbBits.toList.drop sDiv2Bits := by
      have heq : (rvb.lsbBits.toList.drop sDiv2Bits)[i]'(by
          simp only [List.length_drop, Vector.length_toList]; omega)
          = rvb.lsbBits.toList[sDiv2Bits + i]'(by simpa using hidx) := List.getElem_drop ..
      rw [← heq]
      exact List.getElem_mem _
    have hb0 : bit bs[sDiv2Bits + i] = (0 : F) := by
      rw [← hread (sDiv2Bits + i) hi',
        show rvb.lsbBits[sDiv2Bits + i]'hidx
          = rvb.lsbBits.toList[sDiv2Bits + i]'(by simpa using hidx) from rfl,
        hpin0 _ hmem]
      simp [CVar.val]
    rw [List.getElem_drop, Vector.getElem_toList]
    cases hbb : bs[sDiv2Bits + i] with
    | false => rfl
    | true => rw [hbb] at hb0; simp [bit] at hb0
  have hltSplit : (Kimchi.natLsbVal bs.toList : ℤ) < 2 ^ sDiv2Bits := by
    exact_mod_cast Kimchi.natLsbVal_lt_of_drop_false hzeros
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
      (Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat sv : ℤ))) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => OnCurveAs d.W st base (Point.some _ _ hT) ∧
        CircuitType.ReadsAs (val := F) st sDiv2 sv ∧ CircuitType.ReadsAs (val := Bool) st sOdd bb)
      (scaleFast2 (c := KimchiConstraint F) n chunks sDiv2Bits base sDiv2 sOdd)
      (fun r st' => OnCurveAs d.W st' r
        ((Pasta.Shifted.unshiftType2 (5 * chunks) (ToNat.toNat sv : ℤ) (if bb then 1 else 0))
          • Point.some _ _ hT)) := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have hfits' : ToNat.toNat sv < 2 ^ (5 * chunks) :=
    lt_of_lt_of_le hfits (Nat.pow_le_pow_right (by norm_num) hsplit)
  -- the difference is finite: the regime keeps the result off the base
  have hoff : ((2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks)) • Point.some _ _ hT) ≠ 0 :=
    Kimchi.Gate.VarBaseMul.ladder_off_base d.W (Point.some_ne_zero hT) (5 * chunks)
      (ToNat.toNat sv) (by positivity) (by exact_mod_cast hfits') hregime
  have hsum : ((Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat sv : ℤ))
      • Point.some _ _ hT + -Point.some _ _ hT) ≠ 0 := by
    rw [show ((Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat sv : ℤ))
          • Point.some _ _ hT + -Point.some _ _ hT)
        = ((2 * (ToNat.toNat sv : ℤ) + 2 ^ (5 * chunks)) • Point.some _ _ hT) from by
        rw [Pasta.Shifted.unshiftType1]; module]
    exact hoff
  -- the negated base is a curve point wherever the base is
  have hnegT : ∀ {st : ProverState F}, OnCurveAs d.W st base (Point.some _ _ hT) →
      OnCurveAs d.W st ⟨base.x, CVar.negate_ base.y⟩ (-Point.some _ _ hT) := by
    intro st h
    obtain ⟨hbx, hby⟩ := scoped_affinePoint.mp h.1
    exact ⟨scoped_affinePoint.mpr ⟨hbx, CVar.Scoped.scale_ hby⟩,
      OnCurveAt.neg ⟨d.short.1, d.short.2.2.1⟩ h.2⟩
  simp only [scaleFast2]
  -- the ladder
  refine Complete.bind
    (Complete.imp (fun _ h => ⟨⟨h.1, h.2.1⟩, h.1, h.2.2⟩) (fun _ _ h => h)
      (Complete.frame (Mono.and Mono.onCurveAs Mono.readsAs)
        (varBaseMul_complete d n chunks hn base ⟨sDiv2⟩ xv yv sv hT hfits' hregime)))
    fun r => ?_
  -- the ladder's point never vanishes
  have hGneAt : ∀ {st : ProverState F},
      OnCurveAs d.W st r.g
        ((Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat sv : ℤ))
          • Point.some _ _ hT) →
      ((Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat sv : ℤ))
        • Point.some _ _ hT) ≠ 0 := by
    intro st h
    obtain ⟨hGns, hGeq⟩ := h.2
    rw [hGeq]
    exact Point.some_ne_zero hGns
  -- the high bits the honest scalar leaves clear
  have hpinval : ∀ {st : ProverState F},
      CircuitType.ReadsAs (val := Vector Bool n) st (mapVec BoolVar.unchecked r.lsbBits)
          (unpackPure sv n) →
      ∀ x ∈ r.lsbBits.toList.drop sDiv2Bits, x.Scoped st ∧ x.val st.env.get = 0 := by
    intro st hbits x hx
    have hbitsSc := CircuitType.scoped_vector.mp hbits.1
    have hbitsRd := CircuitType.reads_vector.mp hbits.2
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hi' : sDiv2Bits + i < n := by
      simp only [List.length_drop, Vector.length_toList] at hi
      omega
    have hbit : (ToNat.toNat sv).testBit (sDiv2Bits + i) = false :=
      Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hfits (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have hsc := hbitsSc (sDiv2Bits + i) hi'
    have hval := hbitsRd (sDiv2Bits + i) hi'
    rw [getElem_mapVec] at hsc hval
    simp only [List.getElem_drop, Vector.getElem_toList]
    refine ⟨CircuitType.scoped_boolVar.mp hsc, ?_⟩
    show (BoolVar.unchecked (r.lsbBits[sDiv2Bits + i]'hi')).toCVar.val st.env.get = 0
    rw [CircuitType.reads_boolVar.mp hval]
    simp [hbit, bit]
  have hpinM : Mono (F := F) fun st => ∀ x ∈ r.lsbBits.toList.drop sDiv2Bits,
      x.Scoped st ∧ x.val st.env.get = 0 :=
    fun _ _ hnv hle h x hx => ⟨(h x hx).1.mono hnv,
      by rw [CVar.val_of_le hle (h x hx).1]; exact (h x hx).2⟩
  -- pin the high bits
  refine Complete.bind
    (Complete.imp (fun st h => ⟨hpinval h.1.1, h.1.2, h.2.1, h.2.2⟩) (fun _ _ h => h)
      (Complete.frame
        (Mono.and Mono.onCurveAs (Mono.and Mono.onCurveAs Mono.readsAs))
        (forM_complete (F := F) (c := KimchiConstraint F)
          (fun b : FVar F => assertEqual b (CVar.const 0))
          (fun b => b ∈ r.lsbBits.toList.drop sDiv2Bits)
          (fun _ st => ∀ x ∈ r.lsbBits.toList.drop sDiv2Bits,
            x.Scoped st ∧ x.val st.env.get = 0)
          (fun b _ hb =>
            Complete.imp
              (fun st hstc => ⟨⟨⟨CircuitType.scoped_fvar.mpr (hstc b hb).1,
                  CircuitType.reads_fvar.mpr (hstc b hb).2⟩,
                CircuitType.scoped_fvar.mpr trivial, CircuitType.reads_fvar.mpr rfl⟩,
                hstc⟩)
              (fun _ _ h => h.2)
              (Complete.frame hpinM
                (assertEqual_complete (c := KimchiConstraint F) b (CVar.const 0) 0)))
          (r.lsbBits.toList.drop sDiv2Bits) (fun x hx => hx))))
    fun _ => ?_
  -- the parity fold's subtraction
  refine Complete.bind
    (Complete.imp
      (fun st h => ⟨⟨h.2.1, hnegT h.2.2.1,
        d.two_torsion_free _ (hGneAt h.2.1), fun _ => hsum⟩, h.2.1, h.2.2.2⟩)
      (fun _ _ h => h)
      (Complete.frame (Mono.and Mono.onCurveAs Mono.readsAs)
        (addFast_complete .checkFinite d.W
          ⟨d.short.1, d.short.2.1, d.short.2.2.1, d.short.2.2.2⟩ d.two_ne r.g
          ⟨base.x, CVar.negate_ base.y⟩
          ((Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat sv : ℤ))
            • Point.some _ _ hT)
          (-Point.some _ _ hT))))
    fun q => ?_
  -- the two points' coordinates index the selects
  refine Complete.instantiate
    (ι := {v : F × F × F × F //
      Kimchi.Gate.AddComplete.IsPoint d.W v.1 v.2.1
        ((Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat sv : ℤ))
          • Point.some _ _ hT) ∧
      Kimchi.Gate.AddComplete.IsPoint d.W v.2.2.1 v.2.2.2
        ((Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat sv : ℤ))
          • Point.some _ _ hT + -Point.some _ _ hT)})
    (P := fun v st =>
      CircuitType.ReadsAs (val := F) st r.g.x v.1.1 ∧
      CircuitType.ReadsAs (val := F) st r.g.y v.1.2.1 ∧
      CircuitType.ReadsAs (val := F) st q.p.x v.1.2.2.1 ∧
      CircuitType.ReadsAs (val := F) st q.p.y v.1.2.2.2 ∧
      CircuitType.ReadsAs (val := Bool) st sOdd bb)
    (fun st h => ?inst) fun v => ?_
  case inst =>
    obtain ⟨⟨-, -, hQ⟩, hG, hsOdd⟩ := h
    have hQpt := hQ hsum
    exact ⟨⟨(r.g.x.val st.env.get, r.g.y.val st.env.get,
        q.p.x.val st.env.get, q.p.y.val st.env.get), hG.2, hQpt.2⟩,
      ⟨CircuitType.scoped_fvar.mpr (scoped_affinePoint.mp hG.1).1,
        CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (scoped_affinePoint.mp hG.1).2,
        CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (scoped_affinePoint.mp hQpt.1).1,
        CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (scoped_affinePoint.mp hQpt.1).2,
        CircuitType.reads_fvar.mpr rfl⟩, hsOdd⟩
  obtain ⟨⟨gx, gy, qx, qy⟩, hGpt, hQpt⟩ := v
  -- the point conditional selects coordinatewise, `y` before `x`
  refine Complete.bind
    (Complete.imp
      (fun st h => ⟨⟨h.2.2.2.2, h.2.1, h.2.2.2.1⟩, h.1, h.2.2.1, h.2.2.2.2⟩)
      (fun _ _ h => h)
      (Complete.frame
        (Mono.and Mono.readsAs (Mono.and Mono.readsAs Mono.readsAs))
        (selectField_complete (c := KimchiConstraint F) sOdd r.g.y q.p.y bb gy qy)))
    fun yr => ?_
  refine Complete.bind
    (Complete.imp
      (fun st h => ⟨⟨h.2.2.2, h.2.1, h.2.2.1⟩, h.1⟩)
      (fun _ _ h => h)
      (Complete.frame Mono.readsAs
        (selectField_complete (c := KimchiConstraint F) sOdd r.g.x q.p.x bb gx qx)))
    fun xr => Complete.pure_of fun st h => ?post
  case post =>
    obtain ⟨hxr, hyr⟩ := h
    refine ⟨scoped_affinePoint.mpr ⟨CircuitType.scoped_fvar.mp hxr.1,
      CircuitType.scoped_fvar.mp hyr.1⟩, ?_⟩
    have hx := CircuitType.reads_fvar.mp hxr.2
    have hy := CircuitType.reads_fvar.mp hyr.2
    cases bb with
    | false =>
      show Kimchi.Gate.AddComplete.IsPoint d.W (xr.val st.env.get) (yr.val st.env.get)
        ((Pasta.Shifted.unshiftType2 (5 * chunks) (ToNat.toNat sv : ℤ) 0)
          • Point.some _ _ hT)
      rw [hx, hy, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
        show ((Pasta.Shifted.unshiftType2 (5 * chunks) (ToNat.toNat sv : ℤ) 0)
            • Point.some _ _ hT)
          = ((Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat sv : ℤ))
              • Point.some _ _ hT + -Point.some _ _ hT) from by
          rw [Pasta.Shifted.unshiftType2, Pasta.Shifted.unshiftType1]; module]
      exact hQpt
    | true =>
      show Kimchi.Gate.AddComplete.IsPoint d.W (xr.val st.env.get) (yr.val st.env.get)
        ((Pasta.Shifted.unshiftType2 (5 * chunks) (ToNat.toNat sv : ℤ) 1)
          • Point.some _ _ hT)
      rw [hx, hy, if_pos rfl, if_pos rfl,
        show ((Pasta.Shifted.unshiftType2 (5 * chunks) (ToNat.toNat sv : ℤ) 1)
            • Point.some _ _ hT)
          = ((Pasta.Shifted.unshiftType1 (5 * chunks) (ToNat.toNat sv : ℤ))
              • Point.some _ _ hT) from by
          rw [Pasta.Shifted.unshiftType2, Pasta.Shifted.unshiftType1]; module]
      exact hGpt

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
    Complete (F := F) (c := c) (fun st => CircuitType.ReadsAs (val := F) st s sval)
      (splitFieldVar (c := c) s)
      (fun r st' => CircuitType.ReadsAs (val := F) st' r.1 (splitField sval).1 ∧
        CircuitType.ReadsAs (val := Bool) st' r.2 (splitField sval).2) := by
  have hjoin : 2 * (splitField sval).1 + bit (splitField sval).2 = sval := by
    simp only [splitField, bit, decide_eq_true_eq]
    split <;> field_simp <;> ring
  simp only [splitFieldVar]
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?wrun, h⟩) (fun _ _ h => h)
      (Complete.frame Mono.readsAs
        (Complete.witness (splitFieldWit s)
          ((splitField sval).1, (splitField sval).2) (by simp))))
    fun w => ?_
  case wrun =>
    simp only [splitFieldWit, AsProver.bind_eq, AsProver.run_bind,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.1),
      CircuitType.reads_fvar.mp h.2, Except.bind]
    rfl
  obtain ⟨wD, wO⟩ := w
  -- the witnessed pair, componentwise
  have hw : ∀ {st : ProverState F},
      CircuitType.ReadsAs (val := F × Bool) st (wD, wO)
          ((splitField sval).1, (splitField sval).2) →
        wD.Scoped st ∧ wD.val st.env.get = (splitField sval).1 ∧
        (↑wO : CVar F).Scoped st ∧
        (↑wO : CVar F).val st.env.get = bit (splitField sval).2 := by
    intro st h
    have hsc := h.1
    have hrd := h.2
    simp only [CircuitType.scoped_prod, CircuitType.scoped_fvar,
      CircuitType.scoped_boolVar] at hsc
    simp only [CircuitType.reads_prod, CircuitType.reads_fvar] at hrd
    exact ⟨hsc.1, hrd.1, hsc.2, CircuitType.reads_boolVar.mp hrd.2⟩
  refine Complete.bind
    (Complete.imp
      (fun st h => ⟨⟨h.2,
        ⟨CircuitType.scoped_fvar.mpr
            (CVar.Scoped.add_ (CVar.Scoped.scale_ (hw h.1).1) (hw h.1).2.2.1),
          CircuitType.reads_fvar.mpr (by
            rw [CVar.val_add_, CVar.val_scale_, (hw h.1).2.1, (hw h.1).2.2.2,
              hjoin])⟩⟩, h.1⟩)
      (fun _ _ h => h)
      (Complete.frame Mono.readsAs
        (assertEqual_complete (c := c) s (CVar.add_ (CVar.scale_ 2 wD) ↑wO) sval)))
    fun _ => Complete.pure_of fun st h =>
      ⟨⟨CircuitType.scoped_fvar.mpr (hw h.2).1,
        CircuitType.reads_fvar.mpr (hw h.2).2.1⟩,
      ⟨CircuitType.scoped_boolVar.mpr (hw h.2).2.2.1,
        CircuitType.reads_boolVar.mpr (hw h.2).2.2.2⟩⟩

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
        ∀ _ : d.LadderRegime (5 * chunks) (Pasta.Shifted.unshiftType1 (5 * chunks) z),
          OnCurveAt d.W V r
            ((Pasta.Shifted.unshiftType2 (5 * chunks) z (if bb then 1 else 0)) • T)⌝⦄ := by
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
      (Pasta.Shifted.unshiftType1 (5 * chunks) ((ToNat.toNat (splitField sval).1 : ℤ)))) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => OnCurveAs d.W st base (Point.some _ _ hT) ∧
        CircuitType.ReadsAs (val := F) st s sval)
      (scaleFast2' (c := KimchiConstraint F) n chunks sDiv2Bits base s)
      (fun r st' => OnCurveAs d.W st' r
        ((2 * (ToNat.toNat (splitField sval).1 : ℤ)
            + (if (splitField sval).2 then 1 else 0) + 2 ^ (5 * chunks))
          • Point.some _ _ hT)) := by
  simp only [scaleFast2']
  refine Complete.bind
    (Complete.imp (fun _ h => ⟨h.2, h.1⟩) (fun _ _ h => h)
      (Complete.frame Mono.onCurveAs
        (splitFieldVar_complete (c := KimchiConstraint F) d.two_ne s sval)))
    fun w =>
      Complete.imp (fun _ h => ⟨h.2, h.1.1, h.1.2⟩) (fun _ _ h => h)
        (scaleFast2_complete d n chunks sDiv2Bits hn hsplit base w.1 w.2 xv yv
          (splitField sval).1 (splitField sval).2 hT hfits hregime)

attribute [irreducible] scaleFast2'

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta Kimchi.Gate.VarBaseMul
  WeierstrassCurve.Affine in
/-- **The deployed ladder leg's honest run.** At Vesta, on a base on the curve and a
`Type1` carrier off the ladder's forbidden band, the run succeeds and the result is the
base scaled by the carrier's decode. The width fits and the regime holds for free here:
a carrier's representative is below `|Fq| < 2^255`, and the band exclusion IS the
regime. -/
theorem vesta_varBaseMul_complete {base : AffinePoint (FVar Fq)} {sv : Type1 (FVar Fq)}
    {xv yv : Fq} {Z : Type1 Fq} (hT : Vesta.curve.toAffine.Nonsingular xv yv)
    (hband : Z.toScalarZ ∉ forbiddenValues PALLAS_BASE_CARD) :
    Complete (F := Fq) (c := KimchiConstraint Fq)
      (fun st => OnCurveAs Vesta.curve.toAffine st base (Point.some _ _ hT) ∧
        CircuitType.ReadsAs (val := Fq) st sv.val Z.val)
      (varBaseMul (c := KimchiConstraint Fq) 255 51 base sv)
      (fun r st' =>
        CircuitType.ReadsAs (val := Vector Bool 255) st'
          (mapVec BoolVar.unchecked r.lsbBits) (unpackPure Z.val 255) ∧
        OnCurveAs Vesta.curve.toAffine st' r.g (Z.toScalarZ • Point.some _ _ hT)) := by
  have hval : ToNat.toNat Z.val = Z.val.val := rfl
  have hdec : Pasta.Shifted.unshiftType1 (5 * 51) (ToNat.toNat Z.val : ℤ) = Z.toScalarZ := by
    simp only [hval, Type1.toScalarZ, Type1.fromShifted, Pasta.Shifted.unshiftType1]
  have hfits : ToNat.toNat Z.val < 2 ^ (5 * 51) := by
    rw [hval]
    exact lt_of_lt_of_le (ZMod.val_lt _) (by decide)
  exact hdec ▸ varBaseMul_complete HasCurve.vesta 255 51 (by norm_num) base sv xv yv Z.val hT
    hfits (hdec ▸ vesta_ladderRegime Z hband)

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta Kimchi.Gate.VarBaseMul in
/-- **The deployed ladder leg.** At Vesta, the generic law's output on a `Type1` carrier
off the ladder's forbidden band, whose 255 witnessed bits read as a value below the
scalar order, says the result is the base point scaled by the carrier's decode.

The generic post pins the ladder's integer only through the LSB-first value of its own
bits and guards its conclusion on an abstract `LadderRegime`; the bit bound identifies
that integer with the carrier's canonical representative, and the deployed order
discharges the guard. Neither is visible here.

Stated on the generic law's OUTPUT rather than as a triple, for the same reason as
`vesta_endoMul_read`: a consumer reaches it holding that output. -/
theorem vesta_varBaseMul_read {V : Valuation Fq} {base : AffinePoint (FVar Fq)}
    {sv : Type1 (FVar Fq)} {r : VarBaseMulResult 255 Fq} {Z : Type1 Fq}
    (hread : sv.val.val V = Z.val)
    (hband : Z.toScalarZ ∉ forbiddenValues PALLAS_BASE_CARD)
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
  rw [hZ]
  exact hact (hZ ▸ vesta_ladderRegime Z hband)

end Snarky.Kimchi
