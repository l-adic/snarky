import Snarky.Circuit.DSL.Field
import Snarky.Circuit.DSL.Assert
import Snarky.Circuit.DSL.Bits
import Snarky.Circuit.DSL.Boolean
import Snarky.Types.Shifted
import Snarky.Kimchi.Circuit.AddComplete
import Snarky.Kimchi.Circuit.Utils
import Kimchi.Gate.VarBaseMul
import Kimchi.Gate.Semantics.VarBaseMul
import Kimchi.Gate.Semantics.EndoMul
import Pasta.Basic

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
open Pasta.Shifted (unshiftType1 unshiftType2)

variable {F c : Type}

/-- The scalar's `n` bits LSB-first as field values. -/
private def lsbVals [Zero F] [One F] (n k : ℕ) : Vector F n :=
  Vector.ofFn fun i => if k.testBit i.1 then 1 else 0

/-- The scalar's `n` bits, in ONE witness (PS `unpackPure` under a single `exists`). -/
private def lsbBitsWit [Field F] [ToNat F] (n : ℕ) (scalar : FVar F) :
    AsProver F (Vector F n) := do
  let v ← AsProver.readCVar scalar
  pure (lsbVals n (ToNat.toNat v))

/-- The register update at a chunk's five bits: `2a + b` folded from the previous
register (PS's `foldl (\a b -> double a + b)`). -/
private def nAccVal [Field F] (a b0 b1 b2 b3 b4 : F) : F :=
  b4 + 2 * (b3 + 2 * (b2 + 2 * (b1 + 2 * (b0 + 2 * a))))

/-- Per-chunk scalar-register advice: `nAccVal` at the cells' readings. -/
private def nAccWit [Field F] (nPrev : FVar F) (bs : Vector (FVar F) 5) :
    AsProver F F := do
  let a ← AsProver.readCVar nPrev
  let b0 ← AsProver.readCVar bs[0]
  let b1 ← AsProver.readCVar bs[1]
  let b2 ← AsProver.readCVar bs[2]
  let b3 ← AsProver.readCVar bs[3]
  let b4 ← AsProver.readCVar bs[4]
  pure (nAccVal a b0 b1 b2 b3 b4)

/-- One bit step's advice quintet `(s1, s1Sq, s2, xRes, yRes)` at a bit and the base
and accumulator readings: the wired slope and result from the gate model's `stepBit`,
plus the two dead registers. -/
private def stepQuint [Field F] (bv xb yb xi yi : F) : F × F × F × F × F :=
  let q := Kimchi.Gate.VarBaseMul.stepBit bv xb yb xi yi
  (q.1, q.1 * q.1, 2 * yi / (2 * xi + xb - q.1 * q.1) - q.1, q.2.1, q.2.2)

/-- One bit step's advice: `stepQuint` at the cells' readings. -/
private def bitWit [Field F] [DecidableEq F] (t : AffinePoint (FVar F))
    (b : FVar F) (acc : AffinePoint (FVar F)) :
    AsProver F (F × F × F × F × F) := do
  let xb ← AsProver.readCVar t.x
  let yb ← AsProver.readCVar t.y
  let xi ← AsProver.readCVar acc.x
  let yi ← AsProver.readCVar acc.y
  let bv ← AsProver.readCVar b
  pure (stepQuint bv xb yb xi yi)

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

/-- `scaleFast1 g a ~ [fromShifted a]·g` (PS docstring) — the `Type1` path, for a
scalar field no larger than the circuit field. Drops the bits. -/
def scaleFast1 [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (n chunks : ℕ) (p : AffinePoint (FVar F))
    (t : Type1 (FVar F)) : CircuitM F c (AffinePoint (FVar F)) := do
  let r ← varBaseMul n chunks p t
  pure r.g

/-- `scaleFast2 g (sDiv2, sOdd) ~ [2·sDiv2 + sOdd + 2^n]·g` — the split path, for a
scalar field larger than the circuit field: run the ladder on `sDiv2`, pin its high
bits to zero, and fold the parity in by conditionally subtracting the base. -/
def scaleFast2 [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (n chunks sDiv2Bits : ℕ) (base : AffinePoint (FVar F))
    (sDiv2 : FVar F) (sOdd : BoolVar F) : CircuitM F c (AffinePoint (FVar F)) := do
  let r ← varBaseMul n chunks base ⟨sDiv2⟩
  for bit in r.lsbBits.toList.drop sDiv2Bits do
    assertEqual bit (.const 0)
  -- the else branch first (PS `if_ sOdd g =<< …`): `g − base` via the pure negation
  let negBase : AffinePoint (FVar F) := ⟨base.x, CVar.negate_ base.y⟩
  let q ← addFast .checkFinite r.g negBase
  -- the point conditional selects coordinatewise, `y` BEFORE `x`: PS's record `if_`
  -- builds right-to-left (the fixture pins the emission order)
  let y ← select sOdd r.g.y q.p.y
  let x ← select sOdd r.g.x q.p.x
  pure ⟨x, y⟩

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

/-! ## The ladder regime and the soundness laws -/

open Std.Do WeierstrassCurve.Affine

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

open CompElliptic.Fields.Pasta in
open Kimchi.Gate.VarBaseMul (forbiddenValues) in
/-- The deployed ladder accepts any `Type1` carrier whose decode is off the forbidden
set: Vesta sits in the one-wrap band at 255 bits. -/
theorem vesta_ladderRegime (t : Type1 Fq)
    (hband : t.fromShiftedZ ∉ forbiddenValues PALLAS_BASE_CARD) :
    HasCurve.vesta.LadderRegime 255 t.fromShiftedZ := by
  have hOv : HasCurve.vesta.W.order = PALLAS_BASE_CARD := Pasta.vesta_card
  refine Or.inr ⟨?_, ?_, ?_, ?_⟩ <;> rw [hOv]
  · decide
  · decide
  · decide
  · exact hband

namespace VarBaseMul

/-- The loop's structural view: the collected rounds are the chain-threaded records
over the traversed chunks — each round's `(acc0, nPrev)` are the previous round's
output variables, from `st` to `fin`, and every round shares the sealed base.
Valuation-free: the soundness invariant carries shape only; the values arrive with
the constraint after the loop. -/
private def Threaded (base : AffinePoint (FVar F)) :
    (AffinePoint (FVar F) × FVar F) → List (Vector (FVar F) 5) →
    List (ScaleRound F) → (AffinePoint (FVar F) × FVar F) → Prop
  | st, [], rounds, fin => rounds = [] ∧ fin = st
  | st, bs :: rest, rounds, fin =>
    ∃ (nAcc : FVar F)
      (w0 w1 w2 w3 w4 : FVar F × FVar F × FVar F × FVar F × FVar F)
      (tail : List (ScaleRound F)),
      rounds = ({ acc0 := st.1,
                  acc1 := ⟨w0.2.2.2.1, w0.2.2.2.2⟩, acc2 := ⟨w1.2.2.2.1, w1.2.2.2.2⟩,
                  acc3 := ⟨w2.2.2.2.1, w2.2.2.2.2⟩, acc4 := ⟨w3.2.2.2.1, w3.2.2.2.2⟩,
                  acc5 := ⟨w4.2.2.2.1, w4.2.2.2.2⟩,
                  bit0 := bs[0], bit1 := bs[1], bit2 := bs[2], bit3 := bs[3],
                  bit4 := bs[4],
                  slope0 := w0.1, slope1 := w1.1, slope2 := w2.1, slope3 := w3.1,
                  slope4 := w4.1,
                  nPrev := st.2, nNext := nAcc, base } : ScaleRound F) :: tail ∧
      Threaded base (⟨w4.2.2.2.1, w4.2.2.2.2⟩, nAcc) rest tail fin

/-- One more chunk extends a threading at the tail. -/
private theorem Threaded.snoc {base : AffinePoint (FVar F)} :
    ∀ {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 5)}
      {rounds : List (ScaleRound F)},
      Threaded base st pref rounds fin →
      ∀ (bs : Vector (FVar F) 5) (nAcc : FVar F)
        (w0 w1 w2 w3 w4 : FVar F × FVar F × FVar F × FVar F × FVar F),
      Threaded base st (pref ++ [bs])
        (rounds ++ [{ acc0 := fin.1,
                      acc1 := ⟨w0.2.2.2.1, w0.2.2.2.2⟩,
                      acc2 := ⟨w1.2.2.2.1, w1.2.2.2.2⟩,
                      acc3 := ⟨w2.2.2.2.1, w2.2.2.2.2⟩,
                      acc4 := ⟨w3.2.2.2.1, w3.2.2.2.2⟩,
                      acc5 := ⟨w4.2.2.2.1, w4.2.2.2.2⟩,
                      bit0 := bs[0], bit1 := bs[1], bit2 := bs[2], bit3 := bs[3],
                      bit4 := bs[4],
                      slope0 := w0.1, slope1 := w1.1, slope2 := w2.1,
                      slope3 := w3.1, slope4 := w4.1,
                      nPrev := fin.2, nNext := nAcc, base }])
        (⟨w4.2.2.2.1, w4.2.2.2.2⟩, nAcc)
  | st, fin, [], rounds, h, bs, nAcc, w0, w1, w2, w3, w4 => by
    obtain ⟨hr, hfin⟩ := h
    subst hr hfin
    exact ⟨nAcc, w0, w1, w2, w3, w4, [], rfl, rfl, rfl⟩
  | st, fin, chunk :: rest, rounds, h, bs, nAcc, w0, w1, w2, w3, w4 => by
    obtain ⟨nAcc', v0, v1, v2, v3, v4, tail, hr, hrest⟩ := h
    subst hr
    exact ⟨nAcc', v0, v1, v2, v3, v4, tail ++ [_], rfl,
      hrest.snoc bs nAcc w0 w1 w2 w3 w4⟩

/-- An empty threading traversed no chunks: the final pair is the start. -/
private theorem Threaded.nil {base : AffinePoint (FVar F)} :
    ∀ {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 5)},
      Threaded base st pref [] fin → pref = [] ∧ fin = st
  | _, _, [], h => ⟨rfl, h.2⟩
  | _, _, _ :: _, h => by
    obtain ⟨nAcc, w0, w1, w2, w3, w4, tail, heq, -⟩ := h
    exact nomatch heq

/-- The structural facts of a nonempty threading: the round count, the shared base,
round `0`'s seed wiring, the shared accumulator/register variables between adjacent
rounds, and the final pair's wiring — everything the per-round reading and
`varBaseMul_off` consume, extracted without touching a valuation. -/
private theorem threaded_chain {base : AffinePoint (FVar F)} :
    ∀ {pref : List (Vector (FVar F) 5)} {st fin : AffinePoint (FVar F) × FVar F}
      {r₀ : ScaleRound F} {rs : List (ScaleRound F)},
      Threaded base st pref (r₀ :: rs) fin →
      (r₀ :: rs).length = pref.length ∧
      (∀ i (hi : i < (r₀ :: rs).length), (r₀ :: rs)[i].base = base) ∧
      (r₀.acc0 = st.1 ∧ r₀.nPrev = st.2) ∧
      (∀ i (hi : i + 1 < (r₀ :: rs).length),
        (r₀ :: rs)[i + 1].acc0 = (r₀ :: rs)[i].acc5 ∧
        (r₀ :: rs)[i + 1].nPrev = (r₀ :: rs)[i].nNext) ∧
      (fin.1 = (r₀ :: rs)[rs.length].acc5 ∧ fin.2 = (r₀ :: rs)[rs.length].nNext)
  | x :: rest, st, fin, r₀, rs, h => by
    obtain ⟨nAcc, w0, w1, w2, w3, w4, tail, heq, hrest⟩ := h
    injection heq with h1 h2
    subst h1 h2
    cases rs with
    | nil =>
      obtain ⟨rfl, rfl⟩ := Threaded.nil hrest
      refine ⟨rfl, ?_, ⟨rfl, rfl⟩, fun i hi => by simp at hi, ⟨rfl, rfl⟩⟩
      intro i hi
      cases i with
      | zero => rfl
      | succ j => simp at hi
    | cons r₁ ts =>
      obtain ⟨ihlen, ihbase, ⟨e1, e2⟩, ihstep, ihlast⟩ := threaded_chain hrest
      refine ⟨by simpa using ihlen, ?_, ⟨rfl, rfl⟩, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => rfl
        | succ j =>
          have hj : j < (r₁ :: ts).length := by simpa using hi
          simpa only [List.getElem_cons_succ] using ihbase j hj
      · intro i hi
        cases i with
        | zero =>
          simpa only [List.getElem_cons_succ, List.getElem_cons_zero] using ⟨e1, e2⟩
        | succ j =>
          have hj : j + 1 < (r₁ :: ts).length := by simpa using hi
          simpa only [List.getElem_cons_succ] using ihstep j hj
      · obtain ⟨f1, f2⟩ := ihlast
        simpa only [List.length_cons, List.getElem_cons_succ] using ⟨f1, f2⟩

/-- The rounds' wired bits, in ladder order — the list the law's promise ties to the
returned bit vector. -/
private def roundBits (rounds : List (ScaleRound F)) : List (FVar F) :=
  rounds.flatMap fun r => [r.bit0, r.bit1, r.bit2, r.bit3, r.bit4]

/-- A threading's round bits are its traversed chunks' entries, in order. -/
private theorem threaded_roundBits {base : AffinePoint (FVar F)} :
    ∀ {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 5)}
      {rounds : List (ScaleRound F)},
      Threaded base st pref rounds fin →
      roundBits rounds = pref.flatMap fun bs => [bs[0], bs[1], bs[2], bs[3], bs[4]]
  | st, fin, [], rounds, h => by
    obtain ⟨rfl, -⟩ := h
    rfl
  | st, fin, bs :: rest, rounds, h => by
    obtain ⟨nAcc, w0, w1, w2, w3, w4, tail, rfl, hrest⟩ := h
    simp only [roundBits, List.flatMap_cons]
    exact congrArg _ (threaded_roundBits hrest)

open Kimchi.Gate.VarBaseMul in
/-- The run reading's bits are the rounds' bit variables' values, in order. -/
private theorem read_runBits [Field F] [DecidableEq F] {V : Valuation F} :
    ∀ (rounds : List (ScaleRound F)) (dflt : ScaleRound F),
      runBits (fun i => ScaleRound.read V (rounds.getD i dflt)) rounds.length
        = (roundBits rounds).map (·.val V) := by
  intro rounds
  induction rounds using List.reverseRecOn with
  | nil => intro dflt; rfl
  | append_singleton rs r ih =>
    intro dflt
    have hlen : (rs ++ [r]).length = rs.length + 1 := by simp
    rw [hlen, runBits_succ,
      runBits_congr _ (fun i => ScaleRound.read V (rs.getD i dflt)) rs.length
        (fun i hi => by rw [List.getD_append _ _ _ _ hi]),
      ih dflt,
      show (rs ++ [r]).getD rs.length dflt = r from by
        rw [List.getD_eq_getElem _ _ (by simp)]
        simp]
    simp [roundBits, List.flatMap_append, ScaleRound.read]

/-- Flattening the 5-bit windows of a list of exactly `5·c` entries recovers it —
the gate model's window tiling (`flatMap_range_window`) read through `getD`. -/
private theorem flatMap_window {α : Type} (dflt : α) (c : ℕ) (l : List α)
    (hl : l.length = 5 * c) :
    (List.range c).flatMap (fun i =>
      [l.getD (5 * i) dflt, l.getD (5 * i + 1) dflt, l.getD (5 * i + 2) dflt,
       l.getD (5 * i + 3) dflt, l.getD (5 * i + 4) dflt]) = l := by
  rw [Kimchi.Gate.VarBaseMul.flatMap_range_window (fun i => l.getD i dflt) c]
  refine List.ext_getElem (by simp [hl]) (fun i h1 h2 => ?_)
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa [hl] using h1)]

open Kimchi.Gate.VarBaseMul in
/-- A satisfied threading from the doubled-base init computes the ladder: the
structural wiring (`threaded_chain`) turns the per-round reading into
`varBaseMul_off`'s indexed run — the register chain (`chain_accN`) reads the final
register as the bits' base-2 fold, the point chain the final accumulator as the
Type1-unshift multiple. The gadget layer contributes wiring only; the mathematics is
the gate-semantics theorems'. The empty run returns the init `[2]·T` — the decode of
no bits. -/
private theorem threaded_sound [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F)
    [Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)] [Fact (Nat.Prime W.order)]
    (h2 : (2 : F) ≠ 0) (hodd : W.order ≠ 2)
    (V : Valuation F) {base P0 : AffinePoint (FVar F)}
    {pref : List (Vector (FVar F) 5)} {rounds : List (ScaleRound F)}
    {fin : AffinePoint (FVar F) × FVar F}
    (hthr : Threaded base (P0, .const 0) pref rounds fin)
    (hpay : ∀ r ∈ rounds, Kimchi.Gate.VarBaseMul.Holds (ScaleRound.read V r))
    (hT : W.Nonsingular (base.x.val V) (base.y.val V))
    (hP0ns : W.Nonsingular (P0.x.val V) (P0.y.val V))
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • Point.some _ _ hT) :
    ∃ (bl : List F) (bs : List Bool),
      (∀ b ∈ bl, b = 0 ∨ b = 1) ∧ bl = (roundBits rounds).map (·.val V) ∧
      bs = (bl.map fun b => decide (b = 1)).reverse ∧
      fin.2.val V = ((natLsbVal bs : ℕ) : F) ∧
      ∀ _ : (3 : ℕ) * 2 ^ (5 * pref.length) ≤ W.order ∨
          (2 ^ (5 * pref.length - 1) < W.order ∧ W.order < 2 ^ (5 * pref.length) ∧
            W.order % 4 = 1 ∧
            unshiftType1 (5 * pref.length) (natLsbVal bs : ℤ) ∉ forbiddenValues W.order),
        ∃ hfin : W.Nonsingular (fin.1.x.val V) (fin.1.y.val V),
          Point.some _ _ hfin
            = unshiftType1 (5 * pref.length) (natLsbVal bs : ℤ) • Point.some _ _ hT := by
  match hround : rounds, hthr with
  | [], hthr' =>
    obtain ⟨rfl, rfl⟩ := Threaded.nil hthr'
    refine ⟨[], [], by simp, by simp [roundBits], by simp,
      by simp [natLsbVal, CVar.val], fun _ => ?_⟩
    refine ⟨hP0ns, ?_⟩
    rw [hP0]
    norm_num [unshiftType1, natLsbVal]
  | r₀ :: rs, hthr' =>
    subst hround
    obtain ⟨hlen, hbase, ⟨hp0, hn0⟩, hstep, hf1, hf2⟩ := threaded_chain hthr'
    set R : ℕ → ScaleRound F := fun i => (r₀ :: rs).getD i r₀ with hR
    have hRi : ∀ i (hi : i ≤ rs.length), R i = (r₀ :: rs)[i]'(by simp; omega) := by
      intro i hi
      simp only [hR]
      exact List.getD_eq_getElem _ _ (by simp; omega)
    set g : ℕ → Kimchi.Gate.VarBaseMul.Witness F := fun i =>
      ScaleRound.read V (R i) with hg
    have hHolds : ∀ i, i < rs.length + 1 → Kimchi.Gate.VarBaseMul.Holds (g i) := by
      intro i hi
      simp only [hg, hRi i (by omega)]
      exact hpay _ (List.getElem_mem _)
    have hbase' : ∀ i, i ≤ rs.length → (R i).base = base := by
      intro i hi
      rw [hRi i hi]
      exact hbase i (by simp; omega)
    have hTns : W.Nonsingular ((g 0).xT) ((g 0).yT) := by
      simp only [hg, ScaleRound.read, hbase' 0 (by omega)]
      exact hT
    have hTeq : Point.some _ _ hT = Point.some _ _ hTns :=
      Kimchi.Gate.EndoMul.some_congr W hT hTns
        (by simp [hg, ScaleRound.read, hbase' 0 (by omega)])
        (by simp [hg, ScaleRound.read, hbase' 0 (by omega)])
    have hR0p : (R 0).acc0 = P0 := by rw [hRi 0 (by omega)]; exact hp0
    have hR0n : (R 0).nPrev = .const 0 := by rw [hRi 0 (by omega)]; exact hn0
    have hP0ns' : W.Nonsingular ((g 0).x0) ((g 0).y0) := by
      simp only [hg, ScaleRound.read, hR0p]
      exact hP0ns
    have hP0' : Point.some _ _ hP0ns' = (2 : ℤ) • Point.some _ _ hT := by
      rw [← hP0]
      exact Kimchi.Gate.EndoMul.some_congr W hP0ns' hP0ns
        (by simp [hg, ScaleRound.read, hR0p]) (by simp [hg, ScaleRound.read, hR0p])
    have hm : rs.length + 1 = pref.length := by simpa using hlen
    refine ⟨runBits g (rs.length + 1), runBools g (rs.length + 1),
      runBits_bool (rs.length + 1) g hHolds,
      read_runBits (r₀ :: rs) r₀,
      rfl,
      ?_, ?_⟩
    · -- the register chain from the zero seed
      have hthreadN : ∀ i, i + 1 < rs.length + 1 → (g (i + 1)).n = (g i).nPrime := by
        intro i hi
        obtain ⟨-, en⟩ := hstep i (by simp; omega)
        simp only [hg, ScaleRound.read]
        rw [hRi (i + 1) (by omega), hRi i (by omega), en]
      have hchain := chain_accN (rs.length + 1) g hHolds hthreadN
      have hlast : accN g (rs.length + 1) = fin.2.val V := by
        show (g rs.length).nPrime = _
        simp only [hg, ScaleRound.read]
        rw [hRi rs.length (le_refl _), ← hf2]
      have hzero : accN g 0 = 0 := by
        show (g 0).n = 0
        simp [hg, ScaleRound.read, hR0n, CVar.val]
      rw [← hlast, hchain, hzero, mul_zero, zero_add]
    · intro hregime
      rw [hm] at hregime
      obtain ⟨hfin', hpt, -⟩ :=
        varBaseMul_off W (rs.length + 1) g (Point.some _ _ hT)
          (unshiftType1 (5 * (rs.length + 1)) (natLsbVal (runBools g (rs.length + 1)) : ℤ))
          (Point.some_ne_zero hT) hHolds hTns hTeq
          (fun i hi =>
            ⟨by simp only [hg, ScaleRound.read]
                rw [hbase' i (by omega), hbase' 0 (by omega)],
             by simp only [hg, ScaleRound.read]
                rw [hbase' i (by omega), hbase' 0 (by omega)]⟩)
          (fun i hi => by
            obtain ⟨ep, -⟩ := hstep i (by simp; omega)
            refine ⟨?_, ?_⟩ <;>
              (simp only [hg, ScaleRound.read]
               rw [hRi (i + 1) (by omega), hRi i (by omega), ep]))
          hP0ns' hP0' h2 hodd
          (by simp only [gateLadder_eq_register, gateRegister_eq_natLsbVal, unshiftType1])
          (by rw [← hm] at hregime; exact hregime)
      have hax : accX g (rs.length + 1) = fin.1.x.val V := by
        show (g rs.length).x5 = _
        simp only [hg, ScaleRound.read]
        rw [hRi rs.length (le_refl _), ← hf1]
      have hay : accY g (rs.length + 1) = fin.1.y.val V := by
        show (g rs.length).y5 = _
        simp only [hg, ScaleRound.read]
        rw [hRi rs.length (le_refl _), ← hf1]
      have hfin : W.Nonsingular (fin.1.x.val V) (fin.1.y.val V) := by
        rw [← hax, ← hay]
        exact hfin'
      rw [← hm]
      exact ⟨hfin,
        (Kimchi.Gate.EndoMul.some_congr W hfin hfin' hax.symm hay.symm).trans hpt⟩

end VarBaseMul

/-- The gate seam's one representation bridge: a boolean MSB-first field-bit list
read off a wire slice has an LSB-first boolean view — per-index readings of the
wires, and the list the gate layer's `runBools` decides to. Stated once; the ladder
laws compose through it and no other proof converts representations. -/
private theorem exists_lsbView [Field F] [DecidableEq F] {V : Valuation F}
    {n k : ℕ} (hn : k ≤ n) (v : Vector (FVar F) n) (bl : List F)
    (hbool : ∀ b ∈ bl, b = 0 ∨ b = 1)
    (hsrc : bl = ((v.toList.take k).reverse).map (·.val V)) :
    ∃ bs : Vector Bool k,
      (∀ i (hi : i < k), (v[i]'(lt_of_lt_of_le hi hn)).val V = bit bs[i]) ∧
      bs.toList = (bl.map fun b => decide (b = 1)).reverse := by
  have hblen : bl.length = k := by
    rw [hsrc]
    simp only [List.length_map, List.length_reverse, List.length_take,
      Vector.length_toList]
    omega
  have hblget : ∀ j (hj : j < k),
      bl[j]'(by omega) = (v[k - 1 - j]'(by omega)).val V := by
    intro j hj
    rw [List.getElem_of_eq hsrc (by omega), List.getElem_map, List.getElem_reverse]
    congr 1
    rw [List.getElem_take, Vector.getElem_toList]
    congr 1
    simp only [List.length_take, Vector.length_toList]
    omega
  have hlist : bl.map (fun b => decide (b = 1))
      = (Vector.ofFn fun i : Fin k =>
          decide ((v[i.val]'(lt_of_lt_of_le i.isLt hn)).val V = 1)).toList.reverse := by
    apply List.ext_getElem
    · simp [hblen]
    · intro j h1 h2
      rw [List.getElem_map, List.getElem_reverse]
      simp only [Vector.getElem_toList, Vector.getElem_ofFn, Vector.length_toList]
      rw [hblget j (by simpa [hblen] using h1)]
  refine ⟨Vector.ofFn fun i : Fin k =>
    decide ((v[i.val]'(lt_of_lt_of_le i.isLt hn)).val V = 1), ?_, ?_⟩
  · intro i hi
    simp only [Vector.getElem_ofFn]
    have hvi : (v[i]'(lt_of_lt_of_le hi hn)).val V = bl[k - 1 - i]'(by omega) := by
      rw [hblget (k - 1 - i) (by omega)]
      congr 2
      omega
    rcases hbool (bl[k - 1 - i]'(by omega)) (List.getElem_mem _) with h0 | h1
    · rw [hvi, h0, decide_eq_false (zero_ne_one (α := F))]
      rfl
    · rw [hvi, h1, decide_eq_true (rfl : (1 : F) = 1)]
      rfl
  · rw [hlist, List.reverse_reverse]

open Kimchi.Gate.VarBaseMul (y_ne_zero_of_odd_order) in
/-- The gadget is sound: under any satisfying valuation, for a base point reading
on-curve, the consumed bit wires read as booleans — LSB first, per index — the
scalar reads as the cast of their ℕ value, and, whenever the ladder's regime fact
holds at the one integer `2·natLsbVal + 2^bits + 1` (the `unshiftType1` decode
of the bits), the result reads as exactly that multiple of the base. The cast pin is
the gadget's whole truth: the wire fixes the bits' value only mod the
characteristic — canonicity is a lock's business (`assertBitsBelow`), not the
ladder's. The curve facts arrive bundled as the dictionary `d : HasCurve F`; the
regime fact (`HasCurve.LadderRegime`) is the ladder's analog of `endoMul`'s
off-targets promise — per-scalar, because the one-wrap band's forbidden residues
depend on the decoded value. -/
@[spec] theorem varBaseMul_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    [d : HasCurve F]
    (n chunks : ℕ) (hn : 5 * chunks ≤ n)
    (base : AffinePoint (FVar F)) (scalar : Type1 (FVar F)) :
    ⦃⌜True⌝⦄
    (varBaseMul (c := Builder V (KimchiConstraint F)) n chunks base scalar)
    ⦃⇓ r _ => ⌜∀ hT : d.W.Nonsingular (base.x.val V) (base.y.val V),
          ∃ bs : Vector Bool (5 * chunks),
            (∀ i (hi : i < 5 * chunks),
              (r.lsbBits[i]'(lt_of_lt_of_le hi hn)).val V = bit bs[i]) ∧
            scalar.val.val V = ((natLsbVal bs.toList : ℕ) : F) ∧
            ∀ _ : d.LadderRegime (5 * chunks)
                (unshiftType1 (5 * chunks) (natLsbVal bs.toList : ℤ)),
              ∃ hfin : d.W.Nonsingular (r.g.x.val V) (r.g.y.val V),
                Point.some _ _ hfin
                  = (unshiftType1 (5 * chunks) (natLsbVal bs.toList : ℤ))
                      • Point.some _ _ hT⌝⦄ := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  simp only [varBaseMul, scaleRound, mapAccumM]
  have hadd := AddFast.addFast_checkFinite_spec (V := V) (d := d)
  mvcgen [hadd]
  case inv1 =>
    rename_i sbase _ _ _ _ _ p _ _
    exact ⇓ pr _ => ⌜VarBaseMul.Threaded sbase (p.p, .const 0) pr.1.prefix pr.2.snd pr.2.fst⌝
  case vc2.post.success.post.success.post.success.pre =>
    exact ⟨rfl, rfl⟩
  case vc1.step.post.success.post.success.post.success.post.success.post.success.post.success =>
    rename_i pref cur suff _ b _ hinv nAcc _ _ w0 _ _ w1 _ _ w2 _ _ w3 _ _ w4 _ _
    simp at hinv ⊢
    exact hinv.snoc cur nAcc w0 w1 w2 w3 w4
  case vc3.post.success.post.success.post.success.post.success.post.success.post.success =>
    rename_i sbase _ hs bits _ _ p _ hp finp _ hinv _ _ hpay _ _ heq
    obtain ⟨hsx, hsy⟩ := hs
    simp at hinv
    intro hT
    have hT' : d.W.Nonsingular (sbase.x.val V) (sbase.y.val V) := by
      rw [hsx, hsy]
      exact hT
    have hy : sbase.y.val V ≠ 0 :=
      y_ne_zero_of_odd_order d.W d.odd hT'
    obtain ⟨hP0ns, hsum⟩ := hp hT' hT' hy
    have hP0 : Point.some _ _ hP0ns = (2 : ℤ) • Point.some _ _ hT' := by
      rw [← hsum]
      module
    obtain ⟨bl, bsL, hbool, hsrc, hbsL, hregpin, hpoint⟩ :=
      VarBaseMul.threaded_sound d.W d.two_ne d.odd V hinv hpay hT' hP0ns hP0
    have hTeq : Point.some _ _ hT' = Point.some _ _ hT :=
      Kimchi.Gate.EndoMul.some_congr d.W hT' hT hsx hsy
    have hsrc' : bl = (((bits.toList.take (5 * chunks)).reverse).map (·.val V)) := by
      rw [hsrc, VarBaseMul.threaded_roundBits hinv, List.flatMap_map,
        List.flatMap_congr (fun i _ => by
          show _ = [((bits.toList.take (5 * chunks)).reverse).getD (5 * i) (.const 0),
            ((bits.toList.take (5 * chunks)).reverse).getD (5 * i + 1) (.const 0),
            ((bits.toList.take (5 * chunks)).reverse).getD (5 * i + 2) (.const 0),
            ((bits.toList.take (5 * chunks)).reverse).getD (5 * i + 3) (.const 0),
            ((bits.toList.take (5 * chunks)).reverse).getD (5 * i + 4) (.const 0)]
          simp [Vector.getElem_ofFn]),
        VarBaseMul.flatMap_window ((.const 0 : FVar F)) chunks _ (by
          simp only [List.length_reverse, List.length_take, Vector.length_toList]
          omega)]
    obtain ⟨bs, hread, hbs⟩ := exists_lsbView hn bits bl hbool hsrc'
    have hint : bsL = bs.toList := hbsL.trans hbs.symm
    refine ⟨bs, hread, (heq.symm.trans hregpin).trans (by rw [hint]), fun hregime => ?_⟩
    obtain ⟨hfin, hpt⟩ := hpoint (by simpa [hint] using hregime)
    refine ⟨hfin, ?_⟩
    rw [← hTeq]
    simpa [hint] using hpt

/-- `scaleFast2' g s ~ [s + 2^n]·g`: split the raw scalar, then `scaleFast2`. -/
def scaleFast2' [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (n chunks sDiv2Bits : ℕ) (base : AffinePoint (FVar F))
    (s : FVar F) : CircuitM F c (AffinePoint (FVar F)) := do
  let (sDiv2, sOdd) ← splitFieldVar s
  scaleFast2 n chunks sDiv2Bits base sDiv2 sOdd

/-- `splitFieldVar` is sound: the operand reads as the parity recombination
`2·sDiv2 + sOdd` of the returned pair, with the parity a genuine bit (its witness's
`boolean` row). -/
theorem splitFieldVar_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (s : FVar F) :
    ⦃⌜True⌝⦄
    (splitFieldVar (c := Builder V (KimchiConstraint F)) s)
    ⦃⇓ r _ => ⌜s.val V = 2 * r.1.val V + (↑r.2 : CVar F).val V ∧
        ((↑r.2 : CVar F).val V = 0 ∨ (↑r.2 : CVar F).val V = 1)⌝⦄ := by
  simp only [splitFieldVar]
  mvcgen
  rename_i r _ hbool _ _ heq
  refine ⟨?_, hbool.2⟩
  rw [heq]
  simp [CVar.val_add_, CVar.val_scale_]

/-- `scaleFast1` is sound — the PS defining equation
`scaleFast1 g a ~ scalarMul (fromShifted a) g`: the result reads as `[s]·g` for the
`Type1` decode `s = unshift t`, pinned in `F` and bounded by the width. The
bounds feed the wrap analysis: the F-pin fixes `s` only mod the characteristic (at
full width the wire genuinely cannot distinguish `t` from `t + p` — the ambiguity
the forbidden band exists to police), and the structural range is what the regime's
mod-order reasoning consumes; below the characteristic they determine `s` exactly.
The wired bits are `varBaseMul_spec`'s business; this statement is decode-only. -/
theorem scaleFast1_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F] [d : HasCurve F]
    (n chunks : ℕ) (hn : 5 * chunks ≤ n)
    (p : AffinePoint (FVar F)) (t : Type1 (FVar F)) :
    ⦃⌜True⌝⦄
    (scaleFast1 (c := Builder V (KimchiConstraint F)) n chunks p t)
    ⦃⇓ r _ => ⌜∀ hT : d.W.Nonsingular (p.x.val V) (p.y.val V),
          ∃ s : ℤ,
            2 ^ (5 * chunks) < s ∧ s < 3 * 2 ^ (5 * chunks) ∧
            (s : F) = unshiftType1 (5 * chunks) (t.val.val V) ∧
            ∀ _ : d.LadderRegime (5 * chunks) s,
              ∃ hfin : d.W.Nonsingular (r.x.val V) (r.y.val V),
                Point.some _ _ hfin = s • Point.some _ _ hT⌝⦄ := by
  simp only [scaleFast1]
  mvcgen
  rename_i r _ hr
  intro hT
  obtain ⟨bs, -, hpin, hpt⟩ := hr hT
  have hmlt : natLsbVal bs.toList < 2 ^ (5 * chunks) := by
    have h := natLsbVal_lt bs.toList
    rwa [Vector.length_toList] at h
  have hmlt' : (natLsbVal bs.toList : ℤ) < 2 ^ (5 * chunks) := by exact_mod_cast hmlt
  refine ⟨2 * (natLsbVal bs.toList : ℤ) + 2 ^ (5 * chunks) + 1, by omega, by omega, ?_,
    fun hregime => hpt hregime⟩
  simp only [unshiftType1]
  rw [hpin]
  push_cast
  ring

open Kimchi.Gate.VarBaseMul (y_ne_zero_of_odd_order) in
/-- `scaleFast2` is sound — the PS defining equation
`scaleFast2 g (sDiv2, sOdd) ~ [fromShifted (sDiv2, sOdd)]·g`, the `unshiftType2`
decode `2·sDiv2 + sOdd + 2^(5·chunks)`: the inner ladder computes the register's
`unshiftType1` multiple, the high-bit pins force `v < 2^sDiv2Bits`, and the
parity correction folds `sOdd` in by conditionally subtracting the base. The
parity's booleanity is the caller's promise (the `select_spec` shape);
`splitFieldVar` supplies it in `scaleFast2'`. -/
theorem scaleFast2_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F] [d : HasCurve F]
    (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n) (hd : sDiv2Bits ≤ 5 * chunks)
    (base : AffinePoint (FVar F)) (sDiv2 : FVar F) (sOdd : BoolVar F) :
    ⦃⌜True⌝⦄
    (scaleFast2 (c := Builder V (KimchiConstraint F)) n chunks sDiv2Bits base sDiv2 sOdd)
    ⦃⇓ r _ => ⌜∀ hT : d.W.Nonsingular (base.x.val V) (base.y.val V),
        ∀ bb : Bool, (↑sOdd : CVar F).val V = bit bb →
          ∃ v : ℤ, 0 ≤ v ∧ v < 2 ^ sDiv2Bits ∧ sDiv2.val V = ((v : ℤ) : F) ∧
            ∀ _ : d.LadderRegime (5 * chunks) (unshiftType1 (5 * chunks) v),
              ∃ hres : d.W.Nonsingular (r.x.val V) (r.y.val V),
                Point.some _ _ hres
                  = unshiftType2 (5 * chunks) v (bit bb)
                      • Point.some _ _ hT⌝⦄ := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  simp only [scaleFast2]
  have hadd := AddFast.addFast_checkFinite_spec (V := V) (d := d)
  mvcgen [hadd]
  case inv1 => exact ⇓ p _ => ⌜∀ b ∈ p.1.prefix, b.val V = 0⌝
  case vc2.step.post.success =>
    rename_i pref cur suff _ _ _ hinv _ _ hpin
    simp at hinv ⊢
    intro b hb
    rcases hb with hb | rfl
    · exact hinv b hb
    · simpa using hpin
  case vc3.post.success.pre => simp
  case vc4.post.success.post.success =>
    rename_i r _ hr _ _ hzeros q _ y _ hysel x _ hxsel hq
    simp at hzeros
    intro hT bb hbb
    obtain ⟨bs, hbits, hpin, hpfn⟩ := hr hT
    -- the pins force the high window to zero: the value fits `sDiv2Bits` bits
    have hbfalse : ∀ i (hi : i < 5 * chunks), sDiv2Bits ≤ i → bs[i] = false := by
      intro i hi hle
      have hz : (r.lsbBits[i]'(lt_of_lt_of_le hi hn)).val V = 0 := by
        apply hzeros
        rw [show r.lsbBits[i]'(lt_of_lt_of_le hi hn)
            = (r.lsbBits.toList.drop sDiv2Bits)[i - sDiv2Bits]'(by
                simp only [List.length_drop, Vector.length_toList]
                omega) from by
          rw [List.getElem_drop, Vector.getElem_toList]
          congr 1
          omega]
        exact List.getElem_mem _
      have hread := hbits i hi
      rw [hz] at hread
      cases hb : bs[i]
      · rfl
      · rw [hb] at hread
        exact absurd hread.symm (by simp [bit])
    have hvfit : natLsbVal bs.toList < 2 ^ sDiv2Bits := by
      refine natLsbVal_lt_of_drop_false fun b hb => ?_
      obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hb
      rw [← hjb, List.getElem_drop, Vector.getElem_toList]
      refine hbfalse _ (by
        simp only [List.length_drop, Vector.length_toList] at hj
        omega) (by omega)
    refine ⟨(natLsbVal bs.toList : ℤ), by positivity, by exact_mod_cast hvfit, ?_,
      fun hregime => ?_⟩
    · rw [hpin]
      push_cast
      ring
    · obtain ⟨hg, hgpt⟩ := hpfn (by simpa [unshiftType1] using hregime)
      have hnegv : (CVar.negate_ base.y).val V = -(base.y.val V) := by
        simp [CVar.negate_, CVar.val_scale_]
      have hnegT : d.W.Nonsingular (base.x.val V) ((CVar.negate_ base.y).val V) := by
        rw [hnegv]
        have hneg := (d.W.nonsingular_neg (base.x.val V) (base.y.val V)).mpr hT
        rwa [show d.W.negY (base.x.val V) (base.y.val V) = -(base.y.val V) from by
          rw [WeierstrassCurve.Affine.negY, d.short.1, d.short.2.2.1]
          ring] at hneg
      have hy : r.g.y.val V ≠ 0 := y_ne_zero_of_odd_order d.W d.odd hg
      obtain ⟨hqns, hqsum⟩ := hq hg hnegT hy
      have hnegPt : (Point.some _ _ hnegT : d.W.Point) = -Point.some _ _ hT := by
        rw [WeierstrassCurve.Affine.Point.neg_some]
        exact Kimchi.Gate.EndoMul.some_congr d.W hnegT _ rfl (by
          rw [hnegv, WeierstrassCurve.Affine.negY, d.short.1, d.short.2.2.1]
          ring)
      have hqpt : (Point.some _ _ hqns : d.W.Point)
          = (2 * (natLsbVal bs.toList : ℤ) + 2 ^ (5 * chunks)) • Point.some _ _ hT := by
        rw [← hqsum, hgpt, hnegPt]
        simp only [unshiftType1]
        module
      have hxv := hxsel bb hbb
      have hyv := hysel bb hbb
      cases bb
      · have hres : d.W.Nonsingular (x.val V) (y.val V) := by
          rw [hxv, hyv]
          simpa [selectPure] using hqns
        refine ⟨hres, ?_⟩
        rw [show unshiftType2 (5 * chunks) (natLsbVal bs.toList : ℤ) (bit false)
            = 2 * (natLsbVal bs.toList : ℤ) + 2 ^ (5 * chunks) from by
          simp [unshiftType2, bit]]
        refine (Kimchi.Gate.EndoMul.some_congr d.W hres hqns ?_ ?_).trans hqpt
        · rw [hxv]; simp [selectPure]
        · rw [hyv]; simp [selectPure]
      · have hres : d.W.Nonsingular (x.val V) (y.val V) := by
          rw [hxv, hyv]
          simpa [selectPure] using hg
        refine ⟨hres, ?_⟩
        rw [show unshiftType2 (5 * chunks) (natLsbVal bs.toList : ℤ) (bit true)
            = 2 * (natLsbVal bs.toList : ℤ) + 2 ^ (5 * chunks) + 1 from by
          simp [unshiftType2, bit]; ring]
        refine (Kimchi.Gate.EndoMul.some_congr d.W hres hg ?_ ?_).trans hgpt
        · rw [hxv]; simp [selectPure]
        · rw [hyv]; simp [selectPure]

/-- `scaleFast2'` is sound — `scaleFast2' g s ~ [s + 2^(5·chunks)]·g`, `s` read
through its parity split: the split's recombination `s = 2·v + sOdd` composes with
`scaleFast2`'s `unshiftType2` decode. -/
theorem scaleFast2'_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F] [d : HasCurve F]
    (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n) (hd : sDiv2Bits ≤ 5 * chunks)
    (base : AffinePoint (FVar F)) (sc : FVar F) :
    ⦃⌜True⌝⦄
    (scaleFast2' (c := Builder V (KimchiConstraint F)) n chunks sDiv2Bits base sc)
    ⦃⇓ r _ => ⌜∀ hT : d.W.Nonsingular (base.x.val V) (base.y.val V),
          ∃ (v : ℤ) (bb : Bool), 0 ≤ v ∧ v < 2 ^ sDiv2Bits ∧
            sc.val V = 2 * ((v : ℤ) : F) + bit bb ∧
            ∀ _ : d.LadderRegime (5 * chunks) (unshiftType1 (5 * chunks) v),
              ∃ hres : d.W.Nonsingular (r.x.val V) (r.y.val V),
                Point.some _ _ hres
                  = unshiftType2 (5 * chunks) v (bit bb)
                      • Point.some _ _ hT⌝⦄ := by
  simp only [scaleFast2']
  have hs := scaleFast2_spec (V := V) n chunks sDiv2Bits hn hd base
  mvcgen [hs, splitFieldVar_spec]
  rename_i pr _ hsplit _ _
  obtain ⟨hsum, hbool⟩ := hsplit
  intro hr hT
  rcases hbool with h0 | h1
  · obtain ⟨v, hv0, hvlt, hvv, hpt⟩ := hr hT false (by simpa [bit] using h0)
    refine ⟨v, false, hv0, hvlt, ?_, hpt⟩
    rw [hsum, hvv, h0]
    simp [bit]
  · obtain ⟨v, hv0, hvlt, hvv, hpt⟩ := hr hT true (by simpa [bit] using h1)
    refine ⟨v, true, hv0, hvlt, ?_, hpt⟩
    rw [hsum, hvv, h1]
    simp [bit]

/-! ## The honest run

The run functions and their laws. A round's run allocates the register advice and the
five bit-step quintets at the counter (`roundRun`); the gadget's run seals the base,
writes the bit table, doubles, and folds the rounds (`varBaseMulRun`). `round_run`/
`varBaseMul_run` land the prover at them; `varBaseMulRun_grants` reads the result as
`[unshift t]·g` through the gate model's honest walk `chainBuild`, whose rows the
collected rounds evaluate to (`roundsRun_inv`). The wrappers `scaleFast1`, `scaleFast2`,
`splitFieldVar` and `scaleFast2'` follow, each with its run and grants. -/

/-- A round evaluates to a witness exactly when each cell reads as its field. -/
private theorem evalScale_ok_iff [Field F] [DecidableEq F] {env : Assignments F}
    {r : ScaleRound F} {w : Kimchi.Gate.VarBaseMul.Witness F} :
    ScaleRound.eval env r = .ok w ↔
      r.base.x.eval env = .ok w.xT ∧ r.base.y.eval env = .ok w.yT ∧
      r.acc0.x.eval env = .ok w.x0 ∧ r.acc0.y.eval env = .ok w.y0 ∧
      r.acc1.x.eval env = .ok w.x1 ∧ r.acc1.y.eval env = .ok w.y1 ∧
      r.acc2.x.eval env = .ok w.x2 ∧ r.acc2.y.eval env = .ok w.y2 ∧
      r.acc3.x.eval env = .ok w.x3 ∧ r.acc3.y.eval env = .ok w.y3 ∧
      r.acc4.x.eval env = .ok w.x4 ∧ r.acc4.y.eval env = .ok w.y4 ∧
      r.acc5.x.eval env = .ok w.x5 ∧ r.acc5.y.eval env = .ok w.y5 ∧
      r.nPrev.eval env = .ok w.n ∧ r.nNext.eval env = .ok w.nPrime ∧
      r.bit0.eval env = .ok w.b0 ∧ r.bit1.eval env = .ok w.b1 ∧
      r.bit2.eval env = .ok w.b2 ∧ r.bit3.eval env = .ok w.b3 ∧
      r.bit4.eval env = .ok w.b4 ∧
      r.slope0.eval env = .ok w.s0 ∧ r.slope1.eval env = .ok w.s1 ∧
      r.slope2.eval env = .ok w.s2 ∧ r.slope3.eval env = .ok w.s3 ∧
      r.slope4.eval env = .ok w.s4 := by
  constructor
  · intro h
    unfold ScaleRound.eval at h
    obtain ⟨xT, hxT, h⟩ := bind_ok h
    obtain ⟨yT, hyT, h⟩ := bind_ok h
    obtain ⟨x0, hx0, h⟩ := bind_ok h
    obtain ⟨y0, hy0, h⟩ := bind_ok h
    obtain ⟨x1, hx1, h⟩ := bind_ok h
    obtain ⟨y1, hy1, h⟩ := bind_ok h
    obtain ⟨x2, hx2, h⟩ := bind_ok h
    obtain ⟨y2, hy2, h⟩ := bind_ok h
    obtain ⟨x3, hx3, h⟩ := bind_ok h
    obtain ⟨y3, hy3, h⟩ := bind_ok h
    obtain ⟨x4, hx4, h⟩ := bind_ok h
    obtain ⟨y4, hy4, h⟩ := bind_ok h
    obtain ⟨x5, hx5, h⟩ := bind_ok h
    obtain ⟨y5, hy5, h⟩ := bind_ok h
    obtain ⟨nv, hnv, h⟩ := bind_ok h
    obtain ⟨nP, hnP, h⟩ := bind_ok h
    obtain ⟨b0, hb0, h⟩ := bind_ok h
    obtain ⟨b1, hb1, h⟩ := bind_ok h
    obtain ⟨b2, hb2, h⟩ := bind_ok h
    obtain ⟨b3, hb3, h⟩ := bind_ok h
    obtain ⟨b4, hb4, h⟩ := bind_ok h
    obtain ⟨s0, hs0, h⟩ := bind_ok h
    obtain ⟨s1, hs1, h⟩ := bind_ok h
    obtain ⟨s2, hs2, h⟩ := bind_ok h
    obtain ⟨s3, hs3, h⟩ := bind_ok h
    obtain ⟨s4, hs4, h⟩ := bind_ok h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hxT, hyT, hx0, hy0, hx1, hy1, hx2, hy2, hx3, hy3, hx4, hy4, hx5, hy5,
      hnv, hnP, hb0, hb1, hb2, hb3, hb4, hs0, hs1, hs2, hs3, hs4⟩
  · intro ⟨hxT, hyT, hx0, hy0, hx1, hy1, hx2, hy2, hx3, hy3, hx4, hy4, hx5, hy5,
      hnv, hnP, hb0, hb1, hb2, hb3, hb4, hs0, hs1, hs2, hs3, hs4⟩
    unfold ScaleRound.eval
    rw [hxT, hyT, hx0, hy0, hx1, hy1, hx2, hy2, hx3, hy3, hx4, hy4, hx5, hy5,
      hnv, hnP, hb0, hb1, hb2, hb3, hb4, hs0, hs1, hs2, hs3, hs4]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A round's read survives table extension. -/
private theorem evalScale_le [Field F] [DecidableEq F] {env env' : Assignments F}
    (hle : env.Le env') {r : ScaleRound F} {w : Kimchi.Gate.VarBaseMul.Witness F}
    (h : ScaleRound.eval env r = .ok w) : ScaleRound.eval env' r = .ok w := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, h20, h21, h22, h23, h24, h25, h26⟩ := evalScale_ok_iff.mp h
  exact evalScale_ok_iff.mpr ⟨CVar.eval_le hle h1, CVar.eval_le hle h2,
    CVar.eval_le hle h3, CVar.eval_le hle h4, CVar.eval_le hle h5,
    CVar.eval_le hle h6, CVar.eval_le hle h7, CVar.eval_le hle h8,
    CVar.eval_le hle h9, CVar.eval_le hle h10, CVar.eval_le hle h11,
    CVar.eval_le hle h12, CVar.eval_le hle h13, CVar.eval_le hle h14,
    CVar.eval_le hle h15, CVar.eval_le hle h16, CVar.eval_le hle h17,
    CVar.eval_le hle h18, CVar.eval_le hle h19, CVar.eval_le hle h20,
    CVar.eval_le hle h21, CVar.eval_le hle h22, CVar.eval_le hle h23,
    CVar.eval_le hle h24, CVar.eval_le hle h25, CVar.eval_le hle h26⟩

/-- A quintet's cells, as the list an allocation writes. -/
private abbrev quintCells (q : F × F × F × F × F) : List F :=
  [q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2]

/-- A variable reads its slot. -/
private theorem val_var [Add F] [Mul F] (n : Variable) (V : Valuation F) :
    (CVar.var n).val V = V n := rfl

/-- The cells a bit step writes: the slope, then the output point at offsets `3`, `4`. -/
private theorem quintCells_getElem (q : F × F × F × F × F) :
    (quintCells q)[0] = q.1 ∧ (quintCells q)[3] = q.2.2.2.1 ∧ (quintCells q)[4] = q.2.2.2.2 :=
  ⟨rfl, rfl, rfl⟩

/-- A bit step's quintet, read: the slope and the output point are `stepBit`'s. -/
private theorem stepQuint_fields [Field F] (bv xb yb xi yi : F) :
    (stepQuint bv xb yb xi yi).1 = (Kimchi.Gate.VarBaseMul.stepBit bv xb yb xi yi).1 ∧
    (stepQuint bv xb yb xi yi).2.2.2.1 = (Kimchi.Gate.VarBaseMul.stepBit bv xb yb xi yi).2.1 ∧
    (stepQuint bv xb yb xi yi).2.2.2.2 = (Kimchi.Gate.VarBaseMul.stepBit bv xb yb xi yi).2.2 :=
  ⟨rfl, rfl, rfl⟩

/-- A bit step's witness at a state whose cells read `(xT, yT, xi, yi, bv)`: the quintet
at the counter, the five fresh variables returned. -/
private theorem bitStep_run [Field F] [DecidableEq F] {st : ProverState F}
    {base : AffinePoint (FVar F)} {b : FVar F} {acc : AffinePoint (FVar F)}
    (hbx : base.x.Scoped st) (hby : base.y.Scoped st) (hax : acc.x.Scoped st)
    (hay : acc.y.Scoped st) (hb : b.Scoped st) {xT yT xi yi bv : F}
    (hxT : base.x.val st.env.toValuation = xT) (hyT : base.y.val st.env.toValuation = yT)
    (hxi : acc.x.val st.env.toValuation = xi) (hyi : acc.y.val st.env.toValuation = yi)
    (hbv : b.val st.env.toValuation = bv) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (witness (val := F × F × F × F × F) (bitWit base b acc)) st.nv st.env
      = .ok ((st.extendMany (quintCells (stepQuint bv xT yT xi yi))).out
          (.var st.nv, .var (st.nv + 1), .var (st.nv + 2), .var (st.nv + 3),
            .var (st.nv + 4))) := by
  rw [prove_witness_run (w := bitWit base b acc) st
    (.bind (.readCVar hbx) fun _ => .bind (.readCVar hby) fun _ => .bind (.readCVar hax) fun _ =>
      .bind (.readCVar hay) fun _ => .bind (.readCVar hb) fun _ => trivial)
    (v := stepQuint bv xT yT xi yi) (by simp [bitWit, Except.bind, hxT, hyT, hxi, hyi, hbv])]
  simp only [valueToFields_prod_toList, valueToFields_fvar_toList, List.cons_append,
    List.nil_append, fieldsToVar_prod_alloc, fieldsToVar_fvar_alloc]
  simp only [size_fvar, Nat.add_assoc, Nat.reduceAdd]

/-- A round's run: the register advice at the counter, then the five bit-step quintets,
each at the counter it finds, the accumulator threaded through the fresh `(x, y)` cells;
the record over those variables and the advanced `(accumulator, register)` state. -/
private def roundRun [Field F] [DecidableEq F] (base : AffinePoint (FVar F))
    (st : ProverState F) (acc : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 5) :
    ProverState F × (ScaleRound F × (AffinePoint (FVar F) × FVar F)) :=
  let st₁ := st.extendMany [nAccVal (acc.2.val st.env.toValuation) (bs[0].val st.env.toValuation)
    (bs[1].val st.env.toValuation) (bs[2].val st.env.toValuation) (bs[3].val st.env.toValuation)
    (bs[4].val st.env.toValuation)]
  let st₂ := st₁.extendMany (quintCells (stepQuint (bs[0].val st₁.env.toValuation)
    (base.x.val st₁.env.toValuation) (base.y.val st₁.env.toValuation)
    (acc.1.x.val st₁.env.toValuation) (acc.1.y.val st₁.env.toValuation)))
  let a1 : AffinePoint (FVar F) := ⟨.var (st₁.nv + 3), .var (st₁.nv + 4)⟩
  let st₃ := st₂.extendMany (quintCells (stepQuint (bs[1].val st₂.env.toValuation)
    (base.x.val st₂.env.toValuation) (base.y.val st₂.env.toValuation)
    (a1.x.val st₂.env.toValuation) (a1.y.val st₂.env.toValuation)))
  let a2 : AffinePoint (FVar F) := ⟨.var (st₂.nv + 3), .var (st₂.nv + 4)⟩
  let st₄ := st₃.extendMany (quintCells (stepQuint (bs[2].val st₃.env.toValuation)
    (base.x.val st₃.env.toValuation) (base.y.val st₃.env.toValuation)
    (a2.x.val st₃.env.toValuation) (a2.y.val st₃.env.toValuation)))
  let a3 : AffinePoint (FVar F) := ⟨.var (st₃.nv + 3), .var (st₃.nv + 4)⟩
  let st₅ := st₄.extendMany (quintCells (stepQuint (bs[3].val st₄.env.toValuation)
    (base.x.val st₄.env.toValuation) (base.y.val st₄.env.toValuation)
    (a3.x.val st₄.env.toValuation) (a3.y.val st₄.env.toValuation)))
  let a4 : AffinePoint (FVar F) := ⟨.var (st₄.nv + 3), .var (st₄.nv + 4)⟩
  let st₆ := st₅.extendMany (quintCells (stepQuint (bs[4].val st₅.env.toValuation)
    (base.x.val st₅.env.toValuation) (base.y.val st₅.env.toValuation)
    (a4.x.val st₅.env.toValuation) (a4.y.val st₅.env.toValuation)))
  (st₆, (({ acc0 := acc.1, acc1 := a1, acc2 := a2, acc3 := a3, acc4 := a4,
            acc5 := ⟨.var (st₅.nv + 3), .var (st₅.nv + 4)⟩,
            bit0 := bs[0], bit1 := bs[1], bit2 := bs[2], bit3 := bs[3], bit4 := bs[4],
            slope0 := .var st₁.nv, slope1 := .var st₂.nv, slope2 := .var st₃.nv,
            slope3 := .var st₄.nv, slope4 := .var st₅.nv,
            nPrev := acc.2, nNext := .var st.nv, base } : ScaleRound F),
         (⟨.var (st₅.nv + 3), .var (st₅.nv + 4)⟩, .var st.nv)))

/-- A round's run grows the table, its state in scope. -/
private theorem roundRun_scopes [Field F] [DecidableEq F] (base : AffinePoint (FVar F))
    (st : ProverState F) (acc : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 5) :
    st.env.Le (roundRun base st acc bs).1.env ∧
      (roundRun base st acc bs).2.2.1.x.Scoped (roundRun base st acc bs).1 ∧
      (roundRun base st acc bs).2.2.1.y.Scoped (roundRun base st acc bs).1 ∧
      (roundRun base st acc bs).2.2.2.Scoped (roundRun base st acc bs).1 := by
  dsimp only [roundRun]
  refine ⟨(ProverState.le_extendMany _ _).trans ((ProverState.le_extendMany _ _).trans
      ((ProverState.le_extendMany _ _).trans ((ProverState.le_extendMany _ _).trans
      ((ProverState.le_extendMany _ _).trans (ProverState.le_extendMany _ _))))),
    ProverState.new_mem_extendMany _ (i := 3) (by simp [quintCells]),
    ProverState.new_mem_extendMany _ (i := 4) (by simp [quintCells]),
    CVar.Scoped.of_le ((ProverState.le_extendMany _ _).trans
      ((ProverState.le_extendMany _ _).trans ((ProverState.le_extendMany _ _).trans
      ((ProverState.le_extendMany _ _).trans (ProverState.le_extendMany _ _)))))
      (ProverState.mem_extendMany_head ..)⟩

/-- One round's honest run, at any state where the base, the state and the bits are in
scope. -/
private theorem round_run [Field F] [DecidableEq F] (base : AffinePoint (FVar F))
    {st : ProverState F} {acc : AffinePoint (FVar F) × FVar F} {bs : Vector (FVar F) 5}
    (hbx : base.x.Scoped st) (hby : base.y.Scoped st) (hax : acc.1.x.Scoped st)
    (hay : acc.1.y.Scoped st) (han : acc.2.Scoped st)
    (hbs : ∀ k (hk : k < 5), (bs[k]).Scoped st) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (scaleRound (c := KimchiConstraint F) base acc bs) st.nv st.env
      = .ok ((roundRun base st acc bs).1.out (roundRun base st acc bs).2) := by
  simp only [scaleRound, prove_bind]
  rw [prove_witness_run (w := nAccWit acc.2 bs) st
    (.bind (.readCVar han) fun _ => .bind (.readCVar (hbs 0 (by omega))) fun _ =>
      .bind (.readCVar (hbs 1 (by omega))) fun _ => .bind (.readCVar (hbs 2 (by omega))) fun _ =>
      .bind (.readCVar (hbs 3 (by omega))) fun _ => .bind (.readCVar (hbs 4 (by omega))) fun _ =>
      trivial)
    (v := nAccVal (acc.2.val st.env.toValuation) (bs[0].val st.env.toValuation) (bs[1].val st.env.toValuation) (bs[2].val st.env.toValuation) (bs[3].val st.env.toValuation) (bs[4].val st.env.toValuation))
    (by simp [nAccWit, Except.bind])]
  simp only [valueToFields_fvar_toList, fieldsToVar_fvar_alloc, Except.bind]
  generalize hS1 : st.extendMany [nAccVal (acc.2.val st.env.toValuation) (bs[0].val st.env.toValuation) (bs[1].val st.env.toValuation) (bs[2].val st.env.toValuation) (bs[3].val st.env.toValuation) (bs[4].val st.env.toValuation)] = S1
  have hl₁ : st.env.Le S1.env := by rw [← hS1]; exact st.le_extendMany _
  rw [bitStep_run (hbx.of_le hl₁) (hby.of_le hl₁) (hax.of_le hl₁) (hay.of_le hl₁)
    ((hbs 0 (by omega)).of_le hl₁) rfl rfl rfl rfl rfl]
  simp only [ProverState.out]
  generalize hS2 : S1.extendMany (quintCells (stepQuint (bs[0].val S1.env.toValuation) (base.x.val S1.env.toValuation)
    (base.y.val S1.env.toValuation) (acc.1.x.val S1.env.toValuation) (acc.1.y.val S1.env.toValuation))) = S2
  have hl2 : S1.env.Le S2.env := by rw [← hS2]; exact S1.le_extendMany _
  have hL2 : st.env.Le S2.env := hl₁.trans hl2
  have ha1x : (CVar.var (S1.nv + 3)).Scoped S2 := by
    rw [← hS2]; exact S1.new_mem_extendMany (i := 3) (by simp [quintCells])
  have ha1y : (CVar.var (S1.nv + 4)).Scoped S2 := by
    rw [← hS2]; exact S1.new_mem_extendMany (i := 4) (by simp [quintCells])
  rw [bitStep_run (acc := ⟨.var (S1.nv + 3), .var (S1.nv + 4)⟩) (hbx.of_le hL2) (hby.of_le hL2) ha1x ha1y
    ((hbs 1 (by omega)).of_le hL2) rfl rfl rfl rfl rfl]
  simp only []
  generalize hS3 : S2.extendMany (quintCells (stepQuint (bs[1].val S2.env.toValuation) (base.x.val S2.env.toValuation)
    (base.y.val S2.env.toValuation) ((CVar.var (S1.nv + 3)).val S2.env.toValuation) ((CVar.var (S1.nv + 4)).val S2.env.toValuation))) = S3
  have hl3 : S2.env.Le S3.env := by rw [← hS3]; exact S2.le_extendMany _
  have hL3 : st.env.Le S3.env := hL2.trans hl3
  have ha2x : (CVar.var (S2.nv + 3)).Scoped S3 := by
    rw [← hS3]; exact S2.new_mem_extendMany (i := 3) (by simp [quintCells])
  have ha2y : (CVar.var (S2.nv + 4)).Scoped S3 := by
    rw [← hS3]; exact S2.new_mem_extendMany (i := 4) (by simp [quintCells])
  rw [bitStep_run (acc := ⟨.var (S2.nv + 3), .var (S2.nv + 4)⟩) (hbx.of_le hL3) (hby.of_le hL3) ha2x ha2y
    ((hbs 2 (by omega)).of_le hL3) rfl rfl rfl rfl rfl]
  simp only []
  generalize hS4 : S3.extendMany (quintCells (stepQuint (bs[2].val S3.env.toValuation) (base.x.val S3.env.toValuation)
    (base.y.val S3.env.toValuation) ((CVar.var (S2.nv + 3)).val S3.env.toValuation) ((CVar.var (S2.nv + 4)).val S3.env.toValuation))) = S4
  have hl4 : S3.env.Le S4.env := by rw [← hS4]; exact S3.le_extendMany _
  have hL4 : st.env.Le S4.env := hL3.trans hl4
  have ha3x : (CVar.var (S3.nv + 3)).Scoped S4 := by
    rw [← hS4]; exact S3.new_mem_extendMany (i := 3) (by simp [quintCells])
  have ha3y : (CVar.var (S3.nv + 4)).Scoped S4 := by
    rw [← hS4]; exact S3.new_mem_extendMany (i := 4) (by simp [quintCells])
  rw [bitStep_run (acc := ⟨.var (S3.nv + 3), .var (S3.nv + 4)⟩) (hbx.of_le hL4) (hby.of_le hL4) ha3x ha3y
    ((hbs 3 (by omega)).of_le hL4) rfl rfl rfl rfl rfl]
  simp only []
  generalize hS5 : S4.extendMany (quintCells (stepQuint (bs[3].val S4.env.toValuation) (base.x.val S4.env.toValuation)
    (base.y.val S4.env.toValuation) ((CVar.var (S3.nv + 3)).val S4.env.toValuation) ((CVar.var (S3.nv + 4)).val S4.env.toValuation))) = S5
  have hl5 : S4.env.Le S5.env := by rw [← hS5]; exact S4.le_extendMany _
  have hL5 : st.env.Le S5.env := hL4.trans hl5
  have ha4x : (CVar.var (S4.nv + 3)).Scoped S5 := by
    rw [← hS5]; exact S4.new_mem_extendMany (i := 3) (by simp [quintCells])
  have ha4y : (CVar.var (S4.nv + 4)).Scoped S5 := by
    rw [← hS5]; exact S4.new_mem_extendMany (i := 4) (by simp [quintCells])
  rw [bitStep_run (acc := ⟨.var (S4.nv + 3), .var (S4.nv + 4)⟩) (hbx.of_le hL5) (hby.of_le hL5) ha4x ha4y
    ((hbs 4 (by omega)).of_le hL5) rfl rfl rfl rfl rfl]
  simp only []
  generalize hS6 : S5.extendMany (quintCells (stepQuint (bs[4].val S5.env.toValuation) (base.x.val S5.env.toValuation)
    (base.y.val S5.env.toValuation) ((CVar.var (S4.nv + 3)).val S5.env.toValuation) ((CVar.var (S4.nv + 4)).val S5.env.toValuation))) = S6
  subst hS6 hS5 hS4 hS3 hS2 hS1
  simp only [roundRun, prove_pure]

/-- A round's run, its six states named: the run is the record over them, each state
extends the last, and every fresh cell is in scope at its state reading the canonical row's
field — at cells reading `(xT, yT, x0, y0, nv, b0, …, b4)`. -/
private theorem roundRun_facts [Field F] [DecidableEq F] (base : AffinePoint (FVar F))
    {st : ProverState F} {acc : AffinePoint (FVar F) × FVar F} {bs : Vector (FVar F) 5}
    (hbx : base.x.Scoped st) (hby : base.y.Scoped st) (hax : acc.1.x.Scoped st)
    (hay : acc.1.y.Scoped st)
    (hbs : ∀ k (hk : k < 5), (bs[k]).Scoped st) {xT yT x0 y0 nv b0 b1 b2 b3 b4 : F}
    (hxT : base.x.val st.env.toValuation = xT) (hyT : base.y.val st.env.toValuation = yT)
    (hx0 : acc.1.x.val st.env.toValuation = x0) (hy0 : acc.1.y.val st.env.toValuation = y0)
    (hnv : acc.2.val st.env.toValuation = nv)
    (hb0 : bs[0].val st.env.toValuation = b0) (hb1 : bs[1].val st.env.toValuation = b1)
    (hb2 : bs[2].val st.env.toValuation = b2) (hb3 : bs[3].val st.env.toValuation = b3)
    (hb4 : bs[4].val st.env.toValuation = b4) :
    ∃ S1 S2 S3 S4 S5 S6 : ProverState F,
      roundRun base st acc bs = (S6, (({
          acc0 := acc.1, acc1 := ⟨.var (S1.nv + 3), .var (S1.nv + 4)⟩,
          acc2 := ⟨.var (S2.nv + 3), .var (S2.nv + 4)⟩, acc3 := ⟨.var (S3.nv + 3), .var (S3.nv + 4)⟩,
          acc4 := ⟨.var (S4.nv + 3), .var (S4.nv + 4)⟩, acc5 := ⟨.var (S5.nv + 3), .var (S5.nv + 4)⟩,
          bit0 := bs[0], bit1 := bs[1], bit2 := bs[2], bit3 := bs[3], bit4 := bs[4],
          slope0 := .var S1.nv, slope1 := .var S2.nv, slope2 := .var S3.nv, slope3 := .var S4.nv,
          slope4 := .var S5.nv, nPrev := acc.2, nNext := .var st.nv, base } : ScaleRound F), (⟨.var (S5.nv + 3), .var (S5.nv + 4)⟩, .var st.nv))) ∧
      st.env.Le S1.env ∧
      S1.env.Le S2.env ∧
      S2.env.Le S3.env ∧
      S3.env.Le S4.env ∧
      S4.env.Le S5.env ∧
      S5.env.Le S6.env ∧
      (CVar.var st.nv).Scoped S1 ∧
      (CVar.var st.nv).val S1.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).nPrime ∧
      (CVar.var S1.nv).Scoped S2 ∧
      (CVar.var S1.nv).val S2.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).s0 ∧
      (CVar.var (S1.nv + 3)).Scoped S2 ∧
      (CVar.var (S1.nv + 4)).Scoped S2 ∧
      (CVar.var (S1.nv + 3)).val S2.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).x1 ∧
      (CVar.var (S1.nv + 4)).val S2.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).y1 ∧
      (CVar.var S2.nv).Scoped S3 ∧
      (CVar.var S2.nv).val S3.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).s1 ∧
      (CVar.var (S2.nv + 3)).Scoped S3 ∧
      (CVar.var (S2.nv + 4)).Scoped S3 ∧
      (CVar.var (S2.nv + 3)).val S3.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).x2 ∧
      (CVar.var (S2.nv + 4)).val S3.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).y2 ∧
      (CVar.var S3.nv).Scoped S4 ∧
      (CVar.var S3.nv).val S4.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).s2 ∧
      (CVar.var (S3.nv + 3)).Scoped S4 ∧
      (CVar.var (S3.nv + 4)).Scoped S4 ∧
      (CVar.var (S3.nv + 3)).val S4.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).x3 ∧
      (CVar.var (S3.nv + 4)).val S4.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).y3 ∧
      (CVar.var S4.nv).Scoped S5 ∧
      (CVar.var S4.nv).val S5.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).s3 ∧
      (CVar.var (S4.nv + 3)).Scoped S5 ∧
      (CVar.var (S4.nv + 4)).Scoped S5 ∧
      (CVar.var (S4.nv + 3)).val S5.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).x4 ∧
      (CVar.var (S4.nv + 4)).val S5.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).y4 ∧
      (CVar.var S5.nv).Scoped S6 ∧
      (CVar.var S5.nv).val S6.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).s4 ∧
      (CVar.var (S5.nv + 3)).Scoped S6 ∧
      (CVar.var (S5.nv + 4)).Scoped S6 ∧
      (CVar.var (S5.nv + 3)).val S6.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).x5 ∧
      (CVar.var (S5.nv + 4)).val S6.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).y5 := by
  have hnAv0 : nAccVal (acc.2.val st.env.toValuation) (bs[0].val st.env.toValuation)
      (bs[1].val st.env.toValuation) (bs[2].val st.env.toValuation) (bs[3].val st.env.toValuation)
      (bs[4].val st.env.toValuation) = nAccVal nv b0 b1 b2 b3 b4 := by
    rw [hnv, hb0, hb1, hb2, hb3, hb4]
  obtain ⟨S1, hS1⟩ : ∃ S, st.extendMany [nAccVal (acc.2.val st.env.toValuation) (bs[0].val st.env.toValuation) (bs[1].val st.env.toValuation) (bs[2].val st.env.toValuation) (bs[3].val st.env.toValuation) (bs[4].val st.env.toValuation)] = S := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S, S1.extendMany (quintCells (stepQuint (bs[0].val S1.env.toValuation) (base.x.val S1.env.toValuation)
      (base.y.val S1.env.toValuation) (acc.1.x.val S1.env.toValuation) (acc.1.y.val S1.env.toValuation))) = S := ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ S, S2.extendMany (quintCells (stepQuint (bs[1].val S2.env.toValuation) (base.x.val S2.env.toValuation)
      (base.y.val S2.env.toValuation) ((CVar.var (S1.nv + 3)).val S2.env.toValuation) ((CVar.var (S1.nv + 4)).val S2.env.toValuation))) = S := ⟨_, rfl⟩
  obtain ⟨S4, hS4⟩ : ∃ S, S3.extendMany (quintCells (stepQuint (bs[2].val S3.env.toValuation) (base.x.val S3.env.toValuation)
      (base.y.val S3.env.toValuation) ((CVar.var (S2.nv + 3)).val S3.env.toValuation) ((CVar.var (S2.nv + 4)).val S3.env.toValuation))) = S := ⟨_, rfl⟩
  obtain ⟨S5, hS5⟩ : ∃ S, S4.extendMany (quintCells (stepQuint (bs[3].val S4.env.toValuation) (base.x.val S4.env.toValuation)
      (base.y.val S4.env.toValuation) ((CVar.var (S3.nv + 3)).val S4.env.toValuation) ((CVar.var (S3.nv + 4)).val S4.env.toValuation))) = S := ⟨_, rfl⟩
  obtain ⟨S6, hS6⟩ : ∃ S, S5.extendMany (quintCells (stepQuint (bs[4].val S5.env.toValuation) (base.x.val S5.env.toValuation)
      (base.y.val S5.env.toValuation) ((CVar.var (S4.nv + 3)).val S5.env.toValuation) ((CVar.var (S4.nv + 4)).val S5.env.toValuation))) = S := ⟨_, rfl⟩
  have hl₁ : st.env.Le S1.env := by rw [← hS1]; exact st.le_extendMany _
  have hl2 : S1.env.Le S2.env := by rw [← hS2]; exact S1.le_extendMany _
  have hl3 : S2.env.Le S3.env := by rw [← hS3]; exact S2.le_extendMany _
  have hl4 : S3.env.Le S4.env := by rw [← hS4]; exact S3.le_extendMany _
  have hl5 : S4.env.Le S5.env := by rw [← hS5]; exact S4.le_extendMany _
  have hl6 : S5.env.Le S6.env := by rw [← hS6]; exact S5.le_extendMany _
  have hnA : (CVar.var st.nv).Scoped S1 := by rw [← hS1]; exact ProverState.mem_extendMany_head ..
  have hnAv : (CVar.var st.nv).val S1.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).nPrime := by
    rw [val_var, ← hS1, ProverState.get_extendMany_head, hnAv0]
    exact (Kimchi.Gate.VarBaseMul.build_nPrime xT yT x0 y0 nv b0 b1 b2 b3 b4).symm
  have hL2 : st.env.Le S2.env := hl₁.trans hl2
  have hs0 : (CVar.var S1.nv).Scoped S2 := by
    rw [← hS2]; exact ProverState.mem_extendMany_head ..
  have hsv0 : (CVar.var S1.nv).val S2.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).s0 := by
    rw [val_var, ← hS2, ProverState.get_extendMany_head, (stepQuint_fields _ _ _ _ _).1,
      CVar.val_of_le hl₁ hbx, CVar.val_of_le hl₁ hby, CVar.val_of_le hl₁ (hbs 0 (by omega)),
      hxT, hyT, hb0, CVar.val_of_le hl₁ hax, CVar.val_of_le hl₁ hay, hx0, hy0]
    exact (Kimchi.Gate.VarBaseMul.build_step0 xT yT x0 y0 nv b0 b1 b2 b3 b4).1.symm
  have ha1x : (CVar.var (S1.nv + 3)).Scoped S2 := by
    rw [← hS2]; exact S1.new_mem_extendMany (i := 3) (by simp [quintCells])
  have ha1y : (CVar.var (S1.nv + 4)).Scoped S2 := by
    rw [← hS2]; exact S1.new_mem_extendMany (i := 4) (by simp [quintCells])
  have hv1x : (CVar.var (S1.nv + 3)).val S2.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).x1 := by
    rw [val_var, ← hS2, ProverState.get_extendMany_new _ (by simp [quintCells]),
      (quintCells_getElem _).2.1, (stepQuint_fields _ _ _ _ _).2.1,
      CVar.val_of_le hl₁ hbx, CVar.val_of_le hl₁ hby, CVar.val_of_le hl₁ (hbs 0 (by omega)),
      hxT, hyT, hb0, CVar.val_of_le hl₁ hax, CVar.val_of_le hl₁ hay, hx0, hy0]
    exact (Kimchi.Gate.VarBaseMul.build_step0 xT yT x0 y0 nv b0 b1 b2 b3 b4).2.1.symm
  have hv1y : (CVar.var (S1.nv + 4)).val S2.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).y1 := by
    rw [val_var, ← hS2, ProverState.get_extendMany_new _ (by simp [quintCells]),
      (quintCells_getElem _).2.2, (stepQuint_fields _ _ _ _ _).2.2,
      CVar.val_of_le hl₁ hbx, CVar.val_of_le hl₁ hby, CVar.val_of_le hl₁ (hbs 0 (by omega)),
      hxT, hyT, hb0, CVar.val_of_le hl₁ hax, CVar.val_of_le hl₁ hay, hx0, hy0]
    exact (Kimchi.Gate.VarBaseMul.build_step0 xT yT x0 y0 nv b0 b1 b2 b3 b4).2.2.symm
  have hL3 : st.env.Le S3.env := hL2.trans hl3
  have hs1 : (CVar.var S2.nv).Scoped S3 := by
    rw [← hS3]; exact ProverState.mem_extendMany_head ..
  have hsv1 : (CVar.var S2.nv).val S3.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).s1 := by
    rw [val_var, ← hS3, ProverState.get_extendMany_head, (stepQuint_fields _ _ _ _ _).1,
      CVar.val_of_le hL2 hbx, CVar.val_of_le hL2 hby, CVar.val_of_le hL2 (hbs 1 (by omega)),
      hxT, hyT, hb1, hv1x, hv1y]
    exact (Kimchi.Gate.VarBaseMul.build_step1 xT yT x0 y0 nv b0 b1 b2 b3 b4).1.symm
  have ha2x : (CVar.var (S2.nv + 3)).Scoped S3 := by
    rw [← hS3]; exact S2.new_mem_extendMany (i := 3) (by simp [quintCells])
  have ha2y : (CVar.var (S2.nv + 4)).Scoped S3 := by
    rw [← hS3]; exact S2.new_mem_extendMany (i := 4) (by simp [quintCells])
  have hv2x : (CVar.var (S2.nv + 3)).val S3.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).x2 := by
    rw [val_var, ← hS3, ProverState.get_extendMany_new _ (by simp [quintCells]),
      (quintCells_getElem _).2.1, (stepQuint_fields _ _ _ _ _).2.1,
      CVar.val_of_le hL2 hbx, CVar.val_of_le hL2 hby, CVar.val_of_le hL2 (hbs 1 (by omega)),
      hxT, hyT, hb1, hv1x, hv1y]
    exact (Kimchi.Gate.VarBaseMul.build_step1 xT yT x0 y0 nv b0 b1 b2 b3 b4).2.1.symm
  have hv2y : (CVar.var (S2.nv + 4)).val S3.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).y2 := by
    rw [val_var, ← hS3, ProverState.get_extendMany_new _ (by simp [quintCells]),
      (quintCells_getElem _).2.2, (stepQuint_fields _ _ _ _ _).2.2,
      CVar.val_of_le hL2 hbx, CVar.val_of_le hL2 hby, CVar.val_of_le hL2 (hbs 1 (by omega)),
      hxT, hyT, hb1, hv1x, hv1y]
    exact (Kimchi.Gate.VarBaseMul.build_step1 xT yT x0 y0 nv b0 b1 b2 b3 b4).2.2.symm
  have hL4 : st.env.Le S4.env := hL3.trans hl4
  have hs2 : (CVar.var S3.nv).Scoped S4 := by
    rw [← hS4]; exact ProverState.mem_extendMany_head ..
  have hsv2 : (CVar.var S3.nv).val S4.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).s2 := by
    rw [val_var, ← hS4, ProverState.get_extendMany_head, (stepQuint_fields _ _ _ _ _).1,
      CVar.val_of_le hL3 hbx, CVar.val_of_le hL3 hby, CVar.val_of_le hL3 (hbs 2 (by omega)),
      hxT, hyT, hb2, hv2x, hv2y]
    exact (Kimchi.Gate.VarBaseMul.build_step2 xT yT x0 y0 nv b0 b1 b2 b3 b4).1.symm
  have ha3x : (CVar.var (S3.nv + 3)).Scoped S4 := by
    rw [← hS4]; exact S3.new_mem_extendMany (i := 3) (by simp [quintCells])
  have ha3y : (CVar.var (S3.nv + 4)).Scoped S4 := by
    rw [← hS4]; exact S3.new_mem_extendMany (i := 4) (by simp [quintCells])
  have hv3x : (CVar.var (S3.nv + 3)).val S4.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).x3 := by
    rw [val_var, ← hS4, ProverState.get_extendMany_new _ (by simp [quintCells]),
      (quintCells_getElem _).2.1, (stepQuint_fields _ _ _ _ _).2.1,
      CVar.val_of_le hL3 hbx, CVar.val_of_le hL3 hby, CVar.val_of_le hL3 (hbs 2 (by omega)),
      hxT, hyT, hb2, hv2x, hv2y]
    exact (Kimchi.Gate.VarBaseMul.build_step2 xT yT x0 y0 nv b0 b1 b2 b3 b4).2.1.symm
  have hv3y : (CVar.var (S3.nv + 4)).val S4.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).y3 := by
    rw [val_var, ← hS4, ProverState.get_extendMany_new _ (by simp [quintCells]),
      (quintCells_getElem _).2.2, (stepQuint_fields _ _ _ _ _).2.2,
      CVar.val_of_le hL3 hbx, CVar.val_of_le hL3 hby, CVar.val_of_le hL3 (hbs 2 (by omega)),
      hxT, hyT, hb2, hv2x, hv2y]
    exact (Kimchi.Gate.VarBaseMul.build_step2 xT yT x0 y0 nv b0 b1 b2 b3 b4).2.2.symm
  have hL5 : st.env.Le S5.env := hL4.trans hl5
  have hs3 : (CVar.var S4.nv).Scoped S5 := by
    rw [← hS5]; exact ProverState.mem_extendMany_head ..
  have hsv3 : (CVar.var S4.nv).val S5.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).s3 := by
    rw [val_var, ← hS5, ProverState.get_extendMany_head, (stepQuint_fields _ _ _ _ _).1,
      CVar.val_of_le hL4 hbx, CVar.val_of_le hL4 hby, CVar.val_of_le hL4 (hbs 3 (by omega)),
      hxT, hyT, hb3, hv3x, hv3y]
    exact (Kimchi.Gate.VarBaseMul.build_step3 xT yT x0 y0 nv b0 b1 b2 b3 b4).1.symm
  have ha4x : (CVar.var (S4.nv + 3)).Scoped S5 := by
    rw [← hS5]; exact S4.new_mem_extendMany (i := 3) (by simp [quintCells])
  have ha4y : (CVar.var (S4.nv + 4)).Scoped S5 := by
    rw [← hS5]; exact S4.new_mem_extendMany (i := 4) (by simp [quintCells])
  have hv4x : (CVar.var (S4.nv + 3)).val S5.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).x4 := by
    rw [val_var, ← hS5, ProverState.get_extendMany_new _ (by simp [quintCells]),
      (quintCells_getElem _).2.1, (stepQuint_fields _ _ _ _ _).2.1,
      CVar.val_of_le hL4 hbx, CVar.val_of_le hL4 hby, CVar.val_of_le hL4 (hbs 3 (by omega)),
      hxT, hyT, hb3, hv3x, hv3y]
    exact (Kimchi.Gate.VarBaseMul.build_step3 xT yT x0 y0 nv b0 b1 b2 b3 b4).2.1.symm
  have hv4y : (CVar.var (S4.nv + 4)).val S5.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).y4 := by
    rw [val_var, ← hS5, ProverState.get_extendMany_new _ (by simp [quintCells]),
      (quintCells_getElem _).2.2, (stepQuint_fields _ _ _ _ _).2.2,
      CVar.val_of_le hL4 hbx, CVar.val_of_le hL4 hby, CVar.val_of_le hL4 (hbs 3 (by omega)),
      hxT, hyT, hb3, hv3x, hv3y]
    exact (Kimchi.Gate.VarBaseMul.build_step3 xT yT x0 y0 nv b0 b1 b2 b3 b4).2.2.symm
  have hL6 : st.env.Le S6.env := hL5.trans hl6
  have hs4 : (CVar.var S5.nv).Scoped S6 := by
    rw [← hS6]; exact ProverState.mem_extendMany_head ..
  have hsv4 : (CVar.var S5.nv).val S6.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).s4 := by
    rw [val_var, ← hS6, ProverState.get_extendMany_head, (stepQuint_fields _ _ _ _ _).1,
      CVar.val_of_le hL5 hbx, CVar.val_of_le hL5 hby, CVar.val_of_le hL5 (hbs 4 (by omega)),
      hxT, hyT, hb4, hv4x, hv4y]
    exact (Kimchi.Gate.VarBaseMul.build_step4 xT yT x0 y0 nv b0 b1 b2 b3 b4).1.symm
  have ha5x : (CVar.var (S5.nv + 3)).Scoped S6 := by
    rw [← hS6]; exact S5.new_mem_extendMany (i := 3) (by simp [quintCells])
  have ha5y : (CVar.var (S5.nv + 4)).Scoped S6 := by
    rw [← hS6]; exact S5.new_mem_extendMany (i := 4) (by simp [quintCells])
  have hv5x : (CVar.var (S5.nv + 3)).val S6.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).x5 := by
    rw [val_var, ← hS6, ProverState.get_extendMany_new _ (by simp [quintCells]),
      (quintCells_getElem _).2.1, (stepQuint_fields _ _ _ _ _).2.1,
      CVar.val_of_le hL5 hbx, CVar.val_of_le hL5 hby, CVar.val_of_le hL5 (hbs 4 (by omega)),
      hxT, hyT, hb4, hv4x, hv4y]
    exact (Kimchi.Gate.VarBaseMul.build_step4 xT yT x0 y0 nv b0 b1 b2 b3 b4).2.1.symm
  have hv5y : (CVar.var (S5.nv + 4)).val S6.env.toValuation = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).y5 := by
    rw [val_var, ← hS6, ProverState.get_extendMany_new _ (by simp [quintCells]),
      (quintCells_getElem _).2.2, (stepQuint_fields _ _ _ _ _).2.2,
      CVar.val_of_le hL5 hbx, CVar.val_of_le hL5 hby, CVar.val_of_le hL5 (hbs 4 (by omega)),
      hxT, hyT, hb4, hv4x, hv4y]
    exact (Kimchi.Gate.VarBaseMul.build_step4 xT yT x0 y0 nv b0 b1 b2 b3 b4).2.2.symm
  refine ⟨S1, S2, S3, S4, S5, S6, ?_, hl₁, hl2, hl3, hl4, hl5, hl6, hnA, hnAv, hs0, hsv0, ha1x, ha1y, hv1x, hv1y, hs1, hsv1, ha2x, ha2y, hv2x, hv2y, hs2, hsv2, ha3x, ha3y, hv3x, hv3y, hs3, hsv3, ha4x, ha4y, hv4x, hv4y, hs4, hsv4, ha5x, ha5y, hv5x, hv5y⟩
  rw [← hS6, ← hS5, ← hS4, ← hS3, ← hS2, ← hS1]
  dsimp only [roundRun]

/-- What a round's run reads, at cells reading `(xT, yT, x0, y0, nv, b0, …, b4)`: the
table grew, the advanced state is in scope and reads the canonical row's
`(x5, y5, nPrime)`, and the collected record evaluates to the canonical row
`build xT yT x0 y0 nv b0 b1 b2 b3 b4`. -/
private theorem roundRun_reads [Field F] [DecidableEq F] (base : AffinePoint (FVar F))
    {st : ProverState F} {acc : AffinePoint (FVar F) × FVar F} {bs : Vector (FVar F) 5}
    (hbx : base.x.Scoped st) (hby : base.y.Scoped st) (hax : acc.1.x.Scoped st)
    (hay : acc.1.y.Scoped st) (han : acc.2.Scoped st)
    (hbs : ∀ k (hk : k < 5), (bs[k]).Scoped st) {xT yT x0 y0 nv b0 b1 b2 b3 b4 : F}
    (hxT : base.x.val st.env.toValuation = xT) (hyT : base.y.val st.env.toValuation = yT)
    (hx0 : acc.1.x.val st.env.toValuation = x0) (hy0 : acc.1.y.val st.env.toValuation = y0)
    (hnv : acc.2.val st.env.toValuation = nv)
    (hb0 : bs[0].val st.env.toValuation = b0) (hb1 : bs[1].val st.env.toValuation = b1)
    (hb2 : bs[2].val st.env.toValuation = b2) (hb3 : bs[3].val st.env.toValuation = b3)
    (hb4 : bs[4].val st.env.toValuation = b4) :
    st.env.Le (roundRun base st acc bs).1.env ∧
      ((roundRun base st acc bs).2.2.1.x.Scoped (roundRun base st acc bs).1 ∧
        (roundRun base st acc bs).2.2.1.y.Scoped (roundRun base st acc bs).1 ∧
        (roundRun base st acc bs).2.2.2.Scoped (roundRun base st acc bs).1) ∧
      ((roundRun base st acc bs).2.2.1.x.val (roundRun base st acc bs).1.env.toValuation
          = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).x5 ∧
        (roundRun base st acc bs).2.2.1.y.val (roundRun base st acc bs).1.env.toValuation
          = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).y5 ∧
        (roundRun base st acc bs).2.2.2.val (roundRun base st acc bs).1.env.toValuation
          = (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).nPrime) ∧
      ScaleRound.eval (roundRun base st acc bs).1.env (roundRun base st acc bs).2.1
        = .ok (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4) := by
  obtain ⟨S1, S2, S3, S4, S5, S6, hR, hl₁, hl2, hl3, hl4, hl5, hl6, hnA, hnAv, hs0, hsv0, ha1x, ha1y, hv1x, hv1y, hs1, hsv1, ha2x, ha2y, hv2x, hv2y, hs2, hsv2, ha3x, ha3y, hv3x, hv3y, hs3, hsv3, ha4x, ha4y, hv4x, hv4y, hs4, hsv4, ha5x, ha5y, hv5x, hv5y⟩ :=
    roundRun_facts base hbx hby hax hay hbs hxT hyT hx0 hy0 hnv hb0 hb1 hb2 hb3 hb4
  rw [hR]
  dsimp only
  have hl₂₆ := hl3.trans (hl4.trans (hl5.trans hl6))
  have hl₃₆ := hl4.trans (hl5.trans hl6)
  have hl₄₆ := hl5.trans hl6
  have hl₁₆ := hl2.trans hl₂₆
  have hL₆ := hl₁.trans hl₁₆
  refine ⟨hL₆, ⟨ha5x, ha5y, hnA.of_le hl₁₆⟩,
    ⟨hv5x, hv5y, by rw [CVar.val_of_le hl₁₆ hnA, hnAv]⟩, ?_⟩
  refine evalScale_ok_iff.mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [CVar.eval_eq_val (hbx.of_le hL₆), CVar.val_of_le hL₆ hbx, hxT, (Kimchi.Gate.VarBaseMul.build_fields xT yT x0 y0 nv b0 b1 b2 b3 b4).1]
  · rw [CVar.eval_eq_val (hby.of_le hL₆), CVar.val_of_le hL₆ hby, hyT, (Kimchi.Gate.VarBaseMul.build_fields xT yT x0 y0 nv b0 b1 b2 b3 b4).2.1]
  · rw [CVar.eval_eq_val (hax.of_le hL₆), CVar.val_of_le hL₆ hax, hx0, (Kimchi.Gate.VarBaseMul.build_fields xT yT x0 y0 nv b0 b1 b2 b3 b4).2.2.1]
  · rw [CVar.eval_eq_val (hay.of_le hL₆), CVar.val_of_le hL₆ hay, hy0, (Kimchi.Gate.VarBaseMul.build_fields xT yT x0 y0 nv b0 b1 b2 b3 b4).2.2.2.1]
  · rw [CVar.eval_eq_val (ha1x.of_le hl₂₆), CVar.val_of_le hl₂₆ ha1x, hv1x]
  · rw [CVar.eval_eq_val (ha1y.of_le hl₂₆), CVar.val_of_le hl₂₆ ha1y, hv1y]
  · rw [CVar.eval_eq_val (ha2x.of_le hl₃₆), CVar.val_of_le hl₃₆ ha2x, hv2x]
  · rw [CVar.eval_eq_val (ha2y.of_le hl₃₆), CVar.val_of_le hl₃₆ ha2y, hv2y]
  · rw [CVar.eval_eq_val (ha3x.of_le hl₄₆), CVar.val_of_le hl₄₆ ha3x, hv3x]
  · rw [CVar.eval_eq_val (ha3y.of_le hl₄₆), CVar.val_of_le hl₄₆ ha3y, hv3y]
  · rw [CVar.eval_eq_val (ha4x.of_le hl6), CVar.val_of_le hl6 ha4x, hv4x]
  · rw [CVar.eval_eq_val (ha4y.of_le hl6), CVar.val_of_le hl6 ha4y, hv4y]
  · rw [CVar.eval_eq_val ha5x, hv5x]
  · rw [CVar.eval_eq_val ha5y, hv5y]
  · rw [CVar.eval_eq_val (han.of_le hL₆), CVar.val_of_le hL₆ han, hnv, (Kimchi.Gate.VarBaseMul.build_fields xT yT x0 y0 nv b0 b1 b2 b3 b4).2.2.2.2.1]
  · rw [CVar.eval_eq_val (hnA.of_le hl₁₆), CVar.val_of_le hl₁₆ hnA, hnAv]
  · rw [CVar.eval_eq_val ((hbs 0 (by omega)).of_le hL₆), CVar.val_of_le hL₆ (hbs 0 (by omega)), hb0,
      (Kimchi.Gate.VarBaseMul.build_fields xT yT x0 y0 nv b0 b1 b2 b3 b4).2.2.2.2.2.1]
  · rw [CVar.eval_eq_val ((hbs 1 (by omega)).of_le hL₆), CVar.val_of_le hL₆ (hbs 1 (by omega)), hb1,
      (Kimchi.Gate.VarBaseMul.build_fields xT yT x0 y0 nv b0 b1 b2 b3 b4).2.2.2.2.2.2.1]
  · rw [CVar.eval_eq_val ((hbs 2 (by omega)).of_le hL₆), CVar.val_of_le hL₆ (hbs 2 (by omega)), hb2,
      (Kimchi.Gate.VarBaseMul.build_fields xT yT x0 y0 nv b0 b1 b2 b3 b4).2.2.2.2.2.2.2.1]
  · rw [CVar.eval_eq_val ((hbs 3 (by omega)).of_le hL₆), CVar.val_of_le hL₆ (hbs 3 (by omega)), hb3,
      (Kimchi.Gate.VarBaseMul.build_fields xT yT x0 y0 nv b0 b1 b2 b3 b4).2.2.2.2.2.2.2.2.1]
  · rw [CVar.eval_eq_val ((hbs 4 (by omega)).of_le hL₆), CVar.val_of_le hL₆ (hbs 4 (by omega)), hb4,
      (Kimchi.Gate.VarBaseMul.build_fields xT yT x0 y0 nv b0 b1 b2 b3 b4).2.2.2.2.2.2.2.2.2]
  · rw [CVar.eval_eq_val (hs0.of_le hl₂₆), CVar.val_of_le hl₂₆ hs0, hsv0]
  · rw [CVar.eval_eq_val (hs1.of_le hl₃₆), CVar.val_of_le hl₃₆ hs1, hsv1]
  · rw [CVar.eval_eq_val (hs2.of_le hl₄₆), CVar.val_of_le hl₄₆ hs2, hsv2]
  · rw [CVar.eval_eq_val (hs3.of_le hl6), CVar.val_of_le hl6 hs3, hsv3]
  · rw [CVar.eval_eq_val hs4, hsv4]

/-- The bit table's variables: the bulk allocation at the counter. -/
private def lsbVarsOf (st : ProverState F) (n : ℕ) : Vector (FVar F) n :=
  CircuitType.fieldsToVar (F := F) (val := Vector F n)
    (mapVec CVar.var (allocRange st.nv (CircuitType.size F (Vector F n))))

/-- The state after the bulk witness: the scalar's bit table written. -/
private def lsbState [Field F] [ToNat F] (st : ProverState F) (n : ℕ) (scalar : FVar F) :
    ProverState F :=
  st.extendMany (CircuitType.valueToFields (F := F) (var := Vector (FVar F) n)
    (lsbVals (F := F) n (ToNat.toNat (scalar.val st.env.toValuation)))).toList

/-- The bit state extends the state. -/
private theorem lsbState_le [Field F] [ToNat F] (st : ProverState F) (n : ℕ) (scalar : FVar F) :
    st.env.Le (lsbState st n scalar).env := by
  unfold lsbState
  exact st.le_extendMany _

/-- Every bit variable is in scope at the bit state. -/
private theorem lsbVarsOf_scoped [Field F] [ToNat F] (st : ProverState F) (n : ℕ)
    (scalar : FVar F) (i : ℕ) (hi : i < n) : ((lsbVarsOf st n)[i]).Scoped (lsbState st n scalar) :=
  scoped_fvar_iff.mp (scoped_vector_iff.mp (scoped_extendMany_new (var := Vector (FVar F) n) st
    (lsbVals (F := F) n (ToNat.toNat (scalar.val st.env.toValuation)))) i hi)

/-- A bit variable reads, at the bit state, as the scalar's bit. -/
private theorem lsbVarsOf_val [Field F] [ToNat F] (st : ProverState F) (n : ℕ)
    (scalar : FVar F) (i : ℕ) (hi : i < n) :
    ((lsbVarsOf st n)[i]).val (lsbState st n scalar).env.toValuation
      = if (ToNat.toNat (scalar.val st.env.toValuation)).testBit i then 1 else 0 := by
  refine (encodes_fvar_iff.mp (encodes_vector_iff.mp (encodes_extendMany_new
    (var := Vector (FVar F) n) st
    (lsbVals (F := F) n (ToNat.toNat (scalar.val st.env.toValuation)))) i hi)).trans ?_
  simp [lsbVals]

/-- The honest stream: the `L`-bit scalar `k`'s bits MSB-first, as `chainBuild` consumes
them. -/
private def bitStream [Zero F] [One F] (L k j : ℕ) : F :=
  if k.testBit (L - 1 - j) then 1 else 0

/-- A window's cell is the bit table's cell at the mirrored index. -/
private theorem window_getElem [Field F] {n chunks : ℕ} (hn : 5 * chunks ≤ n)
    (bits : Vector (FVar F) n)
    (j k : ℕ) (hj : j < chunks) (hk : k < 5) :
    (((bits.toList.take (5 * chunks)).reverse).getD (5 * j + k) (.const 0) : FVar F)
      = bits[5 * chunks - 1 - (5 * j + k)]'(by omega) := by
  have hlen5 : (bits.toList.take (5 * chunks)).length = 5 * chunks := by
    simp only [List.length_take, Vector.length_toList]
    omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by rw [hlen5]; omega), hlen5,
    List.getElem?_take_of_lt (by omega),
    List.getElem?_eq_getElem (by simp only [Vector.length_toList]; omega)]
  simp [Vector.getElem_toList]

/-- The rounds' fold, read: from a state reading the chain's row-`i` inputs, over rows
reading the chain's bits, the fold grows the table, its state reads the chain's
row-`(i + l.length)` inputs, and every collected round evaluates at the final table to
its chain row. -/
private theorem roundsRun_inv [Field F] [DecidableEq F] (xT yT xP0 yP0 n0 : F) (bsF : ℕ → F)
    (base : AffinePoint (FVar F)) :
    ∀ (l : List (Vector (FVar F) 5)) (i : ℕ) (st : ProverState F)
      (acc : AffinePoint (FVar F) × FVar F),
      base.x.Scoped st → base.y.Scoped st →
      base.x.val st.env.toValuation = xT → base.y.val st.env.toValuation = yT →
      (∀ j (hj : j < l.length) (k : ℕ) (hk : k < 5), (l[j][k]).Scoped st) →
      (∀ j (hj : j < l.length),
        ((l[j][0]).val st.env.toValuation, (l[j][1]).val st.env.toValuation,
          (l[j][2]).val st.env.toValuation, (l[j][3]).val st.env.toValuation,
          (l[j][4]).val st.env.toValuation)
        = (bsF (5 * (i + j)), bsF (5 * (i + j) + 1), bsF (5 * (i + j) + 2),
            bsF (5 * (i + j) + 3), bsF (5 * (i + j) + 4))) →
      acc.1.x.Scoped st → acc.1.y.Scoped st → acc.2.Scoped st →
      acc.1.x.val st.env.toValuation
        = (Kimchi.Gate.VarBaseMul.chainBuild xT yT xP0 yP0 n0 bsF i).x0 →
      acc.1.y.val st.env.toValuation
        = (Kimchi.Gate.VarBaseMul.chainBuild xT yT xP0 yP0 n0 bsF i).y0 →
      acc.2.val st.env.toValuation
        = (Kimchi.Gate.VarBaseMul.chainBuild xT yT xP0 yP0 n0 bsF i).n →
      st.env.Le (mapAccumRun (roundRun base) st acc l).1.env ∧
      ((mapAccumRun (roundRun base) st acc l).2.2.1.x.Scoped
          (mapAccumRun (roundRun base) st acc l).1 ∧
        (mapAccumRun (roundRun base) st acc l).2.2.1.y.Scoped
          (mapAccumRun (roundRun base) st acc l).1 ∧
        (mapAccumRun (roundRun base) st acc l).2.2.2.Scoped
          (mapAccumRun (roundRun base) st acc l).1) ∧
      ((mapAccumRun (roundRun base) st acc l).2.2.1.x.val
          (mapAccumRun (roundRun base) st acc l).1.env.toValuation
          = (Kimchi.Gate.VarBaseMul.chainBuild xT yT xP0 yP0 n0 bsF (i + l.length)).x0 ∧
        (mapAccumRun (roundRun base) st acc l).2.2.1.y.val
          (mapAccumRun (roundRun base) st acc l).1.env.toValuation
          = (Kimchi.Gate.VarBaseMul.chainBuild xT yT xP0 yP0 n0 bsF (i + l.length)).y0 ∧
        (mapAccumRun (roundRun base) st acc l).2.2.2.val
          (mapAccumRun (roundRun base) st acc l).1.env.toValuation
          = (Kimchi.Gate.VarBaseMul.chainBuild xT yT xP0 yP0 n0 bsF (i + l.length)).n) ∧
      ∀ j (hj : j < (mapAccumRun (roundRun base) st acc l).2.1.length),
        ScaleRound.eval (mapAccumRun (roundRun base) st acc l).1.env
          (mapAccumRun (roundRun base) st acc l).2.1[j]
          = .ok (Kimchi.Gate.VarBaseMul.chainBuild xT yT xP0 yP0 n0 bsF (i + j))
  | [], i, st, acc, _, _, _, _, _, _, hax, hay, han, hva, hvb, hvn => by
    refine ⟨Assignments.Le.refl _, ⟨hax, hay, han⟩, ?_, fun j hj => by simp [mapAccumRun] at hj⟩
    simp only [mapAccumRun, List.length_nil, Nat.add_zero]
    exact ⟨hva, hvb, hvn⟩
  | x :: l, i, st, acc, hbx, hby, hbxv, hbyv, hbs, hbv, hax, hay, han, hva, hvb, hvn => by
    have hb := hbv 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hb
    have hb0v := congrArg Prod.fst hb
    have hb1v := congrArg (fun p : F × F × F × F × F => p.2.1) hb
    have hb2v := congrArg (fun p : F × F × F × F × F => p.2.2.1) hb
    have hb3v := congrArg (fun p : F × F × F × F × F => p.2.2.2.1) hb
    have hb4v := congrArg (fun p : F × F × F × F × F => p.2.2.2.2) hb
    simp only [] at hb0v hb1v hb2v hb3v hb4v
    have hbs0 : ∀ k (hk : k < 5), (x[k]).Scoped st := fun k hk => by
      simpa using hbs 0 (by simp) k hk
    have hr := roundRun_reads base hbx hby hax hay han hbs0 hbxv hbyv hva hvb hvn hb0v hb1v hb2v
      hb3v hb4v
    rw [← Kimchi.Gate.VarBaseMul.chainBuild_eta xT yT xP0 yP0 n0 bsF i] at hr
    obtain ⟨hle₁, ⟨hs₁, hs₂, hs₃⟩, ⟨hv₁, hv₂, hv₃⟩, hev⟩ := hr
    have hbsl : ∀ j (hj : j < l.length) (k : ℕ) (hk : k < 5), (l[j][k]).Scoped st :=
      fun j hj k hk => by simpa using hbs (j + 1) (by simpa using hj) k hk
    have ih := roundsRun_inv xT yT xP0 yP0 n0 bsF base l (i + 1) (roundRun base st acc x).1
      (roundRun base st acc x).2.2 (hbx.of_le hle₁) (hby.of_le hle₁)
      (by rw [CVar.val_of_le hle₁ hbx, hbxv]) (by rw [CVar.val_of_le hle₁ hby, hbyv])
      (fun j hj k hk => (hbsl j hj k hk).of_le hle₁)
      (fun j hj => by
        have h := hbv (j + 1) (by simpa using hj)
        simp only [List.getElem_cons_succ] at h
        rw [show i + 1 + j = i + (j + 1) by omega, ← h,
          CVar.val_of_le hle₁ (hbsl j hj 0 (by omega)), CVar.val_of_le hle₁ (hbsl j hj 1 (by omega)),
          CVar.val_of_le hle₁ (hbsl j hj 2 (by omega)), CVar.val_of_le hle₁ (hbsl j hj 3 (by omega)),
          CVar.val_of_le hle₁ (hbsl j hj 4 (by omega))])
      hs₁ hs₂ hs₃ (by rw [Kimchi.Gate.VarBaseMul.chainBuild_succ_x0]; exact hv₁)
      (by rw [Kimchi.Gate.VarBaseMul.chainBuild_succ_y0]; exact hv₂)
      (by rw [Kimchi.Gate.VarBaseMul.chainBuild_succ_n]; exact hv₃)
    simp only [mapAccumRun, List.length_cons]
    refine ⟨hle₁.trans ih.1, ih.2.1, ?_, ?_⟩
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using ih.2.2.1
    · intro j hj
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        exact evalScale_le ih.1 hev
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [show i + (j + 1) = i + 1 + j by omega]
        exact ih.2.2.2 j (by simpa using hj)

/-- The state and result of `varBaseMul`'s honest run: the sealed base, the bit table,
the doubled init, the rounds; the result's point is the fold's accumulator and its bits
the table. -/
def varBaseMulRun [Field F] [DecidableEq F] [ToNat F] (n chunks : ℕ) (st : ProverState F)
    (base' : AffinePoint (FVar F)) (scalar : Type1 (FVar F)) :
    ProverState F × VarBaseMulResult n F :=
  let r₁ := sealPointRun st base'
  let st₂ := lsbState r₁.1 n scalar.val
  let lsbBits := lsbVarsOf r₁.1 n
  let r₃ := AddFast.addFastRun st₂ .checkFinite r₁.2 r₁.2
  let msb : List (FVar F) := (lsbBits.toList.take (5 * chunks)).reverse
  let window : ℕ → Vector (FVar F) 5 := fun i =>
    Vector.ofFn fun j => msb.getD (5 * i + j.1) (.const 0)
  let r := mapAccumRun (roundRun r₁.2) r₃.1 (r₃.2.p, .const 0) ((List.range chunks).map window)
  (r.1, ⟨r.2.2.1, lsbBits⟩)

open Kimchi.Gate.VarBaseMul (y_ne_zero_of_odd_order smul_ne_zero_of_lt) in
/-- The init segment at an on-curve base: the doubling's operand condition holds at the
sealed base, and the state and point it lands at (named) extend the table, keep the
sealed base in scope reading as the base, keep `P₀` in scope, and read it on-curve as
`[2]·T`. -/
private theorem init_facts [Field F] [DecidableEq F] [ToNat F] [d : HasCurve F] (n : ℕ)
    (st : ProverState F) {base' : AffinePoint (FVar F)} (scalar : FVar F)
    (hx : base'.x.Scoped st) (hy : base'.y.Scoped st)
    (hT : d.W.Nonsingular (base'.x.val st.env.toValuation) (base'.y.val st.env.toValuation)) :
    ∃ (st₃ : ProverState F) (P0 : AddResult F),
      AddFast.addFastRun (lsbState (sealPointRun st base').1 n scalar) .checkFinite
          (sealPointRun st base').2 (sealPointRun st base').2 = (st₃, P0) ∧
      AddFast.Operands d .checkFinite
        ((sealPointRun st base').2.x.val
          (lsbState (sealPointRun st base').1 n scalar).env.toValuation)
        ((sealPointRun st base').2.y.val
          (lsbState (sealPointRun st base').1 n scalar).env.toValuation)
        ((sealPointRun st base').2.x.val
          (lsbState (sealPointRun st base').1 n scalar).env.toValuation)
        ((sealPointRun st base').2.y.val
          (lsbState (sealPointRun st base').1 n scalar).env.toValuation) ∧
      (sealPointRun st base').2.x.Scoped (lsbState (sealPointRun st base').1 n scalar) ∧
      (sealPointRun st base').2.y.Scoped (lsbState (sealPointRun st base').1 n scalar) ∧
      (lsbState (sealPointRun st base').1 n scalar).env.Le st₃.env ∧
      st.env.Le st₃.env ∧
      (sealPointRun st base').2.x.Scoped st₃ ∧ (sealPointRun st base').2.y.Scoped st₃ ∧
      (sealPointRun st base').2.x.val st₃.env.toValuation = base'.x.val st.env.toValuation ∧
      (sealPointRun st base').2.y.val st₃.env.toValuation = base'.y.val st.env.toValuation ∧
      P0.p.x.Scoped st₃ ∧ P0.p.y.Scoped st₃ ∧
      ∃ hP0 : d.W.Nonsingular (P0.p.x.val st₃.env.toValuation) (P0.p.y.val st₃.env.toValuation),
        Point.some _ _ hP0 = (2 : ℤ) • Point.some _ _ hT := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have hg₁ := sealPointRun_grants (st := st) hx hy
  have hle₁ := hg₁.1.le
  have hle₂ := lsbState_le (sealPointRun st base').1 n scalar
  have hsx₂ := hg₁.1.fvar_scoped.of_le hle₂
  have hsy₂ := hg₁.2.fvar_scoped.of_le hle₂
  have hbx₂ : (sealPointRun st base').2.x.val
      (lsbState (sealPointRun st base').1 n scalar).env.toValuation
      = base'.x.val st.env.toValuation := by
    rw [CVar.val_of_le hle₂ hg₁.1.fvar_scoped, hg₁.1.fvar_val]
  have hby₂ : (sealPointRun st base').2.y.val
      (lsbState (sealPointRun st base').1 n scalar).env.toValuation
      = base'.y.val st.env.toValuation := by
    rw [CVar.val_of_le hle₂ hg₁.2.fvar_scoped, hg₁.2.fvar_val]
  have hT₂ : d.W.Nonsingular ((sealPointRun st base').2.x.val
      (lsbState (sealPointRun st base').1 n scalar).env.toValuation)
      ((sealPointRun st base').2.y.val
        (lsbState (sealPointRun st base').1 n scalar).env.toValuation) := by
    rw [hbx₂, hby₂]; exact hT
  have hT₂eq : Point.some _ _ hT₂ = Point.some _ _ hT :=
    Kimchi.Gate.EndoMul.some_congr d.W hT₂ hT hbx₂ hby₂
  have hyne := y_ne_zero_of_odd_order d.W d.odd hT₂
  have h2Tne : Point.some _ _ hT₂ + Point.some _ _ hT₂ ≠ 0 := by
    intro hzero
    have h2P : (2 : ℤ) • Point.some _ _ hT₂ = 0 := by rw [two_zsmul, hzero]
    have hlt : (2 : ℤ) < (d.W.order : ℤ) := by
      have h2le := d.prime.two_le
      have hne2 := d.odd
      have h3' : 3 ≤ d.W.order := by omega
      exact_mod_cast h3'
    exact smul_ne_zero_of_lt d.W (Point.some_ne_zero hT₂) (by norm_num) hlt h2P
  have hops : AddFast.Operands d .checkFinite
      ((sealPointRun st base').2.x.val
        (lsbState (sealPointRun st base').1 n scalar).env.toValuation)
      ((sealPointRun st base').2.y.val
        (lsbState (sealPointRun st base').1 n scalar).env.toValuation)
      ((sealPointRun st base').2.x.val
        (lsbState (sealPointRun st base').1 n scalar).env.toValuation)
      ((sealPointRun st base').2.y.val
        (lsbState (sealPointRun st base').1 n scalar).env.toValuation) :=
    ⟨hT₂, hT₂, hyne, fun _ => h2Tne⟩
  have hg₃ := AddFast.addFastRun_grants .checkFinite _ hsx₂ hsy₂ hsx₂ hsy₂ hops
  obtain ⟨hle₃, hs3x, hs3y, -, hsum₃⟩ := hg₃
  obtain ⟨hP0, -, hP0eq⟩ := (hsum₃ hT₂ hT₂).resolve_left (by
    rintro ⟨-, hzero⟩
    exact h2Tne hzero)
  refine ⟨_, _, Prod.mk.eta.symm, hops, hsx₂, hsy₂, hle₃, hle₁.trans (hle₂.trans hle₃),
    hsx₂.of_le hle₃, hsy₂.of_le hle₃, by rw [CVar.val_of_le hle₃ hsx₂, hbx₂],
    by rw [CVar.val_of_le hle₃ hsy₂, hby₂], hs3x, hs3y, hP0, ?_⟩
  rw [← hP0eq, hT₂eq]
  module

/-- The honest walk from the doubled init: every row holds, its ladder is the scalar's
`Type1` decode, and the final register reconstructs the scalar. -/
private theorem chain_facts [Field F] [DecidableEq F] [d : HasCurve F] (chunks : ℕ)
    {xv yv x0v y0v : F} (hT : d.W.Nonsingular xv yv) (hP0 : d.W.Nonsingular x0v y0v)
    (hP0eq : Point.some _ _ hP0 = (2 : ℤ) • Point.some _ _ hT) (nn : ℕ)
    (hrange : nn < 2 ^ (5 * chunks))
    (hreg : d.LadderRegime (5 * chunks) (unshiftType1 (5 * chunks) (nn : ℤ))) :
    (∀ i, i < chunks → Kimchi.Gate.VarBaseMul.Holds
      (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 (bitStream (5 * chunks) nn) i)) ∧
    Kimchi.Gate.VarBaseMul.gateLadder
        (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 (bitStream (5 * chunks) nn))
        (5 * chunks)
      = 2 * (nn : ℤ) + 2 ^ (5 * chunks) + 1 ∧
    (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 (bitStream (5 * chunks) nn) chunks).n
      = (nn : F) := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have hbsb : ∀ j, j < 5 * chunks →
      bitStream (F := F) (5 * chunks) nn j = 0 ∨ bitStream (F := F) (5 * chunks) nn j = 1 := by
    intro j _
    unfold bitStream
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hrun : Kimchi.Gate.VarBaseMul.runBits
      (fun i => Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 (bitStream (5 * chunks) nn) i)
      chunks
      = (List.range (5 * chunks)).map (bitStream (5 * chunks) nn) := by
    unfold Kimchi.Gate.VarBaseMul.runBits
    rw [List.flatMap_congr (fun i _ => by
      obtain ⟨-, -, hb0, hb1, hb2, hb3, hb4⟩ :=
        Kimchi.Gate.VarBaseMul.chainBuild_fields xv yv x0v y0v 0 (bitStream (5 * chunks) nn) i
      rw [hb0, hb1, hb2, hb3, hb4]),
      Kimchi.Gate.VarBaseMul.flatMap_range_window]
  have hnat : natLsbVal (Kimchi.Gate.VarBaseMul.runBools
      (fun i => Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 (bitStream (5 * chunks) nn) i)
      chunks) = nn := by
    rw [Kimchi.Gate.VarBaseMul.runBools, hrun]
    exact Kimchi.Gate.VarBaseMul.natLsbVal_testBit_msbStream nn (5 * chunks) hrange
  have hladder : Kimchi.Gate.VarBaseMul.gateLadder
        (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 (bitStream (5 * chunks) nn))
        (5 * chunks)
      = 2 * (nn : ℤ) + 2 ^ (5 * chunks) + 1 := by
    rw [Kimchi.Gate.VarBaseMul.gateLadder_eq_register,
      Kimchi.Gate.VarBaseMul.gateRegister_eq_natLsbVal, hnat]
  simp only [HasCurve.LadderRegime, unshiftType1] at hreg
  have hregime' : 3 * 2 ^ (5 * chunks) ≤ d.W.order ∨
      (2 ^ (5 * chunks - 1) < d.W.order ∧ d.W.order < 2 ^ (5 * chunks) ∧
        d.W.order % 4 = 1 ∧
        Kimchi.Gate.VarBaseMul.gateLadder
            (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 (bitStream (5 * chunks) nn))
            (5 * chunks)
          ∉ Kimchi.Gate.VarBaseMul.forbiddenValues d.W.order) := by
    rcases hreg with h | ⟨h1, h2', h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2', h3, by rw [hladder]; exact h4⟩
  have hH := Kimchi.Gate.VarBaseMul.chain_complete d.W d.two_ne d.odd chunks hT
    (bitStream (5 * chunks) nn) hbsb 0 hP0 hP0eq hregime'
  refine ⟨hH, hladder, ?_⟩
  have hchain := Kimchi.Gate.VarBaseMul.chain_accN chunks
    (fun i => Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 (bitStream (5 * chunks) nn) i)
    hH (fun i _ => rfl)
  rw [Kimchi.Gate.VarBaseMul.accN_chainBuild, Kimchi.Gate.VarBaseMul.accN_chainBuild, hnat,
    show (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 (bitStream (5 * chunks) nn) 0).n = 0
      from rfl, mul_zero, zero_add] at hchain
  exact hchain

/-- The rounds' run at the honest init: the sealed base and the init point (named) read
on-curve as the base and `[2]·T`, the walk from the init holds row by row with the
scalar's bits, and the rounds' fold lands at a state (named) reading the chain's finals,
every collected round evaluating to its chain row there; the bit table reads as the
scalar's bits throughout. -/
private theorem walk_facts [Field F] [DecidableEq F] [ToNat F] [d : HasCurve F]
    (n chunks : ℕ) (hn : 5 * chunks ≤ n) (st : ProverState F) {base' : AffinePoint (FVar F)}
    {scalar : Type1 (FVar F)} (hs : scalar.val.Scoped st) (hx : base'.x.Scoped st)
    (hy : base'.y.Scoped st)
    (hrange : ToNat.toNat (scalar.val.val st.env.toValuation) < 2 ^ (5 * chunks))
    (hreg : d.LadderRegime (5 * chunks)
      (unshiftType1 (5 * chunks) (ToNat.toNat (scalar.val.val st.env.toValuation) : ℤ)))
    (hT : d.W.Nonsingular (base'.x.val st.env.toValuation) (base'.y.val st.env.toValuation)) :
    ∃ (st₃ : ProverState F) (P0 : AddResult F) (stR : ProverState F)
      (w : List (ScaleRound F) × (AffinePoint (FVar F) × FVar F)) (nn : ℕ) (xP0 yP0 : F)
      (hP0 : d.W.Nonsingular xP0 yP0),
      AddFast.addFastRun (lsbState (sealPointRun st base').1 n scalar.val) .checkFinite
          (sealPointRun st base').2 (sealPointRun st base').2 = (st₃, P0) ∧
      mapAccumRun (roundRun (sealPointRun st base').2) st₃ (P0.p, .const 0)
          ((List.range chunks).map fun i => Vector.ofFn fun j =>
            (((lsbVarsOf (sealPointRun st base').1 n).toList.take (5 * chunks)).reverse).getD
              (5 * i + j.1) (.const 0))
        = (stR, w) ∧
      nn = ToNat.toNat (scalar.val.val st.env.toValuation) ∧
      P0.p.x.val st₃.env.toValuation = xP0 ∧ P0.p.y.val st₃.env.toValuation = yP0 ∧
      st.env.Le st₃.env ∧ st₃.env.Le stR.env ∧
      (∀ i, i < chunks → Kimchi.Gate.VarBaseMul.Holds
        (Kimchi.Gate.VarBaseMul.chainBuild (base'.x.val st.env.toValuation)
          (base'.y.val st.env.toValuation) xP0 yP0 0 (bitStream (5 * chunks) nn) i)) ∧
      Kimchi.Gate.VarBaseMul.gateLadder
          (Kimchi.Gate.VarBaseMul.chainBuild (base'.x.val st.env.toValuation)
            (base'.y.val st.env.toValuation) xP0 yP0 0 (bitStream (5 * chunks) nn))
          (5 * chunks)
        = 2 * (nn : ℤ) + 2 ^ (5 * chunks) + 1 ∧
      (Kimchi.Gate.VarBaseMul.chainBuild (base'.x.val st.env.toValuation)
        (base'.y.val st.env.toValuation) xP0 yP0 0 (bitStream (5 * chunks) nn) chunks).n
        = (nn : F) ∧
      (w.2.1.x.Scoped stR ∧ w.2.1.y.Scoped stR ∧ w.2.2.Scoped stR) ∧
      (w.2.1.x.val stR.env.toValuation
          = (Kimchi.Gate.VarBaseMul.chainBuild (base'.x.val st.env.toValuation)
            (base'.y.val st.env.toValuation) xP0 yP0 0 (bitStream (5 * chunks) nn) chunks).x0 ∧
        w.2.1.y.val stR.env.toValuation
          = (Kimchi.Gate.VarBaseMul.chainBuild (base'.x.val st.env.toValuation)
            (base'.y.val st.env.toValuation) xP0 yP0 0 (bitStream (5 * chunks) nn) chunks).y0 ∧
        w.2.2.val stR.env.toValuation
          = (Kimchi.Gate.VarBaseMul.chainBuild (base'.x.val st.env.toValuation)
            (base'.y.val st.env.toValuation) xP0 yP0 0 (bitStream (5 * chunks) nn) chunks).n) ∧
      w.1.length = chunks ∧
      (∀ j (hj : j < w.1.length), ScaleRound.eval stR.env w.1[j]
        = .ok (Kimchi.Gate.VarBaseMul.chainBuild (base'.x.val st.env.toValuation)
            (base'.y.val st.env.toValuation) xP0 yP0 0 (bitStream (5 * chunks) nn) j)) ∧
      (∀ i (hi : i < n), ((lsbVarsOf (sealPointRun st base').1 n)[i]).Scoped stR ∧
        ((lsbVarsOf (sealPointRun st base').1 n)[i]).val stR.env.toValuation
          = if nn.testBit i then 1 else 0) ∧
      Point.some _ _ hP0 = (2 : ℤ) • Point.some _ _ hT := by
  obtain ⟨st₃, P0, heq₃, -, -, -, hle₂₃, hle₀, hsbx, hsby, hbx₃, hby₃, hs3x, hs3y, hP0, hP0eq⟩ :=
    init_facts n st scalar.val hx hy hT
  have hg₁ := sealPointRun_grants (st := st) hx hy
  have hsv₁ : scalar.val.val (sealPointRun st base').1.env.toValuation
      = scalar.val.val st.env.toValuation := CVar.val_of_le hg₁.1.le hs
  obtain ⟨hH, hladder, hreg'⟩ := chain_facts chunks hT hP0 hP0eq _ hrange hreg
  have hbit : ∀ i (hi : i < n), ((lsbVarsOf (sealPointRun st base').1 n)[i]).Scoped st₃ ∧
      ((lsbVarsOf (sealPointRun st base').1 n)[i]).val st₃.env.toValuation
        = if (ToNat.toNat (scalar.val.val st.env.toValuation)).testBit i then 1 else 0 :=
    fun i hi => ⟨(lsbVarsOf_scoped _ n scalar.val i hi).of_le hle₂₃, by
      rw [CVar.val_of_le hle₂₃ (lsbVarsOf_scoped _ n scalar.val i hi),
        lsbVarsOf_val _ n scalar.val i hi, hsv₁]⟩
  have hinv := roundsRun_inv (base'.x.val st.env.toValuation) (base'.y.val st.env.toValuation)
    (P0.p.x.val st₃.env.toValuation) (P0.p.y.val st₃.env.toValuation) 0
    (bitStream (5 * chunks) (ToNat.toNat (scalar.val.val st.env.toValuation)))
    (sealPointRun st base').2
    ((List.range chunks).map fun i => Vector.ofFn fun j =>
      (((lsbVarsOf (sealPointRun st base').1 n).toList.take (5 * chunks)).reverse).getD
        (5 * i + j.1) (.const 0))
    0 st₃ (P0.p, .const 0) hsbx hsby hbx₃ hby₃
    (fun j hj k hk => by
      have hj' : j < chunks := by simpa using hj
      simp only [List.getElem_map, List.getElem_range, Vector.getElem_ofFn]
      rw [window_getElem hn _ j k hj' hk]
      exact (hbit _ (by omega)).1)
    (fun j hj => by
      have hj' : j < chunks := by simpa using hj
      simp only [List.getElem_map, List.getElem_range, Vector.getElem_ofFn, Nat.zero_add]
      rw [window_getElem hn _ j 0 hj' (by omega), window_getElem hn _ j 1 hj' (by omega),
        window_getElem hn _ j 2 hj' (by omega), window_getElem hn _ j 3 hj' (by omega),
        window_getElem hn _ j 4 hj' (by omega), (hbit _ (by omega)).2, (hbit _ (by omega)).2,
        (hbit _ (by omega)).2, (hbit _ (by omega)).2, (hbit _ (by omega)).2]
      rfl)
    hs3x hs3y (CVar.scoped_const _ _) rfl rfl
    (by simp [CVar.val, Kimchi.Gate.VarBaseMul.chainBuild, Kimchi.Gate.VarBaseMul.build])
  obtain ⟨hleR, hsc, hrd, hev⟩ := hinv
  simp only [List.length_map, List.length_range, Nat.zero_add] at hrd hev
  refine ⟨st₃, P0, _, _, _, _, _, hP0, heq₃, Prod.mk.eta.symm, rfl, rfl, rfl, hle₀, hleR, hH,
    hladder, hreg', hsc, hrd, ?_, hev, fun i hi => ⟨(hbit i hi).1.of_le hleR, ?_⟩, hP0eq⟩
  · rw [mapAccumRun_length]
    simp
  · rw [CVar.val_of_le hleR (hbit i hi).1]
    exact (hbit i hi).2

/-- The honest run of `varBaseMul`, generic over the curve dictionary: on an in-scope
on-curve base and an in-scope in-range scalar whose `Type1` decode satisfies the ladder
regime, the prover lands at `varBaseMulRun` — the sealed base, the bit witness, the
doubling (`addFast_run` at `init_facts`' operand condition), the rounds
(`prove_mapAccumM` over `round_run`), the constraint accepted on the collected rounds
(`walk_facts`), and the register pin (the chain's final register is the scalar). -/
theorem varBaseMul_run [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F] [d : HasCurve F]
    (n chunks : ℕ) (hn : 5 * chunks ≤ n) (st : ProverState F) {base' : AffinePoint (FVar F)}
    {scalar : Type1 (FVar F)} (hs : scalar.val.Scoped st) (hx : base'.x.Scoped st)
    (hy : base'.y.Scoped st)
    (hrange : ToNat.toNat (scalar.val.val st.env.toValuation) < 2 ^ (5 * chunks))
    (hreg : d.LadderRegime (5 * chunks)
      (unshiftType1 (5 * chunks) (ToNat.toNat (scalar.val.val st.env.toValuation) : ℤ)))
    (hT : d.W.Nonsingular (base'.x.val st.env.toValuation) (base'.y.val st.env.toValuation)) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (varBaseMul (c := KimchiConstraint F) n chunks base' scalar) st.nv st.env
      = .ok ((varBaseMulRun n chunks st base' scalar).1.out
          (varBaseMulRun n chunks st base' scalar).2) := by
  obtain ⟨st₃, P0, stR, w, nn, xP0, yP0, -, heq₃, heqR, hnn, -, -, hle₀, hleR, hH, -, hreg',
    ⟨hsx, hsy, hsn⟩, ⟨-, -, hrn⟩, hlen, hev, -, -⟩ :=
    walk_facts n chunks hn st hs hx hy hrange hreg hT
  subst hnn
  obtain ⟨st₃', P0', heq₃', hops, hsx₂, hsy₂, hle₂₃, -, hs3x', hs3y', -, -, hs3x, hs3y, -⟩ :=
    init_facts n st scalar.val hx hy hT
  rw [heq₃] at heq₃'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq₃'
  have hg₁ := sealPointRun_grants (st := st) hx hy
  simp only [varBaseMul, varBaseMulRun, prove_bind]
  rw [sealPoint_run st hx hy]
  simp only [Except.bind]
  rw [prove_witness_run (w := lsbBitsWit n scalar.val) _
    (.bind (.readCVar (hs.of_le hg₁.1.le)) fun _ => trivial)
    (v := lsbVals (F := F) n
      (ToNat.toNat (scalar.val.val (sealPointRun st base').1.env.toValuation)))
    (by simp [lsbBitsWit, Except.bind])]
  rw [show CircuitType.fieldsToVar (F := F) (val := Vector F n)
      (mapVec CVar.var (allocRange (sealPointRun st base').1.nv
        (CircuitType.size F (Vector F n))))
      = lsbVarsOf (sealPointRun st base').1 n from rfl,
    show (sealPointRun st base').1.extendMany (CircuitType.valueToFields (F := F)
      (var := Vector (FVar F) n) (lsbVals (F := F) n
        (ToNat.toNat (scalar.val.val (sealPointRun st base').1.env.toValuation)))).toList
      = lsbState (sealPointRun st base').1 n scalar.val from rfl]
  simp only []
  rw [AddFast.addFast_run .checkFinite _ hsx₂ hsy₂ hsx₂ hsy₂ hops]
  simp only [heq₃]
  rw [prove_mapAccumM (fun st' (acc : AffinePoint (FVar F) × FVar F) =>
      (lsbState (sealPointRun st base').1 n scalar.val).env.Le st'.env ∧
      acc.1.x.Scoped st' ∧ acc.1.y.Scoped st' ∧ acc.2.Scoped st')
    _ (roundRun (sealPointRun st base').2) _
    (fun st' acc bs hbs ⟨hle, hax, hay, han⟩ =>
      round_run _ (hsx₂.of_le hle) (hsy₂.of_le hle) hax hay han (fun k hk => by
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hbs
        have hj' : j < chunks := by simpa using hj
        simp only [List.getElem_map, List.getElem_range, Vector.getElem_ofFn]
        rw [window_getElem hn _ j k hj' hk]
        exact (lsbVarsOf_scoped _ n scalar.val _ (by omega)).of_le hle))
    (fun st' acc bs _ ⟨hle, _, _, _⟩ =>
      ⟨hle.trans (roundRun_scopes _ st' acc bs).1, (roundRun_scopes _ st' acc bs).2.1,
        (roundRun_scopes _ st' acc bs).2.2.1, (roundRun_scopes _ st' acc bs).2.2.2⟩)
    (P0.p, .const 0) st₃ ⟨hle₂₃, hs3x, hs3y, CVar.scoped_const _ _⟩]
  simp only [heqR]
  rw [prove_addConstraint _ (by
    show KimchiConstraint.check (.varBaseMul w.1) _ = true
    simp only [KimchiConstraint.check, List.all_eq_true]
    intro r hr
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
    rw [hev j hj]
    exact (Kimchi.Gate.VarBaseMul.ok_iff _).mpr (hH j (by omega)))]
  simp only []
  rw [assertEqual_run _ hsn (hs.of_le (hle₀.trans hleR)) (by
    rw [hrn, hreg', CVar.val_of_le (hle₀.trans hleR) hs]
    exact LawfulToNat.cast_toNat _)]
  rfl

/-- What `varBaseMulRun` grants, generic over the curve dictionary: the table grew, the
result's point and bits are in scope, the bits read as the scalar's LSB-first, and the
point reads as `[unshift t]·g` at the scalar's canonical value (`varBaseMul_off` at the
honest walk). The regime precondition is per-scalar, exactly the fact the soundness law
conditions on. -/
theorem varBaseMulRun_grants [Field F] [DecidableEq F] [ToNat F] [d : HasCurve F]
    (n chunks : ℕ) (hn : 5 * chunks ≤ n) (st : ProverState F) {base' : AffinePoint (FVar F)}
    {scalar : Type1 (FVar F)} (hs : scalar.val.Scoped st) (hx : base'.x.Scoped st)
    (hy : base'.y.Scoped st)
    (hrange : ToNat.toNat (scalar.val.val st.env.toValuation) < 2 ^ (5 * chunks))
    (hreg : d.LadderRegime (5 * chunks)
      (unshiftType1 (5 * chunks) (ToNat.toNat (scalar.val.val st.env.toValuation) : ℤ)))
    (hT : d.W.Nonsingular (base'.x.val st.env.toValuation) (base'.y.val st.env.toValuation)) :
    st.env.Le (varBaseMulRun n chunks st base' scalar).1.env ∧
      (varBaseMulRun n chunks st base' scalar).2.g.x.Scoped
        (varBaseMulRun n chunks st base' scalar).1 ∧
      (varBaseMulRun n chunks st base' scalar).2.g.y.Scoped
        (varBaseMulRun n chunks st base' scalar).1 ∧
      (∀ i (hi : i < n),
        ((varBaseMulRun n chunks st base' scalar).2.lsbBits[i]).Scoped
          (varBaseMulRun n chunks st base' scalar).1 ∧
        ((varBaseMulRun n chunks st base' scalar).2.lsbBits[i]).val
            (varBaseMulRun n chunks st base' scalar).1.env.toValuation
          = if (ToNat.toNat (scalar.val.val st.env.toValuation)).testBit i then 1 else 0) ∧
      ∃ hfin : d.W.Nonsingular
          ((varBaseMulRun n chunks st base' scalar).2.g.x.val
            (varBaseMulRun n chunks st base' scalar).1.env.toValuation)
          ((varBaseMulRun n chunks st base' scalar).2.g.y.val
            (varBaseMulRun n chunks st base' scalar).1.env.toValuation),
        Point.some _ _ hfin
          = unshiftType1 (5 * chunks) (ToNat.toNat (scalar.val.val st.env.toValuation) : ℤ)
              • Point.some _ _ hT := by
  obtain ⟨st₃, P0, stR, w, nn, xP0, yP0, hP0, heq₃, heqR, hnn, -, -, hle₀, hleR, hH, hladder, -,
    ⟨hsx, hsy, -⟩, ⟨hrx, hry, -⟩, -, -, hbits, hP0eq⟩ :=
    walk_facts n chunks hn st hs hx hy hrange hreg hT
  subst hnn
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have hregpre := hreg
  simp only [HasCurve.LadderRegime, unshiftType1] at hregpre
  obtain ⟨hfin', hpt, -⟩ := Kimchi.Gate.VarBaseMul.varBaseMul_off d.W chunks
    (fun i => Kimchi.Gate.VarBaseMul.chainBuild (base'.x.val st.env.toValuation)
      (base'.y.val st.env.toValuation) xP0 yP0 0
      (bitStream (5 * chunks) (ToNat.toNat (scalar.val.val st.env.toValuation))) i)
    (Point.some _ _ hT)
    (2 * (ToNat.toNat (scalar.val.val st.env.toValuation) : ℤ) + 2 ^ (5 * chunks) + 1)
    (Point.some_ne_zero hT) hH hT rfl
    (fun i _ => by
      obtain ⟨hx1, hy1, -, -, -, -, -⟩ :=
        Kimchi.Gate.VarBaseMul.chainBuild_fields (base'.x.val st.env.toValuation)
          (base'.y.val st.env.toValuation) xP0 yP0 0
          (bitStream (5 * chunks) (ToNat.toNat (scalar.val.val st.env.toValuation))) i
      obtain ⟨hx0', hy0', -, -, -, -, -⟩ :=
        Kimchi.Gate.VarBaseMul.chainBuild_fields (base'.x.val st.env.toValuation)
          (base'.y.val st.env.toValuation) xP0 yP0 0
          (bitStream (5 * chunks) (ToNat.toNat (scalar.val.val st.env.toValuation))) 0
      rw [hx1, hy1, hx0', hy0']
      exact ⟨rfl, rfl⟩)
    (fun i _ => ⟨rfl, rfl⟩) hP0 hP0eq d.two_ne d.odd hladder.symm hregpre
  have hax := Kimchi.Gate.VarBaseMul.accX_chainBuild (base'.x.val st.env.toValuation)
    (base'.y.val st.env.toValuation) xP0 yP0 0
    (bitStream (5 * chunks) (ToNat.toNat (scalar.val.val st.env.toValuation))) chunks
  have hay := Kimchi.Gate.VarBaseMul.accY_chainBuild (base'.x.val st.env.toValuation)
    (base'.y.val st.env.toValuation) xP0 yP0 0
    (bitStream (5 * chunks) (ToNat.toNat (scalar.val.val st.env.toValuation))) chunks
  have hfin : d.W.Nonsingular
      (Kimchi.Gate.VarBaseMul.chainBuild (base'.x.val st.env.toValuation)
        (base'.y.val st.env.toValuation) xP0 yP0 0
        (bitStream (5 * chunks) (ToNat.toNat (scalar.val.val st.env.toValuation))) chunks).x0
      (Kimchi.Gate.VarBaseMul.chainBuild (base'.x.val st.env.toValuation)
        (base'.y.val st.env.toValuation) xP0 yP0 0
        (bitStream (5 * chunks) (ToNat.toNat (scalar.val.val st.env.toValuation))) chunks).y0 := by
    rw [← hax, ← hay]
    exact hfin'
  dsimp only [varBaseMulRun]
  rw [heq₃]
  dsimp only
  rw [heqR]
  dsimp only
  refine ⟨hle₀.trans hleR, hsx, hsy, hbits, ?_⟩
  rw [hrx, hry]
  refine ⟨hfin, (Kimchi.Gate.EndoMul.some_congr d.W hfin hfin' hax.symm hay.symm).trans
    (hpt.trans ?_)⟩
  simp only [unshiftType1]

/-- The state and result of `scaleFast1`'s honest run: `varBaseMul`'s, the bits dropped. -/
def scaleFast1Run [Field F] [DecidableEq F] [ToNat F] (n chunks : ℕ) (st : ProverState F)
    (p : AffinePoint (FVar F)) (t : Type1 (FVar F)) : ProverState F × AffinePoint (FVar F) :=
  ((varBaseMulRun n chunks st p t).1, (varBaseMulRun n chunks st p t).2.g)

/-- The honest run of `scaleFast1`: `varBaseMul_run`, the bits dropped. -/
theorem scaleFast1_run [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F] [d : HasCurve F]
    (n chunks : ℕ) (hn : 5 * chunks ≤ n) (st : ProverState F) {p : AffinePoint (FVar F)}
    {t : Type1 (FVar F)} (hs : t.val.Scoped st) (hx : p.x.Scoped st) (hy : p.y.Scoped st)
    (hrange : ToNat.toNat (t.val.val st.env.toValuation) < 2 ^ (5 * chunks))
    (hreg : d.LadderRegime (5 * chunks)
      (unshiftType1 (5 * chunks) (ToNat.toNat (t.val.val st.env.toValuation) : ℤ)))
    (hT : d.W.Nonsingular (p.x.val st.env.toValuation) (p.y.val st.env.toValuation)) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (scaleFast1 (c := KimchiConstraint F) n chunks p t) st.nv st.env
      = .ok ((scaleFast1Run n chunks st p t).1.out (scaleFast1Run n chunks st p t).2) := by
  simp only [scaleFast1, scaleFast1Run, prove_bind]
  rw [varBaseMul_run n chunks hn st hs hx hy hrange hreg hT]
  rfl

/-- What `scaleFast1Run` grants — the honest side of the defining equation
`scaleFast1 g a ~ scalarMul (fromShifted a) g`: `varBaseMulRun_grants`' point promise. -/
theorem scaleFast1Run_grants [Field F] [DecidableEq F] [ToNat F] [d : HasCurve F]
    (n chunks : ℕ) (hn : 5 * chunks ≤ n) (st : ProverState F) {p : AffinePoint (FVar F)}
    {t : Type1 (FVar F)} (hs : t.val.Scoped st) (hx : p.x.Scoped st) (hy : p.y.Scoped st)
    (hrange : ToNat.toNat (t.val.val st.env.toValuation) < 2 ^ (5 * chunks))
    (hreg : d.LadderRegime (5 * chunks)
      (unshiftType1 (5 * chunks) (ToNat.toNat (t.val.val st.env.toValuation) : ℤ)))
    (hT : d.W.Nonsingular (p.x.val st.env.toValuation) (p.y.val st.env.toValuation)) :
    st.env.Le (scaleFast1Run n chunks st p t).1.env ∧
      (scaleFast1Run n chunks st p t).2.x.Scoped (scaleFast1Run n chunks st p t).1 ∧
      (scaleFast1Run n chunks st p t).2.y.Scoped (scaleFast1Run n chunks st p t).1 ∧
      ∃ hfin : d.W.Nonsingular
          ((scaleFast1Run n chunks st p t).2.x.val (scaleFast1Run n chunks st p t).1.env.toValuation)
          ((scaleFast1Run n chunks st p t).2.y.val (scaleFast1Run n chunks st p t).1.env.toValuation),
        Point.some _ _ hfin
          = unshiftType1 (5 * chunks) (ToNat.toNat (t.val.val st.env.toValuation) : ℤ)
              • Point.some _ _ hT := by
  obtain ⟨hle, hgx, hgy, -, hfin, hpt⟩ := varBaseMulRun_grants n chunks hn st hs hx hy hrange hreg hT
  exact ⟨hle, hgx, hgy, hfin, hpt⟩

/-- The regime keeps the honest decode off the base: `unshift t ≢ 1 (mod order)`
— subwrap by size (the window sits strictly inside `(0, order)`), one-wrap because
`1` is a forbidden residue. What makes `scaleFast2`'s parity correction — the
incomplete subtraction of the base — well-defined on the honest run. -/
private theorem regime_off_base [Field F] [DecidableEq F] [d : HasCurve F]
    {L : ℕ} {t : ℤ} (ht0 : 0 ≤ t) (htlt : t < 2 ^ L)
    (hreg : d.LadderRegime L (unshiftType1 L t)) :
    ¬ ((d.W.order : ℤ) ∣ (2 * t + 2 ^ L)) := by
  intro hdvd
  rcases hreg with hsub | ⟨-, -, -, hnf⟩
  · have hpos : (0 : ℤ) < 2 ^ L := by positivity
    have hord : (3 : ℤ) * 2 ^ L ≤ (d.W.order : ℤ) := by exact_mod_cast hsub
    have hle' := Int.le_of_dvd (by linarith) hdvd
    linarith
  · refine hnf (Kimchi.Gate.VarBaseMul.mem_forbiddenValues_of_dvd_sub_one
      d.W.order ?_)
    rw [show unshiftType1 L t - 1 = 2 * t + 2 ^ L from by
      simp [unshiftType1]]
    exact hdvd

/-- The state and result of `scaleFast2`'s honest run: the ladder on the half, the pins
(nothing allocated), the correction `g − base`, then the coordinatewise selection, `y`
before `x`. -/
def scaleFast2Run [Field F] [DecidableEq F] [ToNat F] (n chunks : ℕ) (st : ProverState F)
    (base : AffinePoint (FVar F)) (sDiv2 : FVar F) (sOdd : BoolVar F) :
    ProverState F × AffinePoint (FVar F) :=
  let r := varBaseMulRun n chunks st base ⟨sDiv2⟩
  let q := AddFast.addFastRun r.1 .checkFinite r.2.g ⟨base.x, CVar.negate_ base.y⟩
  let ry := selectRun q.1 sOdd r.2.g.y q.2.p.y
  let rx := selectRun ry.1 sOdd r.2.g.x q.2.p.x
  (rx.1, ⟨rx.2, ry.2⟩)

open Kimchi.Gate.VarBaseMul (y_ne_zero_of_odd_order zsmul_eq_zero_iff_order_dvd) in
/-- The correction's facts at the honest ladder: the negated base is a genuine point in
scope reading `−T`, the ladder's point is finite, and the correction's sum is nonzero —
the regime keeps the ladder off the base (`s ≢ 1`, subwrap by size, one-wrap because `1`
is a forbidden residue), the completeness-side counterpart of the sound law's `tne`
self-enforcement. -/
private theorem correction_facts [Field F] [DecidableEq F] [ToNat F] [d : HasCurve F]
    (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n) (hd : sDiv2Bits ≤ 5 * chunks)
    (st : ProverState F) {base : AffinePoint (FVar F)} {sDiv2 : FVar F}
    (hs : sDiv2.Scoped st) (hx : base.x.Scoped st) (hy : base.y.Scoped st)
    (hrange : ToNat.toNat (sDiv2.val st.env.toValuation) < 2 ^ sDiv2Bits)
    (hreg : d.LadderRegime (5 * chunks)
      (unshiftType1 (5 * chunks) (ToNat.toNat (sDiv2.val st.env.toValuation) : ℤ)))
    (hT : d.W.Nonsingular (base.x.val st.env.toValuation) (base.y.val st.env.toValuation)) :
    (CVar.negate_ base.y).Scoped (varBaseMulRun n chunks st base ⟨sDiv2⟩).1 ∧
    AddFast.Operands d .checkFinite
      ((varBaseMulRun n chunks st base ⟨sDiv2⟩).2.g.x.val
        (varBaseMulRun n chunks st base ⟨sDiv2⟩).1.env.toValuation)
      ((varBaseMulRun n chunks st base ⟨sDiv2⟩).2.g.y.val
        (varBaseMulRun n chunks st base ⟨sDiv2⟩).1.env.toValuation)
      (base.x.val (varBaseMulRun n chunks st base ⟨sDiv2⟩).1.env.toValuation)
      ((CVar.negate_ base.y).val (varBaseMulRun n chunks st base ⟨sDiv2⟩).1.env.toValuation) ∧
    ∀ (hfin : d.W.Nonsingular
        ((varBaseMulRun n chunks st base ⟨sDiv2⟩).2.g.x.val
          (varBaseMulRun n chunks st base ⟨sDiv2⟩).1.env.toValuation)
        ((varBaseMulRun n chunks st base ⟨sDiv2⟩).2.g.y.val
          (varBaseMulRun n chunks st base ⟨sDiv2⟩).1.env.toValuation))
      (hnegT : d.W.Nonsingular
        (base.x.val (varBaseMulRun n chunks st base ⟨sDiv2⟩).1.env.toValuation)
        ((CVar.negate_ base.y).val (varBaseMulRun n chunks st base ⟨sDiv2⟩).1.env.toValuation)),
      Point.some _ _ hfin + Point.some _ _ hnegT
        = (2 * (ToNat.toNat (sDiv2.val st.env.toValuation) : ℤ) + 2 ^ (5 * chunks))
            • Point.some _ _ hT := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have hrange' : ToNat.toNat (sDiv2.val st.env.toValuation) < 2 ^ (5 * chunks) :=
    lt_of_lt_of_le hrange (Nat.pow_le_pow_right (by norm_num) hd)
  obtain ⟨hle, hgx, hgy, -, hfin, hpt⟩ :=
    varBaseMulRun_grants n chunks hn st (scalar := ⟨sDiv2⟩) hs hx hy hrange' hreg hT
  have hvlt : (ToNat.toNat (sDiv2.val st.env.toValuation) : ℤ) < 2 ^ (5 * chunks) := by
    exact_mod_cast hrange'
  have hs1 := regime_off_base (Int.natCast_nonneg _) hvlt hreg
  have hbx' := CVar.val_of_le hle hx
  have hny : (CVar.negate_ base.y).val (varBaseMulRun n chunks st base ⟨sDiv2⟩).1.env.toValuation
      = -(base.y.val st.env.toValuation) := by
    show (CVar.scale_ (-1) base.y).val _ = _
    rw [CVar.val_scale_, CVar.val_of_le hle hy, neg_one_mul]
  have hgyne := y_ne_zero_of_odd_order d.W d.odd hfin
  obtain ⟨hnegT, hnegPt⟩ := AddFast.neg_point_reading d.W
    ⟨d.short.1, d.short.2.1, d.short.2.2.1⟩ hT
  have hnegT' : d.W.Nonsingular
      (base.x.val (varBaseMulRun n chunks st base ⟨sDiv2⟩).1.env.toValuation)
      ((CVar.negate_ base.y).val (varBaseMulRun n chunks st base ⟨sDiv2⟩).1.env.toValuation) := by
    rw [hbx', hny]; exact hnegT
  have hsum : ∀ (hfin' : d.W.Nonsingular
        ((varBaseMulRun n chunks st base ⟨sDiv2⟩).2.g.x.val
          (varBaseMulRun n chunks st base ⟨sDiv2⟩).1.env.toValuation)
        ((varBaseMulRun n chunks st base ⟨sDiv2⟩).2.g.y.val
          (varBaseMulRun n chunks st base ⟨sDiv2⟩).1.env.toValuation))
      (hnegT'' : d.W.Nonsingular
        (base.x.val (varBaseMulRun n chunks st base ⟨sDiv2⟩).1.env.toValuation)
        ((CVar.negate_ base.y).val (varBaseMulRun n chunks st base ⟨sDiv2⟩).1.env.toValuation)),
      Point.some _ _ hfin' + Point.some _ _ hnegT''
        = (2 * (ToNat.toNat (sDiv2.val st.env.toValuation) : ℤ) + 2 ^ (5 * chunks))
            • Point.some _ _ hT := by
    intro hfin' hnegT''
    rw [Kimchi.Gate.EndoMul.some_congr d.W hfin' hfin rfl rfl,
      Kimchi.Gate.EndoMul.some_congr d.W hnegT'' hnegT hbx' hny, hpt, hnegPt]
    simp only [unshiftType1]
    module
  refine ⟨CVar.Scoped.scale_ _ (hy.of_le hle), ⟨hfin, hnegT', hgyne, fun _ => ?_⟩, hsum⟩
  rw [hsum hfin hnegT']
  intro h0
  exact hs1 ((zsmul_eq_zero_iff_order_dvd d.W (Point.some_ne_zero hT) _).1 h0)

/-- The honest run of `scaleFast2`, generic over the curve dictionary: on an in-scope
on-curve base, an in-scope in-range half whose `Type1` decode satisfies the inner
ladder's regime, and a parity flag reading a genuine bit, the prover lands at
`scaleFast2Run` — the inner ladder (`varBaseMul_run`), the pins of the bits above the
half's width (zero, `testBit` vanishes above a value's width), the correction
(`addFast_run` at `correction_facts`), and the two selections. -/
theorem scaleFast2_run [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F] [d : HasCurve F]
    (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n) (hd : sDiv2Bits ≤ 5 * chunks)
    (st : ProverState F) {base : AffinePoint (FVar F)} {sDiv2 : FVar F} {sOdd : BoolVar F}
    {bb : Bool} (hs : sDiv2.Scoped st) (hb : (↑sOdd : CVar F).Scoped st)
    (hbv : (↑sOdd : CVar F).val st.env.toValuation = bit bb)
    (hx : base.x.Scoped st) (hy : base.y.Scoped st)
    (hrange : ToNat.toNat (sDiv2.val st.env.toValuation) < 2 ^ sDiv2Bits)
    (hreg : d.LadderRegime (5 * chunks)
      (unshiftType1 (5 * chunks) (ToNat.toNat (sDiv2.val st.env.toValuation) : ℤ)))
    (hT : d.W.Nonsingular (base.x.val st.env.toValuation) (base.y.val st.env.toValuation)) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (scaleFast2 (c := KimchiConstraint F) n chunks sDiv2Bits base sDiv2 sOdd) st.nv st.env
      = .ok ((scaleFast2Run n chunks st base sDiv2 sOdd).1.out
          (scaleFast2Run n chunks st base sDiv2 sOdd).2) := by
  have hrange' : ToNat.toNat (sDiv2.val st.env.toValuation) < 2 ^ (5 * chunks) :=
    lt_of_lt_of_le hrange (Nat.pow_le_pow_right (by norm_num) hd)
  obtain ⟨hle, hgx, hgy, hbits, -, -⟩ :=
    varBaseMulRun_grants n chunks hn st (scalar := ⟨sDiv2⟩) hs hx hy hrange' hreg hT
  obtain ⟨hsneg, hops, -⟩ := correction_facts n chunks sDiv2Bits hn hd st hs hx hy hrange hreg hT
  simp only [scaleFast2, scaleFast2Run, prove_bind]
  rw [varBaseMul_run n chunks hn st (scalar := ⟨sDiv2⟩) hs hx hy hrange' hreg hT]
  simp only [Except.bind]
  rw [prove_forIn_unit _ _ _ (fun bpin hbpin => ?_)]
  · simp only []
    rw [AddFast.addFast_run (p2' := ⟨base.x, CVar.negate_ base.y⟩) .checkFinite _ hgx hgy
      (hx.of_le hle) hsneg hops]
    simp only []
    have hg₂ := AddFast.addFastRun_grants (p2' := ⟨base.x, CVar.negate_ base.y⟩) .checkFinite _
      hgx hgy (hx.of_le hle) hsneg hops
    obtain ⟨hle₂, hqx, hqy, -, -⟩ := hg₂
    have hb₂ := hb.of_le (hle.trans hle₂)
    have hbv₂ := (CVar.val_of_le (hle.trans hle₂) hb).trans hbv
    rw [select_run _ hb₂ (hgy.of_le hle₂) hqy hbv₂]
    simp only []
    have hgy' := selectRun_grants hb₂ (hgy.of_le hle₂) hqy hbv₂
    rw [select_run _ (hb₂.of_le hgy'.le) (hgx.of_le (hle₂.trans hgy'.le)) (hqx.of_le hgy'.le)
      (by rw [CVar.val_of_le hgy'.le hb₂, hbv₂])]
    rfl
  · -- a dropped bit reads zero: `testBit` vanishes above the half's width
    obtain ⟨k, hk', hEq⟩ := List.mem_iff_getElem.mp hbpin
    have hkn : sDiv2Bits + k < n := by
      have hlen : ((varBaseMulRun n chunks st base ⟨sDiv2⟩).2.lsbBits.toList.drop
          sDiv2Bits).length = n - sDiv2Bits := by
        simp [List.length_drop]
      omega
    rw [← hEq, List.getElem_drop, Vector.getElem_toList]
    have hbfalse : (ToNat.toNat (sDiv2.val st.env.toValuation)).testBit (sDiv2Bits + k) = false := by
      apply Nat.testBit_lt_two_pow
      calc ToNat.toNat (sDiv2.val st.env.toValuation) < 2 ^ sDiv2Bits := hrange
        _ ≤ 2 ^ (sDiv2Bits + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [prove_bind]
    rw [assertEqual_run _ (hbits _ hkn).1 (CVar.scoped_const _ _) (by
      rw [(hbits _ hkn).2, hbfalse]
      rfl)]
    rfl

/-- What `scaleFast2Run` grants — the honest side of the PS defining equation
`scaleFast2 g (sDiv2, sOdd) ~ [fromShifted (sDiv2, sOdd)]·g`: the table grew, the result
is in scope, and it reads as the `unshiftType2` decode's multiple at the parity bit. -/
theorem scaleFast2Run_grants [Field F] [DecidableEq F] [ToNat F] [d : HasCurve F]
    (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n) (hd : sDiv2Bits ≤ 5 * chunks)
    (st : ProverState F) {base : AffinePoint (FVar F)} {sDiv2 : FVar F} {sOdd : BoolVar F}
    {bb : Bool} (hs : sDiv2.Scoped st) (hb : (↑sOdd : CVar F).Scoped st)
    (hbv : (↑sOdd : CVar F).val st.env.toValuation = bit bb)
    (hx : base.x.Scoped st) (hy : base.y.Scoped st)
    (hrange : ToNat.toNat (sDiv2.val st.env.toValuation) < 2 ^ sDiv2Bits)
    (hreg : d.LadderRegime (5 * chunks)
      (unshiftType1 (5 * chunks) (ToNat.toNat (sDiv2.val st.env.toValuation) : ℤ)))
    (hT : d.W.Nonsingular (base.x.val st.env.toValuation) (base.y.val st.env.toValuation)) :
    st.env.Le (scaleFast2Run n chunks st base sDiv2 sOdd).1.env ∧
      (scaleFast2Run n chunks st base sDiv2 sOdd).2.x.Scoped
        (scaleFast2Run n chunks st base sDiv2 sOdd).1 ∧
      (scaleFast2Run n chunks st base sDiv2 sOdd).2.y.Scoped
        (scaleFast2Run n chunks st base sDiv2 sOdd).1 ∧
      ∃ hres : d.W.Nonsingular
          ((scaleFast2Run n chunks st base sDiv2 sOdd).2.x.val
            (scaleFast2Run n chunks st base sDiv2 sOdd).1.env.toValuation)
          ((scaleFast2Run n chunks st base sDiv2 sOdd).2.y.val
            (scaleFast2Run n chunks st base sDiv2 sOdd).1.env.toValuation),
        Point.some _ _ hres
          = unshiftType2 (5 * chunks) (ToNat.toNat (sDiv2.val st.env.toValuation) : ℤ) (bit bb)
              • Point.some _ _ hT := by
  have hrange' : ToNat.toNat (sDiv2.val st.env.toValuation) < 2 ^ (5 * chunks) :=
    lt_of_lt_of_le hrange (Nat.pow_le_pow_right (by norm_num) hd)
  obtain ⟨hle, hgx, hgy, -, hfin, hpt⟩ :=
    varBaseMulRun_grants n chunks hn st (scalar := ⟨sDiv2⟩) hs hx hy hrange' hreg hT
  obtain ⟨hsneg, hops, hsum⟩ := correction_facts n chunks sDiv2Bits hn hd st hs hx hy hrange hreg hT
  have hg₂ := AddFast.addFastRun_grants (p2' := ⟨base.x, CVar.negate_ base.y⟩) .checkFinite _
    hgx hgy (hx.of_le hle) hsneg hops
  obtain ⟨hfinT, hnegT, -, -⟩ := hops
  obtain ⟨hle₂, hqx, hqy, -, hsumq⟩ := hg₂
  obtain ⟨hqns, -, hqsum⟩ := (hsumq hfinT hnegT).resolve_left (by
    rintro ⟨-, hzero⟩
    rw [hsum hfinT hnegT] at hzero
    haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
    haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
      ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
    have hvlt : (ToNat.toNat (sDiv2.val st.env.toValuation) : ℤ) < 2 ^ (5 * chunks) := by
      exact_mod_cast hrange'
    exact regime_off_base (Int.natCast_nonneg _) hvlt hreg
      ((Kimchi.Gate.VarBaseMul.zsmul_eq_zero_iff_order_dvd d.W (Point.some_ne_zero hT) _).1 hzero))
  have hqpt : Point.some _ _ hqns
      = (2 * (ToNat.toNat (sDiv2.val st.env.toValuation) : ℤ) + 2 ^ (5 * chunks))
          • Point.some _ _ hT := by
    rw [← hqsum, hsum hfinT hnegT]
  have hb₂ := hb.of_le (hle.trans hle₂)
  have hbv₂ := (CVar.val_of_le (hle.trans hle₂) hb).trans hbv
  have hgy' := selectRun_grants hb₂ (hgy.of_le hle₂) hqy hbv₂
  have hgx' := selectRun_grants (hb₂.of_le hgy'.le) (hgx.of_le (hle₂.trans hgy'.le))
    (hqx.of_le hgy'.le) (by rw [CVar.val_of_le hgy'.le hb₂, hbv₂])
  dsimp only [scaleFast2Run]
  refine ⟨hle.trans (hle₂.trans (hgy'.le.trans hgx'.le)), hgx'.fvar_scoped,
    hgy'.fvar_scoped.of_le hgx'.le, ?_⟩
  rw [hgx'.fvar_val, CVar.val_of_le hgx'.le hgy'.fvar_scoped, hgy'.fvar_val,
    CVar.val_of_le hgy'.le (hgx.of_le hle₂), CVar.val_of_le hgy'.le hqx, CVar.val_of_le hle₂ hgx,
    CVar.val_of_le hle₂ hgy]
  cases bb
  · dsimp only [selectPure]
    refine ⟨hqns, ?_⟩
    rw [show unshiftType2 (5 * chunks) (ToNat.toNat (sDiv2.val st.env.toValuation) : ℤ) (bit false)
        = 2 * (ToNat.toNat (sDiv2.val st.env.toValuation) : ℤ) + 2 ^ (5 * chunks) from by
      simp [unshiftType2, bit]]
    exact hqpt
  · dsimp only [selectPure]
    refine ⟨hfin, ?_⟩
    rw [show unshiftType2 (5 * chunks) (ToNat.toNat (sDiv2.val st.env.toValuation) : ℤ) (bit true)
        = unshiftType1 (5 * chunks) (ToNat.toNat (sDiv2.val st.env.toValuation) : ℤ) from by
      simp [unshiftType2, unshiftType1, bit]; ring]
    exact hpt

/-- The state and result of `splitFieldVar`'s honest run: the parity split at the
counter, the half and the bit as the two fresh variables. -/
def splitFieldVarRun [Field F] [DecidableEq F] [ToNat F] (st : ProverState F) (s : FVar F) :
    ProverState F × (FVar F × BoolVar F) :=
  (st.extendMany [(splitField (s.val st.env.toValuation)).1,
      bit (splitField (s.val st.env.toValuation)).2],
    (.var st.nv, .unchecked (.var (st.nv + 1))))

/-- The honest run of `splitFieldVar`: on an in-scope operand in odd characteristic the
recombination assert accepts — `2·((s − sOdd)/2) + sOdd = s` needs only `2 ≠ 0`, for ANY
parity bit — and the prover lands at `splitFieldVarRun`. -/
theorem splitFieldVar_run [Field F] [DecidableEq F] [ToNat F] {s : FVar F} (st : ProverState F)
    (hs : s.Scoped st) (h2 : (2 : F) ≠ 0) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (splitFieldVar (c := KimchiConstraint F) s) st.nv st.env
      = .ok ((splitFieldVarRun st s).1.out (splitFieldVarRun st s).2) := by
  simp only [splitFieldVar, splitFieldVarRun, prove_bind]
  rw [prove_witness_run (w := splitFieldWit s) st (.bind (.readCVar hs) fun _ => trivial)
    (v := splitField (s.val st.env.toValuation)) (by simp [splitFieldWit, Except.bind])]
  simp only [valueToFields_prod_toList, valueToFields_fvar_toList, valueToFields_bool_toList,
    List.cons_append, List.nil_append, fieldsToVar_prod_alloc, fieldsToVar_fvar_alloc,
    fieldsToVar_bool_alloc, Except.bind]
  simp only [size_fvar]
  have hle := st.le_extendMany [(splitField (s.val st.env.toValuation)).1,
    bit (splitField (s.val st.env.toValuation)).2]
  have hh : (CVar.var st.nv).Scoped (st.extendMany [(splitField (s.val st.env.toValuation)).1,
      bit (splitField (s.val st.env.toValuation)).2]) := ProverState.mem_extendMany_head ..
  have ho : (CVar.var (st.nv + 1)).Scoped (st.extendMany
      [(splitField (s.val st.env.toValuation)).1, bit (splitField (s.val st.env.toValuation)).2]) :=
    st.new_mem_extendMany (i := 1) (by simp)
  have hhv : (CVar.var st.nv).val (st.extendMany [(splitField (s.val st.env.toValuation)).1,
      bit (splitField (s.val st.env.toValuation)).2]).env.toValuation
      = (splitField (s.val st.env.toValuation)).1 := ProverState.get_extendMany_head ..
  have hov : (CVar.var (st.nv + 1)).val (st.extendMany [(splitField (s.val st.env.toValuation)).1,
      bit (splitField (s.val st.env.toValuation)).2]).env.toValuation
      = bit (splitField (s.val st.env.toValuation)).2 := by
    show (st.extendMany _).env.toValuation (st.nv + 1) = _
    rw [ProverState.get_extendMany_new st (by simp)]
    rfl
  rw [assertEqual_run _ (hs.of_le hle)
    (CVar.Scoped.add_ (CVar.Scoped.scale_ _ hh) (by rw [BoolVar.toCVar_unchecked]; exact ho)) (by
      rw [CVar.val_add_, CVar.val_scale_, BoolVar.toCVar_unchecked, hhv, hov,
        CVar.val_of_le hle hs]
      by_cases hoddc : (ToNat.toNat (s.val st.env.toValuation)) % 2 = 1 <;>
        simp only [splitField, bit, hoddc, if_true, if_false] <;>
        field_simp <;>
        simp)]
  rfl

/-- What `splitFieldVarRun` grants: the table grew, the pair is in scope, and it reads
as the parity split. -/
theorem splitFieldVarRun_grants [Field F] [DecidableEq F] [ToNat F] {s : FVar F}
    (st : ProverState F) :
    st.env.Le (splitFieldVarRun st s).1.env ∧
      (splitFieldVarRun st s).2.1.Scoped (splitFieldVarRun st s).1 ∧
      (↑(splitFieldVarRun st s).2.2 : CVar F).Scoped (splitFieldVarRun st s).1 ∧
      (splitFieldVarRun st s).2.1.val (splitFieldVarRun st s).1.env.toValuation
        = (splitField (s.val st.env.toValuation)).1 ∧
      (↑(splitFieldVarRun st s).2.2 : CVar F).val (splitFieldVarRun st s).1.env.toValuation
        = bit (splitField (s.val st.env.toValuation)).2 := by
  refine ⟨st.le_extendMany _, ProverState.mem_extendMany_head .., ?_,
    ProverState.get_extendMany_head .., ?_⟩
  · show (CVar.var (st.nv + 1)).Scoped _
    exact st.new_mem_extendMany (i := 1) (by simp)
  · show (st.extendMany _).env.toValuation (st.nv + 1) = _
    rw [ProverState.get_extendMany_new st (by simp)]
    rfl

/-- The state and result of `scaleFast2'`'s honest run: the split, then `scaleFast2`. -/
def scaleFast2'Run [Field F] [DecidableEq F] [ToNat F] (n chunks : ℕ) (st : ProverState F)
    (base : AffinePoint (FVar F)) (s : FVar F) : ProverState F × AffinePoint (FVar F) :=
  scaleFast2Run n chunks (splitFieldVarRun st s).1 base (splitFieldVarRun st s).2.1
    (splitFieldVarRun st s).2.2

/-- The honest run of `scaleFast2'`: `splitFieldVar_run`, then `scaleFast2_run` at the
split's readings — the split's half must be in range and regime-satisfying (its `Type1`
decode feeds the inner ladder). -/
theorem scaleFast2'_run [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F] [d : HasCurve F]
    (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n) (hd : sDiv2Bits ≤ 5 * chunks)
    (st : ProverState F) {base : AffinePoint (FVar F)} {sc : FVar F} (hs : sc.Scoped st)
    (hx : base.x.Scoped st) (hy : base.y.Scoped st)
    (hrange : ToNat.toNat (splitField (sc.val st.env.toValuation)).1 < 2 ^ sDiv2Bits)
    (hreg : d.LadderRegime (5 * chunks)
      (unshiftType1 (5 * chunks) (ToNat.toNat (splitField (sc.val st.env.toValuation)).1 : ℤ)))
    (hT : d.W.Nonsingular (base.x.val st.env.toValuation) (base.y.val st.env.toValuation)) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (scaleFast2' (c := KimchiConstraint F) n chunks sDiv2Bits base sc) st.nv st.env
      = .ok ((scaleFast2'Run n chunks st base sc).1.out (scaleFast2'Run n chunks st base sc).2) := by
  obtain ⟨hle, hsh, hso, hhv, hov⟩ := splitFieldVarRun_grants (s := sc) st
  simp only [scaleFast2', scaleFast2'Run, prove_bind]
  rw [splitFieldVar_run st hs d.two_ne]
  simp only [Except.bind]
  rw [scaleFast2_run n chunks sDiv2Bits hn hd _ (bb := (splitField (sc.val st.env.toValuation)).2)
    hsh hso hov (hx.of_le hle) (hy.of_le hle) (by rw [hhv]; exact hrange) (by rw [hhv]; exact hreg)
    (by rw [CVar.val_of_le hle hx, CVar.val_of_le hle hy]; exact hT)]

/-- What `scaleFast2'Run` grants — the honest side of the defining equation
`scaleFast2' g s ~ [s + 2^(5·chunks)]·g`, `s` read through its parity split: the
`unshiftType2` decode's multiple at the honest split. -/
theorem scaleFast2'Run_grants [Field F] [DecidableEq F] [ToNat F] [d : HasCurve F]
    (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n) (hd : sDiv2Bits ≤ 5 * chunks)
    (st : ProverState F) {base : AffinePoint (FVar F)} {sc : FVar F} (hs : sc.Scoped st)
    (hx : base.x.Scoped st) (hy : base.y.Scoped st)
    (hrange : ToNat.toNat (splitField (sc.val st.env.toValuation)).1 < 2 ^ sDiv2Bits)
    (hreg : d.LadderRegime (5 * chunks)
      (unshiftType1 (5 * chunks) (ToNat.toNat (splitField (sc.val st.env.toValuation)).1 : ℤ)))
    (hT : d.W.Nonsingular (base.x.val st.env.toValuation) (base.y.val st.env.toValuation)) :
    st.env.Le (scaleFast2'Run n chunks st base sc).1.env ∧
      (scaleFast2'Run n chunks st base sc).2.x.Scoped (scaleFast2'Run n chunks st base sc).1 ∧
      (scaleFast2'Run n chunks st base sc).2.y.Scoped (scaleFast2'Run n chunks st base sc).1 ∧
      ∃ hres : d.W.Nonsingular
          ((scaleFast2'Run n chunks st base sc).2.x.val
            (scaleFast2'Run n chunks st base sc).1.env.toValuation)
          ((scaleFast2'Run n chunks st base sc).2.y.val
            (scaleFast2'Run n chunks st base sc).1.env.toValuation),
        Point.some _ _ hres
          = unshiftType2 (5 * chunks) (ToNat.toNat (splitField (sc.val st.env.toValuation)).1 : ℤ)
              (bit (splitField (sc.val st.env.toValuation)).2) • Point.some _ _ hT := by
  have _ := hs
  obtain ⟨hle, hsh, hso, hhv, hov⟩ := splitFieldVarRun_grants (s := sc) st
  have hT' : d.W.Nonsingular (base.x.val (splitFieldVarRun st sc).1.env.toValuation)
      (base.y.val (splitFieldVarRun st sc).1.env.toValuation) := by
    rw [CVar.val_of_le hle hx, CVar.val_of_le hle hy]; exact hT
  obtain ⟨hle', hgx, hgy, hres, hpt⟩ := scaleFast2Run_grants n chunks sDiv2Bits hn hd _
    (bb := (splitField (sc.val st.env.toValuation)).2) hsh hso hov (hx.of_le hle) (hy.of_le hle)
    (by rw [hhv]; exact hrange) (by rw [hhv]; exact hreg) hT'
  dsimp only [scaleFast2'Run]
  refine ⟨hle.trans hle', hgx, hgy, hres, ?_⟩
  rw [hpt, hhv, Kimchi.Gate.EndoMul.some_congr d.W hT' hT (CVar.val_of_le hle hx)
    (CVar.val_of_le hle hy)]

end Snarky.Kimchi
