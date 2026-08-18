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

variable {F c : Type}

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

/-! ## The curve dictionary and the soundness laws -/

open Std.Do WeierstrassCurve.Affine

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
    ∃ bits : List F,
      (∀ b ∈ bits, b = 0 ∨ b = 1) ∧ bits.length = 5 * pref.length ∧
      bits = (roundBits rounds).map (·.val V) ∧
      fin.2.val V = bitsRegister bits ∧
      ∀ _ : (3 : ℕ) * 2 ^ (5 * pref.length) ≤ W.order ∨
          (2 ^ (5 * pref.length - 1) < W.order ∧ W.order < 2 ^ (5 * pref.length) ∧
            W.order % 4 = 1 ∧
            (2 * bitsVal bits + 2 ^ (5 * pref.length) + 1) ∉ forbiddenValues W.order),
        ∃ hfin : W.Nonsingular (fin.1.x.val V) (fin.1.y.val V),
          Point.some _ _ hfin
            = (2 * bitsVal bits + 2 ^ (5 * pref.length) + 1) • Point.some _ _ hT := by
  match hround : rounds, hthr with
  | [], hthr' =>
    obtain ⟨rfl, rfl⟩ := Threaded.nil hthr'
    refine ⟨[], by simp, by simp, by simp [roundBits],
      by simp [bitsRegister, CVar.val], fun _ => ?_⟩
    refine ⟨hP0ns, ?_⟩
    rw [hP0]
    norm_num [bitsVal]
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
    refine ⟨runBits g (rs.length + 1),
      runBits_bool (rs.length + 1) g hHolds,
      by rw [runBits_length, hm],
      read_runBits (r₀ :: rs) r₀,
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
          (2 * bitsVal (runBits g (rs.length + 1)) + 2 ^ (5 * (rs.length + 1)) + 1)
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
          (by rw [gateLadder_eq_register, gateRegister_eq_bitsVal])
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

open Kimchi.Gate.VarBaseMul (bitsRegister bitsVal) in
open Kimchi.Gate.VarBaseMul (y_ne_zero_of_odd_order) in
/-- The gadget is sound: under any satisfying valuation, for a base point reading
on-curve, the wired bits are boolean, the scalar reads as their base-2 fold, and —
whenever the ladder's regime fact holds at the bits' `Type1.fromShifted` decode —
the result reads as exactly that multiple of the base:
`varBaseMul g (Type1 t) ~ [2·t + 2^bits + 1]·g`, the `fromShifted` decode.
The curve facts arrive bundled as the dictionary `d : HasCurve F`; the
regime fact (`HasCurve.LadderRegime`) is the ladder's analog of `endoMul`'s
off-targets promise — per-scalar, because the one-wrap band's forbidden residues
depend on the decoded value. -/
theorem varBaseMul_spec [Field F] [DecidableEq F] [ToNat F] (d : HasCurve F)
    (n chunks : ℕ) (hn : 5 * chunks ≤ n)
    (base : AffinePoint (FVar F)) (scalar : Type1 (FVar F))
    (Q : PostCond (VarBaseMulResult n F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : VarBaseMulResult n F) =>
        ∀ hT : d.W.Nonsingular (base.x.val V) (base.y.val V),
          ∃ bits : List F,
            (∀ b ∈ bits, b = 0 ∨ b = 1) ∧ bits.length = 5 * chunks ∧
            bits = ((r.lsbBits.toList.take (5 * chunks)).reverse).map (·.val V) ∧
            scalar.val.val V = bitsRegister bits ∧
            ∀ _ : d.LadderRegime (5 * chunks)
                (Type1.fromShifted (5 * chunks) ⟨bitsVal bits⟩),
              ∃ hfin : d.W.Nonsingular (r.g.x.val V) (r.g.y.val V),
                Point.some _ _ hfin
                  = Type1.fromShifted (5 * chunks) ⟨bitsVal bits⟩
                      • Point.some _ _ hT) Q⦄
    (varBaseMul (c := KimchiConstraint F) n chunks base scalar)
    ⦃Q⦄ := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  simp only [varBaseMul, scaleRound, mapAccumM]
  mvcgen
  rename_i s hpre
  intro sbase _ hsx hsy
  mvcgen
  intro bits _
  mvcgen
  refine AddFast.addFast_checkFinite_spec d.W d.short d.two_ne sbase sbase _ _ ?_
  intro p nv hp
  mvcgen
  case inv1 =>
    exact ⇓ pr s' => ⌜s'.V = s.V ∧
      VarBaseMul.Threaded sbase (p.p, .const 0) pr.1.prefix pr.2.snd pr.2.fst⌝
  case vc2.vc1.vc1.vc1.pre =>
    exact ⟨rfl, rfl, rfl⟩
  case vc1.step =>
    rename_i pref cur suff hsplit b st' hinv
    intro nAcc nv0
    mvcgen
    intro w0 nv1
    mvcgen
    intro w1 nv2
    mvcgen
    intro w2 nv3
    mvcgen
    intro w3 nv4
    mvcgen
    intro w4 nv5
    mvcgen
    obtain ⟨hV, hthr⟩ := hinv
    exact ⟨hV, hthr.snoc cur nAcc w0 w1 w2 w3 w4⟩
  case vc3.vc1.vc1.vc1.post.success =>
    rename_i finp st' hinv
    obtain ⟨hV, hthr⟩ := hinv
    intro _ nv6 hpay
    mvcgen
    intro _ nv7 heq
    rw [hV] at hpay heq
    rw [hV]
    mvcgen
    refine hpre ⟨finp.fst.1, bits⟩ _ ?_
    intro hT
    have hT' : d.W.Nonsingular (sbase.x.val s.V) (sbase.y.val s.V) := by
      rw [hsx, hsy]
      exact hT
    have hy : sbase.y.val s.V ≠ 0 :=
      y_ne_zero_of_odd_order d.W d.odd hT'
    obtain ⟨hP0ns, hsum⟩ := hp hT' hT' hy
    have hP0 : Point.some _ _ hP0ns = (2 : ℤ) • Point.some _ _ hT' := by
      rw [← hsum]
      module
    obtain ⟨bl, hbool, hblen, hsrc, hregpin, hpoint⟩ :=
      VarBaseMul.threaded_sound d.W d.two_ne d.odd s.V hthr hpay hT' hP0ns hP0
    have hTeq : Point.some _ _ hT' = Point.some _ _ hT :=
      Kimchi.Gate.EndoMul.some_congr d.W hT' hT hsx hsy
    have hsrc' : bl = (((bits.toList.take (5 * chunks)).reverse).map (·.val s.V)) := by
      rw [hsrc, VarBaseMul.threaded_roundBits hthr, List.flatMap_map,
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
    refine ⟨bl, hbool, by simpa using hblen, hsrc',
      heq.symm.trans hregpin, fun hregime => ?_⟩
    obtain ⟨hfin, hpt⟩ := hpoint (by simpa [Type1.fromShifted] using hregime)
    exact ⟨hfin, by rw [← hTeq]; simpa [Type1.fromShifted] using hpt⟩

/-- `scaleFast2' g s ~ [s + 2^n]·g`: split the raw scalar, then `scaleFast2`. -/
def scaleFast2' [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (n chunks sDiv2Bits : ℕ) (base : AffinePoint (FVar F))
    (s : FVar F) : CircuitM F c (AffinePoint (FVar F)) := do
  let (sDiv2, sOdd) ← splitFieldVar s
  scaleFast2 n chunks sDiv2Bits base sDiv2 sOdd

open Std.Do in
/-- The checked pair witness `(F, Bool)`: the `boolean` row emitted on the second
component makes it a bit — `splitFieldVar`'s leaf, the pair analog of
`witnessBool_spec`. -/
private theorem witnessFBool_spec [Field F] [DecidableEq F] {c : Type}
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (w : AsProver F (F × Bool))
    (Q : PostCond (FVar F × BoolVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : FVar F × BoolVar F) =>
        (↑r.2 : CVar F).val V = 0 ∨ (↑r.2 : CVar F).val V = 1) Q⦄
    (witness (val := F × Bool) w : CircuitM F c (FVar F × BoolVar F))
    ⦃Q⦄ := by
  intro s hpre hsat
  exact hpre _ _
    (LawfulBasicSystem.holds_boolean s.V _ (hsat _ (List.mem_cons_self ..)))

/-- `splitFieldVar` is sound: the operand reads as the parity recombination
`2·sDiv2 + sOdd` of the returned pair, with the parity a genuine bit (its witness's
`boolean` row). -/
theorem splitFieldVar_spec [Field F] [DecidableEq F] [ToNat F]
    (s : FVar F) (Q : PostCond (FVar F × BoolVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : FVar F × BoolVar F) =>
        s.val V = 2 * r.1.val V + (↑r.2 : CVar F).val V ∧
        ((↑r.2 : CVar F).val V = 0 ∨ (↑r.2 : CVar F).val V = 1)) Q⦄
    (splitFieldVar (c := KimchiConstraint F) s)
    ⦃Q⦄ := by
  simp only [splitFieldVar]
  mvcgen [witnessFBool_spec, -witness_spec]
  rename_i st hpre
  intro r _ hbool
  mvcgen
  intro _ _ heq
  mvcgen
  refine hpre r _ ?_ hbool
  rw [heq]
  simp [CVar.val_add_, CVar.val_scale_]

open Kimchi.Gate.VarBaseMul (bitsRegister bitsVal bitsVal_lt bitsRegister_eq_cast) in
/-- `scaleFast1` is sound — the PS defining equation
`scaleFast1 g a ~ scalarMul (fromShifted a) g`: the result reads as `[s]·g` for the
`Type1` unshift `s = fromShifted t`, pinned in `F` and bounded by the width. The
bounds feed the wrap analysis: the F-pin fixes `s` only mod the characteristic (at
full width the wire genuinely cannot distinguish `t` from `t + p` — the ambiguity
the forbidden band exists to police), and the structural range is what the regime's
mod-order reasoning consumes; below the characteristic they determine `s` exactly.
The wired bits are `varBaseMul_spec`'s business; this statement is decode-only. -/
theorem scaleFast1_spec [Field F] [DecidableEq F] [ToNat F] (d : HasCurve F)
    (n chunks : ℕ) (hn : 5 * chunks ≤ n)
    (p : AffinePoint (FVar F)) (t : Type1 (FVar F))
    (Q : PostCond (AffinePoint (FVar F)) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : AffinePoint (FVar F)) =>
        ∀ hT : d.W.Nonsingular (p.x.val V) (p.y.val V),
          ∃ s : ℤ,
            2 ^ (5 * chunks) < s ∧ s < 3 * 2 ^ (5 * chunks) ∧
            (s : F) = Type1.fromShifted (5 * chunks) ⟨t.val.val V⟩ ∧
            ∀ _ : d.LadderRegime (5 * chunks) s,
              ∃ hfin : d.W.Nonsingular (r.x.val V) (r.y.val V),
                Point.some _ _ hfin = s • Point.some _ _ hT) Q⦄
    (scaleFast1 (c := KimchiConstraint F) n chunks p t)
    ⦃Q⦄ := by
  simp only [scaleFast1]
  mvcgen
  refine varBaseMul_spec d n chunks hn p t _ _ ?_
  intro r nv hr
  mvcgen
  rename_i st hpre
  refine hpre r.g _ (fun hT => ?_)
  obtain ⟨bl, hb, hl, -, hreg, hpt⟩ := hr hT
  obtain ⟨hlt, hnn⟩ := bitsVal_lt bl hb
  rw [hl] at hlt
  refine ⟨2 * bitsVal bl + 2 ^ (5 * chunks) + 1, by omega, by omega, ?_,
    fun hregime => hpt hregime⟩
  rw [hreg, bitsRegister_eq_cast bl hb]
  simp only [Type1.fromShifted]
  push_cast
  ring

open Kimchi.Gate.VarBaseMul (bitsRegister bitsVal bitsVal_lt bitsVal_drop_of_zeros
  bitsRegister_eq_cast y_ne_zero_of_odd_order) in
/-- `scaleFast2` is sound — the PS defining equation
`scaleFast2 g (sDiv2, sOdd) ~ [fromShifted (sDiv2, sOdd)]·g`, the `SplitField`
decode `2·sDiv2 + sOdd + 2^(5·chunks)`: the inner ladder computes the register's
`Type1.fromShifted` multiple, the high-bit pins force `v < 2^sDiv2Bits`, and the
parity correction folds `sOdd` in by conditionally subtracting the base. The
parity's booleanity is the caller's promise (the `select_spec` shape);
`splitFieldVar` supplies it in `scaleFast2'`. -/
theorem scaleFast2_spec [Field F] [DecidableEq F] [ToNat F] (d : HasCurve F)
    (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n) (hd : sDiv2Bits ≤ 5 * chunks)
    (base : AffinePoint (FVar F)) (sDiv2 : FVar F) (sOdd : BoolVar F)
    (Q : PostCond (AffinePoint (FVar F)) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : AffinePoint (FVar F)) =>
        ∀ hT : d.W.Nonsingular (base.x.val V) (base.y.val V),
        ∀ bb : Bool, (↑sOdd : CVar F).val V = bit bb →
          ∃ v : ℤ, 0 ≤ v ∧ v < 2 ^ sDiv2Bits ∧ sDiv2.val V = ((v : ℤ) : F) ∧
            ∀ _ : d.LadderRegime (5 * chunks) (Type1.fromShifted (5 * chunks) ⟨v⟩),
              ∃ hres : d.W.Nonsingular (r.x.val V) (r.y.val V),
                Point.some _ _ hres
                  = SplitField.fromShifted (5 * chunks) ⟨v, bb⟩
                      • Point.some _ _ hT) Q⦄
    (scaleFast2 (c := KimchiConstraint F) n chunks sDiv2Bits base sDiv2 sOdd)
    ⦃Q⦄ := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  simp only [scaleFast2]
  mvcgen
  rename_i s hpre
  refine varBaseMul_spec d n chunks hn base ⟨sDiv2⟩ _ _ ?_
  intro r nv hr
  mvcgen
  case inv1 =>
    exact ⇓ p s' => ⌜s'.V = s.V ∧ ∀ b ∈ p.1.prefix, b.val s.V = 0⌝
  case step =>
    rename_i pref cur suff hsplit u st' hinv
    intro _ nv hpin
    mvcgen
    refine ⟨hinv.1, fun b hb => ?_⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact hinv.2 b hb
    · rw [List.mem_singleton.mp hb, ← hinv.1]
      simpa using hpin
  case pre => exact ⟨rfl, by simp⟩
  case post.success =>
    rename_i u st' hinv
    obtain ⟨hV, hzeros⟩ := hinv
    mvcgen
    refine AddFast.addFast_checkFinite_spec d.W d.short d.two_ne r.g
      ⟨base.x, CVar.negate_ base.y⟩ _ _ ?_
    intro q nvq hq
    rw [hV] at hq
    mvcgen
    intro y _ hysel
    rw [hV] at hysel
    mvcgen
    intro x _ hxsel
    rw [hV] at hxsel
    mvcgen
    rw [hV]
    refine hpre ⟨x, y⟩ _ ?_
    intro hT bb hbb
    obtain ⟨bl, hbool, hblen, hsrc, hregF, hpfn⟩ := hr hT
    -- the pins force the decode's leading window to zero
    have hzeros' : ∀ b ∈ bl.take (5 * chunks - sDiv2Bits), b = 0 := by
      intro b hb
      rw [hsrc, ← List.map_take] at hb
      obtain ⟨fv, hfv, rfl⟩ := List.mem_map.mp hb
      apply hzeros
      rw [List.take_reverse,
        show (r.lsbBits.toList.take (5 * chunks)).length - (5 * chunks - sDiv2Bits)
            = sDiv2Bits from by
          simp only [List.length_take, Vector.length_toList]
          omega,
        List.mem_reverse, List.drop_take] at hfv
      exact List.mem_of_mem_take hfv
    have hvlt : bitsVal bl < 2 ^ sDiv2Bits ∧ 0 ≤ bitsVal bl := by
      rw [bitsVal_drop_of_zeros bl (5 * chunks - sDiv2Bits) hzeros']
      have hb' : ∀ b ∈ bl.drop (5 * chunks - sDiv2Bits), b = 0 ∨ b = 1 :=
        fun b hb => hbool b (List.mem_of_mem_drop hb)
      have hlt := bitsVal_lt _ hb'
      rwa [List.length_drop, hblen,
        show 5 * chunks - (5 * chunks - sDiv2Bits) = sDiv2Bits from by omega] at hlt
    refine ⟨bitsVal bl, hvlt.2, hvlt.1, ?_, fun hregime => ?_⟩
    · rw [hregF, bitsRegister_eq_cast bl hbool]
    · obtain ⟨hg, hgpt⟩ := hpfn hregime
      simp only [Type1.fromShifted] at hgpt
      have hnegv : (CVar.negate_ base.y).val s.V = -(base.y.val s.V) := by
        simp [CVar.negate_, CVar.val_scale_]
      have hnegT : d.W.Nonsingular (base.x.val s.V) ((CVar.negate_ base.y).val s.V) := by
        rw [hnegv]
        have hneg := (d.W.nonsingular_neg (base.x.val s.V) (base.y.val s.V)).mpr hT
        rwa [show d.W.negY (base.x.val s.V) (base.y.val s.V) = -(base.y.val s.V) from by
          rw [WeierstrassCurve.Affine.negY, d.short.1, d.short.2.2.1]
          ring] at hneg
      have hy : r.g.y.val s.V ≠ 0 := y_ne_zero_of_odd_order d.W d.odd hg
      obtain ⟨hqns, hqsum⟩ := hq hg hnegT hy
      have hnegPt : (Point.some _ _ hnegT : d.W.Point) = -Point.some _ _ hT := by
        rw [WeierstrassCurve.Affine.Point.neg_some]
        exact Kimchi.Gate.EndoMul.some_congr d.W hnegT _ rfl (by
          rw [hnegv, WeierstrassCurve.Affine.negY, d.short.1, d.short.2.2.1]
          ring)
      have hqpt : (Point.some _ _ hqns : d.W.Point)
          = (2 * bitsVal bl + 2 ^ (5 * chunks)) • Point.some _ _ hT := by
        rw [← hqsum, hgpt, hnegPt]
        module
      have hxv := hxsel bb hbb
      have hyv := hysel bb hbb
      cases bb
      · have hres : d.W.Nonsingular (x.val s.V) (y.val s.V) := by
          rw [hxv, hyv]
          simpa [selectPure] using hqns
        refine ⟨hres, ?_⟩
        rw [show SplitField.fromShifted (5 * chunks) (⟨bitsVal bl, false⟩ : SplitField ℤ Bool)
            = 2 * bitsVal bl + 2 ^ (5 * chunks) from by
          simp [SplitField.fromShifted]]
        refine (Kimchi.Gate.EndoMul.some_congr d.W hres hqns ?_ ?_).trans hqpt
        · rw [hxv]; simp [selectPure]
        · rw [hyv]; simp [selectPure]
      · have hres : d.W.Nonsingular (x.val s.V) (y.val s.V) := by
          rw [hxv, hyv]
          simpa [selectPure] using hg
        refine ⟨hres, ?_⟩
        rw [show SplitField.fromShifted (5 * chunks) (⟨bitsVal bl, true⟩ : SplitField ℤ Bool)
            = 2 * bitsVal bl + 2 ^ (5 * chunks) + 1 from by
          simp [SplitField.fromShifted]; ring]
        refine (Kimchi.Gate.EndoMul.some_congr d.W hres hg ?_ ?_).trans hgpt
        · rw [hxv]; simp [selectPure]
        · rw [hyv]; simp [selectPure]

open Kimchi.Gate.VarBaseMul (bitsRegister bitsVal) in
/-- `scaleFast2'` is sound — `scaleFast2' g s ~ [s + 2^(5·chunks)]·g`, `s` read
through its parity split: the split's recombination `s = 2·v + sOdd` composes with
`scaleFast2`'s `SplitField.fromShifted` decode. -/
theorem scaleFast2'_spec [Field F] [DecidableEq F] [ToNat F] (d : HasCurve F)
    (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n) (hd : sDiv2Bits ≤ 5 * chunks)
    (base : AffinePoint (FVar F)) (sc : FVar F)
    (Q : PostCond (AffinePoint (FVar F)) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : AffinePoint (FVar F)) =>
        ∀ hT : d.W.Nonsingular (base.x.val V) (base.y.val V),
          ∃ (v : ℤ) (bb : Bool), 0 ≤ v ∧ v < 2 ^ sDiv2Bits ∧
            sc.val V = 2 * ((v : ℤ) : F) + bit bb ∧
            ∀ _ : d.LadderRegime (5 * chunks) (Type1.fromShifted (5 * chunks) ⟨v⟩),
              ∃ hres : d.W.Nonsingular (r.x.val V) (r.y.val V),
                Point.some _ _ hres
                  = SplitField.fromShifted (5 * chunks) ⟨v, bb⟩
                      • Point.some _ _ hT) Q⦄
    (scaleFast2' (c := KimchiConstraint F) n chunks sDiv2Bits base sc)
    ⦃Q⦄ := by
  simp only [scaleFast2']
  mvcgen [scaleFast2_spec, splitFieldVar_spec]
  rename_i s hpre
  intro pr nv hsum hbool
  obtain ⟨sd, so⟩ := pr
  refine scaleFast2_spec d n chunks sDiv2Bits hn hd base sd so _ _ ?_
  intro r nv2 hr
  refine hpre r _ ?_
  intro hT
  rcases hbool with h0 | h1
  · obtain ⟨v, hv0, hvlt, hvv, hpt⟩ := hr hT false (by simpa [bit] using h0)
    refine ⟨v, false, hv0, hvlt, ?_, hpt⟩
    rw [hsum, hvv, h0]
    simp [bit]
  · obtain ⟨v, hv0, hvlt, hvv, hpt⟩ := hr hT true (by simpa [bit] using h1)
    refine ⟨v, true, hv0, hvlt, ?_, hpt⟩
    rw [hsum, hvv, h1]
    simp [bit]

/-! ## Completeness plumbing

The prover-side reading of a scale round: `evalScale_ok_iff` splits the 26-cell read,
the read survives table extension, and the advice computations read the threaded
cells and compute the gate's canonical row — `nAccWit` its register update, `bitWit`
its bit-step quintet from the gate model's `stepBit`. -/

open Std.Do in
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

/-- The register advice reads the threaded cells and computes the gate's
`nPrime` fold. -/
private theorem nAccWit_ok [Field F] [DecidableEq F] {env : Assignments F}
    {nPrev : FVar F} {bs : Vector (FVar F) 5} {nv b0 b1 b2 b3 b4 : F}
    (hnv : nPrev.eval env = .ok nv)
    (hb0 : bs[0].eval env = .ok b0) (hb1 : bs[1].eval env = .ok b1)
    (hb2 : bs[2].eval env = .ok b2) (hb3 : bs[3].eval env = .ok b3)
    (hb4 : bs[4].eval env = .ok b4) :
    nAccWit nPrev bs env
      = .ok (b4 + 2 * (b3 + 2 * (b2 + 2 * (b1 + 2 * (b0 + 2 * nv))))) := by
  simp [nAccWit, AsProver.readCVar, hnv, hb0, hb1, hb2, hb3, hb4,
    Bind.bind, ReaderT.bind, Except.bind, Pure.pure, ReaderT.pure, Except.pure]

/-- The bit-step advice reads the threaded cells and computes the gate model's
`stepBit` quintet. -/
private theorem bitWit_ok [Field F] [DecidableEq F] {env : Assignments F}
    {t : AffinePoint (FVar F)} {b : FVar F} {acc : AffinePoint (FVar F)}
    {xb yb xi yi bv : F}
    (hxb : t.x.eval env = .ok xb) (hyb : t.y.eval env = .ok yb)
    (hxi : acc.x.eval env = .ok xi) (hyi : acc.y.eval env = .ok yi)
    (hb : b.eval env = .ok bv) :
    bitWit t b acc env
      = .ok ((Kimchi.Gate.VarBaseMul.stepBit bv xb yb xi yi).1,
        (Kimchi.Gate.VarBaseMul.stepBit bv xb yb xi yi).1
          * (Kimchi.Gate.VarBaseMul.stepBit bv xb yb xi yi).1,
        2 * yi / (2 * xi + xb - (Kimchi.Gate.VarBaseMul.stepBit bv xb yb xi yi).1
          * (Kimchi.Gate.VarBaseMul.stepBit bv xb yb xi yi).1)
          - (Kimchi.Gate.VarBaseMul.stepBit bv xb yb xi yi).1,
        (Kimchi.Gate.VarBaseMul.stepBit bv xb yb xi yi).2.1,
        (Kimchi.Gate.VarBaseMul.stepBit bv xb yb xi yi).2.2) := by
  simp [bitWit, AsProver.readCVar, hxb, hyb, hxi, hyi, hb,
    Bind.bind, ReaderT.bind, Except.bind, Pure.pure, ReaderT.pure, Except.pure]

open Std.Do in
open Kimchi.Gate.VarBaseMul (build_fields build_nPrime
  build_step0 build_step1 build_step2 build_step3 build_step4) in
/-- **One round is the gate's canonical row.** On readable base, accumulator and
register cells and five readable bits, the honest round accepts and its collected
`ScaleRound` reads as `build` at exactly those values — the returned accumulator and
register being that row's `x5`/`y5`/`nPrime`. Stated over the gate model's row rather
than any particular walk, so the caller's loop supplies only the reads and gets the
row back; registered, so `mvcgen` applies it once per iteration. -/
@[spec] theorem scaleRound_complete_spec [Field F] [DecidableEq F]
    (base : AffinePoint (FVar F)) (st : AffinePoint (FVar F) × FVar F)
    (bs : Vector (FVar F) 5)
    (Q : PostCond (ScaleRound F × (AffinePoint (FVar F) × FVar F))
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (base.x.eval env).isOk ∧ (base.y.eval env).isOk ∧
          (st.1.x.eval env).isOk ∧ (st.1.y.eval env).isOk ∧ (st.2.eval env).isOk ∧
          ∀ (j : ℕ) (hj : j < 5), ((bs[j]'hj).eval env).isOk)
        (fun env r env' => ∀ xT yT x0 y0 nv b0 b1 b2 b3 b4,
          base.x.eval env = .ok xT → base.y.eval env = .ok yT →
          st.1.x.eval env = .ok x0 → st.1.y.eval env = .ok y0 →
          st.2.eval env = .ok nv →
          bs[0].eval env = .ok b0 → bs[1].eval env = .ok b1 →
          bs[2].eval env = .ok b2 → bs[3].eval env = .ok b3 →
          bs[4].eval env = .ok b4 →
          ScaleRound.eval env' r.1
              = .ok (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4)
            ∧ r.2.1.x.eval env'
                = .ok (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).x5
            ∧ r.2.1.y.eval env'
                = .ok (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).y5
            ∧ r.2.2.eval env'
                = .ok (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).nPrime)
        Q⦄
    (scaleRound (c := KimchiProverC F) base st bs)
    ⦃Q⦄ := by
  simp only [scaleRound]
  mvcgen
  rename_i st₀ hpre
  obtain ⟨⟨hbxk, hbyk, haxk, hayk, hank, hbk⟩, hk⟩ := hpre
  obtain ⟨xT, hxT⟩ := CVar.evalOk hbxk
  obtain ⟨yT, hyT⟩ := CVar.evalOk hbyk
  obtain ⟨x0, hx0⟩ := CVar.evalOk haxk
  obtain ⟨y0, hy0⟩ := CVar.evalOk hayk
  obtain ⟨nv, hnv⟩ := CVar.evalOk hank
  obtain ⟨b0, hb0⟩ := CVar.evalOk (hbk 0 (by omega))
  obtain ⟨b1, hb1⟩ := CVar.evalOk (hbk 1 (by omega))
  obtain ⟨b2, hb2⟩ := CVar.evalOk (hbk 2 (by omega))
  obtain ⟨b3, hb3⟩ := CVar.evalOk (hbk 3 (by omega))
  obtain ⟨b4, hb4⟩ := CVar.evalOk (hbk 4 (by omega))
  -- the register advice computes the row's `nPrime`
  have hnOk : nAccWit st.2 bs st₀.env
      = .ok (Kimchi.Gate.VarBaseMul.build xT yT x0 y0 nv b0 b1 b2 b3 b4).nPrime := by
    rw [nAccWit_ok hnv hb0 hb1 hb2 hb3 hb4, build_nPrime]
  refine ⟨by rw [hnOk]; rfl, fun nAcc st₁ hgN hle₁ => ?_⟩
  have hnA := (hgN _ hnOk)
  mvcgen
  -- the five bit steps, each reading the previous accumulator
  have hw0Ok := bitWit_ok (CVar.eval_le hle₁ hxT) (CVar.eval_le hle₁ hyT)
    (CVar.eval_le hle₁ hx0) (CVar.eval_le hle₁ hy0) (CVar.eval_le hle₁ hb0)
  refine ⟨by rw [hw0Ok]; rfl, fun w0 st₂ hg0 hle₂ => ?_⟩
  obtain ⟨hs0', -, -, hx1', hy1'⟩ := hg0 _ hw0Ok
  obtain ⟨es0, ex0, ey0⟩ := build_step0 xT yT x0 y0 nv b0 b1 b2 b3 b4
  obtain ⟨-, -, hfx0, hfy0, -, hfb0, hfb1, hfb2, hfb3, hfb4⟩ :=
    build_fields xT yT x0 y0 nv b0 b1 b2 b3 b4
  rw [← es0] at hs0'
  rw [← ex0] at hx1'
  rw [← ey0] at hy1'
  have hs0 := hs0'
  have hx1 := hx1'
  have hy1 := hy1'
  mvcgen
  have hw1Ok := bitWit_ok (acc := ⟨w0.2.2.2.1, w0.2.2.2.2⟩)
    (CVar.eval_le (hle₁.trans hle₂) hxT) (CVar.eval_le (hle₁.trans hle₂) hyT)
    hx1 hy1 (CVar.eval_le (hle₁.trans hle₂) hb1)
  refine ⟨by rw [hw1Ok]; rfl, fun w1 st₃ hg1 hle₃ => ?_⟩
  obtain ⟨hs1', -, -, hx2', hy2'⟩ := hg1 _ hw1Ok
  obtain ⟨es1, ex1, ey1⟩ := build_step1 xT yT x0 y0 nv b0 b1 b2 b3 b4
  rw [← es1] at hs1'
  rw [← ex1] at hx2'
  rw [← ey1] at hy2'
  have hs1 := hs1'
  have hx2 := hx2'
  have hy2 := hy2'
  mvcgen
  have hw2Ok := bitWit_ok (acc := ⟨w1.2.2.2.1, w1.2.2.2.2⟩)
    (CVar.eval_le ((hle₁.trans hle₂).trans hle₃) hxT)
    (CVar.eval_le ((hle₁.trans hle₂).trans hle₃) hyT) hx2 hy2
    (CVar.eval_le ((hle₁.trans hle₂).trans hle₃) hb2)
  refine ⟨by rw [hw2Ok]; rfl, fun w2 st₄ hg2 hle₄ => ?_⟩
  obtain ⟨hs2', -, -, hx3', hy3'⟩ := hg2 _ hw2Ok
  obtain ⟨es2, ex2, ey2⟩ := build_step2 xT yT x0 y0 nv b0 b1 b2 b3 b4
  rw [← es2] at hs2'
  rw [← ex2] at hx3'
  rw [← ey2] at hy3'
  have hs2 := hs2'
  have hx3 := hx3'
  have hy3 := hy3'
  mvcgen
  have hw3Ok := bitWit_ok (acc := ⟨w2.2.2.2.1, w2.2.2.2.2⟩)
    (CVar.eval_le (((hle₁.trans hle₂).trans hle₃).trans hle₄) hxT)
    (CVar.eval_le (((hle₁.trans hle₂).trans hle₃).trans hle₄) hyT) hx3 hy3
    (CVar.eval_le (((hle₁.trans hle₂).trans hle₃).trans hle₄) hb3)
  refine ⟨by rw [hw3Ok]; rfl, fun w3 st₅ hg3 hle₅ => ?_⟩
  obtain ⟨hs3', -, -, hx4', hy4'⟩ := hg3 _ hw3Ok
  obtain ⟨es3, ex3, ey3⟩ := build_step3 xT yT x0 y0 nv b0 b1 b2 b3 b4
  rw [← es3] at hs3'
  rw [← ex3] at hx4'
  rw [← ey3] at hy4'
  have hs3 := hs3'
  have hx4 := hx4'
  have hy4 := hy4'
  mvcgen
  have hw4Ok := bitWit_ok (acc := ⟨w3.2.2.2.1, w3.2.2.2.2⟩)
    (CVar.eval_le ((((hle₁.trans hle₂).trans hle₃).trans hle₄).trans hle₅) hxT)
    (CVar.eval_le ((((hle₁.trans hle₂).trans hle₃).trans hle₄).trans hle₅) hyT)
    hx4 hy4
    (CVar.eval_le ((((hle₁.trans hle₂).trans hle₃).trans hle₄).trans hle₅) hb4)
  refine ⟨by rw [hw4Ok]; rfl, fun w4 st₆ hg4 hle₆ => ?_⟩
  obtain ⟨hs4', -, -, hx5', hy5'⟩ := hg4 _ hw4Ok
  obtain ⟨es4, ex4, ey4⟩ := build_step4 xT yT x0 y0 nv b0 b1 b2 b3 b4
  rw [← es4] at hs4'
  rw [← ex4] at hx5'
  rw [← ey4] at hy5'
  have hs4 := hs4'
  have hx5 := hx5'
  have hy5 := hy5'
  mvcgen
  have hleA : st₀.env.Le st₆.env :=
    hle₁.trans ((((hle₂.trans hle₃).trans hle₄).trans hle₅).trans hle₆)
  refine hk _ st₆ ?_ hleA
  intro xT' yT' x0' y0' nv' b0' b1' b2' b3' b4'
    hxT' hyT' hx0' hy0' hnv' hb0' hb1' hb2' hb3' hb4'
  rw [hxT] at hxT'; injection hxT' with hxT'
  rw [hyT] at hyT'; injection hyT' with hyT'
  rw [hx0] at hx0'; injection hx0' with hx0'
  rw [hy0] at hy0'; injection hy0' with hy0'
  rw [hnv] at hnv'; injection hnv' with hnv'
  rw [hb0] at hb0'; injection hb0' with hb0'
  rw [hb1] at hb1'; injection hb1' with hb1'
  rw [hb2] at hb2'; injection hb2' with hb2'
  rw [hb3] at hb3'; injection hb3' with hb3'
  rw [hb4] at hb4'; injection hb4' with hb4'
  subst hxT' hyT' hx0' hy0' hnv' hb0' hb1' hb2' hb3' hb4'
  refine ⟨evalScale_ok_iff.mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hx5, hy5,
    CVar.eval_le ((((hle₂.trans hle₃).trans hle₄).trans hle₅).trans hle₆) hnA⟩
  · exact CVar.eval_le hleA hxT
  · exact CVar.eval_le hleA hyT
  · rw [hfx0]; exact CVar.eval_le hleA hx0
  · rw [hfy0]; exact CVar.eval_le hleA hy0
  · exact CVar.eval_le (((hle₃.trans hle₄).trans hle₅).trans hle₆) hx1
  · exact CVar.eval_le (((hle₃.trans hle₄).trans hle₅).trans hle₆) hy1
  · exact CVar.eval_le ((hle₄.trans hle₅).trans hle₆) hx2
  · exact CVar.eval_le ((hle₄.trans hle₅).trans hle₆) hy2
  · exact CVar.eval_le (hle₅.trans hle₆) hx3
  · exact CVar.eval_le (hle₅.trans hle₆) hy3
  · exact CVar.eval_le hle₆ hx4
  · exact CVar.eval_le hle₆ hy4
  · exact hx5
  · exact hy5
  · exact CVar.eval_le hleA hnv
  · exact CVar.eval_le ((((hle₂.trans hle₃).trans hle₄).trans hle₅).trans hle₆) hnA
  · rw [hfb0]; exact CVar.eval_le hleA hb0
  · rw [hfb1]; exact CVar.eval_le hleA hb1
  · rw [hfb2]; exact CVar.eval_le hleA hb2
  · rw [hfb3]; exact CVar.eval_le hleA hb3
  · rw [hfb4]; exact CVar.eval_le hleA hb4
  · exact CVar.eval_le (((hle₃.trans hle₄).trans hle₅).trans hle₆) hs0
  · exact CVar.eval_le ((hle₄.trans hle₅).trans hle₆) hs1
  · exact CVar.eval_le (hle₅.trans hle₆) hs2
  · exact CVar.eval_le hle₆ hs3
  · exact hs4

open Kimchi.Gate.VarBaseMul (y_ne_zero_of_odd_order smul_ne_zero_of_lt) in
/-- The gadget is complete, generic over the curve dictionary: the honest prover run
accepts on a readable on-curve base and a readable in-range faithful scalar whose
`Type1` decode satisfies the ladder regime, and the returned point reads as the
defining equation's honest side — `[fromShifted t]·g` at the scalar's canonical
value. The returned bits read as the scalar's, LSB-first: `scaleFast2` pins the ones
above its width to zero, so its own completeness needs them named here.
The regime precondition is per-scalar, exactly the fact the soundness law
conditions on; at the deployed widths the subwrap arm discharges it for every chunk
count below full width, and at full width it is the `Type1` forbidden-band check's
contract. The loop invariant identifies the run with the honest walk `chainBuild`;
the per-round check is the produce chain's (`chain_complete`), the init is the
doubling `addFast` (`addFast_complete_spec`), and the register pin closes by the
fold identity (`chain_accN` through `bitsVal_testBit`). -/
theorem varBaseMul_complete_spec [Field F] [DecidableEq F] [ToNat F] (d : HasCurve F)
    (n chunks : ℕ) (hn : 5 * chunks ≤ n)
    (base' : AffinePoint (FVar F)) (scalar : Type1 (FVar F))
    (Q : PostCond (VarBaseMulResult n F)
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env =>
          (scalar.val.eval env).isOk ∧ (base'.x.eval env).isOk ∧
          (base'.y.eval env).isOk ∧
          (∀ v, scalar.val.eval env = .ok v →
            ToNat.toNat v < 2 ^ (5 * chunks) ∧ ((ToNat.toNat v : ℕ) : F) = v ∧
            d.LadderRegime (5 * chunks)
              (Type1.fromShifted (5 * chunks) ⟨(ToNat.toNat v : ℤ)⟩)) ∧
          (∀ x y, base'.x.eval env = .ok x → base'.y.eval env = .ok y →
            d.W.Nonsingular x y))
        (fun env r env' =>
          (∀ v, scalar.val.eval env = .ok v →
            ∀ (i : ℕ) (hi : i < n), (r.lsbBits[i]'hi).eval env'
              = .ok (if (ToNat.toNat v).testBit i then (1 : F) else 0)) ∧
          (∀ v xv yv, scalar.val.eval env = .ok v →
            base'.x.eval env = .ok xv → base'.y.eval env = .ok yv →
            ∀ hT : d.W.Nonsingular xv yv,
            ∃ xS yS, r.g.x.eval env' = .ok xS ∧ r.g.y.eval env' = .ok yS ∧
              ∃ hfin : d.W.Nonsingular xS yS,
                Point.some _ _ hfin
                  = Type1.fromShifted (5 * chunks) ⟨(ToNat.toNat v : ℤ)⟩
                      • Point.some _ _ hT))
        Q⦄
    (varBaseMul (c := KimchiProverC F) n chunks base' scalar)
    ⦃Q⦄ := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  simp only [varBaseMul, mapAccumM]
  mvcgen
  rename_i st₀ hpre
  obtain ⟨⟨hsok, hxok, hyok, hsc, hcurve⟩, hk⟩ := hpre
  obtain ⟨v, hv⟩ := CVar.evalOk hsok
  obtain ⟨xv, hxv⟩ := CVar.evalOk hxok
  obtain ⟨yv, hyv⟩ := CVar.evalOk hyok
  obtain ⟨hrange, hfaith, hregpre⟩ := hsc v hv
  have hT : d.W.Nonsingular xv yv := hcurve _ _ hxv hyv
  have hyne : yv ≠ 0 := y_ne_zero_of_odd_order d.W d.odd hT
  -- the sealed base
  refine ⟨⟨hxok, hyok⟩, fun base st₁ hseal hle₁ => ?_⟩
  obtain ⟨hsx, hsy⟩ := hseal xv yv hxv hyv
  mvcgen
  -- the scalar's bits, in one witness
  set nn := ToNat.toNat v with hndef
  have hwit : lsbBitsWit n scalar.val st₁.env
      = .ok (Vector.ofFn fun i => if nn.testBit i.1 then (1 : F) else 0) := by
    simp [lsbBitsWit, AsProver.readCVar, CVar.eval_le hle₁ hv,
      Bind.bind, ReaderT.bind, Except.bind, Pure.pure, ReaderT.pure, Except.pure]
    rw [hndef]
  refine ⟨by rw [hwit]; rfl, fun bits st₂ hgrant hle₂ => ?_⟩
  have hread := hgrant _ hwit
  mvcgen
  -- the doubled init `P₀ = [2]·T`
  have hsx₂ : base.x.eval st₂.env = .ok xv := CVar.eval_le hle₂ hsx
  have hsy₂ : base.y.eval st₂.env = .ok yv := CVar.eval_le hle₂ hsy
  refine AddFast.addFast_complete_spec .checkFinite d.W d.short d.two_ne base base _ _
    ⟨⟨by rw [hsx₂]; rfl, by rw [hsy₂]; rfl, by rw [hsx₂]; rfl, by rw [hsy₂]; rfl,
      fun x1 y1 x2 y2 he1 he2 he3 he4 => ?_⟩,
     fun p st₃ hp hle₃ => ?_⟩
  · rw [hsx₂] at he1; rw [hsy₂] at he2; rw [hsx₂] at he3; rw [hsy₂] at he4
    injection he1 with he1; injection he2 with he2
    injection he3 with he3; injection he4 with he4
    subst he1 he2 he3 he4
    refine ⟨hT.1, hT.1, hyne, fun _ => ?_⟩
    rintro ⟨-, hyeq⟩
    rw [show d.W.negY xv yv = -yv from by
      simp [WeierstrassCurve.Affine.negY, d.short.1, d.short.2.2.1]] at hyeq
    refine hyne ?_
    have h2y : (2 : F) * yv = 0 := by linear_combination hyeq
    exact (mul_eq_zero.mp h2y).resolve_left d.two_ne
  obtain ⟨x0v, y0v, hx0e, hy0e, -, hP0ns, hsum⟩ :=
    (hp xv yv xv yv hsx₂ hsy₂ hsx₂ hsy₂ hT hT).resolve_left (by
      rintro ⟨-, hzero⟩
      have h2P : (2 : ℤ) • Point.some _ _ hT = 0 := by rw [two_zsmul, hzero]
      have hlt : (2 : ℤ) < (d.W.order : ℤ) := by
        have h2le := d.prime.two_le
        have hne2 := d.odd
        have h3' : 3 ≤ d.W.order := by omega
        exact_mod_cast h3'
      exact smul_ne_zero_of_lt d.W (Point.some_ne_zero hT) (by norm_num) hlt h2P)
  have hP0eq : Point.some _ _ hP0ns = (2 : ℤ) • Point.some _ _ hT := by
    rw [← hsum]
    module
  -- the honest stream, its regime, and the produce chain's acceptance
  set bsF : ℕ → F := fun j => if nn.testBit (5 * chunks - 1 - j) then (1 : F) else 0
    with hbsF
  have hbsb : ∀ j, j < 5 * chunks → bsF j = 0 ∨ bsF j = 1 := by
    intro j _
    rw [hbsF]
    dsimp only
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  -- the walk's bits ARE the stream, so its run reads back as the stream
  have hrun : Kimchi.Gate.VarBaseMul.runBits
      (fun i => Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF i) chunks
      = (List.range (5 * chunks)).map bsF := by
    unfold Kimchi.Gate.VarBaseMul.runBits
    rw [List.flatMap_congr (fun i _ => by
      obtain ⟨-, -, hb0, hb1, hb2, hb3, hb4⟩ :=
        Kimchi.Gate.VarBaseMul.chainBuild_fields xv yv x0v y0v 0 bsF i
      rw [hb0, hb1, hb2, hb3, hb4]),
      Kimchi.Gate.VarBaseMul.flatMap_range_window]
  -- and the walk's ladder is the scalar's `Type1` unshift, by the sound side's decode
  have hladder : Kimchi.Gate.VarBaseMul.gateLadder
        (fun i => Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF i) (5 * chunks)
      = 2 * (nn : ℤ) + 2 ^ (5 * chunks) + 1 := by
    rw [Kimchi.Gate.VarBaseMul.gateLadder_eq_register,
      Kimchi.Gate.VarBaseMul.gateRegister_eq_bitsVal, hrun, hbsF,
      Kimchi.Gate.VarBaseMul.bitsVal_testBit nn (5 * chunks) hrange]
  simp only [HasCurve.LadderRegime, Type1.fromShifted] at hregpre
  have hregime' : 3 * 2 ^ (5 * chunks) ≤ d.W.order ∨
      (2 ^ (5 * chunks - 1) < d.W.order ∧ d.W.order < 2 ^ (5 * chunks) ∧
        d.W.order % 4 = 1 ∧
        Kimchi.Gate.VarBaseMul.gateLadder
            (fun i => Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF i)
            (5 * chunks)
          ∉ Kimchi.Gate.VarBaseMul.forbiddenValues d.W.order) := by
    rcases hregpre with h | ⟨h1, h2', h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2', h3, by rw [hladder]; exact h4⟩
  have hHolds : ∀ i, i < chunks →
      Kimchi.Gate.VarBaseMul.Holds
        (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF i) :=
    Kimchi.Gate.VarBaseMul.chain_complete d.W d.two_ne d.odd chunks hT bsF hbsb 0
      hP0ns hP0eq hregime'
  mvcgen
  case inv1 =>
    exact ⇓ p s' => ⌜st₃.env.Le s'.env ∧
      (p.2.fst.1.x.eval s'.env
          = .ok (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF
              p.1.prefix.length).x0 ∧
        p.2.fst.1.y.eval s'.env
          = .ok (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF
              p.1.prefix.length).y0 ∧
        p.2.fst.2.eval s'.env
          = .ok (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF
              p.1.prefix.length).n) ∧
      ∀ r ∈ p.2.snd, ∃ w, ScaleRound.eval s'.env r = .ok w ∧
        Kimchi.Gate.VarBaseMul.Holds w⌝
  case vc1.step =>
    rename_i pref cur suff hsplit b s' hinv
    obtain ⟨hLe, ⟨hxI₀, hyI₀, hnI₀⟩, hrounds⟩ := hinv
    -- name the walk index the loop cursor carries
    have hxI : b.fst.1.x.eval s'.env
        = .ok (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF pref.length).x0 := hxI₀
    have hyI : b.fst.1.y.eval s'.env
        = .ok (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF pref.length).y0 := hyI₀
    have hnI : b.fst.2.eval s'.env
        = .ok (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF pref.length).n := hnI₀
    have hkrows : pref.length < chunks := by
      have hlen := congrArg List.length hsplit
      simp only [List.length_map, List.length_range, List.length_append,
        List.length_cons] at hlen
      omega
    have hcur : cur = Vector.ofFn (fun j : Fin 5 =>
        ((bits.toList.take (5 * chunks)).reverse).getD (5 * pref.length + j.1)
          (.const 0)) := by
      have h1 : ((List.range chunks).map (fun i => Vector.ofFn (fun j : Fin 5 =>
          ((bits.toList.take (5 * chunks)).reverse).getD (5 * i + j.1)
            (.const 0))))[pref.length]'(by
            simp only [List.length_map, List.length_range]
            exact hkrows) = cur := by
        simp only [hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      rw [← h1, List.getElem_map, List.getElem_range]
    subst hcur
    -- the window's bits read as the honest stream
    have hbit : ∀ j, j < 5 →
        (((bits.toList.take (5 * chunks)).reverse).getD (5 * pref.length + j)
            (.const 0) : FVar F).eval s'.env
          = .ok (bsF (5 * pref.length + j)) := by
      intro j hj
      have hlen5 : (bits.toList.take (5 * chunks)).length = 5 * chunks := by
        simp only [List.length_take, Vector.length_toList]
        omega
      have hgd : ((bits.toList.take (5 * chunks)).reverse).getD
          (5 * pref.length + j) (.const 0)
          = bits[5 * chunks - 1 - (5 * pref.length + j)]'(by omega) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by rw [hlen5]; omega),
          hlen5, List.getElem?_take_of_lt (by omega),
          List.getElem?_eq_getElem (by simp only [Vector.length_toList]; omega)]
        simp [Vector.getElem_toList]
      rw [hgd]
      have hr := hread (5 * chunks - 1 - (5 * pref.length + j)) (by omega)
      simp only [Vector.getElem_ofFn] at hr
      rw [hbsF]
      exact CVar.eval_le (hle₃.trans hLe) hr
    have hcurj : ∀ (j : ℕ) (hj : j < 5),
        ((Vector.ofFn (fun j : Fin 5 =>
            ((bits.toList.take (5 * chunks)).reverse).getD (5 * pref.length + j.1)
              (.const 0)))[j]'hj).eval s'.env
          = .ok (bsF (5 * pref.length + j)) := by
      intro j hj
      simp only [Vector.getElem_ofFn]
      exact hbit j hj
    have hcurj0 : ((Vector.ofFn (fun j : Fin 5 =>
        ((bits.toList.take (5 * chunks)).reverse).getD (5 * pref.length + j.1)
          (.const 0)))[0]'(by omega)).eval s'.env
        = .ok (bsF (5 * pref.length)) := hcurj 0 (by omega)
    have hxT' : base.x.eval s'.env = .ok xv :=
      CVar.eval_le ((hle₂.trans hle₃).trans hLe) hsx
    have hyT' : base.y.eval s'.env = .ok yv :=
      CVar.eval_le ((hle₂.trans hle₃).trans hLe) hsy
    -- the round's own law does the rest
    refine ⟨⟨by rw [hxT']; rfl, by rw [hyT']; rfl, by rw [hxI]; rfl,
      by rw [hyI]; rfl, by rw [hnI]; rfl,
      fun j hj => by rw [hcurj j hj]; rfl⟩, fun r st₄ hpost hle₄ => ?_⟩
    obtain ⟨hrow, hx5, hy5, hn5⟩ := hpost xv yv _ _ _ _ _ _ _ _
      hxT' hyT' hxI hyI hnI hcurj0 (hcurj 1 (by omega))
      (hcurj 2 (by omega)) (hcurj 3 (by omega)) (hcurj 4 (by omega))
    rw [← Kimchi.Gate.VarBaseMul.chainBuild_eta xv yv x0v y0v 0 bsF pref.length] at hrow hx5 hy5 hn5
    -- restore the invariant at the extended prefix
    intro _
    refine ⟨hLe.trans hle₄, ⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [Kimchi.Gate.VarBaseMul.chainBuild_succ_x0]
      exact hx5
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [Kimchi.Gate.VarBaseMul.chainBuild_succ_y0]
      exact hy5
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [Kimchi.Gate.VarBaseMul.chainBuild_succ_n]
      exact hn5
    · intro r' hr'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with hr' | rfl
      · obtain ⟨w, hev, hHw⟩ := hrounds r' hr'
        exact ⟨w, evalScale_le hle₄ hev, hHw⟩
      · exact ⟨_, hrow, hHolds pref.length hkrows⟩
  case vc2.vc1.vc1.vc1.refine_2.pre =>
    refine ⟨Assignments.Le.refl st₃.env, ⟨hx0e, hy0e, rfl⟩, fun r hr => ?_⟩
    exact absurd hr List.not_mem_nil
  case vc3.vc1.vc1.vc1.refine_2.post.success =>
    rename_i finp s' hinv
    obtain ⟨hLe, ⟨hxP, hyP, hnP⟩, hrounds⟩ := hinv
    simp only [List.length_map, List.length_range] at hxP hyP hnP hrounds
    -- the register pin: the final register reads as the scalar
    have hreg : (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF chunks).n
        = v := by
      have hchain := Kimchi.Gate.VarBaseMul.chain_accN chunks
        (fun i => Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF i)
        hHolds (fun i _ => rfl)
      rw [Kimchi.Gate.VarBaseMul.accN_chainBuild,
        Kimchi.Gate.VarBaseMul.accN_chainBuild, hrun,
        show (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF 0).n = 0
          from rfl, mul_zero, zero_add,
        Kimchi.Gate.VarBaseMul.bitsRegister_eq_cast _ (fun x hx => by
          obtain ⟨j, hjmem, rfl⟩ := List.mem_map.mp hx
          exact hbsb j (List.mem_range.mp hjmem)),
        hbsF, Kimchi.Gate.VarBaseMul.bitsVal_testBit nn (5 * chunks) hrange]
        at hchain
      rw [hchain]
      push_cast
      exact hfaith
    have hsv' : scalar.val.eval s'.env = .ok v :=
      CVar.eval_le ((hle₁.trans (hle₂.trans hle₃)).trans hLe) hv
    -- the constraint: every collected round's read row holds
    refine addConstraint_complete_spec (c := KimchiConstraint F)
      (KimchiSystem.varBaseMul finp.snd) _ s' ⟨?_, fun u st₄ _ hle₄ => ?_⟩
    · show KimchiConstraint.check (.varBaseMul finp.snd) s'.env = true
      simp only [KimchiConstraint.check]
      rw [List.all_eq_true]
      intro r hr
      obtain ⟨w, hev, hHw⟩ := hrounds r hr
      rw [hev]
      exact (Kimchi.Gate.VarBaseMul.ok_iff w).mpr hHw
    mvcgen
    -- the pin
    refine ⟨⟨by rw [CVar.eval_le hle₄ hnP]; rfl, by rw [CVar.eval_le hle₄ hsv']; rfl,
      fun rv sv hrv hsv => ?_⟩, fun u' st₅ hle₅ => ?_⟩
    · rw [CVar.eval_le hle₄ hnP] at hrv
      injection hrv with hrv
      rw [CVar.eval_le hle₄ hsv'] at hsv
      injection hsv with hsv
      subst hrv hsv
      exact hreg
    simp only [wp, PredTrans.apply, prove]
    intro hf
    refine hk ⟨finp.fst.1, bits⟩ ⟨st₅.nv, st₅.env, hf⟩
      (fun v' hv' i hi => ?_) (fun v' xv' yv' hv' hxv' hyv' hT' => ?_)
      ((hle₁.trans (hle₂.trans hle₃)).trans (hLe.trans (hle₄.trans hle₅)))
    · -- the scalar's bits: the honest witness's reads, transported to the final table
      rw [hv] at hv'
      injection hv' with hv'
      subst hv'
      have hr := hread i hi
      simp only [Vector.getElem_ofFn] at hr
      exact CVar.eval_le (hle₃.trans (hLe.trans (hle₄.trans hle₅))) hr
    rw [hv] at hv'
    injection hv' with hv'
    rw [hxv] at hxv'
    injection hxv' with hxv'
    rw [hyv] at hyv'
    injection hyv' with hyv'
    subst hv' hxv' hyv'
    -- the point chain: `varBaseMul_off` at the honest walk
    obtain ⟨hfin', hpt, -⟩ := Kimchi.Gate.VarBaseMul.varBaseMul_off d.W chunks
      (fun i => Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF i)
      (Point.some _ _ hT) (2 * (nn : ℤ) + 2 ^ (5 * chunks) + 1)
      (Point.some_ne_zero hT) hHolds hT rfl
      (fun i _ => by
        obtain ⟨hx1, hy1, -, -, -, -, -⟩ :=
          Kimchi.Gate.VarBaseMul.chainBuild_fields xv yv x0v y0v 0 bsF i
        obtain ⟨hx0', hy0', -, -, -, -, -⟩ :=
          Kimchi.Gate.VarBaseMul.chainBuild_fields xv yv x0v y0v 0 bsF 0
        rw [hx1, hy1, hx0', hy0']
        exact ⟨rfl, rfl⟩)
      (fun i _ => ⟨rfl, rfl⟩) hP0ns hP0eq d.two_ne d.odd
      hladder.symm hregpre
    have hax := Kimchi.Gate.VarBaseMul.accX_chainBuild xv yv x0v y0v 0 bsF chunks
    have hay := Kimchi.Gate.VarBaseMul.accY_chainBuild xv yv x0v y0v 0 bsF chunks
    have hfin : d.W.Nonsingular
        (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF chunks).x0
        (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF chunks).y0 := by
      rw [← hax, ← hay]
      exact hfin'
    exact ⟨(Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF chunks).x0,
      (Kimchi.Gate.VarBaseMul.chainBuild xv yv x0v y0v 0 bsF chunks).y0,
      CVar.eval_le (hle₄.trans hle₅) hxP, CVar.eval_le (hle₄.trans hle₅) hyP,
      hfin,
      (Kimchi.Gate.EndoMul.some_congr d.W hfin hfin' hax.symm hay.symm).trans hpt⟩
  case vc4.vc1.vc1.vc1.refine_2.post.except =>
    exact ExceptConds.entails_false

/-- `scaleFast1` is complete — the honest side of the defining equation
`scaleFast1 g a ~ scalarMul (fromShifted a) g`: on the same readable, in-range,
faithful, regime-satisfying scalar and readable on-curve base, the honest run
accepts and the returned point is `[fromShifted t]·g` at the scalar's canonical
value. `varBaseMul_complete_spec`'s point promise at the result, the bits dropped. -/
theorem scaleFast1_complete_spec [Field F] [DecidableEq F] [ToNat F] (d : HasCurve F)
    (n chunks : ℕ) (hn : 5 * chunks ≤ n)
    (p : AffinePoint (FVar F)) (t : Type1 (FVar F))
    (Q : PostCond (AffinePoint (FVar F))
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env =>
          (t.val.eval env).isOk ∧ (p.x.eval env).isOk ∧ (p.y.eval env).isOk ∧
          (∀ v, t.val.eval env = .ok v →
            ToNat.toNat v < 2 ^ (5 * chunks) ∧ ((ToNat.toNat v : ℕ) : F) = v ∧
            d.LadderRegime (5 * chunks)
              (Type1.fromShifted (5 * chunks) ⟨(ToNat.toNat v : ℤ)⟩)) ∧
          (∀ x y, p.x.eval env = .ok x → p.y.eval env = .ok y →
            d.W.Nonsingular x y))
        (fun env r env' => ∀ v xv yv, t.val.eval env = .ok v →
          p.x.eval env = .ok xv → p.y.eval env = .ok yv →
          ∀ hT : d.W.Nonsingular xv yv,
          ∃ xS yS, r.x.eval env' = .ok xS ∧ r.y.eval env' = .ok yS ∧
            ∃ hfin : d.W.Nonsingular xS yS,
              Point.some _ _ hfin
                = Type1.fromShifted (5 * chunks) ⟨(ToNat.toNat v : ℤ)⟩
                    • Point.some _ _ hT)
        Q⦄
    (scaleFast1 (c := KimchiProverC F) n chunks p t)
    ⦃Q⦄ := by
  simp only [scaleFast1]
  mvcgen [varBaseMul_complete_spec]
  rename_i st hpre
  refine ⟨hpre.1, fun r st' hrbits hrpt hle => ?_⟩
  mvcgen
  exact hpre.2 r.g st' hrpt hle

/-- A bit reading survives table extension. -/
private theorem readsBit_le [Field F] [DecidableEq F] {x : CVar F}
    {env env' : Assignments F} (hle : env.Le env') (h : ReadsBit x env) :
    ReadsBit x env' := by
  obtain ⟨b, hb⟩ := h.exists_bit
  refine ⟨by rw [CVar.eval_le hle hb]; rfl, fun w hw => ?_⟩
  rw [CVar.eval_le hle hb] at hw
  injection hw with hw
  subst hw
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The ladder's granted bits above the half's width read zero: `testBit` vanishes
above a value's width. -/
private theorem dropped_bits_zero [Field F] [DecidableEq F] {env : Assignments F}
    {n sDiv2Bits : ℕ} {bits : Vector (FVar F) n} {x : ℕ} (hx : x < 2 ^ sDiv2Bits)
    (hbits : ∀ (i : ℕ) (hi : i < n),
      (bits[i]'hi).eval env = .ok (if x.testBit i then (1 : F) else 0)) :
    ∀ b ∈ bits.toList.drop sDiv2Bits, b.eval env = .ok 0 := by
  intro bpin hbpin
  obtain ⟨k, hk', hEq⟩ := List.mem_iff_getElem.mp hbpin
  have hkn : sDiv2Bits + k < n := by
    have hlen : (bits.toList.drop sDiv2Bits).length = n - sDiv2Bits := by
      simp [List.length_drop]
    omega
  rw [← hEq, List.getElem_drop, Vector.getElem_toList]
  have hbfalse : x.testBit (sDiv2Bits + k) = false := by
    apply Nat.testBit_lt_two_pow
    calc x < 2 ^ sDiv2Bits := hx
      _ ≤ 2 ^ (sDiv2Bits + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hbits (sDiv2Bits + k) hkn, hbfalse]
  rfl

/-- The regime keeps the honest decode off the base: `fromShifted t ≢ 1 (mod order)`
— subwrap by size (the window sits strictly inside `(0, order)`), one-wrap because
`1` is a forbidden residue. What makes `scaleFast2`'s parity correction — the
incomplete subtraction of the base — well-defined on the honest run. -/
private theorem regime_off_base [Field F] [DecidableEq F] (d : HasCurve F)
    {L : ℕ} {t : ℤ} (ht0 : 0 ≤ t) (htlt : t < 2 ^ L)
    (hreg : d.LadderRegime L (Type1.fromShifted L ⟨t⟩)) :
    ¬ ((d.W.order : ℤ) ∣ (2 * t + 2 ^ L)) := by
  intro hdvd
  rcases hreg with hsub | ⟨-, -, -, hnf⟩
  · have hpos : (0 : ℤ) < 2 ^ L := by positivity
    have hord : (3 : ℤ) * 2 ^ L ≤ (d.W.order : ℤ) := by exact_mod_cast hsub
    have hle' := Int.le_of_dvd (by linarith) hdvd
    linarith
  · refine hnf (Kimchi.Gate.VarBaseMul.mem_forbiddenValues_of_dvd_sub_one
      d.W.order ?_)
    rw [show Type1.fromShifted L (⟨t⟩ : Type1 ℤ) - 1 = 2 * t + 2 ^ L from by
      simp [Type1.fromShifted]]
    exact hdvd

open Kimchi.Gate.VarBaseMul (y_ne_zero_of_odd_order zsmul_eq_zero_iff_order_dvd) in
/-- `scaleFast2` is complete — the honest side of the PS defining equation
`scaleFast2 g (sDiv2, sOdd) ~ [fromShifted (sDiv2, sOdd)]·g`: on a readable on-curve
base, a readable in-range faithful half whose `Type1` decode satisfies the inner
ladder's regime, and a parity flag reading a genuine bit, the honest run accepts and
the returned point is the `SplitField` decode's multiple. The regime also keeps the
ladder result off the base (`s ≢ 1`, subwrap by size, one-wrap because `1` is a
forbidden residue), which is what makes the parity correction's incomplete
subtraction well-defined — the completeness-side counterpart of the sound law's
`tne` self-enforcement. -/
theorem scaleFast2_complete_spec [Field F] [DecidableEq F] [ToNat F] (d : HasCurve F)
    (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n) (hd : sDiv2Bits ≤ 5 * chunks)
    (base : AffinePoint (FVar F)) (sDiv2 : FVar F) (sOdd : BoolVar F)
    (Q : PostCond (AffinePoint (FVar F))
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env =>
          (sDiv2.eval env).isOk ∧ ReadsBit (↑sOdd : CVar F) env ∧
          (base.x.eval env).isOk ∧ (base.y.eval env).isOk ∧
          (∀ v, sDiv2.eval env = .ok v →
            ToNat.toNat v < 2 ^ sDiv2Bits ∧ ((ToNat.toNat v : ℕ) : F) = v ∧
            d.LadderRegime (5 * chunks)
              (Type1.fromShifted (5 * chunks) ⟨(ToNat.toNat v : ℤ)⟩)) ∧
          (∀ x y, base.x.eval env = .ok x → base.y.eval env = .ok y →
            d.W.Nonsingular x y))
        (fun env r env' => ∀ v xv yv, sDiv2.eval env = .ok v →
          base.x.eval env = .ok xv → base.y.eval env = .ok yv →
          ∀ hT : d.W.Nonsingular xv yv,
          ∀ bb : Bool, (↑sOdd : CVar F).eval env = .ok (bit bb) →
          ∃ xS yS, r.x.eval env' = .ok xS ∧ r.y.eval env' = .ok yS ∧
            ∃ hres : d.W.Nonsingular xS yS,
              Point.some _ _ hres
                = SplitField.fromShifted (5 * chunks) ⟨(ToNat.toNat v : ℤ), bb⟩
                    • Point.some _ _ hT)
        Q⦄
    (scaleFast2 (c := KimchiProverC F) n chunks sDiv2Bits base sDiv2 sOdd)
    ⦃Q⦄ := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  simp only [scaleFast2]
  mvcgen [varBaseMul_complete_spec]
  rename_i st hpre
  obtain ⟨⟨hsok, hbit, hxok, hyok, hsc, hcurve⟩, hk⟩ := hpre
  obtain ⟨v, hv⟩ := CVar.evalOk hsok
  obtain ⟨xv, hxv⟩ := CVar.evalOk hxok
  obtain ⟨yv, hyv⟩ := CVar.evalOk hyok
  obtain ⟨hrange, hfaith, hreg⟩ := hsc v hv
  obtain ⟨bb, hb⟩ := hbit.exists_bit
  have hT : d.W.Nonsingular xv yv := hcurve _ _ hxv hyv
  have hvlt : (ToNat.toNat v : ℤ) < 2 ^ (5 * chunks) := by
    exact_mod_cast lt_of_lt_of_le hrange (Nat.pow_le_pow_right (by norm_num) hd)
  have hs1 : ¬ ((d.W.order : ℤ) ∣ (2 * (ToNat.toNat v : ℤ) + 2 ^ (5 * chunks))) :=
    regime_off_base d (Int.natCast_nonneg _) hvlt hreg
  -- the inner ladder
  refine ⟨⟨hsok, hxok, hyok, fun v' hv' => ?_, hcurve⟩,
    fun r st' hrbits hrpt hle => ?_⟩
  · rw [hv] at hv'
    injection hv' with hv'
    subst hv'
    exact ⟨lt_of_lt_of_le hrange (Nat.pow_le_pow_right (by norm_num) hd),
      hfaith, hreg⟩
  obtain ⟨xg, yg, hgx, hgy, hfin, hpt⟩ := hrpt v xv yv hv hxv hyv hT
  have hpins := dropped_bits_zero hrange (hrbits v hv)
  mvcgen
  case inv1 =>
    exact ⇓ p s' => ⌜st'.env.Le s'.env⌝
  case step =>
    rename_i pref cur suff hsplit u s' hinv
    have hcur : cur ∈ r.lsbBits.toList.drop sDiv2Bits := by
      rw [hsplit]
      exact List.mem_append_right _ List.mem_cons_self
    refine ⟨⟨by rw [CVar.eval_le hinv (hpins cur hcur)]; rfl, by rfl,
      fun xv' yv' hx' hy' => ?_⟩, fun u' s'' hle'' => ?_⟩
    · rw [CVar.eval_le hinv (hpins cur hcur)] at hx'
      injection hx' with hx'
      injection hy' with hy'
      rw [← hx', ← hy']
    · mvcgen
      exact hinv.trans hle''
  case pre => exact Assignments.Le.refl st'.env
  case post.success =>
    rename_i u st'' hle'
    -- the correction addition: `g − T` via the pure negation
    have hgx' := CVar.eval_le hle' hgx
    have hgy' := CVar.eval_le hle' hgy
    have hbx' : base.x.eval st''.env = .ok xv := CVar.eval_le (hle.trans hle') hxv
    have hny : (CVar.negate_ base.y).eval st''.env = .ok (-yv) := by
      rw [show (-yv) = (-1 : F) * yv from by ring]
      exact CVar.eval_scale_ (CVar.eval_le (hle.trans hle') hyv) (-1)
    have hgyne : yg ≠ 0 := y_ne_zero_of_odd_order d.W d.odd hfin
    obtain ⟨hnegT, hnegPt⟩ := AddFast.neg_point_reading d.W
      ⟨d.short.1, d.short.2.1, d.short.2.2.1⟩ hT
    have hsumne : Point.some _ _ hfin + Point.some _ _ hnegT ≠ 0 := by
      rw [hpt, hnegPt]
      intro h0
      apply hs1
      refine (zsmul_eq_zero_iff_order_dvd d.W (Point.some_ne_zero hT) _).1 ?_
      calc (2 * (ToNat.toNat v : ℤ) + 2 ^ (5 * chunks)) • Point.some _ _ hT
          = Type1.fromShifted (5 * chunks) ⟨(ToNat.toNat v : ℤ)⟩
              • Point.some _ _ hT + -Point.some _ _ hT := by
            simp only [Type1.fromShifted]
            module
        _ = 0 := h0
    mvcgen
    refine AddFast.addFast_complete_point_spec d.W d.short d.two_ne
      r.g ⟨base.x, CVar.negate_ base.y⟩ _ _
      ⟨⟨by rw [hgx']; rfl, by rw [hgy']; rfl, by rw [hbx']; rfl, by rw [hny]; rfl,
        fun x1 y1 x2 y2 he1 he2 he3 he4 => ?_⟩,
       fun q st₃ hq hle₃ => ?_⟩
    · rw [hgx'] at he1; rw [hgy'] at he2; rw [hbx'] at he3; rw [hny] at he4
      injection he1 with he1; injection he2 with he2
      injection he3 with he3; injection he4 with he4
      subst he1 he2 he3 he4
      exact ⟨hfin, hnegT, hgyne, hsumne⟩
    obtain ⟨xq, yq, hqx, hqy, hqns, hqsum⟩ :=
      hq xg yg xv (-yv) hgx' hgy' hbx' hny hfin hnegT
    have hqpt : (Point.some _ _ hqns : d.W.Point)
        = (2 * (ToNat.toNat v : ℤ) + 2 ^ (5 * chunks)) • Point.some _ _ hT := by
      rw [← hqsum, hpt, hnegPt]
      simp only [Type1.fromShifted]
      module
    -- the point conditional selects coordinatewise, `y` before `x`
    mvcgen
    refine ⟨⟨readsBit_le ((hle.trans hle').trans hle₃) hbit,
      by rw [CVar.eval_le hle₃ hgy']; rfl, by rw [hqy]; rfl⟩,
      fun ysel sty hyg hley => ?_⟩
    have hyv' := hyg bb yg yq
      (CVar.eval_le ((hle.trans hle').trans hle₃) hb)
      (CVar.eval_le hle₃ hgy') hqy
    mvcgen
    refine ⟨⟨readsBit_le (((hle.trans hle').trans hle₃).trans hley) hbit,
      by rw [CVar.eval_le (hle₃.trans hley) hgx']; rfl,
      by rw [CVar.eval_le hley hqx]; rfl⟩,
      fun xsel stx hxg hlex => ?_⟩
    have hxv' := hxg bb xg xq
      (CVar.eval_le (((hle.trans hle').trans hle₃).trans hley) hb)
      (CVar.eval_le (hle₃.trans hley) hgx') (CVar.eval_le hley hqx)
    mvcgen
    refine hk ⟨xsel, ysel⟩ stx
      (fun v' xv' yv' hv' hxv' hyv' hT' bb' hb' => ?_)
      ((((hle.trans hle').trans hle₃).trans hley).trans hlex)
    rw [hv] at hv'
    injection hv' with hv'
    rw [hxv] at hxv'
    injection hxv' with hxv'
    rw [hyv] at hyv'
    injection hyv' with hyv'
    subst hv' hxv' hyv'
    rw [hb] at hb'
    injection hb' with hb'
    obtain rfl := bit_inj one_ne_zero hb'
    cases bb
    · refine ⟨xq, yq, by simpa [selectPure] using hxv',
        by simpa [selectPure] using CVar.eval_le hlex hyv', hqns, ?_⟩
      rw [show SplitField.fromShifted (5 * chunks)
          (⟨(ToNat.toNat v : ℤ), false⟩ : SplitField ℤ Bool)
          = 2 * (ToNat.toNat v : ℤ) + 2 ^ (5 * chunks) from by
        simp [SplitField.fromShifted]]
      exact hqpt
    · refine ⟨xg, yg, by simpa [selectPure] using hxv',
        by simpa [selectPure] using CVar.eval_le hlex hyv', hfin, ?_⟩
      rw [show SplitField.fromShifted (5 * chunks)
          (⟨(ToNat.toNat v : ℤ), true⟩ : SplitField ℤ Bool)
          = Type1.fromShifted (5 * chunks) (⟨(ToNat.toNat v : ℤ)⟩ : Type1 ℤ) from by
        simp [SplitField.fromShifted, Type1.fromShifted]; ring]
      exact hpt
  case post.except =>
    exact ExceptConds.entails_false

end Snarky.Kimchi
