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
  let (rounds, fin) ← mapAccumM
    (fun (st : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 5) => do
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
      pure (({ acc0 := st.1, acc1 := a1, acc2 := a2, acc3 := a3, acc4 := a4,
               acc5 := a5,
               bit0 := bs[0], bit1 := bs[1], bit2 := bs[2], bit3 := bs[3],
               bit4 := bs[4],
               slope0 := w0.1, slope1 := w1.1, slope2 := w2.1, slope3 := w3.1,
               slope4 := w4.1,
               nPrev := st.2, nNext := nAcc, base } : ScaleRound F),
            (a5, nAcc)))
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
  (r.lsbBits.toList.drop sDiv2Bits).forM fun bit => assertEqual bit (.const 0)
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

/-- Flattening the 5-bit windows of a list of exactly `5·c` entries recovers it. -/
private theorem flatMap_window {α : Type} (dflt : α) :
    ∀ (c : ℕ) (l : List α), l.length = 5 * c →
      (List.range c).flatMap (fun i =>
        [l.getD (5 * i) dflt, l.getD (5 * i + 1) dflt, l.getD (5 * i + 2) dflt,
         l.getD (5 * i + 3) dflt, l.getD (5 * i + 4) dflt]) = l
  | 0, l, hl => by
    rw [show l = [] from List.eq_nil_of_length_eq_zero (by omega)]
    rfl
  | c + 1, a :: b :: d :: e :: f :: rest, hl => by
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    have hshift : ∀ i, i ∈ List.range c →
        [( a :: b :: d :: e :: f :: rest).getD (5 * (i + 1)) dflt,
         (a :: b :: d :: e :: f :: rest).getD (5 * (i + 1) + 1) dflt,
         (a :: b :: d :: e :: f :: rest).getD (5 * (i + 1) + 2) dflt,
         (a :: b :: d :: e :: f :: rest).getD (5 * (i + 1) + 3) dflt,
         (a :: b :: d :: e :: f :: rest).getD (5 * (i + 1) + 4) dflt]
          = [rest.getD (5 * i) dflt, rest.getD (5 * i + 1) dflt,
             rest.getD (5 * i + 2) dflt, rest.getD (5 * i + 3) dflt,
             rest.getD (5 * i + 4) dflt] := by
      intro i _
      have h5 : ∀ j, (a :: b :: d :: e :: f :: rest).getD (5 * (i + 1) + j) dflt
          = rest.getD (5 * i + j) dflt := by
        intro j
        rw [show 5 * (i + 1) + j = (5 * i + j) + 1 + 1 + 1 + 1 + 1 from by ring]
        simp
      rw [show (5 * (i + 1) : ℕ) = 5 * (i + 1) + 0 from rfl,
        h5 0, h5 1, h5 2, h5 3, h5 4,
        show (5 * i + 0 : ℕ) = 5 * i from rfl]
    rw [List.flatMap_congr hshift,
      flatMap_window dflt c rest (by simp at hl; omega)]
    simp [List.getD]

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
whenever the ladder's regime fact holds at the bits' Type1 decode
`2·(bits value) + 2^(5·chunks) + 1` — the result reads as exactly that multiple of
the base: `varBaseMul g (Type1 t) ~ [2·t + 2^bits + 1]·g`, the `fromShifted`
decode. The curve facts arrive bundled as the dictionary `d : HasCurve F`; the
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
                (2 * bitsVal bits + 2 ^ (5 * chunks) + 1),
              ∃ hfin : d.W.Nonsingular (r.g.x.val V) (r.g.y.val V),
                Point.some _ _ hfin
                  = (2 * bitsVal bits + 2 ^ (5 * chunks) + 1)
                      • Point.some _ _ hT) Q⦄
    (varBaseMul (c := KimchiConstraint F) n chunks base scalar)
    ⦃Q⦄ := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  simp only [varBaseMul, mapAccumM]
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
    obtain ⟨hfin, hpt⟩ := hpoint (by simpa using hregime)
    exact ⟨hfin, by rw [← hTeq]; simpa using hpt⟩

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
            (s : F) = Type1.fromShifted (5 * chunks) (t.val.val V) ∧
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
  unfold Type1.fromShifted
  push_cast
  ring

open Std.Do in
/-- Pinning a list of variables to the zero constant reads them all as zero —
`scaleFast2`'s high-bit pins, one `assertEqual` per variable. -/
private theorem forM_pinZero_spec [Field F] [DecidableEq F]
    (l : List (FVar F)) (Q : PostCond PUnit (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (_ : PUnit) => ∀ b ∈ l, b.val V = 0) Q⦄
    ((l.forM fun bit => assertEqual bit (.const 0)) :
      CircuitM F (KimchiConstraint F) PUnit)
    ⦃Q⦄ := by
  induction l generalizing Q with
  | nil =>
    mvcgen
    intro s hpre
    simp only [List.forM_eq_forM, List.forM_nil]
    mvcgen
    exact hpre ⟨⟩ _ (by simp)
  | cons b t ih =>
    mvcgen
    intro s hpre
    simp only [List.forM_eq_forM, List.forM_cons]
    mvcgen
    intro _ nv hpin
    exact ih _ _ fun _ nv2 hrest =>
      hpre ⟨⟩ _ fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · simpa using hpin
        · exact hrest x hx

open Kimchi.Gate.VarBaseMul (bitsRegister bitsVal bitsVal_lt bitsVal_drop_of_zeros
  bitsRegister_eq_cast y_ne_zero_of_odd_order) in
/-- `scaleFast2` is sound — the Type2 defining equation
`scaleFast2 g (sDiv2, sOdd) ~ [2·sDiv2 + sOdd + 2^(5·chunks)]·g`: the inner ladder
computes `[2·v + 2^(5·chunks) + 1]·g` at the register's decode `v`, the high-bit pins
force `v < 2^sDiv2Bits`, and the parity correction folds `sOdd` in by conditionally
subtracting the base. The parity's booleanity is the caller's promise (the
`select_spec` shape); `splitFieldVar` supplies it in `scaleFast2'`. -/
theorem scaleFast2_spec [Field F] [DecidableEq F] [ToNat F] (d : HasCurve F)
    (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n) (hd : sDiv2Bits ≤ 5 * chunks)
    (base : AffinePoint (FVar F)) (sDiv2 : FVar F) (sOdd : BoolVar F)
    (Q : PostCond (AffinePoint (FVar F)) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : AffinePoint (FVar F)) =>
        ∀ hT : d.W.Nonsingular (base.x.val V) (base.y.val V),
        ∀ bb : Bool, (↑sOdd : CVar F).val V = bit bb →
          ∃ v : ℤ, 0 ≤ v ∧ v < 2 ^ sDiv2Bits ∧ sDiv2.val V = ((v : ℤ) : F) ∧
            ∀ _ : d.LadderRegime (5 * chunks) (2 * v + 2 ^ (5 * chunks) + 1),
              ∃ hres : d.W.Nonsingular (r.x.val V) (r.y.val V),
                Point.some _ _ hres
                  = (2 * v + (if bb then 1 else 0) + 2 ^ (5 * chunks))
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
  refine forM_pinZero_spec (r.lsbBits.toList.drop sDiv2Bits) _ _ ?_
  intro _ nvp hzeros
  mvcgen
  refine AddFast.addFast_checkFinite_spec d.W d.short d.two_ne r.g
    ⟨base.x, CVar.negate_ base.y⟩ _ _ ?_
  intro q nvq hq
  mvcgen
  intro y _ hysel
  mvcgen
  intro x _ hxsel
  mvcgen
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
      rw [show (2 * bitsVal bl + (if false then (1:ℤ) else 0) + 2 ^ (5 * chunks))
          = 2 * bitsVal bl + 2 ^ (5 * chunks) from by norm_num]
      refine (Kimchi.Gate.EndoMul.some_congr d.W hres hqns ?_ ?_).trans hqpt
      · rw [hxv]; simp [selectPure]
      · rw [hyv]; simp [selectPure]
    · have hres : d.W.Nonsingular (x.val s.V) (y.val s.V) := by
        rw [hxv, hyv]
        simpa [selectPure] using hg
      refine ⟨hres, ?_⟩
      rw [show (2 * bitsVal bl + (if true then (1:ℤ) else 0) + 2 ^ (5 * chunks))
          = 2 * bitsVal bl + 2 ^ (5 * chunks) + 1 from by norm_num; ring]
      refine (Kimchi.Gate.EndoMul.some_congr d.W hres hg ?_ ?_).trans hgpt
      · rw [hxv]; simp [selectPure]
      · rw [hyv]; simp [selectPure]

open Kimchi.Gate.VarBaseMul (bitsRegister bitsVal) in
/-- `scaleFast2'` is sound — `scaleFast2' g s ~ [s + 2^(5·chunks)]·g`, `s` read
through its parity split: the split's recombination `s = 2·v + sOdd` composes with
`scaleFast2`'s Type2 decode. -/
theorem scaleFast2'_spec [Field F] [DecidableEq F] [ToNat F] (d : HasCurve F)
    (n chunks sDiv2Bits : ℕ) (hn : 5 * chunks ≤ n) (hd : sDiv2Bits ≤ 5 * chunks)
    (base : AffinePoint (FVar F)) (sc : FVar F)
    (Q : PostCond (AffinePoint (FVar F)) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : AffinePoint (FVar F)) =>
        ∀ hT : d.W.Nonsingular (base.x.val V) (base.y.val V),
          ∃ (v : ℤ) (bb : Bool), 0 ≤ v ∧ v < 2 ^ sDiv2Bits ∧
            sc.val V = 2 * ((v : ℤ) : F) + bit bb ∧
            ∀ _ : d.LadderRegime (5 * chunks) (2 * v + 2 ^ (5 * chunks) + 1),
              ∃ hres : d.W.Nonsingular (r.x.val V) (r.y.val V),
                Point.some _ _ hres
                  = (2 * v + (if bb then 1 else 0) + 2 ^ (5 * chunks))
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

end Snarky.Kimchi
