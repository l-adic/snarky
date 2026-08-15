import Snarky.Circuit.DSL.Field
import Kimchi.Gate.Semantics.EndoMul
import Kimchi.Gate.Semantics.VarBaseMul
import Pasta.Endo
import Snarky.Circuit.DSL.Assert
import Snarky.Circuit.DSL.Bits
import Snarky.Kimchi.Semantics
import Snarky.Kimchi.Circuit.Utils
import Snarky.Kimchi.Circuit.AddComplete

/-!
# The EndoMul gadget

Port of `Snarky.Circuit.Kimchi.EndoMul`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/EndoMul.purs): the
endomorphism-optimized scalar multiplication. `endoMul` witnesses the scalar's
`4·rounds` bits MSB-first in ONE bulk `exists` — four per GLV round, plain field
`0`/`1` values (the gate's own booleanity rows cover them) — builds the initial
accumulator `[2](g + φ(g))` from a sealed `β·x` and two `addFast`s, threads
`(acc, nAcc)` through `mapAccumM` with one eight-field witness per round, pins the
scalar register to the scalar, and emits the `endoMul` constraint.

Name map: PS `endo` becomes `endoMul`, the gate's own name — `endo` names the
coefficient family here (`endoBase`, `Pasta.pallasEndo`); the coefficient
parameter is `eb` after the PS binding. `endoInv` is a higher-level consumer
(cross-field scalar-multiplication witnesses over an on-curve checked point) and
is not ported, like `EndoScalar.expandToEndoScalar`.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS's type-level `SizedF k` sizing renders as the explicit `rounds` parameter with
  `4 · rounds` bits, and the bit reads go through `[ToNat F]`.
- PS batches the whole witness chain through `mkWitnessTable`/`computeEndoChain`
  (Montgomery-trick advice; its own comment: the emitted circuit is untouched).
  The port computes each round's witness sequentially from the threaded variables
  via the gate's own `Kimchi.Gate.EndoMul.build` — the same field values, and the
  same eight-variable allocation per round in the PS record's alphabetical order
  `(inv, nAccNext, r, s, s1, s3)`.
- PS reads the endo coefficient off the ambient `HasEndo` class; the deep embedding
  passes it as the `eb` parameter (the Poseidon parameter-data deviation).

The soundness law reads the emitted constraints through the semantic layer:
`EndoMul.endoMul_spec` and its deployed instantiations
`endoMul_spec_pallas`/`endoMul_spec_vesta` (`§ Soundness` below).
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

/-- The scalar's `4·rounds` bits MSB-first as field values, four per row (PS's
bulk bit witness: `toBits` reversed). -/
private def bitsWit [Field F] [ToNat F] (rounds : ℕ) (scalar : FVar F) :
    AsProver F (Vector (Vector F 4) rounds) := do
  let v ← AsProver.readCVar scalar
  let n := ToNat.toNat v
  pure (Vector.ofFn fun r => Vector.ofFn fun j =>
    if n.testBit (4 * rounds - 1 - (4 * r.1 + j.1)) then 1 else 0)

/-- One GLV round's witness: read the base, the threaded accumulator and register,
and the four window bits, and build the gate's canonical row
(`Kimchi.Gate.EndoMul.build` — two `stepWindow` double-adds, the scalar recoding,
the distinct-point inverse). Returned in the PS record's alphabetical allocation
order `(inv, nAccNext, r.x, r.y, s.x, s.y, s1, s3)`. -/
private def rowWit [Field F] [DecidableEq F] (eb : F) (t : AffinePoint (FVar F))
    (bs : Vector (FVar F) 4) (st : AffinePoint (FVar F) × FVar F) :
    AsProver F (F × F × F × F × F × F × F × F) := do
  let xt ← AsProver.readCVar t.x
  let yt ← AsProver.readCVar t.y
  let xp ← AsProver.readCVar st.1.x
  let yp ← AsProver.readCVar st.1.y
  let n ← AsProver.readCVar st.2
  let b1 ← AsProver.readCVar bs[0]
  let b2 ← AsProver.readCVar bs[1]
  let b3 ← AsProver.readCVar bs[2]
  let b4 ← AsProver.readCVar bs[3]
  let w := Kimchi.Gate.EndoMul.build eb xt yt xp yp n b1 b2 b3 b4
  pure (w.inv, w.nPrime, w.xR, w.yR, w.xS, w.yS, w.s1, w.s3)

/-- The endomorphism-optimized scalar multiplication (PS `endo`; OCaml
`Pickles.Step_main_inputs.Ops.endo`): witness the MSB-first bits, seal `β·x` and
build `acc = [2](g + φ(g))` with two `addFast`s, run the `rounds` window rounds
threading `(acc, nAcc)`, pin the scalar fold, emit one `endoMul` constraint, and
return the final accumulator. -/
def endoMul [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]
    (eb : F) (rounds : ℕ) (g : AffinePoint (FVar F)) (scalar : FVar F) :
    CircuitM F c (AffinePoint (FVar F)) := do
  let bits ← witness (val := Vector (Vector F 4) rounds) (bitsWit rounds scalar)
  let phix ← sealVar (CVar.scale_ eb g.x)
  let p1 ← addFast .checkFinite g ⟨phix, g.y⟩
  let p2 ← addFast .checkFinite p1.p p1.p
  let (state, fin) ← mapAccumM
    (fun (st : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 4) => do
      let w ← witness (val := F × F × F × F × F × F × F × F) (rowWit eb g bs st)
      let s : AffinePoint (FVar F) := ⟨w.2.2.2.2.1, w.2.2.2.2.2.1⟩
      pure (({ t := g, p := st.1, r := ⟨w.2.2.1, w.2.2.2.1⟩, s,
               s1 := w.2.2.2.2.2.2.1, s3 := w.2.2.2.2.2.2.2,
               nAcc := st.2, nAccNext := w.2.1,
               bit0 := bs[0], bit1 := bs[1], bit2 := bs[2], bit3 := bs[3],
               inv := w.1 } : EndoMulRound F),
            (s, w.2.1)))
    (p2.p, .const 0) bits.toList
  assertEqual fin.2 scalar
  addConstraint (KimchiSystem.endoMul { state, s := fin.1, nAcc := fin.2, endo := eb })
  pure fin.1

/-! ## Soundness

`endoMul_spec`: any satisfying valuation reads the returned point as `[s]·T` with
`(s : F) = EndoScalar.toField crumbs λ` over a valid crumb list whose reconstruction
is the scalar — the defining equation coupling this gadget to the EndoScalar decode,
one shared crumb list. The loop's invariant is structural only; the values arrive at
the constraint after the loop, where `Kimchi.Gate.EndoMul.endoMul_off` and
`chain_nAcc` consume the extracted run. The successor-chain constraint reading makes
the row threading definitional: a round's output cells and its successor's input
cells are the same variables. -/

open Std.Do WeierstrassCurve.Affine

namespace EndoMul

/-- The loop's structural view: the collected rounds are the chain-threaded records
over the traversed chunks — each round's `(p, nAcc)` are the previous round's output
variables, from `st` to `fin`, and every round shares the base `t`. Valuation-free:
the soundness invariant carries shape only; the values arrive with the constraint
after the loop. -/
private def Threaded (t : AffinePoint (FVar F)) :
    (AffinePoint (FVar F) × FVar F) → List (Vector (FVar F) 4) →
    List (EndoMulRound F) → (AffinePoint (FVar F) × FVar F) → Prop
  | st, [], rounds, fin => rounds = [] ∧ fin = st
  | st, bs :: rest, rounds, fin =>
    ∃ (w : FVar F × FVar F × FVar F × FVar F × FVar F × FVar F × FVar F × FVar F)
      (tail : List (EndoMulRound F)),
      rounds = ({ t, p := st.1, r := ⟨w.2.2.1, w.2.2.2.1⟩,
                  s := ⟨w.2.2.2.2.1, w.2.2.2.2.2.1⟩,
                  s1 := w.2.2.2.2.2.2.1, s3 := w.2.2.2.2.2.2.2,
                  nAcc := st.2, nAccNext := w.2.1,
                  bit0 := bs[0], bit1 := bs[1], bit2 := bs[2], bit3 := bs[3],
                  inv := w.1 } : EndoMulRound F) :: tail ∧
      Threaded t (⟨w.2.2.2.2.1, w.2.2.2.2.2.1⟩, w.2.1) rest tail fin

/-- One more chunk extends a threading at the tail. -/
private theorem Threaded.snoc {t : AffinePoint (FVar F)} :
    ∀ {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 4)}
      {rounds : List (EndoMulRound F)},
      Threaded t st pref rounds fin →
      ∀ (bs : Vector (FVar F) 4)
        (w : FVar F × FVar F × FVar F × FVar F × FVar F × FVar F × FVar F × FVar F),
      Threaded t st (pref ++ [bs])
        (rounds ++ [{ t, p := fin.1, r := ⟨w.2.2.1, w.2.2.2.1⟩,
                      s := ⟨w.2.2.2.2.1, w.2.2.2.2.2.1⟩,
                      s1 := w.2.2.2.2.2.2.1, s3 := w.2.2.2.2.2.2.2,
                      nAcc := fin.2, nAccNext := w.2.1,
                      bit0 := bs[0], bit1 := bs[1], bit2 := bs[2], bit3 := bs[3],
                      inv := w.1 }])
        (⟨w.2.2.2.2.1, w.2.2.2.2.2.1⟩, w.2.1)
  | st, fin, [], rounds, h, bs, w => by
    obtain ⟨hr, hfin⟩ := h
    subst hr hfin
    exact ⟨w, [], rfl, rfl, rfl⟩
  | st, fin, chunk :: rest, rounds, h, bs, w => by
    obtain ⟨w', tail, hr, hrest⟩ := h
    subst hr
    exact ⟨w', tail ++ [_], rfl, hrest.snoc bs w⟩

/-- An empty threading traversed no chunks: the final pair is the start. -/
private theorem Threaded.nil {t : AffinePoint (FVar F)} :
    ∀ {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 4)},
      Threaded t st pref [] fin → pref = [] ∧ fin = st
  | _, _, [], h => ⟨rfl, h.2⟩
  | _, _, _ :: _, h => by
    obtain ⟨w, tail, heq, -⟩ := h
    exact nomatch heq

/-- The structural facts of a nonempty threading: the round count, the shared base
variables, round `0`'s seed wiring, the shared accumulator/register variables between
adjacent rounds, and the final pair's wiring — everything the successor-chain reading
and `endoMul_off` consume, extracted without touching a valuation. -/
private theorem threaded_chain {t : AffinePoint (FVar F)} :
    ∀ {pref : List (Vector (FVar F) 4)} {st fin : AffinePoint (FVar F) × FVar F}
      {r₀ : EndoMulRound F} {rs : List (EndoMulRound F)},
      Threaded t st pref (r₀ :: rs) fin →
      (r₀ :: rs).length = pref.length ∧
      (∀ i (hi : i < (r₀ :: rs).length), (r₀ :: rs)[i].t = t) ∧
      (r₀.p = st.1 ∧ r₀.nAcc = st.2) ∧
      (∀ i (hi : i + 1 < (r₀ :: rs).length),
        (r₀ :: rs)[i + 1].p = (r₀ :: rs)[i].s ∧
        (r₀ :: rs)[i + 1].nAcc = (r₀ :: rs)[i].nAccNext) ∧
      (fin.1 = (r₀ :: rs)[rs.length].s ∧ fin.2 = (r₀ :: rs)[rs.length].nAccNext)
  | x :: rest, st, fin, r₀, rs, h => by
    obtain ⟨w, tail, heq, hrest⟩ := h
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

/-- The successor-chain reading, indexed: round `i`'s gate witness reads its output
cells from round `i + 1`'s `p`/`nAcc` values. -/
private theorem chainHolds_succ [Field F] [DecidableEq F] {V : Valuation F} {eb : F}
    {fv : F × F × F} :
    ∀ {rounds : List (EndoMulRound F)}, EndoMul.chainHolds V eb fv rounds →
      ∀ i (hi : i + 1 < rounds.length),
        Kimchi.Gate.EndoMul.Holds eb (EndoMulRound.readWith V rounds[i]
          (rounds[i + 1].p.x.val V) (rounds[i + 1].p.y.val V)
          (rounds[i + 1].nAcc.val V))
  | [], _, i, hi => by simp at hi
  | [_], _, i, hi => by simp at hi
  | _ :: _ :: _, h, 0, _ => h.1
  | _ :: r' :: rest, h, i + 1, hi => by
    simpa only [List.getElem_cons_succ] using
      chainHolds_succ h.2 i (by simpa using hi)

/-- The successor-chain reading, last round: its gate witness reads its output cells
from the finals `fv`. -/
private theorem chainHolds_last [Field F] [DecidableEq F] {V : Valuation F} {eb : F}
    {fv : F × F × F} :
    ∀ {rounds : List (EndoMulRound F)}, EndoMul.chainHolds V eb fv rounds →
      ∀ (hne : rounds ≠ []),
        Kimchi.Gate.EndoMul.Holds eb
          (EndoMulRound.readWith V (rounds.getLast hne) fv.1 fv.2.1 fv.2.2)
  | [], _, hne => absurd rfl hne
  | [_], h, _ => h
  | _ :: r' :: rest, h, _ => chainHolds_last h.2 (List.cons_ne_nil r' rest)

open Kimchi.Gate.EndoMul in
open Kimchi.Gate.VarBaseMul (y_ne_zero_of_odd_order) in
/-- A satisfied threading from the init pair computes the scalar multiplication: the
structural wiring (`threaded_chain`) turns the successor-chain reading into
`endoMul_off`'s indexed run — the register chain (`chain_nAcc`) reads the final
register as the crumb reconstruction, the point chain the final accumulator as
`[s]·T`. The gadget layer contributes wiring only; the mathematics is the
gate-semantics theorems'. The empty run returns the init: `[2 + 2λ]·T`, the
`toField` of no crumbs. -/
private theorem threaded_sound [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F)
    [Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)] [Fact (Nat.Prime W.order)]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hodd : W.order ≠ 2) (eb : F) (lam : ℤ)
    (V : Valuation F) {t P0 : AffinePoint (FVar F)}
    {pref : List (Vector (FVar F) 4)} {rounds : List (EndoMulRound F)}
    {fin : AffinePoint (FVar F) × FVar F}
    (hbits : 4 * pref.length ≤ 244)
    (hthr : Threaded t (P0, .const 0) pref rounds fin)
    (hpay : EndoMul.chainHolds V eb
      (fin.1.x.val V, fin.1.y.val V, fin.2.val V) rounds)
    (hT : W.Nonsingular (t.x.val V) (t.y.val V))
    (hφT : W.Nonsingular (eb * t.x.val V) (t.y.val V))
    (hoff : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → |a| < 2 ^ 126 → |b| < 2 ^ 126 →
      a • Point.some _ _ hT + b • Point.some _ _ hφT ≠ Point.some _ _ hT ∧
      a • Point.some _ _ hT + b • Point.some _ _ hφT ≠ -Point.some _ _ hT ∧
      a • Point.some _ _ hT + b • Point.some _ _ hφT ≠ Point.some _ _ hφT ∧
      a • Point.some _ _ hT + b • Point.some _ _ hφT ≠ -Point.some _ _ hφT)
    (heig : Point.some _ _ hφT = lam • Point.some _ _ hT)
    (hP0ns : W.Nonsingular (P0.x.val V) (P0.y.val V))
    (hP0 : Point.some _ _ hP0ns
      = (2 : ℤ) • Point.some _ _ hT + (2 : ℤ) • Point.some _ _ hφT) :
    ∃ crumbs : List F,
      (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
      crumbs.length = 2 * pref.length ∧
      fin.2.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs ∧
      ∃ (hfin : W.Nonsingular (fin.1.x.val V) (fin.1.y.val V)) (s : ℤ),
        Point.some _ _ hfin = s • Point.some _ _ hT ∧
        (s : F) = Kimchi.Gate.EndoScalar.toField crumbs (lam : F) := by
  match hround : rounds, hthr with
  | [], hthr' =>
    obtain ⟨rfl, rfl⟩ := Threaded.nil hthr'
    refine ⟨[], by simp, by simp, ?_, hP0ns, 2 + 2 * lam, ?_, ?_⟩
    · simp [Kimchi.Gate.EndoScalar.nReconstruct, CVar.val]
    · rw [hP0, heig]; module
    · push_cast
      simp [Kimchi.Gate.EndoScalar.toField, Kimchi.Gate.EndoScalar.decomposeA,
        Kimchi.Gate.EndoScalar.decomposeB]
      ring
  | r₀ :: rs, hthr' =>
    subst hround
    obtain ⟨hlen, hbase, ⟨hp0, hn0⟩, hstep, hf1, hf2⟩ := threaded_chain hthr'
    set R : ℕ → EndoMulRound F := fun i => (r₀ :: rs).getD i r₀ with hR
    have hRi : ∀ i (hi : i ≤ rs.length), R i = (r₀ :: rs)[i]'(by simp; omega) := by
      intro i hi
      simp only [hR]
      exact List.getD_eq_getElem _ _ (by simp; omega)
    set g : ℕ → Kimchi.Gate.EndoMul.Witness F := fun i =>
      EndoMulRound.readWith V (R i)
        ((R i).s.x.val V) ((R i).s.y.val V) ((R i).nAccNext.val V) with hg
    -- per-round `Holds`: the successor reads equal the self-reads by the wiring
    have hHolds : ∀ i, i < rs.length + 1 → Kimchi.Gate.EndoMul.Holds eb (g i) := by
      intro i hi
      rcases Nat.lt_or_ge i rs.length with hlt | hge
      · have h := chainHolds_succ hpay i (by simp; omega)
        obtain ⟨ep, en⟩ := hstep i (by simp; omega)
        rw [ep, en] at h
        simp only [hg, hRi i (by omega)]
        exact h
      · have hieq : i = rs.length := by omega
        subst hieq
        have h := chainHolds_last hpay (List.cons_ne_nil _ _)
        rw [List.getLast_eq_getElem] at h
        simp only [List.length_cons, Nat.add_sub_cancel] at h
        rw [hf1, hf2] at h
        simp only [hg, hRi rs.length (le_refl _)]
        exact h
    -- the base is shared, so every round's `t`-cells read as `t`
    have hbase' : ∀ i, i ≤ rs.length → (R i).t = t := by
      intro i hi
      rw [hRi i hi]
      exact hbase i (by simp; omega)
    have hTns : W.Nonsingular ((g 0).xT) ((g 0).yT) := by
      simp only [hg, EndoMulRound.readWith, hbase' 0 (by omega)]
      exact hT
    have hφTns : W.Nonsingular (eb * (g 0).xT) ((g 0).yT) := by
      simp only [hg, EndoMulRound.readWith, hbase' 0 (by omega)]
      exact hφT
    have hTeq : Point.some _ _ hT = Point.some _ _ hTns :=
      some_congr W hT hTns (by simp [hg, EndoMulRound.readWith, hbase' 0 (by omega)])
        (by simp [hg, EndoMulRound.readWith, hbase' 0 (by omega)])
    have hφTeq : Point.some _ _ hφT = Point.some _ _ hφTns :=
      some_congr W hφT hφTns (by simp [hg, EndoMulRound.readWith, hbase' 0 (by omega)])
        (by simp [hg, EndoMulRound.readWith, hbase' 0 (by omega)])
    -- the seed wiring reads round 0's inputs as the init pair
    have hR0p : (R 0).p = P0 := by rw [hRi 0 (by omega)]; exact hp0
    have hR0n : (R 0).nAcc = .const 0 := by rw [hRi 0 (by omega)]; exact hn0
    have hP0ns' : W.Nonsingular ((g 0).xP) ((g 0).yP) := by
      simp only [hg, EndoMulRound.readWith, hR0p]
      exact hP0ns
    have hP0' : Point.some _ _ hP0ns' = (2 : ℤ) • Point.some _ _ hT
        + (2 : ℤ) • Point.some _ _ hφT := by
      rw [← hP0]
      exact some_congr W hP0ns' hP0ns (by simp [hg, EndoMulRound.readWith, hR0p])
        (by simp [hg, EndoMulRound.readWith, hR0p])
    -- the run count is the traversed prefix's
    have hm : rs.length + 1 = pref.length := by simpa using hlen
    -- the point chain: `endoMul_off` at the extracted run
    obtain ⟨hfin', s, hseq, hsval⟩ :=
      endoMul_off W h2 h3 hodd eb (Point.some _ _ hT) (Point.some _ _ hφT) hoff
        (rs.length + 1) (by omega) g hHolds hTns hTeq hφTns hφTeq
        (fun i hi =>
          ⟨by simp only [hg, EndoMulRound.readWith]
              rw [hbase' i (by omega), hbase' 0 (by omega)],
           by simp only [hg, EndoMulRound.readWith]
              rw [hbase' i (by omega), hbase' 0 (by omega)]⟩)
        (fun i hi => by
          obtain ⟨ep, -⟩ := hstep i (by simp; omega)
          refine ⟨?_, ?_⟩ <;>
            (simp only [hg, EndoMulRound.readWith]
             rw [hRi (i + 1) (by omega), hRi i (by omega), ep]))
        hP0ns' hP0' lam heig
    -- transport the final accumulator to the payload's final pair
    have hax : accX g (rs.length + 1) = fin.1.x.val V := by
      show (g rs.length).xS = _
      simp only [hg, EndoMulRound.readWith]
      rw [hRi rs.length (le_refl _), ← hf1]
    have hay : accY g (rs.length + 1) = fin.1.y.val V := by
      show (g rs.length).yS = _
      simp only [hg, EndoMulRound.readWith]
      rw [hRi rs.length (le_refl _), ← hf1]
    have hfin : W.Nonsingular (fin.1.x.val V) (fin.1.y.val V) := by
      rw [← hax, ← hay]
      exact hfin'
    -- the register chain: `chain_nAcc` from the zero seed
    have hreg : fin.2.val V
        = Kimchi.Gate.EndoScalar.nReconstruct (crumbList g (rs.length + 1)) := by
      have hthreadN : ∀ i, i + 1 < rs.length + 1 → (g (i + 1)).n = (g i).nPrime := by
        intro i hi
        obtain ⟨-, en⟩ := hstep i (by simp; omega)
        simp only [hg, EndoMulRound.readWith]
        rw [hRi (i + 1) (by omega), hRi i (by omega), en]
      have hchain := chain_nAcc eb (rs.length + 1) g hHolds hthreadN
      have hlast : accN g (rs.length + 1) = fin.2.val V := by
        show (g rs.length).nPrime = _
        simp only [hg, EndoMulRound.readWith]
        rw [hRi rs.length (le_refl _), ← hf2]
      have hzero : accN g 0 = 0 := by
        show (g 0).n = 0
        simp [hg, EndoMulRound.readWith, hR0n, CVar.val]
      rw [← hlast, hchain, hzero, zero_mul, zero_add]
    exact ⟨crumbList g (rs.length + 1),
      crumbList_valid eb (rs.length + 1) g hHolds,
      by rw [crumbList_length, hm],
      hreg,
      hfin, s, (some_congr W hfin hfin' hax.symm hay.symm).trans hseq, hsval⟩

open Kimchi.Gate.VarBaseMul (y_ne_zero_of_odd_order) in
/-- The gadget is sound: under any satisfying valuation, for a base point reading
on-curve together with its endomorphism image, the result reads as `[s]·T` where
`(s : F) = EndoScalar.toField crumbs λ` for a valid crumb list of length `2·rounds`
whose reconstruction is the scalar — EndoMul multiplies by exactly the scalar
EndoScalar decodes. The curve-specific hypotheses are the eigenvalue relation `heig`
and the GLV off-targets fact `hoff` (`{pallas,vesta}_combo_off_targets`'s shape);
the deployed corollaries instantiate them. -/
theorem endoMul_spec [Field F] [DecidableEq F] [ToNat F]
    (W : WeierstrassCurve.Affine F) [Fact (Nat.Prime W.order)]
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hodd : W.order ≠ 2)
    (eb : F) (lam : ℤ)
    (heig : ∀ {x y : F} (hT : W.Nonsingular x y) (hφT : W.Nonsingular (eb * x) y),
      Point.some _ _ hφT = lam • Point.some _ _ hT)
    (hoff : ∀ {a b : ℤ}, a ≠ 0 → b ≠ 0 → |a| < 2 ^ 126 → |b| < 2 ^ 126 →
      ∀ {T φT : W.Point}, T ≠ 0 → φT = lam • T →
        a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T ∧
        a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT)
    (rounds : ℕ) (hbits : 4 * rounds ≤ 244)
    (t : AffinePoint (FVar F)) (scalar : FVar F)
    (Q : PostCond (AffinePoint (FVar F)) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : AffinePoint (FVar F)) =>
        ∀ (hT : W.Nonsingular (t.x.val V) (t.y.val V)),
          W.Nonsingular (eb * t.x.val V) (t.y.val V) →
          ∃ crumbs : List F,
            (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
            crumbs.length = 2 * rounds ∧
            scalar.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs ∧
            ∃ (hfin : W.Nonsingular (r.x.val V) (r.y.val V)) (s : ℤ),
              Point.some _ _ hfin = s • Point.some _ _ hT ∧
              (s : F) = Kimchi.Gate.EndoScalar.toField crumbs (lam : F)) Q⦄
    (endoMul (c := KimchiConstraint F) eb rounds t scalar)
    ⦃Q⦄ := by
  haveI : Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0) := ⟨⟨ha.1, ha.2.1, ha.2.2.1⟩⟩
  simp only [endoMul, mapAccumM]
  mvcgen
  rename_i s hpre
  intro bits _
  mvcgen
  intro phix _ hphix
  mvcgen
  refine AddFast.addFast_checkFinite_spec W ha h2 t ⟨phix, t.y⟩ _ _ ?_
  intro p1 nv1 hp1
  mvcgen
  refine AddFast.addFast_checkFinite_spec W ha h2 p1.p p1.p _ _ ?_
  intro p2 nv2 hp2
  mvcgen
  case inv1 =>
    exact ⇓ p s' => ⌜s'.V = s.V ∧
      Threaded t (p2.p, .const 0) p.1.prefix p.2.snd p.2.fst⌝
  case vc2.vc1.vc1.vc1.vc1.pre =>
    exact ⟨rfl, rfl, rfl⟩
  case vc1.step =>
    rename_i pref cur suff hsplit b st' hinv
    intro w nv'
    mvcgen
    obtain ⟨hV, hthr⟩ := hinv
    exact ⟨hV, hthr.snoc cur w⟩
  case vc3.vc1.vc1.vc1.vc1.post.success =>
    rename_i finp st' hinv
    obtain ⟨hV, hthr⟩ := hinv
    intro _ nv3 heq
    mvcgen
    intro _ nv4 hpay
    rw [hV] at heq hpay
    rw [hV]
    mvcgen
    refine hpre finp.fst.1 _ ?_
    intro hT hφT
    -- the init chain: `[2](T + φT)` from the seal and the two pinned additions
    have hy : t.y.val s.V ≠ 0 := y_ne_zero_of_odd_order W hodd hT
    have hφTp : W.Nonsingular (phix.val s.V) (t.y.val s.V) := by
      rw [hphix, CVar.val_scale_]
      exact hφT
    obtain ⟨hP1, hsum1⟩ := hp1 hT hφTp hy
    have hy1 : p1.p.y.val s.V ≠ 0 := y_ne_zero_of_odd_order W hodd hP1
    obtain ⟨hP0ns, hsum2⟩ := hp2 hP1 hP1 hy1
    have hφeq : Point.some _ _ hφTp = Point.some _ _ hφT :=
      Kimchi.Gate.EndoMul.some_congr W hφTp hφT (by rw [hphix, CVar.val_scale_]) rfl
    have hP0 : Point.some _ _ hP0ns
        = (2 : ℤ) • Point.some _ _ hT + (2 : ℤ) • Point.some _ _ hφT := by
      rw [← hsum2, ← hsum1, hφeq]
      module
    -- the extracted run through `threaded_sound`
    obtain ⟨crumbs, hvalid, hlen, hreg, hfin, sc, hseq, hsval⟩ :=
      threaded_sound W h2 h3 hodd eb lam s.V (by simpa using hbits) hthr hpay hT hφT
        (fun a b ha' hb' hba hbb =>
          hoff ha' hb' hba hbb (Point.some_ne_zero hT) (heig hT hφT))
        (heig hT hφT) hP0ns hP0
    exact ⟨crumbs, hvalid, by simpa using hlen, heq.symm.trans hreg,
      hfin, sc, hseq, hsval⟩

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- `endoMul_spec` at the deployed Pallas instantiation: the eigenvalue from
`pallas_eigen`, the off-targets fact from `pallas_combo_off_targets`, the field and
order facts from `Pasta`. -/
theorem endoMul_spec_pallas [ToNat Fp] (rounds : ℕ) (hbits : 4 * rounds ≤ 244)
    (t : AffinePoint (FVar Fp)) (scalar : FVar Fp)
    (Q : PostCond (AffinePoint (FVar Fp)) (.arg (BuilderState Fp) .pure)) :
    ⦃Sound (fun V (r : AffinePoint (FVar Fp)) =>
        ∀ (hT : Pallas.curve.toAffine.Nonsingular (t.x.val V) (t.y.val V)),
          Pallas.curve.toAffine.Nonsingular (pallasEndo * t.x.val V) (t.y.val V) →
          ∃ crumbs : List Fp,
            (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
            crumbs.length = 2 * rounds ∧
            scalar.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs ∧
            ∃ (hfin : Pallas.curve.toAffine.Nonsingular (r.x.val V) (r.y.val V))
              (s : ℤ),
              Point.some _ _ hfin = s • Point.some _ _ hT ∧
              (s : Fp) = Kimchi.Gate.EndoScalar.toField crumbs (pallasLam : Fp)) Q⦄
    (endoMul (c := KimchiConstraint Fp) pallasEndo rounds t scalar)
    ⦃Q⦄ := by
  refine endoMul_spec Pallas.curve.toAffine ⟨rfl, rfl, rfl, rfl⟩ (by decide) (by decide)
    (by rw [pallas_card]; decide) pallasEndo pallasLam
    (fun hT _ => pallas_eigen hT)
    (fun {a b} ha hb hba hbb {T φT} hTne heig =>
      Kimchi.Gate.EndoMul.pallas_combo_off_targets ha hb hba hbb hTne heig)
    rounds hbits t scalar Q

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- `endoMul_spec` at the deployed Vesta instantiation — the other half of the
2-cycle, identical modulo `vesta_*`. -/
theorem endoMul_spec_vesta [ToNat Fq] (rounds : ℕ) (hbits : 4 * rounds ≤ 244)
    (t : AffinePoint (FVar Fq)) (scalar : FVar Fq)
    (Q : PostCond (AffinePoint (FVar Fq)) (.arg (BuilderState Fq) .pure)) :
    ⦃Sound (fun V (r : AffinePoint (FVar Fq)) =>
        ∀ (hT : Vesta.curve.toAffine.Nonsingular (t.x.val V) (t.y.val V)),
          Vesta.curve.toAffine.Nonsingular (vestaEndo * t.x.val V) (t.y.val V) →
          ∃ crumbs : List Fq,
            (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
            crumbs.length = 2 * rounds ∧
            scalar.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs ∧
            ∃ (hfin : Vesta.curve.toAffine.Nonsingular (r.x.val V) (r.y.val V))
              (s : ℤ),
              Point.some _ _ hfin = s • Point.some _ _ hT ∧
              (s : Fq) = Kimchi.Gate.EndoScalar.toField crumbs (vestaLam : Fq)) Q⦄
    (endoMul (c := KimchiConstraint Fq) vestaEndo rounds t scalar)
    ⦃Q⦄ := by
  refine endoMul_spec Vesta.curve.toAffine ⟨rfl, rfl, rfl, rfl⟩ (by decide) (by decide)
    (by rw [vesta_card]; decide) vestaEndo vestaLam
    (fun hT _ => vesta_eigen hT)
    (fun {a b} ha hb hba hbb {T φT} hTne heig =>
      Kimchi.Gate.EndoMul.vesta_combo_off_targets ha hb hba hbb hTne heig)
    rounds hbits t scalar Q

end EndoMul

end Snarky.Kimchi
