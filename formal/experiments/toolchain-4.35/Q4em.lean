import Snarky.DSL.Field
import Snarky.DSL.SizedF
import Kimchi.Gate.Semantics.EndoMul
import Kimchi.Gate.Semantics.VarBaseMul
import Pasta.Endo
import Snarky.DSL.Assert
import Snarky.DSL.Bits
import Snarky.Kimchi.Semantics
import Snarky.Traverse
import Snarky.Kimchi.Circuit.AddComplete
import Snarky.Kimchi.Circuit.CheckedPoint
import Snarky.Kimchi.Circuit.Curve
import Snarky.Prover.StdWP
import Mathlib.Util.CountHeartbeats

/-!
# The EndoMul gadget

Port of `packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/EndoMul.purs`: the
endomorphism-optimized scalar multiplication. `endoMul` witnesses the scalar's
`4·rounds` bits MSB-first in one bulk witness — four per GLV round, plain field
`0`/`1` values (the gate's own booleanity rows cover them) — builds the initial
accumulator `[2](g + φ(g))` from a sealed `β·x` and two `addFast`s, threads
`(acc, nAcc)` through `mapAccumM` with one eight-field witness per round, pins the
scalar register to the scalar, and emits the `endoMul` constraint.

Naming: `endo` here is the coefficient family (`Pasta.pallasEndo`), so the gadget
carrying the gate's name is `endoMul` and its coefficient parameter is `eb`. `endoInv`
witnesses `[s⁻¹]·g` — the inverse of the scalar `Kimchi.Gate.EndoScalar.toField`
decodes, computed in the other field — over an on-curve checked point, then verifies
with `endoMul` and pins to the input: the cross-field division gadget.

## Deviations from the original

- Type-level sizing renders as the explicit `rounds` parameter with `4 · rounds` bits,
  and the bit reads go through `[ToNat F]`.
- The original batches the whole witness chain (Montgomery-trick advice, leaving the
  emitted circuit untouched). Here each round's witness is computed sequentially from
  the threaded variables via the gate's own `Kimchi.Gate.EndoMul.build` — the same field
  values, and the same eight-variable allocation per round, in the alphabetical order
  `(inv, nAccNext, r, s, s1, s3)`.
- The endo coefficient is the `eb` parameter rather than a field of an ambient class
  (the Poseidon parameter-data deviation). The law layer renders that class as the
  explicit `HasEndo` structure — the coefficient, the eigenvalue, and every curve fact
  the law pair consumes — with the deployed dictionaries `HasEndo.pallas`/`HasEndo.vesta`.
- `endoInv`'s checked point witness renders as the plain pair witness plus
  `CheckedPoint.check` — same allocation, same three rows (`square`, `mul`, `assertSquare`);
  the curve `W` and the scalar-field data `q`, `lam'` are parameters, like `eb`. Its
  advice computes in the other field through the kimchi gate model itself
  (`Kimchi.Gate.EndoScalar.toField` at `crumbsOf`, in `ZMod q`) and scalar-multiplies in
  Mathlib's `WeierstrassCurve.Affine.Point` group, where the original calls a native
  backend; the original's partial affine conversion renders as a `(0, 0)` default on the
  off-curve and infinity paths — unreachable for honest inputs, and advice-only either way.

The law pair reads the emitted constraints through the semantic layer, generic over the
curve dictionary `HasEndo`: `endoMul_spec` (`§ Soundness` below) and `Prover.endoMul_spec`,
the completeness at the prover's reading (at the end) — both directions decode the scalar
through one crumb list.
There are no per-curve law statements: the laws are concretized only inside a larger
circuit's instantiation, and the deployed dictionaries are the discharge (and the exhibit
that the dictionary is satisfiable at Pasta).
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

/-- The scalar's `4·rounds` bits MSB-first as field values, four per row. -/
private def bitsWit [Field F] [ToNat F] (rounds : ℕ) (scalar : FVar F) :
    AsProver F (Vector (Vector F 4) rounds) := do
  let v ← AsProver.readCVar scalar
  let n := ToNat.toNat v
  pure (Vector.ofFn fun r => Vector.ofFn fun j =>
    if n.testBit (4 * rounds - 1 - (4 * r.1 + j.1)) then 1 else 0)

/-- One GLV round's witness: read the base, the threaded accumulator and register,
and the four window bits, and build the gate's canonical row
(`Kimchi.Gate.EndoMul.build` — two `stepWindow` double-adds, the scalar recoding,
the distinct-point inverse). Returned in the alphabetical allocation order
`(inv, nAccNext, r.x, r.y, s.x, s.y, s1, s3)`. -/
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

/-- One `endoMul` window round (the loop body, named): witness the row's advice
octet and assemble the `EndoMulRound` record, returning the round and the advanced
`(accumulator, register)` state. -/
def endoMulRound [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (eb : F) (t : AffinePoint (FVar F)) (st : AffinePoint (FVar F) × FVar F)
    (bs : Vector (FVar F) 4) :
    CircuitM F c (EndoMulRound F × (AffinePoint (FVar F) × FVar F)) := do
  let w ← witness (val := F × F × F × F × F × F × F × F) (rowWit eb t bs st)
  let s : AffinePoint (FVar F) := ⟨w.2.2.2.2.1, w.2.2.2.2.2.1⟩
  pure (({ t, p := st.1, r := ⟨w.2.2.1, w.2.2.2.1⟩, s,
           s1 := w.2.2.2.2.2.2.1, s3 := w.2.2.2.2.2.2.2,
           nAcc := st.2, nAccNext := w.2.1,
           bit0 := bs[0], bit1 := bs[1], bit2 := bs[2], bit3 := bs[3],
           inv := w.1 } : EndoMulRound F),
        (s, w.2.1))

/-- The endomorphism-optimized scalar multiplication: witness the MSB-first bits, seal
`β·x` and build `acc = [2](g + φ(g))` with two `addFast`s, run the `rounds` window rounds
threading `(acc, nAcc)`, pin the scalar fold, emit one `endoMul` constraint, and return
the final accumulator. -/
def endoMul [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [ConstraintHolds F c]
    [KimchiSystem F c]
    (eb : F) (rounds : ℕ) (g : AffinePoint (FVar F))
    (scalar : SizedF (4 * rounds) (FVar F)) :
    CircuitM F c (AffinePoint (FVar F)) := do
  let bits ← witness (val := Vector (Vector F 4) rounds) (bitsWit rounds scalar.val)
  let phix ← sealVar (CVar.scale_ eb g.x)
  let p1 ← addFast .checkFinite g ⟨phix, g.y⟩
  let p2 ← addFast .checkFinite p1.p p1.p
  let (state, fin) ← mapAccumM (endoMulRound eb g) (p2.p, .const 0) bits.toList
  assertEqual fin.2 scalar.val
  addConstraint (KimchiSystem.endoMul { state, s := fin.1, nAcc := fin.2, endo := eb })
  pure fin.1

/-! ### The cross-field division witness

`endoInv`'s advice scalar-multiplies in Mathlib's proven group — the same
`WeierstrassCurve.Affine.Point` the gadget laws are stated over (`nsmulBinRec`
underneath, so a 255-bit multiple is a binary ladder). Advice-only: the emitted circuit
never depends on these values holding anything; the on-curve and `endoMul`-verification
rows are the contract. -/

/-- `endoInv`'s result witness: read the point and the 128-bit challenge, decode the
effective scalar in the scalar field `ZMod q` — the kimchi gate model itself,
`EndoScalar.toField` at the challenge's canonical crumbs and the scalar-field
eigenvalue `lam'` — and hand back `[s⁻¹]·g` computed in `W.Point`. Off-curve reads
and the point at infinity fall back to `(0, 0)` — unreachable for honest inputs. -/
private def endoInvWit [Field F] [DecidableEq F] [ToNat F]
    (W : WeierstrassCurve.Affine F) (q : ℕ) (hq : q.Prime) (lam' : ZMod q)
    (g : AffinePoint (FVar F)) (scalar : FVar F) :
    AsProver F (F × F) :=
  letI : Fact q.Prime := ⟨hq⟩
  do
  let gx ← AsProver.readCVar g.x
  let gy ← AsProver.readCVar g.y
  let s ← AsProver.readCVar scalar
  let eff : ZMod q := Kimchi.Gate.EndoScalar.toField
    (Kimchi.Gate.EndoScalar.crumbsOf 64 (ToNat.toNat s)) lam'
  letI : Decidable (W.Equation gx gy) :=
    decidable_of_iff _ (W.equation_iff gx gy).symm
  letI : Decidable (W.Nonsingular gx gy) :=
    decidable_of_iff _ (W.nonsingular_iff gx gy).symm
  if h : W.Nonsingular gx gy then
    match eff⁻¹.val • (WeierstrassCurve.Affine.Point.some gx gy h : W.Point) with
    | .zero => pure (0, 0)
    | .some x y _ => pure (x, y)
  else pure (0, 0)

/-- Cross-field division by the decoded challenge: witness `[s⁻¹]·g` on-curve — the pair
witness plus the inline on-curve rows — verify `endoMul result scalar = g`, and return the
witnessed point. `W` is the (short-Weierstrass) curve, whose `a₄`/`a₆` are the check's
coefficients; `q` and `lam'` are the scalar-field order and eigenvalue the advice decodes
through. -/
def endoInv [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [ConstraintHolds F c]
    [KimchiSystem F c]
    (eb : F) (W : WeierstrassCurve.Affine F) (q : ℕ) (hq : q.Prime) (lam' : ZMod q)
    (g : AffinePoint (FVar F)) (scalar : SizedF 128 (FVar F)) :
    CircuitM F c (AffinePoint (FVar F)) := do
  let result ← witness (val := F × F) (endoInvWit W q hq lam' g scalar.val)
  let rp : AffinePoint (FVar F) := ⟨result.1, result.2⟩
  CheckedPoint.check W.a₄ W.a₆ rp
  let computed ← endoMul eb 32 rp scalar
  assertEqual computed.x g.x
  assertEqual computed.y g.y
  pure rp

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

/-! ### The chain reading

The payload reads each row's output cells off the next round — the two-row gate's
convention — so `readChain` lays the round list out as the model's witness list, and
three of the four conditions a run needs hold by construction: the links are the shared
cells, and the closing accumulators are the payload's finals. What the trace has to
supply is the base and the seeds. -/

/-- The round list as the model's witness list: each row's output cells come from the
next round's input cells, the last row's from the finals. -/
private def readChain [Field F] (V : Valuation F) (fin : F × F × F) :
    List (EndoMulRound F) → List (Kimchi.Gate.EndoMul.Witness F)
  | [] => []
  | [r] => [EndoMulRound.readWith V r fin.1 fin.2.1 fin.2.2]
  | r :: r' :: rest =>
    EndoMulRound.readWith V r (r'.p.x.val V) (r'.p.y.val V) (r'.nAcc.val V)
      :: readChain V fin (r' :: rest)

private theorem readChain_length [Field F] (V : Valuation F) (fin : F × F × F) :
    ∀ rounds : List (EndoMulRound F), (readChain V fin rounds).length = rounds.length
  | [] => rfl
  | [_] => rfl
  | r :: r' :: rest => by
    show (readChain V fin (r' :: rest)).length + 1 = _
    rw [readChain_length V fin (r' :: rest)]
    rfl

/-- The payload is exactly the gate at every row of the reading. -/
private theorem readChain_holds [Field F] [DecidableEq F] {V : Valuation F} {endo : F}
    {fin : F × F × F} :
    ∀ {rounds : List (EndoMulRound F)}, EndoMul.chainHolds V endo fin rounds →
      ∀ w ∈ readChain V fin rounds, Kimchi.Gate.EndoMul.Holds endo w
  | [], _, _, hw => by simp [readChain] at hw
  | [_], h, w, hw => by
    simp only [readChain, List.mem_singleton] at hw
    exact hw ▸ h
  | _ :: r' :: rest, h, w, hw => by
    rw [readChain, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact h.1
    · exact readChain_holds h.2 w hw

/-- The reading's first row is the first round's: its base, accumulator and register
cells are that round's. -/
private theorem readChain_head [Field F] (V : Valuation F) (fin : F × F × F)
    (d : Kimchi.Gate.EndoMul.Witness F) (r₀ : EndoMulRound F) :
    ∀ rs : List (EndoMulRound F),
      ((readChain V fin (r₀ :: rs)).getD 0 d).xT = r₀.t.x.val V
        ∧ ((readChain V fin (r₀ :: rs)).getD 0 d).yT = r₀.t.y.val V
        ∧ ((readChain V fin (r₀ :: rs)).getD 0 d).xP = r₀.p.x.val V
        ∧ ((readChain V fin (r₀ :: rs)).getD 0 d).yP = r₀.p.y.val V
        ∧ ((readChain V fin (r₀ :: rs)).getD 0 d).n = r₀.nAcc.val V
  | [] => ⟨rfl, rfl, rfl, rfl, rfl⟩
  | _ :: _ => ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Every row of the reading is some round's, so it reads that round's base. -/
private theorem readChain_mem [Field F] (V : Valuation F) (fin : F × F × F) :
    ∀ {rounds : List (EndoMulRound F)} {w : Kimchi.Gate.EndoMul.Witness F},
      w ∈ readChain V fin rounds → ∃ r ∈ rounds, w.xT = r.t.x.val V ∧ w.yT = r.t.y.val V
  | [], _, hw => by simp [readChain] at hw
  | [r], _, hw => by
    simp only [readChain, List.mem_singleton] at hw
    exact ⟨r, by simp, by rw [hw]; exact ⟨rfl, rfl⟩⟩
  | r :: r' :: rest, w, hw => by
    have hcons : readChain V fin (r :: r' :: rest)
        = EndoMulRound.readWith V r (r'.p.x.val V) (r'.p.y.val V) (r'.nAcc.val V)
          :: readChain V fin (r' :: rest) := rfl
    rw [hcons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ⟨r, by simp, rfl, rfl⟩
    · obtain ⟨r'', hr'', hx, hy⟩ := readChain_mem V fin hw
      exact ⟨r'', List.mem_cons_of_mem _ hr'', hx, hy⟩

/-- Adjacent rows of the reading link on both accumulators: they share the cells. -/
private theorem readChain_link [Field F] (V : Valuation F) (fin : F × F × F) :
    ∀ rounds : List (EndoMulRound F),
      (readChain V fin rounds).IsChain
        fun a b => (b.xP = a.xS ∧ b.yP = a.yS) ∧ b.n = a.nPrime
  | [] => by simp [readChain]
  | [_] => by simp [readChain]
  | r :: r' :: rest => by
    show (EndoMulRound.readWith V r (r'.p.x.val V) (r'.p.y.val V) (r'.nAcc.val V)
      :: readChain V fin (r' :: rest)).IsChain _
    exact (readChain_link V fin (r' :: rest)).cons (by
      cases rest <;> simp [readChain, EndoMulRound.readWith])

/-- The reading closes at the payload's finals. -/
private theorem readChain_getLast [Field F] (V : Valuation F) (fin : F × F × F) :
    ∀ (rounds : List (EndoMulRound F)) (hne : readChain V fin rounds ≠ []),
      ((readChain V fin rounds).getLast hne).xS = fin.1
        ∧ ((readChain V fin rounds).getLast hne).yS = fin.2.1
        ∧ ((readChain V fin rounds).getLast hne).nPrime = fin.2.2
  | [], hne => by simp [readChain] at hne
  | [_], _ => ⟨rfl, rfl, rfl⟩
  | r :: r' :: rest, _ => by
    have hne' : readChain V fin (r' :: rest) ≠ [] := by cases rest <;> simp [readChain]
    have hcons : readChain V fin (r :: r' :: rest)
        = EndoMulRound.readWith V r (r'.p.x.val V) (r'.p.y.val V) (r'.nAcc.val V)
          :: readChain V fin (r' :: rest) := rfl
    obtain ⟨h1, h2, h3⟩ := readChain_getLast V fin (r' :: rest) hne'
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hcons, List.getLast_cons hne']
    · exact h1
    · exact h2
    · exact h3

/-- A round against its row: it reads the base and the row's four bits. -/
private def RowIn (t : AffinePoint (FVar F)) (bs : Vector (FVar F) 4) (r : EndoMulRound F) :
    Prop :=
  r.t = t ∧ r.bit0 = bs[0] ∧ r.bit1 = bs[1] ∧ r.bit2 = bs[2] ∧ r.bit3 = bs[3]

/-- The round reads the accumulator `st`, writes `st'`, and is wired to the base and the row's
four bits. Structural — no valuation appears. -/
private def Threads (t : AffinePoint (FVar F)) (st : AffinePoint (FVar F) × FVar F)
    (bs : Vector (FVar F) 4) (r : EndoMulRound F)
    (st' : AffinePoint (FVar F) × FVar F) : Prop :=
  (r.p, r.nAcc) = st ∧ (r.s, r.nAccNext) = st' ∧ RowIn t bs r

/-- A trace, read through `chain_iff`: each round against its row, adjacent rounds linking,
and the ends. -/
private theorem threads_facts {t : AffinePoint (FVar F)}
    {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 4)}
    {rounds : List (EndoMulRound F)} (h : Chain (Threads t) st pref rounds fin) :
    List.Forall₂ (RowIn t) pref rounds ∧
      rounds.IsChain (fun y y' => (y'.p, y'.nAcc) = (y.s, y.nAccNext)) ∧
      (∀ y ∈ rounds.head?, (y.p, y.nAcc) = st) ∧
      (rounds.getLast?.map fun r => (r.s, r.nAccNext)).getD st = fin :=
  (chain_iff (fun r : EndoMulRound F => (r.p, r.nAcc)) (fun r => (r.s, r.nAccNext))
    (RowIn t) fun _ _ _ _ => Iff.rfl).mp h

/-- Every round of a trace reads the same base. -/
private theorem threads_base {t : AffinePoint (FVar F)}
    {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 4)}
    {rounds : List (EndoMulRound F)} (h : Chain (Threads t) st pref rounds fin) :
    ∀ r ∈ rounds, r.t = t := by
  have hF := (threads_facts h).1
  clear h
  induction hF with
  | nil => simp
  | cons hq _ ih => simpa [hq.1] using ih

/-- A trace's first round opens at the seed accumulators. -/
private theorem threads_head {t : AffinePoint (FVar F)}
    {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 4)}
    {r₀ : EndoMulRound F} {rs : List (EndoMulRound F)}
    (h : Chain (Threads t) st pref (r₀ :: rs) fin) : r₀.p = st.1 ∧ r₀.nAcc = st.2 :=
  Prod.ext_iff.mp ((threads_facts h).2.2.1 r₀ (by simp))

/-- A trace's rounds are as many as the rows it traversed. -/
private theorem threads_length {t : AffinePoint (FVar F)}
    {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 4)}
    {rounds : List (EndoMulRound F)} (h : Chain (Threads t) st pref rounds fin) :
    rounds.length = pref.length :=
  (threads_facts h).1.length_eq.symm

open Std.Do in
/-- The step's spec: the round it emits is wired to the base, the accumulators either
side, and the row's bits. -/
@[spec] private theorem endoMulRound_spec {V : Valuation F} [Field F] [DecidableEq F]
    (eb : F) (t : AffinePoint (FVar F)) (st : AffinePoint (FVar F) × FVar F)
    (bs : Vector (FVar F) 4) :
    ⦃⌜True⌝⦄
    endoMulRound (c := Builder V (KimchiConstraint F)) eb t st bs
    ⦃⇓ p _ => ⌜Threads t st bs p.1 p.2⌝⦄ := by
  simp only [endoMulRound, Threads]
  mvcgen

/-- A satisfied trace from the doubled seed computes the gate tower's chain: the reading
is a run (`isChain_getD`), so `endoMul_off` gives the final accumulator as a multiple of
the base and `chain_nAcc` gives the register as the run's crumb reconstruction. -/
private theorem chain_sound [Field F] [DecidableEq F] (d : HasEndo F) (V : Valuation F)
    {t P0 : AffinePoint (FVar F)} {pref : List (Vector (FVar F) 4)}
    {rounds : List (EndoMulRound F)} {fin : AffinePoint (FVar F) × FVar F}
    (hbits : 4 * pref.length ≤ 244)
    (hthr : Chain (Threads t) (P0, .const 0) pref rounds fin)
    (hpay : EndoMul.chainHolds V d.endo
      (fin.1.x.val V, fin.1.y.val V, fin.2.val V) rounds)
    (hT : d.W.Nonsingular (t.x.val V) (t.y.val V))
    (hP0ns : d.W.Nonsingular (P0.x.val V) (P0.y.val V))
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • Point.some _ _ hT
      + (2 : ℤ) • Point.some _ _ (d.endo_nonsingular hT)) :
    ∃ crumbs : List F,
      (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
      crumbs.length = 2 * pref.length ∧
      fin.2.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs ∧
      ∃ (hfin : d.W.Nonsingular (fin.1.x.val V) (fin.1.y.val V)) (s A B : ℤ),
        Point.some _ _ hfin = s • Point.some _ _ hT ∧
        s = B + A * d.lam ∧
        |A| ≤ 3 * 4 ^ pref.length ∧ |B| ≤ 3 * 4 ^ pref.length ∧
        (A : F) = Kimchi.Gate.EndoScalar.decomposeA crumbs ∧
        (B : F) = Kimchi.Gate.EndoScalar.decomposeB crumbs ∧
        (s : F) = Kimchi.Gate.EndoScalar.toField crumbs (d.lam : F) := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have hφT := d.endo_nonsingular hT
  match hround : rounds, hthr with
  | [], hthr' =>
    obtain ⟨rfl, rfl⟩ := Chain.of_nil_out hthr'
    refine ⟨[], by simp, by simp, ?_, hP0ns, 2 + 2 * d.lam, 2, 2, ?_, by ring,
      by norm_num, by norm_num, by simp [Kimchi.Gate.EndoScalar.decomposeA,
        Kimchi.Gate.EndoScalar.decomposeFold], by simp [Kimchi.Gate.EndoScalar.decomposeB,
        Kimchi.Gate.EndoScalar.decomposeFold], ?_⟩
    · simp [Kimchi.Gate.EndoScalar.nReconstruct, CVar.val]
    · rw [hP0, d.eigen hT hφT, smul_smul, add_smul]
    · simp [Kimchi.Gate.EndoScalar.toField, Kimchi.Gate.EndoScalar.decomposeA,
        Kimchi.Gate.EndoScalar.decomposeB, Kimchi.Gate.EndoScalar.decomposeFold]
      ring
  | r₀ :: rs, hthr' =>
    subst hround
    set finV : F × F × F := (fin.1.x.val V, fin.1.y.val V, fin.2.val V) with hfinV
    set l := EndoMul.readChain V finV (r₀ :: rs) with hl
    have hne : l ≠ [] := by
      simp only [hl]
      cases rs <;> simp [EndoMul.readChain]
    set g : ℕ → Kimchi.Gate.EndoMul.Witness F := fun i => l.getD i (l.head hne) with hg
    have hlen : l.length = rs.length + 1 := by
      rw [hl, EndoMul.readChain_length]
      simp
    -- every row reads the same base, so the run's `base` holds
    have hbaseAll : ∀ w ∈ l, w.xT = t.x.val V ∧ w.yT = t.y.val V := by
      intro w hw
      obtain ⟨r, hr, hx, hy⟩ := EndoMul.readChain_mem V finV hw
      rw [hx, hy, EndoMul.threads_base hthr' r hr]
      exact ⟨rfl, rfl⟩
    have hbaseD : ∀ w ∈ l.head hne :: l, w.xT = t.x.val V ∧ w.yT = t.y.val V := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hbaseAll _ (List.head_mem hne)
      · exact hbaseAll w hw
    obtain ⟨hgH, hgB, hgE, hgL, hgN⟩ :=
      Kimchi.Gate.EndoMul.isChain_getD d.W d.endo (Point.some _ _ hT) (Point.some _ _ hφT) l
        (l.head hne)
        (fun w hw => EndoMul.readChain_holds hpay w hw)
        (fun w hw => by
          rw [(hbaseD w hw).1, (hbaseD w hw).2]
          exact ⟨hT, rfl⟩)
        (fun w hw => by
          rw [(hbaseD w hw).1, (hbaseD w hw).2]
          exact ⟨hφT, rfl⟩)
        (EndoMul.readChain_link V finV (r₀ :: rs))
    -- the run's first row is round `r₀`, so its seed cells are the trace's
    obtain ⟨h0xT, h0yT, h0xP, h0yP, h0n⟩ :=
      EndoMul.readChain_head V finV (l.head hne) r₀ rs
    obtain ⟨hp0, hn0⟩ := EndoMul.threads_head hthr'
    have hbase0P : (g 0).xP = P0.x.val V ∧ (g 0).yP = P0.y.val V := by
      constructor
      · show (l.getD 0 (l.head hne)).xP = _
        rw [hl] at *
        rw [h0xP, hp0]
      · show (l.getD 0 (l.head hne)).yP = _
        rw [hl] at *
        rw [h0yP, hp0]
    have hP0ns' : d.W.Nonsingular (g 0).xP (g 0).yP := by
      rw [hbase0P.1, hbase0P.2]; exact hP0ns
    obtain ⟨hfin', sc, A, B, hseq, hsab, hAle, hBle, hAval, hBval, hsval⟩ :=
      Kimchi.Gate.EndoMul.endoMul_off d.W d.two_ne d.three_ne d.odd d.endo
        (Point.some _ _ hT) (Point.some _ _ hφT)
        (fun a b ha hb hba hbb =>
          d.off_targets ha hb hba hbb (Point.some_ne_zero hT) (d.eigen hT hφT))
        l.length (by
          have hl' := EndoMul.threads_length hthr'
          simp only [List.length_cons] at hl'
          omega) g hgH hgB hgE hgL
        hP0ns'
        ((Kimchi.Gate.AddComplete.some_congr d.W hP0ns' hP0ns
          hbase0P.1 hbase0P.2).trans hP0)
        d.lam (d.eigen hT hφT)
    -- the run closes at the payload's finals
    obtain ⟨hax, hay, han⟩ :=
      Kimchi.Gate.EndoMul.acc_getD_length l hne (l.head hne)
    obtain ⟨hlx, hly, hln⟩ := EndoMul.readChain_getLast V finV (r₀ :: rs) hne
    have hfinx : Kimchi.Gate.EndoMul.accX g l.length = fin.1.x.val V := by
      rw [hg, hax, hlx]
    have hfiny : Kimchi.Gate.EndoMul.accY g l.length = fin.1.y.val V := by
      rw [hg, hay, hly]
    have hfinn : Kimchi.Gate.EndoMul.accN g l.length = fin.2.val V := by
      rw [hg, han, hln]
    have hfin : d.W.Nonsingular (fin.1.x.val V) (fin.1.y.val V) := by
      rw [← hfinx, ← hfiny]; exact hfin'
    -- the register chain
    have hreg : fin.2.val V
        = Kimchi.Gate.EndoScalar.nReconstruct (Kimchi.Gate.EndoMul.crumbList g l.length) := by
      have hzero : Kimchi.Gate.EndoMul.accN g 0 = 0 := by
        show (l.getD 0 (l.head hne)).n = 0
        rw [hl] at *
        rw [h0n, hn0]
        simp [CVar.val]
      rw [← hfinn, Kimchi.Gate.EndoMul.chain_nAcc d.endo l.length g hgH hgN, hzero,
        zero_mul, zero_add]
    refine ⟨Kimchi.Gate.EndoMul.crumbList g l.length,
      Kimchi.Gate.EndoMul.crumbList_valid d.endo l.length g hgH,
      ?_, hreg, hfin, sc, A, B, ?_, hsab, ?_, ?_, hAval, hBval, hsval⟩
    case refine_3 =>
      have hpl : pref.length = l.length := by
        rw [hlen, ← EndoMul.threads_length hthr']
        simp
      rw [hpl]; exact hAle
    case refine_4 =>
      have hpl : pref.length = l.length := by
        rw [hlen, ← EndoMul.threads_length hthr']
        simp
      rw [hpl]; exact hBle
    · rw [Kimchi.Gate.EndoMul.crumbList_length, hlen, ← EndoMul.threads_length hthr']
      simp
    · exact (Kimchi.Gate.AddComplete.some_congr d.W hfin hfin' hfinx.symm hfiny.symm).trans hseq

/-! ## The honest digits

The bit quadruples the bulk witness writes, and the identification of a bounded
decomposition with the prechallenge's `endoExpandZ`: what the soundness spec below and the
law at the prover's reading share. -/

/-- A round's cells. -/
private def cells (r : EndoMulRound F) : List (CVar F) :=
  [r.t.x, r.t.y, r.p.x, r.p.y, r.nAcc, r.nAccNext, r.r.x, r.r.y, r.s.x, r.s.y,
    r.s1, r.s3, r.inv, r.bit0, r.bit1, r.bit2, r.bit3]

/-- The honest bit quadruples: row `i`'s four scalar bits, MSB-first — what the bulk
witness writes and what the model's walk is threaded on. -/
private def bitsOf [Field F] (rounds k i : ℕ) : F × F × F × F :=
  ((if k.testBit (4 * rounds - 1 - 4 * i) then 1 else 0),
    (if k.testBit (4 * rounds - 1 - (4 * i + 1)) then 1 else 0),
    (if k.testBit (4 * rounds - 1 - (4 * i + 2)) then 1 else 0),
    (if k.testBit (4 * rounds - 1 - (4 * i + 3)) then 1 else 0))

open Kimchi.Gate.EndoScalar in
/-- An integer of the shape the sound law hands back — `s = B + A·λ`, bounded by
`3·2^64`, pinned in `F` to the canonical 64-crumb decomposition (a 128-bit
challenge is 64 two-bit crumbs; `3·2^64 = 3·4^32` at 32 rounds) — is the prechallenge's
`endoExpandZ`, via the `d.char_big` window. Modulus-free: consumers cast the one integer
into whichever scalar field acts. -/
private theorem decomposition_eq_endoExpandZ [Field F] [DecidableEq F]
    (d : HasEndo F)
    (n : ℕ) {s A B : ℤ} (hsab : s = B + A * d.lam)
    (hAle : |A| ≤ 3 * 2 ^ 64) (hBle : |B| ≤ 3 * 2 ^ 64)
    (hAval : (A : F) = Kimchi.Gate.EndoScalar.decomposeA (crumbsOf 64 n))
    (hBval : (B : F) = Kimchi.Gate.EndoScalar.decomposeB (crumbsOf 64 n)) :
    s = endoExpandZ d.lam n := by
  obtain ⟨hAlo, hAhi⟩ := decomposeAInt_bounds (digitsOf 64 n)
  obtain ⟨hBlo, hBhi⟩ := decomposeBInt_bounds (digitsOf 64 n)
  rw [digitsOf_length] at hAlo hAhi hBlo hBhi
  have hAZF : Kimchi.Gate.EndoScalar.decomposeA (crumbsOf 64 n)
      = ((decomposeAInt (digitsOf 64 n) : ℤ) : F) := by
    rw [crumbsOf_eq_map, decomposeA_digits d.two_ne d.three_ne _ (digitsOf_lt 64 _)]
  have hBZF : Kimchi.Gate.EndoScalar.decomposeB (crumbsOf 64 n)
      = ((decomposeBInt (digitsOf 64 n) : ℤ) : F) := by
    rw [crumbsOf_eq_map, decomposeB_digits d.two_ne d.three_ne _ (digitsOf_lt 64 _)]
  have hwindow : ∀ X XZ : ℤ, |X| ≤ 3 * 2 ^ 64 →
      2 ^ 64 + 1 ≤ XZ → XZ ≤ 3 * 2 ^ 64 - 1 → ((X - XZ : ℤ) : F) = 0 → X = XZ := by
    intro X XZ hXle hXZlo hXZhi hcast
    have habs : |X - XZ| < 2 ^ 127 := by
      rw [abs_lt]
      obtain ⟨hX1, hX2⟩ := abs_le.mp hXle
      have hbig : (6 : ℤ) * 2 ^ 64 < 2 ^ 127 := by norm_num
      constructor <;> linarith
    have := d.char_big _ habs hcast
    omega
  have hAeq : A = decomposeAInt (digitsOf 64 n) :=
    hwindow _ _ hAle hAlo hAhi (by push_cast; rw [hAval, hAZF]; ring)
  have hBeq : B = decomposeBInt (digitsOf 64 n) :=
    hwindow _ _ hBle hBlo hBhi (by push_cast; rw [hBval, hBZF]; ring)
  rw [hsab, hAeq, hBeq, endoExpandZ, toIntZ]
  ring

open Std.Do WeierstrassCurve.Affine Kimchi.Gate.EndoScalar in
/-- **Soundness**, at the deployed thirty-two rounds — the sixty-four crumbs of a 128-bit
challenge, the width the `SizedF 128` operand fixes. Any satisfying valuation reads the
scalar as a prechallenge below that width, and the result as the base multiplied by that
prechallenge's decoded integer.

The integer is modulus-free: the crumbs the gate exposes are pinned to their own base-4
value, and the accumulator bounds identify the decomposition with its ℤ shadow through
`d.char_big`, so a consumer casts the one integer into whichever scalar field acts. -/
theorem endoMul_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (d : HasEndo F) (t : AffinePoint (FVar F)) (scalar : SizedF 128 (FVar F)) :
    ⦃⌜True⌝⦄
    Snarky.Kimchi.endoMul (c := Builder V (KimchiConstraint F)) d.endo 32 t scalar
    ⦃⇓ r _ => ⌜∀ T : d.W.Point, OnCurveAt d.W V t T →
      ∃ n : ℕ, n < 2 ^ 128 ∧ scalar.val.val V = ((n : ℕ) : F) ∧
        OnCurveAt d.W V r (endoExpandZ d.lam n • T)⌝⦄ := by
  have hbits : 4 * 32 ≤ 244 := by norm_num
  have hloop := mapAccumM_spec (V := V) (c := KimchiConstraint F)
    (Snarky.Kimchi.endoMulRound d.endo t) (Threads t)
    (fun st bs => endoMulRound_spec d.endo t st bs)
  unfold Snarky.Kimchi.endoMul
  mvcgen [hloop]
  case vc1.W => exact d.W
  case vc2.ha => exact ⟨d.short.1, d.short.2.1, d.short.2.2.1, d.short.2.2.2⟩
  case vc3.htwo => exact d.two_ne
  case vc4.W => exact d.W
  case vc5.ha => exact ⟨d.short.1, d.short.2.1, d.short.2.2.1, d.short.2.2.2⟩
  case vc6.htwo => exact d.two_ne
  rename_i _ bits _ _ phix _ hphix p1 _ hp1 p2 _ loop _ hchainT _ _ heqScalar _ _ hpay hp2
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  rintro T ⟨hT, rfl⟩
  have hφT := d.endo_nonsingular hT
  have hφTp : d.W.Nonsingular (phix.val V) (t.y.val V) := by
    rw [hphix, CVar.val_scale_]
    exact hφT
  obtain ⟨hP1, hsum1⟩ : ∃ h3 : d.W.Nonsingular (p1.p.x.val V) (p1.p.y.val V),
      Point.some _ _ hT + Point.some _ _ hφTp = Point.some _ _ h3 := by
    rcases hp1.2 (Point.some _ _ hT) (Point.some _ _ hφTp) ⟨hT, rfl⟩ ⟨hφTp, rfl⟩
      (d.two_torsion_free _ (Point.some_ne_zero hT)) with ⟨hinf, -⟩ | ⟨-, h3⟩
    · exact absurd ((hp1.1 rfl).symm.trans hinf) (by norm_num)
    · exact h3
  obtain ⟨hP0ns, hsum2⟩ : ∃ h3 : d.W.Nonsingular (p2.p.x.val V) (p2.p.y.val V),
      Point.some _ _ hP1 + Point.some _ _ hP1 = Point.some _ _ h3 := by
    rcases hp2.2 (Point.some _ _ hP1) (Point.some _ _ hP1) ⟨hP1, rfl⟩ ⟨hP1, rfl⟩
      (d.two_torsion_free _ (Point.some_ne_zero hP1)) with ⟨hinf, -⟩ | ⟨-, h3⟩
    · exact absurd (hp2.1.symm.trans hinf) (by norm_num)
    · exact h3
  have hφeq : Point.some _ _ hφTp = Point.some _ _ hφT :=
    Kimchi.Gate.AddComplete.some_congr d.W hφTp hφT (by rw [hphix, CVar.val_scale_]) rfl
  have hP0 : Point.some _ _ hP0ns
      = (2 : ℤ) • Point.some _ _ hT + (2 : ℤ) • Point.some _ _ hφT := by
    rw [← hsum2, ← hsum1, hφeq]
    module
  obtain ⟨crumbs, hvalid, hlen, hreg, hfin, sc, A, B, hseq, hsab, hAle, hBle,
    hAval, hBval, -⟩ :=
    chain_sound d V (by simp) hchainT hpay hT hP0ns hP0
  -- the crumbs the gate exposed are the canonical expansion of the value they spell
  have hlen' : crumbs.length = 64 := by simpa using hlen
  obtain ⟨n, hnlt, hcr⟩ := eq_crumbsOf d.two_ne d.three_ne crumbs hvalid
  rw [hlen'] at hnlt hcr
  have h4 : (3 : ℤ) * 4 ^ 32 = 3 * 2 ^ 64 := by norm_num
  refine ⟨n, by rw [show (2 : ℕ) ^ 128 = 4 ^ 64 from by norm_num]; exact hnlt, ?_, hfin, ?_⟩
  · rw [heqScalar.symm.trans hreg, hcr, nReconstruct_crumbsOf, Nat.mod_eq_of_lt hnlt]
  · rw [← decomposition_eq_endoExpandZ d n hsab (h4 ▸ by simpa using hAle)
      (h4 ▸ by simpa using hBle) (hcr ▸ hAval) (hcr ▸ hBval)]
    exact hseq.symm

/-! ## `endoInv`: the division gadget's law pair

The gadget witnesses the quotient and verifies it by multiplying back, so both laws
run through `endoMul`'s: soundness reads the on-curve rows at the witnessed point to
discharge `endoMul_spec`'s hypothesis there, and the two pins carry the product to the
input; completeness, `Prover.endoInv_spec` at the end, supplies the honest quotient and
lands `endoMul`'s law at the prover's reading on it. The multiplier is `endoMul`'s own —
one `endoExpandZ` integer, shared by both directions — and the division is stated by
inverting its residue. -/

open Kimchi.Gate.EndoScalar in
/-- The decoded challenge is a unit modulo the group order: its ℤ shadow is a positive
two-base GLV combination inside the window `combo_ne_zero` prices, so it cannot kill a
nonzero point, and a multiple of the order would. This is what makes the division the
gadget performs well defined — soundness inverts this residue, and completeness needs
the honest quotient to exist. -/
theorem endoExpandZ_ne_zero [Field F] [DecidableEq F] (d : HasEndo F)
    {xv yv : F} (hg : d.W.Nonsingular xv yv) (n : ℕ) :
    ((endoExpandZ d.lam n : ℤ) : ZMod d.W.order) ≠ 0 := by
  haveI : NeZero d.W.order := ⟨d.prime.ne_zero⟩
  obtain ⟨hAlo, hAhi⟩ := decomposeAInt_bounds (digitsOf 64 n)
  obtain ⟨hBlo, hBhi⟩ := decomposeBInt_bounds (digitsOf 64 n)
  rw [digitsOf_length] at hAlo hAhi hBlo hBhi
  intro h0
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  have hkill : endoExpandZ d.lam n • (Point.some _ _ hg : d.W.Point) = 0 := by
    have horder : (d.W.order : ℤ) • (Point.some _ _ hg : d.W.Point) = 0 := by
      rw [natCast_zsmul]; exact card_nsmul_eq_zero'
    rw [hm, mul_comm, mul_smul, horder, smul_zero]
  have hexp : endoExpandZ d.lam n • (Point.some _ _ hg : d.W.Point)
      = decomposeBInt (digitsOf 64 n) • (Point.some _ _ hg : d.W.Point)
        + decomposeAInt (digitsOf 64 n)
          • (d.lam • (Point.some _ _ hg : d.W.Point)) := by
    rw [endoExpandZ, toIntZ]; module
  exact Kimchi.Gate.EndoMul.combo_ne_zero
    (fun a b ha hb hba hbb =>
      d.off_targets ha hb hba hbb (Point.some_ne_zero hg) rfl)
    (by linarith) (by linarith) (by norm_num at hAhi ⊢; linarith)
    (by norm_num at hBhi ⊢; linarith)
    (hexp ▸ hkill)

open Std.Do WeierstrassCurve.Affine Kimchi.Gate.EndoScalar in
open Kimchi.Gate.VarBaseMul (eq_inv_smul_of_smul_eq) in
/-- **Soundness.** Under any satisfying valuation, an input reading as a curve point is
the result scaled by the challenge's decoded integer — so the result is that integer's
inverse residue acting on the input.

The on-curve rows discharge `endoMul_spec`'s hypothesis at the witnessed point — the
gadget's design point — with smoothness (`d.delta_ne`) upgrading their equation to
nonsingularity, and the two pins carry the product to the input. The advice parameters
`q`, `hq` and `lam'` are universally quantified: soundness never consults the witness. -/
theorem endoInv_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (d : HasEndo F) (q : ℕ) (hq : q.Prime) (lam' : ZMod q)
    (g : AffinePoint (FVar F)) (scalar : SizedF 128 (FVar F)) :
    ⦃⌜True⌝⦄
    Snarky.Kimchi.endoInv (c := Builder V (KimchiConstraint F))
      d.endo d.W q hq lam' g scalar
    ⦃⇓ r _ => ⌜∀ G : d.W.Point, OnCurveAt d.W V g G →
      ∃ n : ℕ, n < 2 ^ 128 ∧ scalar.val.val V = ((n : ℕ) : F) ∧
        ∃ R : d.W.Point, OnCurveAt d.W V r R ∧
          ((endoExpandZ d.lam n : ℤ) : ZMod d.W.order) ≠ 0 ∧
          endoExpandZ d.lam n • R = G ∧
          R = ((((endoExpandZ d.lam n : ℤ) : ZMod d.W.order)⁻¹).val : ℕ) • G⌝⦄ := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  simp only [Snarky.Kimchi.endoInv]
  have hendo := fun (rp : AffinePoint (FVar F)) =>
    endoMul_spec (V := V) d rp scalar
  have hcheck := fun (rp : AffinePoint (FVar F)) =>
    CheckedPoint.check_spec (V := V) (c := KimchiConstraint F) d.W.a₄ d.W.a₆ rp
  mvcgen [hendo, hcheck]
  rename_i result _ _ _ _ hsq _ _ hcomp _ _ heqx _ _ heqy
  intro G hG
  -- the on-curve rows read as the curve equation at the witnessed point
  have hEq : d.W.Equation (result.1.val V) (result.2.val V) := by
    rw [d.W.equation_iff, d.short.1, d.short.2.1, d.short.2.2.1]
    linear_combination hsq
  have hres : d.W.Nonsingular (result.1.val V) (result.2.val V) :=
    (d.W.equation_iff_nonsingular_of_Δ_ne_zero d.delta_ne).mp hEq
  set R : d.W.Point := Point.some _ _ hres with hRdef
  have hRat : OnCurveAt d.W V (⟨result.1, result.2⟩ : AffinePoint (FVar F)) R := ⟨hres, rfl⟩
  -- `endoMul`'s promise at the witnessed point
  obtain ⟨n, hnlt, hscal, hcompAt⟩ := hcomp R hRat
  -- the pins carry the product to the input
  have hprod : endoExpandZ d.lam n • R = G := OnCurveAt.eq hcompAt hG heqx heqy
  have hs0 : ((endoExpandZ d.lam n : ℤ) : ZMod d.W.order) ≠ 0 :=
    endoExpandZ_ne_zero d hres n
  exact ⟨n, hnlt, hscal, R, hRat, hs0, hprod,
    eq_inv_smul_of_smul_eq d.W hs0 hprod.symm⟩

open Kimchi.Gate.EndoScalar in
/-- The advice's decoded challenge is the residue of the integer `endoMul` names: the
`toField` fold at the canonical crumbs is `endoExpandZ`'s shadow, once `2` and `3` are
units in the scalar field — which an odd prime order that is not `3` makes them. -/
theorem toField_crumbsOf_eq_endoExpandZ [Field F] [DecidableEq F] (d : HasEndo F)
    [Fact (Nat.Prime d.W.order)] (n : ℕ) :
    toField (crumbsOf 64 n) ((d.lam : ZMod d.W.order))
      = ((endoExpandZ d.lam n : ℤ) : ZMod d.W.order) := by
  haveI : NeZero d.W.order := ⟨d.prime.ne_zero⟩
  have h2q : (2 : ZMod d.W.order) ≠ 0 := by
    have h : ((2 : ℤ) : ZMod d.W.order) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hdvd
      have h2 : d.W.order ∣ 2 := by exact_mod_cast hdvd
      exact d.odd ((Nat.prime_dvd_prime_iff_eq d.prime Nat.prime_two).mp h2)
    exact_mod_cast h
  have h3q : (3 : ZMod d.W.order) ≠ 0 := by
    have h : ((3 : ℤ) : ZMod d.W.order) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro hdvd
      have h3 : d.W.order ∣ 3 := by exact_mod_cast hdvd
      exact d.order_ne_three ((Nat.prime_dvd_prime_iff_eq d.prime Nat.prime_three).mp h3)
    exact_mod_cast h
  rw [crumbsOf_eq_map, toField_digits h2q h3q _ (digitsOf_lt 64 _) d.lam]
  rfl

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta Kimchi.Gate.EndoScalar
  WeierstrassCurve.Affine in
/-- **The deployed challenge leg.** At Vesta, the generic law's output on a scalar cell
reading as a prechallenge `n < 2^128` says the result is the base point scaled by the wire's
challenge — the Fq-sponge's endo-expansion of `n`, acting through the point group's
`Fp`-module structure. The generic post names its own prechallenge; below `|Fq|` the
scalar's reading determines it, and its decoded integer is that expansion.

Stated on the generic law's output rather than as a triple, because a consumer reaches it
holding that output — its own program walk has already passed the call. -/
theorem vesta_endoMul_read {V : Valuation Fq} {t r : AffinePoint (FVar Fq)}
    {cv : FVar Fq} {n : ℕ} (hn : n < 2 ^ 128) (hread : cv.val V = ((n : ℕ) : Fq))
    (h : ∀ T : Vesta.curve.toAffine.Point, OnCurveAt Vesta.curve.toAffine V t T →
      ∃ m : ℕ, m < 2 ^ 128 ∧ cv.val V = ((m : ℕ) : Fq) ∧
        OnCurveAt Vesta.curve.toAffine V r (endoExpandZ HasEndo.vesta.lam m • T)) :
    ∀ T : Vesta.curve.toAffine.Point, OnCurveAt Vesta.curve.toAffine V t T →
      OnCurveAt Vesta.curve.toAffine V r
        ((Poseidon.FqSponge.endoExpand ((HasEndo.vesta.lam : ℤ) : Fp) n : Fp) • T) := by
  intro T hT
  obtain ⟨m, hm, hmread, hseq⟩ := h T hT
  have hmn : m = n :=
    CharP.natCast_injOn_Iio Fq PALLAS_SCALAR_CARD
      (Set.mem_Iio.mpr (lt_of_lt_of_le hm (by decide)))
      (Set.mem_Iio.mpr (lt_of_lt_of_le hn (by decide)))
      (by rw [← hmread, hread])
  subst hmn
  rw [← endoExpandZ_cast (by decide) (by decide), Int.cast_smul_eq_zsmul]
  exact hseq

end EndoMul

/-! ## The state-relative completeness laws

`endoMul`'s laws at the prover's reading (`Snarky.Prover.WP`), on `varBaseMul`'s template: the
round's step fact in `Prover.ScanStep` shape at readings named once, the loop's instance of
`Prover.mapAccumM_scan_spec` registered, and the ladder's law closing with the loop as a
spec-table hit and a model bridge onto the gate's honest walk. -/

/-! ### The round at the prover's reading

The round witnesses one advice octet, so the round's chain of states is one link. A round is
read with its own output cells; the payload reads them off the successor instead, and the
ladder's bridge carries the one to the other at the value level. -/

namespace EndoMul

/-- The round's advice octet from the readings: `Kimchi.Gate.EndoMul.build`'s cells, in the
witness's allocation order `(inv, nAccNext, r.x, r.y, s.x, s.y, s1, s3)`. -/
private def rowVal [Field F] (eb xt yt xp yp n b1 b2 b3 b4 : F) :
    F × F × F × F × F × F × F × F :=
  let w := Kimchi.Gate.EndoMul.build eb xt yt xp yp n b1 b2 b3 b4
  (w.inv, w.nPrime, w.xR, w.yR, w.xS, w.yS, w.s1, w.s3)

/-- The round's canonical row from the advice octet: what `Kimchi.Gate.EndoMul.build` computes,
in the witness's own vocabulary, so a round's reading is this record by unfolding alone. -/
private def roundVal [Field F] (eb xt yt xp yp n b1 b2 b3 b4 : F) :
    Kimchi.Gate.EndoMul.Witness F :=
  let v := rowVal eb xt yt xp yp n b1 b2 b3 b4
  { xT := xt, yT := yt, xP := xp, yP := yp, n := n, nPrime := v.2.1,
    b1 := b1, b2 := b2, b3 := b3, b4 := b4,
    s1 := v.2.2.2.2.2.2.1, xR := v.2.2.1, yR := v.2.2.2.1, s3 := v.2.2.2.2.2.2.2,
    xS := v.2.2.2.2.1, yS := v.2.2.2.2.2.1, inv := v.1 }

/-- The octet's record is the gate's canonical row. -/
private theorem roundVal_eq_build [Field F] (eb xt yt xp yp n b1 b2 b3 b4 : F) :
    roundVal eb xt yt xp yp n b1 b2 b3 b4 =
      Kimchi.Gate.EndoMul.build eb xt yt xp yp n b1 b2 b3 b4 := rfl

/-- A row's four bits in scope. -/
private def bitsScoped (st : ProverState F) (b : Vector (FVar F) 4) : Prop :=
  ∀ (i : ℕ) (hi : i < 4), (b[i]'hi).Scoped st

/-- The threaded pair's condition: the base and the accumulator in scope. -/
private def accScoped (t : AffinePoint (FVar F)) (st : ProverState F)
    (a : AffinePoint (FVar F) × FVar F) : Prop :=
  t.x.Scoped st ∧ t.y.Scoped st ∧ a.1.x.Scoped st ∧ a.1.y.Scoped st ∧ a.2.Scoped st

private theorem rowWit_run [Field F] [DecidableEq F] {s : ProverState F} {eb : F}
    {t : AffinePoint (FVar F)} {bs : Vector (FVar F) 4} {acc : AffinePoint (FVar F) × FVar F}
    (hacc : accScoped t s acc) (hbs : bitsScoped s bs) :
    (rowWit eb t bs acc).run s.env = .ok (rowVal eb (t.x.val s.env.get) (t.y.val s.env.get)
      (acc.1.x.val s.env.get) (acc.1.y.val s.env.get) (acc.2.val s.env.get)
      (bs[0].val s.env.get) (bs[1].val s.env.get) (bs[2].val s.env.get)
      (bs[3].val s.env.get)) := by
  simp [rowWit, rowVal, AsProver.readCVar_run hacc.1, AsProver.readCVar_run hacc.2.1,
    AsProver.readCVar_run hacc.2.2.1, AsProver.readCVar_run hacc.2.2.2.1,
    AsProver.readCVar_run hacc.2.2.2.2, AsProver.readCVar_run (hbs 0 (by omega)),
    AsProver.readCVar_run (hbs 1 (by omega)), AsProver.readCVar_run (hbs 2 (by omega)),
    AsProver.readCVar_run (hbs 3 (by omega))]

/-- A round's cells in scope. -/
private def rowScoped (st : ProverState F) (r : EndoMulRound F) : Prop :=
  ∀ cv ∈ cells r, cv.Scoped st

/-- The threaded pair's reading: the base's, the accumulator's, the register's. -/
private def accRead [Field F] (t : AffinePoint (FVar F)) (st : ProverState F)
    (a : AffinePoint (FVar F) × FVar F) : (F × F) × (F × F) × F :=
  ((st.read t.x, st.read t.y), (st.read a.1.x, st.read a.1.y), st.read a.2)

/-- A row's bits' readings. -/
private def bitsRead [Field F] (st : ProverState F) (b : Vector (FVar F) 4) : F × F × F × F :=
  (st.read b[0], st.read b[1], st.read b[2], st.read b[3])

/-- A round's reading with its own output cells: the gate's row, its outputs where the round
witnessed them. -/
private def roundRead [Field F] [DecidableEq F] (st : ProverState F) (r : EndoMulRound F) :
    Kimchi.Gate.EndoMul.Witness F :=
  EndoMulRound.readWith st.env.get r (st.read r.s.x) (st.read r.s.y) (st.read r.nAccNext)

/-- The row a round produces, from the pair's and the bits' readings. -/
private def rowStep [Field F] (eb : F) (a : (F × F) × (F × F) × F) (x : F × F × F × F) :
    Kimchi.Gate.EndoMul.Witness F :=
  roundVal eb a.1.1 a.1.2 a.2.1.1 a.2.1.2 a.2.2 x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The pair's reading after a round: the base unchanged, the row's outputs. -/
private def accStep [Field F] (eb : F) (a : (F × F) × (F × F) × F) (x : F × F × F × F) :
    (F × F) × (F × F) × F :=
  (a.1, ((rowStep eb a x).xS, (rowStep eb a x).yS), (rowStep eb a x).nPrime)

set_option Elab.async false in
#count_heartbeats in
/-- The round's chain of states and every entry cell's reading along it, the one place the
chain is known: the witness's state lies past the entry, and an entry cell in scope reads, at
every state past the entry, what it read at the entry. -/
private theorem round_readings [Field F] {t : AffinePoint (FVar F)} {s₁ s : ProverState F}
    {acc : AffinePoint (FVar F) × FVar F} {bs : Vector (FVar F) 4} (hl : s₁ ≤ s)
    (hacc : accScoped t s₁ acc) (hbs : bitsScoped s₁ bs) :
    s₁ ≤ s ∧
      ∀ u, s₁ ≤ u →
        t.x.val u.env.get = t.x.val s₁.env.get ∧
        t.y.val u.env.get = t.y.val s₁.env.get ∧
        acc.1.x.val u.env.get = acc.1.x.val s₁.env.get ∧
        acc.1.y.val u.env.get = acc.1.y.val s₁.env.get ∧
        acc.2.val u.env.get = acc.2.val s₁.env.get ∧
        ∀ (i : ℕ) (hi : i < 4), (bs[i]'hi).val u.env.get = (bs[i]'hi).val s₁.env.get :=
  ⟨hl, fun _ hle => ⟨CVar.val_of_le hle hacc.1, CVar.val_of_le hle hacc.2.1,
    CVar.val_of_le hle hacc.2.2.1, CVar.val_of_le hle hacc.2.2.2.1,
    CVar.val_of_le hle hacc.2.2.2.2, fun i hi => CVar.val_of_le hle (hbs i hi)⟩⟩

set_option Elab.async false in
#count_heartbeats in
/-- A round's reading survives the state's growth when its cells are in scope. -/
private theorem roundRead_of_le [Field F] [DecidableEq F] {st st' : ProverState F}
    (hle : st ≤ st') {r : EndoMulRound F} (h : ∀ cv ∈ cells r, cv.Scoped st) :
    roundRead st' r = roundRead st r := by
  simp (disch := (apply h; simp [cells])) only [roundRead, EndoMulRound.readWith,
    ProverState.read, CVar.val_of_le hle]

end EndoMul

open EndoMul in
/-- `rowWit` returns the round's advice octet. -/
@[spec] private def Prover.rowWit_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (eb : F) (t : AffinePoint (FVar F)) (bs : Vector (FVar F) 4)
    (acc : AffinePoint (FVar F) × FVar F) :=
  Prover.register (Prover.witness_of_run (c := c) (rowWit eb t bs acc)
    (fun st => accScoped t st acc ∧ bitsScoped st bs)
    (fun st => rowVal eb (st.read t.x) (st.read t.y) (st.read acc.1.x) (st.read acc.1.y)
      (st.read acc.2) (st.read bs[0]) (st.read bs[1]) (st.read bs[2]) (st.read bs[3]))
    (fun _ h => rowWit_run h.1 h.2) fun _ _ => by simp)

open EndoMul in
set_option Elab.async false in
#count_heartbeats in
/-- The round's step fact: its cells in scope, the next accumulator in scope, the round reading
(with its own output cells) as the gate's canonical row at the entry readings, and the
accumulator reading as that row's outputs. -/
private theorem Prover.endoMulRound_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (eb : F) (t : AffinePoint (FVar F)) (st : ProverState F)
    (acc : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 4) :
    ⦃fun s => ⌜s = st ∧ accScoped t st acc ∧ bitsScoped st bs ∧ True⌝⦄
    endoMulRound (c := Prover c) eb t acc bs
    ⦃⇓ p s' => ⌜Prover.ScanStep (accScoped t) rowScoped (accRead t) bitsRead roundRead
      (accStep eb) (rowStep eb) st acc bs p.1 p.2 s'⌝⦄ := by
  unfold endoMulRound
  mvcgen
  all_goals (try grind [Prover.Reg.iff, CircuitType.ReadsAs, CircuitType.scoped_fvar,
    CircuitType.scoped_prod', CVar.Scoped.of_le, accScoped, bitsScoped])
  -- the step fact
  rename_i s₁ w sPt s h hpre
  simp only [Prover.Reg.iff] at h
  simp only [sPt]
  obtain ⟨rfl, hacc, hbs⟩ := hpre
  obtain ⟨hw, hl⟩ := h
  -- the chain and the entry cells' readings along it, from the one lemma that knows it
  obtain ⟨hl, hrd⟩ := round_readings hl hacc hbs
  simp only [CircuitType.ReadsAs, CircuitType.scoped_prod', CircuitType.scoped_fvar,
    CircuitType.reads_prod', CircuitType.reads_fvar] at hw
  refine ⟨?_, ?_, ?_, ?_, hl⟩
  · simp only [rowScoped, cells, List.forall_mem_cons]
    grind [CVar.Scoped.of_le, accScoped, bitsScoped]
  · exact ⟨hacc.1.of_le hl, hacc.2.1.of_le hl, hw.1.2.2.2.2.1, hw.1.2.2.2.2.2.1, hw.1.2.1⟩
  -- the two equations: the vocabulary, the octet's readings, and the entry cells' readings,
  -- the chain's link found in the context
  · simp (disch := assumption) only [roundRead, EndoMulRound.readWith, ProverState.read,
      accRead, bitsRead, rowStep, hw.2, hrd]
    exact rfl
  · simp (disch := assumption) only [ProverState.read, accRead, bitsRead, accStep, rowStep,
      hw.2, hrd]
    exact rfl

open EndoMul in
set_option Elab.async false in
#count_heartbeats in
/-- The ladder's loop, registered: the scan corollary at the round, its transports discharged. -/
@[spec] private def Prover.endoLoop_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (eb : F) (t : AffinePoint (FVar F))
    (init : AffinePoint (FVar F) × FVar F) (xs : List (Vector (FVar F) 4)) :=
  Prover.register (Prover.mapAccumM_scan_spec (accScoped t) bitsScoped rowScoped (accRead t)
    bitsRead roundRead (accStep eb) (rowStep eb) (endoMulRound (c := Prover c) eb t)
    (fun _ => True)
    (fun _ _ _ hle h i hi => (h i hi).of_le hle)
    (fun _ _ _ hle h cv hcv => (h cv hcv).of_le hle)
    (fun _ _ x hle h => by
      simp only [bitsRead, ProverState.read, CVar.val_of_le hle (h 0 (by omega)),
        CVar.val_of_le hle (h 1 (by omega)), CVar.val_of_le hle (h 2 (by omega)),
        CVar.val_of_le hle (h 3 (by omega))])
    (fun _ _ _ hle h => roundRead_of_le hle h)
    (fun st acc x => Prover.endoMulRound_spec eb t st acc x) init xs)

end Snarky.Kimchi

/-! ## EXPERIMENT (Q4): the round under `vcgen` and the cells frame -/

namespace Snarky.Kimchi

open Snarky Lean.Order Std.WP EndoMul

variable {F c : Type}

set_option experimental.vcgen true

theorem tuple_fst {α β : Type} (a : α) (b : β) : (a, b).1 = a := rfl

theorem tuple_snd {α β : Type} (a : α) (b : β) : (a, b).2 = b := rfl

/-- `bitsScoped` as its four cells. -/
theorem bitsScoped_iff' {st : ProverState F} {b : Vector (FVar F) 4} :
    bitsScoped st b ↔ b[0].Scoped st ∧ b[1].Scoped st ∧ b[2].Scoped st ∧ b[3].Scoped st := by
  constructor
  · intro h
    exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)⟩
  · rintro ⟨h0, h1, h2, h3⟩ i hi
    match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3

/-- `witness (rowWit …)` under a name of its own. -/
def rowWitQ [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (eb : F)
    (t : AffinePoint (FVar F)) (bs : Vector (FVar F) 4) (acc : AffinePoint (FVar F) × FVar F) :
    CircuitM F c (FVar F × FVar F × FVar F × FVar F × FVar F × FVar F × FVar F × FVar F) :=
  witness (val := F × F × F × F × F × F × F × F) (rowWit eb t bs acc)

/-- The advice octet's law, without `st₀ ≤ s'`. -/
@[spec] theorem Prover.rowWitQ_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (eb : F) (t : AffinePoint (FVar F)) (bs : Vector (FVar F) 4)
    (acc : AffinePoint (FVar F) × FVar F) (st₀ : ProverState F) :
    ⦃fun s => s = st₀ ∧ (accScoped t st₀ acc ∧ bitsScoped st₀ bs)⦄
    rowWitQ (c := Prover c) eb t bs acc
    ⦃fun r s' => CircuitType.ReadsAs (val := F × F × F × F × F × F × F × F) s' r
      (rowVal eb (st₀.read t.x) (st₀.read t.y) (st₀.read acc.1.x) (st₀.read acc.1.y)
        (st₀.read acc.2) (st₀.read bs[0]) (st₀.read bs[1]) (st₀.read bs[2]) (st₀.read bs[3]))⦄ :=
  Prover.std_witness_of_run (rowWit eb t bs acc) (fun st => accScoped t st acc ∧ bitsScoped st bs)
    (fun st => rowVal eb (st.read t.x) (st.read t.y) (st.read acc.1.x) (st.read acc.1.y)
      (st.read acc.2) (st.read bs[0]) (st.read bs[1]) (st.read bs[2]) (st.read bs[3]))
    (fun _ h => rowWit_run h.1 h.2) (fun _ _ => by simp) st₀

/-- `endoMulRound`, verbatim, over the restated leaf. -/
def endoMulRoundQ [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (eb : F) (t : AffinePoint (FVar F)) (st : AffinePoint (FVar F) × FVar F)
    (bs : Vector (FVar F) 4) :
    CircuitM F c (EndoMulRound F × (AffinePoint (FVar F) × FVar F)) := do
  let w ← rowWitQ eb t bs st
  let s : AffinePoint (FVar F) := ⟨w.2.2.2.2.1, w.2.2.2.2.2.1⟩
  pure (({ t, p := st.1, r := ⟨w.2.2.1, w.2.2.2.1⟩, s,
           s1 := w.2.2.2.2.2.2.1, s3 := w.2.2.2.2.2.2.2,
           nAcc := st.2, nAccNext := w.2.1,
           bit0 := bs[0], bit1 := bs[1], bit2 := bs[2], bit3 := bs[3],
           inv := w.1 } : EndoMulRound F),
        (s, w.2.1))

set_option Elab.async false in
#count_heartbeats in
/-- The round's law without its order conjunct, by `vcgen` under the cells frame. -/
theorem Prover.endoMulRoundQ_spec₀ [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (eb : F) (t : AffinePoint (FVar F)) (st : ProverState F)
    (acc : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 4) :
    ⦃fun s => s = st ∧ (accScoped t st acc ∧ bitsScoped st bs ∧ True)⦄
    endoMulRoundQ (c := Prover c) eb t acc bs
    ⦃fun p s' => Prover.ScanStep₀ (accScoped t) rowScoped (accRead t) bitsRead roundRead
      (accStep eb) (rowStep eb) st acc bs p.1 p.2 s'⦄ := by
  refine ⟨fun s hs => ?_⟩
  obtain ⟨rfl, hacc, hbs, -⟩ := hs
  simp only [accScoped, bitsScoped_iff'] at hacc hbs
  unfold endoMulRoundQ
  vcgen simplifying_assumptions [CircuitType.ReadsAs.eq_1, CircuitType.scoped_prod',
    CircuitType.reads_prod', CircuitType.scoped_fvar, CircuitType.reads_fvar, tuple_fst,
    tuple_snd]
  all_goals first
    | exact Prover.frames_cellsAt _ _ _
    | ((try simp only [CellsAt, rowScoped, cells, List.forall_mem_cons, List.forall_mem_nil,
          accScoped, roundRead, EndoMulRound.readWith, accRead, bitsRead, rowStep, accStep,
          roundVal, Kimchi.Gate.EndoMul.Witness.mk.injEq, Prod.mk.injEq, and_true] at *)
       grind [bitsScoped_iff', rowVal])

/-- The round's law as written. -/
@[spec] theorem Prover.endoMulRoundQ_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (eb : F) (t : AffinePoint (FVar F)) (st : ProverState F)
    (acc : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 4) :
    ⦃fun s => s = st ∧ (accScoped t st acc ∧ bitsScoped st bs ∧ True)⦄
    endoMulRoundQ (c := Prover c) eb t acc bs
    ⦃fun p s' => Prover.ScanStep (accScoped t) rowScoped (accRead t) bitsRead roundRead
      (accStep eb) (rowStep eb) st acc bs p.1 p.2 s'⦄ :=
  Prover.std_scanStep _ _ _ _ _ _ _ (Prover.endoMulRoundQ_spec₀ eb t st acc bs)

open Std.Do in
set_option Elab.async false in
#count_heartbeats in
/-- The loop's instance, as written, over the `vcgen` round. -/
def Prover.endoLoopQ [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (eb : F) (t : AffinePoint (FVar F))
    (init : AffinePoint (FVar F) × FVar F) (xs : List (Vector (FVar F) 4)) (st₀ : ProverState F) :=
  Prover.mapAccumM_scan_spec (accScoped t) bitsScoped rowScoped (accRead t)
    bitsRead roundRead (accStep eb) (rowStep eb) (endoMulRoundQ (c := Prover c) eb t)
    (fun _ => True)
    (fun _ _ _ hle h i hi => (h i hi).of_le hle)
    (fun _ _ _ hle h cv hcv => (h cv hcv).of_le hle)
    (fun _ _ x hle h => by
      simp only [bitsRead, ProverState.read, CVar.val_of_le hle (h 0 (by omega)),
        CVar.val_of_le hle (h 1 (by omega)), CVar.val_of_le hle (h 2 (by omega)),
        CVar.val_of_le hle (h 3 (by omega))])
    (fun _ _ _ hle h => roundRead_of_le hle h)
    (fun st acc x => Prover.do_of_std (Prover.endoMulRoundQ_spec eb t st acc x)) init xs st₀

end Snarky.Kimchi

#print axioms Snarky.Kimchi.Prover.endoMulRoundQ_spec
#print axioms Snarky.Kimchi.Prover.endoLoopQ
