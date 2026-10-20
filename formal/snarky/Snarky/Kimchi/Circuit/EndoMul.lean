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

/-! ### The ladder at the prover's reading

`endoMul`'s law. The loop is the registered scan instance, whose rows are `rowStep` along the
prefix folds from the doubled seed; `scan_rows` and `scan_fold` read those folds as the model's
honest walk (`Kimchi.Gate.EndoMul.chainBuild`), `chainHolds_of_reads` reads the payload's
successor chain off the rounds' own readings, `walk_facts` is the model's side (the rows hold by
`chain_complete`, the final register is the scalar by `chain_nAcc`, the final accumulator names
the decoded multiple by `endoMul_off`), and `exit_facts` states the exit in the law's
vocabulary, so each of the law's conditions is one projection of it. The seed's two additions
are cited by hand at their points: the same law at two instantiations, which `mvcgen` tells
apart by their operands. -/

namespace EndoMul

open Kimchi.Gate.EndoMul (chainBuild accX accY accN)

/-- The scalar's bits MSB-first as field values, four per row: `bitsWit`'s value. -/
private def bitsVal [Field F] [ToNat F] (rounds : ℕ) (v : F) : Vector (Vector F 4) rounds :=
  Vector.ofFn fun r => Vector.ofFn fun j =>
    if (ToNat.toNat v).testBit (4 * rounds - 1 - (4 * r.1 + j.1)) then 1 else 0

private theorem bitsWit_run [Field F] [ToNat F] {s : ProverState F} {rounds : ℕ}
    {scalar : FVar F} (h : scalar.Scoped s) :
    (bitsWit rounds scalar).run s.env = .ok (bitsVal rounds (scalar.val s.env.get)) := by
  simp [bitsWit, bitsVal, AsProver.readCVar_run h]

/-- Every row of the bits bundle is in scope and reads the scalar's bits, off the bundle's
reading. -/
private theorem bits_facts [Field F] [ToNat F] {rounds : ℕ} {st : ProverState F}
    {bits : Vector (Vector (FVar F) 4) rounds} {v : F}
    (h : CircuitType.ReadsAs (val := Vector (Vector F 4) rounds) st bits (bitsVal rounds v))
    (i : ℕ) (hi : i < rounds) :
    bitsScoped st (bits[i]'hi) ∧ bitsRead st (bits[i]'hi) = bitsOf rounds (ToNat.toNat v) i := by
  have hrd : ∀ (j : ℕ) (hj : j < 4), ((bits[i]'hi)[j]'hj).val st.env.get =
      if (ToNat.toNat v).testBit (4 * rounds - 1 - (4 * i + j)) then 1 else 0 := fun j hj => by
    have := CircuitType.reads_fvar.mp
      (CircuitType.reads_vector.mp (CircuitType.reads_vector.mp h.2 i hi) j hj)
    simpa only [bitsVal, Vector.getElem_ofFn] using this
  refine ⟨fun j hj => CircuitType.scoped_fvar.mp
    (CircuitType.scoped_vector.mp (CircuitType.scoped_vector.mp h.1 i hi) j hj), ?_⟩
  simp only [bitsRead, bitsOf, ProverState.read]
  rw [hrd 0 (by omega), hrd 1 (by omega), hrd 2 (by omega), hrd 3 (by omega), Nat.add_zero]

/-- Along rows reading a stream, each `rowStep` at the prefix fold is the walk's row. -/
private theorem scan_rows [Field F] (eb xT yT : F) :
    ∀ (ws : List (F × F × F × F)) (x0 y0 n0 : F) (bs : ℕ → F × F × F × F)
      (d : (F × F) × (F × F) × F),
      (∀ (i : ℕ) (hi : i < ws.length), ws[i] = bs i) →
      ∀ (i : ℕ) (hi : i < ws.length),
        rowStep eb ((ws.scanl (accStep eb) ((xT, yT), (x0, y0), n0)).getD i d) ws[i]
          = chainBuild eb xT yT x0 y0 n0 bs i
  | [], _, _, _, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | w :: ws, x0, y0, n0, bs, d, hws, i, hi => by
    have hw : w = bs 0 := hws 0 (by simp)
    have hstep : accStep eb ((xT, yT), (x0, y0), n0) w
        = ((xT, yT), ((chainBuild eb xT yT x0 y0 n0 bs 0).xS,
            (chainBuild eb xT yT x0 y0 n0 bs 0).yS),
          (chainBuild eb xT yT x0 y0 n0 bs 0).nPrime) := by
      rw [hw]
      simp only [accStep, rowStep]
      rw [roundVal_eq_build]
      rfl
    have hws' : ∀ (k : ℕ) (hk : k < ws.length), ws[k] = bs (k + 1) := fun k hk =>
      hws (k + 1) (by simpa using hk)
    cases i with
    | zero =>
      simp only [List.scanl_cons, List.getD_cons_zero, List.getElem_cons_zero]
      rw [hw]
      simp only [rowStep]
      rw [roundVal_eq_build]
      rfl
    | succ j =>
      have hj : j < ws.length := by simpa using hi
      simp only [List.scanl_cons, List.getD_cons_succ, List.getElem_cons_succ]
      rw [hstep, scan_rows eb xT yT ws _ _ _ (fun m => bs (m + 1)) d hws' j hj,
        Kimchi.Gate.EndoMul.chainBuild_shift]

/-- The walk from row `0`'s outputs, `m` rows on, closes where the walk closes `m + 1` rows
on. -/
private theorem acc_shift [Field F] (eb xT yT x0 y0 n0 : F) (bs : ℕ → F × F × F × F) (m : ℕ) :
    ((accX (chainBuild eb xT yT (chainBuild eb xT yT x0 y0 n0 bs 0).xS
          (chainBuild eb xT yT x0 y0 n0 bs 0).yS (chainBuild eb xT yT x0 y0 n0 bs 0).nPrime
          (fun k => bs (k + 1))) m,
        accY (chainBuild eb xT yT (chainBuild eb xT yT x0 y0 n0 bs 0).xS
          (chainBuild eb xT yT x0 y0 n0 bs 0).yS (chainBuild eb xT yT x0 y0 n0 bs 0).nPrime
          (fun k => bs (k + 1))) m),
      accN (chainBuild eb xT yT (chainBuild eb xT yT x0 y0 n0 bs 0).xS
          (chainBuild eb xT yT x0 y0 n0 bs 0).yS (chainBuild eb xT yT x0 y0 n0 bs 0).nPrime
          (fun k => bs (k + 1))) m)
      = ((accX (chainBuild eb xT yT x0 y0 n0 bs) (m + 1),
          accY (chainBuild eb xT yT x0 y0 n0 bs) (m + 1)),
          accN (chainBuild eb xT yT x0 y0 n0 bs) (m + 1)) := by
  cases m with
  | zero => rfl
  | succ k =>
    simp only [accX, accY, accN]
    rw [Kimchi.Gate.EndoMul.chainBuild_shift eb xT yT x0 y0 n0 bs k]

/-- Along rows reading a stream, the fold from the seed is the walk's final accumulator. -/
private theorem scan_fold [Field F] (eb xT yT : F) :
    ∀ (ws : List (F × F × F × F)) (x0 y0 n0 : F) (bs : ℕ → F × F × F × F),
      (∀ (i : ℕ) (hi : i < ws.length), ws[i] = bs i) →
      ws.foldl (accStep eb) ((xT, yT), (x0, y0), n0)
        = ((xT, yT), (accX (chainBuild eb xT yT x0 y0 n0 bs) ws.length,
            accY (chainBuild eb xT yT x0 y0 n0 bs) ws.length),
          accN (chainBuild eb xT yT x0 y0 n0 bs) ws.length)
  | [], _, _, _, _, _ => rfl
  | w :: ws, x0, y0, n0, bs, hws => by
    have hw : w = bs 0 := hws 0 (by simp)
    have hstep : accStep eb ((xT, yT), (x0, y0), n0) w
        = ((xT, yT), ((chainBuild eb xT yT x0 y0 n0 bs 0).xS,
            (chainBuild eb xT yT x0 y0 n0 bs 0).yS),
          (chainBuild eb xT yT x0 y0 n0 bs 0).nPrime) := by
      rw [hw]
      simp only [accStep, rowStep]
      rw [roundVal_eq_build]
      rfl
    have hws' : ∀ (k : ℕ) (hk : k < ws.length), ws[k] = bs (k + 1) := fun k hk =>
      hws (k + 1) (by simpa using hk)
    rw [List.foldl_cons, hstep, scan_fold eb xT yT ws _ _ _ (fun m => bs (m + 1)) hws',
      List.length_cons, acc_shift]

/-- The payload holds, off the rounds' own readings: when every round reads, with its own
output cells, as a row of a walk whose rows hold and link, and the finals read as the walk's
closing accumulator, the successor-chain reading holds, since a successor's input cells and
its predecessor's output cells both read as the walk's link. -/
private theorem chainHolds_of_reads [Field F] [DecidableEq F] (eb : F) (V : Valuation F) :
    ∀ (W : ℕ → Kimchi.Gate.EndoMul.Witness F) (rounds : List (EndoMulRound F))
      (fin : F × F × F),
      (∀ (i : ℕ) (hi : i < rounds.length), EndoMulRound.readWith V (rounds[i]'hi)
          ((rounds[i]'hi).s.x.val V) ((rounds[i]'hi).s.y.val V)
          ((rounds[i]'hi).nAccNext.val V) = W i) →
      (∀ i, i < rounds.length → Kimchi.Gate.EndoMul.Holds eb (W i)) →
      (∀ i, (W (i + 1)).xP = (W i).xS ∧ (W (i + 1)).yP = (W i).yS ∧
        (W (i + 1)).n = (W i).nPrime) →
      fin = (accX W rounds.length, accY W rounds.length, accN W rounds.length) →
      EndoMul.chainHolds V eb fin rounds
  | _, [], _, _, _, _, _ => trivial
  | W, [r], _, hread, hholds, _, rfl => by
    have h0 := hread 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    show Kimchi.Gate.EndoMul.Holds eb (EndoMulRound.readWith V r (W 0).xS (W 0).yS (W 0).nPrime)
    rw [show (W 0).xS = r.s.x.val V by rw [← h0]; rfl, show (W 0).yS = r.s.y.val V by
      rw [← h0]; rfl, show (W 0).nPrime = r.nAccNext.val V by rw [← h0]; rfl, h0]
    exact hholds 0 (by simp)
  | W, r :: r' :: rest, fin, hread, hholds, hlink, hfin => by
    have h0 := hread 0 (by simp)
    have h1 := hread 1 (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
    have hx : r'.p.x.val V = r.s.x.val V := by
      rw [show r'.p.x.val V = (W 1).xP by rw [← h1]; rfl, (hlink 0).1, ← h0]; rfl
    have hy : r'.p.y.val V = r.s.y.val V := by
      rw [show r'.p.y.val V = (W 1).yP by rw [← h1]; rfl, (hlink 0).2.1, ← h0]; rfl
    have hn : r'.nAcc.val V = r.nAccNext.val V := by
      rw [show r'.nAcc.val V = (W 1).n by rw [← h1]; rfl, (hlink 0).2.2, ← h0]; rfl
    refine ⟨?_, chainHolds_of_reads eb V (fun i => W (i + 1)) (r' :: rest) fin
      (fun i hi => hread (i + 1) (by simpa using hi))
      (fun i hi => hholds (i + 1) (by simpa using hi)) (fun i => hlink (i + 1))
      (by rw [hfin]; rfl)⟩
    show Kimchi.Gate.EndoMul.Holds eb (EndoMulRound.readWith V r _ _ _)
    rw [hx, hy, hn, h0]
    exact hholds 0 (by simp)

/-- The model's side of the ladder: from the base's and the doubled seed's readings, the walk's
rows hold, its final register is the scalar, and its final accumulator names the scalar's
decoded multiple of the base. -/
private theorem walk_facts [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F] (d : HasEndo F)
    {xT yT x0 y0 : F} {T : d.W.Point} (hT : Kimchi.Gate.AddComplete.IsPoint d.W xT yT T)
    (hP0 : Kimchi.Gate.AddComplete.IsPoint d.W x0 y0 ((T + d.lam • T) + (T + d.lam • T)))
    (v : F) (hfits : ToNat.toNat v < 2 ^ 128) :
    (∀ i, i < 32 → Kimchi.Gate.EndoMul.Holds d.endo
        (chainBuild d.endo xT yT x0 y0 0 (bitsOf 32 (ToNat.toNat v)) i)) ∧
      accN (chainBuild d.endo xT yT x0 y0 0 (bitsOf 32 (ToNat.toNat v))) 32 = v ∧
      ∃ hfin : d.W.Nonsingular
          (accX (chainBuild d.endo xT yT x0 y0 0 (bitsOf 32 (ToNat.toNat v))) 32)
          (accY (chainBuild d.endo xT yT x0 y0 0 (bitsOf 32 (ToNat.toNat v))) 32),
        Point.some _ _ hfin = Kimchi.Gate.EndoScalar.endoExpandZ d.lam (ToNat.toNat v) • T := by
  have hbits : 4 * 32 ≤ 244 := by norm_num
  have hfits' : ToNat.toNat v < 4 ^ (2 * 32) := by norm_num; omega
  have h4 : (3 : ℤ) * 4 ^ 32 = 3 * 2 ^ 64 := by norm_num
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  obtain ⟨hTns, rfl⟩ := hT
  have hφT := d.endo_nonsingular hTns
  have heig := d.eigen hTns hφT
  obtain ⟨hP0ns, hP0eq'⟩ := hP0
  have hP0eq : Point.some _ _ hP0ns
      = (2 : ℤ) • Point.some _ _ hTns + (2 : ℤ) • Point.some _ _ hφT := by
    rw [← hP0eq', heig]
    module
  set W := chainBuild d.endo xT yT x0 y0 0 (bitsOf (F := F) 32 (ToNat.toNat v)) with hWdef
  have hbsval : ∀ i, ((bitsOf (F := F) 32 (ToNat.toNat v) i).1 = 0 ∨
        (bitsOf (F := F) 32 (ToNat.toNat v) i).1 = 1) ∧
      ((bitsOf (F := F) 32 (ToNat.toNat v) i).2.1 = 0 ∨
        (bitsOf (F := F) 32 (ToNat.toNat v) i).2.1 = 1) ∧
      ((bitsOf (F := F) 32 (ToNat.toNat v) i).2.2.1 = 0 ∨
        (bitsOf (F := F) 32 (ToNat.toNat v) i).2.2.1 = 1) ∧
      ((bitsOf (F := F) 32 (ToNat.toNat v) i).2.2.2 = 0 ∨
        (bitsOf (F := F) 32 (ToNat.toNat v) i).2.2.2 = 1) := by
    intro i
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [bitsOf] <;> split <;> simp
  have hholds : ∀ i, i < 32 → Kimchi.Gate.EndoMul.Holds d.endo (W i) :=
    Kimchi.Gate.EndoMul.chain_complete d.W (Point.some _ _ hTns) (Point.some _ _ hφT)
      (fun a b ha hb hba hbb => d.off_targets ha hb hba hbb (Point.some_ne_zero hTns) heig)
      32 hbits hTns hφT rfl rfl (bitsOf (F := F) 32 (ToNat.toNat v)) hbsval 0 hP0ns hP0eq
  have hcl : Kimchi.Gate.EndoMul.crumbList W 32
      = Kimchi.Gate.EndoScalar.crumbsOf (2 * 32) (ToNat.toNat v) := by
    rw [Kimchi.Gate.EndoMul.crumbList_ofBits 32 (ToNat.toNat v) W ?_]
    intro r _
    cases r <;> exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨hholds, ?_, ?_⟩
  · rw [Kimchi.Gate.EndoMul.chain_nAcc d.endo 32 W hholds (fun _ _ => rfl),
      show accN W 0 = 0 from rfl, zero_mul, zero_add, hcl,
      Kimchi.Gate.EndoScalar.nReconstruct_crumbsOf, Nat.mod_eq_of_lt hfits',
      LawfulToNat.cast_toNat]
  · obtain ⟨hfin, sc, A, B, hseq, hsab, hAle, hBle, hAval, hBval, -⟩ :=
      Kimchi.Gate.EndoMul.endoMul_off d.W d.two_ne d.three_ne d.odd d.endo
        (Point.some _ _ hTns) (Point.some _ _ hφT)
        (fun a b ha hb hba hbb => d.off_targets ha hb hba hbb (Point.some_ne_zero hTns) heig)
        32 hbits W hholds (fun i _ => by cases i <;> exact ⟨hTns, rfl⟩)
        (fun i _ => by cases i <;> exact ⟨hφT, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) hP0ns hP0eq d.lam
        heig
    refine ⟨hfin, ?_⟩
    rw [← decomposition_eq_endoExpandZ d (ToNat.toNat v) hsab (h4 ▸ hAle) (h4 ▸ hBle)
      (hcl ▸ hAval) (hcl ▸ hBval)]
    exact hseq

/-- The seed's sums are finite: a point named by cells is not zero, `[1 + λ]` does not kill
it, and the group has no 2-torsion. -/
private theorem seed_ne [Field F] [DecidableEq F] (d : HasEndo F) {V : Valuation F}
    {g : AffinePoint (FVar F)} {T : d.W.Point} (h : OnCurveAt d.W V g T) :
    T + T ≠ 0 ∧ T + d.lam • T ≠ 0 ∧ (T + d.lam • T) + (T + d.lam • T) ≠ 0 := by
  obtain ⟨hTns, rfl⟩ := h
  have hne := Point.some_ne_zero hTns
  have hTφ : Point.some _ _ hTns + d.lam • Point.some _ _ hTns ≠ 0 := by
    have := d.lam_succ_smul _ hne
    rwa [add_smul, one_smul] at this
  exact ⟨d.two_torsion_free _ hne, hTφ, d.two_torsion_free _ hTφ⟩

/-- The seed's first addition's operands, past the seal: the base reads `T`, and the sealed
`β·x` beside the base's `y` reads `[λ]·T`. -/
private theorem seed_operands [Field F] [DecidableEq F] (d : HasEndo F)
    {s₀ s₁ s : ProverState F} {g : AffinePoint (FVar F)} {phix : FVar F} {T : d.W.Point}
    (hbase : OnCurveAs d.W s₀ g T) (hle1 : s₀ ≤ s₁)
    (hphix : phix.Scoped s ∧ s.read phix = s₁.read (CVar.scale_ d.endo g.x) ∧ s₁ ≤ s) :
    OnCurveAs d.W s g T ∧ OnCurveAs d.W s ⟨phix, g.y⟩ (d.lam • T) := by
  obtain ⟨hsc, hrd, hle⟩ := hphix
  have hg := scoped_affinePoint.mp hbase.1
  have hx : g.x.val s.env.get = g.x.val s₀.env.get := CVar.val_of_le (hle1.trans hle) hg.1
  have hy : g.y.val s.env.get = g.y.val s₀.env.get := CVar.val_of_le (hle1.trans hle) hg.2
  obtain ⟨hTns, rfl⟩ := hbase.2
  have hφ := d.endo_nonsingular hTns
  refine ⟨⟨scoped_affinePoint.mpr ⟨hg.1.of_le (hle1.trans hle), hg.2.of_le (hle1.trans hle)⟩,
      OnCurveAt.of_reads hx hy hTns⟩,
    ⟨scoped_affinePoint.mpr ⟨hsc, hg.2.of_le (hle1.trans hle)⟩, ?_⟩⟩
  rw [← d.eigen hTns hφ]
  refine OnCurveAt.of_reads (p := ⟨phix, g.y⟩) ?_ hy hφ
  show s.read phix = _
  rw [hrd, ProverState.read, CVar.val_scale_, CVar.val_of_le hle1 hg.1]

/-- The ladder's exit, off what the run leaves at the loop's entry and exit: at any state past
the loop, the payload holds, the final register reads the scalar, and the final accumulator
names the scalar's decoded multiple of the base. -/
private theorem exit_facts [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F] (d : HasEndo F)
    {s₀ s₁ s₄ s₅ u : ProverState F} {g p : AffinePoint (FVar F)} {scalar : FVar F}
    {bits : Vector (Vector (FVar F) 4) 32} {T : d.W.Point}
    {loop : List (EndoMulRound F) × AffinePoint (FVar F) × FVar F}
    (hbase : OnCurveAs d.W s₀ g T) (hfits : ToNat.toNat (s₀.read scalar) < 2 ^ 128)
    (h1 : CircuitType.ReadsAs (val := Vector (Vector F 4) 32) s₁ bits
      (bitsVal 32 (s₀.read scalar)) ∧ s₀ ≤ s₁) (hle : s₁ ≤ s₄)
    (hP : OnCurveAs d.W s₄ p ((T + d.lam • T) + (T + d.lam • T)))
    (hloop : accScoped g s₅ loop.2 ∧
      accRead g s₅ loop.2 =
        (bits.toList.map (bitsRead s₄)).foldl (accStep d.endo) (accRead g s₄ (p, CVar.const 0)) ∧
      loop.1.length = bits.toList.length ∧
      (∀ (i : ℕ) (hi : i < bits.toList.length) (hi' : i < loop.1.length),
        rowScoped s₅ loop.1[i] ∧ roundRead s₅ loop.1[i] =
          rowStep d.endo (((bits.toList.map (bitsRead s₄)).scanl (accStep d.endo)
            (accRead g s₄ (p, CVar.const 0))).getD i (accRead g s₄ (p, CVar.const 0)))
            (bitsRead s₄ bits.toList[i])) ∧
      s₄ ≤ s₅)
    (hu : s₅ ≤ u) :
    EndoMul.chainHolds u.env.get d.endo (u.read loop.2.1.x, u.read loop.2.1.y, u.read loop.2.2)
        loop.1 ∧
      u.read loop.2.2 = s₀.read scalar ∧
      Kimchi.Gate.AddComplete.IsPoint d.W (u.read loop.2.1.x) (u.read loop.2.1.y)
        (Kimchi.Gate.EndoScalar.endoExpandZ d.lam (ToNat.toNat (s₀.read scalar)) • T) := by
  obtain ⟨hbits, hle1⟩ := h1
  obtain ⟨hacc, hfold, hlen, hrows, -⟩ := hloop
  have hbits₄ := hbits.of_le hle
  have hg := scoped_affinePoint.mp hbase.1
  have hT : Kimchi.Gate.AddComplete.IsPoint d.W (s₄.read g.x) (s₄.read g.y) T := by
    rw [ProverState.read_of_le (hle1.trans hle) hg.1, ProverState.read_of_le (hle1.trans hle) hg.2]
    exact hbase.2
  have hws : ∀ (k : ℕ) (hk : k < (bits.toList.map (bitsRead s₄)).length),
      (bits.toList.map (bitsRead s₄))[k] = bitsOf 32 (ToNat.toNat (s₀.read scalar)) k := by
    intro k hk
    have hk' : k < 32 := by simpa using hk
    simp only [List.getElem_map, Vector.getElem_toList]
    exact (bits_facts hbits₄ k hk').2
  have hinit : accRead g s₄ (p, CVar.const 0)
      = ((s₄.read g.x, s₄.read g.y), (s₄.read p.x, s₄.read p.y), 0) := rfl
  obtain ⟨hholds, hreg, hfin, hpt⟩ := walk_facts d hT hP.2 (s₀.read scalar) hfits
  rw [hinit, scan_fold _ _ _ _ _ _ _ _ hws, show (bits.toList.map (bitsRead s₄)).length = 32 by
    simp] at hfold
  simp only [accRead, Prod.mk.injEq] at hfold
  have hux := ProverState.read_of_le hu hacc.2.2.1
  have huy := ProverState.read_of_le hu hacc.2.2.2.1
  have hun := ProverState.read_of_le hu hacc.2.2.2.2
  have hlenR : loop.1.length = 32 := by rw [hlen]; simp
  refine ⟨chainHolds_of_reads d.endo u.env.get _ loop.1 _ (fun i hi => ?_)
      (fun i hi => hholds i (by rw [← hlenR]; exact hi)) (fun _ => ⟨rfl, rfl, rfl⟩) ?_,
    by rw [hun, hfold.2.2]; exact hreg,
    by rw [hux, huy, hfold.2.1.1, hfold.2.1.2]; exact ⟨hfin, hpt.symm⟩⟩
  · have hi' : i < bits.toList.length := by rw [← hlen]; exact hi
    have h := scan_rows d.endo (s₄.read g.x) (s₄.read g.y) _ (s₄.read p.x) (s₄.read p.y) 0
      (bitsOf 32 (ToNat.toNat (s₀.read scalar)))
      ((s₄.read g.x, s₄.read g.y), (s₄.read p.x, s₄.read p.y), 0) hws i (by simpa using hi')
    rw [List.getElem_map] at h
    show roundRead u loop.1[i] = _
    rw [roundRead_of_le hu (hrows i hi' hi).1, (hrows i hi' hi).2, hinit, h]
  · rw [hlenR, hux, huy, hun, hfold.2.1.1, hfold.2.1.2, hfold.2.2]

end EndoMul

open EndoMul in
/-- `bitsWit` returns the scalar's bits. -/
@[spec] private def Prover.bitsWit_reg [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [ConstraintHolds F c] (rounds : ℕ) (scalar : FVar F) :=
  Prover.register (Prover.witness_of_run (c := c) (bitsWit rounds scalar)
    (fun st => scalar.Scoped st) (fun st => bitsVal rounds (st.read scalar))
    (fun _ h => bitsWit_run h) fun _ _ => by simp)

open EndoMul Kimchi.Gate.EndoScalar in
/-- **`endoMul`'s state-relative completeness**, at the deployed thirty-two rounds. From a base
in scope reading as a curve point and a scalar in scope reading below `2 ^ 128`, the run
succeeds and the result reads as the base times the scalar's decoded integer. The loop is the
registered scan instance; `exit_facts` reads its post. -/
theorem Prover.endoMul_spec [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (d : HasEndo F) (g : AffinePoint (FVar F)) (scalar : SizedF 128 (FVar F))
    (T : d.W.Point) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ OnCurveAs d.W st₀ g T ∧ scalar.val.Scoped st₀ ∧
      ToNat.toNat (st₀.read scalar.val) < 2 ^ 128⌝⦄
    endoMul (c := Prover (KimchiConstraint F)) d.endo 32 g scalar
    ⦃⇓ r s' => ⌜OnCurveAs d.W s' r (endoExpandZ d.lam (ToNat.toNat (st₀.read scalar.val)) • T) ∧
      st₀ ≤ s'⌝⦄ := by
  have hadd1 := fun x : FVar F => Prover.register (Prover.addFast_spec .checkFinite d.W d.short
    d.two_ne g ⟨x, g.y⟩ T (d.lam • T))
  have hadd2 := fun a : AffinePoint (FVar F) => Prover.register (Prover.addFast_spec
    .checkFinite d.W d.short d.two_ne a a (T + d.lam • T) (T + d.lam • T))
  unfold endoMul
  -- `-trivial`: the trivial pass would whnf `endoExpandZ`'s sixty-four-digit expansion in the
  -- result's condition
  mvcgen -trivial [hadd1, hadd2]
  all_goals (try grind [Prover.Reg.iff, CircuitType.ReadsAs, CircuitType.scoped_fvar,
    scoped_affinePoint, CVar.Scoped.of_le, CVar.Scoped.scale_, OnCurveAs, accScoped,
    CVar.scoped_const])
  -- the seed's first addition: the base reads `T`, its image `[λ]·T`
  · rename_i s₀ h₀ bits s₁ h1 phix s h2
    simp only [Prover.Reg.iff] at h1 h2
    obtain ⟨rfl, hbase, -, -⟩ := h₀
    obtain ⟨hT2, hTφ, -⟩ := seed_ne d hbase.2
    obtain ⟨hon, honφ⟩ := seed_operands d hbase h1.2 h2
    exact ⟨trivial, hon, honφ, hT2, hTφ⟩
  -- the seed's doubling
  · rename_i s₀ h₀ bits s₁ h1 phix s₂ h2 p1 s h3
    simp only [Prover.Reg.iff] at h3
    obtain ⟨rfl, hbase, -, -⟩ := h₀
    obtain ⟨-, hTφ, h2Tφ⟩ := seed_ne d hbase.2
    exact ⟨trivial, h3.2.2.1 hTφ, h3.2.2.1 hTφ, h2Tφ, h2Tφ⟩
  -- the loop's entry: every row of the bits in scope
  · rename_i s₀ h₀ bits s₁ h1 phix s₂ h2 p1 s₃ h3 p2 s h4
    simp only [Prover.Reg.iff] at h1 h2 h3 h4
    obtain ⟨rfl, hbase, -, -⟩ := h₀
    have hg := scoped_affinePoint.mp hbase.1
    have hle : s₀ ≤ s := h1.2.trans (h2.2.2.trans (h3.2.2.2.trans h4.2.2.2))
    have hps := scoped_affinePoint.mp h4.1
    refine ⟨trivial, ⟨hg.1.of_le hle, hg.2.of_le hle, hps.1, hps.2, CVar.scoped_const _ _⟩,
      fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
    exact (bits_facts (h1.1.of_le (h2.2.2.trans (h3.2.2.2.trans h4.2.2.2))) i hi).1
  -- the register pin: the final register reads the scalar
  · rename_i s₀ h₀ bits s₁ h1 phix s₂ h2 p1 s₃ h3 p2 s₄ h4 loop s h5
    simp only [Prover.Reg.iff] at h1 h2 h3 h4 h5
    obtain ⟨rfl, hbase, hsc, hfits⟩ := h₀
    obtain ⟨-, -, h2Tφ⟩ := seed_ne d hbase.2
    obtain ⟨-, hreg, -⟩ := exit_facts d hbase hfits h1 (h2.2.2.trans (h3.2.2.2.trans h4.2.2.2))
      (h4.2.2.1 h2Tφ) h5 le_rfl
    have hle : s₀ ≤ s := h1.2.trans (h2.2.2.trans (h3.2.2.2.trans (h4.2.2.2.trans h5.2.2.2.2)))
    exact ⟨trivial, h5.1.2.2.2.2, hsc.of_le hle, by rw [hreg, ProverState.read_of_le hle hsc]⟩
  -- the one `endoMul` row: the payload's successor chain holds, its cells in scope
  · rename_i s₀ h₀ bits s₁ h1 phix s₂ h2 p1 s₃ h3 p2 s₄ h4 loop s₅ h5 u s h6
    simp only [Prover.Reg.iff] at h1 h2 h3 h4 h5 h6
    obtain ⟨rfl, hbase, -, hfits⟩ := h₀
    obtain ⟨-, -, h2Tφ⟩ := seed_ne d hbase.2
    refine ⟨trivial, (exit_facts d hbase hfits h1 (h2.2.2.trans (h3.2.2.2.trans h4.2.2.2))
      (h4.2.2.1 h2Tφ) h5 h6).1, fun y hy => ?_⟩
    change y ∈ loop.1.flatMap (fun r => r.cells.filterMap id) ++
      [loop.2.1.x, loop.2.1.y, loop.2.2] at hy
    rw [List.mem_append, List.mem_flatMap] at hy
    rcases hy with ⟨r, hr, hy⟩ | hy
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
      have hs := (h5.2.2.2.1 i (h5.2.2.1 ▸ hi) hi).1
      simp only [rowScoped, cells, List.forall_mem_cons] at hs
      refine CVar.Scoped.of_le h6 ?_
      revert y
      simp [EndoMulRound.cells, hs]
    · obtain ⟨-, -, hx, hy', hn⟩ := h5.1
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · exact hx.of_le h6
      · exact hy'.of_le h6
      · exact hn.of_le h6
  -- the result: the final accumulator reads the decoded multiple
  · rename_i s₀ h₀ bits s₁ h1 phix s₂ h2 p1 s₃ h3 p2 s₄ h4 loop s₅ h5 u₁ s₆ h6 u₂ s h7
    simp only [Prover.Reg.iff] at h1 h2 h3 h4 h5 h6
    obtain ⟨rfl, -⟩ := h7
    obtain ⟨rfl, hbase, -, hfits⟩ := h₀
    obtain ⟨-, -, h2Tφ⟩ := seed_ne d hbase.2
    obtain ⟨-, -, hpt⟩ := exit_facts d hbase hfits h1 (h2.2.2.trans (h3.2.2.2.trans h4.2.2.2))
      (h4.2.2.1 h2Tφ) h5 h6
    exact ⟨⟨scoped_affinePoint.mpr ⟨h5.1.2.2.1.of_le h6, h5.1.2.2.2.1.of_le h6⟩, hpt⟩,
      h1.2.trans (h2.2.2.trans (h3.2.2.2.trans (h4.2.2.2.trans (h5.2.2.2.2.trans h6))))⟩

open EndoMul Kimchi.Gate.EndoScalar in
/-- **`endoInv`'s state-relative completeness**, at the honest advice. From an input reading as a
curve point and a challenge in scope within the deployed width, the run succeeds and the result
reads as `[s⁻¹]·g` for `s` the challenge's decoded integer: `s` is a unit modulo the order, so
the quotient is a finite point, its on-curve rows pass, and multiplying it back by `s` returns
the input, which the two pins need. -/
theorem Prover.endoInv_spec [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (d : HasEndo F) (g : AffinePoint (FVar F)) (scalar : SizedF 128 (FVar F)) (G : d.W.Point)
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ OnCurveAs d.W st₀ g G ∧ scalar.val.Scoped st₀ ∧
      ToNat.toNat (st₀.read scalar.val) < 2 ^ 128⌝⦄
    Snarky.Kimchi.endoInv (c := Prover (KimchiConstraint F)) d.endo d.W d.W.order d.prime
      ((d.lam : ZMod d.W.order)) g scalar
    ⦃⇓ r s' => ⌜OnCurveAs d.W s' r
        (((((endoExpandZ d.lam (ToNat.toNat (st₀.read scalar.val)) : ℤ) : ZMod d.W.order)⁻¹).val
          : ℕ) • G) ∧
      st₀ ≤ s'⌝⦄ := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  haveI : NeZero d.W.order := ⟨d.prime.ne_zero⟩
  -- an input that reads as a curve point names a finite one
  cases G with
  | zero =>
    intro s hs
    simp [OnCurveAs, OnCurveAt, Kimchi.Gate.AddComplete.IsPoint] at hs
  | some xv yv hG =>
  -- the quotient: the decoded challenge is a unit, so `[s⁻¹]·G` is a finite point
  have hs0 : ((endoExpandZ d.lam (ToNat.toNat (st₀.read scalar.val)) : ℤ) : ZMod d.W.order)
      ≠ 0 := endoExpandZ_ne_zero d hG _
  set k : ℕ := (((endoExpandZ d.lam (ToNat.toNat (st₀.read scalar.val)) : ℤ)
    : ZMod d.W.order)⁻¹).val with hkdef
  have hkne : k ≠ 0 := by rw [hkdef, Ne, ZMod.val_eq_zero]; exact inv_ne_zero hs0
  have hkG : ((k : ℕ) : ℤ) • (Point.some xv yv hG : d.W.Point) ≠ 0 :=
    _root_.Pasta.smul_ne_zero_of_lt d.W (Point.some_ne_zero hG)
      (by exact_mod_cast Nat.pos_of_ne_zero hkne) (by exact_mod_cast ZMod.val_lt _)
  obtain ⟨px, py, hpns, hpteq⟩ : ∃ px py, ∃ h : d.W.Nonsingular px py,
      (k : ℕ) • (Point.some xv yv hG : d.W.Point) = Point.some _ _ h := by
    rw [natCast_zsmul] at hkG
    cases hp : (k : ℕ) • (Point.some xv yv hG : d.W.Point) with
    | zero => exact absurd hp hkG
    | some px py h => exact ⟨px, py, h, rfl⟩
  -- multiplying the quotient back by the challenge returns the input
  have hback : endoExpandZ d.lam (ToNat.toNat (st₀.read scalar.val))
      • (Point.some px py hpns : d.W.Point) = Point.some xv yv hG := by
    rw [← hpteq, ← natCast_zsmul, smul_smul]
    have hcast : ((endoExpandZ d.lam (ToNat.toNat (st₀.read scalar.val)) * ((k : ℕ) : ℤ) : ℤ)
        : ZMod d.W.order) = ((1 : ℤ) : ZMod d.W.order) := by
      push_cast
      rw [hkdef, ZMod.natCast_val, ZMod.cast_id, mul_inv_cancel₀ hs0]
    rw [Kimchi.Gate.VarBaseMul.smul_eq_smul_of_zmod_eq d.W hcast, one_smul]
  -- the curve equation at the quotient, in the shape the on-curve rows compare
  have hcurve : py * py = px ^ 3 + d.W.a₄ * px + d.W.a₆ := by
    have h := (d.W.equation_iff px py).mp hpns.1
    rw [d.short.1, d.short.2.1, d.short.2.2.1] at h
    linear_combination h
  -- the honest advice computes the quotient's coordinates
  have hread : ∀ st : ProverState F,
      (OnCurveAs d.W st g (Point.some xv yv hG) ∧ scalar.val.Scoped st ∧
        st.read scalar.val = st₀.read scalar.val) →
      (endoInvWit d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) g scalar.val).run st.env
        = .ok (px, py) := by
    rintro st ⟨⟨hgSc, hgAt⟩, hsc, hsv⟩
    rw [scoped_affinePoint] at hgSc
    obtain ⟨hrx, hry⟩ := Kimchi.Gate.AddComplete.IsPoint.coords_eq hgAt
      (⟨hG, rfl⟩ : Kimchi.Gate.AddComplete.IsPoint d.W xv yv (Point.some xv yv hG))
    simp only [endoInvWit, AsProver.bind_eq, AsProver.run_bind,
      AsProver.readCVar_run hgSc.1, AsProver.readCVar_run hgSc.2,
      AsProver.readCVar_run hsc, hrx, hry, Except.bind]
    rw [dif_pos hG, show scalar.val.val st.env.get = st₀.read scalar.val from hsv,
      toField_crumbsOf_eq_endoExpandZ d, ← hkdef, hpteq]
    rfl
  have hwit := Prover.register (Prover.witness_of_run (c := KimchiConstraint F)
    (endoInvWit d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) g scalar.val)
    (fun st => OnCurveAs d.W st g (Point.some xv yv hG) ∧ scalar.val.Scoped st ∧
      st.read scalar.val = st₀.read scalar.val)
    (fun _ => (px, py)) hread fun _ _ => by simp)
  have hchk := fun p : AffinePoint (FVar F) => Prover.register
    (CheckedPoint.check_prover_spec (c := KimchiConstraint F) d.W.a₄ d.W.a₆ p ⟨px, py⟩ hcurve)
  have hem := fun p : AffinePoint (FVar F) => Prover.register
    (Prover.endoMul_spec d p scalar (Point.some px py hpns))
  -- two cells reading as the same point read the same coordinates: the pins' rows
  have hpin : ∀ (st : ProverState F) (q : AffinePoint (FVar F)),
      OnCurveAs d.W st q (Point.some xv yv hG) → OnCurveAs d.W st g (Point.some xv yv hG) →
      st.read q.x = st.read g.x ∧ st.read q.y = st.read g.y := by
    rintro st q ⟨-, hq⟩ ⟨-, hg⟩
    obtain ⟨hx, hy⟩ := Kimchi.Gate.AddComplete.IsPoint.coords_eq hq hg
    exact ⟨hx, hy⟩
  unfold Snarky.Kimchi.endoInv
  -- `-trivial`: the trivial pass would whnf `endoExpandZ`'s sixty-four-digit expansion in the
  -- conditions, as in `endoMul`'s law
  mvcgen -trivial [hwit, hchk, hem]
  -- EXPERIMENT (toolchain 4.35): grind no longer closes these five VCs; open Q1 item
  all_goals sorry

end Snarky.Kimchi
