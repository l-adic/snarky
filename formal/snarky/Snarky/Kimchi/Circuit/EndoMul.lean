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
parameter is `eb` after the PS binding. `endoInv` keeps its name: it witnesses
`[s⁻¹]·g` (the inverse of the scalar EndoScalar decodes, computed in the OTHER
field) over an on-curve checked point, then verifies with `endoMul` and pins to
the input — the cross-field division gadget.

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
  passes it as the `eb` parameter (the Poseidon parameter-data deviation). The law
  layer renders the class as the explicit `HasEndo` structure — the coefficient, the
  eigenvalue, and every curve fact the law pair consumes, with the deployed
  dictionaries `HasEndo.pallas`/`HasEndo.vesta`.
- `endoInv`'s checked point witness (PS `WeierstrassAffinePoint`, whose `CheckedType`
  instance asserts on-curve) renders as the plain pair witness plus the inline
  on-curve rows — same allocation, same three rows (`square`, `mul`,
  `assertSquare`); the curve `W` and the scalar-field data `(q, lam')` for the
  witness are parameters, like `eb`. Its advice computes in the OTHER field through
  the kimchi gate model itself (`EndoScalar.toField` at `crumbsOf`, in `ZMod q`)
  and scalar-multiplies in Mathlib's `W.Point` group, where PS calls the `curves`
  package's Rust FFI (`Snarky.Curves.Class.scalarMul`); PS's partial `toAffine`
  (`fromJust`) renders as a `(0, 0)` default on the off-curve/infinity paths —
  unreachable for honest inputs, and advice-only either way.

The law pair reads the emitted constraints through the semantic layer, generic over
the curve dictionary `HasEndo`: `EndoMul.endoMul_spec` (`§ Soundness` below) and
`EndoMul.endoMul_complete_spec` (`§ Completeness plumbing` below) — both directions
decode the scalar through one crumb list. There are no per-curve law statements: the
laws are concretized only inside a larger circuit's instantiation, and the deployed
dictionaries `HasEndo.pallas`/`HasEndo.vesta` are the discharge (and the exhibit
that the dictionary is satisfiable at Pasta).
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

/-- One `endoMul` window round (the loop body, named): witness the row's advice
octet and assemble the `EndoMulRound` record, returning the round and the advanced
`(accumulator, register)` state. -/
def endoMulRound [Field F] [DecidableEq F] [BasicSystem F c]
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

/-- The endomorphism-optimized scalar multiplication (PS `endo`; OCaml
`Pickles.Step_main_inputs.Ops.endo`): witness the MSB-first bits, seal `β·x` and
build `acc = [2](g + φ(g))` with two `addFast`s, run the `rounds` window rounds
threading `(acc, nAcc)`, pin the scalar fold, emit one `endoMul` constraint, and
return the final accumulator. -/
def endoMul [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]
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
underneath, so a 255-bit multiple is a binary ladder) — where PS calls the
`curves` package's Rust FFI (`Snarky.Curves.Class.scalarMul`). Advice-only: the
emitted circuit never depends on these values holding anything; the on-curve and
`endoMul`-verification rows are the contract. -/

/-- `endoInv`'s result witness: read the point and the 128-bit challenge, decode the
effective scalar in the scalar field `ZMod q` — the kimchi gate model itself,
`EndoScalar.toField` at the challenge's canonical crumbs and the scalar-field
eigenvalue `lam'` — and hand back `[s⁻¹]·g` computed in `W.Point`. Off-curve reads
and the point at infinity fall back to `(0, 0)` (PS's partial `toAffine`/`fromJust`
path) — unreachable for honest inputs. -/
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

/-- Cross-field division by the decoded challenge (PS `endoInv`; OCaml
`Pickles.Step_verifier`'s `Scalar_challenge.endo_inv`): witness `[s⁻¹]·g` on-curve
— the pair witness plus the inline on-curve rows, PS's checked
`WeierstrassAffinePoint` exists — verify `endoMul result scalar = g`, and return
the witnessed point. `W` is the (short-Weierstrass) curve, whose `a₄`/`a₆` are the
check's coefficients — PS's `curveParams`; `(q, lam')` are the scalar-field order
and eigenvalue the advice decodes through. -/
def endoInv [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]
    (eb : F) (W : WeierstrassCurve.Affine F) (q : ℕ) (hq : q.Prime) (lam' : ZMod q)
    (g : AffinePoint (FVar F)) (scalar : SizedF 128 (FVar F)) :
    CircuitM F c (AffinePoint (FVar F)) := do
  let result ← witness (val := F × F) (endoInvWit W q hq lam' g scalar.val)
  let rp : AffinePoint (FVar F) := ⟨result.1, result.2⟩
  let x2 ← square rp.x
  let x3 ← mul x2 rp.x
  assertSquare rp.y (CVar.add_ (CVar.add_ x3 (CVar.scale_ W.a₄ rp.x)) (.const W.a₆))
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

/-- The endomorphism dictionary (PS `HasEndo` together with the ambient curve facts):
the curve, the endomorphism coefficient and its scalar eigenvalue, and every
curve-level fact the `endoMul` law pair consumes. This is the deep embedding's
rendering of the PS typeclass dictionary — a structure passed explicitly, not a
class, since the formal tree threads theorem content by argument. Generic circuit
laws take one `HasEndo F` and compose over an abstract field the way the PS pickles
circuits do; the deployed `HasEndo.pallas`/`HasEndo.vesta` discharge it, mirroring
the instantiation at wrap/step main. -/
structure HasEndo (F : Type) [Field F] [DecidableEq F] where
  /-- The curve the base point and accumulators live on. -/
  W : WeierstrassCurve.Affine F
  /-- The endomorphism coefficient `β`: `φ(x, y) = (β·x, y)`. -/
  endo : F
  /-- The scalar eigenvalue `λ` of the endomorphism: `φ(T) = [λ]·T`. -/
  lam : ℤ
  /-- The Pasta short-Weierstrass shape. -/
  short : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0
  /-- The curve is smooth, so an on-curve point is nonsingular
  (`equation_iff_nonsingular_of_Δ_ne_zero`). -/
  delta_ne : W.Δ ≠ 0
  /-- The group order is prime. -/
  prime : Nat.Prime W.order
  /-- The group order is not `2` — with `prime`, the group has no 2-torsion. -/
  odd : W.order ≠ 2
  /-- The field does not have characteristic `2`. -/
  two_ne : (2 : F) ≠ 0
  /-- The field does not have characteristic `3`. -/
  three_ne : (3 : F) ≠ 0
  /-- The eigenvalue relation `φ(T) = [λ]·T` at every on-curve point. -/
  eigen : ∀ {x y : F} (hT : W.Nonsingular x y) (hφT : W.Nonsingular (endo * x) y),
    Point.some _ _ hφT = lam • Point.some _ _ hT
  /-- The endomorphism maps the curve to itself. -/
  endo_nonsingular : ∀ {x y : F}, W.Nonsingular x y → W.Nonsingular (endo * x) y
  /-- The GLV off-targets fact: a bounded nonzero two-base combination avoids `±T`,
  `±φT` (`Kimchi.Gate.EndoMul.{pallas,vesta}_combo_off_targets`'s shape). -/
  off_targets : ∀ {a b : ℤ}, a ≠ 0 → b ≠ 0 → |a| < 2 ^ 126 → |b| < 2 ^ 126 →
    ∀ {T φT : W.Point}, T ≠ 0 → φT = lam • T →
      a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T ∧
      a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT
  /-- `[1 + λ]` does not kill a nonzero point — the init sum `T + φT` is finite. -/
  lam_succ_smul : ∀ T : W.Point, T ≠ 0 → (1 + lam) • T ≠ 0
  /-- The order is not `3` either: with `odd`, both `2` and `3` are units in
  `ZMod order`, which lets the decompose tables be read in the scalar field. -/
  order_ne_three : W.order ≠ 3
  /-- The char window: integers below `2^127` in magnitude embed injectively in `F`,
  so bounded fold values with equal `F`-images are equal integers. -/
  char_big : ∀ z : ℤ, |z| < 2 ^ 127 → (z : F) = 0 → z = 0

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- The dictionary at deployed Pallas: `pallasEndo`/`pallasLam`, the facts from
`Pasta` (`pallas_eigen`, `pallas_endo_nonsingular`, `pallas_card`) and the GLV
off-targets fact from the kimchi gate semantics. -/
def HasEndo.pallas : HasEndo Fp where
  W := Pallas.curve.toAffine
  endo := pallasEndo
  lam := pallasLam
  short := ⟨rfl, rfl, rfl, rfl⟩
  delta_ne := by decide
  prime := Fact.out
  odd := by rw [pallas_card]; decide
  two_ne := by decide
  three_ne := by decide
  eigen := fun hT _ => pallas_eigen hT
  endo_nonsingular := fun h => pallas_endo_nonsingular h
  off_targets := fun {a b} ha hb hba hbb {T φT} hTne heig =>
    Kimchi.Gate.EndoMul.pallas_combo_off_targets ha hb hba hbb hTne heig
  lam_succ_smul := fun T hTne => by
    haveI : Fact (Pallas.curve.toAffine.a₁ = 0 ∧ Pallas.curve.toAffine.a₂ = 0
        ∧ Pallas.curve.toAffine.a₃ = 0) := ⟨rfl, rfl, rfl⟩
    exact Kimchi.Gate.VarBaseMul.smul_ne_zero_of_lt Pallas.curve.toAffine hTne
      (by norm_num [pallasLam])
      (by rw [pallas_card]; norm_num [pallasLam])
  order_ne_three := by rw [pallas_card]; decide
  char_big := fun z hz h0 => by
    have hdvd : ((PALLAS_BASE_CARD : ℕ) : ℤ) ∣ z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd z _).mp h0
    exact Int.eq_zero_of_abs_lt_dvd hdvd (hz.trans (by norm_num))

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- The dictionary at deployed Vesta — the other half of the 2-cycle. -/
def HasEndo.vesta : HasEndo Fq where
  W := Vesta.curve.toAffine
  endo := vestaEndo
  lam := vestaLam
  short := ⟨rfl, rfl, rfl, rfl⟩
  delta_ne := by decide
  prime := Fact.out
  odd := by rw [vesta_card]; decide
  two_ne := by decide
  three_ne := by decide
  eigen := fun hT _ => vesta_eigen hT
  endo_nonsingular := fun h => vesta_endo_nonsingular h
  off_targets := fun {a b} ha hb hba hbb {T φT} hTne heig =>
    Kimchi.Gate.EndoMul.vesta_combo_off_targets ha hb hba hbb hTne heig
  lam_succ_smul := fun T hTne => by
    haveI : Fact (Vesta.curve.toAffine.a₁ = 0 ∧ Vesta.curve.toAffine.a₂ = 0
        ∧ Vesta.curve.toAffine.a₃ = 0) := ⟨rfl, rfl, rfl⟩
    exact Kimchi.Gate.VarBaseMul.smul_ne_zero_of_lt Vesta.curve.toAffine hTne
      (by norm_num [vestaLam])
      (by rw [vesta_card]; norm_num [vestaLam])
  order_ne_three := by rw [vesta_card]; decide
  char_big := fun z hz h0 => by
    have hdvd : ((PALLAS_SCALAR_CARD : ℕ) : ℤ) ∣ z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd z _).mp h0
    exact Int.eq_zero_of_abs_lt_dvd hdvd (hz.trans (by norm_num))

namespace EndoMul

/-! ## Soundness

The payload reads each row's output cells off the NEXT round — the two-row gate's
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

/-- The step's grant: the round is built from the base, the accumulators either side of
it, and the row's bits. Structural — no valuation appears. -/
private def Threads (t : AffinePoint (FVar F)) (st : AffinePoint (FVar F) × FVar F)
    (bs : Vector (FVar F) 4) (r : EndoMulRound F)
    (st' : AffinePoint (FVar F) × FVar F) : Prop :=
  r.t = t ∧ (r.p = st.1 ∧ r.nAcc = st.2) ∧ (r.s = st'.1 ∧ r.nAccNext = st'.2) ∧
    (r.bit0 = bs[0] ∧ r.bit1 = bs[1] ∧ r.bit2 = bs[2] ∧ r.bit3 = bs[3])

/-- Every round of a trace reads the same base. -/
private theorem threads_base {t : AffinePoint (FVar F)} :
    ∀ {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 4)}
      {rounds : List (EndoMulRound F)},
      Chain (Threads t) st pref rounds fin → ∀ r ∈ rounds, r.t = t
  | _, _, [], _, h, r, hr => by rw [h.1] at hr; simp at hr
  | _, _, _ :: _, _, h, r, hr => by
    obtain ⟨r', tail, mid, rfl, hgrant, hrest⟩ := h
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hgrant.1
    · exact threads_base hrest r hr

/-- A trace's first round opens at the seed accumulators. -/
private theorem threads_head {t : AffinePoint (FVar F)} :
    ∀ {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 4)}
      {r₀ : EndoMulRound F} {rs : List (EndoMulRound F)},
      Chain (Threads t) st pref (r₀ :: rs) fin → r₀.p = st.1 ∧ r₀.nAcc = st.2
  | _, _, [], _, _, h => by exact absurd h.1 (by simp)
  | _, _, _ :: _, _, _, h => by
    obtain ⟨r', tail, mid, heq, hgrant, -⟩ := h
    injection heq with hr _
    subst hr
    exact hgrant.2.1

/-- A trace's rounds are as many as the rows it traversed. -/
private theorem threads_length {t : AffinePoint (FVar F)} :
    ∀ {st fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 4)}
      {rounds : List (EndoMulRound F)},
      Chain (Threads t) st pref rounds fin → rounds.length = pref.length
  | _, _, [], _, h => by rw [h.1]; rfl
  | _, _, _ :: _, _, h => by
    obtain ⟨r', tail, mid, rfl, -, hrest⟩ := h
    rw [List.length_cons, List.length_cons, threads_length hrest]

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
is a run (`Chain.ofList`), so `endoMul_off` gives the final accumulator as a multiple of
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
      ∃ (hfin : d.W.Nonsingular (fin.1.x.val V) (fin.1.y.val V)) (s : ℤ),
        Point.some _ _ hfin = s • Point.some _ _ hT ∧
        (s : F) = Kimchi.Gate.EndoScalar.toField crumbs (d.lam : F) := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have hφT := d.endo_nonsingular hT
  match hround : rounds, hthr with
  | [], hthr' =>
    obtain ⟨rfl, rfl⟩ := Chain.of_nil_out hthr'
    refine ⟨[], by simp, by simp, ?_, hP0ns, 2 + 2 * d.lam, ?_, ?_⟩
    · simp [Kimchi.Gate.EndoScalar.nReconstruct, CVar.val]
    · rw [hP0, d.eigen hT hφT, smul_smul, add_smul]
    · simp [Kimchi.Gate.EndoScalar.toField, Kimchi.Gate.EndoScalar.decomposeA,
        Kimchi.Gate.EndoScalar.decomposeB, Kimchi.Gate.EndoScalar.decomposeFold]
      push_cast
      ring
  | r₀ :: rs, hthr' =>
    subst hround
    set finV : F × F × F := (fin.1.x.val V, fin.1.y.val V, fin.2.val V) with hfinV
    set l := EndoMul.readChain V finV (r₀ :: rs) with hl
    have hne : l ≠ [] := by
      simp only [hl, EndoMul.readChain]
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
    have hhead := hbaseAll _ (List.getElem_mem (by omega) : l[0]'(by omega) ∈ l)
    have hget0 : l.getD 0 (l.head hne) = l[0]'(by omega) :=
      List.getD_eq_getElem _ _ (by omega)
    have hchain : Kimchi.Gate.EndoMul.Chain d.endo g l.length :=
      Kimchi.Gate.EndoMul.Chain.ofList d.endo l (l.head hne)
        (fun w hw => EndoMul.readChain_holds hpay w hw)
        (fun w hw => by
          rw [(hbaseAll w hw).1, (hbaseAll w hw).2, hget0, hhead.1, hhead.2]
          exact ⟨rfl, rfl⟩)
        (EndoMul.readChain_link V finV (r₀ :: rs))
    -- the run's first row is round `r₀`, so its base and seed cells are the trace's
    obtain ⟨h0xT, h0yT, h0xP, h0yP, h0n⟩ :=
      EndoMul.readChain_head V finV (l.head hne) r₀ rs
    obtain ⟨hp0, hn0⟩ := EndoMul.threads_head hthr'
    have hbase0x : (g 0).xT = t.x.val V := by
      show (l.getD 0 (l.head hne)).xT = _
      rw [hl] at *
      rw [h0xT, EndoMul.threads_base hthr' r₀ (by simp)]
    have hbase0y : (g 0).yT = t.y.val V := by
      show (l.getD 0 (l.head hne)).yT = _
      rw [hl] at *
      rw [h0yT, EndoMul.threads_base hthr' r₀ (by simp)]
    have hbase0P : (g 0).xP = P0.x.val V ∧ (g 0).yP = P0.y.val V := by
      constructor
      · show (l.getD 0 (l.head hne)).xP = _
        rw [hl] at *
        rw [h0xP, hp0]
      · show (l.getD 0 (l.head hne)).yP = _
        rw [hl] at *
        rw [h0yP, hp0]
    have hTns : d.W.Nonsingular (g 0).xT (g 0).yT := by
      rw [hbase0x, hbase0y]; exact hT
    have hφTns : d.W.Nonsingular (d.endo * (g 0).xT) (g 0).yT := by
      rw [hbase0x, hbase0y]; exact hφT
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
          omega) g hchain hTns
        (Kimchi.Gate.EndoMul.some_congr d.W hT hTns hbase0x.symm hbase0y.symm)
        hφTns
        (Kimchi.Gate.EndoMul.some_congr d.W hφT hφTns
          (by rw [hbase0x]) hbase0y.symm)
        hP0ns'
        ((Kimchi.Gate.EndoMul.some_congr d.W hP0ns' hP0ns
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
      rw [← hfinn, Kimchi.Gate.EndoMul.chain_nAcc d.endo l.length g hchain, hzero,
        zero_mul, zero_add]
    refine ⟨Kimchi.Gate.EndoMul.crumbList g l.length,
      Kimchi.Gate.EndoMul.crumbList_valid d.endo l.length g hchain.holds,
      ?_, hreg, hfin, sc, ?_, hsval⟩
    · rw [Kimchi.Gate.EndoMul.crumbList_length, hlen, ← EndoMul.threads_length hthr']
      simp
    · exact (Kimchi.Gate.EndoMul.some_congr d.W hfin hfin' hfinx.symm hfiny.symm).trans hseq

open Kimchi.Gate.VarBaseMul (y_ne_zero_of_odd_order) in
open Std.Do WeierstrassCurve.Affine in
/-- **Soundness.** Any satisfying valuation reads the result as the base multiplied by
the effective scalar of some valid crumb list of the run's width, whose reconstruction
is the scalar the wrapper pinned. -/
theorem endoMul_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (d : HasEndo F) (rounds : ℕ) (hbits : 4 * rounds ≤ 244)
    (t : AffinePoint (FVar F)) (scalar : SizedF (4 * rounds) (FVar F)) :
    ⦃⌜True⌝⦄
    Snarky.Kimchi.endoMul (c := Builder V (KimchiConstraint F)) d.endo rounds t scalar
    ⦃⇓ r _ => ⌜∀ hT : d.W.Nonsingular (t.x.val V) (t.y.val V),
      ∃ crumbs : List F,
        (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
        crumbs.length = 2 * rounds ∧
        scalar.val.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs ∧
        ∃ (hfin : d.W.Nonsingular (r.x.val V) (r.y.val V)) (s : ℤ),
          Point.some _ _ hfin = s • Point.some _ _ hT ∧
          (s : F) = Kimchi.Gate.EndoScalar.toField crumbs (d.lam : F)⌝⦄ := by
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
  intro hT
  have hφT := d.endo_nonsingular hT
  have hy : t.y.val V ≠ 0 := y_ne_zero_of_odd_order d.W d.odd hT
  have hφTp : d.W.Nonsingular (phix.val V) (t.y.val V) := by
    rw [hphix, CVar.val_scale_]
    exact hφT
  obtain ⟨hP1, hsum1⟩ : ∃ h3 : d.W.Nonsingular (p1.p.x.val V) (p1.p.y.val V),
      Point.some _ _ hT + Point.some _ _ hφTp = Point.some _ _ h3 := by
    rcases hp1.2 hT hφTp hy with ⟨hinf, -⟩ | ⟨-, h3, hsum⟩
    · exact absurd ((hp1.1 rfl).symm.trans hinf) (by norm_num)
    · exact ⟨h3, hsum⟩
  have hy1 : p1.p.y.val V ≠ 0 := y_ne_zero_of_odd_order d.W d.odd hP1
  obtain ⟨hP0ns, hsum2⟩ : ∃ h3 : d.W.Nonsingular (p2.p.x.val V) (p2.p.y.val V),
      Point.some _ _ hP1 + Point.some _ _ hP1 = Point.some _ _ h3 := by
    rcases hp2.2 hP1 hP1 hy1 with ⟨hinf, -⟩ | ⟨-, h3, hsum⟩
    · exact absurd (hp2.1.symm.trans hinf) (by norm_num)
    · exact ⟨h3, hsum⟩
  have hφeq : Point.some _ _ hφTp = Point.some _ _ hφT :=
    Kimchi.Gate.EndoMul.some_congr d.W hφTp hφT (by rw [hphix, CVar.val_scale_]) rfl
  have hP0 : Point.some _ _ hP0ns
      = (2 : ℤ) • Point.some _ _ hT + (2 : ℤ) • Point.some _ _ hφT := by
    rw [← hsum2, ← hsum1, hφeq]
    module
  obtain ⟨crumbs, hvalid, hlen, hreg, hfin, sc, hseq, hsval⟩ :=
    chain_sound d V (by simpa using hbits) hchainT hpay hT hP0ns hP0
  exact ⟨crumbs, hvalid, by simpa using hlen, heqScalar.symm.trans hreg, hfin, sc, hseq, hsval⟩

end EndoMul

end Snarky.Kimchi
