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

open WeierstrassCurve.Affine in
/-- No point of the group is 2-torsion: the order is an odd prime, so doubling kills only
zero. This is what the addition gadget asks of its first operand, and it holds of every
point the dictionary describes. -/
theorem HasEndo.two_torsion_free [Field F] [DecidableEq F] (d : HasEndo F)
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
@[reducible] def HasEndo.vesta : HasEndo Fq where
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
    have hchain : Kimchi.Gate.EndoMul.Chain d.W d.endo
        (Point.some _ _ hT) (Point.some _ _ hφT) g l.length :=
      Kimchi.Gate.EndoMul.Chain.ofList d.W d.endo _ _ l (l.head hne)
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
          omega) g hchain
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
      rw [← hfinn, Kimchi.Gate.EndoMul.chain_nAcc d.W d.endo _ _ l.length g hchain, hzero,
        zero_mul, zero_add]
    refine ⟨Kimchi.Gate.EndoMul.crumbList g l.length,
      Kimchi.Gate.EndoMul.crumbList_valid d.endo l.length g hchain.holds,
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

/-! ## Completeness

The loop emits no row of its own — a round only witnesses its advice — so the ladder's
completeness needs nothing of the accumulator but that it is readable. Every row is
judged at the one `endoMul` constraint after the loop, and what discharges it is the
model's `chain_complete` on the honest walk, which the run's readings are shown to be. -/

/-- The rows the ladder is handed: four bit variables in scope. -/
private def BitRow (st₁ : ProverState F) (bs : Vector (FVar F) 4) : Prop :=
  ∀ v ∈ bs.toList, v.Scoped st₁

/-- The ladder's accumulator invariant: the table has only grown since the bits were
witnessed, and the accumulator's three variables are in scope. -/
private def AccInv (st₁ : ProverState F) (acc : AffinePoint (FVar F) × FVar F)
    (st : ProverState F) : Prop :=
  (st₁.nv ≤ st.nv ∧ st₁.env.Le st.env) ∧
    acc.1.x.Scoped st ∧ acc.1.y.Scoped st ∧ acc.2.Scoped st

/-- A round's cells. -/
private def cells (r : EndoMulRound F) : List (CVar F) :=
  [r.t.x, r.t.y, r.p.x, r.p.y, r.nAcc, r.nAccNext, r.r.x, r.r.y, r.s.x, r.s.y,
    r.s1, r.s3, r.inv, r.bit0, r.bit1, r.bit2, r.bit3]

/-- The step's grant at a table: the round is wired to the base, the accumulators either
side and the row's bits; its cells are in scope; and its reading is the gate's canonical
row at its own inputs. -/
private def RowGrant [Field F] [DecidableEq F] (eb : F) (t : AffinePoint (FVar F))
    (acc : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 4) (r : EndoMulRound F)
    (acc' : AffinePoint (FVar F) × FVar F) (st : ProverState F) : Prop :=
  Threads t acc bs r acc' ∧ (∀ cv ∈ cells r, cv.Scoped st) ∧
    EndoMulRound.readWith st.env.get r (r.s.x.val st.env.get) (r.s.y.val st.env.get)
        (r.nAccNext.val st.env.get)
      = Kimchi.Gate.EndoMul.build eb (t.x.val st.env.get) (t.y.val st.env.get)
          (acc.1.x.val st.env.get) (acc.1.y.val st.env.get) (acc.2.val st.env.get)
          (bs[0].val st.env.get) (bs[1].val st.env.get) (bs[2].val st.env.get)
          (bs[3].val st.env.get)

/-- Scope and the table's growth survive further growth. -/
private theorem AccInv.mono [Field F] {st₁ : ProverState F}
    (acc : AffinePoint (FVar F) × FVar F) {st st' : ProverState F}
    (hnv : st.nv ≤ st'.nv) (hle : st.env.Le st'.env) (h : AccInv st₁ acc st) :
    AccInv st₁ acc st' :=
  ⟨⟨Nat.le_trans h.1.1 hnv, h.1.2.trans hle⟩,
    h.2.1.mono hnv, h.2.2.1.mono hnv, h.2.2.2.mono hnv⟩

/-- A row's grant survives the table's growth: the wiring says the operands are the
round's own cells, and those are in scope, so nothing in the reading moves. -/
private theorem RowGrant.mono [Field F] [DecidableEq F] (eb : F) (t : AffinePoint (FVar F))
    (acc : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 4) (r : EndoMulRound F)
    (acc' : AffinePoint (FVar F) × FVar F) {st st' : ProverState F}
    (hnv : st.nv ≤ st'.nv) (hle : st.env.Le st'.env)
    (h : RowGrant eb t acc bs r acc' st) : RowGrant eb t acc bs r acc' st' := by
  obtain ⟨hthr, hsc, hread⟩ := h
  obtain ⟨hrt, ⟨hrp, hrn⟩, hout, hb0, hb1, hb2, hb3⟩ := hthr
  refine ⟨⟨hrt, ⟨hrp, hrn⟩, hout, hb0, hb1, hb2, hb3⟩,
    fun cv hcv => (hsc cv hcv).mono hnv, ?_⟩
  have hcell : ∀ cv ∈ cells r, cv.val st'.env.get = cv.val st.env.get :=
    fun cv hcv => CVar.val_of_le hle (hsc cv hcv)
  have hread' : EndoMulRound.readWith st'.env.get r (r.s.x.val st'.env.get)
        (r.s.y.val st'.env.get) (r.nAccNext.val st'.env.get)
      = EndoMulRound.readWith st.env.get r (r.s.x.val st.env.get)
        (r.s.y.val st.env.get) (r.nAccNext.val st.env.get) := by
    simp only [EndoMulRound.readWith,
      hcell r.t.x (by simp [cells]),
      hcell r.t.y (by simp [cells]),
      hcell r.p.x (by simp [cells]),
      hcell r.p.y (by simp [cells]),
      hcell r.nAcc (by simp [cells]),
      hcell r.nAccNext (by simp [cells]),
      hcell r.r.x (by simp [cells]),
      hcell r.r.y (by simp [cells]),
      hcell r.s.x (by simp [cells]),
      hcell r.s.y (by simp [cells]),
      hcell r.s1 (by simp [cells]),
      hcell r.s3 (by simp [cells]),
      hcell r.inv (by simp [cells]),
      hcell r.bit0 (by simp [cells]),
      hcell r.bit1 (by simp [cells]),
      hcell r.bit2 (by simp [cells]),
      hcell r.bit3 (by simp [cells])]
  rw [hread', hread, ← hrt, ← hrp, ← hrn, ← hb0, ← hb1, ← hb2, ← hb3,
    hcell r.t.x (by simp [cells]), hcell r.t.y (by simp [cells]),
    hcell r.p.x (by simp [cells]), hcell r.p.y (by simp [cells]),
    hcell r.nAcc (by simp [cells]), hcell r.bit0 (by simp [cells]),
    hcell r.bit1 (by simp [cells]), hcell r.bit2 (by simp [cells]),
    hcell r.bit3 (by simp [cells])]

/-- The step's completeness: the round's advice is the gate's canonical row at the
accumulators it was handed, so the run succeeds and its reading is that row. -/
private theorem endoMulRound_complete [Field F] [DecidableEq F] (st₁ : ProverState F)
    (eb : F) (t : AffinePoint (FVar F)) (ht : t.x.Scoped st₁ ∧ t.y.Scoped st₁)
    (acc : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 4) (hbs : BitRow st₁ bs) :
    Complete (F := F) (c := KimchiConstraint F) (AccInv st₁ acc)
      (Snarky.Kimchi.endoMulRound (c := KimchiConstraint F) eb t acc bs)
      (fun p st' => AccInv st₁ p.2 st' ∧ RowGrant eb t acc bs p.1 p.2 st') := by
  simp only [endoMulRound]
  -- the nine cell readings at the entry table index the law
  refine Complete.instantiate
    (ι := F × F × F × F × F × F × F × F × F)
    (P := fun v st => (st₁.nv ≤ st.nv ∧ st₁.env.Le st.env) ∧
      CircuitType.ReadsAs (val := F) st t.x v.1 ∧
      CircuitType.ReadsAs (val := F) st t.y v.2.1 ∧
      CircuitType.ReadsAs (val := F) st acc.1.x v.2.2.1 ∧
      CircuitType.ReadsAs (val := F) st acc.1.y v.2.2.2.1 ∧
      CircuitType.ReadsAs (val := F) st acc.2 v.2.2.2.2.1 ∧
      CircuitType.ReadsAs (val := F) st (bs[0]'(by omega)) v.2.2.2.2.2.1 ∧
      CircuitType.ReadsAs (val := F) st (bs[1]'(by omega)) v.2.2.2.2.2.2.1 ∧
      CircuitType.ReadsAs (val := F) st (bs[2]'(by omega)) v.2.2.2.2.2.2.2.1 ∧
      CircuitType.ReadsAs (val := F) st (bs[3]'(by omega)) v.2.2.2.2.2.2.2.2)
    (fun st h => ?_) fun v => ?_
  · have hb : ∀ (i : ℕ) (hi : i < 4), (bs[i]'hi).Scoped st :=
      fun i hi => (hbs _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))).mono h.1.1
    exact ⟨(t.x.val st.env.get, t.y.val st.env.get, acc.1.x.val st.env.get,
        acc.1.y.val st.env.get, acc.2.val st.env.get, (bs[0]'(by omega)).val st.env.get,
        (bs[1]'(by omega)).val st.env.get, (bs[2]'(by omega)).val st.env.get,
        (bs[3]'(by omega)).val st.env.get),
      h.1,
      ⟨CircuitType.scoped_fvar.mpr (ht.1.mono h.1.1), CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (ht.2.mono h.1.1), CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr h.2.1, CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr h.2.2.1, CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr h.2.2.2, CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (hb 0 (by omega)), CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (hb 1 (by omega)), CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (hb 2 (by omega)), CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (hb 3 (by omega)), CircuitType.reads_fvar.mpr rfl⟩⟩
  obtain ⟨xt, yt, xp, yp, n, b1, b2, b3, b4⟩ := v
  set W := Kimchi.Gate.EndoMul.build eb xt yt xp yp n b1 b2 b3 b4 with hW
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?run, h⟩) (fun _ _ h => h)
      (Complete.frame
        (Mono.and (fun _ _ hnv hle h => ⟨Nat.le_trans h.1 hnv, h.2.trans hle⟩)
          (Mono.and Mono.readsAs (Mono.and Mono.readsAs (Mono.and Mono.readsAs
            (Mono.and Mono.readsAs (Mono.and Mono.readsAs (Mono.and Mono.readsAs
              (Mono.and Mono.readsAs (Mono.and Mono.readsAs Mono.readsAs)))))))))
        (Complete.witness (rowWit eb t bs acc)
          (W.inv, W.nPrime, W.xR, W.yR, W.xS, W.yS, W.s1, W.s3) (by simp))))
    fun w => Complete.pure_of fun st h => ?post
  case run =>
    simp only [rowWit, AsProver.bind_eq, AsProver.run_bind,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.1.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.2.1.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.2.2.1.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.2.2.2.1.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.2.2.2.2.1.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.2.2.2.2.2.1.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.2.2.2.2.2.2.1.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.2.2.2.2.2.2.2.1.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.2.2.2.2.2.2.2.2.1),
      CircuitType.reads_fvar.mp h.2.1.2, CircuitType.reads_fvar.mp h.2.2.1.2,
      CircuitType.reads_fvar.mp h.2.2.2.1.2, CircuitType.reads_fvar.mp h.2.2.2.2.1.2,
      CircuitType.reads_fvar.mp h.2.2.2.2.2.1.2,
      CircuitType.reads_fvar.mp h.2.2.2.2.2.2.1.2,
      CircuitType.reads_fvar.mp h.2.2.2.2.2.2.2.1.2,
      CircuitType.reads_fvar.mp h.2.2.2.2.2.2.2.2.1.2,
      CircuitType.reads_fvar.mp h.2.2.2.2.2.2.2.2.2.2, Except.bind, ← hW]
    rfl
  case post =>
    obtain ⟨inv, nPrime, xR, yR, xS, yS, s1, s3⟩ := w
    obtain ⟨⟨hscW, hrdW⟩, hP⟩ := h
    simp only [CircuitType.scoped_prod, CircuitType.scoped_fvar] at hscW
    simp only [CircuitType.reads_prod, CircuitType.reads_fvar] at hrdW
    refine ⟨⟨hP.1, hscW.2.2.2.2.1, hscW.2.2.2.2.2.1, hscW.2.1⟩,
      ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
    · intro cv hcv
      simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at hcv
      rcases hcv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      · exact CircuitType.scoped_fvar.mp hP.2.1.1
      · exact CircuitType.scoped_fvar.mp hP.2.2.1.1
      · exact CircuitType.scoped_fvar.mp hP.2.2.2.1.1
      · exact CircuitType.scoped_fvar.mp hP.2.2.2.2.1.1
      · exact CircuitType.scoped_fvar.mp hP.2.2.2.2.2.1.1
      · exact hscW.2.1
      · exact hscW.2.2.1
      · exact hscW.2.2.2.1
      · exact hscW.2.2.2.2.1
      · exact hscW.2.2.2.2.2.1
      · exact hscW.2.2.2.2.2.2.1
      · exact hscW.2.2.2.2.2.2.2
      · exact hscW.1
      · exact CircuitType.scoped_fvar.mp hP.2.2.2.2.2.2.1.1
      · exact CircuitType.scoped_fvar.mp hP.2.2.2.2.2.2.2.1.1
      · exact CircuitType.scoped_fvar.mp hP.2.2.2.2.2.2.2.2.1.1
      · exact CircuitType.scoped_fvar.mp hP.2.2.2.2.2.2.2.2.2.1
    · simp only [EndoMulRound.readWith, hrdW.1, hrdW.2.1, hrdW.2.2.1, hrdW.2.2.2.1,
        hrdW.2.2.2.2.1, hrdW.2.2.2.2.2.1, hrdW.2.2.2.2.2.2.1, hrdW.2.2.2.2.2.2.2,
        CircuitType.reads_fvar.mp hP.2.1.2, CircuitType.reads_fvar.mp hP.2.2.1.2,
        CircuitType.reads_fvar.mp hP.2.2.2.1.2, CircuitType.reads_fvar.mp hP.2.2.2.2.1.2,
        CircuitType.reads_fvar.mp hP.2.2.2.2.2.1.2,
        CircuitType.reads_fvar.mp hP.2.2.2.2.2.2.1.2,
        CircuitType.reads_fvar.mp hP.2.2.2.2.2.2.2.1.2,
        CircuitType.reads_fvar.mp hP.2.2.2.2.2.2.2.2.1.2,
        CircuitType.reads_fvar.mp hP.2.2.2.2.2.2.2.2.2.2]
      rw [hW]
      rfl

/-- A trace with no rounds traversed no rows. -/
private theorem ChainAt.of_nil_out [Field F] [DecidableEq F] {eb : F}
    {t : AffinePoint (FVar F)} {stf : ProverState F} :
    ∀ {acc fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 4)},
      ChainAt (RowGrant eb t) stf acc pref [] fin → pref = [] ∧ acc = fin
  | _, _, [], h => ⟨rfl, h.2⟩
  | _, _, _ :: _, h => by
    obtain ⟨y, ys', -, heq, -, -⟩ := h
    exact nomatch heq

/-- A trace's first round opens at the accumulators it was given. -/
private theorem chainAt_head [Field F] [DecidableEq F] {eb : F} {t : AffinePoint (FVar F)}
    {stf : ProverState F} :
    ∀ {acc fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 4)}
      {r₀ : EndoMulRound F} {rs : List (EndoMulRound F)},
      ChainAt (RowGrant eb t) stf acc pref (r₀ :: rs) fin →
      r₀.p = acc.1 ∧ r₀.nAcc = acc.2
  | _, _, [], _, _, h => absurd h.1 (by simp)
  | _, _, _ :: _, _, _, h => by
    obtain ⟨r, tail, mid, heq, hgrant, -⟩ := h
    injection heq with hr _
    subst hr
    exact hgrant.1.2.1

/-- The trace's readings are the model's honest walk: round `i` reads as `chainBuild`'s
row `i`, from the accumulator the trace opened on and the bits it was handed. -/
private theorem grants_walk [Field F] [DecidableEq F] (eb : F) (t : AffinePoint (FVar F))
    (stf : ProverState F) :
    ∀ {bs : ℕ → F × F × F × F} {acc fin : AffinePoint (FVar F) × FVar F}
      {pref : List (Vector (FVar F) 4)} {rounds : List (EndoMulRound F)},
      ChainAt (RowGrant eb t) stf acc pref rounds fin →
      (∀ i (hi : i < pref.length),
        (((pref[i]'hi)[0]'(by omega)).val stf.env.get,
          ((pref[i]'hi)[1]'(by omega)).val stf.env.get,
          ((pref[i]'hi)[2]'(by omega)).val stf.env.get,
          ((pref[i]'hi)[3]'(by omega)).val stf.env.get) = bs i) →
      ∀ i (hi : i < rounds.length),
        EndoMulRound.readWith stf.env.get (rounds[i]'hi)
            ((rounds[i]'hi).s.x.val stf.env.get) ((rounds[i]'hi).s.y.val stf.env.get)
            ((rounds[i]'hi).nAccNext.val stf.env.get)
          = Kimchi.Gate.EndoMul.chainBuild eb (t.x.val stf.env.get) (t.y.val stf.env.get)
              (acc.1.x.val stf.env.get) (acc.1.y.val stf.env.get) (acc.2.val stf.env.get) bs i
  | _, _, _, [], _, h, _, i, hi => by
    obtain ⟨rfl, -⟩ := h
    simp at hi
  | bs, acc, fin, x :: rest, rounds, h, hbits, i, hi => by
    obtain ⟨r, tail, mid, rfl, ⟨⟨hrt, ⟨hrp, hrn⟩, ⟨hrs, hrnn⟩, hb0, hb1, hb2, hb3⟩, -, hread⟩,
      hrest⟩ := h
    have hrow : EndoMulRound.readWith stf.env.get r (r.s.x.val stf.env.get)
        (r.s.y.val stf.env.get) (r.nAccNext.val stf.env.get)
        = Kimchi.Gate.EndoMul.chainBuild eb (t.x.val stf.env.get) (t.y.val stf.env.get)
            (acc.1.x.val stf.env.get) (acc.1.y.val stf.env.get) (acc.2.val stf.env.get) bs 0 := by
      rw [hread]
      show _ = Kimchi.Gate.EndoMul.build _ _ _ _ _ _ (bs 0).1 (bs 0).2.1 (bs 0).2.2.1 (bs 0).2.2.2
      rw [← hbits 0 (by simp)]
      rfl
    cases i with
    | zero => exact hrow
    | succ j =>
      have hj : j < tail.length := by simpa using hi
      have hshift := grants_walk eb t stf hrest
        (fun k hk => hbits (k + 1) (by simpa using hk)) j hj
      have hxS : (Kimchi.Gate.EndoMul.chainBuild eb (t.x.val stf.env.get)
            (t.y.val stf.env.get) (acc.1.x.val stf.env.get) (acc.1.y.val stf.env.get)
            (acc.2.val stf.env.get) bs 0).xS = mid.1.x.val stf.env.get := by
        rw [← hrow]
        show r.s.x.val stf.env.get = _
        rw [hrs]
      have hyS : (Kimchi.Gate.EndoMul.chainBuild eb (t.x.val stf.env.get)
            (t.y.val stf.env.get) (acc.1.x.val stf.env.get) (acc.1.y.val stf.env.get)
            (acc.2.val stf.env.get) bs 0).yS = mid.1.y.val stf.env.get := by
        rw [← hrow]
        show r.s.y.val stf.env.get = _
        rw [hrs]
      have hnP : (Kimchi.Gate.EndoMul.chainBuild eb (t.x.val stf.env.get)
            (t.y.val stf.env.get) (acc.1.x.val stf.env.get) (acc.1.y.val stf.env.get)
            (acc.2.val stf.env.get) bs 0).nPrime = mid.2.val stf.env.get := by
        rw [← hrow]
        show r.nAccNext.val stf.env.get = _
        rw [hrnn]
      rw [show ((r :: tail)[j + 1]'hi) = tail[j]'hj from rfl, hshift,
        Kimchi.Gate.EndoMul.chainBuild_shift, hxS, hyS, hnP]

/-- The trace closes where the walk does: the final accumulator reads as the walk's
accumulator after as many rows as were traversed. -/
private theorem grants_fin [Field F] [DecidableEq F] (eb : F) (t : AffinePoint (FVar F))
    (stf : ProverState F) :
    ∀ {bs : ℕ → F × F × F × F} {acc fin : AffinePoint (FVar F) × FVar F}
      {pref : List (Vector (FVar F) 4)} {rounds : List (EndoMulRound F)},
      ChainAt (RowGrant eb t) stf acc pref rounds fin →
      (∀ i (hi : i < pref.length),
        (((pref[i]'hi)[0]'(by omega)).val stf.env.get,
          ((pref[i]'hi)[1]'(by omega)).val stf.env.get,
          ((pref[i]'hi)[2]'(by omega)).val stf.env.get,
          ((pref[i]'hi)[3]'(by omega)).val stf.env.get) = bs i) →
      fin.1.x.val stf.env.get
          = Kimchi.Gate.EndoMul.accX (Kimchi.Gate.EndoMul.chainBuild eb
              (t.x.val stf.env.get) (t.y.val stf.env.get) (acc.1.x.val stf.env.get)
              (acc.1.y.val stf.env.get) (acc.2.val stf.env.get) bs) pref.length
        ∧ fin.1.y.val stf.env.get
          = Kimchi.Gate.EndoMul.accY (Kimchi.Gate.EndoMul.chainBuild eb
              (t.x.val stf.env.get) (t.y.val stf.env.get) (acc.1.x.val stf.env.get)
              (acc.1.y.val stf.env.get) (acc.2.val stf.env.get) bs) pref.length
        ∧ fin.2.val stf.env.get
          = Kimchi.Gate.EndoMul.accN (Kimchi.Gate.EndoMul.chainBuild eb
              (t.x.val stf.env.get) (t.y.val stf.env.get) (acc.1.x.val stf.env.get)
              (acc.1.y.val stf.env.get) (acc.2.val stf.env.get) bs) pref.length
  | _, _, _, [], _, h, _ => by
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  | bs, acc, fin, x :: rest, rounds, h, hbits => by
    obtain ⟨r, tail, mid, rfl, hgrant, hrest⟩ := h
    obtain ⟨hrt, ⟨hrp, hrn⟩, ⟨hrs, hrnn⟩, hb0, hb1, hb2, hb3⟩ := hgrant.1
    have hrow : EndoMulRound.readWith stf.env.get r (r.s.x.val stf.env.get)
        (r.s.y.val stf.env.get) (r.nAccNext.val stf.env.get)
        = Kimchi.Gate.EndoMul.chainBuild eb (t.x.val stf.env.get) (t.y.val stf.env.get)
            (acc.1.x.val stf.env.get) (acc.1.y.val stf.env.get) (acc.2.val stf.env.get) bs 0 := by
      rw [hgrant.2.2]
      show _ = Kimchi.Gate.EndoMul.build _ _ _ _ _ _ (bs 0).1 (bs 0).2.1 (bs 0).2.2.1 (bs 0).2.2.2
      rw [← hbits 0 (by simp)]
      rfl
    have hmx : mid.1.x.val stf.env.get
        = (Kimchi.Gate.EndoMul.chainBuild eb (t.x.val stf.env.get) (t.y.val stf.env.get)
            (acc.1.x.val stf.env.get) (acc.1.y.val stf.env.get) (acc.2.val stf.env.get)
              bs 0).xS := by
      rw [← hrow]
      show _ = r.s.x.val stf.env.get
      rw [hrs]
    have hmy : mid.1.y.val stf.env.get
        = (Kimchi.Gate.EndoMul.chainBuild eb (t.x.val stf.env.get) (t.y.val stf.env.get)
            (acc.1.x.val stf.env.get) (acc.1.y.val stf.env.get) (acc.2.val stf.env.get)
              bs 0).yS := by
      rw [← hrow]
      show _ = r.s.y.val stf.env.get
      rw [hrs]
    have hmn : mid.2.val stf.env.get
        = (Kimchi.Gate.EndoMul.chainBuild eb (t.x.val stf.env.get) (t.y.val stf.env.get)
            (acc.1.x.val stf.env.get) (acc.1.y.val stf.env.get) (acc.2.val stf.env.get)
              bs 0).nPrime := by
      rw [← hrow]
      show _ = r.nAccNext.val stf.env.get
      rw [hrnn]
    obtain ⟨hx, hy, hn⟩ := grants_fin eb t stf (bs := fun n => bs (n + 1)) hrest
      (fun k hk => hbits (k + 1) (by simpa using hk))
    rw [hx, hy, hn, hmx, hmy, hmn]
    refine ⟨?_, ?_, ?_⟩ <;>
      cases rest with
      | nil => rfl
      | cons a l =>
        simp only [List.length_cons, Kimchi.Gate.EndoMul.accX, Kimchi.Gate.EndoMul.accY,
          Kimchi.Gate.EndoMul.accN, Kimchi.Gate.EndoMul.chainBuild_shift]

/-- The payload holds: the constraint reads each row's outputs off the next round, the
trace's threading says those are the row's own, and every row of the walk holds. -/
private theorem chainHolds_of_walk [Field F] [DecidableEq F] (eb : F)
    (t : AffinePoint (FVar F)) (stf : ProverState F) (W : ℕ → Kimchi.Gate.EndoMul.Witness F) :
    ∀ {acc fin : AffinePoint (FVar F) × FVar F} {pref : List (Vector (FVar F) 4)}
      {rounds : List (EndoMulRound F)},
      ChainAt (RowGrant eb t) stf acc pref rounds fin →
      (∀ i (hi : i < rounds.length),
        EndoMulRound.readWith stf.env.get (rounds[i]'hi)
            ((rounds[i]'hi).s.x.val stf.env.get) ((rounds[i]'hi).s.y.val stf.env.get)
            ((rounds[i]'hi).nAccNext.val stf.env.get) = W i) →
      (∀ i, i < rounds.length → Kimchi.Gate.EndoMul.Holds eb (W i)) →
      EndoMul.chainHolds stf.env.get eb
        (fin.1.x.val stf.env.get, fin.1.y.val stf.env.get, fin.2.val stf.env.get) rounds
  | _, _, [], _, h, _, _ => by
    obtain ⟨rfl, -⟩ := h
    trivial
  | acc, fin, x :: rest, rounds, h, hwalk, hholds => by
    obtain ⟨r, tail, mid, rfl, hgrant, hrest⟩ := h
    obtain ⟨hrt, ⟨hrp, hrn⟩, ⟨hrs, hrnn⟩, -⟩ := hgrant.1
    match tail, hrest with
    | [], hrest' =>
      obtain ⟨-, hmid⟩ := ChainAt.of_nil_out hrest'
      have h0 := hwalk 0 (by simp)
      simp only [List.getElem_cons_zero] at h0
      show Kimchi.Gate.EndoMul.Holds eb _
      rw [← hmid, show (mid.1.x.val stf.env.get) = r.s.x.val stf.env.get by rw [hrs],
        show (mid.1.y.val stf.env.get) = r.s.y.val stf.env.get by rw [hrs],
        show (mid.2.val stf.env.get) = r.nAccNext.val stf.env.get by rw [hrnn], h0]
      exact hholds 0 (by simp)
    | r' :: ts, hrest' =>
      obtain ⟨hr'p, hr'n⟩ := chainAt_head hrest'
      have h0 := hwalk 0 (by simp)
      simp only [List.getElem_cons_zero] at h0
      refine ⟨?_, ?_⟩
      · show Kimchi.Gate.EndoMul.Holds eb _
        rw [show (r'.p.x.val stf.env.get) = r.s.x.val stf.env.get by rw [hr'p, hrs],
          show (r'.p.y.val stf.env.get) = r.s.y.val stf.env.get by rw [hr'p, hrs],
          show (r'.nAcc.val stf.env.get) = r.nAccNext.val stf.env.get by rw [hr'n, hrnn], h0]
        exact hholds 0 (by simp)
      · exact chainHolds_of_walk eb t stf (fun i => W (i + 1)) hrest'
          (fun i hi => hwalk (i + 1) (by simpa using hi))
          (fun i hi => hholds (i + 1) (by simpa using hi))

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
challenge is 64 two-bit crumbs; `3·2^64 = 3·4^32` at 32 rounds) — IS the prechallenge's
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

open Kimchi.Gate.EndoScalar in
/-- **Completeness**, at the deployed thirty-two rounds — the sixty-four crumbs of a
128-bit challenge, the width PS's `toFieldPure` fixes in its `SizedF 128` operand. On a
base on the curve and a scalar faithful to a representative of that width the honest run
succeeds, and the result is the base multiplied by that representative's decoded integer —
the multiplier `endoMul_spec` names, in the same modulus-free currency. -/
theorem endoMul_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (d : HasEndo F) (t : AffinePoint (FVar F)) (scalar : SizedF 128 (FVar F))
    (xv yv sv : F) (hT : d.W.Nonsingular xv yv)
    (hfits : ToNat.toNat sv < 2 ^ 128) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => OnCurveAs d.W st t (Point.some _ _ hT) ∧
        CircuitType.ReadsAs (val := F) st scalar.val sv)
      (Snarky.Kimchi.endoMul (c := KimchiConstraint F) d.endo 32 t scalar)
      (fun r st' => OnCurveAs d.W st' r
        (endoExpandZ d.lam (ToNat.toNat sv) • Point.some _ _ hT)) := by
  have hbits : 4 * 32 ≤ 244 := by norm_num
  replace hfits : ToNat.toNat sv < 4 ^ (2 * 32) := by norm_num; omega
  have h4 : (3 : ℤ) * 4 ^ 32 = 3 * 2 ^ 64 := by norm_num
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have hφT := d.endo_nonsingular hT
  -- the base's coordinates read off any on-curve state
  have htcoords : ∀ {st : ProverState F},
      OnCurveAs d.W st t (Point.some _ _ hT) →
        t.x.val st.env.get = xv ∧ t.y.val st.env.get = yv :=
    fun h => Kimchi.Gate.AddComplete.IsPoint.coords_eq h.2 ⟨hT, rfl⟩
  -- `T + φT` is finite: `[1 + λ]` does not kill `T`
  have hTφ : Point.some _ _ hT + Point.some _ _ hφT ≠ 0 := by
    intro hzero
    rw [d.eigen hT hφT] at hzero
    exact d.lam_succ_smul (Point.some _ _ hT) (Point.some_ne_zero hT)
      (by rw [← hzero]; module)
  have h2P1 : Point.some _ _ hT + Point.some _ _ hφT
      + (Point.some _ _ hT + Point.some _ _ hφT) ≠ 0 := d.two_torsion_free _ hTφ
  have hbsval : ∀ i, ((bitsOf (F := F) 32 (ToNat.toNat sv) i).1 = 0 ∨
        (bitsOf (F := F) 32 (ToNat.toNat sv) i).1 = 1) ∧
      ((bitsOf (F := F) 32 (ToNat.toNat sv) i).2.1 = 0 ∨
        (bitsOf (F := F) 32 (ToNat.toNat sv) i).2.1 = 1) ∧
      ((bitsOf (F := F) 32 (ToNat.toNat sv) i).2.2.1 = 0 ∨
        (bitsOf (F := F) 32 (ToNat.toNat sv) i).2.2.1 = 1) ∧
      ((bitsOf (F := F) 32 (ToNat.toNat sv) i).2.2.2 = 0 ∨
        (bitsOf (F := F) 32 (ToNat.toNat sv) i).2.2.2 = 1) := by
    intro i
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [bitsOf] <;> split <;> simp
  simp only [endoMul]
  -- the bulk bit witness
  refine Complete.seq (by complete_mono_tac)
    (Complete.imp
      (fun st h => by
        simp only [bitsWit, AsProver.bind_eq, AsProver.run_bind,
          AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.1),
          CircuitType.reads_fvar.mp h.2.2, Except.bind]
        rfl)
      (fun _ _ h => h)
      (Complete.witness (bitsWit 32 scalar.val)
        (Vector.ofFn fun r => Vector.ofFn fun j =>
          if (ToNat.toNat sv).testBit (4 * 32 - 1 - (4 * r.1 + j.1)) then 1 else 0)
        (by simp)))
    fun bits => ?_
  -- the bits' landing table indexes the rest of the run: the index carries the bit
  -- cells' scope and canonical readings, and the base's scope
  refine Complete.instantiate
    (ι := {st₁ : ProverState F //
      (∀ (i : ℕ) (hi : i < 32) (j : ℕ) (hj : j < 4),
        ((bits[i]'hi)[j]'hj).Scoped st₁ ∧
          ((bits[i]'hi)[j]'hj).val st₁.env.get
            = if (ToNat.toNat sv).testBit (4 * 32 - 1 - (4 * i + j)) then 1 else 0) ∧
      t.x.Scoped st₁ ∧ t.y.Scoped st₁})
    (P := fun i st => (i.1.nv ≤ st.nv ∧ i.1.env.Le st.env) ∧
      OnCurveAs d.W st t (Point.some _ _ hT) ∧
      CircuitType.ReadsAs (val := F) st scalar.val sv)
    (fun st h => ?inst1) fun i => ?_
  case inst1 =>
    refine ⟨⟨st, fun i hi j hj =>
        ⟨CircuitType.scoped_fvar.mp
          (CircuitType.scoped_vector.mp (CircuitType.scoped_vector.mp h.2.1 i hi) j hj),
          ?_⟩,
        (scoped_affinePoint.mp h.1.1.1).1, (scoped_affinePoint.mp h.1.1.1).2⟩,
      ⟨Nat.le_refl _, Assignments.Le.refl _⟩, h.1.1, h.1.2⟩
    have hv := CircuitType.reads_fvar.mp
      (CircuitType.reads_vector.mp (CircuitType.reads_vector.mp h.2.2 i hi) j hj)
    simpa using hv
  obtain ⟨st₁, hbitfacts, htx₁, hty₁⟩ := i
  have hextM : Mono (F := F) fun st => st₁.nv ≤ st.nv ∧ st₁.env.Le st.env :=
    fun _ _ hnv hle h => ⟨Nat.le_trans h.1 hnv, h.2.trans hle⟩
  -- the rows' bits, at any table past the witness
  have hbitsRead : ∀ (stf : ProverState F), st₁.env.Le stf.env →
      ∀ i (hi : i < bits.toList.length),
        (((bits.toList[i]'hi)[0]'(by omega)).val stf.env.get,
          ((bits.toList[i]'hi)[1]'(by omega)).val stf.env.get,
          ((bits.toList[i]'hi)[2]'(by omega)).val stf.env.get,
          ((bits.toList[i]'hi)[3]'(by omega)).val stf.env.get)
          = bitsOf (F := F) 32 (ToNat.toNat sv) i := by
    intro stf hlef i hi
    have hi' : i < 32 := by simpa using hi
    have hentry : ∀ (j : ℕ) (hj : j < 4),
        ((bits[i]'hi')[j]'hj).val stf.env.get
          = (if (ToNat.toNat sv).testBit (4 * 32 - 1 - (4 * i + j)) then 1 else 0) := by
      intro j hj
      rw [CVar.val_of_le hlef (hbitfacts i hi' j hj).1, (hbitfacts i hi' j hj).2]
    simp only [Vector.getElem_toList, bitsOf]
    rw [hentry 0 (by omega), hentry 1 (by omega), hentry 2 (by omega), hentry 3 (by omega)]
    simp
  have hP : ∀ x ∈ bits.toList, BitRow st₁ x := by
    intro x hx v hv
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
    obtain ⟨j, hj, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hv)
    exact (hbitfacts i hi j hj).1
  -- the sealed `β·x`: the bridge reads the scaled abscissa off the on-curve fact,
  -- and the walk pins the value through it
  have hscaleR : ∀ {st : ProverState F}, OnCurveAs d.W st t (Point.some _ _ hT) →
      CircuitType.ReadsAs (val := F) st (CVar.scale_ d.endo t.x) (d.endo * xv) :=
    fun h => ⟨CircuitType.scoped_fvar.mpr
        (CVar.Scoped.scale_ (scoped_affinePoint.mp h.1).1),
      CircuitType.reads_fvar.mpr (by rw [CVar.val_scale_, (htcoords h).1])⟩
  complete_walk
  -- the base's image, read as a curve point wherever `β·x` reads canonically
  have hφTread : ∀ {st : ProverState F},
      CircuitType.ReadsAs (val := F) st phix (d.endo * xv) →
      OnCurveAs d.W st t (Point.some _ _ hT) →
      OnCurveAs d.W st ⟨phix, t.y⟩ (Point.some _ _ hφT) := fun hp hOn =>
    ⟨scoped_affinePoint.mpr ⟨CircuitType.scoped_fvar.mp hp.1,
        (scoped_affinePoint.mp hOn.1).2⟩,
      OnCurveAt.of_reads (p := ⟨phix, t.y⟩) (CircuitType.reads_fvar.mp hp.2)
        (htcoords hOn).2 hφT⟩
  -- the first addition: `T + φT`, finite since `[1 + λ]` does not kill `T`
  refine Complete.bind
    (Complete.imp
      (fun st h => ⟨⟨h.1.2.1, hφTread h.2 h.1.2.1,
        d.two_torsion_free _ (Point.some_ne_zero hT), fun _ => hTφ⟩,
        h.1.1, h.1.2.1, h.1.2.2⟩)
      (fun _ _ h => h)
      (Complete.frame (Mono.and hextM (Mono.and Mono.onCurveAs Mono.readsAs))
        (addFast_complete .checkFinite d.W
          ⟨d.short.1, d.short.2.1, d.short.2.2.1, d.short.2.2.2⟩ d.two_ne t ⟨phix, t.y⟩
          (Point.some _ _ hT) (Point.some _ _ hφT))))
    fun p1 => ?_
  -- the second addition: the doubling
  refine Complete.bind
    (Complete.imp
      (fun st h => ⟨⟨h.1.2.2 hTφ, h.1.2.2 hTφ, h2P1, fun _ => h2P1⟩,
        h.2.1, h.2.2.1, h.2.2.2⟩)
      (fun _ _ h => h)
      (Complete.frame (Mono.and hextM (Mono.and Mono.onCurveAs Mono.readsAs))
        (addFast_complete .checkFinite d.W
          ⟨d.short.1, d.short.2.1, d.short.2.2.1, d.short.2.2.2⟩ d.two_ne p1.p p1.p
          (Point.some _ _ hT + Point.some _ _ hφT)
          (Point.some _ _ hT + Point.some _ _ hφT))))
    fun p2 => ?_
  -- the walk's seed coordinates index the rest, with the point they name on the index
  refine Complete.instantiate
    (ι := {q : F × F // ∃ h : d.W.Nonsingular q.1 q.2,
      Point.some _ _ hT + Point.some _ _ hφT
        + (Point.some _ _ hT + Point.some _ _ hφT) = Point.some q.1 q.2 h})
    (P := fun q st => (st₁.nv ≤ st.nv ∧ st₁.env.Le st.env) ∧
      CircuitType.ReadsAs (val := F) st p2.p.x q.1.1 ∧
      CircuitType.ReadsAs (val := F) st p2.p.y q.1.2 ∧
      OnCurveAs d.W st t (Point.some _ _ hT) ∧
      CircuitType.ReadsAs (val := F) st scalar.val sv)
    (fun st h => ⟨⟨(p2.p.x.val st.env.get, p2.p.y.val st.env.get), (h.1.2.2 h2P1).2⟩,
      h.2.1,
      ⟨CircuitType.scoped_fvar.mpr (scoped_affinePoint.mp (h.1.2.2 h2P1).1).1,
        CircuitType.reads_fvar.mpr rfl⟩,
      ⟨CircuitType.scoped_fvar.mpr (scoped_affinePoint.mp (h.1.2.2 h2P1).1).2,
        CircuitType.reads_fvar.mpr rfl⟩,
      h.2.2.1, h.2.2.2⟩)
    fun q => ?_
  obtain ⟨⟨x0, y0⟩, hP0ns, hP0eq'⟩ := q
  -- the walk the honest run is, and its value-level facts
  set W : ℕ → Kimchi.Gate.EndoMul.Witness F :=
    Kimchi.Gate.EndoMul.chainBuild d.endo xv yv x0 y0 0
      (bitsOf (F := F) 32 (ToNat.toNat sv)) with hWdef
  have hP0eq : Point.some _ _ hP0ns
      = (2 : ℤ) • Point.some _ _ hT + (2 : ℤ) • Point.some _ _ hφT := by
    rw [← hP0eq']
    module
  have hwalkHolds : ∀ i, i < 32 → Kimchi.Gate.EndoMul.Holds d.endo (W i) :=
    Kimchi.Gate.EndoMul.chain_complete d.W (Point.some _ _ hT) (Point.some _ _ hφT)
      (fun a b ha hb hba hbb =>
        d.off_targets ha hb hba hbb (Point.some_ne_zero hT) (d.eigen hT hφT))
      32 hbits hT hφT rfl rfl (bitsOf (F := F) 32 (ToNat.toNat sv)) hbsval 0 hP0ns hP0eq
  have hchainW : Kimchi.Gate.EndoMul.Chain d.W d.endo (Point.some _ _ hT)
      (Point.some _ _ hφT) W 32 := by
    refine ⟨hwalkHolds, fun i _ => ?_, fun i _ => ?_, fun i _ => ⟨rfl, rfl⟩,
      fun i _ => rfl⟩
    · cases i <;> exact ⟨hT, rfl⟩
    · cases i <;> exact ⟨hφT, rfl⟩
  have hlenB : bits.toList.length = 32 := by simp
  -- the register the ladder ends on is the scalar
  have hreg : Kimchi.Gate.EndoMul.accN W 32 = sv := by
    rw [Kimchi.Gate.EndoMul.chain_nAcc d.W d.endo _ _ 32 W hchainW,
      show Kimchi.Gate.EndoMul.accN W 0 = 0 from rfl, zero_mul, zero_add,
      Kimchi.Gate.EndoMul.crumbList_ofBits 32 (ToNat.toNat sv) W ?_,
      Kimchi.Gate.EndoScalar.nReconstruct_crumbsOf, Nat.mod_eq_of_lt hfits,
      LawfulToNat.cast_toNat]
    intro r _
    cases r <;> exact ⟨rfl, rfl, rfl, rfl⟩
  -- the trace's rows and finals are the walk's, wherever the seeds read canonically
  have hWat : ∀ (stf : ProverState F), t.x.val stf.env.get = xv →
      t.y.val stf.env.get = yv → p2.p.x.val stf.env.get = x0 →
      p2.p.y.val stf.env.get = y0 →
      Kimchi.Gate.EndoMul.chainBuild d.endo (t.x.val stf.env.get) (t.y.val stf.env.get)
          ((p2.p, (CVar.const 0 : FVar F)).1.x.val stf.env.get)
          ((p2.p, (CVar.const 0 : FVar F)).1.y.val stf.env.get)
          ((p2.p, (CVar.const 0 : FVar F)).2.val stf.env.get)
          (bitsOf (F := F) 32 (ToNat.toNat sv)) = W := by
    intro stf h1 h2 h3 h4
    show Kimchi.Gate.EndoMul.chainBuild d.endo (t.x.val stf.env.get) (t.y.val stf.env.get)
        (p2.p.x.val stf.env.get) (p2.p.y.val stf.env.get)
        ((CVar.const 0 : FVar F).val stf.env.get) _ = _
    rw [h1, h2, h3, h4, hWdef]
    rfl
  -- the ladder
  refine Complete.bind
    (Complete.imp
      (fun st h => ⟨⟨h.1, CircuitType.scoped_fvar.mp h.2.1.1,
        CircuitType.scoped_fvar.mp h.2.2.1.1, trivial⟩, h⟩)
      (fun _ _ h => h)
      (Complete.frame
        (Mono.and hextM (Mono.and Mono.readsAs (Mono.and Mono.readsAs
          (Mono.and Mono.onCurveAs Mono.readsAs))))
        (mapAccumM_complete (F := F) (c := KimchiConstraint F)
          (Snarky.Kimchi.endoMulRound d.endo t) (BitRow st₁) (fun _ => AccInv st₁)
          (RowGrant d.endo t) (fun _ => AccInv.mono) (RowGrant.mono d.endo t)
          (fun acc x _ hx => endoMulRound_complete st₁ d.endo t ⟨htx₁, hty₁⟩ acc x hx)
          (p2.p, .const 0) bits.toList hP)))
    fun loop => ?_
  obtain ⟨rounds, fin⟩ := loop
  -- the register pin
  refine Complete.bind
    (Complete.imp
      (fun st h => ⟨⟨⟨CircuitType.scoped_fvar.mpr h.1.1.2.2.2,
          CircuitType.reads_fvar.mpr ?pin⟩, h.2.2.2.2.2⟩, h⟩)
      (fun _ _ h => h)
      (Complete.frame
        (Mono.and (Mono.and (fun _ _ hnv hle h => AccInv.mono _ hnv hle h)
            (fun _ _ hnv hle h => ChainAt.mono (RowGrant.mono d.endo t) hnv hle h))
          (Mono.and hextM (Mono.and Mono.readsAs (Mono.and Mono.readsAs
            (Mono.and Mono.onCurveAs Mono.readsAs)))))
        (assertEqual_complete (c := KimchiConstraint F) fin.2 scalar.val sv)))
    fun _ => ?_
  case pin =>
    obtain ⟨⟨hinv, hchain⟩, hext, hp2x, hp2y, hOnT, hscal⟩ := h
    obtain ⟨-, -, hfn⟩ := grants_fin d.endo t st hchain (hbitsRead st hext.2)
    rw [hfn, hWat st (htcoords hOnT).1 (htcoords hOnT).2
      (CircuitType.reads_fvar.mp hp2x.2) (CircuitType.reads_fvar.mp hp2y.2), hlenB, hreg]
  -- the one `endoMul` row, and the returned accumulator
  refine Complete.bind (Complete.addConstraint ?row)
    fun _ => Complete.pure_of fun st h => ?post
  case row =>
    rintro st ⟨-, ⟨hinv, hchain⟩, hext, hp2x, hp2y, hOnT, hscal⟩ stf hle
    have hnv := ProverState.nv_le_of_env_le hle
    have hlenR : rounds.length = 32 := by rw [ChainAt.length hchain, hlenB]
    have hchain' := ChainAt.mono (RowGrant.mono d.endo t) hnv hle hchain
    have hOnT' := OnCurveAs.mono hnv hle hOnT
    have hp2x' := CircuitType.ReadsAs.mono hnv hle hp2x
    have hp2y' := CircuitType.ReadsAs.mono hnv hle hp2y
    have hwalk : ∀ i (hi : i < rounds.length),
        EndoMulRound.readWith stf.env.get (rounds[i]'hi)
            ((rounds[i]'hi).s.x.val stf.env.get) ((rounds[i]'hi).s.y.val stf.env.get)
            ((rounds[i]'hi).nAccNext.val stf.env.get) = W i := by
      intro i hi
      have hgw := grants_walk d.endo t stf hchain'
        (hbitsRead stf (hext.2.trans hle)) i hi
      rwa [hWat stf (htcoords hOnT').1 (htcoords hOnT').2
        (CircuitType.reads_fvar.mp hp2x'.2) (CircuitType.reads_fvar.mp hp2y'.2)] at hgw
    exact chainHolds_of_walk d.endo t stf W hchain' hwalk
      (fun i hi => hwalkHolds i (by rw [← hlenR]; exact hi))
  case post =>
    -- the point conclusion, off the model's own chain theorem
    obtain ⟨-, ⟨hinv, hchain⟩, hext, hp2x, hp2y, hOnT, hscal⟩ := h
    obtain ⟨hfx, hfy, -⟩ := grants_fin d.endo t st hchain (hbitsRead st hext.2)
    rw [hWat st (htcoords hOnT).1 (htcoords hOnT).2 (CircuitType.reads_fvar.mp hp2x.2)
      (CircuitType.reads_fvar.mp hp2y.2), hlenB] at hfx hfy
    obtain ⟨hfin', sc, A, B, hseq, hsab, hAle, hBle, hAval, hBval, -⟩ :=
      Kimchi.Gate.EndoMul.endoMul_off d.W d.two_ne d.three_ne d.odd d.endo
        (Point.some _ _ hT) (Point.some _ _ hφT)
        (fun a b ha hb hba hbb =>
          d.off_targets ha hb hba hbb (Point.some_ne_zero hT) (d.eigen hT hφT))
        32 hbits W hchainW hP0ns hP0eq d.lam (d.eigen hT hφT)
    have hfin : d.W.Nonsingular (fin.1.x.val st.env.get) (fin.1.y.val st.env.get) := by
      rw [hfx, hfy]
      exact hfin'
    have hcl : Kimchi.Gate.EndoMul.crumbList W 32
        = Kimchi.Gate.EndoScalar.crumbsOf (2 * 32) (ToNat.toNat sv) := by
      rw [Kimchi.Gate.EndoMul.crumbList_ofBits 32 (ToNat.toNat sv) W ?_]
      intro r _
      cases r <;> exact ⟨rfl, rfl, rfl, rfl⟩
    -- the accumulators, under their bounds, ARE the prechallenge's decoded integer
    rw [← decomposition_eq_endoExpandZ d (ToNat.toNat sv) hsab (h4 ▸ hAle) (h4 ▸ hBle)
      (hcl ▸ hAval) (hcl ▸ hBval)]
    exact ⟨scoped_affinePoint.mpr ⟨hinv.2.1, hinv.2.2.1⟩, hfin,
      ((Kimchi.Gate.AddComplete.some_congr d.W hfin hfin' hfx hfy).trans hseq).symm⟩

open Std.Do WeierstrassCurve.Affine Kimchi.Gate.EndoScalar in
/-- **Soundness**, at the deployed thirty-two rounds — the sixty-four crumbs of a 128-bit
challenge, the width PS's `toFieldPure` fixes in its `SizedF 128` operand. Any satisfying
valuation reads the scalar as a prechallenge below that width, and the result as the base
multiplied by that prechallenge's decoded integer.

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
run through `endoMul`'s: soundness reads the on-curve rows at the WITNESSED point to
discharge `endoMul_spec`'s hypothesis there, and the two pins carry the product to the
input; completeness supplies the honest quotient and lands `endoMul_complete`'s
conclusion on it. The multiplier is `endoMul`'s own — one `endoExpandZ` integer,
shared by both directions — and the division is stated by inverting its residue. -/

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
inverse residue acting on the input, the PS defining equation
`endoInv g a ~ scalarMul (recip (toFieldPure a endoScalar)) g`.

The on-curve rows discharge `endoMul_spec`'s hypothesis at the WITNESSED point — the
gadget's design point — with smoothness (`d.delta_ne`) upgrading their equation to
nonsingularity, and the two pins carry the product to the input. The advice parameters
`(q, hq, lam')` are universally quantified: soundness never consults the witness. -/
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
  mvcgen [hendo]
  rename_i result _ _ _ _ hx2 _ _ hx3 _ _ hsq _ _ hcomp _ _ heqx _ _ heqy
  intro G hG
  -- the on-curve rows read as the curve equation at the witnessed point
  have hEq : d.W.Equation (result.1.val V) (result.2.val V) := by
    rw [d.W.equation_iff, d.short.1, d.short.2.1, d.short.2.2.1]
    simp only [CVar.val_add_, CVar.val_scale_, CVar.val] at hsq
    rw [hx3, hx2] at hsq
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

/-- `witness` at an admissible value the advice computes, in the shape a completeness
chain consumes: the run allocates the value's cells and the result reads as it. -/
private theorem witnessAt_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] {val var : Type}
    [CircuitType F val var] [CheckedType F c val var]
    (compute : AsProver F val) (v : val)
    (hv : CheckedType.Valid (F := F) (c := c) (var := var) v)
    {pre : ProverState F → Prop} (h : ∀ st, pre st → compute.run st.env = .ok v) :
    Complete (F := F) (c := c) pre (witness (c := c) (val := val) compute)
      (fun r st' => CircuitType.ReadsAs (val := val) st' r v) :=
  Complete.imp h (fun _ _ h => h) (Complete.witness compute v hv)

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

open WeierstrassCurve.Affine Kimchi.Gate.EndoScalar in
open Kimchi.Gate.VarBaseMul (smul_ne_zero_of_lt smul_eq_smul_of_zmod_eq) in
/-- **Completeness**, at the honest advice — the gadget instantiated in its own scalar
field (`q := W.order`, `λ' := λ mod q`). On an input reading as a curve point and a
challenge faithful and within the deployed width, the run succeeds, every row it emits
is satisfied, and the result reads as `[s⁻¹]·g` for `s` the challenge's decoded integer:
the PS witness's defining equation, in the residue `endoInv_spec` inverts.

The run cannot fail: `s` is a unit modulo the order (`endoExpandZ_ne_zero`), so the
quotient is a genuine affine point — the on-curve rows pass on it — and multiplying it
back by `s` returns the input, which is what the two pins need. -/
theorem endoInv_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (d : HasEndo F) (g : AffinePoint (FVar F)) (scalar : SizedF 128 (FVar F))
    (xv yv sv : F) (hG : d.W.Nonsingular xv yv)
    (hfits : ToNat.toNat sv < 2 ^ 128) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => OnCurveAs d.W st g (Point.some _ _ hG) ∧
        CircuitType.ReadsAs (val := F) st scalar.val sv)
      (Snarky.Kimchi.endoInv (c := KimchiConstraint F) d.endo d.W d.W.order d.prime
        ((d.lam : ZMod d.W.order)) g scalar)
      (fun r st' => OnCurveAs d.W st' r
        (((((endoExpandZ d.lam (ToNat.toNat sv) : ℤ) : ZMod d.W.order)⁻¹).val : ℕ)
          • Point.some _ _ hG)) := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  haveI : NeZero d.W.order := ⟨d.prime.ne_zero⟩
  set G : d.W.Point := Point.some xv yv hG with hGdef
  have hs0 : ((endoExpandZ d.lam (ToNat.toNat sv) : ℤ) : ZMod d.W.order) ≠ 0 :=
    endoExpandZ_ne_zero d hG _
  have hGne : G ≠ 0 := Point.some_ne_zero hG
  set k : ℕ := (((endoExpandZ d.lam (ToNat.toNat sv) : ℤ) : ZMod d.W.order)⁻¹).val with hkdef
  have hkne : k ≠ 0 := by rw [hkdef, Ne, ZMod.val_eq_zero]; exact inv_ne_zero hs0
  have hklt : k < d.W.order := ZMod.val_lt _
  have hkG : ((k : ℕ) : ℤ) • G ≠ 0 :=
    smul_ne_zero_of_lt d.W hGne (by exact_mod_cast Nat.pos_of_ne_zero hkne)
      (by exact_mod_cast hklt)
  obtain ⟨px, py, hpns, hpteq⟩ :
      ∃ px py, ∃ h : d.W.Nonsingular px py, (k : ℕ) • G = Point.some _ _ h := by
    rw [natCast_zsmul] at hkG
    cases hp : (k : ℕ) • G with
    | zero => exact absurd hp hkG
    | some px py h => exact ⟨px, py, h, rfl⟩
  -- multiplying the quotient back by the challenge returns the input
  have hback : endoExpandZ d.lam (ToNat.toNat sv) • (Point.some px py hpns : d.W.Point) = G := by
    rw [← hpteq, ← natCast_zsmul, smul_smul]
    have hcast : ((endoExpandZ d.lam (ToNat.toNat sv) * ((k : ℕ) : ℤ) : ℤ) : ZMod d.W.order)
        = ((1 : ℤ) : ZMod d.W.order) := by
      push_cast
      rw [hkdef, ZMod.natCast_val, ZMod.cast_id, mul_inv_cancel₀ hs0]
    rw [smul_eq_smul_of_zmod_eq d.W hcast, one_smul]
  -- the curve equation at the quotient, in the shape the on-curve row compares
  have hEq : py * py = px * px * px + d.W.a₄ * px + d.W.a₆ := by
    have h := (d.W.equation_iff px py).mp hpns.1
    rw [d.short.1, d.short.2.1, d.short.2.2.1] at h
    linear_combination h
  -- the honest advice computes the quotient's coordinates
  have hread : ∀ st : ProverState F,
      (OnCurveAs d.W st g G ∧ CircuitType.ReadsAs (val := F) st scalar.val sv) →
      (endoInvWit d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) g scalar.val).run
        st.env = .ok (px, py) := by
    rintro st ⟨⟨hgSc, hgAt⟩, hsc⟩
    rw [scoped_affinePoint] at hgSc
    obtain ⟨hrx, hry⟩ := Kimchi.Gate.AddComplete.IsPoint.coords_eq hgAt
      (⟨hG, rfl⟩ : Kimchi.Gate.AddComplete.IsPoint d.W xv yv G)
    simp only [endoInvWit, AsProver.bind_eq, AsProver.run_bind,
      AsProver.readCVar_run hgSc.1, AsProver.readCVar_run hgSc.2,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp hsc.1),
      hrx, hry, CircuitType.reads_fvar.mp hsc.2, Except.bind]
    rw [dif_pos hG, toField_crumbsOf_eq_endoExpandZ d, ← hkdef, ← hGdef, hpteq]
    rfl
  -- the ambient context: the input's reading, and what each stage adds to it
  have mT : Mono (F := F) (fun _ : ProverState F => True) := fun _ _ _ _ _ => trivial
  have m₀ : Mono (F := F) fun st =>
      OnCurveAs d.W st g G ∧ CircuitType.ReadsAs (val := F) st scalar.val sv :=
    (Mono.onCurveAs (W := d.W) (p := g) (P := G)).and Mono.readsAs
  refine Complete.seq m₀
    (witnessAt_complete (c := KimchiConstraint F) (val := F × F) _ (px, py) (by simp) hread)
    fun rp => ?_
  have hrpx : ∀ st : ProverState F,
      CircuitType.ReadsAs (val := F × F) st rp (px, py) →
      CircuitType.ReadsAs (val := F) st rp.1 px := by
    rintro st ⟨hsc, hrd⟩
    rw [CircuitType.scoped_prod] at hsc
    rw [CircuitType.reads_prod] at hrd
    exact ⟨hsc.1, hrd.1⟩
  have hrpy : ∀ st : ProverState F,
      CircuitType.ReadsAs (val := F × F) st rp (px, py) →
      CircuitType.ReadsAs (val := F) st rp.2 py := by
    rintro st ⟨hsc, hrd⟩
    rw [CircuitType.scoped_prod] at hsc
    rw [CircuitType.reads_prod] at hrd
    exact ⟨hsc.2, hrd.2⟩
  have m₁ := m₀.and (Mono.readsAs (val := F × F) (v := rp) (a := (px, py)))
  -- `x²`
  refine Complete.seq m₁
    (Complete.imp (fun st h => hrpx st h.2) (fun _ _ h => h)
      (square_complete (c := KimchiConstraint F) rp.1 px)) fun x2 => ?_
  have m₂ := m₁.and (Mono.readsAs (v := x2) (a := px * px))
  -- `x³`
  refine Complete.seq m₂
    (Complete.imp (fun st h => ⟨h.2, hrpx st h.1.2⟩) (fun _ _ h => h)
      (mul_complete (c := KimchiConstraint F) x2 rp.1 (px * px) px)) fun x3 => ?_
  have m₃ := m₂.and (Mono.readsAs (v := x3) (a := px * px * px))
  -- the on-curve row
  refine Complete.seq m₃
    (Complete.imp
      (fun st h => ⟨hrpy st h.1.1.2,
        ⟨CircuitType.scoped_fvar.mpr
          (((CircuitType.scoped_fvar.mp h.2.1).add_
            (CVar.Scoped.scale_ (CircuitType.scoped_fvar.mp (hrpx st h.1.1.2).1))).add_
              (CVar.scoped_const _ _)),
          CircuitType.reads_fvar.mpr (by
            rw [CVar.val_add_, CVar.val_add_, CVar.val_scale_,
              CircuitType.reads_fvar.mp h.2.2,
              CircuitType.reads_fvar.mp (hrpx st h.1.1.2).2]
            rfl)⟩⟩)
      (fun _ _ h => h)
      (assertSquare_complete (c := KimchiConstraint F) rp.2
        (CVar.add_ (CVar.add_ x3 (CVar.scale_ d.W.a₄ rp.1)) (.const d.W.a₆))
        py (px * px * px + d.W.a₄ * px + d.W.a₆) hEq)) fun _ => ?_
  have m₄ := m₃.and mT
  -- the multiply-back
  refine Complete.seq m₄
    (Complete.imp
      (fun st h => ⟨⟨scoped_affinePoint.mpr
          ⟨CircuitType.scoped_fvar.mp (hrpx st h.1.1.1.2).1,
            CircuitType.scoped_fvar.mp (hrpy st h.1.1.1.2).1⟩,
          OnCurveAt.of_reads (CircuitType.reads_fvar.mp (hrpx st h.1.1.1.2).2)
            (CircuitType.reads_fvar.mp (hrpy st h.1.1.1.2).2) hpns⟩,
        h.1.1.1.1.2⟩)
      (fun _ _ h => h)
      (endoMul_complete d ⟨rp.1, rp.2⟩ scalar px py sv hpns hfits)) fun computed => ?_
  have m₅ := m₄.and (Mono.onCurveAs (W := d.W) (p := computed)
    (P := endoExpandZ d.lam (ToNat.toNat sv) • Point.some px py hpns))
  -- the two pins: the product reads as the input point
  have hcx : ∀ st : ProverState F,
      OnCurveAs d.W st computed
        (endoExpandZ d.lam (ToNat.toNat sv) • Point.some px py hpns) →
      OnCurveAs d.W st g G →
      CircuitType.ReadsAs (val := F) st computed.x xv ∧
        CircuitType.ReadsAs (val := F) st g.x xv ∧
        CircuitType.ReadsAs (val := F) st computed.y yv ∧
        CircuitType.ReadsAs (val := F) st g.y yv := by
    rintro st ⟨hcSc, hcAt⟩ ⟨hgSc, hgAt⟩
    rw [scoped_affinePoint] at hcSc hgSc
    rw [hback] at hcAt
    obtain ⟨hcx, hcy⟩ := Kimchi.Gate.AddComplete.IsPoint.coords_eq hcAt
      (⟨hG, rfl⟩ : Kimchi.Gate.AddComplete.IsPoint d.W xv yv G)
    obtain ⟨hgx, hgy⟩ := Kimchi.Gate.AddComplete.IsPoint.coords_eq hgAt
      (⟨hG, rfl⟩ : Kimchi.Gate.AddComplete.IsPoint d.W xv yv G)
    exact ⟨⟨CircuitType.scoped_fvar.mpr hcSc.1, CircuitType.reads_fvar.mpr hcx⟩,
      ⟨CircuitType.scoped_fvar.mpr hgSc.1, CircuitType.reads_fvar.mpr hgx⟩,
      ⟨CircuitType.scoped_fvar.mpr hcSc.2, CircuitType.reads_fvar.mpr hcy⟩,
      ⟨CircuitType.scoped_fvar.mpr hgSc.2, CircuitType.reads_fvar.mpr hgy⟩⟩
  refine Complete.seq m₅
    (Complete.imp
      (fun st h => ⟨(hcx st h.2 h.1.1.1.1.1.1).1, (hcx st h.2 h.1.1.1.1.1.1).2.1⟩)
      (fun _ _ h => h)
      (assertEqual_complete (c := KimchiConstraint F) computed.x g.x xv)) fun _ => ?_
  have m₆ := m₅.and mT
  refine Complete.seq m₆
    (Complete.imp
      (fun st h => ⟨(hcx st h.1.2 h.1.1.1.1.1.1.1).2.2.1,
        (hcx st h.1.2 h.1.1.1.1.1.1.1).2.2.2⟩)
      (fun _ _ h => h)
      (assertEqual_complete (c := KimchiConstraint F) computed.y g.y yv)) fun _ => ?_
  -- the result reads as the quotient
  refine Complete.pure_of fun st h => ?_
  refine ⟨scoped_affinePoint.mpr
      ⟨CircuitType.scoped_fvar.mp (hrpx st h.1.1.1.1.1.1.2).1,
        CircuitType.scoped_fvar.mp (hrpy st h.1.1.1.1.1.1.2).1⟩, ?_⟩
  rw [hpteq]
  exact OnCurveAt.of_reads (CircuitType.reads_fvar.mp (hrpx st h.1.1.1.1.1.1.2).2)
    (CircuitType.reads_fvar.mp (hrpy st h.1.1.1.1.1.1.2).2) hpns

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta Kimchi.Gate.EndoScalar
  WeierstrassCurve.Affine in
/-- **The deployed challenge leg's honest run.** At Vesta, on a base on the curve and a
scalar cell reading as a prechallenge `n < 2^128`, the run succeeds and the result is the
base scaled by the wire's challenge — the Fq-sponge's endo-expansion of `n`, acting
through the point group's `Fp`-module structure. -/
@[complete_law]
theorem vesta_endoMul_complete {t : AffinePoint (FVar Fq)} {cv : FVar Fq} {xv yv : Fq}
    {n : ℕ} (hT : HasEndo.vesta.W.Nonsingular xv yv) (hn : n < 2 ^ 128) :
    Complete (F := Fq) (c := KimchiConstraint Fq)
      (fun st => OnCurveAs HasEndo.vesta.W st t (Point.some _ _ hT) ∧
        CircuitType.ReadsAs (val := Fq) st cv ((n : ℕ) : Fq))
      (Snarky.Kimchi.endoMul (c := KimchiConstraint Fq) HasEndo.vesta.endo 32 t ⟨cv⟩)
      (fun r st' => OnCurveAs HasEndo.vesta.W st' r
        ((Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam n : Fp)
          • Point.some _ _ hT)) := by
  have hcard : n < LawfulToNat.card (F := Fq) := by
    show n < PALLAS_SCALAR_CARD
    exact lt_of_lt_of_le hn (by decide)
  have hrep : ToNat.toNat ((n : ℕ) : Fq) = n := LawfulToNat.toNat_natCast n hcard
  have hfits : ToNat.toNat ((n : ℕ) : Fq) < 2 ^ 128 := by rw [hrep]; exact hn
  have hexp : (Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam n : Fp)
      = ((endoExpandZ HasEndo.vesta.lam n : ℤ) : Fp) := by
    rw [show Poseidon.FqVesta.spec.lam = ((HasEndo.vesta.lam : ℤ) : Fp) from rfl,
      endoExpandZ_cast (by decide) (by decide)]
  have hgen := endoMul_complete HasEndo.vesta t ⟨cv⟩ xv yv ((n : ℕ) : Fq) hT hfits
  intro st hst
  obtain ⟨r, st', hrun, hsat, hpt⟩ := hgen st hst
  refine ⟨r, st', hrun, hsat, ?_⟩
  rw [hexp, Int.cast_smul_eq_zsmul]
  exact hrep ▸ hpt

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta Kimchi.Gate.EndoScalar
  WeierstrassCurve.Affine in
/-- **The deployed challenge leg.** At Vesta, the generic law's output on a scalar cell
reading as a prechallenge `n < 2^128` says the result is the base point scaled by the
wire's challenge — the Fq-sponge's endo-expansion of `n`, acting through the point
group's `Fp`-module structure.

The generic post names its own prechallenge, pinned only through the scalar's reading in
`Fq`; below `|Fq|` that reading determines it, and the decoded integer is then the
expansion the sponge computes. Neither step is visible here: a consumer supplies a
reading and a bound, and receives the scalar action it needs.

Stated on the generic law's OUTPUT rather than as a triple, because a consumer reaches it
holding that output — its own program walk has already passed the call. -/
theorem vesta_endoMul_read {V : Valuation Fq} {t r : AffinePoint (FVar Fq)}
    {cv : FVar Fq} {n : ℕ} (hn : n < 2 ^ 128) (hread : cv.val V = ((n : ℕ) : Fq))
    (h : ∀ T : Vesta.curve.toAffine.Point, OnCurveAt Vesta.curve.toAffine V t T →
      ∃ m : ℕ, m < 2 ^ 128 ∧ cv.val V = ((m : ℕ) : Fq) ∧
        OnCurveAt Vesta.curve.toAffine V r (endoExpandZ HasEndo.vesta.lam m • T)) :
    ∀ T : Vesta.curve.toAffine.Point, OnCurveAt Vesta.curve.toAffine V t T →
      OnCurveAt Vesta.curve.toAffine V r
        ((Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam n : Fp) • T) := by
  intro T hT
  obtain ⟨m, hm, hmread, hseq⟩ := h T hT
  have hmn : m = n :=
    CharP.natCast_injOn_Iio Fq PALLAS_SCALAR_CARD
      (Set.mem_Iio.mpr (lt_of_lt_of_le hm (by decide)))
      (Set.mem_Iio.mpr (lt_of_lt_of_le hn (by decide)))
      (by rw [← hmread, hread])
  subst hmn
  rw [show Poseidon.FqVesta.spec.lam = ((HasEndo.vesta.lam : ℤ) : Fp) from rfl,
    ← endoExpandZ_cast (by decide) (by decide), Int.cast_smul_eq_zsmul]
  exact hseq

end EndoMul

end Snarky.Kimchi
