import Snarky.Circuit.DSL.Field
import Snarky.Circuit.DSL.SizedF
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

/-- The scalar's `4·rounds` bits MSB-first as field values, four per row. -/
private def bitVals [Zero F] [One F] (rounds n : ℕ) : Vector (Vector F 4) rounds :=
  Vector.ofFn fun r => Vector.ofFn fun j =>
    if n.testBit (4 * rounds - 1 - (4 * r.1 + j.1)) then 1 else 0

/-- The scalar's bits, witnessed in bulk (PS's bulk bit witness: `toBits` reversed). -/
private def bitsWit [Field F] [ToNat F] (rounds : ℕ) (scalar : FVar F) :
    AsProver F (Vector (Vector F 4) rounds) := do
  let v ← AsProver.readCVar scalar
  pure (bitVals rounds (ToNat.toNat v))

/-- One GLV round's advice at its cell readings: the gate's canonical row
(`Kimchi.Gate.EndoMul.build` — two `stepWindow` double-adds, the scalar recoding,
the distinct-point inverse), in the PS record's alphabetical allocation order
`(inv, nAccNext, r.x, r.y, s.x, s.y, s1, s3)`. -/
private def rowVals [Field F] [DecidableEq F] (eb xt yt xp yp n b1 b2 b3 b4 : F) :
    F × F × F × F × F × F × F × F :=
  let w := Kimchi.Gate.EndoMul.build eb xt yt xp yp n b1 b2 b3 b4
  (w.inv, w.nPrime, w.xR, w.yR, w.xS, w.yS, w.s1, w.s3)

/-- One GLV round's witness: read the base, the threaded accumulator and register,
and the four window bits, and build `rowVals`. -/
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
  pure (rowVals eb xt yt xp yp n b1 b2 b3 b4)

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

/-- `endoInv`'s advice at the point's and challenge's readings: decode the effective
scalar in the scalar field `ZMod q` — the kimchi gate model itself,
`EndoScalar.toField` at the challenge's canonical crumbs and the scalar-field
eigenvalue `lam'` — and hand back `[s⁻¹]·g` computed in `W.Point`. Off-curve reads
and the point at infinity fall back to `(0, 0)` (PS's partial `toAffine`/`fromJust`
path) — unreachable for honest inputs. -/
private def endoInvVal [Field F] [DecidableEq F] [ToNat F] (W : WeierstrassCurve.Affine F)
    (q : ℕ) (hq : q.Prime) (lam' : ZMod q) (gx gy s : F) : F × F :=
  letI : Fact q.Prime := ⟨hq⟩
  let eff : ZMod q := Kimchi.Gate.EndoScalar.toField
    (Kimchi.Gate.EndoScalar.crumbsOf 64 (ToNat.toNat s)) lam'
  letI : Decidable (W.Equation gx gy) :=
    decidable_of_iff _ (W.equation_iff gx gy).symm
  letI : Decidable (W.Nonsingular gx gy) :=
    decidable_of_iff _ (W.nonsingular_iff gx gy).symm
  if h : W.Nonsingular gx gy then
    match eff⁻¹.val • (WeierstrassCurve.Affine.Point.some gx gy h : W.Point) with
    | .zero => (0, 0)
    | .some x y _ => (x, y)
  else (0, 0)

/-- `endoInv`'s result witness: read the point and the 128-bit challenge, and compute
`endoInvVal`. -/
private def endoInvWit [Field F] [DecidableEq F] [ToNat F]
    (W : WeierstrassCurve.Affine F) (q : ℕ) (hq : q.Prime) (lam' : ZMod q)
    (g : AffinePoint (FVar F)) (scalar : FVar F) :
    AsProver F (F × F) := do
  let gx ← AsProver.readCVar g.x
  let gy ← AsProver.readCVar g.y
  let s ← AsProver.readCVar scalar
  pure (endoInvVal W q hq lam' gx gy s)

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
the curve dictionary `HasCurve` it extends, the endomorphism coefficient and its
scalar eigenvalue, and every curve-level fact the `endoMul` law pair consumes — the
deep embedding's rendering of the PS typeclass, resolved by the field. Generic
circuit laws close over one `HasEndo F` and compose over an abstract field the way
the PS pickles circuits do; the deployed instances `HasEndo.pallas`/`HasEndo.vesta`
discharge it, mirroring the instantiation at wrap/step main. -/
class HasEndo (F : Type) [Field F] [DecidableEq F] extends HasCurve F where
  /-- The endomorphism coefficient `β`: `φ(x, y) = (β·x, y)`. -/
  endo : F
  /-- The scalar eigenvalue `λ` of the endomorphism: `φ(T) = [λ]·T`. -/
  lam : ℤ
  /-- The curve is smooth, so an on-curve point is nonsingular
  (`equation_iff_nonsingular_of_Δ_ne_zero`). -/
  delta_ne : W.Δ ≠ 0
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
instance HasEndo.pallas : HasEndo Fp where
  toHasCurve := HasCurve.pallas
  endo := pallasEndo
  lam := pallasLam
  delta_ne := by decide
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
  order_ne_three := by show Pallas.curve.toAffine.order ≠ 3; rw [pallas_card]; decide
  char_big := fun z hz h0 => by
    have hdvd : ((PALLAS_BASE_CARD : ℕ) : ℤ) ∣ z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd z _).mp h0
    exact Int.eq_zero_of_abs_lt_dvd hdvd (hz.trans (by norm_num))

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Pasta in
/-- The dictionary at deployed Vesta — the other half of the 2-cycle. -/
instance HasEndo.vesta : HasEndo Fq where
  toHasCurve := HasCurve.vesta
  endo := vestaEndo
  lam := vestaLam
  delta_ne := by decide
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
  order_ne_three := by show Vesta.curve.toAffine.order ≠ 3; rw [vesta_card]; decide
  char_big := fun z hz h0 => by
    have hdvd : ((PALLAS_SCALAR_CARD : ℕ) : ℤ) ∣ z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd z _).mp h0
    exact Int.eq_zero_of_abs_lt_dvd hdvd (hz.trans (by norm_num))

open Kimchi.Gate.EndoScalar in
/-- An integer of the shape the sound law hands back — `s = B + A·λ`, bounded by
`3·2^64`, pinned in `F` to the canonical 64-crumb decomposition (a 128-bit
challenge is 64 two-bit crumbs; `3·2^64 = 3·4^32` at 32 rounds) — IS the gate's
decoded integer `toIntZ`, via the `d.char_big` window. Modulus-free: consumers cast
the one integer into whichever scalar field acts. -/
theorem HasEndo.decomposition_eq_toIntZ [Field F] [DecidableEq F]
    [d : HasEndo F]
    (n : ℕ) {s A B : ℤ} (hsab : s = B + A * d.lam)
    (hAle : |A| ≤ 3 * 2 ^ 64) (hBle : |B| ≤ 3 * 2 ^ 64)
    (hAval : (A : F) = Kimchi.Gate.EndoScalar.decomposeA (crumbsOf 64 n))
    (hBval : (B : F) = Kimchi.Gate.EndoScalar.decomposeB (crumbsOf 64 n)) :
    s = toIntZ (digitsOf 64 n) d.lam := by
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
  rw [hsab, hAeq, hBeq, toIntZ]
  ring

open Kimchi.Gate.EndoScalar in
/-- `decomposition_eq_toIntZ` mod the group order: the one integer scalar, read back
as the gate's decoded scalar at the canonical crumbs (`toField_digits`). -/
theorem HasEndo.decomposition_residue [Field F] [DecidableEq F]
    [d : HasEndo F]
    [Fact (Nat.Prime d.W.order)]
    (n : ℕ) {s A B : ℤ} (hsab : s = B + A * d.lam)
    (hAle : |A| ≤ 3 * 2 ^ 64) (hBle : |B| ≤ 3 * 2 ^ 64)
    (hAval : (A : F) = Kimchi.Gate.EndoScalar.decomposeA (crumbsOf 64 n))
    (hBval : (B : F) = Kimchi.Gate.EndoScalar.decomposeB (crumbsOf 64 n)) :
    ((s : ℤ) : ZMod d.W.order)
      = Kimchi.Gate.EndoScalar.toField (crumbsOf 64 n) ((d.lam : ZMod d.W.order)) := by
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
      exact d.order_ne_three
        ((Nat.prime_dvd_prime_iff_eq d.prime Nat.prime_three).mp h3)
    exact_mod_cast h
  have heffz : Kimchi.Gate.EndoScalar.toField (crumbsOf 64 n)
      ((d.lam : ZMod d.W.order))
      = ((toIntZ (digitsOf 64 n) d.lam : ℤ) : ZMod d.W.order) := by
    rw [crumbsOf_eq_map, toField_digits h2q h3q _ (digitsOf_lt 64 _) d.lam]
  rw [heffz, HasEndo.decomposition_eq_toIntZ n hsab hAle hBle hAval hBval]

open CompElliptic.Fields.Pasta Kimchi.Gate.EndoScalar in
/-- At Vesta, 64 crumbs reconstructing a value below `2^128` are its canonical crumbs:
`nReconstruct` is injective on valid 64-crumb lists in `Fq`. -/
theorem HasEndo.vesta_crumbs_eq {n : ℕ} (hn : n < 2 ^ 128) {crumbs : List Fq}
    (hcrv : ∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) (hclen : crumbs.length = 2 * 32)
    (hcrec : ((n : ℕ) : Fq) = nReconstruct crumbs) : crumbs = crumbsOf 64 n := by
  refine nReconstruct_inj (p := PALLAS_SCALAR_CARD) crumbs _ (by decide) (by decide) hcrv
    (crumbsOf_valid 64 n) ?_ ?_ ?_
  · rw [hclen, crumbsOf_length]
  · rw [hclen]; decide
  · rw [← hcrec, nReconstruct_crumbsOf]
    exact congrArg (Nat.cast (R := Fq))
      (Nat.mod_eq_of_lt (lt_of_lt_of_le hn (by decide))).symm

open CompElliptic.Fields.Pasta Kimchi.Gate.EndoScalar in
/-- The deployed challenge: the scalar `endoMul_spec` hands back at Vesta, at the
canonical crumbs of a prechallenge `n`, reads in `Fp` as the Fq-sponge's
endo-expansion of `n` — the in-circuit `[c]·pk` acts by the wire's challenge. -/
theorem HasEndo.vesta_endoExpand {n : ℕ} {s A B : ℤ} (hsab : s = B + A * HasEndo.vesta.lam)
    (hAle : |A| ≤ 3 * 4 ^ 32) (hBle : |B| ≤ 3 * 4 ^ 32)
    (hAval : (A : Fq) = decomposeA (crumbsOf 64 n))
    (hBval : (B : Fq) = decomposeB (crumbsOf 64 n)) :
    ((s : ℤ) : Fp) = Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam n := by
  rw [HasEndo.decomposition_eq_toIntZ (d := HasEndo.vesta) n hsab
      (by norm_num at hAle ⊢; exact hAle) (by norm_num at hBle ⊢; exact hBle) hAval hBval,
    endoExpand_eq_toField (by decide) (by decide),
    show Poseidon.FqVesta.spec.lam = ((HasEndo.vesta.lam : ℤ) : Fp) from rfl,
    crumbsOf_eq_map,
    toField_digits (by decide) (by decide) _ (digitsOf_lt 64 _) HasEndo.vesta.lam]

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
      ∃ (hfin : W.Nonsingular (fin.1.x.val V) (fin.1.y.val V)) (s A B : ℤ),
        Point.some _ _ hfin = s • Point.some _ _ hT ∧
        s = B + A * lam ∧
        |A| ≤ 3 * 4 ^ pref.length ∧ |B| ≤ 3 * 4 ^ pref.length ∧
        (A : F) = Kimchi.Gate.EndoScalar.decomposeA crumbs ∧
        (B : F) = Kimchi.Gate.EndoScalar.decomposeB crumbs ∧
        (s : F) = Kimchi.Gate.EndoScalar.toField crumbs (lam : F) := by
  match hround : rounds, hthr with
  | [], hthr' =>
    obtain ⟨rfl, rfl⟩ := Threaded.nil hthr'
    refine ⟨[], by simp, by simp, ?_, hP0ns, 2 + 2 * lam, 2, 2, ?_, by ring,
      by norm_num, by norm_num, ?_, ?_, ?_⟩
    · simp [Kimchi.Gate.EndoScalar.nReconstruct, CVar.val]
    · rw [hP0, heig]; module
    · push_cast
      simp [Kimchi.Gate.EndoScalar.decomposeA, Kimchi.Gate.EndoScalar.decomposeFold]
    · push_cast
      simp [Kimchi.Gate.EndoScalar.decomposeB, Kimchi.Gate.EndoScalar.decomposeFold]
    · push_cast
      simp [Kimchi.Gate.EndoScalar.toField, Kimchi.Gate.EndoScalar.decomposeA,
        Kimchi.Gate.EndoScalar.decomposeB, Kimchi.Gate.EndoScalar.decomposeFold]
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
    obtain ⟨hfin', s, A, B, hseq, hsab, hAle, hBle, hAval, hBval, hsval⟩ :=
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
      hfin, s, A, B, (some_congr W hfin hfin' hax.symm hay.symm).trans hseq,
      hsab, hm ▸ hAle, hm ▸ hBle, hAval, hBval, hsval⟩

open Kimchi.Gate.VarBaseMul (y_ne_zero_of_odd_order) in
/-- The gadget is sound: for an on-curve base reading, the result reads as `[s]·T`
with `s = B + A·λ`, the accumulators bounded by `3·4^rounds` and pinned in `F` to
the decomposition of a valid crumb list reconstructing the scalar. The bounded shape
lets a consumer read the same integer in a second field
(`HasEndo.decomposition_residue`); concretized at `HasEndo.pallas`/`vesta`. -/
@[spec] theorem endoMul_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F] [d : HasEndo F]
    (rounds : ℕ) (hbits : 4 * rounds ≤ 244) (e : F) (he : e = d.endo)
    (t : AffinePoint (FVar F)) (scalar : SizedF (4 * rounds) (FVar F)) :
    ⦃⌜True⌝⦄
    (endoMul (c := Builder V (KimchiConstraint F)) e rounds t scalar)
    ⦃⇓ r _ => ⌜∀ hT : d.W.Nonsingular (t.x.val V) (t.y.val V),
          ∃ crumbs : List F,
            (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
            crumbs.length = 2 * rounds ∧
            scalar.val.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs ∧
            ∃ (hfin : d.W.Nonsingular (r.x.val V) (r.y.val V)) (s A B : ℤ),
              Point.some _ _ hfin = s • Point.some _ _ hT ∧
              s = B + A * d.lam ∧
              |A| ≤ 3 * 4 ^ rounds ∧ |B| ≤ 3 * 4 ^ rounds ∧
              (A : F) = Kimchi.Gate.EndoScalar.decomposeA crumbs ∧
              (B : F) = Kimchi.Gate.EndoScalar.decomposeB crumbs ∧
              (s : F) = Kimchi.Gate.EndoScalar.toField crumbs (d.lam : F)⌝⦄ := by
  subst he
  obtain ⟨eb, lam, -, h3, heig, hφns, hoff, -, -, -⟩ := d
  set W := HasCurve.W (F := F)
  have ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0 := HasCurve.short
  have hprime : Nat.Prime W.order := HasCurve.prime
  have hodd : W.order ≠ 2 := HasCurve.odd
  have h2 : (2 : F) ≠ 0 := HasCurve.two_ne
  haveI : Fact (Nat.Prime W.order) := ⟨hprime⟩
  haveI : Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0) := ⟨⟨ha.1, ha.2.1, ha.2.2.1⟩⟩
  simp only [endoMul, endoMulRound, mapAccumM]
  have hadd := AddFast.addFast_checkFinite_spec (V := V) (d := ⟨W, ha, hprime, hodd, h2⟩)
  mvcgen [hadd]
  · rename_i _ _ _ _ _ _ _ _ p2 _ _ _
    exact ⇓ p _ => ⌜Threaded t (p2.p, .const 0) p.1.prefix p.2.snd p.2.fst⌝
  · rename_i pref cur suff _ b _ hinv w _ _
    simp at hinv ⊢
    exact hinv.snoc cur w
  · exact ⟨rfl, rfl⟩
  · rename_i bits _ _ phix _ hphix p1 _ hp1 p2 _ hp2 finp _ hinv _ _ heq _ _ hpay
    simp at hinv
    intro hT
    have hφT : W.Nonsingular (eb * t.x.val V) (t.y.val V) := hφns hT
    -- the init chain: `[2](T + φT)` from the seal and the two pinned additions
    have hy : t.y.val V ≠ 0 := y_ne_zero_of_odd_order W hodd hT
    have hφTp : W.Nonsingular (phix.val V) (t.y.val V) := by
      rw [hphix, CVar.val_scale_]
      exact hφT
    obtain ⟨hP1, hsum1⟩ := hp1 hT hφTp hy
    have hy1 : p1.p.y.val V ≠ 0 := y_ne_zero_of_odd_order W hodd hP1
    obtain ⟨hP0ns, hsum2⟩ := hp2 hP1 hP1 hy1
    have hφeq : Point.some _ _ hφTp = Point.some _ _ hφT :=
      Kimchi.Gate.EndoMul.some_congr W hφTp hφT (by rw [hphix, CVar.val_scale_]) rfl
    have hP0 : Point.some _ _ hP0ns
        = (2 : ℤ) • Point.some _ _ hT + (2 : ℤ) • Point.some _ _ hφT := by
      rw [← hsum2, ← hsum1, hφeq]
      module
    -- the extracted run through `threaded_sound`
    obtain ⟨crumbs, hvalid, hlen, hreg, hfin, sc, A, B, hseq, hsab, hAle, hBle,
      hAval, hBval, hsval⟩ :=
      threaded_sound W h2 h3 hodd eb lam V (by simpa using hbits) hinv hpay hT hφT
        (fun a b ha' hb' hba hbb =>
          hoff ha' hb' hba hbb (Point.some_ne_zero hT) (heig hT hφT))
        (heig hT hφT) hP0ns hP0
    exact ⟨crumbs, hvalid, by simpa using hlen, heq.symm.trans hreg,
      hfin, sc, A, B, hseq, hsab, by simpa using hAle, by simpa using hBle,
      hAval, hBval, hsval⟩

/-! ## The honest run

The run functions and their laws. A round's run allocates its advice octet at the
counter (`roundRun`); the gadget's run writes the bit table, seals `β·x`, adds twice,
and folds the rounds (`endoMulRun`). `round_run`/`endoMul_run` land the prover at them;
`endoMulRun_grants` reads the result as `[s]·T` through the gate model's honest walk
`chainBuild`, whose rows the collected rounds evaluate to (`roundsRun_inv`). -/

/-- A round evaluates to a witness exactly when each cell reads as its field and the
supplied output values are its output fields. -/
private theorem evalWith_ok_iff [Field F] [DecidableEq F] {env : Assignments F}
    {r : EndoMulRound F} {xS yS nPrime : F} {w : Kimchi.Gate.EndoMul.Witness F} :
    EndoMulRound.evalWith env r xS yS nPrime = .ok w ↔
      r.t.x.eval env = .ok w.xT ∧ r.t.y.eval env = .ok w.yT ∧
      r.p.x.eval env = .ok w.xP ∧ r.p.y.eval env = .ok w.yP ∧
      r.nAcc.eval env = .ok w.n ∧
      r.bit0.eval env = .ok w.b1 ∧ r.bit1.eval env = .ok w.b2 ∧
      r.bit2.eval env = .ok w.b3 ∧ r.bit3.eval env = .ok w.b4 ∧
      r.s1.eval env = .ok w.s1 ∧ r.r.x.eval env = .ok w.xR ∧
      r.r.y.eval env = .ok w.yR ∧ r.s3.eval env = .ok w.s3 ∧
      r.inv.eval env = .ok w.inv ∧ xS = w.xS ∧ yS = w.yS ∧ nPrime = w.nPrime := by
  constructor
  · intro h
    unfold EndoMulRound.evalWith at h
    obtain ⟨xT, hxT, h⟩ := bind_ok h
    obtain ⟨yT, hyT, h⟩ := bind_ok h
    obtain ⟨xP, hxP, h⟩ := bind_ok h
    obtain ⟨yP, hyP, h⟩ := bind_ok h
    obtain ⟨n, hn, h⟩ := bind_ok h
    obtain ⟨b1, hb1, h⟩ := bind_ok h
    obtain ⟨b2, hb2, h⟩ := bind_ok h
    obtain ⟨b3, hb3, h⟩ := bind_ok h
    obtain ⟨b4, hb4, h⟩ := bind_ok h
    obtain ⟨s1, hs1, h⟩ := bind_ok h
    obtain ⟨xR, hxR, h⟩ := bind_ok h
    obtain ⟨yR, hyR, h⟩ := bind_ok h
    obtain ⟨s3, hs3, h⟩ := bind_ok h
    obtain ⟨inv, hinv, h⟩ := bind_ok h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hxT, hyT, hxP, hyP, hn, hb1, hb2, hb3, hb4, hs1, hxR, hyR, hs3, hinv,
      rfl, rfl, rfl⟩
  · intro ⟨hxT, hyT, hxP, hyP, hn, hb1, hb2, hb3, hb4, hs1, hxR, hyR, hs3, hinv,
      hxS, hyS, hnP⟩
    unfold EndoMulRound.evalWith
    rw [hxT, hyT, hxP, hyP, hn, hb1, hb2, hb3, hb4, hs1, hxR, hyR, hs3, hinv,
      hxS, hyS, hnP]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The chain check, one round at a time: a round whose record evaluates to an accepted
row extends a checked tail whose first round reads the row's outputs — or, at the end,
whose finals are the row's outputs. -/
private theorem chainOk_cons [Field F] [DecidableEq F] {env : Assignments F} {eb : F}
    {fv : F × F × F} {r : EndoMulRound F} {rest : List (EndoMulRound F)}
    {w : Kimchi.Gate.EndoMul.Witness F}
    (hev : EndoMulRound.evalWith env r w.xS w.yS w.nPrime = .ok w)
    (hok : Kimchi.Gate.EndoMul.ok eb w = true)
    (hnil : rest = [] → fv = (w.xS, w.yS, w.nPrime))
    (hcons : ∀ r' rest', rest = r' :: rest' →
      r'.p.x.eval env = .ok w.xS ∧ r'.p.y.eval env = .ok w.yS ∧ r'.nAcc.eval env = .ok w.nPrime)
    (hrest : EndoMul.chainOk env eb fv rest = true) :
    EndoMul.chainOk env eb fv (r :: rest) = true := by
  cases rest with
  | nil =>
    rw [hnil rfl]
    simp only [EndoMul.chainOk, hev]
    exact hok
  | cons r' rest' =>
    obtain ⟨hx, hy, hn⟩ := hcons r' rest' rfl
    simp only [EndoMul.chainOk, hx, hy, hn, hev, hok, hrest, Bool.and_self]

/-- A round's run: the advice octet at the counter, the record over it, and the
advanced `(accumulator, register)` state. -/
private def roundRun [Field F] [DecidableEq F] (eb : F) (t : AffinePoint (FVar F))
    (st : ProverState F) (acc : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 4) :
    ProverState F × (EndoMulRound F × (AffinePoint (FVar F) × FVar F)) :=
  let w := Kimchi.Gate.EndoMul.build eb (t.x.val st.env.toValuation)
    (t.y.val st.env.toValuation) (acc.1.x.val st.env.toValuation)
    (acc.1.y.val st.env.toValuation) (acc.2.val st.env.toValuation)
    (bs[0].val st.env.toValuation) (bs[1].val st.env.toValuation)
    (bs[2].val st.env.toValuation) (bs[3].val st.env.toValuation)
  let s : AffinePoint (FVar F) := ⟨.var (st.nv + 4), .var (st.nv + 5)⟩
  (st.extendMany [w.inv, w.nPrime, w.xR, w.yR, w.xS, w.yS, w.s1, w.s3],
   ({ t, p := acc.1, r := ⟨.var (st.nv + 2), .var (st.nv + 3)⟩, s,
      s1 := .var (st.nv + 6), s3 := .var (st.nv + 7), nAcc := acc.2,
      nAccNext := .var (st.nv + 1), bit0 := bs[0], bit1 := bs[1], bit2 := bs[2],
      bit3 := bs[3], inv := .var st.nv },
    (s, .var (st.nv + 1))))

/-- One round's honest run, at any state where the base, the state and the bits are in
scope. -/
private theorem round_run [Field F] [DecidableEq F] (eb : F) {t : AffinePoint (FVar F)}
    {st : ProverState F} {acc : AffinePoint (FVar F) × FVar F} {bs : Vector (FVar F) 4}
    (htx : t.x.Scoped st) (hty : t.y.Scoped st) (hax : acc.1.x.Scoped st)
    (hay : acc.1.y.Scoped st) (han : acc.2.Scoped st)
    (hbs : ∀ k (hk : k < 4), (bs[k]).Scoped st) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (endoMulRound (c := KimchiConstraint F) eb t acc bs) st.nv st.env
      = .ok ((roundRun eb t st acc bs).1.out (roundRun eb t st acc bs).2) := by
  simp only [endoMulRound, prove_bind]
  rw [prove_witness_run (w := rowWit eb t bs acc) st
    (.bind (.readCVar htx) fun _ => .bind (.readCVar hty) fun _ =>
      .bind (.readCVar hax) fun _ => .bind (.readCVar hay) fun _ =>
      .bind (.readCVar han) fun _ => .bind (.readCVar (hbs 0 (by omega))) fun _ =>
      .bind (.readCVar (hbs 1 (by omega))) fun _ => .bind (.readCVar (hbs 2 (by omega))) fun _ =>
      .bind (.readCVar (hbs 3 (by omega))) fun _ => trivial)
    (v := rowVals eb (t.x.val st.env.toValuation) (t.y.val st.env.toValuation)
      (acc.1.x.val st.env.toValuation) (acc.1.y.val st.env.toValuation)
      (acc.2.val st.env.toValuation) (bs[0].val st.env.toValuation)
      (bs[1].val st.env.toValuation) (bs[2].val st.env.toValuation)
      (bs[3].val st.env.toValuation))
    (by simp [rowWit, Except.bind])]
  simp only [rowVals, valueToFields_prod_toList, valueToFields_fvar_toList, List.cons_append,
    List.nil_append, fieldsToVar_prod_alloc, fieldsToVar_fvar_alloc, Except.bind, roundRun]
  simp only [size_fvar, Nat.add_assoc, Nat.reduceAdd]
  rfl

/-- The bit table's variables: the bulk allocation at the counter. -/
private def bitVarsOf (st : ProverState F) (rounds : ℕ) : Vector (Vector (FVar F) 4) rounds :=
  CircuitType.fieldsToVar (F := F) (val := Vector (Vector F 4) rounds)
    (mapVec CVar.var (allocRange st.nv (CircuitType.size F (Vector (Vector F 4) rounds))))

/-- The state after the bulk witness: the scalar's bit table written. -/
private def bitState [Field F] [ToNat F] (st : ProverState F) (rounds : ℕ) (scalar : FVar F) :
    ProverState F :=
  st.extendMany (CircuitType.valueToFields (F := F) (var := Vector (Vector (FVar F) 4) rounds)
    (bitVals (F := F) rounds (ToNat.toNat (scalar.val st.env.toValuation)))).toList

/-- The bit state extends the state. -/
private theorem bitState_le [Field F] [ToNat F] (st : ProverState F) (rounds : ℕ)
    (scalar : FVar F) : st.env.Le (bitState st rounds scalar).env := by
  unfold bitState
  exact st.le_extendMany _

/-- Every bit variable is in scope at the bit state. -/
private theorem bitVarsOf_scoped [Field F] [ToNat F] (st : ProverState F) (rounds : ℕ)
    (scalar : FVar F) (j : ℕ) (hj : j < rounds) (k : ℕ) (hk : k < 4) :
    ((bitVarsOf st rounds)[j][k]).Scoped (bitState st rounds scalar) := by
  have h := scoped_vector_iff.mp (scoped_extendMany_new (var := Vector (Vector (FVar F) 4) rounds)
    st (bitVals (F := F) rounds (ToNat.toNat (scalar.val st.env.toValuation)))) j hj
  exact scoped_fvar_iff.mp (scoped_vector_iff.mp h k hk)

/-- A bit variable reads, at the bit state, as the scalar's bit. -/
private theorem bitVarsOf_val [Field F] [ToNat F] (st : ProverState F) (rounds : ℕ)
    (scalar : FVar F) (j : ℕ) (hj : j < rounds) (k : ℕ) (hk : k < 4) :
    ((bitVarsOf st rounds)[j][k]).val (bitState st rounds scalar).env.toValuation
      = if (ToNat.toNat (scalar.val st.env.toValuation)).testBit (4 * rounds - 1 - (4 * j + k))
        then 1 else 0 := by
  have h := encodes_vector_iff.mp (encodes_extendMany_new
    (var := Vector (Vector (FVar F) 4) rounds) st
    (bitVals (F := F) rounds (ToNat.toNat (scalar.val st.env.toValuation)))) j hj
  refine (encodes_fvar_iff.mp (encodes_vector_iff.mp h k hk)).trans ?_
  simp [bitVals]

/-- `accX`/`accY`/`accN` at the walk are the next row's input cells. -/
private theorem accX_chainBuild [Field F] [DecidableEq F]
    (eb xT yT xP0 yP0 n0 : F) (bsv : ℕ → F × F × F × F) (m : ℕ) :
    Kimchi.Gate.EndoMul.accX (fun i => Kimchi.Gate.EndoMul.chainBuild
        eb xT yT xP0 yP0 n0 bsv i) m
      = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv m).xP := by
  cases m <;> rfl

private theorem accY_chainBuild [Field F] [DecidableEq F]
    (eb xT yT xP0 yP0 n0 : F) (bsv : ℕ → F × F × F × F) (m : ℕ) :
    Kimchi.Gate.EndoMul.accY (fun i => Kimchi.Gate.EndoMul.chainBuild
        eb xT yT xP0 yP0 n0 bsv i) m
      = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv m).yP := by
  cases m <;> rfl

private theorem accN_chainBuild [Field F] [DecidableEq F]
    (eb xT yT xP0 yP0 n0 : F) (bsv : ℕ → F × F × F × F) (m : ℕ) :
    Kimchi.Gate.EndoMul.accN (fun i => Kimchi.Gate.EndoMul.chainBuild
        eb xT yT xP0 yP0 n0 bsv i) m
      = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv m).n := by
  cases m <;> rfl

/-- The walk's base and bit cells are the arguments, at every row. -/
private theorem chainBuild_fields [Field F] [DecidableEq F]
    (eb xT yT xP0 yP0 n0 : F) (bsv : ℕ → F × F × F × F) (m : ℕ) :
    (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv m).xT = xT
    ∧ (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv m).yT = yT
    ∧ (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv m).b1 = (bsv m).1
    ∧ (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv m).b2 = (bsv m).2.1
    ∧ (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv m).b3 = (bsv m).2.2.1
    ∧ (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv m).b4 = (bsv m).2.2.2 := by
  cases m <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Row `r`'s four bits of the `4·rounds`-bit scalar `n`, as `chainBuild` consumes
them. -/
private def bitRows [Zero F] [One F] (rounds n r : ℕ) : F × F × F × F :=
  ((if n.testBit (4 * rounds - 1 - (4 * r + 0)) then 1 else 0),
   (if n.testBit (4 * rounds - 1 - (4 * r + 1)) then 1 else 0),
   (if n.testBit (4 * rounds - 1 - (4 * r + 2)) then 1 else 0),
   (if n.testBit (4 * rounds - 1 - (4 * r + 3)) then 1 else 0))

/-- The rounds' fold, read: from a state reading the chain's row-`i` inputs, over rows
reading the chain's bits, the fold grows the table, its state reads the chain's
row-`(i + l.length)` inputs, and the collected rounds pass the chain check at those
finals — the `m` rows of the chain holding. -/
private theorem roundsRun_inv [Field F] [DecidableEq F] (eb xT yT xP0 yP0 n0 : F)
    (bsv : ℕ → F × F × F × F) (m : ℕ)
    (hH : ∀ j, j < m → Kimchi.Gate.EndoMul.Holds eb
      (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv j))
    (t : AffinePoint (FVar F)) :
    ∀ (l : List (Vector (FVar F) 4)) (i : ℕ) (st : ProverState F)
      (acc : AffinePoint (FVar F) × FVar F),
      i + l.length ≤ m →
      t.x.Scoped st → t.y.Scoped st →
      t.x.val st.env.toValuation = xT → t.y.val st.env.toValuation = yT →
      (∀ j (hj : j < l.length) (k : ℕ) (hk : k < 4), (l[j][k]).Scoped st) →
      (∀ j (hj : j < l.length),
        ((l[j][0]).val st.env.toValuation, (l[j][1]).val st.env.toValuation,
          (l[j][2]).val st.env.toValuation, (l[j][3]).val st.env.toValuation) = bsv (i + j)) →
      acc.1.x.Scoped st → acc.1.y.Scoped st → acc.2.Scoped st →
      acc.1.x.val st.env.toValuation
        = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv i).xP →
      acc.1.y.val st.env.toValuation
        = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv i).yP →
      acc.2.val st.env.toValuation
        = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv i).n →
      st.env.Le (mapAccumRun (roundRun eb t) st acc l).1.env ∧
      ((mapAccumRun (roundRun eb t) st acc l).2.2.1.x.Scoped
          (mapAccumRun (roundRun eb t) st acc l).1 ∧
        (mapAccumRun (roundRun eb t) st acc l).2.2.1.y.Scoped
          (mapAccumRun (roundRun eb t) st acc l).1 ∧
        (mapAccumRun (roundRun eb t) st acc l).2.2.2.Scoped
          (mapAccumRun (roundRun eb t) st acc l).1) ∧
      ((mapAccumRun (roundRun eb t) st acc l).2.2.1.x.val
          (mapAccumRun (roundRun eb t) st acc l).1.env.toValuation
          = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv (i + l.length)).xP ∧
        (mapAccumRun (roundRun eb t) st acc l).2.2.1.y.val
          (mapAccumRun (roundRun eb t) st acc l).1.env.toValuation
          = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv (i + l.length)).yP ∧
        (mapAccumRun (roundRun eb t) st acc l).2.2.2.val
          (mapAccumRun (roundRun eb t) st acc l).1.env.toValuation
          = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv (i + l.length)).n) ∧
      EndoMul.chainOk (mapAccumRun (roundRun eb t) st acc l).1.env eb
        ((Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv (i + l.length)).xP,
         (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv (i + l.length)).yP,
         (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv (i + l.length)).n)
        (mapAccumRun (roundRun eb t) st acc l).2.1 = true
  | [], i, st, acc, _, _, _, _, _, _, _, hax, hay, han, hva, hvb, hvn => by
    refine ⟨Assignments.Le.refl _, ⟨hax, hay, han⟩, ?_, rfl⟩
    simp only [mapAccumRun, List.length_nil, Nat.add_zero]
    exact ⟨hva, hvb, hvn⟩
  | x :: l, i, st, acc, hlen, htx, hty, htxv, htyv, hbs, hbv, hax, hay, han, hva, hvb, hvn => by
    have hb := hbv 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hb
    have hb1v := congrArg Prod.fst hb
    have hb2v := congrArg (fun p : F × F × F × F => p.2.1) hb
    have hb3v := congrArg (fun p : F × F × F × F => p.2.2.1) hb
    have hb4v := congrArg (fun p : F × F × F × F => p.2.2.2) hb
    simp only [] at hb1v hb2v hb3v hb4v
    have hbs0 : ∀ k (hk : k < 4), (x[k]).Scoped st := fun k hk => by
      simpa using hbs 0 (by simp) k hk
    obtain ⟨hfxT, hfyT, hfb1, hfb2, hfb3, hfb4⟩ :=
      chainBuild_fields eb xT yT xP0 yP0 n0 bsv i
    have hw : Kimchi.Gate.EndoMul.build eb (t.x.val st.env.toValuation)
        (t.y.val st.env.toValuation) (acc.1.x.val st.env.toValuation)
        (acc.1.y.val st.env.toValuation) (acc.2.val st.env.toValuation)
        (x[0].val st.env.toValuation) (x[1].val st.env.toValuation)
        (x[2].val st.env.toValuation) (x[3].val st.env.toValuation)
        = Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv i := by
      rw [htxv, htyv, hva, hvb, hvn, hb1v, hb2v, hb3v, hb4v]
      exact (Kimchi.Gate.EndoMul.chainBuild_eta eb xT yT xP0 yP0 n0 bsv i).symm
    have hle₁ : st.env.Le (roundRun eb t st acc x).1.env := st.le_extendMany _
    have hs₀ : (roundRun eb t st acc x).2.1.inv.Scoped (roundRun eb t st acc x).1 :=
      ProverState.mem_extendMany_head ..
    have hs₁ : (roundRun eb t st acc x).2.2.2.Scoped (roundRun eb t st acc x).1 :=
      st.new_mem_extendMany (i := 1) (by simp)
    have hs₂ : (roundRun eb t st acc x).2.1.r.x.Scoped (roundRun eb t st acc x).1 :=
      st.new_mem_extendMany (i := 2) (by simp)
    have hs₃ : (roundRun eb t st acc x).2.1.r.y.Scoped (roundRun eb t st acc x).1 :=
      st.new_mem_extendMany (i := 3) (by simp)
    have hs₄ : (roundRun eb t st acc x).2.2.1.x.Scoped (roundRun eb t st acc x).1 :=
      st.new_mem_extendMany (i := 4) (by simp)
    have hs₅ : (roundRun eb t st acc x).2.2.1.y.Scoped (roundRun eb t st acc x).1 :=
      st.new_mem_extendMany (i := 5) (by simp)
    have hs₆ : (roundRun eb t st acc x).2.1.s1.Scoped (roundRun eb t st acc x).1 :=
      st.new_mem_extendMany (i := 6) (by simp)
    have hs₇ : (roundRun eb t st acc x).2.1.s3.Scoped (roundRun eb t st acc x).1 :=
      st.new_mem_extendMany (i := 7) (by simp)
    have hv₀ : (roundRun eb t st acc x).2.1.inv.val (roundRun eb t st acc x).1.env.toValuation
        = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv i).inv := by
      show (roundRun eb t st acc x).1.env.toValuation st.nv = _
      simp only [roundRun, ProverState.get_extendMany_head, hw]
    have hv₁ : (roundRun eb t st acc x).2.2.2.val (roundRun eb t st acc x).1.env.toValuation
        = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv i).nPrime := by
      show (roundRun eb t st acc x).1.env.toValuation (st.nv + 1) = _
      simp only [roundRun]
      rw [ProverState.get_extendMany_new st (by simp), hw]
      rfl
    have hv₂ : (roundRun eb t st acc x).2.1.r.x.val (roundRun eb t st acc x).1.env.toValuation
        = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv i).xR := by
      show (roundRun eb t st acc x).1.env.toValuation (st.nv + 2) = _
      simp only [roundRun]
      rw [ProverState.get_extendMany_new st (by simp), hw]
      rfl
    have hv₃ : (roundRun eb t st acc x).2.1.r.y.val (roundRun eb t st acc x).1.env.toValuation
        = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv i).yR := by
      show (roundRun eb t st acc x).1.env.toValuation (st.nv + 3) = _
      simp only [roundRun]
      rw [ProverState.get_extendMany_new st (by simp), hw]
      rfl
    have hv₄ : (roundRun eb t st acc x).2.2.1.x.val (roundRun eb t st acc x).1.env.toValuation
        = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv i).xS := by
      show (roundRun eb t st acc x).1.env.toValuation (st.nv + 4) = _
      simp only [roundRun]
      rw [ProverState.get_extendMany_new st (by simp), hw]
      rfl
    have hv₅ : (roundRun eb t st acc x).2.2.1.y.val (roundRun eb t st acc x).1.env.toValuation
        = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv i).yS := by
      show (roundRun eb t st acc x).1.env.toValuation (st.nv + 5) = _
      simp only [roundRun]
      rw [ProverState.get_extendMany_new st (by simp), hw]
      rfl
    have hv₆ : (roundRun eb t st acc x).2.1.s1.val (roundRun eb t st acc x).1.env.toValuation
        = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv i).s1 := by
      show (roundRun eb t st acc x).1.env.toValuation (st.nv + 6) = _
      simp only [roundRun]
      rw [ProverState.get_extendMany_new st (by simp), hw]
      rfl
    have hv₇ : (roundRun eb t st acc x).2.1.s3.val (roundRun eb t st acc x).1.env.toValuation
        = (Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv i).s3 := by
      show (roundRun eb t st acc x).1.env.toValuation (st.nv + 7) = _
      simp only [roundRun]
      rw [ProverState.get_extendMany_new st (by simp), hw]
      rfl
    have hbsl : ∀ j (hj : j < l.length) (k : ℕ) (hk : k < 4), (l[j][k]).Scoped st :=
      fun j hj k hk => by simpa using hbs (j + 1) (by simpa using hj) k hk
    have ih := roundsRun_inv eb xT yT xP0 yP0 n0 bsv m hH t l (i + 1) (roundRun eb t st acc x).1
      (roundRun eb t st acc x).2.2
      (by simp only [List.length_cons] at hlen; omega)
      (htx.of_le hle₁) (hty.of_le hle₁)
      (by rw [CVar.val_of_le hle₁ htx, htxv]) (by rw [CVar.val_of_le hle₁ hty, htyv])
      (fun j hj k hk => (hbsl j hj k hk).of_le hle₁)
      (fun j hj => by
        have h := hbv (j + 1) (by simpa using hj)
        simp only [List.getElem_cons_succ] at h
        rw [show i + 1 + j = i + (j + 1) by omega, ← h,
          CVar.val_of_le hle₁ (hbsl j hj 0 (by omega)), CVar.val_of_le hle₁ (hbsl j hj 1 (by omega)),
          CVar.val_of_le hle₁ (hbsl j hj 2 (by omega)), CVar.val_of_le hle₁ (hbsl j hj 3 (by omega))])
      hs₄ hs₅ hs₁ hv₄ hv₅ hv₁
    have hle := hle₁.trans ih.1
    simp only [mapAccumRun, List.length_cons]
    rw [show i + (l.length + 1) = i + 1 + l.length by omega]
    refine ⟨hle, ih.2.1, ih.2.2.1, ?_⟩
    refine chainOk_cons (w := Kimchi.Gate.EndoMul.chainBuild eb xT yT xP0 yP0 n0 bsv i) ?_
      ((Kimchi.Gate.EndoMul.ok_iff eb _).mpr (hH i (by simp only [List.length_cons] at hlen; omega)))
      ?_ ?_ ih.2.2.2
    · refine evalWith_ok_iff.mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
      · show t.x.eval _ = _
        rw [CVar.eval_eq_val (htx.of_le hle), CVar.val_of_le hle htx, htxv, hfxT]
      · show t.y.eval _ = _
        rw [CVar.eval_eq_val (hty.of_le hle), CVar.val_of_le hle hty, htyv, hfyT]
      · show acc.1.x.eval _ = _
        rw [CVar.eval_eq_val (hax.of_le hle), CVar.val_of_le hle hax, hva]
      · show acc.1.y.eval _ = _
        rw [CVar.eval_eq_val (hay.of_le hle), CVar.val_of_le hle hay, hvb]
      · show acc.2.eval _ = _
        rw [CVar.eval_eq_val (han.of_le hle), CVar.val_of_le hle han, hvn]
      · show x[0].eval _ = _
        rw [CVar.eval_eq_val ((hbs0 0 (by omega)).of_le hle), CVar.val_of_le hle (hbs0 0 (by omega)),
          hb1v, hfb1]
      · show x[1].eval _ = _
        rw [CVar.eval_eq_val ((hbs0 1 (by omega)).of_le hle), CVar.val_of_le hle (hbs0 1 (by omega)),
          hb2v, hfb2]
      · show x[2].eval _ = _
        rw [CVar.eval_eq_val ((hbs0 2 (by omega)).of_le hle), CVar.val_of_le hle (hbs0 2 (by omega)),
          hb3v, hfb3]
      · show x[3].eval _ = _
        rw [CVar.eval_eq_val ((hbs0 3 (by omega)).of_le hle), CVar.val_of_le hle (hbs0 3 (by omega)),
          hb4v, hfb4]
      · show (roundRun eb t st acc x).2.1.s1.eval _ = _
        rw [CVar.eval_eq_val (hs₆.of_le ih.1), CVar.val_of_le ih.1 hs₆, hv₆]
      · show (roundRun eb t st acc x).2.1.r.x.eval _ = _
        rw [CVar.eval_eq_val (hs₂.of_le ih.1), CVar.val_of_le ih.1 hs₂, hv₂]
      · show (roundRun eb t st acc x).2.1.r.y.eval _ = _
        rw [CVar.eval_eq_val (hs₃.of_le ih.1), CVar.val_of_le ih.1 hs₃, hv₃]
      · show (roundRun eb t st acc x).2.1.s3.eval _ = _
        rw [CVar.eval_eq_val (hs₇.of_le ih.1), CVar.val_of_le ih.1 hs₇, hv₇]
      · show (roundRun eb t st acc x).2.1.inv.eval _ = _
        rw [CVar.eval_eq_val (hs₀.of_le ih.1), CVar.val_of_le ih.1 hs₀, hv₀]
    · intro hnil
      cases l with
      | nil => rfl
      | cons y l' => simp [mapAccumRun] at hnil
    · intro r' rest' hcons
      cases l with
      | nil => simp [mapAccumRun] at hcons
      | cons y l' =>
        simp only [mapAccumRun, List.cons.injEq] at hcons
        obtain ⟨rfl, -⟩ := hcons
        refine ⟨?_, ?_, ?_⟩
        · show (roundRun eb t st acc x).2.2.1.x.eval _ = _
          rw [CVar.eval_eq_val (hs₄.of_le ih.1), CVar.val_of_le ih.1 hs₄, hv₄]
        · show (roundRun eb t st acc x).2.2.1.y.eval _ = _
          rw [CVar.eval_eq_val (hs₅.of_le ih.1), CVar.val_of_le ih.1 hs₅, hv₅]
        · show (roundRun eb t st acc x).2.2.2.eval _ = _
          rw [CVar.eval_eq_val (hs₁.of_le ih.1), CVar.val_of_le ih.1 hs₁, hv₁]

/-- The state and result of `endoMul`'s honest run: the bit table, the sealed `β·x`,
the two pinned additions, the window rounds. -/
def endoMulRun [Field F] [DecidableEq F] [ToNat F] (eb : F) (rounds : ℕ) (st : ProverState F)
    (g : AffinePoint (FVar F)) (scalar : SizedF (4 * rounds) (FVar F)) :
    ProverState F × AffinePoint (FVar F) :=
  let st₁ := bitState st rounds scalar.val
  let r₂ := sealRun st₁ (CVar.scale_ eb g.x)
  let r₃ := AddFast.addFastRun r₂.1 .checkFinite g ⟨r₂.2, g.y⟩
  let r₄ := AddFast.addFastRun r₃.1 .checkFinite r₃.2.p r₃.2.p
  let r := mapAccumRun (roundRun eb g) r₄.1 (r₄.2.p, .const 0) (bitVarsOf st rounds).toList
  (r.1, r.2.2.1)

open Kimchi.Gate.VarBaseMul (y_ne_zero_of_odd_order smul_ne_zero_of_lt) in
/-- The init segment at an on-curve base: both additions' operand conditions hold, and
the state and point it lands at (named) extend the table, keep `P₀` in scope, and read
it on-curve as `[2]·T + [2]·φT`. -/
private theorem init_facts [Field F] [DecidableEq F] [d : HasEndo F] (st : ProverState F)
    {g : AffinePoint (FVar F)} (hx : g.x.Scoped st) (hy : g.y.Scoped st)
    (hT : d.W.Nonsingular (g.x.val st.env.toValuation) (g.y.val st.env.toValuation)) :
    ∃ (st₄ : ProverState F) (P0 : AddResult F),
      AddFast.addFastRun
          (AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
            ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).1 .checkFinite
          (AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
            ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).2.p
          (AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
            ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).2.p
        = (st₄, P0) ∧
      AddFast.Operands d.toHasCurve .checkFinite
        (g.x.val (sealRun st (CVar.scale_ d.endo g.x)).1.env.toValuation)
        (g.y.val (sealRun st (CVar.scale_ d.endo g.x)).1.env.toValuation)
        ((sealRun st (CVar.scale_ d.endo g.x)).2.val
          (sealRun st (CVar.scale_ d.endo g.x)).1.env.toValuation)
        (g.y.val (sealRun st (CVar.scale_ d.endo g.x)).1.env.toValuation) ∧
      AddFast.Operands d.toHasCurve .checkFinite
        ((AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
            ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).2.p.x.val
          (AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
            ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).1.env.toValuation)
        ((AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
            ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).2.p.y.val
          (AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
            ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).1.env.toValuation)
        ((AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
            ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).2.p.x.val
          (AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
            ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).1.env.toValuation)
        ((AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
            ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).2.p.y.val
          (AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
            ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).1.env.toValuation) ∧
      st.env.Le st₄.env ∧ P0.p.x.Scoped st₄ ∧ P0.p.y.Scoped st₄ ∧
      ∃ hP0 : d.W.Nonsingular (P0.p.x.val st₄.env.toValuation) (P0.p.y.val st₄.env.toValuation),
        Point.some _ _ hP0
          = (2 : ℤ) • Point.some _ _ hT + (2 : ℤ) • Point.some _ _ (d.endo_nonsingular hT) := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have hφT := d.endo_nonsingular hT
  have hTne : Point.some _ _ hT ≠ 0 := Point.some_ne_zero hT
  have hyne : g.y.val st.env.toValuation ≠ 0 := y_ne_zero_of_odd_order d.W d.odd hT
  have hTφne : Point.some _ _ hT + Point.some _ _ hφT ≠ 0 := by
    intro hzero
    rw [d.eigen hT hφT] at hzero
    exact d.lam_succ_smul (Point.some _ _ hT) hTne (by rw [← hzero]; module)
  -- the sealed `β·x`
  have hg₂ := sealRun_grants (st := st) (CVar.Scoped.scale_ d.endo hx)
  have hle₂ := hg₂.le
  have hx₂ := CVar.val_of_le hle₂ hx
  have hy₂ := CVar.val_of_le hle₂ hy
  have hφ₂ : (sealRun st (CVar.scale_ d.endo g.x)).2.val
      (sealRun st (CVar.scale_ d.endo g.x)).1.env.toValuation
      = d.endo * g.x.val st.env.toValuation := by
    rw [hg₂.fvar_val, CVar.val_scale_]
  have hT₂ : d.W.Nonsingular (g.x.val (sealRun st (CVar.scale_ d.endo g.x)).1.env.toValuation)
      (g.y.val (sealRun st (CVar.scale_ d.endo g.x)).1.env.toValuation) := by
    rw [hx₂, hy₂]; exact hT
  have hφT₂ : d.W.Nonsingular ((sealRun st (CVar.scale_ d.endo g.x)).2.val
      (sealRun st (CVar.scale_ d.endo g.x)).1.env.toValuation)
      (g.y.val (sealRun st (CVar.scale_ d.endo g.x)).1.env.toValuation) := by
    rw [hφ₂, hy₂]; exact hφT
  have hsum₂ : Point.some _ _ hT₂ + Point.some _ _ hφT₂
      = Point.some _ _ hT + Point.some _ _ hφT := by
    rw [Kimchi.Gate.EndoMul.some_congr d.W hT₂ hT hx₂ hy₂,
      Kimchi.Gate.EndoMul.some_congr d.W hφT₂ hφT hφ₂ hy₂]
  have hops₁ : AddFast.Operands d.toHasCurve .checkFinite
      (g.x.val (sealRun st (CVar.scale_ d.endo g.x)).1.env.toValuation)
      (g.y.val (sealRun st (CVar.scale_ d.endo g.x)).1.env.toValuation)
      ((sealRun st (CVar.scale_ d.endo g.x)).2.val
        (sealRun st (CVar.scale_ d.endo g.x)).1.env.toValuation)
      (g.y.val (sealRun st (CVar.scale_ d.endo g.x)).1.env.toValuation) :=
    ⟨hT₂, hφT₂, by rw [hy₂]; exact hyne, fun _ => by rw [hsum₂]; exact hTφne⟩
  -- `P₁ = T + φT`
  have hg₃ := AddFast.addFastRun_grants (p2' := ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩)
    .checkFinite (sealRun st (CVar.scale_ d.endo g.x)).1 (hx.of_le hle₂) (hy.of_le hle₂)
    hg₂.fvar_scoped (hy.of_le hle₂) hops₁
  obtain ⟨hle₃, hs3x, hs3y, -, hsum₃⟩ := hg₃
  obtain ⟨hP1, -, hP1eq⟩ := (hsum₃ hT₂ hφT₂).resolve_left (by
    rintro ⟨-, hzero⟩
    rw [hsum₂] at hzero
    exact hTφne hzero)
  have hy1ne := y_ne_zero_of_odd_order d.W d.odd hP1
  have h2P1ne : Point.some _ _ hP1 + Point.some _ _ hP1 ≠ 0 := by
    intro hzero
    have h2P : (2 : ℤ) • Point.some _ _ hP1 = 0 := by rw [two_zsmul, hzero]
    have hlt : (2 : ℤ) < (d.W.order : ℤ) := by
      have hp2' := d.prime.two_le
      have h3' : 3 ≤ d.W.order := by
        rcases Nat.lt_or_ge 2 d.W.order with h | h
        · omega
        · exact absurd (by omega : d.W.order = 2) d.odd
      exact_mod_cast h3'
    exact smul_ne_zero_of_lt d.W (Point.some_ne_zero hP1) (by norm_num) hlt h2P
  have hops₂ : AddFast.Operands d.toHasCurve .checkFinite
      ((AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
          ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).2.p.x.val
        (AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
          ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).1.env.toValuation)
      ((AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
          ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).2.p.y.val
        (AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
          ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).1.env.toValuation)
      ((AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
          ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).2.p.x.val
        (AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
          ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).1.env.toValuation)
      ((AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
          ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).2.p.y.val
        (AddFast.addFastRun (sealRun st (CVar.scale_ d.endo g.x)).1 .checkFinite g
          ⟨(sealRun st (CVar.scale_ d.endo g.x)).2, g.y⟩).1.env.toValuation) :=
    ⟨hP1, hP1, hy1ne, fun _ => h2P1ne⟩
  -- `P₀ = P₁ + P₁`
  have hg₄ := AddFast.addFastRun_grants .checkFinite _ hs3x hs3y hs3x hs3y hops₂
  obtain ⟨hle₄, hs4x, hs4y, -, hsum₄⟩ := hg₄
  obtain ⟨hP0, -, hP0eq⟩ := (hsum₄ hP1 hP1).resolve_left (by
    rintro ⟨-, hzero⟩
    exact h2P1ne hzero)
  refine ⟨_, _, Prod.mk.eta.symm, hops₁, hops₂, hle₂.trans (hle₃.trans hle₄), hs4x, hs4y,
    hP0, ?_⟩
  rw [← hP0eq, ← hP1eq, hsum₂]
  module

/-- The honest walk from the init point: every row holds, its crumb list is the
scalar's canonical crumbs, and the final register reconstructs the scalar. -/
private theorem chain_facts [Field F] [DecidableEq F] [d : HasEndo F] (rounds : ℕ)
    (hbits : 4 * rounds ≤ 244) {xv yv x0v y0v : F} (hT : d.W.Nonsingular xv yv)
    (hP0 : d.W.Nonsingular x0v y0v)
    (hP0eq : Point.some _ _ hP0
      = (2 : ℤ) • Point.some _ _ hT + (2 : ℤ) • Point.some _ _ (d.endo_nonsingular hT))
    (n : ℕ) (hn : n < 4 ^ (2 * rounds)) :
    (∀ j, j < rounds → Kimchi.Gate.EndoMul.Holds d.endo
      (Kimchi.Gate.EndoMul.chainBuild d.endo xv yv x0v y0v 0 (bitRows rounds n) j)) ∧
    Kimchi.Gate.EndoMul.crumbList
        (fun i => Kimchi.Gate.EndoMul.chainBuild d.endo xv yv x0v y0v 0 (bitRows rounds n) i)
        rounds
      = Kimchi.Gate.EndoScalar.crumbsOf (2 * rounds) n ∧
    (Kimchi.Gate.EndoMul.chainBuild d.endo xv yv x0v y0v 0 (bitRows rounds n) rounds).n
      = (n : F) := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have hTne : Point.some _ _ hT ≠ 0 := Point.some_ne_zero hT
  have hφT := d.endo_nonsingular hT
  have hbit01 : ∀ c : Bool,
      (if c then (1 : F) else 0) = 0 ∨ (if c then (1 : F) else 0) = 1 := by
    intro c
    cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hbsb : ∀ i, ((bitRows (F := F) rounds n i).1 = 0 ∨ (bitRows (F := F) rounds n i).1 = 1)
      ∧ ((bitRows (F := F) rounds n i).2.1 = 0 ∨ (bitRows (F := F) rounds n i).2.1 = 1)
      ∧ ((bitRows (F := F) rounds n i).2.2.1 = 0 ∨ (bitRows (F := F) rounds n i).2.2.1 = 1)
      ∧ ((bitRows (F := F) rounds n i).2.2.2 = 0 ∨ (bitRows (F := F) rounds n i).2.2.2 = 1) :=
    fun i => ⟨hbit01 _, hbit01 _, hbit01 _, hbit01 _⟩
  have hH := Kimchi.Gate.EndoMul.chain_complete d.W (Point.some _ _ hT) (Point.some _ _ hφT)
    (fun a b ha' hb' hba hbb => d.off_targets ha' hb' hba hbb hTne (d.eigen hT hφT))
    rounds hbits hT hφT rfl rfl (bitRows rounds n) hbsb 0 hP0 hP0eq
  have hcl : Kimchi.Gate.EndoMul.crumbList
      (fun i => Kimchi.Gate.EndoMul.chainBuild d.endo xv yv x0v y0v 0 (bitRows rounds n) i) rounds
      = Kimchi.Gate.EndoScalar.crumbsOf (2 * rounds) n := by
    refine Kimchi.Gate.EndoMul.crumbList_ofBits rounds n _ (fun r hr => ?_)
    obtain ⟨-, -, hb1', hb2', hb3', hb4'⟩ :=
      chainBuild_fields d.endo xv yv x0v y0v 0 (bitRows rounds n) r
    exact ⟨by rw [hb1']; rfl, by rw [hb2']; rfl, by rw [hb3']; rfl, by rw [hb4']; rfl⟩
  refine ⟨hH, hcl, ?_⟩
  have hchain := Kimchi.Gate.EndoMul.chain_nAcc d.endo rounds
    (fun i => Kimchi.Gate.EndoMul.chainBuild d.endo xv yv x0v y0v 0 (bitRows rounds n) i)
    hH (fun i _ => rfl)
  rw [accN_chainBuild, accN_chainBuild, hcl,
    Kimchi.Gate.EndoScalar.nReconstruct_crumbsOf, Nat.mod_eq_of_lt hn] at hchain
  rw [hchain]
  show (0 : F) * 4 ^ (2 * rounds) + (n : F) = (n : F)
  rw [zero_mul, zero_add]

/-- The rounds' run at the honest init: the init point (named) reads on-curve as
`[2]·T + [2]·φT`, the walk from it holds row by row with the scalar's crumbs, and the
rounds' fold lands at a state (named) reading the chain's finals, the collected rounds
passing the chain check there. -/
private theorem walk_facts [Field F] [DecidableEq F] [ToNat F] [d : HasEndo F]
    (rounds : ℕ) (hbits : 4 * rounds ≤ 244) (st : ProverState F) {g : AffinePoint (FVar F)}
    {scalar : SizedF (4 * rounds) (FVar F)} (hx : g.x.Scoped st) (hy : g.y.Scoped st)
    (hfits : scalar.Fits st.env.toValuation)
    (hT : d.W.Nonsingular (g.x.val st.env.toValuation) (g.y.val st.env.toValuation)) :
    ∃ (st₄ : ProverState F) (P0 : AddResult F) (stR : ProverState F)
      (w : List (EndoMulRound F) × (AffinePoint (FVar F) × FVar F)) (n : ℕ) (xP0 yP0 : F)
      (hP0 : d.W.Nonsingular xP0 yP0),
      AddFast.addFastRun
          (AddFast.addFastRun
            (sealRun (bitState st rounds scalar.val) (CVar.scale_ d.endo g.x)).1 .checkFinite g
            ⟨(sealRun (bitState st rounds scalar.val) (CVar.scale_ d.endo g.x)).2, g.y⟩).1
          .checkFinite
          (AddFast.addFastRun
            (sealRun (bitState st rounds scalar.val) (CVar.scale_ d.endo g.x)).1 .checkFinite g
            ⟨(sealRun (bitState st rounds scalar.val) (CVar.scale_ d.endo g.x)).2, g.y⟩).2.p
          (AddFast.addFastRun
            (sealRun (bitState st rounds scalar.val) (CVar.scale_ d.endo g.x)).1 .checkFinite g
            ⟨(sealRun (bitState st rounds scalar.val) (CVar.scale_ d.endo g.x)).2, g.y⟩).2.p
        = (st₄, P0) ∧
      mapAccumRun (roundRun d.endo g) st₄ (P0.p, .const 0) (bitVarsOf st rounds).toList
        = (stR, w) ∧
      n = ToNat.toNat (scalar.val.val st.env.toValuation) ∧
      P0.p.x.val st₄.env.toValuation = xP0 ∧ P0.p.y.val st₄.env.toValuation = yP0 ∧
      st.env.Le st₄.env ∧ st₄.env.Le stR.env ∧
      (∀ j, j < rounds → Kimchi.Gate.EndoMul.Holds d.endo
        (Kimchi.Gate.EndoMul.chainBuild d.endo (g.x.val st.env.toValuation)
          (g.y.val st.env.toValuation) xP0 yP0 0 (bitRows rounds n) j)) ∧
      Kimchi.Gate.EndoMul.crumbList
          (fun j => Kimchi.Gate.EndoMul.chainBuild d.endo (g.x.val st.env.toValuation)
            (g.y.val st.env.toValuation) xP0 yP0 0 (bitRows rounds n) j) rounds
        = Kimchi.Gate.EndoScalar.crumbsOf (2 * rounds) n ∧
      (Kimchi.Gate.EndoMul.chainBuild d.endo (g.x.val st.env.toValuation)
        (g.y.val st.env.toValuation) xP0 yP0 0 (bitRows rounds n) rounds).n = (n : F) ∧
      (w.2.1.x.Scoped stR ∧ w.2.1.y.Scoped stR ∧ w.2.2.Scoped stR) ∧
      (w.2.1.x.val stR.env.toValuation
          = (Kimchi.Gate.EndoMul.chainBuild d.endo (g.x.val st.env.toValuation)
            (g.y.val st.env.toValuation) xP0 yP0 0 (bitRows rounds n) rounds).xP ∧
        w.2.1.y.val stR.env.toValuation
          = (Kimchi.Gate.EndoMul.chainBuild d.endo (g.x.val st.env.toValuation)
            (g.y.val st.env.toValuation) xP0 yP0 0 (bitRows rounds n) rounds).yP ∧
        w.2.2.val stR.env.toValuation
          = (Kimchi.Gate.EndoMul.chainBuild d.endo (g.x.val st.env.toValuation)
            (g.y.val st.env.toValuation) xP0 yP0 0 (bitRows rounds n) rounds).n) ∧
      EndoMul.chainOk stR.env d.endo
        ((Kimchi.Gate.EndoMul.chainBuild d.endo (g.x.val st.env.toValuation)
            (g.y.val st.env.toValuation) xP0 yP0 0 (bitRows rounds n) rounds).xP,
         (Kimchi.Gate.EndoMul.chainBuild d.endo (g.x.val st.env.toValuation)
            (g.y.val st.env.toValuation) xP0 yP0 0 (bitRows rounds n) rounds).yP,
         (Kimchi.Gate.EndoMul.chainBuild d.endo (g.x.val st.env.toValuation)
            (g.y.val st.env.toValuation) xP0 yP0 0 (bitRows rounds n) rounds).n)
        w.1 = true ∧
      Point.some _ _ hP0
        = (2 : ℤ) • Point.some _ _ hT + (2 : ℤ) • Point.some _ _ (d.endo_nonsingular hT) := by
  have hle₁ := bitState_le st rounds scalar.val
  have hx₁ := CVar.val_of_le hle₁ hx
  have hy₁ := CVar.val_of_le hle₁ hy
  have hT₁ : d.W.Nonsingular (g.x.val (bitState st rounds scalar.val).env.toValuation)
      (g.y.val (bitState st rounds scalar.val).env.toValuation) := by
    rw [hx₁, hy₁]; exact hT
  obtain ⟨st₄, P0, heq₄, -, -, hle₄, hs4x, hs4y, hP0, hP0eq⟩ :=
    init_facts (bitState st rounds scalar.val) (hx.of_le hle₁) (hy.of_le hle₁) hT₁
  have hP0eq' : Point.some _ _ hP0
      = (2 : ℤ) • Point.some _ _ hT + (2 : ℤ) • Point.some _ _ (d.endo_nonsingular hT) := by
    rw [hP0eq, Kimchi.Gate.EndoMul.some_congr d.W hT₁ hT hx₁ hy₁,
      Kimchi.Gate.EndoMul.some_congr d.W (d.endo_nonsingular hT₁) (d.endo_nonsingular hT)
        (by rw [hx₁]) hy₁]
  have hrange : ToNat.toNat (scalar.val.val st.env.toValuation) < 4 ^ (2 * rounds) := by
    have hpow : (4 : ℕ) ^ (2 * rounds) = 2 ^ (4 * rounds) := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
      congr 1
      ring
    rw [hpow]
    exact hfits
  obtain ⟨hH, hcl, hreg⟩ := chain_facts rounds hbits hT hP0 hP0eq' _ hrange
  have hle₁₄ := hle₁.trans hle₄
  have hinv := roundsRun_inv d.endo (g.x.val st.env.toValuation) (g.y.val st.env.toValuation)
    (P0.p.x.val st₄.env.toValuation) (P0.p.y.val st₄.env.toValuation) 0
    (bitRows rounds (ToNat.toNat (scalar.val.val st.env.toValuation))) rounds hH g
    (bitVarsOf st rounds).toList 0 st₄ (P0.p, .const 0)
    (by simp) (hx.of_le hle₁₄) (hy.of_le hle₁₄) (CVar.val_of_le hle₁₄ hx)
    (CVar.val_of_le hle₁₄ hy)
    (fun j hj k hk => by
      simp only [Vector.getElem_toList]
      exact (bitVarsOf_scoped st rounds scalar.val j (by simpa using hj) k hk).of_le hle₄)
    (fun j hj => by
      have hj' : j < rounds := by simpa using hj
      simp only [Vector.getElem_toList, Nat.zero_add]
      rw [CVar.val_of_le hle₄ (bitVarsOf_scoped st rounds scalar.val j hj' 0 (by omega)),
        CVar.val_of_le hle₄ (bitVarsOf_scoped st rounds scalar.val j hj' 1 (by omega)),
        CVar.val_of_le hle₄ (bitVarsOf_scoped st rounds scalar.val j hj' 2 (by omega)),
        CVar.val_of_le hle₄ (bitVarsOf_scoped st rounds scalar.val j hj' 3 (by omega)),
        bitVarsOf_val st rounds scalar.val j hj' 0 (by omega),
        bitVarsOf_val st rounds scalar.val j hj' 1 (by omega),
        bitVarsOf_val st rounds scalar.val j hj' 2 (by omega),
        bitVarsOf_val st rounds scalar.val j hj' 3 (by omega)]
      rfl)
    hs4x hs4y (CVar.scoped_const _ _)
    (by simp only [Kimchi.Gate.EndoMul.chainBuild, Kimchi.Gate.EndoMul.build])
    (by simp only [Kimchi.Gate.EndoMul.chainBuild, Kimchi.Gate.EndoMul.build])
    (by simp [CVar.val, Kimchi.Gate.EndoMul.chainBuild, Kimchi.Gate.EndoMul.build])
  obtain ⟨hleR, hsc, hrd, hchk⟩ := hinv
  simp only [Vector.length_toList, Nat.zero_add] at hrd hchk
  exact ⟨st₄, P0, _, _, _, _, _, hP0, heq₄, Prod.mk.eta.symm, rfl, rfl, rfl, hle₁₄, hleR, hH,
    hcl, hreg, hsc, hrd, hchk, hP0eq'⟩

/-- The honest run of `endoMul`, generic over the curve dictionary: on an in-scope,
in-range scalar and an in-scope on-curve base, the prover lands at `endoMulRun` — the
bit witness, the sealed `β·x`, the two pinned additions (`addFast_run` at the operand
conditions `init_facts` supplies), the rounds (`prove_mapAccumM` over `round_run`), the
register pin (the chain's final register is the scalar, `chain_facts`), and the chain
constraint accepted on the collected rounds (`walk_facts`). -/
theorem endoMul_run [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F] [d : HasEndo F]
    (rounds : ℕ) (hbits : 4 * rounds ≤ 244) (st : ProverState F) {g : AffinePoint (FVar F)}
    {scalar : SizedF (4 * rounds) (FVar F)} (hs : scalar.val.Scoped st) (hx : g.x.Scoped st)
    (hy : g.y.Scoped st) (hfits : scalar.Fits st.env.toValuation)
    (hT : d.W.Nonsingular (g.x.val st.env.toValuation) (g.y.val st.env.toValuation)) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (endoMul (c := KimchiConstraint F) d.endo rounds g scalar) st.nv st.env
      = .ok ((endoMulRun d.endo rounds st g scalar).1.out
          (endoMulRun d.endo rounds st g scalar).2) := by
  obtain ⟨st₄, P0, stR, w, n, xP0, yP0, -, heq₄, heqR, hn, -, -, hle₀, hleR, -, -, hreg,
    ⟨hsx, hsy, hsn⟩, ⟨hrx, hry, hrn⟩, hchk, -⟩ := walk_facts rounds hbits st hx hy hfits hT
  subst hn
  have hle₁ := bitState_le st rounds scalar.val
  have hT₁ : d.W.Nonsingular (g.x.val (bitState st rounds scalar.val).env.toValuation)
      (g.y.val (bitState st rounds scalar.val).env.toValuation) := by
    rw [CVar.val_of_le hle₁ hx, CVar.val_of_le hle₁ hy]; exact hT
  obtain ⟨st₄', P0', heq₄', hops₁, hops₂, hle₄', hs4x', hs4y', -⟩ :=
    init_facts (bitState st rounds scalar.val) (hx.of_le hle₁) (hy.of_le hle₁) hT₁
  rw [heq₄] at heq₄'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq₄'
  have hg₂ := sealRun_grants (st := bitState st rounds scalar.val)
    (CVar.Scoped.scale_ d.endo (hx.of_le hle₁))
  have hg₃ := AddFast.addFastRun_grants
    (p2' := ⟨(sealRun (bitState st rounds scalar.val) (CVar.scale_ d.endo g.x)).2, g.y⟩)
    .checkFinite _ (hx.of_le (hle₁.trans hg₂.le)) (hy.of_le (hle₁.trans hg₂.le))
    hg₂.fvar_scoped (hy.of_le (hle₁.trans hg₂.le)) hops₁
  simp only [endoMul, endoMulRun, prove_bind]
  rw [prove_witness_run (w := bitsWit rounds scalar.val) st
    (.bind (.readCVar hs) fun _ => trivial)
    (v := bitVals (F := F) rounds (ToNat.toNat (scalar.val.val st.env.toValuation)))
    (by simp [bitsWit, Except.bind])]
  rw [show CircuitType.fieldsToVar (F := F) (val := Vector (Vector F 4) rounds)
      (mapVec CVar.var (allocRange st.nv (CircuitType.size F (Vector (Vector F 4) rounds))))
      = bitVarsOf st rounds from rfl,
    show st.extendMany (CircuitType.valueToFields (F := F)
      (var := Vector (Vector (FVar F) 4) rounds)
      (bitVals (F := F) rounds (ToNat.toNat (scalar.val.val st.env.toValuation)))).toList
      = bitState st rounds scalar.val from rfl]
  simp only [Except.bind]
  rw [sealVar_run _ (CVar.Scoped.scale_ d.endo (hx.of_le hle₁))]
  simp only [Except.bind]
  rw [AddFast.addFast_run
    (p2' := ⟨(sealRun (bitState st rounds scalar.val) (CVar.scale_ d.endo g.x)).2, g.y⟩)
    .checkFinite _ (hx.of_le (hle₁.trans hg₂.le)) (hy.of_le (hle₁.trans hg₂.le))
    hg₂.fvar_scoped (hy.of_le (hle₁.trans hg₂.le)) hops₁]
  simp only [Except.bind]
  rw [AddFast.addFast_run .checkFinite _ hg₃.2.1 hg₃.2.2.1 hg₃.2.1 hg₃.2.2.1 hops₂]
  simp only [Except.bind, heq₄]
  rw [prove_mapAccumM (fun st' (acc : AffinePoint (FVar F) × FVar F) =>
      (bitState st rounds scalar.val).env.Le st'.env ∧
      acc.1.x.Scoped st' ∧ acc.1.y.Scoped st' ∧ acc.2.Scoped st')
    _ (roundRun d.endo g) _
    (fun st' acc bs hbs ⟨hle, hax, hay, han⟩ =>
      round_run d.endo (hx.of_le (hle₁.trans hle)) (hy.of_le (hle₁.trans hle))
        hax hay han (fun k hk => by
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hbs
          simp only [Vector.getElem_toList]
          exact (bitVarsOf_scoped st rounds scalar.val j (by simpa using hj) k hk).of_le hle))
    (fun st' acc bs _ ⟨hle, _, _, _⟩ => ⟨hle.trans (st'.le_extendMany _),
      st'.new_mem_extendMany (i := 4) (by simp), st'.new_mem_extendMany (i := 5) (by simp),
      st'.new_mem_extendMany (i := 1) (by simp)⟩)
    (P0.p, .const 0) st₄ ⟨hle₄', hs4x', hs4y', CVar.scoped_const _ _⟩]
  simp only [heqR]
  rw [assertEqual_run _ hsn (hs.of_le (hle₀.trans hleR)) (by
    rw [hrn, hreg, CVar.val_of_le (hle₀.trans hleR) hs]
    exact LawfulToNat.cast_toNat _)]
  simp only [Except.bind]
  rw [prove_addConstraint _ (by
    show KimchiConstraint.check (.endoMul _) _ = true
    simp only [KimchiConstraint.check, CVar.eval_eq_val hsx, CVar.eval_eq_val hsy,
      CVar.eval_eq_val hsn, hrx, hry, hrn]
    exact hchk)]
  rfl

open Kimchi.Gate.EndoMul in
/-- What `endoMulRun` grants, generic over the curve dictionary: the table grew, the
result is in scope, and it reads as `[s]·T` with
`(s : F) = EndoScalar.toField (crumbsOf (2·rounds) n) λ` — the honest side of the
defining equation, at the canonical crumbs of the scalar (`endoMul_off` at the honest
walk).

The curve facts arrive bundled as the dictionary `d : HasEndo F` — hypotheses, not
instantiations — so this law composes with OTHER generic circuit laws the way the PS
circuits compose over an abstract field: a composite gadget's law takes the same
dictionary and threads it here, and everything is discharged once, inside the larger
circuit's instantiation, at the deployed dictionaries `HasEndo.pallas`/`HasEndo.vesta`. -/
theorem endoMulRun_grants [Field F] [DecidableEq F] [ToNat F] [d : HasEndo F]
    (rounds : ℕ) (hbits : 4 * rounds ≤ 244) (st : ProverState F) {g : AffinePoint (FVar F)}
    {scalar : SizedF (4 * rounds) (FVar F)} (hx : g.x.Scoped st) (hy : g.y.Scoped st)
    (hfits : scalar.Fits st.env.toValuation)
    (hT : d.W.Nonsingular (g.x.val st.env.toValuation) (g.y.val st.env.toValuation)) :
    st.env.Le (endoMulRun d.endo rounds st g scalar).1.env ∧
      (endoMulRun d.endo rounds st g scalar).2.x.Scoped (endoMulRun d.endo rounds st g scalar).1 ∧
      (endoMulRun d.endo rounds st g scalar).2.y.Scoped (endoMulRun d.endo rounds st g scalar).1 ∧
      ∃ (hfin : d.W.Nonsingular
          ((endoMulRun d.endo rounds st g scalar).2.x.val
            (endoMulRun d.endo rounds st g scalar).1.env.toValuation)
          ((endoMulRun d.endo rounds st g scalar).2.y.val
            (endoMulRun d.endo rounds st g scalar).1.env.toValuation))
        (s A B : ℤ),
        Point.some _ _ hfin = s • Point.some _ _ hT ∧
        s = B + A * d.lam ∧
        |A| ≤ 3 * 4 ^ rounds ∧ |B| ≤ 3 * 4 ^ rounds ∧
        (A : F) = Kimchi.Gate.EndoScalar.decomposeA (Kimchi.Gate.EndoScalar.crumbsOf
          (2 * rounds) (ToNat.toNat (scalar.val.val st.env.toValuation))) ∧
        (B : F) = Kimchi.Gate.EndoScalar.decomposeB (Kimchi.Gate.EndoScalar.crumbsOf
          (2 * rounds) (ToNat.toNat (scalar.val.val st.env.toValuation))) ∧
        (s : F) = Kimchi.Gate.EndoScalar.toField (Kimchi.Gate.EndoScalar.crumbsOf
          (2 * rounds) (ToNat.toNat (scalar.val.val st.env.toValuation))) (d.lam : F) := by
  obtain ⟨st₄, P0, stR, w, n, xP0, yP0, hP0, heq₄, heqR, hn, -, -, hle₀, hleR, hH, hcl, -,
    ⟨hsx, hsy, -⟩, ⟨hrx, hry, -⟩, -, hP0eq⟩ := walk_facts rounds hbits st hx hy hfits hT
  subst hn
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  have hTne : Point.some _ _ hT ≠ 0 := Point.some_ne_zero hT
  have hφT := d.endo_nonsingular hT
  obtain ⟨hfin', s, A, B, hseq, hsab, hAle, hBle, hAval, hBval, hsval⟩ :=
    endoMul_off d.W d.two_ne d.three_ne d.odd d.endo (Point.some _ _ hT) (Point.some _ _ hφT)
      (fun a b ha' hb' hba hbb => d.off_targets ha' hb' hba hbb hTne (d.eigen hT hφT))
      rounds hbits
      (fun i => Kimchi.Gate.EndoMul.chainBuild d.endo (g.x.val st.env.toValuation)
        (g.y.val st.env.toValuation) xP0 yP0 0
        (bitRows rounds (ToNat.toNat (scalar.val.val st.env.toValuation))) i)
      hH hT rfl hφT rfl
      (fun i _ => by
        obtain ⟨hx1, hy1, -, -, -, -⟩ := chainBuild_fields d.endo (g.x.val st.env.toValuation)
          (g.y.val st.env.toValuation) xP0 yP0 0
          (bitRows rounds (ToNat.toNat (scalar.val.val st.env.toValuation))) i
        rw [hx1, hy1]
        exact ⟨rfl, rfl⟩)
      (fun i _ => ⟨rfl, rfl⟩)
      hP0 hP0eq d.lam (d.eigen hT hφT)
  rw [hcl] at hAval hBval hsval
  have hax := accX_chainBuild d.endo (g.x.val st.env.toValuation) (g.y.val st.env.toValuation)
    xP0 yP0 0 (bitRows rounds (ToNat.toNat (scalar.val.val st.env.toValuation))) rounds
  have hay := accY_chainBuild d.endo (g.x.val st.env.toValuation) (g.y.val st.env.toValuation)
    xP0 yP0 0 (bitRows rounds (ToNat.toNat (scalar.val.val st.env.toValuation))) rounds
  have hfin : d.W.Nonsingular
      (Kimchi.Gate.EndoMul.chainBuild d.endo (g.x.val st.env.toValuation)
        (g.y.val st.env.toValuation) xP0 yP0 0
        (bitRows rounds (ToNat.toNat (scalar.val.val st.env.toValuation))) rounds).xP
      (Kimchi.Gate.EndoMul.chainBuild d.endo (g.x.val st.env.toValuation)
        (g.y.val st.env.toValuation) xP0 yP0 0
        (bitRows rounds (ToNat.toNat (scalar.val.val st.env.toValuation))) rounds).yP := by
    rw [← hax, ← hay]
    exact hfin'
  dsimp only [endoMulRun]
  rw [heq₄]
  dsimp only
  rw [heqR]
  dsimp only
  refine ⟨hle₀.trans hleR, hsx, hsy, ?_⟩
  rw [hrx, hry]
  exact ⟨hfin, s, A, B, (some_congr d.W hfin hfin' hax.symm hay.symm).trans hseq,
    hsab, hAle, hBle, hAval, hBval, hsval⟩

open Kimchi.Gate.VarBaseMul (eq_inv_smul_of_smul_eq) in
/-- The division gadget is sound: under any satisfying valuation, for an input point
reading on-curve, some `[s]` with `(s : F) = EndoScalar.toField crumbs (d.lam)` and
`scalar` reading as the crumbs' reconstruction maps the RESULT to the INPUT — and,
`s` being a unit mod the prime order (free: the input is affine, hence nonzero), the
result is `[s⁻¹]·g`, the PS defining equation
`endoInv g a ~ scalarMul (recip (toFieldPure a endoScalar)) g`.
The on-curve rows discharge `endoMul_spec`'s promise hypothesis at the WITNESSED
point — the gadget's design point — with smoothness (`d.delta_ne`) upgrading their
equation to nonsingularity. The advice parameters `(q, hq, lam')` are universally
quantified: soundness never consults the witness. -/
theorem endoInv_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F] [d : HasEndo F]
    (q : ℕ) (hq : q.Prime) (lam' : ZMod q)
    (t : AffinePoint (FVar F)) (scalar : SizedF 128 (FVar F)) :
    ⦃⌜True⌝⦄
    (endoInv (c := Builder V (KimchiConstraint F)) d.endo d.W q hq lam' t scalar)
    ⦃⇓ r _ => ⌜∀ hg : d.W.Nonsingular (t.x.val V) (t.y.val V),
          ∃ crumbs : List F,
            (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
            crumbs.length = 64 ∧
            scalar.val.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs ∧
            ∃ (hres : d.W.Nonsingular (r.x.val V) (r.y.val V)) (s : ℤ),
              (s : F) = Kimchi.Gate.EndoScalar.toField crumbs (d.lam : F) ∧
              (s : ZMod d.W.order) ≠ 0 ∧
              Point.some _ _ hg = s • Point.some _ _ hres ∧
              Point.some _ _ hres
                = ((s : ZMod d.W.order)⁻¹.val : ℕ) • Point.some _ _ hg⌝⦄ := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  simp only [endoInv]
  mvcgen
  rename_i result _ _ x2 _ hx2 x3 _ hx3 _ _ hsq computed _ _ _ heqx _ _ heqy hcomp
  intro hg
  -- the on-curve rows read as the curve equation at the witnessed point
  have hEq : d.W.Equation (result.1.val V) (result.2.val V) := by
    rw [d.W.equation_iff, d.short.1, d.short.2.1, d.short.2.2.1]
    simp only [CVar.val_add_, CVar.val_scale_, CVar.val] at hsq
    rw [hx3, hx2] at hsq
    linear_combination hsq
  have hres : d.W.Nonsingular (result.1.val V) (result.2.val V) :=
    (d.W.equation_iff_nonsingular_of_Δ_ne_zero d.delta_ne).mp hEq
  -- `endoMul`'s promise at the witnessed point
  obtain ⟨crumbs, hval, hlen, hn, hfin, sZ, -, -, hseq, -, -, -, -, -, hcast⟩ :=
    hcomp hres
  -- the pins carry the computed point to the input
  have hgeq : Point.some _ _ hg = sZ • Point.some _ _ hres :=
    (Kimchi.Gate.EndoMul.some_congr d.W hg hfin heqx.symm heqy.symm).trans hseq
  -- the scalar is a unit mod the order: the input is affine, hence nonzero
  have hs0 : (sZ : ZMod d.W.order) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    refine Point.some_ne_zero hg (hgeq.trans ?_)
    have hkill : (d.W.order : ℤ) • Point.some _ _ hres = 0 := by
      rw [natCast_zsmul]
      exact card_nsmul_eq_zero'
    rw [hm, mul_comm, mul_smul, hkill, smul_zero]
  exact ⟨crumbs, hval, by omega, hn, hres, sZ, hcast, hs0, hgeq,
    eq_inv_smul_of_smul_eq d.W hs0 hgeq⟩

open Kimchi.Gate.EndoScalar in
/-- The scalar side of `endoInv`'s completeness, packaged away from the walk: at any
on-curve point, the endo-decoded challenge is a unit mod the order (its ℤ-shadow is a
positive bounded GLV combo, priced by `combo_ne_zero`), and any integer with the
decomposition shape `endoMul` hands back is congruent to it (the char window
`d.char_big` reads the bounded decomposition integers exactly). The digit-shadow
recursion (`digitsOf`) stays inside this proof — the walk's context never carries it,
which keeps the walk's elaboration off the 64-deep symbolic unfolding.

Numeral convention: everything here is spelled at the 128-bit challenge's literals —
`64` crumbs (crumbs are 2-bit, `64 = 128 / 2`) and `2 ^ 64` bound magnitudes. The
caller bridges `endoMul`'s rounds-arithmetic spellings (`2 * 32`, `4 ^ 32` at
`rounds = 32`) once, at the application. -/
private theorem endoInv_scalar_facts [Field F] [DecidableEq F] [d : HasEndo F]
    [Fact (Nat.Prime d.W.order)] {xv yv : F} (hg : d.W.Nonsingular xv yv) (n : ℕ) :
    Kimchi.Gate.EndoScalar.toField (crumbsOf 64 n) ((d.lam : ZMod d.W.order)) ≠ 0 ∧
    ∀ s A B : ℤ, s = B + A * d.lam → |A| ≤ 3 * 2 ^ 64 → |B| ≤ 3 * 2 ^ 64 →
      (A : F) = Kimchi.Gate.EndoScalar.decomposeA (crumbsOf 64 n) →
      (B : F) = Kimchi.Gate.EndoScalar.decomposeB (crumbsOf 64 n) →
      ((s : ℤ) : ZMod d.W.order)
        = Kimchi.Gate.EndoScalar.toField (crumbsOf 64 n) ((d.lam : ZMod d.W.order)) := by
  haveI : NeZero d.W.order := ⟨d.prime.ne_zero⟩
  -- the residues of 2 and 3 are units: the order is prime and avoids both
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
  obtain ⟨hAlo, hAhi⟩ := decomposeAInt_bounds (digitsOf 64 n)
  obtain ⟨hBlo, hBhi⟩ := decomposeBInt_bounds (digitsOf 64 n)
  rw [digitsOf_length] at hAlo hAhi hBlo hBhi
  have h64 : (0 : ℤ) < 2 ^ 64 := by positivity
  have heffz : Kimchi.Gate.EndoScalar.toField (crumbsOf 64 n) ((d.lam : ZMod d.W.order))
      = ((toIntZ (digitsOf 64 n) d.lam : ℤ) : ZMod d.W.order) := by
    rw [crumbsOf_eq_map, toField_digits h2q h3q _ (digitsOf_lt 64 _) d.lam]
  have hAZF : Kimchi.Gate.EndoScalar.decomposeA (crumbsOf 64 n)
      = ((decomposeAInt (digitsOf 64 n) : ℤ) : F) := by
    rw [crumbsOf_eq_map, decomposeA_digits d.two_ne d.three_ne _ (digitsOf_lt 64 _)]
  have hBZF : Kimchi.Gate.EndoScalar.decomposeB (crumbsOf 64 n)
      = ((decomposeBInt (digitsOf 64 n) : ℤ) : F) := by
    rw [crumbsOf_eq_map, decomposeB_digits d.two_ne d.three_ne _ (digitsOf_lt 64 _)]
  constructor
  · -- the decoded challenge is a unit: its shadow is a positive bounded GLV combo
    rw [heffz]
    intro h0
    obtain ⟨mm, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    have hkill : (toIntZ (digitsOf 64 n) d.lam) • (Point.some _ _ hg : d.W.Point) = 0 := by
      have horder : (d.W.order : ℤ) • (Point.some _ _ hg : d.W.Point) = 0 := by
        rw [natCast_zsmul]; exact card_nsmul_eq_zero'
      rw [hm, mul_comm, mul_smul, horder, smul_zero]
    have hexp : (toIntZ (digitsOf 64 n) d.lam) • (Point.some _ _ hg : d.W.Point)
        = decomposeBInt (digitsOf 64 n) • (Point.some _ _ hg : d.W.Point)
          + decomposeAInt (digitsOf 64 n)
            • (d.lam • (Point.some _ _ hg : d.W.Point)) := by
      rw [toIntZ]; module
    exact Kimchi.Gate.EndoMul.combo_ne_zero
      (fun a b ha hb hba hbb =>
        d.off_targets ha hb hba hbb (Point.some_ne_zero hg) rfl)
      (by linarith) (by linarith) (by norm_num at hBhi ⊢; linarith)
      (by norm_num at hAhi ⊢; linarith)
      (hexp ▸ hkill)
  · exact fun s A B hsab hAle hBle hAval hBval =>
      HasEndo.decomposition_residue n hsab hAle hBle hAval hBval

open Kimchi.Gate.EndoScalar in
open Kimchi.Gate.VarBaseMul (smul_ne_zero_of_lt smul_eq_smul_of_zmod_eq) in
/-- The advice at an on-curve point: `endoInvVal` is a genuine point `[eff⁻¹]·g` for
`eff` the endo-decoded challenge — a unit mod the order — and any scalar of the
decomposition shape `endoMul` hands back, applied to it, returns to `g`
(`s ≡ eff (mod q)` by reading the decomposition integers through the char window). -/
private theorem advice_facts [Field F] [DecidableEq F] [ToNat F] [d : HasEndo F]
    [Fact (Nat.Prime d.W.order)] {xv yv : F} (hg : d.W.Nonsingular xv yv) (sv : F) :
    ∃ (px py : F) (hpns : d.W.Nonsingular px py),
      endoInvVal d.W d.W.order d.prime (d.lam : ZMod d.W.order) xv yv sv = (px, py) ∧
      Point.some _ _ hpns
        = ((Kimchi.Gate.EndoScalar.toField (crumbsOf 64 (ToNat.toNat sv))
            (d.lam : ZMod d.W.order))⁻¹.val : ℕ) • Point.some _ _ hg ∧
      ∀ (s A B : ℤ) {x y : F} (hfin : d.W.Nonsingular x y),
        Point.some _ _ hfin = s • Point.some _ _ hpns → s = B + A * d.lam →
        |A| ≤ 3 * 4 ^ 32 → |B| ≤ 3 * 4 ^ 32 →
        (A : F) = decomposeA (crumbsOf (2 * 32) (ToNat.toNat sv)) →
        (B : F) = decomposeB (crumbsOf (2 * 32) (ToNat.toNat sv)) →
        x = xv ∧ y = yv := by
  haveI : NeZero d.W.order := ⟨d.prime.ne_zero⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  obtain ⟨heffne', hkey⟩ := endoInv_scalar_facts hg (ToNat.toNat sv)
  obtain ⟨eff, heff⟩ : ∃ eff : ZMod d.W.order,
      eff = Kimchi.Gate.EndoScalar.toField (crumbsOf 64 (ToNat.toNat sv))
        ((d.lam : ZMod d.W.order)) := ⟨_, rfl⟩
  have heffne : eff ≠ 0 := heff ▸ heffne'
  obtain ⟨G, hG⟩ : ∃ G : d.W.Point, G = Point.some _ _ hg := ⟨_, rfl⟩
  have hGne : G ≠ 0 := by rw [hG]; exact Point.some_ne_zero hg
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = eff⁻¹.val := ⟨_, rfl⟩
  have hinv_ne : eff⁻¹ ≠ 0 := inv_ne_zero heffne
  have hkne : k ≠ 0 := by rw [hkdef, Ne, ZMod.val_eq_zero]; exact hinv_ne
  have hklt : k < d.W.order := by rw [hkdef]; exact ZMod.val_lt _
  have hsmul_ne : (k : ℤ) • G ≠ 0 := fun h0 =>
    smul_ne_zero_of_lt d.W hGne
      (by exact_mod_cast Nat.pos_of_ne_zero hkne) (by exact_mod_cast hklt) h0
  obtain ⟨px, py, hpns, hpteq⟩ :
      ∃ px py, ∃ hpns : d.W.Nonsingular px py, (k : ℕ) • G = Point.some _ _ hpns := by
    rw [natCast_zsmul] at hsmul_ne
    cases hp : (k : ℕ) • G with
    | zero => exact absurd hp hsmul_ne
    | some px py hpns => exact ⟨px, py, hpns, rfl⟩
  refine ⟨px, py, hpns, ?_, by rw [← heff, ← hkdef, hG.symm, hpteq], ?_⟩
  · simp only [endoInvVal]
    rw [dif_pos hg, ← heff, ← hkdef, hG.symm, hpteq]
  · intro s A B x y hfin hpt hsab hAle hBle hAval hBval
    have hsmod : ((s : ℤ) : ZMod d.W.order) = eff := by
      rw [heff]
      exact hkey s A B hsab (by norm_num at hAle ⊢; exact hAle)
        (by norm_num at hBle ⊢; exact hBle) hAval hBval
    have hsk : ((s * (k : ℤ) : ℤ) : ZMod d.W.order) = ((1 : ℤ) : ZMod d.W.order) := by
      push_cast
      rw [hsmod, hkdef, ZMod.natCast_val, ZMod.cast_id]
      exact mul_inv_cancel₀ heffne
    have hchain : Point.some _ _ hfin = Point.some _ _ hg := by
      rw [hpt, ← hpteq, ← natCast_zsmul, smul_smul, smul_eq_smul_of_zmod_eq d.W hsk,
        one_smul]
      exact hG
    injection hchain with h1 h2
    exact ⟨h1, h2⟩

/-- The state and result of `endoInv`'s honest run: the advice pair, the two on-curve
rows, the verifying `endoMul`. -/
def endoInvRun [Field F] [DecidableEq F] [ToNat F] (eb : F) (W : WeierstrassCurve.Affine F)
    (q : ℕ) (hq : q.Prime) (lam' : ZMod q) (st : ProverState F) (g : AffinePoint (FVar F))
    (scalar : SizedF 128 (FVar F)) : ProverState F × AffinePoint (FVar F) :=
  let rv := endoInvVal W q hq lam' (g.x.val st.env.toValuation) (g.y.val st.env.toValuation)
    (scalar.val.val st.env.toValuation)
  let st₁ := st.extendMany [rv.1, rv.2]
  let rp : AffinePoint (FVar F) := ⟨.var st.nv, .var (st.nv + 1)⟩
  let r₂ := squareRun st₁ rp.x
  let r₃ := mulRun r₂.1 r₂.2 rp.x
  let r₄ := endoMulRun eb 32 r₃.1 rp scalar
  (r₄.1, rp)

/-- The on-curve rows after the advice pair: the state they land at (named), which
extends the start, keeps the pair in scope reading as the advice, and holds the cube. -/
private theorem endoInv_prefix [Field F] [DecidableEq F] (st : ProverState F) (px py : F) :
    ∃ (st₃ : ProverState F) (x3 : FVar F),
      mulRun (squareRun (st.extendMany [px, py]) (.var st.nv)).1
          (squareRun (st.extendMany [px, py]) (.var st.nv)).2 (.var st.nv) = (st₃, x3) ∧
      st.env.Le st₃.env ∧ (CVar.var st.nv).Scoped st₃ ∧ (CVar.var (st.nv + 1)).Scoped st₃ ∧
      (CVar.var st.nv).val st₃.env.toValuation = px ∧
      (CVar.var (st.nv + 1)).val st₃.env.toValuation = py ∧
      x3.Scoped st₃ ∧ x3.val st₃.env.toValuation = px * px * px := by
  have hsx₁ : (CVar.var st.nv).Scoped (st.extendMany [px, py]) :=
    ProverState.mem_extendMany_head ..
  have hsy₁ : (CVar.var (st.nv + 1)).Scoped (st.extendMany [px, py]) :=
    st.new_mem_extendMany (i := 1) (by simp)
  have hvx₁ : (CVar.var st.nv).val (st.extendMany [px, py]).env.toValuation = px :=
    ProverState.get_extendMany_head ..
  have hvy₁ : (CVar.var (st.nv + 1)).val (st.extendMany [px, py]).env.toValuation = py := by
    show (st.extendMany [px, py]).env.toValuation (st.nv + 1) = py
    rw [ProverState.get_extendMany_new st (by simp)]
    rfl
  have hle₁ : st.env.Le (st.extendMany [px, py]).env := st.le_extendMany _
  have hg₂ := squareRun_grants (st := st.extendMany [px, py]) hsx₁
  have hg₃ := mulRun_grants (st := (squareRun (st.extendMany [px, py]) (.var st.nv)).1)
    hg₂.fvar_scoped (hsx₁.of_le hg₂.le)
  refine ⟨_, _, Prod.mk.eta.symm, hle₁.trans (hg₂.le.trans hg₃.le),
    hsx₁.of_le (hg₂.le.trans hg₃.le),
    hsy₁.of_le (hg₂.le.trans hg₃.le), ?_, ?_, hg₃.fvar_scoped, ?_⟩
  · rw [CVar.val_of_le (hg₂.le.trans hg₃.le) hsx₁, hvx₁]
  · rw [CVar.val_of_le (hg₂.le.trans hg₃.le) hsy₁, hvy₁]
  · rw [hg₃.fvar_val, hg₂.fvar_val, CVar.val_of_le hg₂.le hsx₁, hvx₁]

open Kimchi.Gate.EndoScalar in
/-- The honest run of `endoInv`, instantiated in its own scalar field (`q := W.order`,
`λ' := λ mod q`): on an in-scope, in-range challenge and an in-scope on-curve point,
the prover lands at `endoInvRun` — the advice pair (a genuine point, `advice_facts`),
the on-curve rows (its curve equation), the verifying `endoMul` (`endoMul_run` at the
advice point), and the two pins (`endoMul` returns to `g`, `advice_facts` again). -/
theorem endoInv_run [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F] [d : HasEndo F]
    [Fact (Nat.Prime d.W.order)] (st : ProverState F) {g : AffinePoint (FVar F)}
    {scalar : SizedF 128 (FVar F)} (hs : scalar.val.Scoped st) (hx : g.x.Scoped st)
    (hy : g.y.Scoped st) (hfits : scalar.Fits st.env.toValuation)
    (hg : d.W.Nonsingular (g.x.val st.env.toValuation) (g.y.val st.env.toValuation)) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (endoInv (c := KimchiConstraint F) d.endo d.W d.W.order d.prime
        ((d.lam : ZMod d.W.order)) g scalar) st.nv st.env
      = .ok ((endoInvRun d.endo d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) st g scalar).1.out
          (endoInvRun d.endo d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) st g scalar).2) := by
  obtain ⟨px, py, hpns, hval, -, hret⟩ := advice_facts hg (scalar.val.val st.env.toValuation)
  have hval1 : (endoInvVal d.W d.W.order d.prime ((d.lam : ZMod d.W.order))
      (g.x.val st.env.toValuation) (g.y.val st.env.toValuation)
      (scalar.val.val st.env.toValuation)).1 = px := by rw [hval]
  have hval2 : (endoInvVal d.W d.W.order d.prime ((d.lam : ZMod d.W.order))
      (g.x.val st.env.toValuation) (g.y.val st.env.toValuation)
      (scalar.val.val st.env.toValuation)).2 = py := by rw [hval]
  obtain ⟨st₃, x3, heq, hle₃, hsx₃, hsy₃, hvx₃, hvy₃, hsx3, hvx3⟩ := endoInv_prefix st px py
  simp only [endoInv, prove_bind]
  rw [show endoInvRun d.endo d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) st g scalar
      = ((endoMulRun d.endo 32 (mulRun (squareRun (st.extendMany [(endoInvVal d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) (g.x.val st.env.toValuation)
      (g.y.val st.env.toValuation) (scalar.val.val st.env.toValuation)).1, (endoInvVal d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) (g.x.val st.env.toValuation)
      (g.y.val st.env.toValuation) (scalar.val.val st.env.toValuation)).2]) (.var st.nv)).1
        (squareRun (st.extendMany [(endoInvVal d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) (g.x.val st.env.toValuation)
      (g.y.val st.env.toValuation) (scalar.val.val st.env.toValuation)).1, (endoInvVal d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) (g.x.val st.env.toValuation)
      (g.y.val st.env.toValuation) (scalar.val.val st.env.toValuation)).2]) (.var st.nv)).2 (.var st.nv)).1
      ⟨.var st.nv, .var (st.nv + 1)⟩ scalar).1, (⟨.var st.nv, .var (st.nv + 1)⟩ : AffinePoint (FVar F))) from rfl]
  rw [prove_witness_run
    (w := endoInvWit d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) g scalar.val) st
    (.bind (.readCVar hx) fun _ => .bind (.readCVar hy) fun _ => .bind (.readCVar hs) fun _ =>
      trivial)
    (v := endoInvVal d.W d.W.order d.prime ((d.lam : ZMod d.W.order))
      (g.x.val st.env.toValuation) (g.y.val st.env.toValuation)
      (scalar.val.val st.env.toValuation))
    (by simp [endoInvWit, Except.bind])]
  simp only [valueToFields_prod_toList, valueToFields_fvar_toList, List.cons_append,
    List.nil_append, fieldsToVar_prod_alloc, fieldsToVar_fvar_alloc, Except.bind]
  simp only [size_fvar]
  rw [hval1, hval2]
  have hsx₁ : (CVar.var st.nv).Scoped (st.extendMany [px, py]) :=
    ProverState.mem_extendMany_head ..
  have hg₂ := squareRun_grants (st := st.extendMany [px, py]) hsx₁
  rw [square_run _ hsx₁]
  simp only [Except.bind]
  rw [mul_run _ hg₂.fvar_scoped (hsx₁.of_le hg₂.le)]
  simp only [Except.bind]
  rw [heq]
  -- the on-curve row
  have hEq : py * py = px * px * px + d.W.a₄ * px + d.W.a₆ := by
    have h := (d.W.equation_iff px py).mp hpns.1
    rw [d.short.1, d.short.2.1, d.short.2.2.1] at h
    linear_combination h
  rw [assertSquare_run _ hsy₃
    (CVar.Scoped.add_ (CVar.Scoped.add_ hsx3 (CVar.Scoped.scale_ _ hsx₃)) (CVar.scoped_const _ _))
    (by rw [CVar.val_add_, CVar.val_add_, CVar.val_scale_, hvx3, hvx₃, hvy₃]; exact hEq)]
  simp only [Except.bind]
  -- the verifying `endoMul` at the advice point
  have hpns₃ : d.W.Nonsingular ((CVar.var st.nv).val st₃.env.toValuation)
      ((CVar.var (st.nv + 1)).val st₃.env.toValuation) := by
    rw [hvx₃, hvy₃]; exact hpns
  have hfits₃ : scalar.Fits st₃.env.toValuation := by
    show ToNat.toNat (scalar.val.val st₃.env.toValuation) < 2 ^ 128
    rw [CVar.val_of_le hle₃ hs]; exact hfits
  rw [endoMul_run (g := ⟨.var st.nv, .var (st.nv + 1)⟩) 32 (by norm_num) st₃ (hs.of_le hle₃)
    hsx₃ hsy₃ hfits₃ hpns₃]
  simp only [Except.bind]
  have hg := endoMulRun_grants (g := ⟨.var st.nv, .var (st.nv + 1)⟩) 32 (by norm_num) st₃ hsx₃
    hsy₃ hfits₃ hpns₃
  -- the run is opaque from here: at 32 rounds its unfolding is the whole ladder
  generalize endoMulRun d.endo 32 st₃ ⟨.var st.nv, .var (st.nv + 1)⟩ scalar = E at hg ⊢
  obtain ⟨hle₄, hcx, hcy, hfin, s, A, B, hpt, hsab, hAle, hBle, hAval, hBval, -⟩ := hg
  rw [CVar.val_of_le hle₃ hs] at hAval hBval
  obtain ⟨hxe, hye⟩ := hret s A B hfin
    (hpt.trans (congrArg (s • ·) (Kimchi.Gate.EndoMul.some_congr d.W hpns₃ hpns hvx₃ hvy₃)))
    hsab hAle hBle hAval hBval
  -- the two pins
  rw [assertEqual_run _ hcx (hx.of_le (hle₃.trans hle₄))
    (by rw [hxe, CVar.val_of_le (hle₃.trans hle₄) hx])]
  simp only [Except.bind]
  rw [assertEqual_run _ hcy (hy.of_le (hle₃.trans hle₄))
    (by rw [hye, CVar.val_of_le (hle₃.trans hle₄) hy])]
  rfl

/-- What `endoInvRun` grants: the table grew, the result is in scope, and it reads as
`[eff⁻¹]·g` for `eff` the endo-decoded challenge — the PS witness's defining
equation. -/
theorem endoInvRun_grants [Field F] [DecidableEq F] [ToNat F] [d : HasEndo F]
    [Fact (Nat.Prime d.W.order)] (st : ProverState F) {g : AffinePoint (FVar F)}
    {scalar : SizedF 128 (FVar F)} (hs : scalar.val.Scoped st) (hx : g.x.Scoped st)
    (hy : g.y.Scoped st) (hfits : scalar.Fits st.env.toValuation)
    (hg : d.W.Nonsingular (g.x.val st.env.toValuation) (g.y.val st.env.toValuation)) :
    st.env.Le (endoInvRun d.endo d.W d.W.order d.prime ((d.lam : ZMod d.W.order))
      st g scalar).1.env ∧
    (endoInvRun d.endo d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) st g scalar).2.x.Scoped
      (endoInvRun d.endo d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) st g scalar).1 ∧
    (endoInvRun d.endo d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) st g scalar).2.y.Scoped
      (endoInvRun d.endo d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) st g scalar).1 ∧
    ∃ hres : d.W.Nonsingular
        ((endoInvRun d.endo d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) st g scalar).2.x.val
          (endoInvRun d.endo d.W d.W.order d.prime ((d.lam : ZMod d.W.order))
            st g scalar).1.env.toValuation)
        ((endoInvRun d.endo d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) st g scalar).2.y.val
          (endoInvRun d.endo d.W d.W.order d.prime ((d.lam : ZMod d.W.order))
            st g scalar).1.env.toValuation),
      Point.some _ _ hres
        = ((Kimchi.Gate.EndoScalar.toField
            (Kimchi.Gate.EndoScalar.crumbsOf 64 (ToNat.toNat (scalar.val.val st.env.toValuation)))
            ((d.lam : ZMod d.W.order)))⁻¹.val : ℕ) • Point.some _ _ hg := by
  obtain ⟨px, py, hpns, hval, hpt, -⟩ := advice_facts hg (scalar.val.val st.env.toValuation)
  have hval1 : (endoInvVal d.W d.W.order d.prime ((d.lam : ZMod d.W.order))
      (g.x.val st.env.toValuation) (g.y.val st.env.toValuation)
      (scalar.val.val st.env.toValuation)).1 = px := by rw [hval]
  have hval2 : (endoInvVal d.W d.W.order d.prime ((d.lam : ZMod d.W.order))
      (g.x.val st.env.toValuation) (g.y.val st.env.toValuation)
      (scalar.val.val st.env.toValuation)).2 = py := by rw [hval]
  obtain ⟨st₃, x3, heq, hle₃, hsx₃, hsy₃, hvx₃, hvy₃, -, -⟩ := endoInv_prefix st px py
  rw [show endoInvRun d.endo d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) st g scalar
      = ((endoMulRun d.endo 32 (mulRun (squareRun (st.extendMany [(endoInvVal d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) (g.x.val st.env.toValuation)
      (g.y.val st.env.toValuation) (scalar.val.val st.env.toValuation)).1, (endoInvVal d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) (g.x.val st.env.toValuation)
      (g.y.val st.env.toValuation) (scalar.val.val st.env.toValuation)).2]) (.var st.nv)).1
        (squareRun (st.extendMany [(endoInvVal d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) (g.x.val st.env.toValuation)
      (g.y.val st.env.toValuation) (scalar.val.val st.env.toValuation)).1, (endoInvVal d.W d.W.order d.prime ((d.lam : ZMod d.W.order)) (g.x.val st.env.toValuation)
      (g.y.val st.env.toValuation) (scalar.val.val st.env.toValuation)).2]) (.var st.nv)).2 (.var st.nv)).1
      ⟨.var st.nv, .var (st.nv + 1)⟩ scalar).1, (⟨.var st.nv, .var (st.nv + 1)⟩ : AffinePoint (FVar F))) from rfl]
  rw [hval1, hval2, heq, show ((st₃, x3) : ProverState F × FVar F).1 = st₃ from rfl]
  have hpns₃ : d.W.Nonsingular ((CVar.var st.nv).val st₃.env.toValuation)
      ((CVar.var (st.nv + 1)).val st₃.env.toValuation) := by
    rw [hvx₃, hvy₃]; exact hpns
  have hfits₃ : scalar.Fits st₃.env.toValuation := by
    show ToNat.toNat (scalar.val.val st₃.env.toValuation) < 2 ^ 128
    rw [CVar.val_of_le hle₃ hs]; exact hfits
  have hg := endoMulRun_grants (g := ⟨.var st.nv, .var (st.nv + 1)⟩) 32 (by norm_num) st₃ hsx₃
    hsy₃ hfits₃ hpns₃
  -- the run is opaque from here: at 32 rounds its unfolding is the whole ladder
  generalize endoMulRun d.endo 32 st₃ ⟨.var st.nv, .var (st.nv + 1)⟩ scalar = E at hg ⊢
  obtain ⟨hle₄, -, -, -⟩ := hg
  dsimp only
  refine ⟨hle₃.trans hle₄, hsx₃.of_le hle₄, hsy₃.of_le hle₄, ?_⟩
  rw [CVar.val_of_le hle₄ hsx₃, CVar.val_of_le hle₄ hsy₃, hvx₃, hvy₃]
  exact ⟨hpns, hpt⟩

end EndoMul

end Snarky.Kimchi
