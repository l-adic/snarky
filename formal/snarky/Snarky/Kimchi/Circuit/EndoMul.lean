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
    (g : AffinePoint (FVar F)) (scalar : FVar F) :
    CircuitM F c (AffinePoint (FVar F)) := do
  let result ← witness (val := F × F) (endoInvWit W q hq lam' g scalar)
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
      hfin, s, (some_congr W hfin hfin' hax.symm hay.symm).trans hseq, hsval⟩

open Kimchi.Gate.VarBaseMul (y_ne_zero_of_odd_order) in
/-- The gadget is sound: under any satisfying valuation, for a base point reading
on-curve, the result reads as `[s]·T` where
`(s : F) = EndoScalar.toField crumbs λ` for a valid crumb list of length `2·rounds`
whose reconstruction is the scalar — EndoMul multiplies by exactly the scalar
EndoScalar decodes. The curve facts arrive bundled as the dictionary `d : HasEndo F`,
so the law composes with other generic circuit laws over an abstract field, and is
concretized only inside a larger circuit's instantiation, at the deployed
dictionaries `HasEndo.pallas`/`HasEndo.vesta`. -/
theorem endoMul_spec [Field F] [DecidableEq F] [ToNat F] (d : HasEndo F)
    (rounds : ℕ) (hbits : 4 * rounds ≤ 244)
    (t : AffinePoint (FVar F)) (scalar : FVar F)
    (Q : PostCond (AffinePoint (FVar F)) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : AffinePoint (FVar F)) =>
        ∀ hT : d.W.Nonsingular (t.x.val V) (t.y.val V),
          ∃ crumbs : List F,
            (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
            crumbs.length = 2 * rounds ∧
            scalar.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs ∧
            ∃ (hfin : d.W.Nonsingular (r.x.val V) (r.y.val V)) (s : ℤ),
              Point.some _ _ hfin = s • Point.some _ _ hT ∧
              (s : F) = Kimchi.Gate.EndoScalar.toField crumbs (d.lam : F)) Q⦄
    (endoMul (c := KimchiConstraint F) d.endo rounds t scalar)
    ⦃Q⦄ := by
  obtain ⟨W, eb, lam, ha, -, hprime, hodd, h2, h3, heig, hφns, hoff, -⟩ := d
  haveI : Fact (Nat.Prime W.order) := ⟨hprime⟩
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
    intro hT
    have hφT : W.Nonsingular (eb * t.x.val s.V) (t.y.val s.V) := hφns hT
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

/-! ## Completeness plumbing

The prover-side reading of a round and the successor chain's check: a round's
`evalWith` is the conjunction of its cell reads with the supplied output values, the
check survives table extension, and appending a round extends the chain's check when
the old finals are the appended round's input-cell reads — the same shared variables
the successor-chain reading closes over. -/

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

/-- A round's read survives table extension. -/
private theorem evalWith_le [Field F] [DecidableEq F] {env env' : Assignments F}
    (hle : env.Le env') {r : EndoMulRound F} {xS yS nPrime : F}
    {w : Kimchi.Gate.EndoMul.Witness F}
    (h : EndoMulRound.evalWith env r xS yS nPrime = .ok w) :
    EndoMulRound.evalWith env' r xS yS nPrime = .ok w := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ :=
    evalWith_ok_iff.mp h
  exact evalWith_ok_iff.mpr ⟨CVar.eval_le hle h1, CVar.eval_le hle h2,
    CVar.eval_le hle h3, CVar.eval_le hle h4, CVar.eval_le hle h5,
    CVar.eval_le hle h6, CVar.eval_le hle h7, CVar.eval_le hle h8,
    CVar.eval_le hle h9, CVar.eval_le hle h10, CVar.eval_le hle h11,
    CVar.eval_le hle h12, CVar.eval_le hle h13, CVar.eval_le hle h14, h15, h16, h17⟩

/-- The chain's check survives table extension. -/
private theorem chainOk_le [Field F] [DecidableEq F] {env env' : Assignments F}
    (hle : env.Le env') {eb : F} {fv : F × F × F} :
    ∀ {rounds : List (EndoMulRound F)},
      EndoMul.chainOk env eb fv rounds = true →
      EndoMul.chainOk env' eb fv rounds = true
  | [], _ => rfl
  | [r], h => by
    simp only [EndoMul.chainOk] at h ⊢
    cases he : EndoMulRound.evalWith env r fv.1 fv.2.1 fv.2.2 with
    | error e => rw [he] at h; simp at h
    | ok w =>
      rw [he] at h
      rw [evalWith_le hle he]
      exact h
  | r :: r' :: rest, h => by
    simp only [EndoMul.chainOk, Bool.and_eq_true] at h ⊢
    obtain ⟨hhead, htail⟩ := h
    refine ⟨?_, chainOk_le hle htail⟩
    cases hex : r'.p.x.eval env with
    | error e => simp [hex] at hhead
    | ok xS =>
      cases hey : r'.p.y.eval env with
      | error e => simp [hex, hey] at hhead
      | ok yS =>
        cases hen : r'.nAcc.eval env with
        | error e => simp [hex, hey, hen] at hhead
        | ok nP =>
          simp only [hex, hey, hen] at hhead
          simp only [CVar.eval_le hle hex, CVar.eval_le hle hey, CVar.eval_le hle hen]
          cases hev : EndoMulRound.evalWith env r xS yS nP with
          | error e => simp [hev] at hhead
          | ok w =>
            simp only [hev] at hhead
            simp only [evalWith_le hle hev]
            exact hhead

/-- Appending a round extends the chain's check: the old finals are the appended
round's input-cell reads (the shared variables), and the new finals are its output
values. -/
private theorem chainOk_snoc [Field F] [DecidableEq F] {env : Assignments F} {eb : F} :
    ∀ {rounds : List (EndoMulRound F)} {v1 v2 v3 : F},
      EndoMul.chainOk env eb (v1, v2, v3) rounds = true →
      ∀ {r : EndoMulRound F},
        r.p.x.eval env = .ok v1 → r.p.y.eval env = .ok v2 →
        r.nAcc.eval env = .ok v3 →
      ∀ {fv : F × F × F} {w : Kimchi.Gate.EndoMul.Witness F},
        EndoMulRound.evalWith env r fv.1 fv.2.1 fv.2.2 = .ok w →
        Kimchi.Gate.EndoMul.ok eb w = true →
        EndoMul.chainOk env eb fv (rounds ++ [r]) = true
  | [], v1, v2, v3, _, r, hpx, hpy, hn, fv, w, hev, hok => by
    simp only [List.nil_append, EndoMul.chainOk, hev]
    exact hok
  | [r0], v1, v2, v3, h, r, hpx, hpy, hn, fv, w, hev, hok => by
    simp only [EndoMul.chainOk] at h
    simp only [List.cons_append, List.nil_append, EndoMul.chainOk, Bool.and_eq_true,
      hpx, hpy, hn, hev]
    exact ⟨h, hok⟩
  | r0 :: r1 :: rest, v1, v2, v3, h, r, hpx, hpy, hn, fv, w, hev, hok => by
    simp only [EndoMul.chainOk, Bool.and_eq_true] at h
    obtain ⟨hhead, htail⟩ := h
    simp only [List.cons_append, EndoMul.chainOk, Bool.and_eq_true]
    exact ⟨hhead, chainOk_snoc htail hpx hpy hn hev hok⟩

/-- One row's witness computation reads the threaded cells and computes the gate's
canonical row's outputs. -/
private theorem rowWit_ok [Field F] [DecidableEq F] {env : Assignments F}
    {eb : F} {t : AffinePoint (FVar F)} {bs : Vector (FVar F) 4}
    {st : AffinePoint (FVar F) × FVar F} {xt yt xp yp n b1 b2 b3 b4 : F}
    (hxt : t.x.eval env = .ok xt) (hyt : t.y.eval env = .ok yt)
    (hxp : st.1.x.eval env = .ok xp) (hyp : st.1.y.eval env = .ok yp)
    (hn : st.2.eval env = .ok n)
    (hb1 : bs[0].eval env = .ok b1) (hb2 : bs[1].eval env = .ok b2)
    (hb3 : bs[2].eval env = .ok b3) (hb4 : bs[3].eval env = .ok b4) :
    rowWit eb t bs st env
      = .ok ((Kimchi.Gate.EndoMul.build eb xt yt xp yp n b1 b2 b3 b4).inv,
             (Kimchi.Gate.EndoMul.build eb xt yt xp yp n b1 b2 b3 b4).nPrime,
             (Kimchi.Gate.EndoMul.build eb xt yt xp yp n b1 b2 b3 b4).xR,
             (Kimchi.Gate.EndoMul.build eb xt yt xp yp n b1 b2 b3 b4).yR,
             (Kimchi.Gate.EndoMul.build eb xt yt xp yp n b1 b2 b3 b4).xS,
             (Kimchi.Gate.EndoMul.build eb xt yt xp yp n b1 b2 b3 b4).yS,
             (Kimchi.Gate.EndoMul.build eb xt yt xp yp n b1 b2 b3 b4).s1,
             (Kimchi.Gate.EndoMul.build eb xt yt xp yp n b1 b2 b3 b4).s3) := by
  simp [rowWit, AsProver.readCVar, hxt, hyt, hxp, hyp, hn, hb1, hb2, hb3, hb4,
    Bind.bind, ReaderT.bind, Except.bind, Pure.pure, ReaderT.pure, Except.pure]

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

open Kimchi.Gate.EndoMul in
open Kimchi.Gate.VarBaseMul (y_ne_zero_of_odd_order smul_ne_zero_of_lt) in
/-- The gadget is complete, generic over the curve dictionary: the honest prover run
accepts on a readable in-range faithful scalar and a readable on-curve base, and the
returned point reads as `[s]·T` with
`(s : F) = EndoScalar.toField (crumbsOf (2·rounds) n) λ` — the honest side of the
defining equation, at the canonical crumbs of the scalar.

The curve facts arrive bundled as the dictionary `d : HasEndo F` — hypotheses, not
instantiations — so this law composes with OTHER generic circuit completeness laws
the way the PS circuits compose over an abstract field: a composite gadget's law
takes the same dictionary and threads it here (as this walk itself threads `d.W` and
its facts into `addFast_complete_spec`), and everything is discharged once, inside
the larger circuit's instantiation, at the deployed dictionaries
`HasEndo.pallas`/`HasEndo.vesta`.

The loop invariant identifies the run with the honest walk `chainBuild`; the
per-round check is the produce chain's (`chain_complete` through `off`), the init
chain is the two pinned additions (`addFast_complete_spec`), and the register pin is
`chain_nAcc` through the bit-to-crumb bridge (`crumbList_ofBits`). -/
theorem endoMul_complete_spec [Field F] [DecidableEq F] [ToNat F] (d : HasEndo F)
    (rounds : ℕ) (hbits : 4 * rounds ≤ 244)
    (t : AffinePoint (FVar F)) (scalar : FVar F)
    (Q : PostCond (AffinePoint (FVar F)) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env =>
          (scalar.eval env).isOk ∧ (t.x.eval env).isOk ∧ (t.y.eval env).isOk ∧
          (∀ v, scalar.eval env = .ok v →
            ToNat.toNat v < 4 ^ (2 * rounds) ∧ ((ToNat.toNat v : F) = v)) ∧
          (∀ x y, t.x.eval env = .ok x → t.y.eval env = .ok y → d.W.Nonsingular x y))
        (fun env r env' => ∀ v xv yv, scalar.eval env = .ok v →
          t.x.eval env = .ok xv → t.y.eval env = .ok yv →
          ∀ hT : d.W.Nonsingular xv yv,
          ∃ xS yS, r.x.eval env' = .ok xS ∧ r.y.eval env' = .ok yS ∧
            ∃ (hfin : d.W.Nonsingular xS yS) (s : ℤ),
              Point.some _ _ hfin = s • Point.some _ _ hT ∧
              (s : F) = Kimchi.Gate.EndoScalar.toField
                (Kimchi.Gate.EndoScalar.crumbsOf (2 * rounds) (ToNat.toNat v))
                (d.lam : F))
        Q⦄
    (endoMul (c := KimchiProverC F) d.endo rounds t scalar)
    ⦃Q⦄ := by
  obtain ⟨W, eb, lam, ha, -, hprime, hodd, h2, h3, heig, hφns, hoff, hlam1⟩ := d
  haveI : Fact (Nat.Prime W.order) := ⟨hprime⟩
  haveI : Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0) := ⟨⟨ha.1, ha.2.1, ha.2.2.1⟩⟩
  simp only [endoMul, mapAccumM]
  mvcgen
  rename_i st₀ hpre
  obtain ⟨⟨hsok, hxok, hyok, hsc, hcurve⟩, hk⟩ := hpre
  obtain ⟨v, hv⟩ := CVar.evalOk hsok
  obtain ⟨xv, hxv⟩ := CVar.evalOk hxok
  obtain ⟨yv, hyv⟩ := CVar.evalOk hyok
  obtain ⟨hrange, hfaith⟩ := hsc v hv
  have hT : W.Nonsingular xv yv := hcurve _ _ hxv hyv
  have hφT : W.Nonsingular (eb * xv) yv := hφns hT
  have hyne : yv ≠ 0 := y_ne_zero_of_odd_order W hodd hT
  -- the bulk bit witness
  have hwit : bitsWit rounds scalar st₀.env
      = .ok (Vector.ofFn fun r => Vector.ofFn fun j =>
          if (ToNat.toNat v).testBit (4 * rounds - 1 - (4 * r.1 + j.1))
          then 1 else 0) := by
    simp [bitsWit, AsProver.readCVar, hv, Bind.bind, ReaderT.bind, Except.bind,
      Pure.pure, ReaderT.pure, Except.pure]
  refine ⟨by rw [hwit]; rfl, fun bits st₁ hgrant hle₁ => ?_⟩
  have hread := hgrant _ hwit
  mvcgen
  -- the sealed `β·x`
  have hsx : (CVar.scale_ eb t.x).eval st₁.env = .ok (eb * xv) :=
    CVar.eval_scale_ (CVar.eval_le hle₁ hxv) eb
  refine ⟨by rw [hsx]; rfl, fun phix st₂ hphr hle₂ => ?_⟩
  have hphix := hphr _ hsx
  mvcgen
  -- the two pinned additions: `P₁ = T + φT`, `P₀ = P₁ + P₁`
  have hTne : Point.some _ _ hT ≠ 0 := Point.some_ne_zero hT
  have hx02 : t.x.eval st₂.env = .ok xv := CVar.eval_le (hle₁.trans hle₂) hxv
  have hy02 : t.y.eval st₂.env = .ok yv := CVar.eval_le (hle₁.trans hle₂) hyv
  refine AddFast.addFast_complete_spec .checkFinite W ha h2 t ⟨phix, t.y⟩ _ _
    ⟨⟨by rw [hx02]; rfl, by rw [hy02]; rfl, by rw [hphix]; rfl, by rw [hy02]; rfl,
      fun x1 y1 x2 y2 he1 he2 he3 he4 => ?_⟩,
     fun p1 st₃ hp1 hle₃ => ?_⟩
  · rw [hx02] at he1; rw [hy02] at he2; rw [hphix] at he3; rw [hy02] at he4
    injection he1 with he1; injection he2 with he2
    injection he3 with he3; injection he4 with he4
    subst he1 he2 he3 he4
    refine ⟨hT.1, hφT.1, hyne, fun _ => ?_⟩
    rintro ⟨-, hyeq⟩
    rw [show W.negY (eb * xv) yv = -yv from by
      simp [WeierstrassCurve.Affine.negY, ha.1, ha.2.2.1]] at hyeq
    refine hyne ?_
    have h2y : (2 : F) * yv = 0 := by linear_combination hyeq
    exact (mul_eq_zero.mp h2y).resolve_left h2
  obtain ⟨x1v, y1v, hx1e, hy1e, -, hP1, hsum1⟩ :=
    (hp1 xv yv (eb * xv) yv hx02 hy02 hphix hy02 hT hφT).resolve_left (by
      rintro ⟨-, hzero⟩
      rw [heig hT hφT] at hzero
      exact hlam1 (Point.some _ _ hT) hTne (by rw [← hzero]; module))
  have hy1ne : y1v ≠ 0 := y_ne_zero_of_odd_order W hodd hP1
  mvcgen
  refine AddFast.addFast_complete_spec .checkFinite W ha h2 p1.p p1.p _ _
    ⟨⟨by rw [hx1e]; rfl, by rw [hy1e]; rfl, by rw [hx1e]; rfl, by rw [hy1e]; rfl,
      fun x1 y1 x2 y2 he1 he2 he3 he4 => ?_⟩,
     fun p2 st₄ hp2 hle₄ => ?_⟩
  · rw [hx1e] at he1; rw [hy1e] at he2; rw [hx1e] at he3; rw [hy1e] at he4
    injection he1 with he1; injection he2 with he2
    injection he3 with he3; injection he4 with he4
    subst he1 he2 he3 he4
    refine ⟨hP1.1, hP1.1, hy1ne, fun _ => ?_⟩
    rintro ⟨-, hyeq⟩
    rw [show W.negY x1v y1v = -y1v from by
      simp [WeierstrassCurve.Affine.negY, ha.1, ha.2.2.1]] at hyeq
    refine hy1ne ?_
    have h2y : (2 : F) * y1v = 0 := by linear_combination hyeq
    exact (mul_eq_zero.mp h2y).resolve_left h2
  obtain ⟨x0v, y0v, hx0e, hy0e, -, hP0ns, hsum2⟩ :=
    (hp2 x1v y1v x1v y1v hx1e hy1e hx1e hy1e hP1 hP1).resolve_left (by
      rintro ⟨-, hzero⟩
      have h2P : (2 : ℤ) • Point.some _ _ hP1 = 0 := by
        rw [two_zsmul, hzero]
      have hlt : (2 : ℤ) < (W.order : ℤ) := by
        have hp2' := (Fact.out : Nat.Prime W.order).two_le
        have h3' : 3 ≤ W.order := by omega
        exact_mod_cast h3'
      exact smul_ne_zero_of_lt W (Point.some_ne_zero hP1) (by norm_num) hlt h2P)
  have hP0 : Point.some _ _ hP0ns
      = (2 : ℤ) • Point.some _ _ hT + (2 : ℤ) • Point.some _ _ hφT := by
    rw [← hsum2, ← hsum1]
    module
  -- the honest walk and its per-row acceptance
  set n := ToNat.toNat v with hndef
  set bsv : ℕ → F × F × F × F := fun r =>
    ((if n.testBit (4 * rounds - 1 - (4 * r + 0)) then (1 : F) else 0),
     (if n.testBit (4 * rounds - 1 - (4 * r + 1)) then (1 : F) else 0),
     (if n.testBit (4 * rounds - 1 - (4 * r + 2)) then (1 : F) else 0),
     (if n.testBit (4 * rounds - 1 - (4 * r + 3)) then (1 : F) else 0)) with hbsv
  have hbit01 : ∀ c : Bool,
      (if c then (1 : F) else 0) = 0 ∨ (if c then (1 : F) else 0) = 1 := by
    intro c
    cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hbsb : ∀ i, ((bsv i).1 = 0 ∨ (bsv i).1 = 1)
      ∧ ((bsv i).2.1 = 0 ∨ (bsv i).2.1 = 1)
      ∧ ((bsv i).2.2.1 = 0 ∨ (bsv i).2.2.1 = 1)
      ∧ ((bsv i).2.2.2 = 0 ∨ (bsv i).2.2.2 = 1) :=
    fun i => ⟨hbit01 _, hbit01 _, hbit01 _, hbit01 _⟩
  have hHolds : ∀ i, i < rounds →
      Kimchi.Gate.EndoMul.Holds eb
        (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv i) :=
    Kimchi.Gate.EndoMul.chain_complete W (Point.some _ _ hT) (Point.some _ _ hφT)
      (fun a b ha' hb' hba hbb => hoff ha' hb' hba hbb hTne (heig hT hφT))
      rounds hbits hT hφT rfl rfl bsv hbsb 0 hP0ns hP0
  mvcgen
  case inv1 =>
    exact ⇓ p s' => ⌜st₄.env.Le s'.env ∧
      (p.2.fst.1.x.eval s'.env
          = .ok (Kimchi.Gate.EndoMul.chainBuild
              eb xv yv x0v y0v 0 bsv p.1.prefix.length).xP ∧
        p.2.fst.1.y.eval s'.env
          = .ok (Kimchi.Gate.EndoMul.chainBuild
              eb xv yv x0v y0v 0 bsv p.1.prefix.length).yP ∧
        p.2.fst.2.eval s'.env
          = .ok (Kimchi.Gate.EndoMul.chainBuild
              eb xv yv x0v y0v 0 bsv p.1.prefix.length).n) ∧
      EndoMul.chainOk s'.env eb
        ((Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv p.1.prefix.length).xP,
         (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv p.1.prefix.length).yP,
         (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv p.1.prefix.length).n)
        p.2.snd = true⌝
  case vc1.step =>
    rename_i pref cur suff hsplit b s' hinv
    obtain ⟨hLe, ⟨hxP, hyP, hnP⟩, hchk⟩ := hinv
    have hkrows : pref.length < rounds := by
      have hlen := congrArg List.length hsplit
      simp only [Vector.length_toList, List.length_append, List.length_cons] at hlen
      omega
    have hcur : cur = bits[pref.length]'hkrows := by
      have h1 : bits.toList[pref.length]'(by
          simp only [Vector.length_toList]; omega) = cur := by
        simp only [hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      rw [← h1, Vector.getElem_toList]
    subst hcur
    have hbit : ∀ j (hj : j < 4),
        ((bits[pref.length]'hkrows)[j]'hj).eval s'.env
          = .ok (if n.testBit (4 * rounds - 1 - (4 * pref.length + j))
              then (1 : F) else 0) := by
      intro j hj
      have hr' : (bits[pref.length]'hkrows)[j].eval st₁.env
          = .ok ((Vector.ofFn fun r => Vector.ofFn fun j =>
              if n.testBit (4 * rounds - 1 - (4 * r.1 + j.1))
              then (1 : F) else 0)[pref.length]'hkrows)[j] :=
        hread pref.length hkrows j hj
      have hr2 := CVar.eval_le (hle₂.trans (hle₃.trans (hle₄.trans hLe))) hr'
      simpa [Vector.getElem_ofFn] using hr2
    have hrow := rowWit_ok (eb := eb)
      (CVar.eval_le ((hle₁.trans (hle₂.trans (hle₃.trans hle₄))).trans hLe) hxv)
      (CVar.eval_le ((hle₁.trans (hle₂.trans (hle₃.trans hle₄))).trans hLe) hyv)
      hxP hyP hnP (hbit 0 (by omega)) (hbit 1 (by omega))
      (hbit 2 (by omega)) (hbit 3 (by omega))
    rw [show Kimchi.Gate.EndoMul.build eb xv yv
        (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv pref.length).xP
        (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv pref.length).yP
        (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv pref.length).n
        (if n.testBit (4 * rounds - 1 - (4 * pref.length + 0)) then (1 : F) else 0)
        (if n.testBit (4 * rounds - 1 - (4 * pref.length + 1)) then (1 : F) else 0)
        (if n.testBit (4 * rounds - 1 - (4 * pref.length + 2)) then (1 : F) else 0)
        (if n.testBit (4 * rounds - 1 - (4 * pref.length + 3)) then (1 : F) else 0)
      = Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv pref.length from
        (Kimchi.Gate.EndoMul.chainBuild_eta eb xv yv x0v y0v 0 bsv
          pref.length).symm] at hrow
    refine ⟨by rw [hrow]; rfl, fun w st' hgrant' hle' => ?_⟩
    have hw := hgrant' _ hrow
    mvcgen
    have hround : EndoMulRound.evalWith st'.env
        { t := t, p := b.fst.1, r := ⟨w.2.2.1, w.2.2.2.1⟩,
          s := ⟨w.2.2.2.2.1, w.2.2.2.2.2.1⟩,
          s1 := w.2.2.2.2.2.2.1, s3 := w.2.2.2.2.2.2.2,
          nAcc := b.fst.2, nAccNext := w.2.1,
          bit0 := (bits[pref.length]'hkrows)[0],
          bit1 := (bits[pref.length]'hkrows)[1],
          bit2 := (bits[pref.length]'hkrows)[2],
          bit3 := (bits[pref.length]'hkrows)[3],
          inv := w.1 }
        (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv pref.length).xS
        (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv pref.length).yS
        (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv pref.length).nPrime
        = .ok (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv pref.length) := by
      obtain ⟨hxT', hyT', hb1', hb2', hb3', hb4'⟩ :=
        chainBuild_fields eb xv yv x0v y0v 0 bsv pref.length
      refine evalWith_ok_iff.mpr
        ⟨?_, ?_, CVar.eval_le hle' hxP, CVar.eval_le hle' hyP,
          CVar.eval_le hle' hnP, ?_, ?_, ?_, ?_, hw.2.2.2.2.2.2.1,
          hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.2.2.2, hw.1, rfl, rfl, rfl⟩
      · rw [hxT']
        exact CVar.eval_le
          (((hle₁.trans (hle₂.trans (hle₃.trans hle₄))).trans hLe).trans hle') hxv
      · rw [hyT']
        exact CVar.eval_le
          (((hle₁.trans (hle₂.trans (hle₃.trans hle₄))).trans hLe).trans hle') hyv
      · rw [hb1']
        exact CVar.eval_le hle' (hbit 0 (by omega))
      · rw [hb2']
        exact CVar.eval_le hle' (hbit 1 (by omega))
      · rw [hb3']
        exact CVar.eval_le hle' (hbit 2 (by omega))
      · rw [hb4']
        exact CVar.eval_le hle' (hbit 3 (by omega))
    refine ⟨hLe.trans hle', ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      exact ⟨hw.2.2.2.2.1, hw.2.2.2.2.2.1, hw.2.1⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      exact chainOk_snoc (chainOk_le hle' hchk)
        (CVar.eval_le hle' hxP) (CVar.eval_le hle' hyP) (CVar.eval_le hle' hnP)
        hround ((Kimchi.Gate.EndoMul.ok_iff eb _).mpr (hHolds pref.length hkrows))
  case vc2.vc1.vc1.vc1.vc1.refine_2.refine_2.pre =>
    exact ⟨Assignments.Le.refl st₄.env, ⟨hx0e, hy0e, rfl⟩, rfl⟩
  case vc3.vc1.vc1.vc1.vc1.refine_2.refine_2.post.success =>
    rename_i finp s' hinv
    obtain ⟨hLe, ⟨hxP, hyP, hnP⟩, hchk⟩ := hinv
    simp only [Vector.length_toList] at hxP hyP hnP hchk
    -- the register pin: the final register reads as the scalar
    have hcl : Kimchi.Gate.EndoMul.crumbList
        (fun i => Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv i) rounds
        = Kimchi.Gate.EndoScalar.crumbsOf (2 * rounds) n := by
      refine Kimchi.Gate.EndoMul.crumbList_ofBits rounds n _ (fun r hr => ?_)
      obtain ⟨-, -, hb1', hb2', hb3', hb4'⟩ :=
        chainBuild_fields eb xv yv x0v y0v 0 bsv r
      exact ⟨by rw [hb1']; rfl, by rw [hb2'], by rw [hb3'], by rw [hb4']⟩
    have hreg : (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv rounds).n
        = v := by
      have hchain := Kimchi.Gate.EndoMul.chain_nAcc eb rounds
        (fun i => Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv i)
        hHolds (fun i _ => rfl)
      rw [accN_chainBuild, accN_chainBuild, hcl,
        Kimchi.Gate.EndoScalar.nReconstruct_crumbsOf, Nat.mod_eq_of_lt hrange]
        at hchain
      rw [hchain]
      show (0 : F) * 4 ^ (2 * rounds) + (n : F) = v
      rw [zero_mul, zero_add, hndef]
      exact hfaith
    -- the pin, the payload check, and the final grant
    have hsv' : scalar.eval s'.env = .ok v :=
      CVar.eval_le ((hle₁.trans (hle₂.trans (hle₃.trans hle₄))).trans hLe) hv
    refine ⟨⟨by rw [hnP]; rfl, by rw [hsv']; rfl, fun rv sv hrv hsv => ?_⟩,
      fun u st₅ hle₅ => ?_⟩
    · rw [hnP] at hrv
      injection hrv with hrv
      rw [hsv'] at hsv
      injection hsv with hsv
      subst hrv hsv
      exact hreg
    mvcgen
    refine addConstraint_complete_spec (c := KimchiConstraint F)
      (KimchiSystem.endoMul
        { state := finp.snd, s := finp.fst.1, nAcc := finp.fst.2, endo := eb })
      _ st₅ ⟨?_, fun u' st₆ _ hle₆ => ?_⟩
    · show KimchiConstraint.check (.endoMul
          { state := finp.snd, s := finp.fst.1, nAcc := finp.fst.2, endo := eb })
          st₅.env = true
      simp only [KimchiConstraint.check, CVar.eval_le hle₅ hxP,
        CVar.eval_le hle₅ hyP, CVar.eval_le hle₅ hnP]
      exact chainOk_le hle₅ hchk
    · simp only [wp, PredTrans.apply, prove]
      intro hf
      refine hk finp.fst.1 ⟨st₆.nv, st₆.env, hf⟩ (fun v' xv' yv' hv' hxv' hyv' hT' => ?_)
        ((hle₁.trans (hle₂.trans (hle₃.trans hle₄))).trans
          (hLe.trans (hle₅.trans hle₆)))
      rw [hv] at hv'
      injection hv' with hv'
      rw [hxv] at hxv'
      injection hxv' with hxv'
      rw [hyv] at hyv'
      injection hyv' with hyv'
      subst hv' hxv' hyv'
      -- the point chain: `endoMul_off` at the honest walk
      obtain ⟨hfin', s, A, B, hseq, hsab, hAle, hBle, hAval, hBval, hsval⟩ :=
        Kimchi.Gate.EndoMul.endoMul_off W h2 h3 hodd eb
          (Point.some _ _ hT) (Point.some _ _ hφT)
          (fun a b ha' hb' hba hbb => hoff ha' hb' hba hbb hTne (heig hT hφT))
          rounds hbits
          (fun i => Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv i)
          hHolds hT rfl hφT rfl
          (fun i _ => by
            show (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv i).xT
                = (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv 0).xT
              ∧ (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv i).yT
                = (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv 0).yT
            obtain ⟨hx1, hy1, -, -, -, -⟩ := chainBuild_fields eb xv yv x0v y0v 0 bsv i
            rw [hx1, hy1]
            exact ⟨rfl, rfl⟩)
          (fun i _ => ⟨rfl, rfl⟩)
          hP0ns hP0 lam (heig hT hφT)
      rw [hcl] at hsval
      have hax := accX_chainBuild eb xv yv x0v y0v 0 bsv rounds
      have hay := accY_chainBuild eb xv yv x0v y0v 0 bsv rounds
      have hfin : W.Nonsingular
          (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv rounds).xP
          (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv rounds).yP := by
        rw [← hax, ← hay]
        exact hfin'
      exact ⟨(Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv rounds).xP,
        (Kimchi.Gate.EndoMul.chainBuild eb xv yv x0v y0v 0 bsv rounds).yP,
        CVar.eval_le (hle₅.trans hle₆) hxP, CVar.eval_le (hle₅.trans hle₆) hyP,
        hfin, s,
        (Kimchi.Gate.EndoMul.some_congr W hfin hfin' hax.symm hay.symm).trans hseq,
        hsval⟩
  case vc4.vc1.vc1.vc1.vc1.refine_2.refine_2.post.except =>
    exact ExceptConds.entails_false

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
theorem endoInv_spec [Field F] [DecidableEq F] [ToNat F] (d : HasEndo F)
    (q : ℕ) (hq : q.Prime) (lam' : ZMod q)
    (t : AffinePoint (FVar F)) (scalar : FVar F)
    (Q : PostCond (AffinePoint (FVar F)) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : AffinePoint (FVar F)) =>
        ∀ hg : d.W.Nonsingular (t.x.val V) (t.y.val V),
          ∃ crumbs : List F,
            (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
            crumbs.length = 64 ∧
            scalar.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs ∧
            ∃ (hres : d.W.Nonsingular (r.x.val V) (r.y.val V)) (s : ℤ),
              (s : F) = Kimchi.Gate.EndoScalar.toField crumbs (d.lam : F) ∧
              (s : ZMod d.W.order) ≠ 0 ∧
              Point.some _ _ hg = s • Point.some _ _ hres ∧
              Point.some _ _ hres
                = ((s : ZMod d.W.order)⁻¹.val : ℕ) • Point.some _ _ hg) Q⦄
    (endoInv (c := KimchiConstraint F) d.endo d.W q hq lam' t scalar)
    ⦃Q⦄ := by
  haveI : Fact (Nat.Prime d.W.order) := ⟨d.prime⟩
  haveI : Fact (d.W.a₁ = 0 ∧ d.W.a₂ = 0 ∧ d.W.a₃ = 0) :=
    ⟨⟨d.short.1, d.short.2.1, d.short.2.2.1⟩⟩
  simp only [endoInv]
  mvcgen
  rename_i s hpre
  intro result _
  mvcgen
  intro x2 _ hx2
  mvcgen
  intro x3 _ hx3
  mvcgen
  intro _ _ hsq
  mvcgen
  refine endoMul_spec d 32 (by norm_num) ⟨result.1, result.2⟩ scalar _ _ ?_
  intro computed nvc hcomp
  mvcgen
  intro _ _ heqx
  mvcgen
  intro _ _ heqy
  mvcgen
  refine hpre ⟨result.1, result.2⟩ _ ?_
  intro hg
  -- the on-curve rows read as the curve equation at the witnessed point
  have hEq : d.W.Equation (result.1.val s.V) (result.2.val s.V) := by
    rw [d.W.equation_iff, d.short.1, d.short.2.1, d.short.2.2.1]
    simp only [CVar.val_add_, CVar.val_scale_, CVar.val] at hsq
    rw [hx3, hx2] at hsq
    linear_combination hsq
  have hres : d.W.Nonsingular (result.1.val s.V) (result.2.val s.V) :=
    (d.W.equation_iff_nonsingular_of_Δ_ne_zero d.delta_ne).mp hEq
  -- `endoMul`'s promise at the witnessed point
  obtain ⟨crumbs, hval, hlen, hn, hfin, sZ, hseq, hcast⟩ := hcomp hres
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

end EndoMul

end Snarky.Kimchi
