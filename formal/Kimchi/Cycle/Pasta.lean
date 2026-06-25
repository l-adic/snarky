import Kimchi.Cycle.EndoMul
import Kimchi.Gate.AddComplete
import CompElliptic.Curves.Pasta

/-!
# Phase 4: instantiating the cycle for Pasta — the axioms become real

Phases 0–3 prove the faithful gate results for *any* `CMCurve`, staying
standard-axiom-clean because the Pasta facts are structure-field *hypotheses*. This
file takes the last step: it instantiates the **concrete** Pallas curve, at which point
the only facts that remain `axiom`s are the ones Mathlib genuinely cannot prove — the
group order (Schoof) and the CM eigenvalue (`φ = [λ]`).

What used to be postulated here is now **concrete**:

* The coordinate field `F` is `CompElliptic.Fields.Pasta.PallasBaseField` — literally
  `ZMod p` for the 255-bit Pasta base prime, carrying a **machine-checked, axiom-clean
  Pratt/Lucas primality certificate** (`Fact (Nat.Prime PALLAS_BASE_CARD)`). The `Field`,
  `DecidableEq`, and `CharP F p` instances all come for free from `ZMod p`. This is the
  hard part — a 255-bit primality proof with no `sorry` and no `native_decide` — and it
  is borrowed wholesale from CompElliptic (daira/CompElliptic), not postulated.
* The curve `W` is **CompElliptic's** Pallas curve (`y² = x³ + 5`): the coefficients of its
  verified `Pallas.curve` transported to a Mathlib `WeierstrassCurve.Affine` via the `toW`
  bridge, so `Wshort` is `rfl`s. This makes CompElliptic's curve the single source of truth —
  the gate theorems run over exactly the object it proves elliptic.
* `order` is the concrete other Pasta prime `q = PALLAS_SCALAR_CARD` (the scalar field
  cardinality = the Pallas group order).
* `beta` is the concrete primitive cube root of unity `5^((p-1)/3) mod p`; `beta_cube`
  (`β³ = 1`) is closed by `decide` (the exponent is `3`, so no modexp tactic is needed).

Only three things stay axioms, and they are exactly the irreducible trusted core:

* `pallas_order_smul` — **Schoof.** The group has exponent dividing `order`. A statement
  about the 255-bit point count; no Mathlib path.
* `pallas_eigen` — **CM.** `φ(x,y) = (β·x, y)` acts as `[λ]` on the group. The
  endomorphism-ring fact Mathlib lacks.
* `lam : ℤ` — the eigenvalue itself. CompElliptic supplies no endomorphism, and the
  *pairing* of a cube-root-of-unity mod `p` (our concrete `β`) with the matching
  cube-root mod `q` is curve-determined data, not a free choice — so it is left opaque
  rather than pinned to a possibly-wrong constant (which would make `pallas_eigen` false).

So `#print axioms pallas_endoMul_faithful` now lists only
`pallas_order_smul, pallas_eigen, lam` on top of `[propext, Classical.choice, Quot.sound]`
— the genuinely-non-Mathlib facts about a *definitely-non-vacuous* concrete curve. The
whole postulated "field + primality + curve" surface is gone.

`addComplete_sound_pallas` goes one further: plain *addition* needs neither Schoof nor CM, so
the AddComplete gate's group-law soundness on this concrete Pallas curve is **fully
axiom-clean** — `#print axioms` is the standard three, resting solely on CompElliptic's
verified field and curve.

This is the gate-level end of the cycle. The remaining *two-curve* reciprocity
(`TwoCycle`) is a recursion-layer concern — how scalars pass between the Pasta step/wrap
circuits — above the per-gate scope.
-/

namespace Kimchi.Cycle.Pasta

open WeierstrassCurve.Affine Kimchi.Gate.EndoMul Kimchi.Circuit.EndoMul
open CompElliptic.Fields.Pasta
open CompElliptic.CurveForms.ShortWeierstrass (toW)
open CompElliptic.Curves.Pasta

/-- The Pallas coordinate field — the **concrete** `ZMod p` from CompElliptic (= Vesta's
    scalar field), with its axiom-clean Pratt primality certificate. The `Field`,
    `DecidableEq`, and `CharP F PALLAS_BASE_CARD` instances are all inherited from `ZMod`. -/
abbrev F := PallasBaseField

/-- The Pasta base-field characteristic (the 255-bit prime `p`), concretely. -/
abbrev pPasta : ℕ := PALLAS_BASE_CARD

/-- The concrete Pallas curve, taken from **CompElliptic**: the coefficients of its verified
    `Pallas.curve` (`Pallas.a = 0`, `Pallas.b = 5`, i.e. `y² = x³ + 5`) transported to a
    Mathlib `WeierstrassCurve.Affine` via CompElliptic's `toW` bridge. This is the single
    source of truth for "the Pasta curve" — the gate theorems below run over exactly the
    curve CompElliptic proves elliptic and reasons about (`five_not_isSquare`, etc.). -/
def W : WeierstrassCurve.Affine F := toW Pallas.a Pallas.b

theorem Wshort : IsShortShape W := ⟨rfl, rfl, rfl, rfl⟩

/-- The group order (= the *other* Pasta prime `q` = the scalar-field cardinality). -/
def order : ℕ := PALLAS_SCALAR_CARD

/-- **AXIOM (Schoof).** The Pallas group has exponent dividing its order. Genuinely not
    a Mathlib theorem — a 255-bit constant. -/
axiom pallas_order_smul : ∀ P : W.Point, (order : ℤ) • P = 0

/-- The concrete base-field primitive cube root of unity `β = 5^((p-1)/3) mod p`. -/
def beta : F :=
  20444556541222657078399132219657928148671392403212669005631716460534733845831

theorem beta_cube : beta ^ 3 = 1 := by unfold beta; decide

/-- The scalar-field eigenvalue `λ` with `φ = [λ]`. Left opaque: CompElliptic supplies no
    endomorphism, and the cube-root pairing is curve-determined data, not a free choice. -/
axiom lam : ℤ

/-- **AXIOM (CM).** The endomorphism `φ(x,y) = (β·x, y)` acts as `[λ]` on the group.
    The endomorphism-ring fact Mathlib lacks. -/
axiom pallas_eigen : ∀ {x y : F} (h : W.Nonsingular x y) (h' : W.Nonsingular (beta * x) y),
    Point.some _ _ h' = lam • Point.some _ _ h

/-- The Pallas curve as a `CMCurve` — assembled over the concrete Pasta field. Using this
    in any theorem pulls only `pallas_order_smul`, `pallas_eigen`, `lam` into its
    `#print axioms` (the field/curve are now concrete definitions). -/
noncomputable def pallas : CMCurve F where
  W := W
  short := Wshort
  order := order
  order_smul := pallas_order_smul
  beta := beta
  beta_cube := beta_cube
  lam := lam
  eigen := pallas_eigen

/-- Scalars on Pallas reduce mod the group order — the Schoof axiom in action. -/
theorem pallas_zsmul (n : ℤ) (Q : pallas.W.Point) : (n % (pallas.order : ℤ)) • Q = n • Q :=
  zsmul_mod F pallas n Q

/-- **Faithful EndoMul on the REAL Pallas curve.** `endoMul_toField_cm` specialized to
    `pallas`: `P_m = [s]·T` with `(s:F) = EndoScalar.toField crumbs λ`, the eigenvalue
    supplied by Pallas's CM structure. Unlike the parametric Phase-3 result, this rests
    on the Pasta axioms — `#print axioms pallas_endoMul_toField` lists `pallas_eigen`
    (and `lam`) alongside the standard three. (A `def` only because the fully
    applied type is inferred from the specialization; it is a proof of a `∀…∃` Prop.) -/
def pallas_endoMul_toField := endoMul_toField_cm pallas

/-- **The faithful capstone, on Pallas.** `endoMul_faithful` specialized to `pallas`:
    EndoMul ∘ EndoScalar computes `[σ]·T` for the genuine scalar `σ` (the `toField`
    decode), under the `Shifted_value` range — eigenvalue *and* scalar honest, on the
    actual curve. `#print axioms` lists exactly `pallas_order_smul`, `pallas_eigen`,
    `lam` on top of the standard three. -/
def pallas_endoMul_faithful := endoMul_faithful pallas

/-- **AddComplete on the REAL Pallas curve.** The generic gate soundness
    `AddComplete.sound_point_noninf` specialized to the concrete CompElliptic Pallas curve
    `W`: a satisfying CompleteAdd witness with `inf = 0` computes the genuine elliptic-curve
    sum `(x₁,y₁) + (x₂,y₂)` in Mathlib's group on Pallas.

    Unlike the scalar results, addition needs neither Schoof (`order_smul`) nor CM (`eigen`),
    so this rests *only* on CompElliptic's verified field + curve: `#print axioms` is the
    standard three (`propext, Classical.choice, Quot.sound`) — no `pallas_*` axioms, no
    `sorryAx`, no `Lean.ofReduceBool`. The `(2 : F) ≠ 0` side condition is discharged
    concretely on `ZMod p`. -/
theorem addComplete_sound_pallas
    (w : Kimchi.Gate.AddComplete.Witness F)
    (h1 : W.Nonsingular w.x1 w.y1) (h2 : W.Nonsingular w.x2 w.y2)
    (hcons : Kimchi.Gate.AddComplete.Holds w) (hy1 : w.y1 ≠ 0) (hinf : w.inf = 0) :
    ∃ h3 : W.Nonsingular w.x3 w.y3,
      Point.some _ _ h1 + Point.some _ _ h2 = Point.some _ _ h3 :=
  Kimchi.Gate.AddComplete.sound_point_noninf W Wshort w h1 h2 hcons hy1 (by decide) hinf

end Kimchi.Cycle.Pasta
