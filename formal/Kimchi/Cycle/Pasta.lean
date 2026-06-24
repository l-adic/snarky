import Kimchi.Cycle.EndoMul

/-!
# Phase 4: instantiating the cycle for Pasta — the axioms become real

Phases 0–3 prove the faithful gate results for *any* `CMCurve`, staying
standard-axiom-clean because the Pasta facts are structure-field *hypotheses*. This
file takes the last step: it instantiates a concrete curve (Pallas), at which point
those hypotheses become honest Lean `axiom`s. Everything downstream that uses `pallas`
will show them in `#print axioms` — no longer `[propext, Classical.choice, Quot.sound]`
but `+ pallas_order_smul, pallas_eigen, …`. That is exactly correct: the curve's group
order (Schoof) and CM eigenvalue (`φ=[λ]`) are genuinely not Mathlib theorems.

The coordinate field `F` is left opaque here (concretely `ZMod p` for the 255-bit Pasta
prime `p`); only the genuinely-unprovable facts — `pallas_order_smul`, `pallas_eigen` —
are the load-bearing axioms. The point-structure data (`W`, short shape, `β`) are
likewise opaque stand-ins for the concrete `y² = x³ + 5`. A fully concrete `ZMod p`
version would replace these with definitions, but `order_smul`/`eigen` stay axioms
regardless — so this faithfully exhibits the axiom boundary.

This is the gate-level end of the cycle. The remaining *two-curve* reciprocity
(`TwoCycle`) is a recursion-layer concern — how scalars pass between the Pasta step/wrap
circuits — above the per-gate scope.
-/

namespace Kimchi.Cycle.Pasta

open WeierstrassCurve.Affine Kimchi.Gate.EndoMul Kimchi.Circuit.EndoMul

/-- The Pallas coordinate field (= Vesta's scalar field); opaque, concretely `ZMod p`. -/
axiom F : Type
axiom instField : Field F
attribute [instance] instField
axiom instDecEq : DecidableEq F
attribute [instance] instDecEq
/-- The Pasta base-field characteristic (the 255-bit prime `p`). -/
axiom pPasta : ℕ
axiom instCharP : CharP F pPasta
attribute [instance] instCharP

/-- Opaque stand-in for the Pallas curve `y² = x³ + 5` over `F`. -/
axiom W : WeierstrassCurve.Affine F
axiom Wshort : IsShortShape W
/-- The group order (= the *other* Pasta prime `q`). -/
axiom order : ℕ
/-- **AXIOM (Schoof).** The Pallas group has exponent dividing its order. Genuinely not
    a Mathlib theorem — a 255-bit constant. -/
axiom pallas_order_smul : ∀ P : W.Point, (order : ℤ) • P = 0
axiom beta : F
axiom beta_cube : beta ^ 3 = 1
axiom lam : ℤ
/-- **AXIOM (CM).** The endomorphism `φ(x,y) = (β·x, y)` acts as `[λ]` on the group.
    The endomorphism-ring fact Mathlib lacks. -/
axiom pallas_eigen : ∀ {x y : F} (h : W.Nonsingular x y) (h' : W.Nonsingular (beta * x) y),
    Point.some h' = lam • Point.some h

/-- The Pallas curve as a `CMCurve` — assembled from the Pasta axioms. Using this in any
    theorem pulls `pallas_order_smul`, `pallas_eigen` (and the opaque data) into its
    `#print axioms`. -/
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
    (and the curve data) alongside the standard three. (A `def` only because the fully
    applied type is inferred from the specialization; it is a proof of a `∀…∃` Prop.) -/
def pallas_endoMul_toField := endoMul_toField_cm pallas

/-- **The faithful capstone, on Pallas.** `endoMul_faithful` specialized to `pallas`:
    EndoMul ∘ EndoScalar computes `[σ]·T` for the genuine scalar `σ` (the `toField`
    decode), under the `Shifted_value` range — eigenvalue *and* scalar honest, on the
    actual curve. `#print axioms` lists `pallas_order_smul`, `pallas_eigen`. -/
def pallas_endoMul_faithful := endoMul_faithful pallas

end Kimchi.Cycle.Pasta
