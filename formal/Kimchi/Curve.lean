/-
  Curve.lean

  The elliptic-curve oracle for the kimchi EC gates.

  The custom EC gates (AddComplete, VarBaseMul, EndoMul) all operate on the Pasta
  curves (Pallas / Vesta), which are short Weierstrass curves `y² = x³ + b` — i.e.
  every `a`-invariant except `a₆` vanishes. The gates are checked against
  Mathlib's `WeierstrassCurve.Affine` specialized to this shape, so we name the
  shape predicate once here and share it across the gate proofs instead of
  inlining the four-way conjunction in every theorem.
-/
import Mathlib

namespace Kimchi

/-- The short-Weierstrass shape the kimchi EC gates assume: `a₁ = a₂ = a₃ = a₄ = 0`
    (so the curve is `y² = x³ + a₆`). The Pasta curves have exactly this shape.

    An `abbrev` so it unfolds transparently to the underlying conjunction — proofs
    can `obtain ⟨_, _, _, _⟩` it and reconstruct it with `⟨_, _, _, _⟩` directly. -/
abbrev IsShortShape {F : Type*} [CommRing F] (W : WeierstrassCurve.Affine F) : Prop :=
  W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0

end Kimchi
