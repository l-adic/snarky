import Mathlib

namespace Kimchi

/-- The short-Weierstrass shape the kimchi EC gates assume: `a₁ = a₂ = a₃ = a₄ = 0`
    (so the curve is `y² = x³ + a₆`). The Pasta curves have exactly this shape.

    An `abbrev` so it unfolds transparently to the underlying conjunction — proofs
    can `obtain ⟨_, _, _, _⟩` it and reconstruct it with `⟨_, _, _, _⟩` directly. -/
abbrev IsShortShape {F : Type*} [CommRing F] (W : WeierstrassCurve.Affine F) : Prop :=
  W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0

end Kimchi
