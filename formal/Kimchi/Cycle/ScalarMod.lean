import Kimchi.Curve
import CompElliptic.CurveForms.ShortWeierstrass

/-!
# Scalars modulo the group order

On a short-Weierstrass curve's point group, `[n]·P` depends only on `n` modulo the group
order `Nat.card (SWPoint E)`. This `zsmul_mod` is the bridge from integer scalars to the
finite scalar group, used throughout the cycle layer.
-/

namespace Kimchi.Cycle

open CompElliptic.CurveForms.ShortWeierstrass

variable {F : Type*} [Field F] [DecidableEq F]

/-- `[n]·P` reduces its scalar modulo the group order:
    `(n % Nat.card (SWPoint E)) • P = n • P`.

    Immediate from `card_nsmul_eq_zero'` (`Nat.card G • x = 0`) on `AddCommGroup (SWPoint E)`;
    when the group order is `0` (an infinite group) it is the vacuous `n % 0 = n`. -/
theorem zsmul_mod (E : SWCurve F) (n : ℤ) (P : SWPoint E) :
    (n % (Nat.card (SWPoint E) : ℤ)) • P = n • P := by
  have hcard : ∀ Q : SWPoint E, (Nat.card (SWPoint E) : ℤ) • Q = 0 := fun Q => by
    rw [natCast_zsmul]; exact card_nsmul_eq_zero'
  have h : n • P
      = (n % (Nat.card (SWPoint E) : ℤ)) • P
        + (Nat.card (SWPoint E) : ℤ) • ((n / (Nat.card (SWPoint E) : ℤ)) • P) := by
    rw [← mul_smul, ← add_smul, Int.emod_add_mul_ediv]
  rw [h, hcard, _root_.add_zero]

end Kimchi.Cycle
