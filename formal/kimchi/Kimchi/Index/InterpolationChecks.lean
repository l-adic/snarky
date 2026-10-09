import Kimchi.Index.Interpolation
import Kimchi.Permutation.Wiring
import Mathlib.Tactic.NormNum.Prime

/-!
# Inverse NTT checks

A nonconstant polynomial over the field of 113 elements is evaluated on sixteen domain nodes
and interpolated back to its coefficients. The check includes coefficients in both halves of
the domain, including its final coefficient. A second check rejects the same coefficients
with the input values changed, and an empty input zero extends to the zero polynomial.
-/

namespace Kimchi.Index.InterpolationChecks

open CompPoly.CPolynomial.NTT

private abbrev K := ZMod 113
private instance : Fact (Nat.Prime 113) := ⟨by norm_num⟩

private def domain : Domain K :=
  ⟨4, 40, Permutation.isPrimitiveRoot_of_certificate rfl (by decide +kernel),
    by decide +kernel⟩

private def coefficients : Array K := #[3, 5, 0, 7, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 13]

private def values (i : Fin domain.n) : K :=
  let x := domain.omega ^ i.val
  3 + 5 * x + 7 * x ^ 3 + 11 * x ^ 8 + 13 * x ^ 15

/-- The inverse transform recovers all coefficients, including the second chunk's. -/
theorem recovers_coefficients : columnCoefficients domain values = coefficients := by
  rw [columnCoefficients, Inverse.inverseImpl_correct]
  decide +kernel

/-- Changing a node value does not reproduce the original coefficients. -/
theorem rejects_altered_value :
    columnCoefficients domain (fun i => values i + if i.val = 9 then 1 else 0) ≠
      coefficients := by
  rw [columnCoefficients, Inverse.inverseImpl_correct]
  decide +kernel

/-- The empty evaluation array interpolates as sixteen zero coefficients. -/
theorem zero_extends_empty : Inverse.inverseImpl domain #[] = Array.replicate 16 (0 : K) := by
  rw [Inverse.inverseImpl_correct]
  decide +kernel

end Kimchi.Index.InterpolationChecks
