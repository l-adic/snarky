import Kimchi.Checker.Row

/-! # The kimchi `EndoMulScalar` (endo scalar decomposition) gate.

Transcribed from proof-systems `.../polynomials/endomul_scalar.rs` (11 constraints, single
row, no coefficients). Decomposes a scalar into 8 two-bit "crumbs" and accumulates `n,a,b`.

Column layout: `0=n0, 1=n8, 2=a0, 3=b0, 4=a8, 5=b8, 6..13 = x0..x7` (crumbs), `14` unused.

The `a`/`b` accumulators use the rational helpers
`c(x) = ⅔x³ − 5⁄2x² + 11⁄6x` and `d(x) = c(x) − x² + 3x − 1`. We clear denominators by
multiplying those two constraints by `6` (invertible mod the prime, so `6·X = 0 ↔ X = 0`),
giving the integer-coefficient forms `c6 = 6·c` and `d6 = 6·d`. -/

namespace Kimchi.Gate.EndoScalar

variable {F : Type*}

/-- `6 · c(x) = 4x³ − 15x² + 11x`. -/
def c6 [CommRing F] (x : F) : F := 4 * x ^ 3 - 15 * x ^ 2 + 11 * x

/-- `6 · d(x) = 4x³ − 21x² + 29x − 6`. -/
def d6 [CommRing F] (x : F) : F := 4 * x ^ 3 - 21 * x ^ 2 + 29 * x - 6

/-- `crumb(x) = x⁴ − 6x³ + 11x² − 6x` — vanishes iff `x ∈ {0,1,2,3}`. -/
def crumb [CommRing F] (x : F) : F := x ^ 4 - 6 * x ^ 3 + 11 * x ^ 2 - 6 * x

def holds [CommRing F] (curr _next : Row F) : Prop :=
  let w := fun i => curr.getD i 0
  -- n8 = 4⁸·n0 + Σ 4^(7−i)·xᵢ
  (65536 * w 0 + 16384 * w 6 + 4096 * w 7 + 1024 * w 8 + 256 * w 9 + 64 * w 10
      + 16 * w 11 + 4 * w 12 + w 13 - w 1) = 0
  -- 6·(a8 − [256·a0 + Σ 2^(7−i)·c(xᵢ)]) = 0
  ∧ (1536 * w 2 + (128 * c6 (w 6) + 64 * c6 (w 7) + 32 * c6 (w 8) + 16 * c6 (w 9)
        + 8 * c6 (w 10) + 4 * c6 (w 11) + 2 * c6 (w 12) + c6 (w 13)) - 6 * w 4) = 0
  -- 6·(b8 − [256·b0 + Σ 2^(7−i)·d(xᵢ)]) = 0
  ∧ (1536 * w 3 + (128 * d6 (w 6) + 64 * d6 (w 7) + 32 * d6 (w 8) + 16 * d6 (w 9)
        + 8 * d6 (w 10) + 4 * d6 (w 11) + 2 * d6 (w 12) + d6 (w 13)) - 6 * w 5) = 0
  ∧ crumb (w 6) = 0 ∧ crumb (w 7) = 0 ∧ crumb (w 8) = 0 ∧ crumb (w 9) = 0
  ∧ crumb (w 10) = 0 ∧ crumb (w 11) = 0 ∧ crumb (w 12) = 0 ∧ crumb (w 13) = 0

def ok [CommRing F] [DecidableEq F] (curr _next : Row F) : Bool :=
  let w := fun i => curr.getD i 0
  (65536 * w 0 + 16384 * w 6 + 4096 * w 7 + 1024 * w 8 + 256 * w 9 + 64 * w 10
      + 16 * w 11 + 4 * w 12 + w 13 - w 1 == 0)
  && (1536 * w 2 + (128 * c6 (w 6) + 64 * c6 (w 7) + 32 * c6 (w 8) + 16 * c6 (w 9)
        + 8 * c6 (w 10) + 4 * c6 (w 11) + 2 * c6 (w 12) + c6 (w 13)) - 6 * w 4 == 0)
  && (1536 * w 3 + (128 * d6 (w 6) + 64 * d6 (w 7) + 32 * d6 (w 8) + 16 * d6 (w 9)
        + 8 * d6 (w 10) + 4 * d6 (w 11) + 2 * d6 (w 12) + d6 (w 13)) - 6 * w 5 == 0)
  && (crumb (w 6) == 0) && (crumb (w 7) == 0) && (crumb (w 8) == 0) && (crumb (w 9) == 0)
  && (crumb (w 10) == 0) && (crumb (w 11) == 0) && (crumb (w 12) == 0) && (crumb (w 13) == 0)

theorem ok_iff [CommRing F] [DecidableEq F] (curr next : Row F) :
    ok curr next = true ↔ holds curr next := by
  simp only [ok, holds, Bool.and_eq_true, beq_iff_eq, and_assoc]

end Kimchi.Gate.EndoScalar
