import Mathlib

/-!
# The kimchi `EndoScalar` gate

The endomorphism-scalar gate, transcribed from proof-systems
`kimchi/src/circuits/polynomials/endomul_scalar.rs` (and the PureScript
`Snarky.Circuit.Kimchi.EndoScalar`). Unlike the EC gates this one is PURE FIELD
ARITHMETIC: it decomposes a scalar challenge into the field element it represents
under the curve endomorphism, ready for `EndoMul` to multiply by.

Each row runs 8 iterations of "Algorithm 2" from the Halo paper (p. 29). The
challenge is read MSB-first in 2-bit *crumbs* `x ∈ {0,1,2,3}`; the state `(a,b,n)`
(initialized to `(2,2,0)`) updates per crumb as

    n := 4·n + x        a := 2·a + c_func(x)        b := 2·b + d_func(x)

and the effective scalar is `a·λ + b` (`λ` = the scalar-field endomorphism
eigenvalue), with `n` asserted equal to the input challenge. The two crumb
functions are the `{0,1,2,3} → value` tables

    c_func = (0, 0, −1, 1)        d_func = (−1, 1, 0, 0)

which the circuit implements as the interpolating cubics (so a single polynomial
identity covers all four cases).

## Main results

* `crumb_iff` — the range constraint `x(x−1)(x−2)(x−3) = 0` holds iff
  `x ∈ {0,1,2,3}` (in any field).
* `cPoly_table` / `dPoly_table` — the Halo interpolating cubics `cPoly` / `dPoly`
  agree with the `c_func` / `d_func` tables on every crumb (char ≠ 2,3).

## Supporting development

The constraint model (`Witness` / `Holds`) and the per-row soundness
`gate_endoScalar` — a satisfying row computes the Algorithm-2 fold over valid
crumbs.
-/

namespace Kimchi.Gate.EndoScalar

variable {F : Type*} [Field F]

/-- `c_func`'s interpolating cubic `⅔x³ − 5⁄2x² + 11⁄6x` (Lagrange over
    `(0,0),(1,0),(2,−1),(3,1)`). The gate enforces this polynomial; `cPoly_table`
    shows it equals the intended `(0,0,−1,1)` table on crumbs. -/
def cPoly (x : F) : F := 2 / 3 * x ^ 3 - 5 / 2 * x ^ 2 + 11 / 6 * x

/-- `d_func = c_func + (−x² + 3x − 1)`; on crumbs it is the `(−1,1,0,0)` table. -/
def dPoly (x : F) : F := cPoly x + (-x ^ 2 + 3 * x - 1)

/-- The crumb-range polynomial `x(x−1)(x−2)(x−3)` — zero exactly on `{0,1,2,3}`. -/
def crumbPoly (x : F) : F := x * (x - 1) * (x - 2) * (x - 3)

/-- The range constraint vanishes iff the crumb is a genuine 2-bit value. Holds in
    any field (an integral domain): a product is zero iff a factor is. -/
theorem crumb_iff (x : F) :
    crumbPoly x = 0 ↔ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  simp only [crumbPoly, mul_eq_zero, sub_eq_zero, or_assoc]

/-- The interpolating cubic `cPoly` reproduces the `c_func = (0,0,−1,1)` table on
    every crumb (needs `2,3 ≠ 0`, true on the Pasta scalar fields). -/
theorem cPoly_table (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    cPoly (0 : F) = 0 ∧ cPoly (1 : F) = 0
      ∧ cPoly (2 : F) = -1 ∧ cPoly (3 : F) = 1 := by
  have h6 : (6 : F) ≠ 0 := by
    rw [show (6 : F) = 2 * 3 by norm_num]; exact mul_ne_zero h2 h3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> · simp only [cPoly]; field_simp; ring

/-- `dPoly` reproduces the `d_func = (−1,1,0,0)` table on every crumb. -/
theorem dPoly_table (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    dPoly (0 : F) = -1 ∧ dPoly (1 : F) = 1
      ∧ dPoly (2 : F) = 0 ∧ dPoly (3 : F) = 0 := by
  obtain ⟨c0, c1, c2, c3⟩ := cPoly_table h2 h3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [dPoly]
  · rw [c0]; ring
  · rw [c1]; ring
  · rw [c2]; ring
  · rw [c3]; ring

/-! ## The gate's constraint model. -/

/-- One `EndoScalar` row: the input/output `(a,b,n)` accumulators and the 8 crumbs
    (kept as a `List` — the fold is uniform in the count). -/
structure Witness (F : Type*) where
  a0 : F
  b0 : F
  n0 : F
  a8 : F
  b8 : F
  n8 : F
  crumbs : List F

/-- The 11 gate constraints: the three accumulator folds (`n := 4n+x`,
    `a := 2a + cPoly x`, `b := 2b + dPoly x`) close at `a8,b8,n8`, and every crumb
    satisfies the range polynomial. -/
def Holds (w : Witness F) : Prop :=
  w.n8 = w.crumbs.foldl (fun acc x => 4 * acc + x) w.n0
    ∧ w.a8 = w.crumbs.foldl (fun acc x => 2 * acc + cPoly x) w.a0
    ∧ w.b8 = w.crumbs.foldl (fun acc x => 2 * acc + dPoly x) w.b0
    ∧ ∀ x ∈ w.crumbs, crumbPoly x = 0

/-- Per-row soundness: a satisfying row forces genuine 2-bit crumbs. (The `a`/`b`/`n`
    accumulator folds are definitional in `Holds`; combined with `cPoly_table` /
    `dPoly_table` this says the row faithfully runs Algorithm 2 over valid crumbs.
    Restating the folds with the bare `c_func`/`d_func` tables is the next step,
    at the multi-row circuit level.) -/
theorem gate_endoScalar (w : Witness F) (h : Holds w) :
    ∀ x ∈ w.crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  obtain ⟨_, _, _, hcrumb⟩ := h
  exact fun x hx => (crumb_iff x).mp (hcrumb x hx)

end Kimchi.Gate.EndoScalar
