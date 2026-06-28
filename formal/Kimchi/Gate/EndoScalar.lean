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

* `sound` / `complete` — a satisfying row genuinely runs Halo's Algorithm 2: the crumbs are
  valid 2-bit values and the `a`/`b`/`n` accumulators are the Algorithm-2 folds, the `a`/`b`
  folds using the *literal* `c_func`/`d_func` tables (the cubics in `Holds` interpolate them).
  Conversely the honest prover's witness (`build`) satisfies the constraints for any valid crumbs.

## Supporting development

The constraint model (`Witness` / `Holds` / `ok` / `ok_iff`) and the cubic↔table bridge
(`cFunc` / `dFunc`, `cPoly_eq_cFunc` / `dPoly_eq_dFunc`, `foldl_table`). The effective scalar
`a·λ + b` and the multi-row composition live in `Kimchi.Circuit.EndoScalar`.
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

/-- One `EndoScalar` row: the input/output `(a,b,n)` accumulators and the crumbs
    (the deployed gate carries 8; kept as a `List`, since the fold is uniform in the
    count — so one `Witness` can equally model a whole multi-row challenge). -/
structure Witness (F : Type*) where
  a0 : F
  b0 : F
  n0 : F
  a8 : F
  b8 : F
  n8 : F
  crumbs : List F
deriving Repr

/-- The gate constraints (11 at the deployed 8-crumb width: `3 + #crumbs`): the three
    accumulator folds (`n := 4n+x`, `a := 2a + cPoly x`, `b := 2b + dPoly x`) close at
    `a8,b8,n8`, and every crumb satisfies the range polynomial. -/
def Holds (w : Witness F) : Prop :=
  w.n8 = w.crumbs.foldl (fun acc x => 4 * acc + x) w.n0
    ∧ w.a8 = w.crumbs.foldl (fun acc x => 2 * acc + cPoly x) w.a0
    ∧ w.b8 = w.crumbs.foldl (fun acc x => 2 * acc + dPoly x) w.b0
    ∧ ∀ x ∈ w.crumbs, crumbPoly x = 0

/-- EXECUTABLE checker: the three accumulator folds close and every crumb is in range. -/
def ok [DecidableEq F] (w : Witness F) : Bool :=
  (w.n8 == w.crumbs.foldl (fun acc x => 4 * acc + x) w.n0)
    && (w.a8 == w.crumbs.foldl (fun acc x => 2 * acc + cPoly x) w.a0)
    && (w.b8 == w.crumbs.foldl (fun acc x => 2 * acc + dPoly x) w.b0)
    && w.crumbs.all (fun x => crumbPoly x == 0)

/-- Reflection: the checker faithfully decides the constraints. -/
theorem ok_iff [DecidableEq F] (w : Witness F) : ok w = true ↔ Holds w := by
  simp only [ok, Holds, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, and_assoc]

/-- Build the canonical satisfying row from valid crumbs and the input accumulators: the three
    outputs are the accumulator folds, run on the given crumbs. -/
def build (a0 b0 n0 : F) (crumbs : List F) : Witness F :=
  { a0, b0, n0
  , n8 := crumbs.foldl (fun acc x => 4 * acc + x) n0
  , a8 := crumbs.foldl (fun acc x => 2 * acc + cPoly x) a0
  , b8 := crumbs.foldl (fun acc x => 2 * acc + dPoly x) b0
  , crumbs }

/-- **Completeness.** The witness the honest prover constructs (`build`) satisfies all the gate
    constraints, given that every crumb is a genuine 2-bit value — the folds close by
    construction, and the range constraint follows from `crumb_iff`. -/
theorem complete (a0 b0 n0 : F) (crumbs : List F)
    (hvalid : ∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) :
    Holds (build a0 b0 n0 crumbs) :=
  ⟨rfl, rfl, rfl, fun x hx => (crumb_iff x).mpr (hvalid x hx)⟩

/-! ## The bare-table form of the folds.

    The `a`/`b` constraints use the interpolating cubics; on valid crumbs they run
    the same fold with the bare `c_func`/`d_func` tables. -/

/-- Replacing the per-crumb function leaves the `2·acc + f x` fold unchanged when
    the two functions agree on every crumb. -/
theorem foldl_table {φ ψ : F → F} :
    ∀ (xs : List F) (init : F), (∀ x ∈ xs, φ x = ψ x) →
      xs.foldl (fun acc x => 2 * acc + φ x) init
        = xs.foldl (fun acc x => 2 * acc + ψ x) init
  | [], _, _ => rfl
  | y :: ys, init, h => by
    simp only [List.foldl_cons]
    rw [h y (by simp), foldl_table ys _ (fun x hx => h x (by simp [hx]))]

variable [DecidableEq F]

/-- `c_func` as the bare `(0,0,−1,1)` table. -/
def cFunc (x : F) : F := if x = 2 then -1 else if x = 3 then 1 else 0

/-- `d_func` as the bare `(−1,1,0,0)` table. -/
def dFunc (x : F) : F := if x = 0 then -1 else if x = 1 then 1 else 0

/-- On a valid crumb the interpolating cubic `cPoly` equals the bare table `cFunc`. -/
theorem cPoly_eq_cFunc (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x : F}
    (hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) : cPoly x = cFunc x := by
  obtain ⟨c0, c1, c2, c3⟩ := cPoly_table h2 h3
  have e02 : (0 : F) ≠ 2 := fun h => h2 h.symm
  have e03 : (0 : F) ≠ 3 := fun h => h3 h.symm
  have e12 : (1 : F) ≠ 2 := fun h => (one_ne_zero : (1 : F) ≠ 0) (by linear_combination -h)
  have e13 : (1 : F) ≠ 3 := fun h => h2 (by linear_combination -h)
  have e32 : (3 : F) ≠ 2 := fun h => (one_ne_zero : (1 : F) ≠ 0) (by linear_combination h)
  rcases hx with rfl | rfl | rfl | rfl
  · rw [c0, cFunc, if_neg e02, if_neg e03]
  · rw [c1, cFunc, if_neg e12, if_neg e13]
  · rw [c2, cFunc, if_pos rfl]
  · rw [c3, cFunc, if_neg e32, if_pos rfl]

/-- On a valid crumb the interpolating cubic `dPoly` equals the bare table `dFunc`. -/
theorem dPoly_eq_dFunc (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x : F}
    (hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) : dPoly x = dFunc x := by
  obtain ⟨d0, d1, d2, d3⟩ := dPoly_table h2 h3
  have e21 : (2 : F) ≠ 1 := fun h => (one_ne_zero : (1 : F) ≠ 0) (by linear_combination h)
  have e31 : (3 : F) ≠ 1 := fun h => h2 (by linear_combination h)
  rcases hx with rfl | rfl | rfl | rfl
  · rw [d0, dFunc, if_pos rfl]
  · rw [d1, dFunc, if_neg ((one_ne_zero : (1 : F) ≠ 0)), if_pos rfl]
  · rw [d2, dFunc, if_neg h2, if_neg e21]
  · rw [d3, dFunc, if_neg h3, if_neg e31]

/-- **Soundness.** A satisfying row genuinely runs Halo's Algorithm 2: the crumbs are valid 2-bit
    values, and the `a`/`b`/`n` accumulators are the Algorithm-2 folds — with the `a`/`b` folds
    using the *literal* `c_func`/`d_func` lookup tables (the cubics in `Holds` interpolate them, so
    `2,3 ≠ 0` — true on the Pasta scalar fields). -/
theorem sound (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (w : Witness F) (h : Holds w) :
    (∀ x ∈ w.crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3)
      ∧ w.n8 = w.crumbs.foldl (fun n x => 4 * n + x) w.n0
      ∧ w.a8 = w.crumbs.foldl (fun a x => 2 * a + cFunc x) w.a0
      ∧ w.b8 = w.crumbs.foldl (fun b x => 2 * b + dFunc x) w.b0 := by
  obtain ⟨hn, ha, hb, hc⟩ := h
  have hv : ∀ x ∈ w.crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 :=
    fun x hx => (crumb_iff x).mp (hc x hx)
  refine ⟨hv, hn, ?_, ?_⟩
  · rw [ha]; exact foldl_table w.crumbs w.a0 (fun x hx => cPoly_eq_cFunc h2 h3 (hv x hx))
  · rw [hb]; exact foldl_table w.crumbs w.b0 (fun x hx => dPoly_eq_dFunc h2 h3 (hv x hx))

end Kimchi.Gate.EndoScalar
