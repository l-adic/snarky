import Mathlib

/-!
# The kimchi `EndoScalar` gate

The endomorphism-scalar gate, transcribed from proof-systems
`kimchi/src/circuits/polynomials/endomul_scalar.rs`. It is field arithmetic only: it decodes a
scalar challenge into the scalar `EndoMul` effectively multiplies by.

A row runs eight steps of Algorithm 2 of the Halo paper (p. 29). The challenge is read
MSB-first in 2-bit *crumbs* `x ∈ {0,1,2,3}`, and the state `(a, b, n)`, starting at
`(2, 2, 0)`, updates per crumb as

    n := 4·n + x        a := 2·a + c(x)        b := 2·b + d(x)

where `c = (0, 0, −1, 1)` and `d = (−1, 1, 0, 0)` are tables on the four crumbs. The circuit
enforces their interpolating cubics `cPoly`/`dPoly`, so one polynomial identity covers every
crumb. Columns 0–5 hold n0, n8, a0, b0, a8, b8 and columns 6–13 the eight crumbs.

## Main results

* `crumb_iff` — the range constraint `x(x−1)(x−2)(x−3) = 0` holds iff `x ∈ {0,1,2,3}`.
* `cPoly_table`, `dPoly_table` — the cubics agree with the tables on every crumb (char ≠ 2, 3).
* `constraints_map` — the constraint list commutes with `F`-algebra homs.
* `holds_iff` — the constraint model as a conjunction.

Soundness and completeness of a row (`sound`, `complete`), the effective scalar `a·λ + b`
and the multi-row composition are in `Kimchi.Gate.Semantics.EndoScalar`.
-/

namespace Kimchi.Gate.EndoScalar

universe u

variable {F : Type u} [Field F]

/-- The cubic `⅔x³ − 5⁄2x² + 11⁄6x` interpolating the table `(0, 0, −1, 1)` on the crumbs
    (`cPoly_table`). It is stated over a commutative `F`-algebra `R`, the field constants
    mapped in by `algebraMap F R`, so the quotient layer can read the gate over `R`. -/
def cPoly {R : Type u} [CommRing R] (x : R) (F : Type u := R) [Field F] [Algebra F R] : R :=
  algebraMap F R (2 / 3) * x ^ 3 - algebraMap F R (5 / 2) * x ^ 2 + algebraMap F R (11 / 6) * x

/-- `cPoly x − x² + 3x − 1`, the cubic interpolating the table `(−1, 1, 0, 0)` on the crumbs
    (`dPoly_table`). Over an `F`-algebra `R`, as `cPoly`. -/
def dPoly {R : Type u} [CommRing R] (x : R) (F : Type u := R) [Field F] [Algebra F R] : R :=
  cPoly x (F := F) + (-x ^ 2 + 3 * x - 1)

/-- The crumb-range polynomial `x(x−1)(x−2)(x−3)`. Its coefficients are integers, so it
    reads over any commutative ring. -/
def crumbPoly {R : Type*} [CommRing R] (x : R) : R := x * (x - 1) * (x - 2) * (x - 3)

/-- The range constraint vanishes iff the crumb is a 2-bit value, in any field. -/
theorem crumb_iff (x : F) :
    crumbPoly x = 0 ↔ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  simp only [crumbPoly, mul_eq_zero, sub_eq_zero, or_assoc]

/-- `cPoly` takes the values `(0, 0, −1, 1)` on the crumbs, given `2, 3 ≠ 0` (true on both
    Pasta fields). -/
theorem cPoly_table (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    cPoly (0 : F) = 0 ∧ cPoly (1 : F) = 0
      ∧ cPoly (2 : F) = -1 ∧ cPoly (3 : F) = 1 := by
  have h6 : (6 : F) ≠ 0 := by
    rw [show (6 : F) = 2 * 3 by norm_num]; exact mul_ne_zero h2 h3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ·
    simp only [cPoly, Algebra.algebraMap_eq_smul_one, smul_eq_mul, mul_one]; field_simp; ring

/-- `dPoly` takes the values `(−1, 1, 0, 0)` on the crumbs, given `2, 3 ≠ 0`. -/
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

/-- One `EndoScalar` row: the input and output `(a, b, n)` accumulators and the crumbs. The
    deployed gate carries eight crumbs; a `List` keeps the fold uniform in the count, so one
    `Witness` can also model a whole multi-row challenge. -/
structure Witness (F : Type*) where
  /-- The input `a` accumulator (`2` at the start of a challenge). -/
  a0 : F
  /-- The input `b` accumulator (`2` at the start of a challenge). -/
  b0 : F
  /-- The input `n` accumulator (`0` at the start of a challenge). -/
  n0 : F
  /-- The output `a` accumulator, after folding `a := 2·a + cPoly x` over the crumbs. -/
  a8 : F
  /-- The output `b` accumulator, after folding `b := 2·b + dPoly x` over the crumbs. -/
  b8 : F
  /-- The output `n` accumulator, after folding `n := 4·n + x` over the crumbs. -/
  n8 : F
  /-- The MSB-first 2-bit crumbs of the challenge. -/
  crumbs : List F

/-- The gate's constraint expressions: the `n`, `a` and `b` folds closing at `n8`, `a8` and
    `b8`, then the range polynomial of each crumb. Each fold is written `expected − actual`,
    as the deployed gate writes it, so the α-weighted linearization matches by value, not just
    by vanishing. `Holds` reads this list. It is stated over an `F`-algebra `R`,
    as `cPoly`, for the quotient layer's `Argument` instance. -/
def constraints {R : Type u} [CommRing R] (w : Witness R) (F : Type u := R) [Field F]
    [Algebra F R] : List R :=
  [ w.crumbs.foldl (fun acc x => 4 * acc + x) w.n0 - w.n8
  , w.crumbs.foldl (fun acc x => 2 * acc + cPoly x (F := F)) w.a0 - w.a8
  , w.crumbs.foldl (fun acc x => 2 * acc + dPoly x (F := F)) w.b0 - w.b8 ]
  ++ w.crumbs.map crumbPoly

/-- Apply `f : R → S` to every cell of a witness: the six accumulators and every crumb. -/
def Witness.map {R S : Type*} (f : R → S) (w : Witness R) : Witness S where
  a0 := f w.a0
  b0 := f w.b0
  n0 := f w.n0
  a8 := f w.a8
  b8 := f w.b8
  n8 := f w.n8
  crumbs := w.crumbs.map f

/-- An `F`-algebra hom commutes with `cPoly`: it fixes the `algebraMap F _` coefficients. -/
private theorem cPoly_map {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) (x : R) : f (cPoly x (F := F)) = cPoly (f x) (F := F) := by
  simp only [cPoly, map_sub, map_add, map_mul, map_pow, AlgHom.commutes]

/-- An `F`-algebra hom commutes with `dPoly`. -/
private theorem dPoly_map {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) (x : R) : f (dPoly x (F := F)) = dPoly (f x) (F := F) := by
  simp only [dPoly, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one, cPoly_map f]

/-- An `F`-algebra hom commutes with `crumbPoly`. -/
private theorem crumbPoly_map {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) (x : R) : f (crumbPoly x) = crumbPoly (f x) := by
  simp only [crumbPoly, map_mul, map_sub, map_ofNat, map_one]

/-- An `F`-algebra hom distributes through the `n` fold `n := 4·n + x`. -/
private theorem foldl_map_n {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) :
    ∀ (xs : List R) (init : R),
      f (xs.foldl (fun acc x => 4 * acc + x) init)
        = (xs.map f).foldl (fun acc x => 4 * acc + x) (f init)
  | [], _ => rfl
  | y :: ys, init => by
    simp only [List.foldl_cons, List.map_cons]
    rw [foldl_map_n f ys (4 * init + y), map_add, map_mul, map_ofNat]

/-- An `F`-algebra hom distributes through the `a` fold `a := 2·a + cPoly x`. -/
private theorem foldl_map_c {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) :
    ∀ (xs : List R) (init : R),
      f (xs.foldl (fun acc x => 2 * acc + cPoly x (F := F)) init)
        = (xs.map f).foldl (fun acc x => 2 * acc + cPoly x (F := F)) (f init)
  | [], _ => rfl
  | y :: ys, init => by
    simp only [List.foldl_cons, List.map_cons]
    rw [foldl_map_c f ys (2 * init + cPoly y (F := F)), map_add, map_mul, map_ofNat, cPoly_map f]

/-- An `F`-algebra hom distributes through the `b` fold `b := 2·b + dPoly x`. -/
private theorem foldl_map_d {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) :
    ∀ (xs : List R) (init : R),
      f (xs.foldl (fun acc x => 2 * acc + dPoly x (F := F)) init)
        = (xs.map f).foldl (fun acc x => 2 * acc + dPoly x (F := F)) (f init)
  | [], _ => rfl
  | y :: ys, init => by
    simp only [List.foldl_cons, List.map_cons]
    rw [foldl_map_d f ys (2 * init + dPoly y (F := F)), map_add, map_mul, map_ofNat, dPoly_map f]

/-- **Naturality.** An `F`-algebra hom `f` commutes with the constraint list: mapping `f`
    over `constraints w` gives `constraints (Witness.map f w)`. This makes the gate an
    `Argument` instance. -/
theorem constraints_map {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) (w : Witness R) :
    (constraints (F := F) w).map f = constraints (F := F) (Witness.map f w) := by
  simp only [constraints, Witness.map, List.map_append, List.map_cons, List.map_nil, map_sub]
  rw [foldl_map_n f w.crumbs w.n0, foldl_map_c f w.crumbs w.a0, foldl_map_d f w.crumbs w.b0]
  congr 1
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun x _ => crumbPoly_map f x

/-- The relational spec: every constraint expression vanishes. -/
def Holds (w : Witness F) : Prop :=
  ∀ e ∈ constraints w, e = 0

instance [DecidableEq F] (w : Witness F) : Decidable (Holds w) := by
  unfold Holds
  infer_instance

/-- `Holds` as a conjunction: the three folds close and every crumb is in range. -/
theorem holds_iff (w : Witness F) :
    Holds w ↔
      w.n8 = w.crumbs.foldl (fun acc x => 4 * acc + x) w.n0
        ∧ w.a8 = w.crumbs.foldl (fun acc x => 2 * acc + cPoly x) w.a0
        ∧ w.b8 = w.crumbs.foldl (fun acc x => 2 * acc + dPoly x) w.b0
        ∧ ∀ x ∈ w.crumbs, crumbPoly x = 0 := by
  simp only [Holds, constraints, List.cons_append, List.nil_append, List.forall_mem_cons,
    List.forall_mem_map, sub_eq_zero]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1.symm, h2.symm, h3.symm, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1.symm, h2.symm, h3.symm, h4⟩

/-- The honest prover's row: the outputs are the three folds of the inputs over `crumbs`. It
    satisfies the gate when every crumb is a 2-bit value (`complete`). -/
def build (a0 b0 n0 : F) (crumbs : List F) : Witness F :=
  { a0, b0, n0
  , n8 := crumbs.foldl (fun acc x => 4 * acc + x) n0
  , a8 := crumbs.foldl (fun acc x => 2 * acc + cPoly x) a0
  , b8 := crumbs.foldl (fun acc x => 2 * acc + dPoly x) b0
  , crumbs }

end Kimchi.Gate.EndoScalar
