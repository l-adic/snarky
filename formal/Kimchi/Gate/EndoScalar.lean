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

universe u

variable {F : Type u} [Field F]

/-- `c_func`'s interpolating cubic `⅔x³ − 5⁄2x² + 11⁄6x` (Lagrange over
    `(0,0),(1,0),(2,−1),(3,1)`). The gate enforces this polynomial; `cPoly_table`
    shows it equals the intended `(0,0,−1,1)` table on crumbs.

    Stated over an arbitrary commutative `F`-algebra `R`: the field constants become their
    `algebraMap F R` images, so the quotient layer can read the gate over `R`. At `R = F` the
    algebra map is the identity and this is the original field polynomial. -/
def cPoly {R : Type u} [CommRing R] (x : R) (F : Type u := R) [Field F] [Algebra F R] : R :=
  algebraMap F R (2 / 3) * x ^ 3 - algebraMap F R (5 / 2) * x ^ 2 + algebraMap F R (11 / 6) * x

/-- `d_func = c_func + (−x² + 3x − 1)`; on crumbs it is the `(−1,1,0,0)` table.
    Read over an arbitrary commutative `F`-algebra `R` (see `cPoly`). -/
def dPoly {R : Type u} [CommRing R] (x : R) (F : Type u := R) [Field F] [Algebra F R] : R :=
  cPoly x (F := F) + (-x ^ 2 + 3 * x - 1)

/-- The crumb-range polynomial `x(x−1)(x−2)(x−3)` — zero exactly on `{0,1,2,3}`.
    Its coefficients are integers, so it needs no algebra map: it reads over any commutative
    ring `R`. -/
def crumbPoly {R : Type*} [CommRing R] (x : R) : R := x * (x - 1) * (x - 2) * (x - 3)

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
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ·
    simp only [cPoly, Algebra.algebraMap_eq_smul_one, smul_eq_mul, mul_one]; field_simp; ring

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

/-- The gate constraint expressions (11 at the deployed 8-crumb width: `3 + #crumbs`) — the
    single transcription: the three accumulator folds (`n := 4n+x`, `a := 2a + cPoly x`,
    `b := 2b + dPoly x`) closing at `a8,b8,n8`, and the range polynomial per crumb. Oriented
    as production writes them (`expected − actual`, `endomul_scalar.rs` `constraint_checks`)
    so the α-weighted verifier linearization matches by value, not just by vanishing. The
    relational spec (`Holds`) and the checker (`ok`) are read from this list. Stated over an
    arbitrary commutative `F`-algebra `R` — `cPoly`/`dPoly` carry field-constant coefficients
    mapped in through `algebraMap F R`; at `R = F` this is the original field reading, and the
    `R`-generic form is what the quotient layer's `Argument` instance consumes. -/
def constraints {R : Type u} [CommRing R] (w : Witness R) (F : Type u := R) [Field F]
    [Algebra F R] : List R :=
  [ w.crumbs.foldl (fun acc x => 4 * acc + x) w.n0 - w.n8
  , w.crumbs.foldl (fun acc x => 2 * acc + cPoly x (F := F)) w.a0 - w.a8
  , w.crumbs.foldl (fun acc x => 2 * acc + dPoly x (F := F)) w.b0 - w.b8 ]
  ++ w.crumbs.map crumbPoly

/-- Push a carrier map `f : R → S` through a witness, cell by cell (the six accumulator cells
    and every crumb). The vehicle for the `Argument` naturality: an `F`-algebra hom commutes
    with the constraint list (see `constraints_map`). -/
def Witness.map {R S : Type*} (f : R → S) (w : Witness R) : Witness S where
  a0 := f w.a0
  b0 := f w.b0
  n0 := f w.n0
  a8 := f w.a8
  b8 := f w.b8
  n8 := f w.n8
  crumbs := w.crumbs.map f

/-- `f` commutes with the interpolating cubic `cPoly`: an `F`-algebra hom fixes the
    `algebraMap F _` coefficients (`AlgHom.commutes`) and preserves powers/products. -/
theorem cPoly_map {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) (x : R) : f (cPoly x (F := F)) = cPoly (f x) (F := F) := by
  simp only [cPoly, map_sub, map_add, map_mul, map_pow, AlgHom.commutes]

/-- `f` commutes with `dPoly` (`cPoly` plus an integer-coefficient tail `−x²+3x−1`). -/
theorem dPoly_map {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) (x : R) : f (dPoly x (F := F)) = dPoly (f x) (F := F) := by
  simp only [dPoly, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one, cPoly_map f]

/-- `f` commutes with the crumb-range polynomial `crumbPoly` (integer coefficients only). -/
theorem crumbPoly_map {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) (x : R) : f (crumbPoly x) = crumbPoly (f x) := by
  simp only [crumbPoly, map_mul, map_sub, map_ofNat, map_one]

/-- `f` distributes through the `n`-accumulator fold `n := 4·n + x` (induction on the crumbs,
    the shape of `foldl_table`; the base is `map f [] = []`, the step pushes `f` past one
    update via `map_add`/`map_mul`/`map_ofNat`). -/
theorem foldl_map_n {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) :
    ∀ (xs : List R) (init : R),
      f (xs.foldl (fun acc x => 4 * acc + x) init)
        = (xs.map f).foldl (fun acc x => 4 * acc + x) (f init)
  | [], _ => rfl
  | y :: ys, init => by
    simp only [List.foldl_cons, List.map_cons]
    rw [foldl_map_n f ys (4 * init + y), map_add, map_mul, map_ofNat]

/-- `f` distributes through the `a`-accumulator fold `a := 2·a + cPoly x`. -/
theorem foldl_map_c {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) :
    ∀ (xs : List R) (init : R),
      f (xs.foldl (fun acc x => 2 * acc + cPoly x (F := F)) init)
        = (xs.map f).foldl (fun acc x => 2 * acc + cPoly x (F := F)) (f init)
  | [], _ => rfl
  | y :: ys, init => by
    simp only [List.foldl_cons, List.map_cons]
    rw [foldl_map_c f ys (2 * init + cPoly y (F := F)), map_add, map_mul, map_ofNat, cPoly_map f]

/-- `f` distributes through the `b`-accumulator fold `b := 2·b + dPoly x`. -/
theorem foldl_map_d {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) :
    ∀ (xs : List R) (init : R),
      f (xs.foldl (fun acc x => 2 * acc + dPoly x (F := F)) init)
        = (xs.map f).foldl (fun acc x => 2 * acc + dPoly x (F := F)) (f init)
  | [], _ => rfl
  | y :: ys, init => by
    simp only [List.foldl_cons, List.map_cons]
    rw [foldl_map_d f ys (2 * init + dPoly y (F := F)), map_add, map_mul, map_ofNat, dPoly_map f]

/-- **Naturality.** An `F`-algebra hom `f : R →ₐ[F] S` commutes with the constraint list:
    mapping `f` over `constraints w` is `constraints (Witness.map f w)`. `f` commutes with
    `cPoly`/`dPoly` (it fixes the `algebraMap F _` coefficients and preserves powers/products)
    and with `crumbPoly`, and distributes through the accumulator folds by induction on the
    crumb list (the shape of `foldl_table`). This is what makes the gate an `Argument` instance. -/
theorem constraints_map {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) (w : Witness R) :
    (constraints (F := F) w).map f = constraints (F := F) (Witness.map f w) := by
  simp only [constraints, Witness.map, List.map_append, List.map_cons, List.map_nil, map_sub]
  rw [foldl_map_n f w.crumbs w.n0, foldl_map_c f w.crumbs w.a0, foldl_map_d f w.crumbs w.b0]
  congr 1
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun x _ => crumbPoly_map f x

/-- RELATIONAL spec: all constraint expressions vanish. -/
def Holds (w : Witness F) : Prop :=
  ∀ e ∈ constraints w, e = 0

instance [DecidableEq F] (w : Witness F) : Decidable (Holds w) := by
  unfold Holds
  infer_instance

/-- EXECUTABLE checker: every constraint expression evaluates to zero. -/
def ok [DecidableEq F] (w : Witness F) : Bool :=
  (constraints w).all (· == 0)

/-- Reflection: the checker faithfully decides the constraints. -/
theorem ok_iff [DecidableEq F] (w : Witness F) : ok w = true ↔ Holds w := by
  simp only [ok, Holds, List.all_eq_true, beq_iff_eq]

/-- `Holds` as the readable conjunction: the three folds close and every crumb is in
    range. -/
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
  (holds_iff _).mpr ⟨rfl, rfl, rfl, fun x hx => (crumb_iff x).mpr (hvalid x hx)⟩

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
  obtain ⟨hn, ha, hb, hc⟩ := (holds_iff w).mp h
  have hv : ∀ x ∈ w.crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 :=
    fun x hx => (crumb_iff x).mp (hc x hx)
  refine ⟨hv, hn, ?_, ?_⟩
  · rw [ha]; exact foldl_table w.crumbs w.a0 (fun x hx => cPoly_eq_cFunc h2 h3 (hv x hx))
  · rw [hb]; exact foldl_table w.crumbs w.b0 (fun x hx => dPoly_eq_dFunc h2 h3 (hv x hx))

end Kimchi.Gate.EndoScalar
