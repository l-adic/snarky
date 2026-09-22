import Kimchi.Gate.EndoScalar
import Pasta.CompElliptic
import Poseidon.FqSponge

/-! # EndoScalar semantics

    An `EndoScalar` row runs Halo's Algorithm 2: it folds eight base-4 crumbs of a challenge
    into the accumulators `(a, b, n)`. This file composes rows into the effective scalar
    `a·λ + b`, and reads the same gate a second way, as a 128-bit range check. It transcribes
    the multi-row layout of `packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/EndoScalar.purs`
    and the range check of `packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/RangeCheck.purs`,
    which lays a value over an eight-row chain and discards the effective scalar.

    ## Main results

    * `complete`, `sound` — one row: the honest witness satisfies the gate, and a satisfying
      row runs Algorithm 2 with the bare tables `cFunc`/`dFunc`.
    * `chain_toField` — a satisfying run of `m + 1` rows threaded from `(2, 2, 0)` outputs the
      effective scalar of its whole crumb stream, and its register reconstructs the challenge.
    * `chain_complete` — for any rows of valid crumbs, the honest prover threads `build` into
      a satisfying run.
    * `endoScalar_unique` — under the no-wrap bound `4 ^ #crumbs ≤ p` the effective scalar
      depends only on the challenge, not on the witness.
    * `chain_range`, `chain_range_unique`, `chain_range_complete` — the range check: at a fixed
      row shape the accepted registers are exactly the casts of the naturals below
      `4 ^ (c(m+1))`. `chain_range_128` and `chain_range_complete_128` fix the deployed shape.
    * `fp_rangeCheck128_sound`, `fp_rangeCheck128_complete`, `fq_rangeCheck128_sound`,
      `fq_rangeCheck128_complete` — the deployed check at the two Pasta fields, every field
      hypothesis discharged; this is why `Pasta.CompElliptic` is imported.
    * `endoExpand_eq_toField` — the sponge's window recoding is `toField` at the challenge's
      canonical crumbs.

    ## Implementation notes

    The `a`/`b` constraints use interpolating cubics `cPoly`/`dPoly`. On valid crumbs they
    equal the bare tables, which needs `2, 3 ≠ 0`, true on both Pasta fields. Threading rows is
    folding the concatenated crumb stream (`chain_decompose`), so the multi-row layout adds
    nothing to the arithmetic. -/

namespace Kimchi.Gate.EndoScalar

variable {F : Type u} [Field F]

/-- **Completeness.** The witness the honest prover constructs (`build`) satisfies all the gate
    constraints, given that every crumb is a genuine 2-bit value — the folds close by
    construction, and the range constraint follows from `crumb_iff`. -/
theorem complete (a0 b0 n0 : F) (crumbs : List F)
    (hvalid : ∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) :
    Holds (build a0 b0 n0 crumbs) :=
  (holds_iff _).mpr ⟨rfl, rfl, rfl, fun x hx => (crumb_iff x).mpr (hvalid x hx)⟩

/-! ## The bare-table form of the folds.

    The `a`/`b` constraints use the interpolating cubics `cPoly`/`dPoly`; on valid crumbs
    they run the same fold as the bare tables `cFunc`/`dFunc`. -/

/-- Replacing the per-crumb function leaves the `2·acc + f x` fold unchanged when
    the two functions agree on every crumb. -/
private theorem foldl_table {φ ψ : F → F} :
    ∀ (xs : List F) (init : F), (∀ x ∈ xs, φ x = ψ x) →
      xs.foldl (fun acc x => 2 * acc + φ x) init
        = xs.foldl (fun acc x => 2 * acc + ψ x) init
  | [], _, _ => rfl
  | y :: ys, init, h => by
    simp only [List.foldl_cons]
    rw [h y (by simp), foldl_table ys _ (fun x hx => h x (by simp [hx]))]

variable [DecidableEq F]

/-- The bare `a`-table: `(0, 0, −1, 1)` at the crumbs `0, 1, 2, 3`, and `0` off them. -/
def cFunc (x : F) : F := if x = 2 then -1 else if x = 3 then 1 else 0

/-- The bare `b`-table: `(−1, 1, 0, 0)` at the crumbs `0, 1, 2, 3`, and `0` off them. -/
def dFunc (x : F) : F := if x = 0 then -1 else if x = 1 then 1 else 0

/-- The `a`-table's value at each crumb; the characteristic hypotheses separate the
four crumb values. -/
theorem cFunc_table (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    cFunc (0 : F) = 0 ∧ cFunc (1 : F) = 0 ∧ cFunc (2 : F) = -1 ∧ cFunc (3 : F) = 1 := by
  have e02 : (0 : F) ≠ 2 := fun h => h2 h.symm
  have e03 : (0 : F) ≠ 3 := fun h => h3 h.symm
  have e12 : (1 : F) ≠ 2 := fun h => (one_ne_zero : (1 : F) ≠ 0) (by linear_combination -h)
  have e13 : (1 : F) ≠ 3 := fun h => h2 (by linear_combination -h)
  have e32 : (3 : F) ≠ 2 := fun h => (one_ne_zero : (1 : F) ≠ 0) (by linear_combination h)
  exact ⟨by rw [cFunc, if_neg e02, if_neg e03], by rw [cFunc, if_neg e12, if_neg e13],
    by rw [cFunc, if_pos rfl], by rw [cFunc, if_neg e32, if_pos rfl]⟩

/-- The `b`-table's value at each crumb. -/
theorem dFunc_table (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    dFunc (0 : F) = -1 ∧ dFunc (1 : F) = 1 ∧ dFunc (2 : F) = 0 ∧ dFunc (3 : F) = 0 := by
  have e21 : (2 : F) ≠ 1 := fun h => (one_ne_zero : (1 : F) ≠ 0) (by linear_combination h)
  have e31 : (3 : F) ≠ 1 := fun h => h2 (by linear_combination h)
  exact ⟨by rw [dFunc, if_pos rfl],
    by rw [dFunc, if_neg ((one_ne_zero : (1 : F) ≠ 0)), if_pos rfl],
    by rw [dFunc, if_neg h2, if_neg e21], by rw [dFunc, if_neg h3, if_neg e31]⟩

/-- On a valid crumb the interpolating cubic `cPoly` equals the bare table `cFunc`. -/
private theorem cPoly_eq_cFunc (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x : F}
    (hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) : cPoly x = cFunc x := by
  obtain ⟨c0, c1, c2, c3⟩ := cPoly_table h2 h3
  obtain ⟨f0, f1, f2, f3⟩ := cFunc_table h2 h3
  rcases hx with rfl | rfl | rfl | rfl
  · rw [c0, f0]
  · rw [c1, f1]
  · rw [c2, f2]
  · rw [c3, f3]

/-- On a valid crumb the interpolating cubic `dPoly` equals the bare table `dFunc`. -/
private theorem dPoly_eq_dFunc (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x : F}
    (hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) : dPoly x = dFunc x := by
  obtain ⟨d0, d1, d2, d3⟩ := dPoly_table h2 h3
  obtain ⟨g0, g1, g2, g3⟩ := dFunc_table h2 h3
  rcases hx with rfl | rfl | rfl | rfl
  · rw [d0, g0]
  · rw [d1, g1]
  · rw [d2, g2]
  · rw [d3, g3]

/-- **Soundness.** A satisfying row runs Halo's Algorithm 2: the crumbs are valid 2-bit values,
    and the `a`/`b`/`n` accumulators are its folds, the `a`/`b` folds over the bare tables
    `cFunc`/`dFunc`. The cubics in `Holds` interpolate those tables, which needs `2, 3 ≠ 0`. -/
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

/-!
## Supporting development

The accumulator folds, their `ℤ`-shadows, the multi-row reconstruction, the fixed-width digit
expansion and the base-4 uniqueness kernel, on which the chain theorems below rest.
-/

namespace Kimchi.Gate.EndoScalar

open Kimchi.Gate.EndoScalar

variable {F : Type*} [Field F]

/-- The Algorithm-2 accumulator fold: double and add the step's contribution, from the
    canonical init `2`. `decomposeA`/`decomposeB` are its instances at `F` with `cPoly`/`dPoly`,
    and `decomposeAInt`/`decomposeBInt` at ℤ with the digit tables. -/
def decomposeFold {α R : Type*} [Semiring R] (step : α → R) (xs : List α) : R :=
  xs.foldl (fun a x => 2 * a + step x) 2

/-- The `a`-accumulator of the Algorithm-2 decomposition (`a := 2a + cPoly x`). -/
def decomposeA (crumbs : List F) : F := decomposeFold (fun x => cPoly x) crumbs

/-- The `b`-accumulator (`b := 2b + dPoly x`). -/
def decomposeB (crumbs : List F) : F := decomposeFold (fun x => dPoly x) crumbs

/-- The raw challenge reconstructed from its base-4 crumbs (`n := 4n + x`): the gate's `n`
    register. -/
def nReconstruct (crumbs : List F) : F := crumbs.foldl (fun n x => 4 * n + x) 0

/-- Zero crumbs decompose to the inits: the empty fold is its seed. -/
@[simp] theorem decomposeA_nil : decomposeA (F := F) [] = 2 := rfl

@[simp] theorem decomposeB_nil : decomposeB (F := F) [] = 2 := rfl

@[simp] theorem nReconstruct_nil : nReconstruct (F := F) [] = 0 := rfl

/-- The effective scalar the gate outputs: `a·λ + b`, with `λ` the endomorphism
    eigenvalue. -/
def toField (crumbs : List F) (lam : F) : F :=
  decomposeA crumbs * lam + decomposeB crumbs

/-! ## The ℤ-shadow of the decomposition

    `cPoly`/`dPoly` live in a field (their coefficients divide by 2 and 3), so the decompose
    folds cannot be read over ℤ directly. On genuine base-4 digits they are integer tables,
    and the folds have exact ℤ-shadows: `decomposeAInt`/`decomposeBInt`/`toIntZ` over the
    pre-cast digit list. The cast lemmas below say each field-side fold is the image of its
    shadow, so one integer value can be read in a second field. -/

/-- `cPoly`'s digit table `(0, 0, −1, 1)`, over ℤ. -/
def cInt : ℕ → ℤ
  | 2 => -1
  | 3 => 1
  | _ => 0

/-- `dPoly`'s digit table `(−1, 1, 0, 0)`, over ℤ. -/
def dInt : ℕ → ℤ
  | 0 => -1
  | 1 => 1
  | _ => 0

/-- The ℤ-shadow of `decomposeA`: the same fold over the pre-cast digits, with `cPoly`'s
    digit values as the integer table `cInt`. -/
def decomposeAInt (ds : List ℕ) : ℤ := decomposeFold cInt ds

/-- The ℤ-shadow of `decomposeB`. -/
def decomposeBInt (ds : List ℕ) : ℤ := decomposeFold dInt ds

/-- The ℤ-shadow of `toField`: the effective scalar as an integer. -/
def toIntZ (ds : List ℕ) (lam : ℤ) : ℤ := decomposeAInt ds * lam + decomposeBInt ds

/-- On a digit `< 4`, `cPoly` at the cast digit is the cast of its ℤ table. Needs `2, 3`
    invertible, like `cPoly_table`. -/
theorem cPoly_digit (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {d : ℕ} (hd : d < 4) :
    cPoly ((d : F)) = ((cInt d : ℤ) : F) := by
  obtain ⟨c0, c1, c2, c3⟩ := cPoly_table h2 h3
  interval_cases d <;> push_cast <;> simp_all [cInt]

/-- `dPoly`'s half of `cPoly_digit`. -/
theorem dPoly_digit (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {d : ℕ} (hd : d < 4) :
    dPoly ((d : F)) = ((dInt d : ℤ) : F) := by
  obtain ⟨d0, d1, d2, d3⟩ := dPoly_table h2 h3
  interval_cases d <;> push_cast <;> simp_all [dInt]

private theorem fold_digits
    {p : F → F} {pz : ℕ → ℤ} (hp : ∀ d : ℕ, d < 4 → p ((d : F)) = ((pz d : ℤ) : F))
    (ds : List ℕ) (h : ∀ d ∈ ds, d < 4) (z : ℤ) :
    (ds.map (Nat.cast : ℕ → F)).foldl (fun a x => 2 * a + p x) ((z : ℤ) : F)
      = ((ds.foldl (fun a d => 2 * a + pz d) z : ℤ) : F) := by
  induction ds generalizing z with
  | nil => rfl
  | cons d ds ih =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons,
      hp d (h d List.mem_cons_self),
      show 2 * ((z : ℤ) : F) + ((pz d : ℤ) : F) = (((2 * z + pz d : ℤ)) : F) from by
        push_cast; ring]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) _

/-- `decomposeA` over cast digits is the cast of `decomposeAInt`. -/
theorem decomposeA_digits (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (ds : List ℕ) (h : ∀ d ∈ ds, d < 4) :
    decomposeA (ds.map (Nat.cast : ℕ → F)) = ((decomposeAInt ds : ℤ) : F) := by
  have := fold_digits (p := fun x => cPoly x) (pz := cInt)
    (fun d hd => cPoly_digit h2 h3 hd) ds h 2
  simpa [decomposeA, decomposeAInt, decomposeFold] using this

/-- `decomposeB` over cast digits is the cast of `decomposeBInt`. -/
theorem decomposeB_digits (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (ds : List ℕ) (h : ∀ d ∈ ds, d < 4) :
    decomposeB (ds.map (Nat.cast : ℕ → F)) = ((decomposeBInt ds : ℤ) : F) := by
  have := fold_digits (p := fun x => dPoly x) (pz := dInt)
    (fun d hd => dPoly_digit h2 h3 hd) ds h 2
  simpa [decomposeB, decomposeBInt, decomposeFold] using this

/-- `toField` over cast digits at a cast eigenvalue is the cast of `toIntZ`: one integer
    scalar, read in any field with `2, 3` invertible. -/
theorem toField_digits (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (ds : List ℕ) (h : ∀ d ∈ ds, d < 4) (lam : ℤ) :
    toField (ds.map (Nat.cast : ℕ → F)) ((lam : ℤ) : F) = ((toIntZ ds lam : ℤ) : F) := by
  rw [toField, toIntZ, decomposeA_digits h2 h3 ds h, decomposeB_digits h2 h3 ds h]
  push_cast; ring

theorem cInt_abs_le (d : ℕ) : |cInt d| ≤ 1 := by
  unfold cInt; split <;> decide

theorem dInt_abs_le (d : ℕ) : |dInt d| ≤ 1 := by
  unfold dInt; split <;> decide

private theorem foldInt_bounds {cz : ℕ → ℤ} (hc : ∀ d, |cz d| ≤ 1) (ds : List ℕ) :
    ∀ z : ℤ, 1 ≤ z →
      2 ^ ds.length * z - (2 ^ ds.length - 1)
          ≤ ds.foldl (fun a d => 2 * a + cz d) z
        ∧ ds.foldl (fun a d => 2 * a + cz d) z
          ≤ 2 ^ ds.length * z + (2 ^ ds.length - 1) := by
  induction ds with
  | nil => intro z hz; simp
  | cons d ds ih =>
    intro z hz
    have hcd := hc d
    have habs : -1 ≤ cz d ∧ cz d ≤ 1 := abs_le.mp hcd
    have hz' : 1 ≤ 2 * z + cz d := by omega
    obtain ⟨hlo, hhi⟩ := ih (2 * z + cz d) hz'
    have hpow : (0 : ℤ) < 2 ^ ds.length := by positivity
    simp only [List.foldl_cons, List.length_cons, pow_succ]
    constructor
    · nlinarith [hlo, habs.1, hpow]
    · nlinarith [hhi, habs.2, hpow]

/-- The `a`-shadow's window: from the init `2`, the fold lands in `[2^n + 1, 3·2^n − 1]`,
    with `n` the digit count. -/
theorem decomposeAInt_bounds (ds : List ℕ) :
    2 ^ ds.length + 1 ≤ decomposeAInt ds ∧ decomposeAInt ds ≤ 3 * 2 ^ ds.length - 1 := by
  obtain ⟨hlo, hhi⟩ := foldInt_bounds cInt_abs_le ds 2 (by norm_num)
  unfold decomposeAInt decomposeFold
  constructor <;> omega

/-- `decomposeBInt`'s half of the window. -/
theorem decomposeBInt_bounds (ds : List ℕ) :
    2 ^ ds.length + 1 ≤ decomposeBInt ds ∧ decomposeBInt ds ≤ 3 * 2 ^ ds.length - 1 := by
  obtain ⟨hlo, hhi⟩ := foldInt_bounds dInt_abs_le ds 2 (by norm_num)
  unfold decomposeBInt decomposeFold
  constructor <;> omega

/-! ## Multi-row composition: threading rows is folding the concatenated crumbs

    A challenge wider than one row's eight crumbs is laid out over several `EndoScalar` rows,
    each row's output accumulators feeding the next. Every accumulator update is a
    `List.foldl`, so the whole run is one fold over the concatenated crumbs. -/

/-- Resuming the `a`-fold across a row boundary: `decomposeA (xs ++ ys)` continues the
    single decomposition from `decomposeA xs`. -/
theorem decomposeA_append (xs ys : List F) :
    decomposeA (xs ++ ys) = ys.foldl (fun a x => 2 * a + cPoly x) (decomposeA xs) := by
  simp only [decomposeA, decomposeFold, List.foldl_append]

/-- Resuming the `b`-fold across a row boundary from `decomposeB xs`. -/
theorem decomposeB_append (xs ys : List F) :
    decomposeB (xs ++ ys) = ys.foldl (fun b x => 2 * b + dPoly x) (decomposeB xs) := by
  simp only [decomposeB, decomposeFold, List.foldl_append]

/-- Resuming the `n`-fold across a row boundary from `nReconstruct xs`. -/
private theorem nReconstruct_append (xs ys : List F) :
    nReconstruct (xs ++ ys) = ys.foldl (fun n x => 4 * n + x) (nReconstruct xs) := by
  simp only [nReconstruct, List.foldl_append]

/-- The positional form of `nReconstruct_append`: the earlier rows contribute their
    reconstruction shifted up by one base-4 place per later crumb, as a separate summand, which
    is what chunking a value into rows needs. The field twin of `valNat_append`, stated here
    rather than transported through `nReconstruct_eq_valNat` because it then needs neither crumb
    validity nor `[DecidableEq F]`. -/
private theorem nReconstruct_append_pos (xs ys : List F) :
    nReconstruct (xs ++ ys) = nReconstruct xs * 4 ^ ys.length + nReconstruct ys := by
  induction ys generalizing xs with
  | nil => simp [nReconstruct]
  | cons y ys ih =>
    have hsnoc : nReconstruct (xs ++ [y]) = 4 * nReconstruct xs + y := by
      simp [nReconstruct, List.foldl_append]
    have hcons : nReconstruct (y :: ys) = y * 4 ^ ys.length + nReconstruct ys := by
      rw [← List.singleton_append, ih [y], show nReconstruct [y] = y by simp [nReconstruct]]
    calc nReconstruct (xs ++ y :: ys)
        = nReconstruct ((xs ++ [y]) ++ ys) := by rw [List.append_assoc, List.singleton_append]
      _ = nReconstruct (xs ++ [y]) * 4 ^ ys.length + nReconstruct ys := ih _
      _ = nReconstruct xs * 4 ^ (y :: ys).length + nReconstruct (y :: ys) := by
          rw [hsnoc, hcons, List.length_cons, pow_succ]; ring

/-- The crumbs of the first `m` rows of a run, concatenated MSB-first. -/
def chainCrumbs (w : ℕ → Witness F) (m : ℕ) : List F :=
  (List.range m).flatMap (fun i => (w i).crumbs)

omit [Field F] in
@[simp] private theorem chainCrumbs_zero (w : ℕ → Witness F) : chainCrumbs w 0 = [] := rfl

omit [Field F] in
/-- The crumbs through row `m` extend those through the first `m` rows by row `m`'s crumbs. -/
private theorem chainCrumbs_succ (w : ℕ → Witness F) (m : ℕ) :
    chainCrumbs w (m + 1) = chainCrumbs w m ++ (w m).crumbs := by
  simp only [chainCrumbs, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

omit [Field F] in
/-- A uniform-width run of `m` rows of `c` crumbs has `c * m` crumbs. This converts the
    stream-level budget `valNat_lt` into the range check's `4 ^ (c · #rows)` bound. -/
theorem chainCrumbs_length (c : ℕ) (w : ℕ → Witness F) :
    ∀ m, (∀ i, i < m → (w i).crumbs.length = c) → (chainCrumbs w m).length = c * m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ k ih =>
    intro hc
    rw [chainCrumbs_succ, List.length_append, ih fun i hi => hc i (by omega),
      hc k (Nat.lt_succ_self k)]
    ring

/-- A satisfying `m + 1`-row run: every row holds, the first opens at the canonical
    accumulators, and each row's outputs are the next row's inputs. -/
structure Chain (w : ℕ → Witness F) (m : ℕ) : Prop where
  /-- Every row of the run satisfies the gate. -/
  holds : ∀ i, i ≤ m → Holds (w i)
  /-- The `a` accumulator opens at `2`. -/
  a0 : (w 0).a0 = 2
  /-- The `b` accumulator opens at `2`. -/
  b0 : (w 0).b0 = 2
  /-- The register opens at `0`. -/
  n0 : (w 0).n0 = 0
  /-- Each row's `a` output is the next row's input. -/
  aStep : ∀ i, i < m → (w (i + 1)).a0 = (w i).a8
  /-- Each row's `b` output is the next row's input. -/
  bStep : ∀ i, i < m → (w (i + 1)).b0 = (w i).b8
  /-- Each row's register output is the next row's input. -/
  nStep : ∀ i, i < m → (w (i + 1)).n0 = (w i).n8

/-- A prefix of a chain is a chain — what feeds the induction in `chain_decompose`. -/
theorem Chain.mono {w : ℕ → Witness F} {m n : ℕ} (h : Chain w n) (hmn : m ≤ n) : Chain w m :=
  ⟨fun i hi => h.holds i (by omega), h.a0, h.b0, h.n0,
    fun i hi => h.aStep i (by omega), fun i hi => h.bStep i (by omega),
    fun i hi => h.nStep i (by omega)⟩

/-- **Sequential-gate reconstruction.** A `Chain` of `m + 1` rows computes the single
    Algorithm-2 decomposition of its concatenated crumb stream `chainCrumbs w (m + 1)`, exactly
    as one row over that stream would. -/
theorem chain_decompose : ∀ (m : ℕ) (w : ℕ → Witness F), Chain w m →
    (w m).a8 = decomposeA (chainCrumbs w (m + 1))
      ∧ (w m).b8 = decomposeB (chainCrumbs w (m + 1))
      ∧ (w m).n8 = nReconstruct (chainCrumbs w (m + 1))
  | 0, w, h => by
    obtain ⟨hn, ha, hb, _⟩ := (holds_iff _).mp (h.holds 0 (le_refl 0))
    rw [chainCrumbs_succ, chainCrumbs_zero, List.nil_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [ha, h.a0, decomposeA, decomposeFold]
    · rw [hb, h.b0, decomposeB, decomposeFold]
    · rw [hn, h.n0, nReconstruct]
  | k + 1, w, h => by
    obtain ⟨ihA, ihB, ihN⟩ := chain_decompose k w (h.mono (by omega))
    obtain ⟨hn, ha, hb, _⟩ := (holds_iff _).mp (h.holds (k + 1) (le_refl _))
    rw [chainCrumbs_succ]
    refine ⟨?_, ?_, ?_⟩
    · rw [ha, h.aStep k (Nat.lt_succ_self k), ihA, decomposeA_append]
    · rw [hb, h.bStep k (Nat.lt_succ_self k), ihB, decomposeB_append]
    · rw [hn, h.nStep k (Nat.lt_succ_self k), ihN, nReconstruct_append]

/-! ## A run given as a list

    A circuit builds its rows as a finite list, not as a function on `ℕ`. `Chain.ofList` is
    that caller's constructor, and the two identities below say what the chain theorems'
    conclusions read as there. The indexed form stays primary: a generated table (`chainBuild`)
    has no list to speak of. -/

/-- The chain a caller holding a finite run builds: every row holds, adjacent rows link, and
    the first row opens at the canonical accumulators. -/
theorem Chain.ofList (l : List (Witness F)) (hne : l ≠ [])
    (hholds : ∀ w ∈ l, Holds w)
    (hlink : l.IsChain fun a b => b.a0 = a.a8 ∧ b.b0 = a.b8 ∧ b.n0 = a.n8)
    (ha0 : (l.head hne).a0 = 2) (hb0 : (l.head hne).b0 = 2) (hn0 : (l.head hne).n0 = 0) :
    Chain (fun i => l.getD i (l.head hne)) (l.length - 1) := by
  have hlen : 0 < l.length := List.length_pos_iff.mpr hne
  have hget : ∀ i (hi : i < l.length), l.getD i (l.head hne) = l[i] :=
    fun i hi => List.getD_eq_getElem _ _ hi
  have hhead : l.head hne = l[0]'hlen := List.head_eq_getElem hne
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hget i (by omega)]
    exact hholds _ (List.getElem_mem _)
  · rw [hget 0 hlen, ← hhead]; exact ha0
  · rw [hget 0 hlen, ← hhead]; exact hb0
  · rw [hget 0 hlen, ← hhead]; exact hn0
  · rw [hget (i + 1) (by omega), hget i (by omega)]
    exact (hlink.getElem i (by omega)).1
  · rw [hget (i + 1) (by omega), hget i (by omega)]
    exact (hlink.getElem i (by omega)).2.1
  · rw [hget (i + 1) (by omega), hget i (by omega)]
    exact (hlink.getElem i (by omega)).2.2

/-- The crumb stream of a run given as a list: its rows' crumbs, concatenated. -/
theorem chainCrumbs_getD (l : List (Witness F)) (d : Witness F) :
    chainCrumbs (fun i => l.getD i d) l.length = l.flatMap (·.crumbs) := by
  show (List.range l.length).flatMap (fun i => (l.getD i d).crumbs) = _
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  refine List.ext_getElem (by simp) fun i _ h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h2)]

/-- The closing row of a run given as a list. -/
theorem getD_length_sub_one (l : List (Witness F)) (hne : l ≠ []) (d : Witness F) :
    l.getD (l.length - 1) d = l.getLast hne := by
  have hlen : 0 < l.length := List.length_pos_iff.mpr hne
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact (List.getLast_eq_getElem hne).symm

/-! ## Completeness: the honest prover fills a multi-row run

    The precondition of `complete` is per-row crumb validity, independent of the threaded
    accumulators, so the honest builder threads with no global side-condition. -/

/-- The honest multi-row witness: thread the gate's `build` from the canonical `(2, 2, 0)`,
    each row started from the previous row's output accumulators. -/
def chainBuild (rows : ℕ → List F) : ℕ → Witness F
  | 0 => build 2 2 0 (rows 0)
  | i + 1 =>
    let prev := chainBuild rows i
    build prev.a8 prev.b8 prev.n8 (rows (i + 1))

/-- The honest witness's crumb stream is the concatenation of the given rows: threading
    changes the accumulators, never the crumbs. -/
theorem chainCrumbs_chainBuild (rows : ℕ → List F) (m : ℕ) :
    chainCrumbs (chainBuild rows) m = (List.range m).flatMap rows :=
  List.flatMap_congr fun i _ => by cases i <;> rfl

/-! ### The digit expansion

    `crumbsOf` runs the register fold backwards: it turns a natural into the crumb list that
    reconstructs to it, at a fixed width. It is the honest prover's crumb list for a given
    value, which makes the range check non-vacuous (`range_complete`). -/

/-- The width-`c` base-4 expansion of a natural, most significant crumb first. High crumbs are
    padded with `0`, and whatever of `k` sits at or above `4 ^ c` is discarded. `Nat.digits` is
    least-significant-first and unpadded, so pinning its width back to `c` costs more. -/
def crumbsOf : ℕ → ℕ → List F
  | 0, _ => []
  | c + 1, k => crumbsOf c (k / 4) ++ [((k % 4 : ℕ) : F)]

@[simp] theorem crumbsOf_zero (k : ℕ) : crumbsOf (F := F) 0 k = [] := rfl

/-- `crumbsOf` has exactly the width asked for, which is what lets it fill whole
    `EndoScalar` rows. -/
theorem crumbsOf_length (c k : ℕ) : (crumbsOf (F := F) c k).length = c := by
  induction c generalizing k with
  | zero => rfl
  | succ c ih =>
    rw [show crumbsOf (F := F) (c + 1) k = crumbsOf c (k / 4) ++ [((k % 4 : ℕ) : F)] from rfl,
      List.length_append, ih (k / 4)]
    rfl

/-- The `ℕ` base-4 digit list of a challenge, MSB-first — `crumbsOf` before the cast. -/
def digitsOf : ℕ → ℕ → List ℕ
  | 0, _ => []
  | c + 1, k => digitsOf c (k / 4) ++ [k % 4]

theorem digitsOf_lt (c k : ℕ) : ∀ d ∈ digitsOf c k, d < 4 := by
  induction c generalizing k with
  | zero => simp [digitsOf]
  | succ c ih =>
    intro d hd
    rcases List.mem_append.mp hd with h | h
    · exact ih _ d h
    · simp only [List.mem_singleton] at h
      omega

theorem crumbsOf_eq_map (c k : ℕ) :
    crumbsOf (F := F) c k = (digitsOf c k).map (Nat.cast : ℕ → F) := by
  induction c generalizing k with
  | zero => rfl
  | succ c ih => rw [crumbsOf, digitsOf, List.map_append, ih]; rfl

theorem digitsOf_length (c k : ℕ) : (digitsOf c k).length = c := by
  induction c generalizing k with
  | zero => rfl
  | succ c ih => simp [digitsOf, ih]

/-- Every entry of `crumbsOf` is a 2-bit crumb, the tail one because `k % 4 < 4`. This is
    `complete`'s precondition, so the expansion feeds `build` directly. -/
theorem crumbsOf_valid (c k : ℕ) :
    ∀ x ∈ crumbsOf (F := F) c k, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  induction c generalizing k with
  | zero => intro x hx; simp only [crumbsOf, List.not_mem_nil] at hx
  | succ c ih =>
    intro x hx
    rw [show crumbsOf (F := F) (c + 1) k = crumbsOf c (k / 4) ++ [((k % 4 : ℕ) : F)] from rfl,
      List.mem_append, List.mem_singleton] at hx
    rcases hx with h | rfl
    · exact ih (k / 4) x h
    · have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
      rcases h4 with h | h | h | h <;> rw [h] <;> norm_num

/-- The expansion inverts the register fold: reconstructing `crumbsOf c k` recovers `k` modulo the
    width budget `4 ^ c`, hence `k` itself below the budget. -/
theorem nReconstruct_crumbsOf (c k : ℕ) :
    nReconstruct (crumbsOf (F := F) c k) = ((k % 4 ^ c : ℕ) : F) := by
  induction c generalizing k with
  | zero => simp only [crumbsOf, nReconstruct, pow_zero, Nat.mod_one, List.foldl_nil,
      Nat.cast_zero]
  | succ c ih =>
    rw [show crumbsOf (F := F) (c + 1) k = crumbsOf c (k / 4) ++ [((k % 4 : ℕ) : F)] from rfl,
      nReconstruct_append, ih (k / 4),
      show k % 4 ^ (c + 1) = k % 4 + 4 * (k / 4 % 4 ^ c) by
        rw [pow_succ, mul_comm (4 ^ c) 4, Nat.mod_mul]]
    simp only [List.foldl_cons, List.foldl_nil]
    push_cast
    ring

/-- **Row chunking.** Laying a natural out over `m + 1` rows of width `c`, most significant row
    first, with row `i` carrying the width-`c` expansion of `k / 4 ^ (c · (m − i))`,
    reconstructs to `k` modulo the run's budget `4 ^ (c(m+1))`. This is `nReconstruct_crumbsOf`
    at a row rather than a crumb, and what `chain_range_complete` rests on. -/
private theorem nReconstruct_rowsOf (c : ℕ) : ∀ (m k : ℕ),
    nReconstruct ((List.range (m + 1)).flatMap
        (fun i => crumbsOf (F := F) c (k / 4 ^ (c * (m - i)))))
      = ((k % 4 ^ (c * (m + 1)) : ℕ) : F) := by
  intro m
  induction m with
  | zero =>
    intro k
    simp only [Nat.zero_add, Nat.zero_sub, List.range_one, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Nat.mul_zero, pow_zero, Nat.div_one, Nat.mul_one]
    exact nReconstruct_crumbsOf c k
  | succ m ih =>
    intro k
    -- peel the least significant row; the rest is the same layout of `k / 4 ^ c`, and the
    -- halves recombine by `nReconstruct_append_pos`
    have hsplit : (List.range (m + 1 + 1)).flatMap
          (fun i => crumbsOf (F := F) c (k / 4 ^ (c * (m + 1 - i))))
        = (List.range (m + 1)).flatMap
            (fun i => crumbsOf (F := F) c (k / 4 ^ c / 4 ^ (c * (m - i))))
          ++ crumbsOf (F := F) c k := by
      rw [List.range_succ, List.flatMap_append]
      congr 1
      · refine List.flatMap_congr fun i hi => ?_
        have hle : i ≤ m := by have := List.mem_range.mp hi; omega
        rw [show c * (m + 1 - i) = c + c * (m - i) by
            rw [show m + 1 - i = (m - i) + 1 by omega]; ring,
          pow_add, Nat.div_div_eq_div_mul]
      · simp
    rw [hsplit, nReconstruct_append_pos, crumbsOf_length, ih (k / 4 ^ c),
      nReconstruct_crumbsOf,
      show k % 4 ^ (c * (m + 1 + 1)) = k % 4 ^ c + 4 ^ c * (k / 4 ^ c % 4 ^ (c * (m + 1))) by
        rw [show c * (m + 1 + 1) = c + c * (m + 1) by ring, pow_add, Nat.mod_mul]]
    push_cast
    ring

/-! ## Uniqueness of the decomposition under the no-wrap bound

    For `challenge ↦ a·λ + b` to be a well-defined function, a challenge must determine its
    crumbs. It does: the crumbs are base-4 digits (by `sound`), and the reconstruction does not
    wrap when `4 ^ #crumbs ≤ p`. At the deployed 64 crumbs that budget is `4 ^ 64 = 2 ^ 128`,
    far under the Pasta orders of about `2 ^ 254`. The kernel below (`digit`, `valNat`,
    `euclid_split`, `valNat_inj`) is pure base-4 number theory; `nReconstruct_eq_valNat` ties
    it to the field-valued register. -/

variable [DecidableEq F]

/-- The base-4 digit a crumb stands for (`0` off the valid set). -/
private def digit (x : F) : ℕ := if x = 1 then 1 else if x = 2 then 2 else if x = 3 then 3 else 0

/-- The natural-number value a crumb list reconstructs to, base-4 MSB-first — the `ℕ`
    shadow of `nReconstruct`, on which the no-wrap bound makes base-4 decoding injective. -/
private def valNat (xs : List F) : ℕ := xs.foldl (fun n x => 4 * n + digit x) 0

/-- Every digit is a base-4 digit. -/
private theorem digit_lt_four (x : F) : digit x < 4 := by
  unfold digit; split_ifs <;> omega

/-- On a valid crumb the digit casts back to the crumb. -/
private theorem digit_cast (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x : F}
    (hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) : ((digit x : ℕ) : F) = x := by
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  rcases hx with rfl | rfl | rfl | rfl
  · unfold digit
    rw [if_neg (fun h => h1 h.symm), if_neg (fun h => h2 h.symm),
      if_neg (fun h => h3 h.symm), Nat.cast_zero]
  · unfold digit; rw [if_pos rfl, Nat.cast_one]
  · unfold digit
    rw [if_neg (fun h => h1 (by linear_combination h)), if_pos rfl, Nat.cast_ofNat]
  · unfold digit
    rw [if_neg (fun h => h2 (by linear_combination h)),
      if_neg (fun h => h1 (by linear_combination h)), if_pos rfl, Nat.cast_ofNat]

/-- Splitting the base-4 value at a list boundary: the earlier crumbs contribute their value
    shifted up by one place per later crumb. The Horner step `valNat_cons` is its singleton
    case, and it is the `ℕ` shadow of `nReconstruct_append_pos`. -/
private theorem valNat_append (xs ys : List F) :
    valNat (xs ++ ys) = valNat xs * 4 ^ ys.length + valNat ys := by
  induction ys generalizing xs with
  | nil => simp [valNat]
  | cons y ys ih =>
    have hsnoc : valNat (xs ++ [y]) = 4 * valNat xs + digit y := by
      simp [valNat, List.foldl_append]
    have hcons : valNat (y :: ys) = digit y * 4 ^ ys.length + valNat ys := by
      rw [← List.singleton_append, ih [y], show valNat [y] = digit y by simp [valNat]]
    calc valNat (xs ++ y :: ys)
        = valNat ((xs ++ [y]) ++ ys) := by rw [List.append_assoc, List.singleton_append]
      _ = valNat (xs ++ [y]) * 4 ^ ys.length + valNat ys := ih _
      _ = valNat xs * 4 ^ (y :: ys).length + valNat (y :: ys) := by
          rw [hsnoc, hcons, List.length_cons, pow_succ]; ring

/-- Peeling the most significant crumb: `valNat (x :: xs) = digit x · 4^|xs| + valNat xs`. -/
private theorem valNat_cons (x : F) (xs : List F) :
    valNat (x :: xs) = digit x * 4 ^ xs.length + valNat xs := by
  rw [← List.singleton_append, valNat_append, show valNat [x] = digit x by simp [valNat]]

/-- The base-4 value of a length-`n` crumb list lies below `4 ^ n` — the no-wrap budget. -/
private theorem valNat_lt (xs : List F) : valNat xs < 4 ^ xs.length := by
  induction xs with
  | nil => simp [valNat]
  | cons x xs ih =>
    rw [valNat_cons, List.length_cons, pow_succ]
    have hx := digit_lt_four x
    nlinarith [ih, Nat.zero_le (valNat xs), Nat.zero_le (4 ^ xs.length)]

omit [Field F] [DecidableEq F] in
/-- Euclidean split at base `M`: a low part below `M` and a high digit are uniquely
    recoverable from `high · M + low`. -/
private theorem euclid_split {a b c d M : ℕ} (hb : b < M) (hd : d < M)
    (h : a * M + b = c * M + d) : a = c ∧ b = d := by
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le b) hb
  have ha : (a * M + b) / M = a := by
    rw [add_comm (a * M) b, Nat.add_mul_div_right b a hM, Nat.div_eq_of_lt hb, Nat.zero_add]
  have hc : (c * M + d) / M = c := by
    rw [add_comm (c * M) d, Nat.add_mul_div_right d c hM, Nat.div_eq_of_lt hd, Nat.zero_add]
  have hac : a = c := by rw [← ha, ← hc, h]
  subst hac; exact ⟨rfl, by omega⟩

/-- Base-4 uniqueness over `ℕ`: valid same-length crumb lists with equal `valNat` are
    equal. The crumbs being digits `< 4` makes each `valNat_cons` layer a `euclid_split`. -/
private theorem valNat_inj (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (xs ys : List F)
    (hx : ∀ x ∈ xs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3)
    (hy : ∀ x ∈ ys, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3)
    (hlen : xs.length = ys.length) (hnat : valNat xs = valNat ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => simp at hlen
  | cons x xs ih => cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [valNat_cons, valNat_cons, hlen] at hnat
      obtain ⟨hdig, htail⟩ := euclid_split (hlen ▸ valNat_lt xs) (valNat_lt ys) hnat
      have hxy : x = y := by
        rw [← digit_cast h2 h3 (hx x (by simp)), ← digit_cast h2 h3 (hy y (by simp)), hdig]
      rw [hxy, ih ys (fun z hz => hx z (by simp [hz])) (fun z hz => hy z (by simp [hz]))
        hlen htail]

/-- On valid crumbs the field reconstruction is the cast of its `ℕ` shadow `valNat`. -/
private theorem nReconstruct_eq_valNat (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (xs : List F)
    (hv : ∀ x ∈ xs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) :
    nReconstruct xs = ((valNat xs : ℕ) : F) := by
  have gen : ∀ (ys : List F) (acc : ℕ), (∀ x ∈ ys, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) →
      ys.foldl (fun n x => 4 * n + x) ((acc : ℕ) : F)
        = ((ys.foldl (fun n x => 4 * n + digit x) acc : ℕ) : F) := by
    intro ys
    induction ys with
    | nil => intro acc _; rfl
    | cons y ys ihy =>
      intro acc hvy
      simp only [List.foldl_cons]
      have hy : ((digit y : ℕ) : F) = y := digit_cast h2 h3 (hvy y (by simp))
      rw [show (4 * ((acc : ℕ) : F) + y) = (((4 * acc + digit y : ℕ) : F)) by push_cast; rw [hy]]
      exact ihy (4 * acc + digit y) (fun x hx => hvy x (by simp [hx]))
  have := gen xs 0 hv
  simpa [nReconstruct, valNat] using this


/-- The canonical expansion inverts the base-4 value: `crumbsOf` at a valid list's own
    width and value returns the list. -/
private theorem crumbsOf_valNat (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ∀ xs : List F, (∀ x ∈ xs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) →
      crumbsOf xs.length (valNat xs) = xs := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton l v ih =>
    intro hv
    have hvl : ∀ x ∈ l, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 :=
      fun x hx => hv x (List.mem_append_left _ hx)
    have hval : valNat (l ++ [v]) = 4 * valNat l + digit v := by
      simp [valNat, List.foldl_append]
    have hd : digit v < 4 := digit_lt_four v
    rw [List.length_append, List.length_singleton, hval,
      show crumbsOf (F := F) (l.length + 1) (4 * valNat l + digit v)
        = crumbsOf l.length ((4 * valNat l + digit v) / 4)
          ++ [(((4 * valNat l + digit v) % 4 : ℕ) : F)] from rfl,
      show (4 * valNat l + digit v) / 4 = valNat l by omega,
      show (4 * valNat l + digit v) % 4 = digit v by omega,
      ih hvl, digit_cast h2 h3 (hv v (by simp))]

/-- **Base-4 decoding is onto.** A valid crumb list is the canonical expansion `crumbsOf` of a
    natural below its width's budget, so a consumer holding the gate's crumbs may speak of the
    challenge they spell instead. -/
theorem eq_crumbsOf (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (xs : List F)
    (hv : ∀ x ∈ xs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) :
    ∃ n : ℕ, n < 4 ^ xs.length ∧ xs = crumbsOf xs.length n :=
  ⟨valNat xs, valNat_lt xs, (crumbsOf_valNat h2 h3 xs hv).symm⟩

/-- **Base-4 digit recovery.** Same-length valid crumb lists that fit the field
    (`4 ^ len ≤ p`) and reconstruct to the same challenge are equal. -/
private theorem nReconstruct_inj {p : ℕ} [CharP F p] (xs ys : List F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hx : ∀ x ∈ xs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3)
    (hy : ∀ x ∈ ys, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3)
    (hlen : xs.length = ys.length) (hbound : (4 : ℕ) ^ xs.length ≤ p)
    (heq : nReconstruct xs = nReconstruct ys) : xs = ys := by
  -- transport the field equality to `ℕ`, where the no-wrap bound makes decoding injective
  have hcast : ((valNat xs : ℕ) : F) = ((valNat ys : ℕ) : F) := by
    rw [← nReconstruct_eq_valNat h2 h3 xs hx, ← nReconstruct_eq_valNat h2 h3 ys hy]; exact heq
  have hxlt : valNat xs < p := lt_of_lt_of_le (valNat_lt xs) hbound
  have hylt : valNat ys < p := lt_of_lt_of_le (valNat_lt ys) (hlen ▸ hbound)
  have hnat : valNat xs = valNat ys :=
    CharP.natCast_injOn_Iio F p (Set.mem_Iio.mpr hxlt) (Set.mem_Iio.mpr hylt) hcast
  exact valNat_inj h2 h3 xs ys hx hy hlen hnat

end Kimchi.Gate.EndoScalar

/-!
## The effective scalar `a·λ + b`

The chain theorems about the effective scalar (`chain_toField`, `chain_complete`,
`endoScalar_unique`), and the range check the same gate implements.
-/

namespace Kimchi.Gate.EndoScalar

open Kimchi.Gate.EndoScalar

variable {F : Type*} [Field F]

/-- The effective scalar of a multi-row run: `a·λ + b` over the whole challenge, with the
    register reconstructing the full concatenated crumb stream. -/
theorem chain_toField (lam : F) (m : ℕ) (w : ℕ → Witness F) (h : Chain w m) :
    (w m).a8 * lam + (w m).b8 = toField (chainCrumbs w (m + 1)) lam
      ∧ (w m).n8 = nReconstruct (chainCrumbs w (m + 1)) := by
  obtain ⟨hA, hB, hN⟩ := chain_decompose m w h
  exact ⟨by rw [hA, hB, toField], hN⟩

/-- **Completeness.** For any rows of valid crumbs, the threaded honest witness `chainBuild` is a
    `Chain` whose rows carry the given crumbs. The threading and init are definitional; the only
    real input is `complete` per row. -/
theorem chain_complete (m : ℕ) (rows : ℕ → List F)
    (hvalid : ∀ i, i ≤ m → ∀ x ∈ rows i, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) :
    Chain (chainBuild rows) m ∧ (∀ i, i ≤ m → (chainBuild rows i).crumbs = rows i) := by
  refine ⟨⟨?_, rfl, rfl, rfl, fun i _ => rfl, fun i _ => rfl, fun i _ => rfl⟩, ?_⟩
  · intro i hi
    cases i with
    | zero => exact complete 2 2 0 (rows 0) (hvalid 0 hi)
    | succ k => exact complete _ _ _ (rows (k + 1)) (hvalid (k + 1) hi)
  · intro i _
    cases i with
    | zero => rfl
    | succ k => rfl

/-! ## The 128-bit range check

    The deployed range check lays a value over an eight-row `EndoScalar` chain and keeps only
    the constraints: eight rows of eight crumbs are 64 crumbs, 128 bits. No new constraint is
    involved. Each crumb lies in `{0,1,2,3}` by `crumb_iff`, and the register is the base-4
    Horner fold from `n₀ = 0`, so it is the image of a natural below `4 ^ #crumbs`.

    * `chain_range` — the bound, at the multi-row shape; `chain_range_128` at eight by eight.
    * `chain_range_unique` — under the no-wrap bound the natural is unique.
    * `range_complete` — every value in range is achieved by a single witness.
    * `chain_range_complete` — the exact converse of `chain_range` at the multi-row shape;
      `chain_range_complete_128` at eight by eight.

    `chain_range` and `chain_range_complete` compose on one run, and together they are an
    *iff*: at row shape `(m, c)` the accepted registers are exactly the casts of the naturals
    below `4 ^ (c(m+1))`. The bound direction needs `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, which let
    a crumb's base-4 digit be read back; the converse needs neither.

    ### What the range check does not cover

    1. `chain_range`'s bound is informative only when `4 ^ width ≤ p`. Over a smaller field
       every element is the image of some natural below the budget, so the statement is true
       but says nothing. `chain_range_unique` is the form that assumes the bound.
    2. Both the bound and its converse fix one width `c` for every row; a run of ragged row
       widths is not covered. The deployed circuit's rows are uniform by construction, so this
       is a gap in generality, not in coverage of the deployed shape.
    3. What the checked register is used for downstream is outside this file. The deployed
       split of a squeezed challenge into two range-checked halves is modelled in
       `Snarky.Kimchi.Circuit.RangeCheck`. -/

/-- **The range check.** A `Chain` of `m + 1` rows, each carrying `c` crumbs (`hwidth`), has an
    output register equal to the cast of a natural `< 4 ^ (c · (m + 1))`. The hypotheses are
    `chain_toField`'s plus `hwidth`, so the chain theorems compose on one run; `h2` and `h3` let
    a crumb's base-4 digit be read back. The bound is informative only under `4 ^ width ≤ p`
    (limit 1 of `§ What the range check does not cover`). -/
theorem chain_range (m c : ℕ) (w : ℕ → Witness F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : Chain w m) (hwidth : ∀ i, i ≤ m → (w i).crumbs.length = c) :
    ∃ k : ℕ, k < 4 ^ (c * (m + 1)) ∧ (w m).n8 = (k : F) := by
  -- the `ℕ` shadow `valNat` needs `DecidableEq F`; obtaining it here keeps it off the statement
  classical
  obtain ⟨-, -, hN⟩ := chain_decompose m w h
  -- crumb validity of the whole stream, from `holds_iff` + `crumb_iff` (not `sound`, which
  -- would drag `DecidableEq F` in through its `cFunc`/`dFunc` tables)
  have hvalid : ∀ x ∈ chainCrumbs w (m + 1), x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
    intro x hxmem
    simp only [chainCrumbs, List.mem_flatMap, List.mem_range] at hxmem
    obtain ⟨i, hi, hxi⟩ := hxmem
    exact (crumb_iff x).mp (((holds_iff (w i)).mp (h.holds i (by omega))).2.2.2 x hxi)
  have hlen : (chainCrumbs w (m + 1)).length = c * (m + 1) :=
    chainCrumbs_length c w (m + 1) fun i hi => hwidth i (by omega)
  refine ⟨valNat (chainCrumbs w (m + 1)), ?_, ?_⟩
  · rw [← hlen]; exact valNat_lt _
  · rw [hN, nReconstruct_eq_valNat h2 h3 _ hvalid]

/-- `chain_range` at the deployed shape, eight rows (`m = 7`) of eight crumbs (`c = 8`), where
    `4 ^ 64 = 2 ^ 128`: a value with a satisfying eight-row witness is the cast of a natural
    below `2¹²⁸`. -/
theorem chain_range_128 (w : ℕ → Witness F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : Chain w 7) (hwidth : ∀ i, i ≤ 7 → (w i).crumbs.length = 8) :
    ∃ k : ℕ, k < 2 ^ 128 ∧ (w 7).n8 = (k : F) := by
  obtain ⟨k, hk, hn⟩ := chain_range 7 8 w h2 h3 h hwidth
  refine ⟨k, ?_, hn⟩
  rw [show (2 : ℕ) ^ 128 = 4 ^ (8 * (7 + 1)) by rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]]
  exact hk

/-- **The sharp range check.** Under the no-wrap bound `hp : 4 ^ width ≤ p` the natural the
    register represents is unique, so the run pins the register to a value in `[0, 4 ^ width)`
    rather than to a residue class. This rules out representing a value `≥ 2¹²⁸` by wrapping.
    Existence is `chain_range`; uniqueness is `CharP.natCast_injOn_Iio`. -/
theorem chain_range_unique {p : ℕ} [CharP F p] (m c : ℕ) (w : ℕ → Witness F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h : Chain w m)
    (hwidth : ∀ i, i ≤ m → (w i).crumbs.length = c)
    (hp : (4 : ℕ) ^ (c * (m + 1)) ≤ p) :
    ∃! k : ℕ, k < 4 ^ (c * (m + 1)) ∧ (w m).n8 = (k : F) := by
  obtain ⟨k, hk, hn⟩ := chain_range m c w h2 h3 h hwidth
  refine ⟨k, ⟨hk, hn⟩, ?_⟩
  rintro j ⟨hj, hjn⟩
  exact CharP.natCast_injOn_Iio F p (Set.mem_Iio.mpr (lt_of_lt_of_le hj hp))
    (Set.mem_Iio.mpr (lt_of_lt_of_le hk hp)) (by rw [← hjn, ← hn])

/-- **Non-vacuity.** For `k < 4 ^ N` the honest prover fills a satisfying witness of width `N`
    whose register is `k`, from any input accumulators `a0`, `b0`. Without this, `chain_range`'s
    bound would also hold of a circuit satisfiable at no value at all. The witness is `build` on
    `crumbsOf N k`, so the content is `nReconstruct_crumbsOf`. -/
theorem range_complete (N k : ℕ) (hk : k < 4 ^ N) (a0 b0 : F) :
    ∃ w : Witness F, Holds w ∧ w.a0 = a0 ∧ w.b0 = b0 ∧ w.n0 = 0
      ∧ w.crumbs.length = N ∧ w.n8 = (k : F) := by
  refine ⟨build a0 b0 0 (crumbsOf N k), complete a0 b0 0 _ (crumbsOf_valid N k),
    rfl, rfl, rfl, crumbsOf_length N k, ?_⟩
  show nReconstruct (crumbsOf (F := F) N k) = (k : F)
  rw [nReconstruct_crumbsOf, Nat.mod_eq_of_lt hk]

/-- **Multi-row non-vacuity.** The exact converse of `chain_range`: for `k < 4 ^ (c(m+1))` the
    honest prover fills a `Chain` of `m + 1` rows of uniform width `c` whose output register is
    `k`. The conclusion is `chain_range`'s hypothesis list, so the two compose on one run. The
    rows are `chainBuild` over the row chunks of `k`, which reconstruct to `k` by
    `nReconstruct_rowsOf`; no field non-degeneracy is needed. -/
theorem chain_range_complete (m c k : ℕ) (hk : k < 4 ^ (c * (m + 1))) :
    ∃ w : ℕ → Witness F,
      Chain w m ∧ (∀ i, i ≤ m → (w i).crumbs.length = c) ∧ (w m).n8 = (k : F) := by
  obtain ⟨hchain, hcrumbs⟩ :=
    chain_complete (F := F) m (fun i => crumbsOf c (k / 4 ^ (c * (m - i))))
      (fun i _ => crumbsOf_valid c _)
  refine ⟨_, hchain, fun i hi => by rw [hcrumbs i hi]; exact crumbsOf_length c _, ?_⟩
  obtain ⟨-, -, hN⟩ := chain_decompose m _ hchain
  rw [hN, chainCrumbs_chainBuild, nReconstruct_rowsOf, Nat.mod_eq_of_lt hk]

/-- `chain_range_complete` at the deployed shape, eight rows (`m = 7`) of eight crumbs
    (`c = 8`): every natural below `2¹²⁸` is the register of a satisfying eight-row run. With
    `chain_range_128` it says an eight-row chain accepts a register iff it is the cast of a
    natural below `2¹²⁸`. -/
theorem chain_range_complete_128 (k : ℕ) (hk : k < 2 ^ 128) :
    ∃ w : ℕ → Witness F,
      Chain w 7 ∧ (∀ i, i ≤ 7 → (w i).crumbs.length = 8) ∧ (w 7).n8 = (k : F) := by
  refine chain_range_complete 7 8 k ?_
  rw [show (4 : ℕ) ^ (8 * (7 + 1)) = 2 ^ 128 by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]]
  exact hk

/-! ### The packaged 128-bit range check

    `Chain128` packages `chain_range_128`'s hypothesis list once; `Chain128.range` and
    `chain_range_complete_128` are the check's two directions, and
    `§ The range check at the deployed Pasta fields` closes their field hypotheses. -/

/-- The eight-row `EndoScalar` chain with output register `v`: a `Chain` of eight rows of
    eight crumbs each, whose last register is `v`. -/
def Chain128 (w : ℕ → Witness F) (v : F) : Prop :=
  Chain w 7 ∧ (∀ i, i ≤ 7 → (w i).crumbs.length = 8) ∧ (w 7).n8 = v

/-- A range-checked register is the cast of a natural below `2¹²⁸`: `chain_range_128` read
    through `Chain128`. -/
theorem Chain128.range {w : ℕ → Witness F} {v : F} (hw : Chain128 w v)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ∃ k : ℕ, k < 2 ^ 128 ∧ v = (k : F) := by
  obtain ⟨hchain, hwidth, hv⟩ := hw
  obtain ⟨k, hk, hn⟩ := chain_range_128 w h2 h3 hchain hwidth
  exact ⟨k, hk, by rw [← hv, hn]⟩

variable [DecidableEq F]

/-- **Self-contained circuit soundness.** Two `Chain`s of `m + 1` rows with the same crumb
    width that decode to the same challenge produce the same effective scalar `a·λ + b`, given
    the no-wrap bound `hbound : 4 ^ width ≤ p`. With `chain_toField`, the gate realizes a
    well-defined function `challenge ↦ a·λ + b`, independent of the prover's witness. -/
theorem endoScalar_unique {p : ℕ} [CharP F p] (lam : F) (m : ℕ) (w w' : ℕ → Witness F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : Chain w m) (h' : Chain w' m)
    (hwidth : (chainCrumbs w (m + 1)).length = (chainCrumbs w' (m + 1)).length)
    (hbound : (4 : ℕ) ^ (chainCrumbs w (m + 1)).length ≤ p)
    (hchal : (w m).n8 = (w' m).n8) :
    (w m).a8 * lam + (w m).b8 = (w' m).a8 * lam + (w' m).b8 := by
  obtain ⟨hA, hB, hN⟩ := chain_decompose m w h
  obtain ⟨hA', hB', hN'⟩ := chain_decompose m w' h'
  -- both runs' crumbs are valid 2-bit values, and reconstruct to the shared challenge
  have hvalid : ∀ (u : ℕ → Witness F), (∀ i, i ≤ m → Holds (u i)) →
      ∀ x ∈ chainCrumbs u (m + 1), x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
    intro u hu x hxmem
    simp only [chainCrumbs, List.mem_flatMap, List.mem_range] at hxmem
    obtain ⟨i, hi, hxi⟩ := hxmem
    exact (sound h2 h3 (u i) (hu i (by omega))).1 x hxi
  have hcrumbs : chainCrumbs w (m + 1) = chainCrumbs w' (m + 1) :=
    nReconstruct_inj (chainCrumbs w (m + 1)) (chainCrumbs w' (m + 1)) h2 h3
      (hvalid w h.holds) (hvalid w' h'.holds) hwidth hbound (by rw [← hN, ← hN', hchal])
  rw [hA, hB, hA', hB', hcrumbs]

/-! ## The range check at the deployed Pasta fields

    `Chain128.range` and `chain_range_complete_128` at the two fields the circuit runs over,
    with `(2 : F) ≠ 0` and `(3 : F) ≠ 0` discharged by `decide`, so nothing here carries a field
    hypothesis. `Fp` and `Fq` are CompElliptic's Pasta fields, reducible to `ZMod` of a
    concrete prime. -/

open CompElliptic.Fields.Pasta

/-- **The deployed range check is sound at `Fp`**, the Pallas base field: a satisfying
    eight-row chain pins its register to the cast of a natural below `2¹²⁸`. -/
theorem fp_rangeCheck128_sound {v : Fp} {w : ℕ → Witness Fp} (hw : Chain128 w v) :
    ∃ k : ℕ, k < 2 ^ 128 ∧ v = (k : Fp) :=
  hw.range (by decide) (by decide)

/-- **The deployed range check is complete at `Fp`**: every natural below `2¹²⁸` is the
    register of some satisfying chain. -/
theorem fp_rangeCheck128_complete (k : ℕ) (hk : k < 2 ^ 128) :
    ∃ w : ℕ → Witness Fp, Chain128 w (k : Fp) :=
  chain_range_complete_128 k hk

/-- **The deployed range check is sound at `Fq`**, the Pallas scalar field: a satisfying
    eight-row chain pins its register to the cast of a natural below `2¹²⁸`. -/
theorem fq_rangeCheck128_sound {v : Fq} {w : ℕ → Witness Fq} (hw : Chain128 w v) :
    ∃ k : ℕ, k < 2 ^ 128 ∧ v = (k : Fq) :=
  hw.range (by decide) (by decide)

/-- **The deployed range check is complete at `Fq`**: every natural below `2¹²⁸` is the
    register of some satisfying chain. -/
theorem fq_rangeCheck128_complete (k : ℕ) (hk : k < 2 ^ 128) :
    ∃ w : ℕ → Witness Fq, Chain128 w (k : Fq) :=
  chain_range_complete_128 k hk

/-! ## The wire recoding is the gate recoding

`FqSponge.endoExpand` folds over a prechallenge's 64 two-bit windows; the gate
recodes the same challenge from its base-4 crumbs. The window at position `i` is the
crumb `crumbsOf` places there, so the folds agree (`endoExpand_eq_toField`). -/

/-- The window fold of `endoExpand` over `c` windows is the paired decompose fold over
    the challenge's `c` crumbs. -/
private theorem endoExpand_fold (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ∀ (c k : ℕ) (ab : F × F),
      (List.range c).reverse.foldl
        (fun (ab : F × F) i =>
          let (a, b) := (2 * ab.1, 2 * ab.2)
          let s : F := if k.testBit (2 * i) then 1 else -1
          if k.testBit (2 * i + 1) then (a + s, b) else (a, b + s))
        ab
      = ((crumbsOf c k).foldl (fun a x => 2 * a + cPoly x) ab.1,
         (crumbsOf c k).foldl (fun b x => 2 * b + dPoly x) ab.2)
  | 0, k, ab => rfl
  | c + 1, k, ab => by
    have hshift : (fun (ab : F × F) i =>
        let (a, b) := (2 * ab.1, 2 * ab.2)
        let s : F := if k.testBit (2 * Nat.succ i) then 1 else -1
        if k.testBit (2 * Nat.succ i + 1) then (a + s, b) else (a, b + s))
        = (fun (ab : F × F) i =>
        let (a, b) := (2 * ab.1, 2 * ab.2)
        let s : F := if (k / 4).testBit (2 * i) then 1 else -1
        if (k / 4).testBit (2 * i + 1) then (a + s, b) else (a, b + s)) := by
      have hdiv : k / 4 = k >>> 2 := by rw [Nat.shiftRight_eq_div_pow]
      funext ab i
      have e0 : k.testBit (2 * Nat.succ i) = (k / 4).testBit (2 * i) := by
        rw [hdiv, Nat.testBit_shiftRight]
        congr 1
        omega
      have e1 : k.testBit (2 * Nat.succ i + 1) = (k / 4).testBit (2 * i + 1) := by
        rw [hdiv, Nat.testBit_shiftRight]
        congr 1
        omega
      rw [e0, e1]
    have hb0 : k.testBit 0 = decide (k % 4 % 2 = 1) := by
      rw [Nat.testBit_zero]
      simp only [decide_eq_decide]
      omega
    have hb1 : k.testBit 1 = decide (k % 4 / 2 = 1) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, Nat.testBit_add_one, Nat.testBit_zero]
      simp only [decide_eq_decide]
      omega
    rw [List.range_succ_eq_map, List.reverse_cons, ← List.map_reverse,
      List.foldl_append, List.foldl_map, hshift, endoExpand_fold h2 h3 c (k / 4) ab,
      show crumbsOf (F := F) (c + 1) k = crumbsOf c (k / 4) ++ [((k % 4 : ℕ) : F)]
        from rfl,
      List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have hm4 : k % 4 < 4 := by omega
    have hc := cPoly_digit h2 h3 hm4
    have hd := dPoly_digit h2 h3 hm4
    rw [hb0, hb1, hc, hd]
    have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases h4 with h | h | h | h <;>
      · rw [h]
        norm_num [cInt, dInt]

/-- The ℤ-shadow of the sponge's endo expansion: the effective scalar of a 128-bit
    prechallenge before any modulus, `a·λ + b` over its sixty-four base-4 digits. An integer,
    because at Pasta the field the multiplier is read in is not the field its crumbs live in. -/
def endoExpandZ (lam : ℤ) (chal : ℕ) : ℤ := toIntZ (digitsOf 64 chal) lam

/-- `endoExpand` at a challenge is `toField` at its canonical crumb list — the two
    folds are one recoding. -/
theorem endoExpand_eq_toField (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (lam : F) (n : ℕ) :
    Poseidon.FqSponge.endoExpand lam n = toField (crumbsOf 64 n) lam := by
  unfold Poseidon.FqSponge.endoExpand
  rw [endoExpand_fold h2 h3 64 n (2, 2)]
  rfl

/-- The shadow casts to the expansion: in any field where the digit tables are honest,
    `endoExpandZ`'s image is `endoExpand` at the cast eigenvalue. -/
theorem endoExpandZ_cast (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (lam : ℤ) (chal : ℕ) :
    ((endoExpandZ lam chal : ℤ) : F)
      = Poseidon.FqSponge.endoExpand ((lam : ℤ) : F) chal := by
  rw [endoExpand_eq_toField h2 h3, crumbsOf_eq_map,
    toField_digits h2 h3 _ (digitsOf_lt 64 _) lam, endoExpandZ]

end Kimchi.Gate.EndoScalar
