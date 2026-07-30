import Kimchi.Gate.EndoScalar

/-! # EndoScalar semantics

    The row runs Halo's Algorithm 2, with soundness and completeness in bare-table form; the
    multi-row chain composes rows into the effective scalar `a·λ + b`.

    Beyond the per-row development the file has two parts: `§ Supporting development` and
    `§ The effective scalar `a·λ + b``. -/

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

    The `a`/`b` constraints use the interpolating cubics; on valid crumbs they run
    the same fold with the bare `c_func`/`d_func` tables. -/

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

/-- `c_func` as the bare `(0,0,−1,1)` table. -/
private def cFunc (x : F) : F := if x = 2 then -1 else if x = 3 then 1 else 0

/-- `d_func` as the bare `(−1,1,0,0)` table. -/
private def dFunc (x : F) : F := if x = 0 then -1 else if x = 1 then 1 else 0

/-- On a valid crumb the interpolating cubic `cPoly` equals the bare table `cFunc`. -/
private theorem cPoly_eq_cFunc (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x : F}
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
private theorem dPoly_eq_dFunc (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x : F}
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

/-!
## Supporting development

The endo-scalar decomposition composes `Kimchi.Gate.EndoScalar` rows into the effective
scalar `a·λ + b`. A challenge is processed eight crumbs at a time, each row threading the
`(a, b, n)` accumulators; the result is the effective scalar `a·λ + b` together with the raw
register `n`, which the wrapper asserts equals the input challenge. This module collects the
definitions and lemmas on which the three headline theorems (`chain_toField`, `chain_complete`,
`endoScalar_unique`, in `Kimchi.Gate.EndoScalar`) rest. It mirrors the OCaml/PureScript
`to_field_checked'`, which runs `mapAccumM` over the row chunks.

### Multi-row composition

A challenge wider than one row's eight crumbs is laid out over several `EndoScalar` rows, each
row's output accumulators feeding the next. Every accumulator update is a `List.foldl`, so the
whole run is a single fold over the concatenated crumb stream (`List.foldl_append`). A single
`Witness` already folds a whole multi-row challenge; chaining rows adds nothing to the
arithmetic.

* `decomposeA`, `decomposeB`, `nReconstruct`, `toField` — the Algorithm-2 accumulators and the
  effective scalar, as field-valued folds over the crumb stream.
* `decomposeA_append`, `decomposeB_append`, `nReconstruct_append` — each fold resumes across a
  row boundary from the partial value of the earlier rows.
* `chainCrumbs`, `chain_decompose` — the concatenated crumbs of the first `m` rows, and the fact
  that a threaded run of `m + 1` rows computes the single base-4 decomposition of that stream.
* `chainCrumbs_length` — the stream of an `m`-row run of uniform width `c` has `c * m` crumbs; the
  width arithmetic behind the range check's `4 ^ (c · #rows)` budget.
* `chainBuild` — the honest threaded witness, built from the gate's `build`.
* `crumbsOf`, `crumbsOf_length`, `crumbsOf_valid`, `nReconstruct_crumbsOf` — the fixed-width base-4
  digit expansion of a natural, most significant crumb first, and the fact that it inverts the
  register fold modulo `4 ^ width`. This is the honest prover's crumb list for a *given* value, and
  what makes the range check non-vacuous (`range_complete`).

### Uniqueness under the no-wrap bound

The decomposition is a well-defined function of the challenge alone once a challenge determines
its crumbs. This holds because the crumbs are base-4 digits (each in `{0,1,2,3}`, by
`Gate.sound`) and the reconstruction does not wrap: the challenge's bit-width stays below the
field size, encoded as `4 ^ #crumbs ≤ p`. For the deployed 128-bit challenge this is
`4 ^ 64 = 2 ^ 128`, comfortably under the ≈ 2²⁵⁴ Pasta order. This is the EndoScalar analogue of
`varBaseMul`'s `5 m ≤ pastaFieldBits` no-wrap bound.

The positional-arithmetic kernel — `digit`, `valNat`, `euclid_split`, `valNat_inj` — is pure
base-4 number theory, independent of the gate, the curve, and the circuit folds. Each crumb is a
2-bit value in `{0,1,2,3}`; a crumb list reconstructs to a challenge base-4 (MSB-first), and that
decoding is injective once it stays below the field size.

* `digit`, `valNat` — the `ℕ` digit a crumb stands for and the `ℕ` shadow of `nReconstruct`.
* `digit_cast` — on a valid crumb the `ℕ` digit casts back to the field element.
* `valNat_cons`, `valNat_lt` — the Horner step of the base-4 value and its `< 4 ^ len` bound.
* `euclid_split` — Euclidean digit recovery: `high · M + low` with `low < M` determines both.
* `valNat_inj` — same-length valid crumb lists with equal value are equal.
* `nReconstruct_eq_valNat`, `nReconstruct_inj` — the bridge from the field register to its `ℕ`
  shadow, and the resulting injectivity of base-4 decoding under the no-wrap bound.
-/

namespace Kimchi.Gate.EndoScalar

open Kimchi.Gate.EndoScalar

variable {F : Type*} [Field F]

/-- The `a`-accumulator of the Algorithm-2 decomposition (`a := 2a + cPoly x`),
    from the canonical init `2`. -/
def decomposeA (crumbs : List F) : F := crumbs.foldl (fun a x => 2 * a + cPoly x) 2

/-- The `b`-accumulator (`b := 2b + dPoly x`), from init `2`. -/
def decomposeB (crumbs : List F) : F := crumbs.foldl (fun b x => 2 * b + dPoly x) 2

/-- The raw challenge reconstructed from its base-4 crumbs (`n := 4n + x`), the
    gate's `n` register. -/
private def nReconstruct (crumbs : List F) : F := crumbs.foldl (fun n x => 4 * n + x) 0

/-- The effective scalar the gate outputs: `a·λ + b` (`λ` the endomorphism
    eigenvalue). This is the pure `to_field` of the challenge. -/
def toField (crumbs : List F) (lam : F) : F :=
  decomposeA crumbs * lam + decomposeB crumbs

/-! ## Multi-row composition: threading rows is folding the concatenated crumbs.

    A challenge wider than one row's eight crumbs is laid out over several `EndoScalar` rows,
    each row's output accumulators feeding the next. Because every accumulator update is a
    `List.foldl`, the whole run is one fold over the concatenated crumbs. -/

/-- Resuming the `a`-fold across a row boundary: `decomposeA (xs ++ ys)` continues the
    single decomposition from `decomposeA xs`. -/
theorem decomposeA_append (xs ys : List F) :
    decomposeA (xs ++ ys) = ys.foldl (fun a x => 2 * a + cPoly x) (decomposeA xs) := by
  simp only [decomposeA, List.foldl_append]

/-- Resuming the `b`-fold across a row boundary from `decomposeB xs`. -/
theorem decomposeB_append (xs ys : List F) :
    decomposeB (xs ++ ys) = ys.foldl (fun b x => 2 * b + dPoly x) (decomposeB xs) := by
  simp only [decomposeB, List.foldl_append]

/-- Resuming the `n`-fold across a row boundary from `nReconstruct xs`. -/
private theorem nReconstruct_append (xs ys : List F) :
    nReconstruct (xs ++ ys) = ys.foldl (fun n x => 4 * n + x) (nReconstruct xs) := by
  simp only [nReconstruct, List.foldl_append]

/-- The crumbs of the first `m` rows of a run, concatenated MSB-first. -/
private def chainCrumbs (w : ℕ → Witness F) (m : ℕ) : List F :=
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
/-- The total crumb width of a uniform-width run: `m` rows of `c` crumbs each concatenate to
    `c * m` crumbs. This is what converts the stream-level budget `valNat_lt` into the deployed
    `4 ^ (c · #rows)` bound of the range check — at the deployed shape, eight rows of eight
    crumbs give `4 ^ 64 = 2 ^ 128`. -/
private theorem chainCrumbs_length (c : ℕ) (w : ℕ → Witness F) :
    ∀ m, (∀ i, i < m → (w i).crumbs.length = c) → (chainCrumbs w m).length = c * m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ k ih =>
    intro hc
    rw [chainCrumbs_succ, List.length_append, ih fun i hi => hc i (by omega),
      hc k (Nat.lt_succ_self k)]
    ring

/-- **Sequential-gate reconstruction.** A run of `m + 1` `EndoScalar` rows (indices `0..m`),
    each satisfying `Holds`, threaded so every row's output `(a8, b8, n8)` is the next row's
    input `(a0, b0, n0)` and the first starts at the canonical `(2, 2, 0)`, computes the single
    Algorithm-2 decomposition of its whole concatenated crumb stream — exactly as a one-row
    `Holds` over `chainCrumbs w (m + 1)` would. The multi-row layout adds nothing to the
    arithmetic, as for `varBaseMul`'s `gateLadder` over its rows. -/
private theorem chain_decompose (m : ℕ) (w : ℕ → Witness F)
    (hHolds : ∀ i, i ≤ m → Holds (w i))
    (ha0 : (w 0).a0 = 2) (hb0 : (w 0).b0 = 2) (hn0 : (w 0).n0 = 0)
    (haStep : ∀ i, i < m → (w (i + 1)).a0 = (w i).a8)
    (hbStep : ∀ i, i < m → (w (i + 1)).b0 = (w i).b8)
    (hnStep : ∀ i, i < m → (w (i + 1)).n0 = (w i).n8) :
    (w m).a8 = decomposeA (chainCrumbs w (m + 1))
      ∧ (w m).b8 = decomposeB (chainCrumbs w (m + 1))
      ∧ (w m).n8 = nReconstruct (chainCrumbs w (m + 1)) := by
  induction m with
  | zero =>
    obtain ⟨hn, ha, hb, _⟩ := (holds_iff _).mp (hHolds 0 (le_refl 0))
    rw [chainCrumbs_succ, chainCrumbs_zero, List.nil_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [ha, ha0, decomposeA]
    · rw [hb, hb0, decomposeB]
    · rw [hn, hn0, nReconstruct]
  | succ k ih =>
    obtain ⟨ihA, ihB, ihN⟩ := ih (fun i hi => hHolds i (by omega))
      (fun i hi => haStep i (by omega)) (fun i hi => hbStep i (by omega))
      (fun i hi => hnStep i (by omega))
    obtain ⟨hn, ha, hb, _⟩ := (holds_iff _).mp (hHolds (k + 1) (le_refl _))
    rw [chainCrumbs_succ]
    refine ⟨?_, ?_, ?_⟩
    · rw [ha, haStep k (Nat.lt_succ_self k), ihA, decomposeA_append]
    · rw [hb, hbStep k (Nat.lt_succ_self k), ihB, decomposeB_append]
    · rw [hn, hnStep k (Nat.lt_succ_self k), ihN, nReconstruct_append]

/-! ## Completeness: the honest prover fills a multi-row run.

    The gate's `complete` precondition is per-row crumb validity — independent of the threaded
    accumulators — so the honest builder threads with no global side-condition. Contrast the EC
    gates, whose ladder completeness must propagate non-exceptional points across rows; that is
    why `varBaseMul`'s circuit carries no free completeness while EndoScalar, being curve- and
    exception-free, does. -/

/-- The honest multi-row witness: thread the gate's `build` from the canonical `(2, 2, 0)`,
    each row started from the previous row's output accumulators. -/
private def chainBuild (rows : ℕ → List F) : ℕ → Witness F
  | 0 => build 2 2 0 (rows 0)
  | i + 1 =>
    let prev := chainBuild rows i
    build prev.a8 prev.b8 prev.n8 (rows (i + 1))

/-! ### The digit expansion

    `crumbsOf` runs the register fold backwards: it turns a natural into the crumb list that
    reconstructs to it, at a fixed width. It is what makes the range check `chain_range` say
    something — without it the bound would also hold of a circuit satisfiable at no value at all.
    It is pure `ℕ → List F` digit arithmetic, independent of the gate and of the row layout. -/

/-- The width-`c` base-4 expansion of a natural, most significant crumb first: peel `k % 4` and
    recurse on `k / 4`. High crumbs are padded with `0`, and whatever of `k` sits at or above
    `4 ^ c` is discarded. Mathlib's `Nat.digits` will not do here: it is least-significant-first
    and unpadded, so pinning the width back to `c` costs more than this peel. -/
private def crumbsOf : ℕ → ℕ → List F
  | 0, _ => []
  | c + 1, k => crumbsOf c (k / 4) ++ [((k % 4 : ℕ) : F)]

/-- `crumbsOf` has exactly the width asked for, which is what lets it fill whole
    `EndoScalar` rows. -/
private theorem crumbsOf_length (c k : ℕ) : (crumbsOf (F := F) c k).length = c := by
  induction c generalizing k with
  | zero => rfl
  | succ c ih =>
    rw [show crumbsOf (F := F) (c + 1) k = crumbsOf c (k / 4) ++ [((k % 4 : ℕ) : F)] from rfl,
      List.length_append, ih (k / 4)]
    rfl

/-- Every entry of `crumbsOf` is a 2-bit crumb, the tail one because `k % 4 < 4`. This is
    `complete`'s precondition, so the expansion feeds `build` directly. -/
private theorem crumbsOf_valid (c k : ℕ) :
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
    width budget `4 ^ c`, hence `k` itself below the budget. The Horner step is core's
    `Nat.mod_mul` at `a = 4`, `b = 4 ^ c`, carried into `F` by `nReconstruct_append`. -/
private theorem nReconstruct_crumbsOf (c k : ℕ) :
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

/-! ## Uniqueness of the decomposition under the bit-size/field-size bound.

    The reconstruction is pinned to the folds of the witness crumbs. The honest meaning —
    `challenge ↦ a·λ + b` is a well-defined function — needs that a challenge determines its
    crumbs. This holds because the crumbs are base-4 digits (each in `{0,1,2,3}`, by
    `Gate.sound`) and the reconstruction does not wrap: the challenge's bit-width stays below the
    field size, `4 ^ #crumbs ≤ p`. The positional-arithmetic kernel below — `digit`, `valNat`,
    `euclid_split`, `valNat_inj` — is pure base-4 number theory; the bridge `nReconstruct_eq_valNat`
    ties it to the field-valued register. -/

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

/-- Peeling the most significant crumb: `valNat (x :: xs) = digit x · 4^|xs| + valNat xs`. -/
private theorem valNat_cons (x : F) (xs : List F) :
    valNat (x :: xs) = digit x * 4 ^ xs.length + valNat xs := by
  -- folding from an arbitrary carry is that carry shifted up by `4^|ys|`, plus `valNat`
  have gen : ∀ (ys : List F) (acc : ℕ),
      ys.foldl (fun n x => 4 * n + digit x) acc = acc * 4 ^ ys.length + valNat ys := by
    intro ys
    induction ys with
    | nil => intro acc; simp [valNat]
    | cons y ys ihy =>
      intro acc
      have hv : valNat (y :: ys) = digit y * 4 ^ ys.length + valNat ys := by
        rw [show valNat (y :: ys)
            = ys.foldl (fun n x => 4 * n + digit x) (4 * 0 + digit y) from rfl, ihy]
        ring
      rw [List.foldl_cons, ihy (4 * acc + digit y), List.length_cons, pow_succ, hv]
      ring
  rw [show valNat (x :: xs)
      = xs.foldl (fun n x => 4 * n + digit x) (4 * 0 + digit x) from rfl, gen]
  ring

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
    recoverable from `high · M + low`. The base-4 digit-recovery step. -/
private theorem euclid_split {a b c d M : ℕ} (hb : b < M) (hd : d < M)
    (h : a * M + b = c * M + d) : a = c ∧ b = d := by
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le b) hb
  have ha : (a * M + b) / M = a := by
    rw [add_comm (a * M) b, Nat.add_mul_div_right b a hM, Nat.div_eq_of_lt hb, Nat.zero_add]
  have hc : (c * M + d) / M = c := by
    rw [add_comm (c * M) d, Nat.add_mul_div_right d c hM, Nat.div_eq_of_lt hd, Nat.zero_add]
  have hac : a = c := by rw [← ha, ← hc, h]
  subst hac; exact ⟨rfl, by omega⟩

/-- Nat-level base-4 uniqueness: valid same-length crumb lists with equal `valNat` are
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

/-- The field reconstruction is the cast of its `ℕ` shadow `valNat`, on valid crumbs. The
    bridge from the base-4 kernel to the circuit's field-valued register. -/
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

/-- **Base-4 digit recovery.** Same-length valid crumb lists whose reconstruction fits the
    field (`4 ^ len ≤ p`) and that reconstruct to the same challenge are equal — the
    decomposition a satisfying gate exposes is the *unique* one. -/
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

The endo-scalar decomposition composes `Kimchi.Gate.EndoScalar` rows into the effective scalar
`a·λ + b`. A challenge is processed eight crumbs at a time, each row threading the `(a, b, n)`
accumulators; the result is the effective scalar `a·λ + b` and the raw register `n`, which the
wrapper asserts equals the input challenge. The construction follows the OCaml/PureScript
`to_field_checked'`, which runs `mapAccumM` over the row chunks.

This module states the three headline theorems about the effective scalar, and — reading the same
gate for its *bound* rather than for its decomposition — the four theorems of the deployed 128-bit
range check. Their supporting development, the accumulator folds, the multi-row reconstruction, the
base-4 uniqueness kernel and the fixed-width digit expansion, lives in `§ Supporting development`
above.

* `chain_toField` — a satisfying run of `m + 1` sequential gate rows, threaded from the canonical
  init `(a, b, n) = (2, 2, 0)` (`varBaseMul`'s multi-row shape), outputs the effective scalar
  `a·λ + b` and the register reconstructing the whole challenge (a single row is the `m = 0` case).
* `chain_complete` — the completeness counterpart: for any rows of valid crumbs the honest prover
  threads the gate's `build` into a satisfying run, with no global side-condition, since the gate's
  completeness precondition is per-row.
* `endoScalar_unique` — self-contained soundness. Under the no-wrap bound `4 ^ #crumbs ≤ p` (the
  challenge's bit-size below the field size), the base-4 decomposition is unique, so the effective
  scalar `a·λ + b` is a well-defined function of the challenge alone, independent of the prover's
  witness.
* `chain_range`, `chain_range_128`, `chain_range_unique`, `range_complete` — the range check the
  gate *also* implements. A satisfying `m + 1`-row run of uniform width `c` pins its register to the
  cast of a natural below `4 ^ (c(m+1))`, uniquely so under the no-wrap bound, and every value in
  range is achieved. `§ The 128-bit range check` below carries the deployed caller and the four
  scope limits.
-/

namespace Kimchi.Gate.EndoScalar

open Kimchi.Gate.EndoScalar

variable {F : Type*} [Field F]

/-- The effective scalar of a multi-row run: `a·λ + b` over the whole challenge, with the
    register reconstructing the full concatenated crumb stream. The wrapper asserts that
    register equals the input challenge. -/
theorem chain_toField (lam : F) (m : ℕ) (w : ℕ → Witness F)
    (hHolds : ∀ i, i ≤ m → Holds (w i))
    (ha0 : (w 0).a0 = 2) (hb0 : (w 0).b0 = 2) (hn0 : (w 0).n0 = 0)
    (haStep : ∀ i, i < m → (w (i + 1)).a0 = (w i).a8)
    (hbStep : ∀ i, i < m → (w (i + 1)).b0 = (w i).b8)
    (hnStep : ∀ i, i < m → (w (i + 1)).n0 = (w i).n8) :
    (w m).a8 * lam + (w m).b8 = toField (chainCrumbs w (m + 1)) lam
      ∧ (w m).n8 = nReconstruct (chainCrumbs w (m + 1)) := by
  obtain ⟨hA, hB, hN⟩ := chain_decompose m w hHolds ha0 hb0 hn0 haStep hbStep hnStep
  exact ⟨by rw [hA, hB, toField], hN⟩

/-- **Completeness.** For any rows of valid crumbs, the threaded honest witness `chainBuild`
    satisfies the entire multi-row run — every row `Holds`, the first starts at `(2, 2, 0)`, the
    accumulators thread, and each row carries the given crumbs. Feeding this into `chain_toField`
    shows the honest prover computes the challenge's effective scalar. The threading and init are
    definitional; the only real input is `Gate.complete` per row. -/
theorem chain_complete (m : ℕ) (rows : ℕ → List F)
    (hvalid : ∀ i, i ≤ m → ∀ x ∈ rows i, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) :
    (∀ i, i ≤ m → Holds (chainBuild rows i))
      ∧ (chainBuild rows 0).a0 = 2 ∧ (chainBuild rows 0).b0 = 2 ∧ (chainBuild rows 0).n0 = 0
      ∧ (∀ i, i < m → (chainBuild rows (i + 1)).a0 = (chainBuild rows i).a8)
      ∧ (∀ i, i < m → (chainBuild rows (i + 1)).b0 = (chainBuild rows i).b8)
      ∧ (∀ i, i < m → (chainBuild rows (i + 1)).n0 = (chainBuild rows i).n8)
      ∧ (∀ i, i ≤ m → (chainBuild rows i).crumbs = rows i) := by
  refine ⟨?_, rfl, rfl, rfl, fun i _ => rfl, fun i _ => rfl, fun i _ => rfl, ?_⟩
  · intro i hi
    cases i with
    | zero => exact complete 2 2 0 (rows 0) (hvalid 0 hi)
    | succ k => exact complete _ _ _ (rows (k + 1)) (hvalid (k + 1) hi)
  · intro i _
    cases i with
    | zero => rfl
    | succ k => rfl

/-! ## The 128-bit range check

    `packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/RangeCheck.purs` range-checks a value to 128
    bits by `rangeCheck128 endo v = void $ EndoScalar.toField @8 v endo`: lay the value out over an
    eight-row `EndoScalar` chain and discard the effective scalar, keeping only the constraints. The
    soundness argument is that such a chain cannot represent a value `≥ 2¹²⁸`, and the theorems
    below are that argument. The width comes from `Circuit/Kimchi/EndoScalar.purs`'s
    `Mul 16 rows nBits`: `@8` is 8 rows × 8 crumbs = 64 crumbs = 128 bits. Gate origin
    `kimchi/src/circuits/polynomials/endomul_scalar.rs`.

    No new constraint is involved. The range check *is* the gate already modelled here, read for
    its bound instead of for its decomposition. Each crumb lies in `{0,1,2,3}` by `crumb_iff`, and
    the register is the base-4 Horner fold from `n₀ = 0`, so it is the image of a natural below
    `4 ^ #crumbs`.

    * `chain_range` — the bound, at the deployed multi-row shape.
    * `chain_range_128` — the deployed instance, eight rows of eight crumbs.
    * `chain_range_unique` — the sharp form: under the no-wrap bound the natural is unique.
    * `range_complete` — non-vacuity: every value in range is achieved.

    ### What the range check does not cover

    The four scope limits live here; the declarations below point at this list rather than
    restating it.

    1. `chain_range`'s bound is informative only when `4 ^ width ≤ p`. Over a field smaller than
       the budget every element is the image of some natural below the budget, so the statement is
       true but says nothing. `chain_range_unique` is the form that assumes the bound.
    2. Soundness is proved at the multi-row shape, completeness at a single witness carrying every
       crumb. The row split is arithmetically inert (`nReconstruct_append`, `chain_decompose`), but
       multi-row completeness needs a crumb-chunking argument that is not proved here.
    3. `lowest128Bits` is not modelled. These theorems are the primitive it rests on.
    4. `lowest128Bits'` witnesses `x = lo + 2¹²⁸ · hi` with both halves range-checked. Over a
       ≈2²⁵⁴ field that pair is not unique — two splits can be congruent mod `p` — so no
       uniqueness claim for the split follows from `chain_range_unique`. -/

/-- **The range check.** A satisfying `EndoScalar` run of `m + 1` rows, each carrying `c` crumbs
    and threaded from the canonical `(a, b, n) = (2, 2, 0)`, has an output register equal to the
    cast of a natural `< 4 ^ (c · (m + 1))`. Equivalently: nothing outside `[0, 4 ^ width)` has a
    satisfying witness, which is what `rangeCheck128` relies on.

    Hypotheses are `chain_toField`'s verbatim plus the uniform row width `hwidth`, so the chain
    theorems compose on one run; `h2` and `h3` are what let a crumb's base-4 digit be read back.
    The bound is informative only under `4 ^ width ≤ p` — see limit 1 of
    `§ What the range check does not cover`. -/
theorem chain_range (m c : ℕ) (w : ℕ → Witness F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hHolds : ∀ i, i ≤ m → Holds (w i))
    (ha0 : (w 0).a0 = 2) (hb0 : (w 0).b0 = 2) (hn0 : (w 0).n0 = 0)
    (haStep : ∀ i, i < m → (w (i + 1)).a0 = (w i).a8)
    (hbStep : ∀ i, i < m → (w (i + 1)).b0 = (w i).b8)
    (hnStep : ∀ i, i < m → (w (i + 1)).n0 = (w i).n8)
    (hwidth : ∀ i, i ≤ m → (w i).crumbs.length = c) :
    ∃ k : ℕ, k < 4 ^ (c * (m + 1)) ∧ (w m).n8 = (k : F) := by
  -- the `ℕ` shadow `valNat` needs `DecidableEq F`; obtaining it here keeps it off the statement
  classical
  obtain ⟨-, -, hN⟩ := chain_decompose m w hHolds ha0 hb0 hn0 haStep hbStep hnStep
  -- crumb validity of the whole stream, from `holds_iff` + `crumb_iff` (not `sound`, which
  -- would drag `DecidableEq F` in through its `cFunc`/`dFunc` tables)
  have hvalid : ∀ x ∈ chainCrumbs w (m + 1), x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
    intro x hxmem
    simp only [chainCrumbs, List.mem_flatMap, List.mem_range] at hxmem
    obtain ⟨i, hi, hxi⟩ := hxmem
    exact (crumb_iff x).mp (((holds_iff (w i)).mp (hHolds i (by omega))).2.2.2 x hxi)
  have hlen : (chainCrumbs w (m + 1)).length = c * (m + 1) :=
    chainCrumbs_length c w (m + 1) fun i hi => hwidth i (by omega)
  refine ⟨valNat (chainCrumbs w (m + 1)), ?_, ?_⟩
  · rw [← hlen]; exact valNat_lt _
  · rw [hN, nReconstruct_eq_valNat h2 h3 _ hvalid]

/-- `chain_range` at the shape the circuit emits: eight rows (`m = 7`) of eight crumbs (`c = 8`),
    where `4 ^ 64 = 2 ^ 128`. Same hypotheses, specialised. This is what `RangeCheck.purs`'s
    `rangeCheck128` rests on — a value with a satisfying eight-row `EndoScalar` witness is the cast
    of a natural below `2¹²⁸`. It says nothing about `lowest128Bits'`, its caller; see limits 3 and
    4 of `§ What the range check does not cover`. -/
theorem chain_range_128 (w : ℕ → Witness F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hHolds : ∀ i, i ≤ 7 → Holds (w i))
    (ha0 : (w 0).a0 = 2) (hb0 : (w 0).b0 = 2) (hn0 : (w 0).n0 = 0)
    (haStep : ∀ i, i < 7 → (w (i + 1)).a0 = (w i).a8)
    (hbStep : ∀ i, i < 7 → (w (i + 1)).b0 = (w i).b8)
    (hnStep : ∀ i, i < 7 → (w (i + 1)).n0 = (w i).n8)
    (hwidth : ∀ i, i ≤ 7 → (w i).crumbs.length = 8) :
    ∃ k : ℕ, k < 2 ^ 128 ∧ (w 7).n8 = (k : F) := by
  obtain ⟨k, hk, hn⟩ :=
    chain_range 7 8 w h2 h3 hHolds ha0 hb0 hn0 haStep hbStep hnStep hwidth
  refine ⟨k, ?_, hn⟩
  rw [show (2 : ℕ) ^ 128 = 4 ^ (8 * (7 + 1)) by rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]]
  exact hk

/-- **The sharp range check.** Under the no-wrap bound `4 ^ width ≤ p` the natural the register
    represents is unique, so the run pins the register to a *value* in `[0, 4 ^ width)` rather than
    to a residue class. This is the statement that rules out representing a value `≥ 2¹²⁸` by
    wrapping, and the counterpart of the PureScript `Compare nBits n LT` side-condition on
    `toField`. The bound `hp` is `endoScalar_unique`'s, and at the deployed width `4 ^ 64 = 2 ^ 128`
    sits far under the ≈2²⁵⁴ Pasta orders. Existence is `chain_range`; uniqueness is
    `CharP.natCast_injOn_Iio`, both candidates being below `p` by `hp`. -/
theorem chain_range_unique {p : ℕ} [CharP F p] (m c : ℕ) (w : ℕ → Witness F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hHolds : ∀ i, i ≤ m → Holds (w i))
    (ha0 : (w 0).a0 = 2) (hb0 : (w 0).b0 = 2) (hn0 : (w 0).n0 = 0)
    (haStep : ∀ i, i < m → (w (i + 1)).a0 = (w i).a8)
    (hbStep : ∀ i, i < m → (w (i + 1)).b0 = (w i).b8)
    (hnStep : ∀ i, i < m → (w (i + 1)).n0 = (w i).n8)
    (hwidth : ∀ i, i ≤ m → (w i).crumbs.length = c)
    (hp : (4 : ℕ) ^ (c * (m + 1)) ≤ p) :
    ∃! k : ℕ, k < 4 ^ (c * (m + 1)) ∧ (w m).n8 = (k : F) := by
  obtain ⟨k, hk, hn⟩ := chain_range m c w h2 h3 hHolds ha0 hb0 hn0 haStep hbStep hnStep hwidth
  refine ⟨k, ⟨hk, hn⟩, ?_⟩
  rintro j ⟨hj, hjn⟩
  exact CharP.natCast_injOn_Iio F p (Set.mem_Iio.mpr (lt_of_lt_of_le hj hp))
    (Set.mem_Iio.mpr (lt_of_lt_of_le hk hp)) (by rw [← hjn, ← hn])

/-- **Non-vacuity.** Every value in range is achieved: for `k < 4 ^ N` the honest prover fills a
    satisfying witness of width `N` whose register is `k`, from any input accumulators `(a0, b0)`.
    Without this, `chain_range`'s bound would also hold of a circuit satisfiable at no value at all;
    with it, the two say the accepted range is exactly `[0, 4 ^ N)`.

    The witness is `build` on the digit expansion `crumbsOf N k`, whose register fold at `n0 = 0`
    *is* `nReconstruct`, so the content is `nReconstruct_crumbsOf`. Proved at a single witness
    rather than the multi-row shape — see limit 2 of `§ What the range check does not cover`. -/
theorem range_complete (N k : ℕ) (hk : k < 4 ^ N) (a0 b0 : F) :
    ∃ w : Witness F, Holds w ∧ w.a0 = a0 ∧ w.b0 = b0 ∧ w.n0 = 0
      ∧ w.crumbs.length = N ∧ w.n8 = (k : F) := by
  refine ⟨build a0 b0 0 (crumbsOf N k), complete a0 b0 0 _ (crumbsOf_valid N k),
    rfl, rfl, rfl, crumbsOf_length N k, ?_⟩
  show nReconstruct (crumbsOf (F := F) N k) = (k : F)
  rw [nReconstruct_crumbsOf, Nat.mod_eq_of_lt hk]

variable [DecidableEq F]

/-- **Self-contained circuit soundness.** Two multi-row `EndoScalar` runs of the same crumb
    width that decode to the same challenge produce the *same* effective scalar `a·λ + b`.

    Combined with `chain_toField`, this is the honest statement that the gate realizes a
    well-defined function `challenge ↦ a·λ + b`: it depends only on the challenge, not on the
    prover's witness. The hypotheses are exactly `varBaseMul`'s shape — a chain over `m + 1`
    rows threaded from `(2, 2, 0)`, plus the no-wrap bound `4 ^ width ≤ p` tying the challenge's
    bit size to the field size. -/
theorem endoScalar_unique {p : ℕ} [CharP F p] (lam : F) (m : ℕ) (w w' : ℕ → Witness F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hHolds : ∀ i, i ≤ m → Holds (w i)) (hHolds' : ∀ i, i ≤ m → Holds (w' i))
    (ha0 : (w 0).a0 = 2) (hb0 : (w 0).b0 = 2) (hn0 : (w 0).n0 = 0)
    (ha0' : (w' 0).a0 = 2) (hb0' : (w' 0).b0 = 2) (hn0' : (w' 0).n0 = 0)
    (haStep : ∀ i, i < m → (w (i + 1)).a0 = (w i).a8)
    (hbStep : ∀ i, i < m → (w (i + 1)).b0 = (w i).b8)
    (hnStep : ∀ i, i < m → (w (i + 1)).n0 = (w i).n8)
    (haStep' : ∀ i, i < m → (w' (i + 1)).a0 = (w' i).a8)
    (hbStep' : ∀ i, i < m → (w' (i + 1)).b0 = (w' i).b8)
    (hnStep' : ∀ i, i < m → (w' (i + 1)).n0 = (w' i).n8)
    (hwidth : (chainCrumbs w (m + 1)).length = (chainCrumbs w' (m + 1)).length)
    (hbound : (4 : ℕ) ^ (chainCrumbs w (m + 1)).length ≤ p)
    (hchal : (w m).n8 = (w' m).n8) :
    (w m).a8 * lam + (w m).b8 = (w' m).a8 * lam + (w' m).b8 := by
  obtain ⟨hA, hB, hN⟩ := chain_decompose m w hHolds ha0 hb0 hn0 haStep hbStep hnStep
  obtain ⟨hA', hB', hN'⟩ := chain_decompose m w' hHolds' ha0' hb0' hn0' haStep' hbStep' hnStep'
  -- both runs' crumbs are valid 2-bit values, and reconstruct to the shared challenge
  have hvalid : ∀ (u : ℕ → Witness F), (∀ i, i ≤ m → Holds (u i)) →
      ∀ x ∈ chainCrumbs u (m + 1), x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
    intro u hu x hxmem
    simp only [chainCrumbs, List.mem_flatMap, List.mem_range] at hxmem
    obtain ⟨i, hi, hxi⟩ := hxmem
    exact (sound h2 h3 (u i) (hu i (by omega))).1 x hxi
  have hcrumbs : chainCrumbs w (m + 1) = chainCrumbs w' (m + 1) :=
    nReconstruct_inj (chainCrumbs w (m + 1)) (chainCrumbs w' (m + 1)) h2 h3
      (hvalid w hHolds) (hvalid w' hHolds') hwidth hbound (by rw [← hN, ← hN', hchal])
  rw [hA, hB, hA', hB', hcrumbs]

end Kimchi.Gate.EndoScalar
