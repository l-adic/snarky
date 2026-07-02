import Kimchi.Gate.EndoScalar

/-!
# The `EndoScalar` circuit: supporting development

The endo-scalar decomposition composes `Kimchi.Gate.EndoScalar` rows into the effective
scalar `a·λ + b`. A challenge is processed eight crumbs at a time, each row threading the
`(a, b, n)` accumulators; the result is the effective scalar `a·λ + b` together with the raw
register `n`, which the wrapper asserts equals the input challenge. This module collects the
definitions and lemmas on which the three headline theorems (`chain_toField`, `chain_complete`,
`endoScalar_unique`, in `Kimchi.Circuit.EndoScalar`) rest. It mirrors the OCaml/PureScript
`to_field_checked'`, which runs `mapAccumM` over the row chunks.

## Multi-row composition

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
* `chainBuild` — the honest threaded witness, built from the gate's `build`.

## Uniqueness under the no-wrap bound

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

namespace Kimchi.Circuit.EndoScalar

open Kimchi.Gate.EndoScalar

variable {F : Type*} [Field F]

/-- The `a`-accumulator of the Algorithm-2 decomposition (`a := 2a + cPoly x`),
    from the canonical init `2`. -/
def decomposeA (crumbs : List F) : F := crumbs.foldl (fun a x => 2 * a + cPoly x) 2

/-- The `b`-accumulator (`b := 2b + dPoly x`), from init `2`. -/
def decomposeB (crumbs : List F) : F := crumbs.foldl (fun b x => 2 * b + dPoly x) 2

/-- The raw challenge reconstructed from its base-4 crumbs (`n := 4n + x`), the
    gate's `n` register. -/
def nReconstruct (crumbs : List F) : F := crumbs.foldl (fun n x => 4 * n + x) 0

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
theorem nReconstruct_append (xs ys : List F) :
    nReconstruct (xs ++ ys) = ys.foldl (fun n x => 4 * n + x) (nReconstruct xs) := by
  simp only [nReconstruct, List.foldl_append]

/-- The crumbs of the first `m` rows of a run, concatenated MSB-first. -/
def chainCrumbs (w : ℕ → Witness F) (m : ℕ) : List F :=
  (List.range m).flatMap (fun i => (w i).crumbs)

omit [Field F] in
@[simp] theorem chainCrumbs_zero (w : ℕ → Witness F) : chainCrumbs w 0 = [] := rfl

omit [Field F] in
/-- The crumbs through row `m` extend those through the first `m` rows by row `m`'s crumbs. -/
theorem chainCrumbs_succ (w : ℕ → Witness F) (m : ℕ) :
    chainCrumbs w (m + 1) = chainCrumbs w m ++ (w m).crumbs := by
  simp only [chainCrumbs, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

/-- **Sequential-gate reconstruction.** A run of `m + 1` `EndoScalar` rows (indices `0..m`),
    each satisfying `Holds`, threaded so every row's output `(a8, b8, n8)` is the next row's
    input `(a0, b0, n0)` and the first starts at the canonical `(2, 2, 0)`, computes the single
    Algorithm-2 decomposition of its whole concatenated crumb stream — exactly as a one-row
    `Holds` over `chainCrumbs w (m + 1)` would. The multi-row layout adds nothing to the
    arithmetic, as for `varBaseMul`'s `gateLadder` over its rows. -/
theorem chain_decompose (m : ℕ) (w : ℕ → Witness F)
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
def chainBuild (rows : ℕ → List F) : ℕ → Witness F
  | 0 => build 2 2 0 (rows 0)
  | i + 1 =>
    let prev := chainBuild rows i
    build prev.a8 prev.b8 prev.n8 (rows (i + 1))

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
def digit (x : F) : ℕ := if x = 1 then 1 else if x = 2 then 2 else if x = 3 then 3 else 0

/-- The natural-number value a crumb list reconstructs to, base-4 MSB-first — the `ℕ`
    shadow of `nReconstruct`, on which the no-wrap bound makes base-4 decoding injective. -/
def valNat (xs : List F) : ℕ := xs.foldl (fun n x => 4 * n + digit x) 0

/-- Every digit is a base-4 digit. -/
theorem digit_lt_four (x : F) : digit x < 4 := by
  unfold digit; split_ifs <;> omega

/-- On a valid crumb the digit casts back to the crumb. -/
theorem digit_cast (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {x : F}
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
theorem valNat_cons (x : F) (xs : List F) :
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
theorem valNat_lt (xs : List F) : valNat xs < 4 ^ xs.length := by
  induction xs with
  | nil => simp [valNat]
  | cons x xs ih =>
    rw [valNat_cons, List.length_cons, pow_succ]
    have hx := digit_lt_four x
    nlinarith [ih, Nat.zero_le (valNat xs), Nat.zero_le (4 ^ xs.length)]

omit [Field F] [DecidableEq F] in
/-- Euclidean split at base `M`: a low part below `M` and a high digit are uniquely
    recoverable from `high · M + low`. The base-4 digit-recovery step. -/
theorem euclid_split {a b c d M : ℕ} (hb : b < M) (hd : d < M)
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
theorem valNat_inj (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (xs ys : List F)
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
theorem nReconstruct_eq_valNat (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (xs : List F)
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
theorem nReconstruct_inj {p : ℕ} [CharP F p] (xs ys : List F)
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

end Kimchi.Circuit.EndoScalar
