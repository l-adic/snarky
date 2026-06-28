import Kimchi.Gate.EndoScalar
import Kimchi.Circuit.EndoScalar.Base4

/-!
# The `EndoScalar` circuit: the effective scalar `a·λ + b`

Composition of `Kimchi.Gate.EndoScalar` rows into the full endo-scalar
decomposition. A challenge is processed 8 crumbs at a time, each row threading the
`(a,b,n)` accumulators; the result is the effective scalar `a·λ + b` and the raw
register `n`, which the wrapper asserts equals the input challenge.

Because a row's crumb list is arbitrary-length, a single `Witness` already folds
the whole multi-row challenge; chaining rows is just folding over the concatenated
crumb list (`List.foldl_append`).

## Main results

* `chain_decompose` / `chain_toField` — a satisfying *run* of `m + 1` sequential gate rows
  threaded from the canonical init `(a,b,n) = (2,2,0)` (`varBaseMul`'s multi-row shape) is
  one fold over the concatenated crumbs: it outputs the effective scalar `a·λ + b` and the
  register `nReconstruct` of the whole challenge (a single row is the `m = 0` case).
* `chain_complete` — the completeness counterpart: for any valid crumb-rows the honest prover
  threads the gate's `build` into a satisfying run (no global side-condition, since the gate's
  completeness precondition is per-row).
* `nReconstruct_inj` / `endoScalar_unique` — the self-contained soundness. Under the
  no-wrap bound `4 ^ #crumbs ≤ p` (the challenge's bit size below the field size), the
  base-4 decomposition is unique, so the effective scalar `a·λ + b` is a well-defined
  function of the challenge alone — not of the prover's witness.
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

/-! ## Multi-row composition: threading rows = folding the concatenated crumbs.

    A challenge wider than one row's 8 crumbs is laid out over several `EndoScalar`
    rows, each row's output accumulators feeding the next (the OCaml/PureScript
    `to_field_checked'` runs `mapAccumM` over `rows` chunks). Because every fold is a
    `List.foldl`, the whole run is one fold over the concatenated crumbs. -/

/-- Resuming the `a`-fold across a row boundary: `decomposeA (xs ++ ys)` continues the
    single decomposition from `decomposeA xs`. -/
theorem decomposeA_append (xs ys : List F) :
    decomposeA (xs ++ ys) = ys.foldl (fun a x => 2 * a + cPoly x) (decomposeA xs) := by
  simp only [decomposeA, List.foldl_append]

theorem decomposeB_append (xs ys : List F) :
    decomposeB (xs ++ ys) = ys.foldl (fun b x => 2 * b + dPoly x) (decomposeB xs) := by
  simp only [decomposeB, List.foldl_append]

theorem nReconstruct_append (xs ys : List F) :
    nReconstruct (xs ++ ys) = ys.foldl (fun n x => 4 * n + x) (nReconstruct xs) := by
  simp only [nReconstruct, List.foldl_append]

/-- The crumbs of the first `m` rows of a run, concatenated MSB-first. -/
def chainCrumbs (w : ℕ → Witness F) (m : ℕ) : List F :=
  (List.range m).flatMap (fun i => (w i).crumbs)

omit [Field F] in
@[simp] theorem chainCrumbs_zero (w : ℕ → Witness F) : chainCrumbs w 0 = [] := rfl

omit [Field F] in
theorem chainCrumbs_succ (w : ℕ → Witness F) (m : ℕ) :
    chainCrumbs w (m + 1) = chainCrumbs w m ++ (w m).crumbs := by
  simp only [chainCrumbs, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

/-- **Sequential-gate reconstruction.** A run of `m + 1` `EndoScalar` rows (indices `0..m`),
    each satisfying `Holds`, threaded so every row's output `(a8,b8,n8)` is the next row's
    input `(a0,b0,n0)` and the first starts at the canonical `(2,2,0)`, computes the single
    Algorithm-2 decomposition of its whole concatenated crumb stream — exactly as a one-row
    `Holds` over `chainCrumbs w (m+1)` would. (The multi-row layout adds nothing to the math;
    cf. `varBaseMul`'s `gateLadder` over its rows.) -/
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
    obtain ⟨hn, ha, hb, _⟩ := hHolds 0 (le_refl 0)
    rw [chainCrumbs_succ, chainCrumbs_zero, List.nil_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [ha, ha0, decomposeA]
    · rw [hb, hb0, decomposeB]
    · rw [hn, hn0, nReconstruct]
  | succ k ih =>
    obtain ⟨ihA, ihB, ihN⟩ := ih (fun i hi => hHolds i (by omega))
      (fun i hi => haStep i (by omega)) (fun i hi => hbStep i (by omega))
      (fun i hi => hnStep i (by omega))
    obtain ⟨hn, ha, hb, _⟩ := hHolds (k + 1) (le_refl _)
    rw [chainCrumbs_succ]
    refine ⟨?_, ?_, ?_⟩
    · rw [ha, haStep k (Nat.lt_succ_self k), ihA, decomposeA_append]
    · rw [hb, hbStep k (Nat.lt_succ_self k), ihB, decomposeB_append]
    · rw [hn, hnStep k (Nat.lt_succ_self k), ihN, nReconstruct_append]

/-- The effective scalar of a multi-row run: `a·λ + b` over the whole challenge, with the
    register reconstructing the full concatenated crumb stream. The wrapper asserts that
    register equals the input challenge (`chain_spec`). -/
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

/-! ## Completeness: the honest prover fills a multi-row run.

    The completeness counterpart of `chain_decompose`. The gate's `complete` precondition is
    per-row crumb validity — independent of the threaded accumulators — so the honest builder
    threads with no global side-condition. (Contrast the EC gates, whose ladder completeness
    must propagate non-exceptional points across rows; that is why `varBaseMul`'s circuit has
    no free completeness while EndoScalar, being curve- and exception-free, does.) -/

/-- The honest multi-row witness: thread the gate's `build` from the canonical `(2,2,0)`,
    each row started from the previous row's output accumulators. -/
def chainBuild (rows : ℕ → List F) : ℕ → Witness F
  | 0 => build 2 2 0 (rows 0)
  | i + 1 =>
    let prev := chainBuild rows i
    build prev.a8 prev.b8 prev.n8 (rows (i + 1))

/-- **Completeness.** For any rows of valid crumbs, the threaded honest witness `chainBuild`
    satisfies the entire multi-row run — every row `Holds`, the first starts at `(2,2,0)`, the
    accumulators thread, and each row carries the given crumbs. Feeding this into
    `chain_toField` shows the honest prover computes the challenge's effective scalar. The
    threading and init are definitional; the only real input is `Gate.complete` per row. -/
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

/-! ## Uniqueness of the decomposition under the bit-size/field-size bound.

    The previous results pin the output to the folds *of the witness crumbs*. The honest
    meaning — `challenge ↦ a·λ + b` is a well-defined function — needs one more fact: a
    challenge determines its crumbs. That holds because the crumbs are base-4 digits (each
    in `{0,1,2,3}`, by `Gate.sound`) and the reconstruction does not wrap: the challenge's
    bit-width stays below the field size, encoded as `4 ^ #crumbs ≤ p`. (For the deployed
    128-bit challenge this is `4 ^ 64 = 2 ^ 128`, comfortably under the ~2²⁵⁴ Pasta order.)
    This is EndoScalar's analogue of `varBaseMul`'s `5m ≤ pastaFieldBits` no-wrap bound.

    The positional-arithmetic kernel — `digit` / `valNat` / `euclid_split` / `valNat_inj` —
    lives in `Kimchi.Circuit.EndoScalar.Base4`; here we bridge it to the field-valued
    `nReconstruct` and conclude. -/

variable [DecidableEq F]

/-- The field reconstruction is the cast of its `ℕ` shadow `valNat`, on valid crumbs. The
    bridge from `Base4` to the circuit's field-valued register. -/
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

/-- **Self-contained circuit soundness.** Two multi-row `EndoScalar` runs of the same crumb
    width that decode to the same challenge produce the *same* effective scalar `a·λ + b`.

    Combined with `chain_toField`, this is the honest statement that the gate realizes a
    well-defined function `challenge ↦ a·λ + b`: it depends only on the challenge, not on the
    prover's witness. The hypotheses are exactly `varBaseMul`'s shape — a chain over `m + 1`
    rows threaded from `(2,2,0)`, plus the no-wrap bound `4 ^ width ≤ p` tying the challenge's
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

end Kimchi.Circuit.EndoScalar
