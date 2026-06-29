import Kimchi.Circuit.EndoScalar.Internal

/-!
# The `EndoScalar` circuit: the effective scalar `a·λ + b`

The endo-scalar decomposition composes `Kimchi.Gate.EndoScalar` rows into the effective scalar
`a·λ + b`. A challenge is processed eight crumbs at a time, each row threading the `(a, b, n)`
accumulators; the result is the effective scalar `a·λ + b` and the raw register `n`, which the
wrapper asserts equals the input challenge. The construction follows the OCaml/PureScript
`to_field_checked'`, which runs `mapAccumM` over the row chunks.

This module states the three headline theorems; their supporting development —
the accumulator folds, the multi-row reconstruction, and the base-4 uniqueness kernel — lives in
`Kimchi.Circuit.EndoScalar.Internal`.

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
-/

namespace Kimchi.Circuit.EndoScalar

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

end Kimchi.Circuit.EndoScalar
