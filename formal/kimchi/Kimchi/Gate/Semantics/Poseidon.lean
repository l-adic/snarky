import Kimchi.Gate.Poseidon

/-! # Poseidon gate semantics: the gate computes the 5-round permutation
    (soundness), and the honest witness satisfies it (completeness). -/

namespace Kimchi.Gate.Poseidon

variable {F : Type*}

/-! ## Soundness: a satisfying row computes the permutation. -/

/-- Each round's three componentwise constraints assemble into `sᵢ₊₁ = round(sᵢ, rcᵢ)`. -/
private theorem step_eq [CommRing F] {a b : F × F × F}
    (h1 : a.1 - b.1 = 0) (h2 : a.2.1 - b.2.1 = 0) (h3 : a.2.2 - b.2.2 = 0) : a = b :=
  Prod.ext (sub_eq_zero.mp h1) (Prod.ext (sub_eq_zero.mp h2) (sub_eq_zero.mp h3))

/-- **Soundness of the Poseidon gate.** A satisfying witness's output state `s5` is the 5-round
    permutation of its input state `s0`. -/
theorem sound [CommRing F] (M : Mds F) (rc : Fin 5 → F × F × F) (w : Witness F)
    (h : Holds M rc w) :
    w.s5 = perm M w.s0 rc := by
  simp only [Holds, constraints, List.forall_mem_cons] at h
  obtain ⟨h1a, h1b, h1c, h2a, h2b, h2c, h3a, h3b, h3c,
    h4a, h4b, h4c, h5a, h5b, h5c, -⟩ := h
  have hs1 : w.s1 = round M w.s0 (rc 0) := step_eq h1a h1b h1c
  have hs2 : w.s2 = round M w.s1 (rc 1) := step_eq h2a h2b h2c
  have hs3 : w.s3 = round M w.s2 (rc 2) := step_eq h3a h3b h3c
  have hs4 : w.s4 = round M w.s3 (rc 3) := step_eq h4a h4b h4c
  have hs5 : w.s5 = round M w.s4 (rc 4) := step_eq h5a h5b h5c
  rw [perm, ← hs1, ← hs2, ← hs3, ← hs4, ← hs5]

/-! ## Completeness: the honest witness satisfies the gate. -/

/-- Build the canonical satisfying row by iterating `round` from the input state. -/
def build [CommRing F] (M : Mds F) (s0 : F × F × F) (rc : Fin 5 → F × F × F) : Witness F :=
  let s1 := round M s0 (rc 0)
  let s2 := round M s1 (rc 1)
  let s3 := round M s2 (rc 2)
  let s4 := round M s3 (rc 3)
  { s0, s1, s2, s3, s4, s5 := round M s4 (rc 4) }

/-- **Completeness of the Poseidon gate.** The honest witness (`build`) satisfies all 15
    constraints — unconditionally (the permutation is total). -/
theorem complete [CommRing F] (M : Mds F) (s0 : F × F × F) (rc : Fin 5 → F × F × F) :
    Holds M rc (build M s0 rc) := by
  intro e he
  fin_cases he <;> simp [build]

/-! ## Runnable example. -/

/-- A small-field MDS for the runnable example. -/
private def egMds : Mds (ZMod 101) := ⟨2, 3, 5, 7, 11, 13, 17, 19, 23⟩

/-- A concrete satisfying row over a small field: `build` always satisfies `ok`. -/
private def egPoseidon : Witness (ZMod 101) :=
  build egMds (1, 2, 3) (fun _ => (1, 1, 1))

#eval ok egMds (fun _ => (1, 1, 1)) egPoseidon   -- expect true

end Kimchi.Gate.Poseidon
