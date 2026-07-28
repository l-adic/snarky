import Mathlib
import Kimchi.Verifier.Reduction.Correspond

/-!
# Batch binding

What a bound batch row *is*, and what binding forces once that row is a fixed column.

Batch extraction yields, per committed row, a witness pair `(a, ρ)` with
`commit σ a ρ = C i` and every claimed evaluation equal to `⟨a, evalVector (x j)⟩`.
`rowPoly a` names the polynomial with coefficient vector `a`; its small kit is the
degree-bounded dictionary between coefficient vectors and polynomials.

When a bound row's commitment is a fixed column — unblinded, or carrying the fixed
blinder the selectors use — binding forces the row polynomial to be that column's
polynomial and pins the blinder. Each claimed evaluation of such a row is therefore an
evaluation of the column itself, which is what turns "the verifier read committed
columns" into "the verifier read the circuit's own interpolants".

Stated over an abstract module with an SRS; binding is carried in the no-relation form.
-/
open Bulletproof

namespace Kimchi.Verifier

open Polynomial Bulletproof

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## Row polynomials -/

/-- The polynomial a bound row *is*: the one whose coefficient vector is the extracted
witness. -/
noncomputable def rowPoly {n : ℕ} (a : Fin n → F) : Polynomial F :=
  ∑ i : Fin n, monomial (i : ℕ) (a i)

/-- A row polynomial evaluates as the inner product of its witness with the evaluation
vector — the bridge from extraction to polynomial language. -/
theorem rowPoly_eval {n : ℕ} (a : Fin n → F) (x : F) :
    (rowPoly a).eval x = innerProduct a (evalVector n x) := by
  unfold rowPoly innerProduct evalVector
  rw [eval_finsetSum]
  simp only [eval_monomial]

/-- A row polynomial of `n` coefficients has degree `< n`. -/
private theorem rowPoly_natDegree_lt {n : ℕ} (hn : 0 < n) (a : Fin n → F) :
    (rowPoly a).natDegree < n := by
  apply lt_of_le_of_lt (natDegree_sum_le _ _)
  rw [Finset.fold_max_lt]
  exact ⟨hn, fun i _ => lt_of_le_of_lt (natDegree_monomial_le _) i.isLt⟩

/-- The degree bound at the SRS width, where positivity is automatic. -/
theorem rowPoly_natDegree_lt_two_pow {k : ℕ} (a : Fin (2 ^ k) → F) :
    (rowPoly a).natDegree < 2 ^ k :=
  rowPoly_natDegree_lt (Nat.two_pow_pos k) a

/-! ## Pinned rows -/

/-- An unblinded column commitment is the hiding commitment of its coefficient vector at
blinder `0` — the shape binding injectivity consumes. -/
theorem commitPoly_eq_commit (σ : SRS G) (p : Polynomial F) :
    commitPoly σ p = commit σ (fun i => p.coeff (i : ℕ)) 0 := by
  simp only [commitPoly, commit, zero_smul, add_zero]

end Kimchi.Verifier
