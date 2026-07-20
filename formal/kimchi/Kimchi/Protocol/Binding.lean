import Mathlib
import Bulletproof.Protocol
import Bulletproof.Soundness
import Kimchi.Protocol.Correspond

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

namespace Kimchi.Protocol

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

/-- The row polynomial's coefficients are the witness entries. -/
private theorem rowPoly_coeff {n : ℕ} (a : Fin n → F) (i : Fin n) :
    (rowPoly a).coeff (i : ℕ) = a i := by
  unfold rowPoly
  simp only [finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
  · intro j _ hj
    exact if_neg fun h => hj (Fin.ext h)
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Reading off the low coefficients of a polynomial of degree `< n` and reassembling
recovers it; with the previous lemma this makes `rowPoly` a dictionary between
coefficient vectors and polynomials of degree `< n`. -/
theorem rowPoly_coeff_self {n : ℕ} {p : Polynomial F} (hp : p.natDegree < n) :
    rowPoly (fun i : Fin n => p.coeff (i : ℕ)) = p := by
  unfold rowPoly
  rw [Fin.sum_univ_eq_sum_range (fun i => monomial i (p.coeff i)) n]
  exact (p.as_sum_range' n hp).symm

/-! ## Pinned rows -/

/-- An unblinded column commitment is the hiding commitment of its coefficient vector at
blinder `0` — the shape binding injectivity consumes. -/
theorem commitPoly_eq_commit (σ : SRS G) (p : Polynomial F) :
    commitPoly σ p = commit σ (fun i => p.coeff (i : ℕ)) 0 := by
  simp only [commitPoly, commit, zero_smul, add_zero]

/-- A fixed-blinder column commitment is the hiding commitment of its coefficient vector
at blinder `1`. -/
private theorem commitPolyMasked_eq_commit (σ : SRS G) (p : Polynomial F) :
    commitPolyMasked σ p = commit σ (fun i => p.coeff (i : ℕ)) 1 := by
  simp only [commitPolyMasked, commitPoly, commit, one_smul]

/-- A bound row against an unblinded fixed column is that column's polynomial: binding
pins the row polynomial to `p` and the blinder to `0`. -/
private theorem bound_eq_of_commitPoly (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    {a : Fin (2 ^ σ.k) → F} {ρ : F} {p : Polynomial F}
    (hcommit : commit σ a ρ = commitPoly σ p) (hdeg : p.natDegree < 2 ^ σ.k) :
    rowPoly a = p ∧ ρ = 0 := by
  have hbd : CommitmentBinding (F := F) σ := (commitmentBinding_iff_no_relation σ).mpr hbind
  have hpair := @hbd (a, ρ) (fun i => p.coeff (i : ℕ), 0)
    (hcommit.trans (commitPoly_eq_commit σ p))
  have ha : a = fun i : Fin (2 ^ σ.k) => p.coeff (i : ℕ) := congrArg Prod.fst hpair
  have hρ : ρ = 0 := congrArg Prod.snd hpair
  refine ⟨?_, hρ⟩
  rw [ha]
  exact rowPoly_coeff_self hdeg

/-- The fixed-blinder analogue: the row polynomial is `p` and the blinder is `1`. -/
private theorem bound_eq_of_commitPolyMasked (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    {a : Fin (2 ^ σ.k) → F} {ρ : F} {p : Polynomial F}
    (hcommit : commit σ a ρ = commitPolyMasked σ p) (hdeg : p.natDegree < 2 ^ σ.k) :
    rowPoly a = p ∧ ρ = 1 := by
  have hbd : CommitmentBinding (F := F) σ := (commitmentBinding_iff_no_relation σ).mpr hbind
  have hpair := @hbd (a, ρ) (fun i => p.coeff (i : ℕ), 1)
    (hcommit.trans (commitPolyMasked_eq_commit σ p))
  have ha : a = fun i : Fin (2 ^ σ.k) => p.coeff (i : ℕ) := congrArg Prod.fst hpair
  have hρ : ρ = 1 := congrArg Prod.snd hpair
  refine ⟨?_, hρ⟩
  rw [ha]
  exact rowPoly_coeff_self hdeg

/-- A claimed evaluation of a row bound to an unblinded fixed column is an evaluation of
that column's own polynomial. -/
theorem bound_eval_of_commitPoly (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    {a : Fin (2 ^ σ.k) → F} {ρ : F} {p : Polynomial F}
    (hcommit : commit σ a ρ = commitPoly σ p) (hdeg : p.natDegree < 2 ^ σ.k)
    {x e : F} (he : e = innerProduct a (evalVector (2 ^ σ.k) x)) :
    e = p.eval x := by
  rw [he, ← rowPoly_eval, (bound_eq_of_commitPoly σ hbind hcommit hdeg).1]

/-- The selector-column analogue. -/
theorem bound_eval_of_commitPolyMasked (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    {a : Fin (2 ^ σ.k) → F} {ρ : F} {p : Polynomial F}
    (hcommit : commit σ a ρ = commitPolyMasked σ p) (hdeg : p.natDegree < 2 ^ σ.k)
    {x e : F} (he : e = innerProduct a (evalVector (2 ^ σ.k) x)) :
    e = p.eval x := by
  rw [he, ← rowPoly_eval, (bound_eq_of_commitPolyMasked σ hbind hcommit hdeg).1]

end Kimchi.Protocol
