import Mathlib
import Kimchi.Commitment.IPA.Soundness.Batch
import Kimchi.Commitment.IPA.Chunk
import Kimchi.Verifier.Correspond

/-!
# Batch binding and the ft equation

Two pieces of the milestone-4 soundness composition, stated at the abstract level of
the IPA soundness stack (a scalar field `F`, an `F`-module `G`, an `SRS G`, exactly as
`Kimchi/Commitment/IPA/Soundness/Batch.lean`) — no wire types appear; the reflection
layer connects them to the executable verifier in the composition step (4.5).

**Batch binding (4.3): what a bound batch row *is*.** `batch_soundnessA` ends with, per
commitment row, an extracted witness pair `(a, ρ)` with `commit σ a ρ = C i` and every
claimed evaluation equal to `⟨a, evalVector (x j)⟩`. `rowPoly a` names the polynomial
with coefficient vector `a`; its kit (`rowPoly_eval`, `rowPoly_natDegree_lt`,
`rowPoly_coeff`, `rowPoly_coeff_self`) is the degree-`< 2^k` vector ↔ polynomial
dictionary — the chunk-index-`0` instance of the window kit in
`Kimchi/Commitment/IPA/Chunk.lean` (`chunkPoly_eval`, `assemblePoly_coeff`), whose
proofs it mirrors. **Pinned rows** then identify the VK columns with the Index's own
polynomials: when a bound row's commitment is a pinned column `commitPoly σ p` (or the
fixed-blinder `commitPolyMasked σ p` — production's selector masking, see
`Kimchi/Verifier/Correspond.lean`), binding forces `rowPoly a = p` and pins the blinder
to `0` (resp. `1`), so each claimed evaluation of that row is an evaluation of `p`
itself (`bound_eval_of_commitPoly`, `bound_eval_of_commitPolyMasked`). Through
`VKCorresponds` this turns "the verifier read column commitments" into "the verifier
read the Index's own interpolants". The binding hypothesis is carried in the
no-DL-relation form so these lemmas compose with `batch_soundnessA` verbatim.

**The ft equation (4.4): the ft row yields the deployed scalar equation.** The verifier
constructs `ftComm = pScalar • Cσ6 − (ζ^n − 1) • Tcomm` (`Cσ6` the seventh sigma
commitment, `Tcomm` the `ζ^n`-power combination of the `t` chunks — inner structure
irrelevant here). A bound ft row with claimed value `ftEval0` at `ζ` yields a quotient
`t` satisfying the deployed equation
`pScalar * σ₆.eval ζ − (ζ^n − 1) * t.eval ζ = ftEval0` — with `t` *defined* from the
identity (`ftQuotient`): at chunk count `nc = 1` no per-chunk extraction is needed,
which is why `chunked_ipa_soundness` is not consumed here (it guards the `nc > 1`
width pass). The all-points identity `ftQuotient_eval` is the primary statement (the
`ζω` companion is its instance at `y = ζω`); `ft_equation` is the `ζ` instance in the
deployed shape, and `ftComm_eq_commit` is the commit-linearity reading of the `ftComm`
construction that justifies its hypothesis set.
-/

namespace Kimchi.Verifier

open Polynomial Kimchi.Commitment.IPA

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## Row polynomials -/

/-- The polynomial a bound batch row *is*: the polynomial whose coefficient vector is
the extracted witness `a`. Project-local: the single-window (chunk-index-`0`) instance
of `Chunk.lean`'s `chunkPoly`/`assemblePoly`, defined directly so the 4.5 composition
never mentions chunks at width `nc = 1`. -/
noncomputable def rowPoly {n : ℕ} (a : Fin n → F) : Polynomial F :=
  ∑ i : Fin n, monomial (i : ℕ) (a i)

/-- A row polynomial evaluates as the witness's inner product with the evaluation
vector — the bridge from `batch_soundnessA`'s conclusion to polynomial language. -/
theorem rowPoly_eval {n : ℕ} (a : Fin n → F) (x : F) :
    (rowPoly a).eval x = innerProduct a (evalVector n x) := by
  unfold rowPoly innerProduct evalVector
  rw [eval_finsetSum]
  simp only [eval_monomial]

/-- A row polynomial of `n` coefficients has degree `< n`. -/
theorem rowPoly_natDegree_lt {n : ℕ} (hn : 0 < n) (a : Fin n → F) :
    (rowPoly a).natDegree < n := by
  apply lt_of_le_of_lt (natDegree_sum_le _ _)
  rw [Finset.fold_max_lt]
  exact ⟨hn, fun i _ => lt_of_le_of_lt (natDegree_monomial_le _) i.isLt⟩

/-- `rowPoly_natDegree_lt` at the SRS width `2 ^ k`, where positivity is automatic. -/
theorem rowPoly_natDegree_lt_two_pow {k : ℕ} (a : Fin (2 ^ k) → F) :
    (rowPoly a).natDegree < 2 ^ k :=
  rowPoly_natDegree_lt (Nat.two_pow_pos k) a

/-- The row polynomial's coefficients are the witness entries. -/
theorem rowPoly_coeff {n : ℕ} (a : Fin n → F) (i : Fin n) :
    (rowPoly a).coeff (i : ℕ) = a i := by
  unfold rowPoly
  simp only [finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
  · intro j _ hj
    exact if_neg fun h => hj (Fin.ext h)
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The coefficient round-trip: reading off the low coefficients of a polynomial of
degree `< n` and reassembling recovers it. With `rowPoly_coeff` this makes `rowPoly`
the vector ↔ polynomial dictionary at degree `< n`. -/
theorem rowPoly_coeff_self {n : ℕ} {p : Polynomial F} (hp : p.natDegree < n) :
    rowPoly (fun i : Fin n => p.coeff (i : ℕ)) = p := by
  unfold rowPoly
  rw [Fin.sum_univ_eq_sum_range (fun i => monomial i (p.coeff i)) n]
  exact (p.as_sum_range' n hp).symm

/-! ## Pinned rows -/

/-- An unblinded column commitment is the hiding commitment of the coefficient vector
at blinder `0` — the shape binding-injectivity consumes. Not `rfl`: the blinder term
`0 • σ.h` must be discharged. -/
theorem commitPoly_eq_commit (σ : SRS G) (p : Polynomial F) :
    commitPoly σ p = commit σ (fun i => p.coeff (i : ℕ)) 0 := by
  simp only [commitPoly, commit, zero_smul, add_zero]

/-- A fixed-blinder column commitment is the hiding commitment of the coefficient
vector at blinder `1` — production's `mask_fixed` on the six selectors. -/
theorem commitPolyMasked_eq_commit (σ : SRS G) (p : Polynomial F) :
    commitPolyMasked σ p = commit σ (fun i => p.coeff (i : ℕ)) 1 := by
  simp only [commitPolyMasked, commitPoly, commit, one_smul]

/-- **A bound row against a pinned column is that column's polynomial.** If an
extracted witness pair `(a, ρ)` commits to an unblinded column commitment
`commitPoly σ p` with `p` inside the SRS degree bound, binding pins the pair: the row
polynomial is `p` itself and the blinder is `0`. The binding hypothesis is the
no-DL-relation form, matching `batch_soundnessA`'s. -/
theorem bound_eq_of_commitPoly (σ : SRS G)
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

/-- **A bound row against a masked pinned column is that column's polynomial.** The
fixed-blinder (`commitPolyMasked`) analogue of `bound_eq_of_commitPoly`: binding pins
the row polynomial to `p` and the blinder to `1`. -/
theorem bound_eq_of_commitPolyMasked (σ : SRS G)
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

/-- **Pinned-row evaluations, unblinded columns** — the corollary shape 4.5 consumes:
a claimed evaluation of a row bound to a pinned column (`batch_soundnessA`'s
`e i j = ⟨a, evalVector (x j)⟩` with `C i = commitPoly σ p`) is an evaluation of that
column's own polynomial. -/
theorem bound_eval_of_commitPoly (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    {a : Fin (2 ^ σ.k) → F} {ρ : F} {p : Polynomial F}
    (hcommit : commit σ a ρ = commitPoly σ p) (hdeg : p.natDegree < 2 ^ σ.k)
    {x e : F} (he : e = innerProduct a (evalVector (2 ^ σ.k) x)) :
    e = p.eval x := by
  rw [he, ← rowPoly_eval, (bound_eq_of_commitPoly σ hbind hcommit hdeg).1]

/-- **Pinned-row evaluations, masked columns** — the selector-column analogue of
`bound_eval_of_commitPoly`. -/
theorem bound_eval_of_commitPolyMasked (σ : SRS G)
    (hbind : ∀ (w : Fin (2 ^ σ.k) → F) (w_h : F), DLRelation σ w w_h → w = 0 ∧ w_h = 0)
    {a : Fin (2 ^ σ.k) → F} {ρ : F} {p : Polynomial F}
    (hcommit : commit σ a ρ = commitPolyMasked σ p) (hdeg : p.natDegree < 2 ^ σ.k)
    {x e : F} (he : e = innerProduct a (evalVector (2 ^ σ.k) x)) :
    e = p.eval x := by
  rw [he, ← rowPoly_eval, (bound_eq_of_commitPolyMasked σ hbind hcommit hdeg).1]

/-! ## The ft equation -/

/-- Two-term homogeneity of the hiding commitment,
`commit σ (c • a) (c * r) = c • commit σ a r` — the two-term instance of
`commit_sum_smul` (`Soundness/Batch.lean`), stated separately so the `ftComm`
rearrangement needs no `Fin 2` packaging. -/
theorem commit_smul (σ : SRS G) (c : F) (a : Fin (2 ^ σ.k) → F) (r : F) :
    commit σ (c • a) (c * r) = c • commit σ a r := by
  simp only [commit, commitGen_smul_left, mul_smul, smul_add]

/-- Two-term subtractivity of the hiding commitment,
`commit σ (a - b) (r - s) = commit σ a r - commit σ b s`. -/
theorem commit_sub (σ : SRS G) (a b : Fin (2 ^ σ.k) → F) (r s : F) :
    commit σ (a - b) (r - s) = commit σ a r - commit σ b s := by
  simp only [commit, commitGen_sub, sub_smul]
  abel

/-- The quotient the ft identity *defines*: `t := (ζ^n − 1)⁻¹ • (pScalar • σ₆ −
rowPoly a)`. At chunk count `nc = 1` the honest `t` need not be extracted — the bound
ft row determines it exactly, and `ftQuotient_spec` is the defining identity. -/
noncomputable def ftQuotient (n : ℕ) (σ₆ : Polynomial F) (pScalar ζ : F)
    {N : ℕ} (a : Fin N → F) : Polynomial F :=
  (ζ ^ n - 1)⁻¹ • (pScalar • σ₆ - rowPoly a)

/-- The defining identity of the ft quotient, **as polynomials**:
`pScalar • σ₆ − (ζ^n − 1) • t = rowPoly a`. Requires only `ζ^n ≠ 1` (so `ζ^n − 1` is
invertible); no commitment data enters. -/
theorem ftQuotient_spec (n : ℕ) (σ₆ : Polynomial F) (pScalar ζ : F) (hζ : ζ ^ n ≠ 1)
    {N : ℕ} (a : Fin N → F) :
    pScalar • σ₆ - (ζ ^ n - 1) • ftQuotient n σ₆ pScalar ζ a = rowPoly a := by
  unfold ftQuotient
  rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hζ), one_smul, sub_sub_cancel]

/-- **The all-points ft identity** — the primary 4.4 statement: at *every* point `y`,
the combination `pScalar • σ₆ − (ζ^n − 1) • t` evaluates to the row's inner product
with the evaluation vector at `y`. The deployed `ζ` instance is `ft_equation`; the
`ζω` companion is this lemma at `y = ζω`, for free. -/
theorem ftQuotient_eval (n : ℕ) (σ₆ : Polynomial F) (pScalar ζ : F) (hζ : ζ ^ n ≠ 1)
    {N : ℕ} (a : Fin N → F) (y : F) :
    (pScalar • σ₆ - (ζ ^ n - 1) • ftQuotient n σ₆ pScalar ζ a).eval y
      = innerProduct a (evalVector N y) := by
  rw [ftQuotient_spec n σ₆ pScalar ζ hζ a, rowPoly_eval]

/-- **The commit-linearity reading of the ft construction** — what the hypothesis set
of `ft_equation` says: given `hC` and `hcommit`, the `t`-side commitment is itself a
hiding commitment, of the vector `pScalar • coeffs σ₆ − a` at blinder `−ρ`. This is
the two-term instance of the `commit_sum_smul` rearrangement; it justifies carrying
`Cσ6`/`Tcomm`/`hcommit` in the deployed statement even though the scalar equation
itself needs none of them. -/
theorem ftComm_eq_commit (σ : SRS G) (n : ℕ) (σ₆ : Polynomial F)
    {Cσ6 Tcomm : G} (hC : Cσ6 = commitPoly σ σ₆) (pScalar ζ : F)
    {a : Fin (2 ^ σ.k) → F} {ρ : F}
    (hcommit : commit σ a ρ = pScalar • Cσ6 - (ζ ^ n - 1) • Tcomm) :
    (ζ ^ n - 1) • Tcomm
      = commit σ (pScalar • (fun i : Fin (2 ^ σ.k) => σ₆.coeff (i : ℕ)) - a) (-ρ) := by
  have h1 : (ζ ^ n - 1) • Tcomm = pScalar • Cσ6 - commit σ a ρ := by
    rw [hcommit]; abel
  rw [h1, hC, commitPoly_eq_commit, ← commit_smul, ← commit_sub, mul_zero, zero_sub]

set_option linter.unusedVariables false in
/-- **The ft equation (4.4)** — the deployed scalar equation, in the deployed shape:
a bound ft row (`hcommit`, against the verifier's
`ftComm = pScalar • Cσ6 − (ζ^n − 1) • Tcomm`) whose claimed value at `ζ` is `ftEval0`
(`heval`) yields a quotient `t` with
`pScalar * σ₆.eval ζ − (ζ^n − 1) * t.eval ζ = ftEval0`.

Hypothesis-minimal by design: the proof consumes only `hζ` and `heval` — the witness
`t := ftQuotient n σ₆ pScalar ζ a` is *defined* from the identity, so no binding and
no commitment algebra is needed for this statement (`hσ₆`, `hC`, `hcommit` document
the deployment reading — see `ftComm_eq_commit` — and keep the binder set 4.5
instantiates; the dictated `hbind` is dropped as unused). -/
theorem ft_equation (σ : SRS G)
    (σ₆ : Polynomial F) (hσ₆ : σ₆.natDegree < 2 ^ σ.k)
    (Cσ6 Tcomm : G) (hC : Cσ6 = commitPoly σ σ₆)
    (pScalar ζ ftEval0 : F) (n : ℕ) (hζ : ζ ^ n ≠ 1)
    (a : Fin (2 ^ σ.k) → F) (ρ : F)
    (hcommit : commit σ a ρ = pScalar • Cσ6 - (ζ ^ n - 1) • Tcomm)
    (heval : innerProduct a (evalVector (2 ^ σ.k) ζ) = ftEval0) :
    ∃ t : Polynomial F,
      pScalar * σ₆.eval ζ - (ζ ^ n - 1) * t.eval ζ = ftEval0 := by
  refine ⟨ftQuotient n σ₆ pScalar ζ a, ?_⟩
  have h := ftQuotient_eval n σ₆ pScalar ζ hζ a ζ
  rw [eval_sub, eval_smul, eval_smul, smul_eq_mul, smul_eq_mul, heval] at h
  exact h

end Kimchi.Verifier
