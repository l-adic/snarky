import Kimchi.Domain
import CompPoly.Univariate.ToPoly.Core
import CompPoly.Univariate.NTT.Interpolation
import Bulletproof.Wire

/-!
# Executable index polynomial commitments

Interpolate an index column by the inverse NTT, then commit consecutive coefficient chunks
against the SRS. Each chunk restarts at the first SRS generator. Selector commitments add the
fixed blinding base once per chunk; permutation and coefficient commitments are unmasked.

`columnCoefficients_getD` identifies every executable coefficient with the column interpolant.
`commitColumn_eq` identifies the accelerated commitment with the polynomial's generator sum.
Neither construction consumes a dumped commitment or a Lagrange table.
-/

namespace Kimchi.Index

open CompPoly.CPolynomial CompPoly.CPolynomial.NTT Bulletproof

variable {F : Type} [Field F]

/-- The coefficients of a column, computed by the inverse NTT. -/
def columnCoefficients (D : Domain F) (v : Fin D.n → F) : Array F :=
  Inverse.inverseImpl D (Array.ofFn v)

/-- The inverse NTT computes the column interpolant. -/
theorem columnCoefficients_toPoly (D : Domain F) (v : Fin D.n → F) :
    Raw.toPoly (columnCoefficients D v) = columnPoly D.omega v := by
  apply eq_of_eval_eq_on_domain D.primitive D.n_pos
  · rw [Polynomial.degree_lt_iff_coeff_zero]
    intro i hi
    change D.n ≤ i at hi
    rw [Raw.coeff_toPoly]
    have hs : (columnCoefficients D v).size = D.n := by
      simp [columnCoefficients, Inverse.inverseImpl_correct]
    have hi' : (columnCoefficients D v).size ≤ i := hs ▸ hi
    simp only [Raw.coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hi',
      Option.getD_none]
  · exact degree_columnPoly_lt D.primitive v
  · intro i hi
    change i < D.n at hi
    rw [Raw.eval_toPoly_eq_eval]
    have he := Inverse.inverseImpl_eval_node_eq D (Array.ofFn v) ⟨i, hi⟩
    simp only [Domain.node, columnCoefficients] at *
    rw [he]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hi,
      Option.getD_some]
    exact (eval_columnPoly D.primitive v ⟨i, hi⟩).symm

/-- Every computed coefficient is the corresponding coefficient of the interpolant. -/
theorem columnCoefficients_getD (D : Domain F) (v : Fin D.n → F) (i : Nat) :
    (columnCoefficients D v).getD i 0 = (columnPoly D.omega v).coeff i := by
  rw [← columnCoefficients_toPoly D v, Raw.coeff_toPoly]

variable (C : Ipa.KimchiCurve)

/-- Commit one coefficient chunk, with zero coefficients beyond the array. Kept separate
from interpolation so that reading a coefficient never recomputes the inverse NTT. -/
@[noinline] def commitCoefficients (σ : SRS C.Point) (coeffs : Array C.ScalarField)
    (chunk : Nat) : C.Point :=
  Ipa.msm C σ.g (fun j => coeffs.getD (chunk * 2 ^ σ.k + j.val) 0)

/-- The generator commitment of one polynomial chunk. -/
noncomputable def commitPolyChunk (σ : SRS C.Point) (p : Polynomial C.ScalarField)
    (chunk : Nat) : C.Point :=
  commitGen σ.g (fun j => p.coeff (chunk * 2 ^ σ.k + j.val))

/-- A column's commitments, obtained by one interpolation followed by one MSM per chunk. -/
@[noinline] def commitColumn (σ : SRS C.Point) (D : Domain C.ScalarField) (nc : Nat)
    (v : Fin D.n → C.ScalarField) : Vector C.Point nc :=
  let coeffs := columnCoefficients D v
  Vector.ofFn (fun c => commitCoefficients C σ coeffs c.val)

/-- The accelerated column commitment is its polynomial's chunk commitment. -/
theorem commitColumn_eq (σ : SRS C.Point) (D : Domain C.ScalarField) (nc : Nat)
    (v : Fin D.n → C.ScalarField) (c : Fin nc) :
    (commitColumn C σ D nc v)[c] = commitPolyChunk C σ (columnPoly D.omega v) c.val := by
  simp only [commitColumn, Fin.getElem_fin, Vector.getElem_ofFn, commitCoefficients]
  rw [Ipa.msm_eq, commitGenₗ_apply]
  congr 1
  funext j
  exact columnCoefficients_getD D v _

end Kimchi.Index
