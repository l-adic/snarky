import Kimchi.GrandProduct
import Kimchi.Permutation.Permutation
import Kimchi.SchwartzZippel

/-!
# Copy soundness: from grand products to values constant on the wiring

The last algebraic step of the permutation argument: the grand-product equality at a
single challenge pair avoiding the counted bad sets forces the witness values to be
invariant under the wiring permutation — the copy constraints.

Two strata:

* **The abstract core** (`values_eq_of_multiset_eq`, `copy_soundness`): cells with an
  *injective* address map and a permutation `σp`. Equality of the multisets of
  `(value, address)` pairs — the own-address tagging against the wired-to-address
  tagging — forces `v ∘ σp = v`, by membership alone: the pair `(v c, addr (σp c))`
  must occur among the own-address pairs, and address injectivity pins its cell to
  `σp c`. The single-challenge form feeds `multiset_eq_of_prod_eval` (the grand-product
  Schwartz–Zippel core) with the product equality at one good pair `(β, γ)` and descends.

* **The kimchi headline** (`Permutation.copy_soundness_of_dvd`): the per-challenge
  quotient-argument hypotheses — at a single good challenge pair `(β, γ)` the prover supplies an
  accumulator `zg` and the three permutation constraints pass the derandomized
  quotient checks (`Permutation.soundness_of_dvd`) — composed with the
  semantics of the sigma polynomials (`σᵢ(ωʲ)` is the address of the wired-to cell) and
  the injectivity of the cell addressing `(i, j) ↦ shiftᵢ·ωʲ` (the coset-disjointness of
  the shifts). Conclusion: on the unmasked region, the witness takes equal values on
  every wiring orbit.
-/

/-! ## The kimchi headline -/

namespace Kimchi.Permutation

open Kimchi.GrandProduct

open Polynomial

variable {F : Type*} [Field F]

/-- The row products evaluate to cell products: `shiftSide` at `ωʲ` is the product over
the columns of the own-address pair factors. -/
theorem shiftSide_eval (w : Fin permCols → Polynomial F) (shifts : Fin permCols → F)
    (β γ : F) (x : F) :
    (shiftSide w shifts β γ).eval x = ∏ i, ((w i).eval x + γ + β * shifts i * x) := by
  simp [shiftSide, eval_prod]

theorem sigmaSide_eval (w σ : Fin permCols → Polynomial F) (β γ : F) (x : F) :
    (sigmaSide w σ β γ).eval x = ∏ i, ((w i).eval x + γ + β * (σ i).eval x) := by
  simp [sigmaSide, eval_prod]

/-- **Copy soundness of the kimchi permutation argument, divisibility form.** Fix the
committed data — the witness columns `w`, the sigma columns `σpoly` (whose row semantics
is the wiring: at row `j`, `σᵢ(ωʲ)` is the address of the cell that `(i, j)` is wired
to), the coset shifts with injective cell addressing on the unmasked region. If at a
**single good challenge pair** `(β, γ)` — avoiding the small bad sets of the cell's
`(value, address)` pair multisets — the prover supplies an accumulator `zg` whose three
permutation constraints are divisible by `Z_H`, then the witness values are invariant under
the wiring on the unmasked region: for every cell `c`, `w(σp c) = w(c)`. -/
theorem copy_soundness_of_dvd [DecidableEq F] {ω : F} {n : ℕ}
    (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    {zkRows : ℕ} (hzk2 : 2 ≤ zkRows) (hzkn : zkRows ≤ n)
    (w σpoly : Fin permCols → Polynomial F) (shifts : Fin permCols → F)
    (σp : Equiv.Perm (Fin permCols × Fin (n - zkRows)))
    (haddr : Function.Injective
      (fun c : Fin permCols × Fin (n - zkRows) => shifts c.1 * ω ^ (c.2 : ℕ)))
    (hσ : ∀ c : Fin permCols × Fin (n - zkRows),
      (σpoly c.1).eval (ω ^ (c.2 : ℕ)) = shifts (σp c).1 * ω ^ ((σp c).2 : ℕ))
    (β γ : F)
    (hβ : β ∉ badBetas
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)), shifts c.1 * ω ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)), shifts (σp c).1 * ω ^ ((σp c).2 : ℕ))))
    (hγ : γ ∉ badGammas
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)), shifts c.1 * ω ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)), shifts (σp c).1 * ω ^ ((σp c).2 : ℕ))) β)
    (zg : Polynomial F)
    (hdvd : ∀ s, zH F n ∣ constraints ω zkRows zg w σpoly shifts
      β γ (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩ s) :
    ∀ c : Fin permCols × Fin (n - zkRows),
      (w (σp c).1).eval (ω ^ ((σp c).2 : ℕ)) = (w c.1).eval (ω ^ (c.2 : ℕ)) := by
  -- The field-level core at the cell data.
  refine Kimchi.GrandProduct.copy_soundness β γ _ _ haddr σp hβ hγ ?_
  -- The grand-product argument gives the row-product equality; reindex rows × columns to cells and
  -- rewrite the sigma side through the wiring semantics.
  have hrows := Permutation.soundness_of_dvd hω hn hzk2 hzkn zg w σpoly shifts β γ hdvd
  calc ∏ x : Fin permCols × Fin (n - zkRows),
        (γ + (w x.1).eval (ω ^ (x.2 : ℕ)) + shifts x.1 * ω ^ (x.2 : ℕ) * β)
      = ∏ j ∈ Finset.range (n - zkRows), (shiftSide w shifts β γ).eval (ω ^ j) := by
        rw [← Finset.univ_product_univ, Finset.prod_product_right,
          ← Fin.prod_univ_eq_prod_range]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [shiftSide_eval]
        exact Finset.prod_congr rfl fun i _ => by ring
    _ = ∏ j ∈ Finset.range (n - zkRows), (sigmaSide w σpoly β γ).eval (ω ^ j) :=
        hrows
    _ = ∏ x : Fin permCols × Fin (n - zkRows),
        (γ + (w x.1).eval (ω ^ (x.2 : ℕ)) + shifts (σp x).1 * ω ^ ((σp x).2 : ℕ) * β) := by
        rw [← Finset.univ_product_univ, Finset.prod_product_right,
          ← Fin.prod_univ_eq_prod_range]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [sigmaSide_eval]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hσ (i, j)]
        ring
end Kimchi.Permutation
