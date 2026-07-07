import Kimchi.Quotient.GrandProduct
import Kimchi.Quotient.Permutation

/-!
# Copy soundness: from grand products to values constant on the wiring

The last algebraic step of the permutation argument: grand-product equalities at an
injective challenge grid force the witness values to be invariant under the wiring
permutation — the copy constraints.

Two strata:

* **The abstract core** (`values_eq_of_multiset_eq`, `copy_soundness`): cells with an
  *injective* address map and a permutation `σp`. Equality of the multisets of
  `(value, address)` pairs — the own-address tagging against the wired-to-address
  tagging — forces `v ∘ σp = v`, by membership alone: the pair `(v c, addr (σp c))`
  must occur among the own-address pairs, and address injectivity pins its cell to
  `σp c`. The grid form feeds `multiset_eq_of_grid_prod_evals` (milestone 1) with the
  per-point product equalities and descends.

* **The kimchi headline** (`Permutation.copy_soundness`): the grid of per-challenge
  quotient-argument hypotheses — at each grid node `(βₐ, γ_b)` the prover supplies an
  accumulator `zg a b` and the three permutation constraints pass the derandomized
  quotient checks (`Permutation.soundness`, milestones 2–3) — composed with the
  semantics of the sigma polynomials (`σᵢ(ωʲ)` is the address of the wired-to cell) and
  the injectivity of the cell addressing `(i, j) ↦ shiftᵢ·ωʲ` (the coset-disjointness of
  the shifts). Conclusion: on the unmasked region, the witness takes equal values on
  every wiring orbit.
-/

namespace Kimchi.Quotient

open Polynomial

variable {F : Type*} [Field F]

/-! ## The abstract core -/

omit [Field F] in
/-- **Values from multisets.** If the multiset of `(value, own address)` pairs equals the
multiset of `(value, wired-to address)` pairs and addresses are injective, values are
invariant under the wiring: the pair `(v c, addr (σp c))` occurs among the own-address
pairs, and its address pins its cell to `σp c`. -/
theorem values_eq_of_multiset_eq {cells : Type*} [Fintype cells]
    (v addr : cells → F) (haddr : Function.Injective addr) (σp : Equiv.Perm cells)
    (h : (Finset.univ.val.map fun c => (v c, addr c))
      = (Finset.univ.val.map fun c => (v c, addr (σp c)))) :
    ∀ c, v (σp c) = v c := by
  intro c₀
  have hmem : (v c₀, addr (σp c₀)) ∈ (Finset.univ.val.map fun c => (v c, addr c)) := by
    rw [h]
    exact Multiset.mem_map.mpr ⟨c₀, by simp, rfl⟩
  obtain ⟨c₁, -, hc₁⟩ := Multiset.mem_map.mp hmem
  have h₂ : c₁ = σp c₀ := haddr (congrArg Prod.snd hc₁)
  have h₁ := congrArg Prod.fst hc₁
  rwa [h₂] at h₁

/-- **Copy soundness, field level.** Products of `(γ + value + address·β)` over the cells
agreeing at every node of an injective challenge grid — own addresses on the left,
wired-to addresses on the right — force the values to be invariant under the wiring.
Milestone 1's grid core turns the products into multiset equality; injective addressing
descends to the values. -/
theorem copy_soundness {cells : Type*} [Fintype cells] {M N : ℕ}
    (b : Fin M → F) (g : Fin N → F)
    (hb : Function.Injective b) (hg : Function.Injective g)
    (hM : Fintype.card cells < M) (hN : Fintype.card cells < N)
    (v addr : cells → F) (haddr : Function.Injective addr) (σp : Equiv.Perm cells)
    (h : ∀ (i : Fin M) (j : Fin N),
      ∏ c, (g j + v c + addr c * b i) = ∏ c, (g j + v c + addr (σp c) * b i)) :
    ∀ c, v (σp c) = v c := by
  refine values_eq_of_multiset_eq v addr haddr σp
    (multiset_eq_of_grid_prod_evals b g hb hg _ _ ?_ ?_ ?_ ?_ fun i j => ?_)
  · simpa using hN
  · simpa using hM
  · simpa using hN
  · simpa using hM
  · rw [Multiset.map_map, Multiset.map_map]
    simpa only [Function.comp_def, ← Finset.prod_eq_multiset_prod] using h i j

end Kimchi.Quotient

/-! ## The kimchi headline -/

namespace Kimchi.Quotient.Permutation

open Polynomial Kimchi.Quotient

variable {F : Type*} [Field F]

/-- The row products evaluate to cell products: `shiftSide` at `ωʲ` is the product over
the columns of the own-address pair factors. -/
theorem shiftSide_eval (w : Fin 7 → Polynomial F) (shifts : Fin 7 → F) (β γ : F) (x : F) :
    (shiftSide w shifts β γ).eval x = ∏ i, ((w i).eval x + γ + β * shifts i * x) := by
  simp [shiftSide, eval_prod]

theorem sigmaSide_eval (w σ : Fin 7 → Polynomial F) (β γ : F) (x : F) :
    (sigmaSide w σ β γ).eval x = ∏ i, ((w i).eval x + γ + β * (σ i).eval x) := by
  simp [sigmaSide, eval_prod]

/-- **Copy soundness of the kimchi permutation argument.** Fix the committed data — the
witness columns `w`, the sigma columns `σpoly` (whose row semantics is the wiring: at row
`j`, `σᵢ(ωʲ)` is the address of the cell that `(i, j)` is wired to), the coset shifts with
injective cell addressing on the unmasked region. If at every node `(bₐ, g_c)` of an
injective challenge grid the prover supplies an accumulator `zg a c` passing the
derandomized quotient checks of the three permutation constraints, then the witness
values are invariant under the wiring on the unmasked region: for every cell `c`,
`w(σp c) = w(c)`. -/
theorem copy_soundness {ω : F} {n NN : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    {zkRows : ℕ} (hzk0 : 0 < zkRows) (hzkn : zkRows ≤ n)
    (w σpoly : Fin 7 → Polynomial F) (shifts : Fin 7 → F)
    (σp : Equiv.Perm (Fin 7 × Fin (n - zkRows)))
    (haddr : Function.Injective
      (fun c : Fin 7 × Fin (n - zkRows) => shifts c.1 * ω ^ (c.2 : ℕ)))
    (hσ : ∀ c : Fin 7 × Fin (n - zkRows),
      (σpoly c.1).eval (ω ^ (c.2 : ℕ)) = shifts (σp c).1 * ω ^ ((σp c).2 : ℕ))
    {M N : ℕ} (b : Fin M → F) (g : Fin N → F)
    (hb : Function.Injective b) (hg : Function.Injective g)
    (hM : 7 * (n - zkRows) < M) (hN : 7 * (n - zkRows) < N)
    (zg : Fin M → Fin N → Polynomial F)
    (α : Fin M → Fin N → Fin 3 → F) (hα : ∀ a c, Function.Injective (α a c))
    (ζ : Fin M → Fin N → Fin NN → F) (hζ : ∀ a c, Function.Injective (ζ a c))
    (t : Fin M → Fin N → Fin 3 → Polynomial F) (D : ℕ) (hD : D < NN)
    (hCdeg : ∀ a c s, (aggregate (α a c s) (constraints ω zkRows (zg a c) w σpoly shifts
      (b a) (g c) (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩)).natDegree ≤ D)
    (htdeg : ∀ a c s, (t a c s * zH F n).natDegree ≤ D)
    (hcheck : ∀ a c s p, (aggregate (α a c s) (constraints ω zkRows (zg a c) w σpoly shifts
        (b a) (g c) (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩)).eval (ζ a c p)
      = (t a c s * zH F n).eval (ζ a c p)) :
    ∀ c : Fin 7 × Fin (n - zkRows),
      (w (σp c).1).eval (ω ^ ((σp c).2 : ℕ)) = (w c.1).eval (ω ^ (c.2 : ℕ)) := by
  -- The field-level core at the cell data.
  refine Kimchi.Quotient.copy_soundness b g hb hg ?_ ?_
    (fun c => (w c.1).eval (ω ^ (c.2 : ℕ)))
    (fun c => shifts c.1 * ω ^ (c.2 : ℕ)) haddr σp fun a c => ?_
  · simpa using hM
  · simpa using hN
  -- At each grid node, milestone 3 gives the row-product equality; reindex rows × columns
  -- to cells and rewrite the sigma side through the wiring semantics.
  have hrows := Permutation.soundness hω hn hzk0 hzkn (zg a c) w σpoly shifts (b a) (g c)
    (α a c) (hα a c) (ζ a c) (hζ a c) (t a c) D hD (hCdeg a c) (htdeg a c) (hcheck a c)
  calc ∏ x : Fin 7 × Fin (n - zkRows),
        (g c + (w x.1).eval (ω ^ (x.2 : ℕ)) + shifts x.1 * ω ^ (x.2 : ℕ) * b a)
      = ∏ j ∈ Finset.range (n - zkRows), (shiftSide w shifts (b a) (g c)).eval (ω ^ j) := by
        rw [← Finset.univ_product_univ, Finset.prod_product_right,
          ← Fin.prod_univ_eq_prod_range]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [shiftSide_eval]
        exact Finset.prod_congr rfl fun i _ => by ring
    _ = ∏ j ∈ Finset.range (n - zkRows), (sigmaSide w σpoly (b a) (g c)).eval (ω ^ j) :=
        hrows
    _ = ∏ x : Fin 7 × Fin (n - zkRows),
        (g c + (w x.1).eval (ω ^ (x.2 : ℕ)) + shifts (σp x).1 * ω ^ ((σp x).2 : ℕ) * b a) := by
        rw [← Finset.univ_product_univ, Finset.prod_product_right,
          ← Fin.prod_univ_eq_prod_range]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [sigmaSide_eval]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hσ (i, j)]
        ring

end Kimchi.Quotient.Permutation
