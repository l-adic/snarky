import Kimchi.Quotient.GrandProduct
import Kimchi.Quotient.Permutation
import Kimchi.Quotient.SchwartzZippel

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
  `σp c`. The single-challenge form feeds `multiset_eq_of_prod_eval` (the grand-product
  Schwartz–Zippel core) with the product equality at one good pair `(β, γ)` and descends.

* **The kimchi headline** (`Permutation.copy_soundness`): the per-challenge
  quotient-argument hypotheses — at a single good challenge pair `(β, γ)` the prover supplies an
  accumulator `zg` and the three permutation constraints pass the derandomized
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
private theorem values_eq_of_multiset_eq {cells : Type*} [Fintype cells]
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
agreeing at a **single good challenge pair** `(β, γ)` — own addresses on the left,
wired-to addresses on the right — force the values to be invariant under the wiring.
The single-challenge Schwartz–Zippel core (`multiset_eq_of_prod_eval`) turns the product
equality into multiset equality once `β` and `γ` avoid the proved-small bad sets
`badBetas`/`badGammas` of the `(value, address)` pair multisets; injective addressing then
descends to the values. -/
theorem copy_soundness [DecidableEq F] {cells : Type*} [Fintype cells]
    (β γ : F)
    (v addr : cells → F) (haddr : Function.Injective addr) (σp : Equiv.Perm cells)
    (hβ : β ∉ badBetas (Finset.univ.val.map fun c => (v c, addr c))
      (Finset.univ.val.map fun c => (v c, addr (σp c))))
    (hγ : γ ∉ badGammas (Finset.univ.val.map fun c => (v c, addr c))
      (Finset.univ.val.map fun c => (v c, addr (σp c))) β)
    (h : ∏ c, (γ + v c + addr c * β) = ∏ c, (γ + v c + addr (σp c) * β)) :
    ∀ c, v (σp c) = v c := by
  refine values_eq_of_multiset_eq v addr haddr σp
    (multiset_eq_of_prod_eval _ _ β γ hβ hγ ?_)
  rw [Multiset.map_map, Multiset.map_map]
  simpa only [Function.comp_def, ← Finset.prod_eq_multiset_prod] using h

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
    {zkRows : ℕ} (hzk0 : 0 < zkRows) (hzkn : zkRows ≤ n)
    (w σpoly : Fin 7 → Polynomial F) (shifts : Fin 7 → F)
    (σp : Equiv.Perm (Fin 7 × Fin (n - zkRows)))
    (haddr : Function.Injective
      (fun c : Fin 7 × Fin (n - zkRows) => shifts c.1 * ω ^ (c.2 : ℕ)))
    (hσ : ∀ c : Fin 7 × Fin (n - zkRows),
      (σpoly c.1).eval (ω ^ (c.2 : ℕ)) = shifts (σp c).1 * ω ^ ((σp c).2 : ℕ))
    (β γ : F)
    (hβ : β ∉ badBetas
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)), shifts c.1 * ω ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)), shifts (σp c).1 * ω ^ ((σp c).2 : ℕ))))
    (hγ : γ ∉ badGammas
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)), shifts c.1 * ω ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)), shifts (σp c).1 * ω ^ ((σp c).2 : ℕ))) β)
    (zg : Polynomial F)
    (hdvd : ∀ s, zH F n ∣ constraints ω zkRows zg w σpoly shifts
      β γ (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩ s) :
    ∀ c : Fin 7 × Fin (n - zkRows),
      (w (σp c).1).eval (ω ^ ((σp c).2 : ℕ)) = (w c.1).eval (ω ^ (c.2 : ℕ)) := by
  -- The field-level core at the cell data.
  refine Kimchi.Quotient.copy_soundness β γ _ _ haddr σp hβ hγ ?_
  -- The grand-product argument gives the row-product equality; reindex rows × columns to cells and
  -- rewrite the sigma side through the wiring semantics.
  have hrows := Permutation.soundness_of_dvd hω hn hzk0 hzkn zg w σpoly shifts β γ hdvd
  calc ∏ x : Fin 7 × Fin (n - zkRows),
        (γ + (w x.1).eval (ω ^ (x.2 : ℕ)) + shifts x.1 * ω ^ (x.2 : ℕ) * β)
      = ∏ j ∈ Finset.range (n - zkRows), (shiftSide w shifts β γ).eval (ω ^ j) := by
        rw [← Finset.univ_product_univ, Finset.prod_product_right,
          ← Fin.prod_univ_eq_prod_range]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [shiftSide_eval]
        exact Finset.prod_congr rfl fun i _ => by ring
    _ = ∏ j ∈ Finset.range (n - zkRows), (sigmaSide w σpoly β γ).eval (ω ^ j) :=
        hrows
    _ = ∏ x : Fin 7 × Fin (n - zkRows),
        (γ + (w x.1).eval (ω ^ (x.2 : ℕ)) + shifts (σp x).1 * ω ^ ((σp x).2 : ℕ) * β) := by
        rw [← Finset.univ_product_univ, Finset.prod_product_right,
          ← Fin.prod_univ_eq_prod_range]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [sigmaSide_eval]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hσ (i, j)]
        ring

/-- **Copy soundness of the kimchi permutation argument.** As `copy_soundness_of_dvd`,
with the divisibilities obtained from the derandomized quotient checks in
**single-challenge counting Schwartz–Zippel form** (`dvd_of_evalCheck`): the prover
supplies ONE aggregation challenge `α` (avoiding the proved-small bad set `badAlphas`) and
ONE quotient `t`, at a single good permutation-challenge pair `(β, γ)`, and evaluates the
quotient check at a single good challenge `ζ` outside the counting bad set
`badZetas (aggregate α C) t n`. Conclusion unchanged. -/
theorem copy_soundness [DecidableEq F] {ω : F} {n : ℕ}
    (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    {zkRows : ℕ} (hzk0 : 0 < zkRows) (hzkn : zkRows ≤ n)
    (w σpoly : Fin 7 → Polynomial F) (shifts : Fin 7 → F)
    (σp : Equiv.Perm (Fin 7 × Fin (n - zkRows)))
    (haddr : Function.Injective
      (fun c : Fin 7 × Fin (n - zkRows) => shifts c.1 * ω ^ (c.2 : ℕ)))
    (hσ : ∀ c : Fin 7 × Fin (n - zkRows),
      (σpoly c.1).eval (ω ^ (c.2 : ℕ)) = shifts (σp c).1 * ω ^ ((σp c).2 : ℕ))
    (β γ : F)
    (hβ : β ∉ badBetas
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)), shifts c.1 * ω ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)), shifts (σp c).1 * ω ^ ((σp c).2 : ℕ))))
    (hγ : γ ∉ badGammas
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)), shifts c.1 * ω ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)), shifts (σp c).1 * ω ^ ((σp c).2 : ℕ))) β)
    (zg : Polynomial F)
    (α : F)
    (hα : α ∉ badAlphas (constraints ω zkRows zg w σpoly shifts
      β γ (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩) ω n)
    (t : Polynomial F)
    (ζ : F)
    (hζ : ζ ∉ badZetas (aggregate α (constraints ω zkRows zg w σpoly shifts
      β γ (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩)) t n)
    (hcheck : (aggregate α (constraints ω zkRows zg w σpoly shifts
        β γ (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩)).eval ζ
      = (t * zH F n).eval ζ) :
    ∀ c : Fin 7 × Fin (n - zkRows),
      (w (σp c).1).eval (ω ^ ((σp c).2 : ℕ)) = (w c.1).eval (ω ^ (c.2 : ℕ)) :=
  have : NeZero n := ⟨hn.ne'⟩
  copy_soundness_of_dvd hω hn hzk0 hzkn w σpoly shifts σp haddr hσ β γ hβ hγ zg
    (dvd_of_evalCheck hω _ α hα t ζ hζ hcheck)

end Kimchi.Quotient.Permutation
