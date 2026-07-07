import Kimchi.Quotient.Copy

/-!
# The wiring instantiation: discharging the copy-soundness hypotheses

Milestone 4's `Permutation.copy_soundness` consumes three per-index facts: injectivity of
the cell addressing, the row semantics of the sigma polynomials, and a wiring permutation
of the unmasked region. This file produces all three from the data a kimchi index
actually carries:

* **Addressing** (`addr`, `addr_injective`): a cell `(i, j)` of the full `7 × n` grid has
  the address `shiftᵢ · ωʲ`. Injectivity follows from the shifts being nonzero and
  representing *distinct cosets* of `⟨ω⟩` (`CosetShifts` — the specification kimchi's
  `Shifts::new` sampling enforces: `shiftᵢ = shiftⱼ · ωᵉ` only for `i = j`).

* **The wiring** (`restrictCells`): the index wires the full grid, and kimchi's wiring
  never crosses into the zero-knowledge rows; a full-grid permutation preserving the
  unmasked region (`RegionPreserving`) restricts to a permutation of the unmasked cells,
  intertwining the embedding (`embCell_restrictCells`).

* **The sigma columns** (`sigmaPoly`, `eval_sigmaPoly`): the index's sigma polynomials
  are the interpolants of the wired-to addresses (`columnPoly` through the domain), so
  their row semantics is definitional on the whole domain.

The headline `Permutation.copy_soundness_wired` composes these through milestone 4: for
an index — coset shifts, a region-preserving wiring, interpolated sigma columns — and a
grid of accepted quotient checks, the witness takes equal values across every wire of
the unmasked region.
-/

namespace Kimchi.Quotient.Permutation

open Polynomial Kimchi.Quotient

variable {F : Type*} [Field F]

/-! ## Addressing -/

/-- The address of a cell of the full grid: column `i`, row `j` lives at `shiftᵢ · ωʲ`. -/
def addr {n : ℕ} (ω : F) (shifts : Fin 7 → F) (c : Fin 7 × Fin n) : F :=
  shifts c.1 * ω ^ (c.2 : ℕ)

/-- The coset specification of the shifts (`Shifts::new`): each is nonzero, and they
represent pairwise-distinct cosets of `⟨ω⟩` — one shift is a `⟨ω⟩`-multiple of another
only trivially. -/
structure CosetShifts (ω : F) (shifts : Fin 7 → F) : Prop where
  ne_zero : ∀ i, shifts i ≠ 0
  coset_distinct : ∀ i j : Fin 7, ∀ e : ℕ, shifts i = shifts j * ω ^ e → i = j

/-- **Cell addresses are injective.** Distinct cosets separate the columns; primitive-root
power injectivity separates the rows within a coset. -/
theorem addr_injective {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) {shifts : Fin 7 → F}
    (hs : CosetShifts ω shifts) :
    Function.Injective (addr (n := n) ω shifts) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  simp only [addr] at h
  have hn : 0 < n := a.pos
  -- Cancel `ω^a`: `shiftᵢ = shiftⱼ · ω^(b + (n − a))`, so the columns agree.
  have hunit : ω ^ (a : ℕ) * ω ^ (n - (a : ℕ)) = 1 := by
    rw [← pow_add, Nat.add_sub_cancel' a.isLt.le, hω.pow_eq_one]
  have hcol : i = j := by
    refine hs.coset_distinct i j ((b : ℕ) + (n - (a : ℕ))) ?_
    calc shifts i = shifts i * (ω ^ (a : ℕ) * ω ^ (n - (a : ℕ))) := by rw [hunit, mul_one]
      _ = shifts j * ω ^ (b : ℕ) * ω ^ (n - (a : ℕ)) := by rw [← mul_assoc, h]
      _ = shifts j * ω ^ ((b : ℕ) + (n - (a : ℕ))) := by rw [mul_assoc, ← pow_add]
  subst hcol
  -- Cancel the shift: `ωᵃ = ωᵇ`, so the rows agree.
  have hrow : (a : ℕ) = (b : ℕ) :=
    hω.pow_inj a.isLt b.isLt (mul_left_cancel₀ (hs.ne_zero i) h)
  exact Prod.ext rfl (Fin.ext hrow)

/-! ## The wiring -/

variable {n zkRows : ℕ}

/-- The embedding of the unmasked cells into the full grid. -/
def embCell (zkRows : ℕ) (c : Fin 7 × Fin (n - zkRows)) : Fin 7 × Fin n :=
  (c.1, ⟨(c.2 : ℕ), lt_of_lt_of_le c.2.isLt (Nat.sub_le n zkRows)⟩)

theorem embCell_injective : Function.Injective (embCell (n := n) zkRows) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  simp only [embCell, Prod.mk.injEq, Fin.mk.injEq] at h
  exact Prod.ext h.1 (Fin.ext h.2)

/-- A full-grid wiring that never crosses the zero-knowledge boundary: a cell is unmasked
iff its image is. -/
def RegionPreserving (zkRows : ℕ) (σpFull : Equiv.Perm (Fin 7 × Fin n)) : Prop :=
  ∀ c : Fin 7 × Fin n, ((c.2 : ℕ) < n - zkRows) ↔ (((σpFull c).2 : ℕ) < n - zkRows)

/-- The restriction of a region-preserving full-grid wiring to the unmasked cells. -/
def restrictCells (σpFull : Equiv.Perm (Fin 7 × Fin n))
    (hp : RegionPreserving zkRows σpFull) : Equiv.Perm (Fin 7 × Fin (n - zkRows)) where
  toFun c := ((σpFull (embCell zkRows c)).1,
    ⟨((σpFull (embCell zkRows c)).2 : ℕ), (hp _).mp c.2.isLt⟩)
  invFun c := ((σpFull.symm (embCell zkRows c)).1,
    ⟨((σpFull.symm (embCell zkRows c)).2 : ℕ), by
      have h := (hp (σpFull.symm (embCell zkRows c))).mpr
      rw [Equiv.apply_symm_apply] at h
      exact h c.2.isLt⟩)
  left_inv c := by
    have hemb : ∀ (x : Fin 7 × Fin n) (h : (x.2 : ℕ) < n - zkRows),
        embCell (n := n) zkRows (x.1, ⟨(x.2 : ℕ), h⟩) = x :=
      fun x h => Prod.ext rfl (Fin.ext rfl)
    simp only [hemb, Equiv.symm_apply_apply]
    exact Prod.ext rfl (Fin.ext rfl)
  right_inv c := by
    have hemb : ∀ (x : Fin 7 × Fin n) (h : (x.2 : ℕ) < n - zkRows),
        embCell (n := n) zkRows (x.1, ⟨(x.2 : ℕ), h⟩) = x :=
      fun x h => Prod.ext rfl (Fin.ext rfl)
    simp only [hemb, Equiv.apply_symm_apply]
    exact Prod.ext rfl (Fin.ext rfl)

/-- The restriction intertwines the embedding: restricting and then embedding is the full
wiring on embedded cells. -/
theorem embCell_restrictCells (σpFull : Equiv.Perm (Fin 7 × Fin n))
    (hp : RegionPreserving zkRows σpFull) (c : Fin 7 × Fin (n - zkRows)) :
    embCell zkRows (restrictCells σpFull hp c) = σpFull (embCell zkRows c) :=
  Prod.ext rfl (Fin.ext rfl)

/-! ## The sigma columns -/

/-- The index's sigma polynomials: the interpolants, through the domain, of the wired-to
addresses. -/
noncomputable def sigmaPoly (ω : F) (shifts : Fin 7 → F)
    (σpFull : Equiv.Perm (Fin 7 × Fin n)) : Fin 7 → Polynomial F :=
  fun i => columnPoly ω (fun j : Fin n => addr ω shifts (σpFull (i, j)))

/-- The sigma columns' row semantics, on the whole domain. -/
theorem eval_sigmaPoly {ω : F} (hω : IsPrimitiveRoot ω n) (shifts : Fin 7 → F)
    (σpFull : Equiv.Perm (Fin 7 × Fin n)) (i : Fin 7) (j : Fin n) :
    (sigmaPoly ω shifts σpFull i).eval (ω ^ (j : ℕ)) = addr ω shifts (σpFull (i, j)) :=
  eval_columnPoly hω _ j

/-! ## The headline -/

/-- **Copy soundness from the index data.** For coset shifts, a region-preserving
full-grid wiring, and sigma columns interpolating the wired-to addresses: if at every
node of an injective `(β, γ)` grid the prover supplies an accumulator passing the
derandomized quotient checks of the three permutation constraints, then the witness
takes equal values across every wire of the unmasked region. -/
theorem copy_soundness_wired {ω : F} {NN : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (hzk0 : 0 < zkRows) (hzkn : zkRows ≤ n)
    (w : Fin 7 → Polynomial F) (shifts : Fin 7 → F) (hs : CosetShifts ω shifts)
    (σpFull : Equiv.Perm (Fin 7 × Fin n)) (hp : RegionPreserving zkRows σpFull)
    {M N : ℕ} (b : Fin M → F) (g : Fin N → F)
    (hb : Function.Injective b) (hg : Function.Injective g)
    (hM : 7 * (n - zkRows) < M) (hN : 7 * (n - zkRows) < N)
    (zg : Fin M → Fin N → Polynomial F)
    (α : Fin M → Fin N → Fin 3 → F) (hα : ∀ a c, Function.Injective (α a c))
    (ζ : Fin M → Fin N → Fin NN → F) (hζ : ∀ a c, Function.Injective (ζ a c))
    (t : Fin M → Fin N → Fin 3 → Polynomial F) (D : ℕ) (hD : D < NN)
    (hCdeg : ∀ a c s, (aggregate (α a c s) (constraints ω zkRows (zg a c) w
      (sigmaPoly ω shifts σpFull) shifts (b a) (g c)
      (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩)).natDegree ≤ D)
    (htdeg : ∀ a c s, (t a c s * zH F n).natDegree ≤ D)
    (hcheck : ∀ a c s p, (aggregate (α a c s) (constraints ω zkRows (zg a c) w
        (sigmaPoly ω shifts σpFull) shifts (b a) (g c)
        (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩)).eval (ζ a c p)
      = (t a c s * zH F n).eval (ζ a c p)) :
    ∀ c : Fin 7 × Fin (n - zkRows),
      (w (σpFull (embCell zkRows c)).1).eval (ω ^ ((σpFull (embCell zkRows c)).2 : ℕ))
        = (w c.1).eval (ω ^ (c.2 : ℕ)) := by
  intro c
  have hmain := Permutation.copy_soundness hω hn hzk0 hzkn w
    (sigmaPoly ω shifts σpFull) shifts (restrictCells σpFull hp)
    (fun x y hxy => embCell_injective (addr_injective hω hs (by
      simpa [addr, embCell] using hxy)))
    (fun x => by
      rw [show ω ^ ((x.2 : ℕ)) = ω ^ (((embCell zkRows x).2 : Fin n) : ℕ) from rfl,
        eval_sigmaPoly hω shifts σpFull, show ((x.1 : Fin 7), (embCell zkRows x).2)
          = embCell zkRows x from rfl,
        ← embCell_restrictCells σpFull hp x]
      rfl)
    b g hb hg hM hN zg α hα ζ hζ t D hD hCdeg htdeg hcheck c
  rw [← embCell_restrictCells σpFull hp c]
  exact hmain

end Kimchi.Quotient.Permutation
