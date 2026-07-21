import Kimchi.Permutation.Copy

/-!
# The wiring instantiation: discharging the copy-soundness hypotheses

`Permutation.copy_soundness` consumes three per-index facts: injectivity of
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

namespace Kimchi.Permutation

open Kimchi.GrandProduct

open Polynomial

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
private theorem addr_injective {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) {shifts : Fin 7 → F}
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

private theorem embCell_injective : Function.Injective (embCell (n := n) zkRows) := by
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
private theorem embCell_restrictCells (σpFull : Equiv.Perm (Fin 7 × Fin n))
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

/-! ## Completeness: nondegenerate challenges and the grand-product identity -/

/-- **Challenge nondegeneracy.** No σ-side factor vanishes on ANY row: at `(β, γ)`,
every cell has `w(c) + γ + β·addr(σ c) ≠ 0`. The honest accumulator divides by these
factors — and with the three-factor `zkpm` the recurrence (hence the division) runs
through the interior zero-knowledge rows too, so the whole grid is quantified, not just
the unmasked region. Each factor is affine-linear in `(β, γ)`, so the degenerate pairs
lie on at most `7·n` lines — the small bad locus a Fiat–Shamir sample misses. The shift
side needs no such hypothesis: once the grand products agree, its nonvanishing follows
from the σ side's. -/
def Nondegenerate (ω : F) (w : Fin 7 → Polynomial F) (shifts : Fin 7 → F)
    (σpFull : Equiv.Perm (Fin 7 × Fin n)) (β γ : F) : Prop :=
  ∀ c : Fin 7 × Fin n,
    (w c.1).eval (ω ^ ((c.2 : ℕ))) + γ + β * addr ω shifts (σpFull c) ≠ 0

/-- On every row, nondegeneracy makes the σ-side row product nonzero. -/
theorem sigmaSide_eval_ne_zero {ω : F} (hω : IsPrimitiveRoot ω n)
    {w : Fin 7 → Polynomial F} {shifts : Fin 7 → F}
    {σpFull : Equiv.Perm (Fin 7 × Fin n)} {β γ : F}
    (hnd : Nondegenerate ω w shifts σpFull β γ)
    {j : ℕ} (hj : j < n) :
    (sigmaSide w (sigmaPoly ω shifts σpFull) β γ).eval (ω ^ j) ≠ 0 := by
  rw [sigmaSide_eval]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  have hs : (sigmaPoly ω shifts σpFull i).eval (ω ^ j)
      = addr ω shifts (σpFull ((i, ⟨j, hj⟩) : Fin 7 × Fin n)) := by
    rw [show (ω ^ j : F) = ω ^ (((⟨j, hj⟩ : Fin n)) : ℕ) from rfl, eval_sigmaPoly hω]
  rw [hs]
  exact hnd (i, ⟨j, hj⟩)

/-- **The grand products agree on a copy-invariant witness** — the completeness
direction of the multiset argument, by pure reindexing: with `w(σ c) = w(c)` on the
unmasked region, the σ-side factor at `c` *is* the shift-side factor at `σ c`, and the
cell product transports along the wiring permutation (`Equiv.prod_comp`). No challenge
grid and no Vandermonde content — pointwise in `(β, γ)`. -/
theorem prod_shiftSide_eq_prod_sigmaSide {ω : F} (hω : IsPrimitiveRoot ω n)
    (w : Fin 7 → Polynomial F) (shifts : Fin 7 → F)
    (σpFull : Equiv.Perm (Fin 7 × Fin n)) (hp : RegionPreserving zkRows σpFull)
    (β γ : F)
    (hcopy : ∀ c : Fin 7 × Fin (n - zkRows),
      (w (σpFull (embCell zkRows c)).1).eval
          (ω ^ (((σpFull (embCell zkRows c)).2 : Fin n) : ℕ))
        = (w c.1).eval (ω ^ ((c.2 : ℕ)))) :
    ∏ j ∈ Finset.range (n - zkRows), (shiftSide w shifts β γ).eval (ω ^ j)
      = ∏ j ∈ Finset.range (n - zkRows),
          (sigmaSide w (sigmaPoly ω shifts σpFull) β γ).eval (ω ^ j) := by
  set σp := restrictCells σpFull hp with hσp
  calc ∏ j ∈ Finset.range (n - zkRows), (shiftSide w shifts β γ).eval (ω ^ j)
      = ∏ x : Fin 7 × Fin (n - zkRows),
          ((w x.1).eval (ω ^ ((x.2 : ℕ))) + γ
            + β * (shifts x.1 * ω ^ ((x.2 : ℕ)))) := by
        rw [← Finset.univ_product_univ, Finset.prod_product_right,
          ← Fin.prod_univ_eq_prod_range]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [shiftSide_eval]
        exact Finset.prod_congr rfl fun i _ => by ring
    _ = ∏ x : Fin 7 × Fin (n - zkRows),
          ((w (σp x).1).eval (ω ^ (((σp x).2 : ℕ))) + γ
            + β * (shifts (σp x).1 * ω ^ (((σp x).2 : ℕ)))) :=
        (Equiv.prod_comp σp fun y : Fin 7 × Fin (n - zkRows) =>
          (w y.1).eval (ω ^ ((y.2 : ℕ))) + γ
            + β * (shifts y.1 * ω ^ ((y.2 : ℕ)))).symm
    _ = ∏ x : Fin 7 × Fin (n - zkRows),
          ((w x.1).eval (ω ^ ((x.2 : ℕ))) + γ
            + β * (sigmaPoly ω shifts σpFull x.1).eval (ω ^ ((x.2 : ℕ)))) := by
        refine Finset.prod_congr rfl fun x _ => ?_
        have hemb := embCell_restrictCells σpFull hp x
        have hval : (w (σp x).1).eval (ω ^ (((σp x).2 : ℕ)))
            = (w x.1).eval (ω ^ ((x.2 : ℕ))) := by
          have hc := hcopy x
          rw [← hemb] at hc
          exact hc
        have haddr : (sigmaPoly ω shifts σpFull x.1).eval (ω ^ ((x.2 : ℕ)))
            = shifts (σp x).1 * ω ^ (((σp x).2 : ℕ)) := by
          calc (sigmaPoly ω shifts σpFull x.1).eval (ω ^ ((x.2 : ℕ)))
              = addr ω shifts (σpFull (embCell zkRows x)) := by
                rw [show (ω ^ ((x.2 : ℕ)) : F)
                    = ω ^ (((embCell zkRows x).2 : Fin n) : ℕ) from rfl,
                  eval_sigmaPoly hω]
                rfl
            _ = addr ω shifts (embCell zkRows (σp x)) := by rw [hemb]
            _ = shifts (σp x).1 * ω ^ (((σp x).2 : ℕ)) := rfl
        rw [hval, haddr]
    _ = ∏ j ∈ Finset.range (n - zkRows),
          (sigmaSide w (sigmaPoly ω shifts σpFull) β γ).eval (ω ^ j) := by
        rw [← Finset.univ_product_univ, Finset.prod_product_right,
          ← Fin.prod_univ_eq_prod_range]
        exact Finset.prod_congr rfl fun j _ => (sigmaSide_eval _ _ _ _ _).symm

/-- An injection avoiding a finite bad set: `Fin m` maps injectively into `F` outside
`B` when `m + B.card ≤ |F|`. -/
private theorem exists_injective_avoiding {F : Type*} [Fintype F] [DecidableEq F]
    (B : Finset F) (m : ℕ) (hcard : m + B.card ≤ Fintype.card F) :
    ∃ f : Fin m → F, Function.Injective f ∧ ∀ i, f i ∉ B := by
  have hle : m ≤ (Finset.univ \ B).card := by
    rw [Finset.card_sdiff, Finset.card_univ, Finset.inter_univ]
    omega
  obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq hle
  let e := t.equivFinOfCardEq htcard
  refine ⟨fun i => (e.symm i : F), fun a b hab => ?_, fun i => ?_⟩
  · exact e.symm.injective (Subtype.ext hab)
  · have hmem : ((e.symm i : t) : F) ∈ t := (e.symm i).2
    exact (Finset.mem_sdiff.mp (ht hmem)).2

/-- **A nondegenerate challenge grid exists** in a large enough field. Each cell
forbids exactly one `γ` per `β` (the factor is affine-linear in `γ`), so with
`K = 7·n`: any `K + 1` distinct `β`'s, and `K + 1` distinct `γ`'s dodging the at most
`(K+1)·K` bad values, give a fully nondegenerate grid — possible once
`(K+1)² ≤ |F|`. -/
theorem exists_nondegenerate_grid {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} {ω : F}
    (w : Fin 7 → Polynomial F) (shifts : Fin 7 → F)
    (σpFull : Equiv.Perm (Fin 7 × Fin n))
    (hF : (7 * n + 1) * (7 * n + 1) ≤ Fintype.card F) :
    ∃ b g : Fin (7 * n + 1) → F,
      Function.Injective b ∧ Function.Injective g
        ∧ ∀ a c, Nondegenerate ω w shifts σpFull (b a) (g c) := by
  set K := 7 * n with hK
  obtain ⟨b, hb, -⟩ := exists_injective_avoiding (∅ : Finset F) (K + 1)
    (by simpa using le_trans (Nat.le_mul_of_pos_right _ (by omega)) hF)
  set Bad : Finset F := (Finset.univ : Finset (Fin (K + 1))).biUnion fun a =>
    (Finset.univ : Finset (Fin 7 × Fin n)).image fun c =>
      -((w c.1).eval (ω ^ ((c.2 : ℕ)))
        + b a * addr ω shifts (σpFull c)) with hBadDef
  have hBad : Bad.card ≤ (K + 1) * K := by
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ K fun a _ => ?_) ?_
    · refine le_trans Finset.card_image_le ?_
      rw [Finset.card_univ]
      simp [hK]
    · simp [Finset.card_univ, mul_comm]
  obtain ⟨g, hg, hgB⟩ := exists_injective_avoiding Bad (K + 1) (by
    calc (K + 1) + Bad.card ≤ (K + 1) + (K + 1) * K := by omega
      _ = (K + 1) * (K + 1) := by ring
      _ ≤ Fintype.card F := hF)
  refine ⟨b, g, hb, hg, fun a c cell h0 => ?_⟩
  refine hgB c ?_
  rw [hBadDef]
  refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, Finset.mem_image.mpr
    ⟨cell, Finset.mem_univ cell, ?_⟩⟩
  linear_combination -h0

/-! ## Executable row forms and certificates

The fixture check (`scripts/check_perm_fixture.lean`) replays the argument on production
data. So that it exercises *these* definitions rather than a parallel copy, the row-level
forms and the hypothesis certificates live here, each with a proved bridge: the row forms
are the polynomial definitions evaluated (`shiftSide_eval_row`/`sigmaSide_eval_row`), and
the decidable certificates imply the specification `Prop`s
(`cosetShifts_of_certificate`, `isPrimitiveRoot_of_certificate`). -/

/-- The shift-side row factor product, executably: `∏ᵢ (wᵢ + γ + β·shiftᵢ·x)` over row
values. -/
def shiftSideRow (wRow : Fin 7 → F) (shifts : Fin 7 → F) (β γ x : F) : F :=
  ∏ i, (wRow i + γ + β * shifts i * x)

/-- The σ-side row factor product, executably: `∏ᵢ (wᵢ + γ + β·σᵢ)` over row values. -/
def sigmaSideRow (wRow σRow : Fin 7 → F) (β γ : F) : F :=
  ∏ i, (wRow i + γ + β * σRow i)

private theorem shiftSide_eval_row (w : Fin 7 → Polynomial F) (shifts : Fin 7 → F) (β γ x : F) :
    (shiftSide w shifts β γ).eval x
      = shiftSideRow (fun i => (w i).eval x) shifts β γ x :=
  shiftSide_eval w shifts β γ x

private theorem sigmaSide_eval_row (w σ : Fin 7 → Polynomial F) (β γ x : F) :
    (sigmaSide w σ β γ).eval x
      = sigmaSideRow (fun i => (w i).eval x) (fun i => (σ i).eval x) β γ :=
  sigmaSide_eval w σ β γ x

/-- The decidable coset certificate: nonzero shifts whose pairwise ratios are not `n`-th
roots of unity. -/
def cosetShiftsCertificate [DecidableEq F] (shifts : Fin 7 → F) (n : ℕ) : Bool :=
  decide ((∀ i, shifts i ≠ 0)
    ∧ ∀ i j : Fin 7, i ≠ j → (shifts i * (shifts j)⁻¹) ^ n ≠ 1)

/-- The certificate implies the coset specification: a relation `shiftᵢ = shiftⱼ·ωᵉ`
raises to `(shiftᵢ/shiftⱼ)ⁿ = (ωⁿ)ᵉ = 1`, which the certificate excludes off the
diagonal. -/
theorem cosetShifts_of_certificate [DecidableEq F] {ω : F} {n : ℕ}
    (hω : IsPrimitiveRoot ω n) {shifts : Fin 7 → F}
    (h : cosetShiftsCertificate shifts n = true) : CosetShifts ω shifts := by
  rw [cosetShiftsCertificate, decide_eq_true_eq] at h
  refine ⟨h.1, fun i j e heq => ?_⟩
  by_contra hij
  refine h.2 i j hij ?_
  rw [heq, mul_comm (shifts j), mul_assoc, mul_inv_cancel₀ (h.1 j), mul_one, ← pow_mul,
    mul_comm e n, pow_mul, hω.pow_eq_one, one_pow]

/-- The decidable primitive-root certificate for two-power orders: `ωⁿ = 1` and
`ω^(n/2) ≠ 1`. -/
def primitiveRootCertificate [DecidableEq F] (ω : F) (n : ℕ) : Bool :=
  decide (ω ^ n = 1 ∧ ω ^ (n / 2) ≠ 1)

/-- For `n = 2^k`, the certificate implies primitivity: the order of `ω` divides `2^k`,
hence is a two-power; were it proper it would divide `n/2`, contradicting the
certificate. -/
theorem isPrimitiveRoot_of_certificate [DecidableEq F] {ω : F} {n k : ℕ}
    (hn : n = 2 ^ k) (h : primitiveRootCertificate ω n = true) :
    IsPrimitiveRoot ω n := by
  rw [primitiveRootCertificate, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hd : orderOf ω ∣ n := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨m, hm, hordm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hn ▸ hd)
  have hmk : m = k := by
    by_contra hne
    have hmlt : m < k := lt_of_le_of_ne hm hne
    have hhalf : n / 2 = 2 ^ (k - 1) := by
      rw [hn, show k = (k - 1) + 1 by omega, pow_succ]
      exact Nat.mul_div_cancel _ two_pos
    refine h2 (orderOf_dvd_iff_pow_eq_one.mp ?_)
    rw [hhalf, hordm]
    exact pow_dvd_pow 2 (by omega)
  have hord : orderOf ω = n := by rw [hordm, hmk, hn]
  exact hord ▸ IsPrimitiveRoot.orderOf ω

/-- The certificate with the two-power fact existential — the form a deserializer
decides. -/
theorem isPrimitiveRoot_of_certificate' [DecidableEq F] {ω : F} {n : ℕ}
    (hn : ∃ k, n = 2 ^ k) (h : primitiveRootCertificate ω n = true) :
    IsPrimitiveRoot ω n := by
  obtain ⟨k, hk⟩ := hn
  exact isPrimitiveRoot_of_certificate hk h

/-! ## The headline -/

/-- **Copy soundness from the index data, divisibility form.** For coset shifts, a
region-preserving full-grid wiring, and sigma columns interpolating the wired-to
addresses: if at every node of an injective `(β, γ)` grid the prover supplies an
accumulator whose three permutation constraints are divisible by `Z_H`, then the witness
takes equal values across every wire of the unmasked region. -/
theorem copy_soundness_wired_of_dvd [DecidableEq F] {ω : F} (hω : IsPrimitiveRoot ω n)
    (hn : 0 < n) (hzk2 : 2 ≤ zkRows) (hzkn : zkRows ≤ n)
    (w : Fin 7 → Polynomial F) (shifts : Fin 7 → F) (hs : CosetShifts ω shifts)
    (σpFull : Equiv.Perm (Fin 7 × Fin n)) (hp : RegionPreserving zkRows σpFull)
    (β γ : F)
    (hβ : β ∉ badBetas
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)), shifts c.1 * ω ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)),
          shifts (restrictCells σpFull hp c).1
            * ω ^ ((restrictCells σpFull hp c).2 : ℕ))))
    (hγ : γ ∉ badGammas
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)), shifts c.1 * ω ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin 7 × Fin (n - zkRows) =>
        ((w c.1).eval (ω ^ (c.2 : ℕ)),
          shifts (restrictCells σpFull hp c).1
            * ω ^ ((restrictCells σpFull hp c).2 : ℕ))) β)
    (zg : Polynomial F)
    (hdvd : ∀ s, zH F n ∣ constraints ω zkRows zg w
      (sigmaPoly ω shifts σpFull) shifts β γ
      (⟨0, hn⟩ : Fin n) ⟨n - zkRows, by omega⟩ s) :
    ∀ c : Fin 7 × Fin (n - zkRows),
      (w (σpFull (embCell zkRows c)).1).eval (ω ^ ((σpFull (embCell zkRows c)).2 : ℕ))
        = (w c.1).eval (ω ^ (c.2 : ℕ)) := by
  intro c
  have hmain := Permutation.copy_soundness_of_dvd hω hn hzk2 hzkn w
    (sigmaPoly ω shifts σpFull) shifts (restrictCells σpFull hp)
    (fun x y hxy => embCell_injective (addr_injective hω hs (by
      simpa [addr, embCell] using hxy)))
    (fun x => by
      rw [show ω ^ ((x.2 : ℕ)) = ω ^ (((embCell zkRows x).2 : Fin n) : ℕ) from rfl,
        eval_sigmaPoly hω shifts σpFull, show ((x.1 : Fin 7), (embCell zkRows x).2)
          = embCell zkRows x from rfl,
        ← embCell_restrictCells σpFull hp x]
      rfl)
    β γ hβ hγ zg hdvd c
  rw [← embCell_restrictCells σpFull hp c]
  exact hmain
end Kimchi.Permutation
