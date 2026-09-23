import Mathlib

/-!
# The grand-product core: linear-factor multisets

Polynomial algebra for the kimchi permutation argument (proof-systems `permutation.rs`). The
permutation accumulator telescopes into an equality of grand products
`∏ (wᵢ + β·posᵢ + γ) = ∏ (wᵢ + β·σ(pos)ᵢ + γ)`; this module proves that such an equality, at one
`(β, γ)` outside two explicit finite sets, forces the multisets of pairs `(wᵢ, posᵢ)` to
coincide. No domain, root of unity or gate appears, and the only import is Mathlib.

Every result is an implication about explicit challenges outside finite sets whose sizes are
proved; no probability or hardness assumption enters.

The pair `(w, a)` gives the pair factor `γ + w + a·β`, a monic linear polynomial in `γ` over
`F[β]`, modelled as `Polynomial (Polynomial F)` with outer variable `γ` and inner variable `β`.

## Contents

* `badBetas` / `badGammas`, with `card_badBetas_le` / `card_badGammas_le`: the bad challenge
  sets, each of size at most `max |m₁| |m₂|`.
* `copy_soundness`: products over the cells agreeing at one good `(β, γ)` force the values to be
  invariant under the wiring.
* `prod_eq_of_accumulator` / `accumulator_of_prod_eq`: an accumulator pinned to `1` at both ends
  telescopes into a grand-product equality, and conversely.
-/

namespace Kimchi.GrandProduct

open Polynomial

variable {F : Type*} [Field F]

/-! ## The pair factor and two-variable evaluation -/

/-- The pair factor `γ + p.1 + p.2·β` of `p`: the outer `X` is `γ`, the inner `X` is `β`. -/
private noncomputable def pairFactor (p : F × F) : Polynomial (Polynomial F) :=
  Polynomial.X + Polynomial.C (Polynomial.C p.1 + Polynomial.C p.2 * Polynomial.X)

/-- The value of `P` at `β = b`, `γ = g`: outer variable first, then inner. -/
private noncomputable def eval2 (b g : F) (P : Polynomial (Polynomial F)) : F :=
  (P.eval (Polynomial.C g)).eval b

/-! ## The core: equal products force equal multisets -/

/-- Equal products of pair factors force equal multisets: each factor is `X - C r` with `r`
injective in the pair, so the root multisets agree. -/
private theorem multiset_eq_of_pairFactor_prod_eq (m₁ m₂ : Multiset (F × F))
    (h : (m₁.map pairFactor).prod = (m₂.map pairFactor).prod) : m₁ = m₂ := by
  -- `r p` is the (negated) constant so that `pairFactor p = X - C (r p)`.
  set r : F × F → Polynomial F :=
    fun p => -(Polynomial.C p.1 + Polynomial.C p.2 * Polynomial.X) with hr
  -- Each pair factor is a monic linear factor `X - C (r p)`.
  have hpf : pairFactor = fun p : F × F => Polynomial.X - Polynomial.C (r p) := by
    funext p
    simp only [pairFactor, hr, map_neg, sub_neg_eq_add]
  -- `r` is injective: recover `p.1, p.2` from the degree-0,1 coefficients.
  have hrinj : Function.Injective r := by
    intro p q hpq
    have h0 : Polynomial.C p.1 + Polynomial.C p.2 * Polynomial.X
            = Polynomial.C q.1 + Polynomial.C q.2 * Polynomial.X := by
      simpa only [hr, neg_inj] using hpq
    have e0 : p.1 = q.1 := by
      have := congrArg (fun t => Polynomial.coeff t 0) h0
      simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_zero] using this
    have e1 : p.2 = q.2 := by
      have := congrArg (fun t => Polynomial.coeff t 1) h0
      simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_one, Polynomial.coeff_C] using this
    exact Prod.ext e0 e1
  -- Rewrite both products as products of `X - C c` over the mapped multisets.
  rw [hpf] at h
  rw [show (fun p : F × F => Polynomial.X - Polynomial.C (r p))
        = (fun c => Polynomial.X - Polynomial.C c) ∘ r from rfl,
     ← Multiset.map_map, ← Multiset.map_map] at h
  -- Root multisets coincide, hence `m₁.map r = m₂.map r`.
  have hroots : m₁.map r = m₂.map r := by
    have := congrArg Polynomial.roots h
    rwa [Polynomial.roots_multiset_prod_X_sub_C,
      Polynomial.roots_multiset_prod_X_sub_C] at this
  exact Multiset.map_injective hrinj hroots

/-! ## Evaluation and degree bounds -/

/-- `eval2 b g` is evaluation at `g` after specialising every coefficient at `β = b`. -/
private lemma eval2_eq_eval_map (b g : F) (P : Polynomial (Polynomial F)) :
    eval2 b g P = (P.map (Polynomial.evalRingHom b)).eval g := by
  rw [eval2, Polynomial.eval_map]
  rw [show P.eval (Polynomial.C g)
        = Polynomial.eval₂ (RingHom.id (Polynomial F)) (Polynomial.C g) P from by
        rw [Polynomial.eval₂_id]]
  rw [← Polynomial.coe_evalRingHom, Polynomial.hom_eval₂]
  simp

/-- The pair-factor product evaluates at `(b, g)` to the field product `∏ (g + p.1 + p.2·b)`. -/
private lemma eval2_prod_pairFactor (b g : F) (m : Multiset (F × F)) :
    eval2 b g (m.map pairFactor).prod = (m.map (fun p => g + p.1 + p.2 * b)).prod := by
  -- `eval2 b g` is the ring hom `(evalRingHom b).comp (evalRingHom (C g))`.
  show ((Polynomial.evalRingHom b).comp (Polynomial.evalRingHom (Polynomial.C g)))
      (m.map pairFactor).prod = _
  rw [map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl ?_
  intro p _
  simp only [Function.comp_apply, RingHom.comp_apply, Polynomial.coe_evalRingHom,
    pairFactor, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul]
  ring

/-- The pair-factor product has outer degree at most `|m|`. -/
private lemma natDegree_prod_pairFactor (m : Multiset (F × F)) :
    (m.map pairFactor).prod.natDegree ≤ Multiset.card m := by
  refine le_trans (Polynomial.natDegree_multiset_prod_le _) ?_
  rw [Multiset.map_map]
  have hconst : m.map (Polynomial.natDegree ∘ pairFactor) = m.map (fun _ => 1) := by
    refine Multiset.map_congr rfl ?_
    intro p _
    simp only [Function.comp_apply, pairFactor]
    exact Polynomial.natDegree_X_add_C _
  rw [hconst]
  simp

/-- Every coefficient of the pair-factor product has inner degree at most `|m|`: each factor
raises it by at most one. -/
private lemma natDegree_coeff_prod_pairFactor (m : Multiset (F × F)) :
    ∀ k, ((m.map pairFactor).prod.coeff k).natDegree ≤ Multiset.card m := by
  induction m using Multiset.induction with
  | empty =>
    intro k
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, Nat.le_zero,
      Polynomial.coeff_one]
    split <;> simp
  | cons p m' ih =>
    intro k
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    set P := (m'.map pairFactor).prod with hP
    -- `pairFactor p = X + C r`, with `r := C p.1 + C p.2 * X` of inner degree ≤ 1.
    show (((Polynomial.X + Polynomial.C (Polynomial.C p.1 + Polynomial.C p.2 * Polynomial.X))
        * P).coeff k).natDegree ≤ Multiset.card m' + 1
    rw [add_mul, Polynomial.coeff_add]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · -- `(X * P).coeff k`
      rcases k with _ | j
      · simp
      · rw [Polynomial.coeff_X_mul]
        exact le_trans (ih j) (Nat.le_succ _)
    · -- `(C r * P).coeff k = r * P.coeff k`
      rw [Polynomial.coeff_C_mul]
      refine le_trans Polynomial.natDegree_mul_le ?_
      have hr : (Polynomial.C p.1 + Polynomial.C p.2 * Polynomial.X).natDegree ≤ 1 := by
        refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
        · simp
        · exact le_trans Polynomial.natDegree_mul_le (by simp)
      have := ih k
      omega

/-! ## Counting Schwartz–Zippel for `β` and `γ`

`Δ` is the difference of the two pair-factor products. A bad `β` is a root of `Δ`'s leading
coefficient in `γ`; a bad `γ`, given `β`, is a root of `Δ` specialised at `β`. Both sets are
empty when `m₁ = m₂`. The same shape as `dvd_separation`'s single-challenge `α`.
-/

/-- `Δ`, the difference of the two pair-factor products; it vanishes only when `m₁ = m₂`
(`multiset_eq_of_pairFactor_prod_eq`). -/
private noncomputable def gpDiff (m₁ m₂ : Multiset (F × F)) : Polynomial (Polynomial F) :=
  (m₁.map pairFactor).prod - (m₂.map pairFactor).prod

section
variable [DecidableEq F]

/-- The bad `β`s: the roots of `Δ`'s leading coefficient in `γ`, or empty when `m₁ = m₂`. -/
noncomputable def badBetas (m₁ m₂ : Multiset (F × F)) : Finset F :=
  if m₁ = m₂ then ∅ else (gpDiff m₁ m₂).leadingCoeff.roots.toFinset

/-- At most `max |m₁| |m₂|` bad `β`s: the leading coefficient is a coefficient of `Δ`, of inner
degree at most that (`natDegree_coeff_prod_pairFactor`). -/
theorem card_badBetas_le (m₁ m₂ : Multiset (F × F)) :
    (badBetas m₁ m₂).card ≤ max (Multiset.card m₁) (Multiset.card m₂) := by
  have hcoeff : ∀ k, ((gpDiff m₁ m₂).coeff k).natDegree
      ≤ max (Multiset.card m₁) (Multiset.card m₂) := by
    intro k
    unfold gpDiff
    rw [Polynomial.coeff_sub]
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    exact max_le_max (natDegree_coeff_prod_pairFactor m₁ k) (natDegree_coeff_prod_pairFactor m₂ k)
  unfold badBetas
  split_ifs with h
  · simp
  · refine le_trans (Multiset.toFinset_card_le _) ?_
    refine le_trans (Polynomial.card_roots' _) ?_
    exact hcoeff _

/-- The bad `γ`s at `β`: the roots of `Δ` specialised at `β`, or empty when `m₁ = m₂`. The
specialisation is nonzero when `β ∉ badBetas`. -/
noncomputable def badGammas (m₁ m₂ : Multiset (F × F)) (β : F) : Finset F :=
  if m₁ = m₂ then ∅ else ((gpDiff m₁ m₂).map (Polynomial.evalRingHom β)).roots.toFinset

/-- At most `max |m₁| |m₂|` bad `γ`s for every `β`: specialising does not raise the outer degree,
which `natDegree_prod_pairFactor` bounds. -/
theorem card_badGammas_le (m₁ m₂ : Multiset (F × F)) (β : F) :
    (badGammas m₁ m₂ β).card ≤ max (Multiset.card m₁) (Multiset.card m₂) := by
  unfold badGammas
  split_ifs with h
  · simp
  · refine le_trans (Multiset.toFinset_card_le _) ?_
    refine le_trans (Polynomial.card_roots' _) ?_
    refine le_trans Polynomial.natDegree_map_le ?_
    unfold gpDiff
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    exact max_le_max (natDegree_prod_pairFactor m₁) (natDegree_prod_pairFactor m₂)

/-- Field products `∏ (γ + p.1 + p.2·β)` over `m₁` and `m₂` agreeing at one `(β, γ)` outside
`badBetas` and `badGammas` force `m₁ = m₂`. Stepped through in the body. -/
private theorem multiset_eq_of_prod_eval (m₁ m₂ : Multiset (F × F)) (β γ : F)
    (hβ : β ∉ badBetas m₁ m₂) (hγ : γ ∉ badGammas m₁ m₂ β)
    (h : (m₁.map (fun p => γ + p.1 + p.2 * β)).prod
       = (m₂.map (fun p => γ + p.1 + p.2 * β)).prod) :
    m₁ = m₂ := by
  by_contra hne
  -- `Δ ≠ 0`: else the pair-factor products agree, forcing `m₁ = m₂`.
  have hΔ : gpDiff m₁ m₂ ≠ 0 := by
    intro h0
    refine hne (multiset_eq_of_pairFactor_prod_eq m₁ m₂ ?_)
    have h0' : (m₁.map pairFactor).prod - (m₂.map pairFactor).prod = 0 := h0
    exact sub_eq_zero.mp h0'
  -- Good β ⇒ the outer-leading coefficient does not vanish at β.
  have hL : (gpDiff m₁ m₂).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hΔ
  unfold badBetas at hβ
  rw [if_neg hne, Multiset.mem_toFinset] at hβ
  have hLeval : (gpDiff m₁ m₂).leadingCoeff.eval β ≠ 0 := fun he =>
    hβ (Polynomial.mem_roots'.mpr ⟨hL, he⟩)
  -- Hence the γ-specialisation is a nonzero polynomial (its top coefficient survives).
  have hMne : (gpDiff m₁ m₂).map (Polynomial.evalRingHom β) ≠ 0 := by
    intro hM0
    apply hLeval
    have hc := congrArg (fun q => Polynomial.coeff q (gpDiff m₁ m₂).natDegree) hM0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coe_evalRingHom] at hc
    exact hc
  -- Good γ ⇒ it is not a root of that nonzero polynomial.
  unfold badGammas at hγ
  rw [if_neg hne, Multiset.mem_toFinset] at hγ
  have hMeval : ((gpDiff m₁ m₂).map (Polynomial.evalRingHom β)).eval γ ≠ 0 := fun he =>
    hγ (Polynomial.mem_roots'.mpr ⟨hMne, he⟩)
  -- But the product equality forces exactly that specialised evaluation to vanish.
  have hadd : eval2 β γ (gpDiff m₁ m₂)
      = eval2 β γ (m₁.map pairFactor).prod - eval2 β γ (m₂.map pairFactor).prod := by
    simp only [eval2, gpDiff, Polynomial.eval_sub]
  have hev : eval2 β γ (gpDiff m₁ m₂) = 0 := by
    rw [hadd, eval2_prod_pairFactor, eval2_prod_pairFactor, h, sub_self]
  rw [eval2_eq_eval_map] at hev
  exact hMeval hev

end

end Kimchi.GrandProduct

namespace Kimchi.GrandProduct

open Polynomial

variable {F : Type*} [Field F]

/-! ## Copy soundness -/

omit [Field F] in
/-- Equal multisets of `(value, own address)` and `(value, wired-to address)` pairs, with
injective addresses, make the values invariant under the wiring `σp`. -/
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

/-- **Copy soundness, field level.** If `∏ (γ + value + address·β)` over the cells agrees with
own addresses and with wired-to addresses at one `(β, γ)` outside `badBetas` / `badGammas`, the
values are invariant under the wiring `σp`. `multiset_eq_of_prod_eval` gives equal pair
multisets; injective addressing descends that to the values. -/
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

end Kimchi.GrandProduct

namespace Kimchi.GrandProduct

variable {F : Type*} [Field F]

/-! ## The permutation accumulator telescopes into a grand-product equality

Finite induction over indexed families, with no polynomials. The permutation argument's wire
constraints instantiate both directions. -/

/-- **Accumulator telescoping.** An accumulator pinned to `1` at both ends of a row range
and satisfying the division-free recurrence `z(k+1) · denₖ = z(k) · numₖ` on it forces the
grand products to agree: `∏ num = ∏ den`. -/
theorem prod_eq_of_accumulator {m : ℕ} (num den z : ℕ → F)
    (h0 : z 0 = 1) (hm : z m = 1)
    (hstep : ∀ k < m, z (k + 1) * den k = z k * num k) :
    ∏ k ∈ Finset.range m, num k = ∏ k ∈ Finset.range m, den k := by
  have aux : ∀ k, k ≤ m →
      z k * ∏ j ∈ Finset.range k, den j = ∏ j ∈ Finset.range k, num j := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      intro hk
      have hk' : k < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      calc z (k + 1) * ((∏ j ∈ Finset.range k, den j) * den k)
          = (z (k + 1) * den k) * ∏ j ∈ Finset.range k, den j := by ring
        _ = (z k * num k) * ∏ j ∈ Finset.range k, den j := by rw [hstep k hk']
        _ = (z k * ∏ j ∈ Finset.range k, den j) * num k := by ring
        _ = (∏ j ∈ Finset.range k, num j) * num k := by rw [ih hk'.le]
  have h := aux m le_rfl
  rw [hm, one_mul] at h
  exact h.symm

/-- **Accumulator construction**, the converse of `prod_eq_of_accumulator`: with nonzero
denominators and agreeing grand products, the running ratio
`z k = (∏_{j<k} num) / (∏_{j<k} den)` is an accumulator. Only this direction divides. -/
theorem accumulator_of_prod_eq {m : ℕ} (num den : ℕ → F)
    (hden : ∀ k < m, den k ≠ 0)
    (hprod : ∏ k ∈ Finset.range m, num k = ∏ k ∈ Finset.range m, den k) :
    ∃ z : ℕ → F, z 0 = 1 ∧ z m = 1
      ∧ ∀ k < m, z (k + 1) * den k = z k * num k := by
  have hdprod : ∀ k, k ≤ m → (∏ j ∈ Finset.range k, den j) ≠ 0 := fun k hk =>
    Finset.prod_ne_zero_iff.mpr fun j hj =>
      hden j (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)
  refine ⟨fun k => (∏ j ∈ Finset.range k, num j) / (∏ j ∈ Finset.range k, den j),
    by simp, ?_, ?_⟩
  · dsimp only
    rw [hprod, div_self (hdprod m le_rfl)]
  · intro k hk
    dsimp only
    have hd := hdprod k hk.le
    have hdk := hden k hk
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    field_simp

end Kimchi.GrandProduct
