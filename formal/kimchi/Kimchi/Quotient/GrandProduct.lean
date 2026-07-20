import Kimchi.Domain

/-!
# The grand-product core: linear-factor multisets and two-variable pinning

Polynomial-algebra infrastructure for the kimchi permutation argument (proof-systems
`permutation.rs`): the permutation accumulator telescopes into an equality of grand products
`∏ (wᵢ + β·posᵢ + γ) = ∏ (wᵢ + β·σ(pos)ᵢ + γ)` at the challenges `β, γ`, and the soundness
core — proved here — is that such an equality forces the multisets of pairs `(wᵢ, posᵢ)` to
coincide. This is **pure algebra**: no protocol content whatsoever (no `Z_H`, no domain `H`,
no root of unity `ω`, no gate). The only project dependency is `Kimchi.Quotient.Domain`.

We work in the two-variable polynomial ring `F[β][γ] := Polynomial (Polynomial F)` with inner
variable `β` and outer variable `γ`, over an abstract field `F`. A pair `(w, a) ∈ F × F` gives
rise to a monic linear **pair factor** `γ + w + a·β`; the multiset product of these factors is
what the permutation accumulator forces to agree on both sides.

## Contents

* `pairFactor` — the monic linear pair factor `X + C (C p.1 + C p.2 * X)`.
* `eval2` — two-variable evaluation `(P.eval (C g)).eval b`.
* `multiset_eq_of_pairFactor_prod_eq` — equal products of pair factors force equal multisets
  (unique factorisation of monic linear factors over the domain `Polynomial F`).
* `badBetas` / `badGammas` (with `card_badBetas_le` / `card_badGammas_le`) — the counting
  Schwartz–Zippel bad sets for the two challenges.
* `multiset_eq_of_prod_eval` — the headline: field-level products agreeing at one `(β, γ)`
  outside the bad sets force multiset equality.
-/

namespace Kimchi.Quotient

open Polynomial

variable {F : Type*} [Field F]

/-! ## The pair factor and two-variable evaluation -/

/-- **Grand-product pair factor.** For a pair `p = (p.1, p.2) ∈ F × F` the monic linear factor
`X + C (C p.1 + C p.2 * X) ∈ Polynomial (Polynomial F)`, where the outer `X` is the `γ` variable,
the inner `X` is the `β` variable, and the two `C`s are the inner/outer constant embeddings. As
an element of `F[β][γ]` this is `γ + p.1 + p.2·β`. -/
private noncomputable def pairFactor (p : F × F) : Polynomial (Polynomial F) :=
  Polynomial.X + Polynomial.C (Polynomial.C p.1 + Polynomial.C p.2 * Polynomial.X)

/-- **Two-variable evaluation.** For `b g : F` and `P ∈ Polynomial (Polynomial F)`, substitute
the outer variable `γ := g` (landing in `Polynomial F`), then the inner variable `β := b`. Thus
`eval2 b g P` is the value of `P` at `β = b`, `γ = g`. -/
private noncomputable def eval2 (b g : F) (P : Polynomial (Polynomial F)) : F :=
  (P.eval (Polynomial.C g)).eval b

/-! ## The core: equal products force equal multisets -/

/-- **Unique factorisation of pair factors.** If the products of pair factors over two multisets
of pairs agree in `Polynomial (Polynomial F)`, then the multisets are equal. -/
theorem multiset_eq_of_pairFactor_prod_eq (m₁ m₂ : Multiset (F × F))
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

/-! ## Two-variable identity pinning on a grid -/

/-- **Evaluation bridge.** `eval2 b g P` equals the outer evaluation at `g` of `P` after mapping
the inner coefficients through `evalRingHom b`. Both sides equal `∑ₖ (P.coeff k)(b)·gᵏ`. -/
private lemma eval2_eq_eval_map (b g : F) (P : Polynomial (Polynomial F)) :
    eval2 b g P = (P.map (Polynomial.evalRingHom b)).eval g := by
  rw [eval2, Polynomial.eval_map]
  rw [show P.eval (Polynomial.C g)
        = Polynomial.eval₂ (RingHom.id (Polynomial F)) (Polynomial.C g) P from by
        rw [Polynomial.eval₂_id]]
  rw [← Polynomial.coe_evalRingHom, Polynomial.hom_eval₂]
  simp

/-! ## The headline: grid products force multiset equality -/

/-- **(a) Evaluation bridge for the product.** Evaluating the pair-factor product at `(b, g)`
gives the field-level product `∏ (g + p.1 + p.2·b)`. `eval2 b g` is a ring-hom composite, so it
commutes with the multiset product and acts factor-by-factor. -/
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

/-- **(b) Outer-degree bound.** The pair-factor product has outer degree at most `|m|`, since each
factor is monic linear in the outer variable. -/
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

/-- **(c) Inner coefficient-degree bound.** Every coefficient of the pair-factor product has inner
degree at most `|m|`. Multiset induction: multiplying by one more factor `(X + C r)` (inner degree
of `r` ≤ 1) raises the coefficient's inner degree by at most one. -/
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

/-! ## Mathlib supplement — single-challenge Schwartz–Zippel (β,γ collapse)

The single-challenge (counting) Schwartz–Zippel argument for the β,γ collapse, in place of a
two-variable injective grid. Working in `F[β][γ]` with
`Δ := (m₁.map pairFactor).prod - (m₂.map pairFactor).prod`, a *good* pair `(β,γ)` — one avoiding
two explicitly-small bad sets — already forces the two grand products to agree, hence the pair
multisets to coincide. Bad β's are the roots of the outer (γ-leading) coefficient of `Δ`; bad γ's
(given β) are the roots of `Δ` specialised at `β`. Both bad sets are empty when `m₁ = m₂`, so the
`∉ bad…` hypotheses are never vacuous. Mirrors `Kimchi/SchwartzZippel.lean`'s α-collapse.
-/

/-- The difference of the two grand products in `F[β][γ]` (outer variable `γ`, inner `β`).
`Δ = 0 ↔ m₁ = m₂` via `multiset_eq_of_pairFactor_prod_eq`; its outer-leading coefficient and its
`β`-specialisation drive the bad-set definitions below. -/
private noncomputable def gpDiff (m₁ m₂ : Multiset (F × F)) : Polynomial (Polynomial F) :=
  (m₁.map pairFactor).prod - (m₂.map pairFactor).prod

section
variable [DecidableEq F]

/-- **Bad β.** Those `β` at which the γ-polynomial of `m₁` minus that of `m₂` collapses to zero
even though `m₁ ≠ m₂`: concretely the roots of `Δ`'s outer-leading (γ-degree) coefficient, a
nonzero inner β-polynomial when `Δ ≠ 0`. EMPTY when `m₁ = m₂`, keeping the hypotheses
satisfiable — the β-axis of the grand-product collapse. -/
noncomputable def badBetas (m₁ m₂ : Multiset (F × F)) : Finset F :=
  if m₁ = m₂ then ∅ else (gpDiff m₁ m₂).leadingCoeff.roots.toFinset

/-- **Card bound for bad β** — at most `max |m₁| |m₂|`. The empty case is trivial; otherwise the
distinct roots of `Δ.leadingCoeff` number at most its degree, and `Δ.leadingCoeff = Δ.coeff
Δ.natDegree` is a coefficient of a degree-`Δ` polynomial, each coefficient of inner degree
`≤ max |m₁| |m₂|` via `natDegree_coeff_prod_pairFactor`; the bound is what keeps `∉ badBetas`
non-vacuous. -/
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

/-- **Bad γ at a good β.** The roots of `Δ` specialised at `β` (the γ-polynomial `Δ.map
(evalRingHom β)`), which is nonzero when `β ∉ badBetas`. EMPTY when `m₁ = m₂` — the γ-axis
of the grand-product collapse. -/
noncomputable def badGammas (m₁ m₂ : Multiset (F × F)) (β : F) : Finset F :=
  if m₁ = m₂ then ∅ else ((gpDiff m₁ m₂).map (Polynomial.evalRingHom β)).roots.toFinset

/-- **Card bound for bad γ** — at most `max |m₁| |m₂|`, for every `β`. The specialised polynomial
has degree at most `Δ.natDegree ≤ max |m₁| |m₂|` (via `natDegree_map_le` and
`natDegree_prod_pairFactor`), so its distinct roots number no more, which keeps `∉ badGammas`
non-vacuous. -/
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

/-- **The grand product at ONE `(β,γ)`** — the counting-form headline. If the
field-level products `∏ (γ + p.1 + p.2·β)` over `m₁` and `m₂` agree at a single good pair `(β,γ)`
(β outside `badBetas`, γ outside `badGammas … β`), then `m₁ = m₂`. Iterated univariate SZ: a good
β keeps the γ-specialisation `Δ.map (evalRingHom β)` nonzero, a good γ is not among its roots, yet
the product equality forces `(Δ.map (evalRingHom β)).eval γ = 0` — contradiction unless `Δ = 0`,
i.e. `m₁ = m₂`. The single-challenge grand-product core. -/
theorem multiset_eq_of_prod_eval (m₁ m₂ : Multiset (F × F)) (β γ : F)
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

end Kimchi.Quotient
