import Kimchi.Gate.EndoMul
import Kimchi.Gate.EndoScalar
import Kimchi.Circuit.EndoScalar

/-!
# The `EndoMul ∘ EndoScalar` recoding kernel

The supporting machinery behind `EndoMul`'s capstone (`endoMul`): the proof that
`EndoMul`'s per-window GLV digits coincide with `EndoScalar`'s Algorithm-2 `cPoly`/`dPoly`
digits over the shared challenge crumbs. It is the technical bridge between the two gates —
pure digit/crumb bookkeeping, independent of the GLV point-fold (`chain_endo`/`EndoStep`) —
so it lives apart from `Kimchi.Circuit.EndoMul`, which assembles it into the point statement.

## Main results

* `recoding_digit` — the per-window correspondence: an `EndoMul` window's bits map to the
  `EndoScalar` crumb on which `cPoly`/`dPoly` reproduce the GLV window digit.
* `sum_reindex` — the row↔crumb reindexing lifting the per-window identity to the fold.
* `row_digit` — a satisfying row's GLV integers `(c₁,c₂)` cast to `EndoScalar`'s digit sums.
* `aDigit` / `bDigit` — the `cPoly` / `dPoly` digit of crumb `j` built from the rows.
* `crumbList` / `decompose_crumbList` — the `2m`-crumb list the rows feed to `EndoScalar`,
  and the init-aligned bridge to its `decomposeA`/`decomposeB`.
-/

namespace Kimchi.Circuit.EndoMul

open Kimchi.Gate.EndoMul WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
open Kimchi.Gate.EndoScalar in
/-- The recoding correspondence (per window). An `EndoMul` window's bits `(b₁, b₂)`
    map to the `EndoScalar` crumb `x = b₂ + 2·b₁` (the crumb's `bitEven`/`bitOdd` are
    the sign/base-selector — `EndoScalar`'s nybble is `bitEven + 2·bitOdd`). On it,
    `EndoScalar`'s Algorithm-2 digit polynomials equal `EndoMul`'s GLV window digit:

        cPoly x = (2·b₂ − 1)·b₁          dPoly x = (2·b₂ − 1)·(1 − b₁)

    where `2·b₂ − 1` is the sign (as in `selectQ`) and `b₁` selects the base — so
    `cPoly` lands on the `φ(T)`/λ component (`EndoScalar`'s `a`, `EndoMul`'s `k₂`)
    and `dPoly` on the `T`/1 component (`EndoScalar`'s `b`, `EndoMul`'s `k₁`). This
    is the heart of `EndoMul ∘ EndoScalar`: the two gates assign the SAME signed
    base to each 2-bit window. Folding these matched digits — with `EndoMul`'s ×4
    per row = ×2 per window matching `EndoScalar`'s ×2 per crumb, and the inits
    aligned (`EndoMul`'s `4^m·P₀` carry ↔ `EndoScalar`'s `a=b=2`) — yields
    `(k₂, k₁) = (a, b)`, i.e. `endoMul`'s scalar equals
    `EndoScalar.toField challenge λ`. -/
theorem recoding_digit (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {b1 b2 : F}
    (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 = 0 ∨ b2 = 1) :
    cPoly (b2 + 2 * b1) = (2 * b2 - 1) * b1
      ∧ dPoly (b2 + 2 * b1) = (2 * b2 - 1) * (1 - b1) := by
  obtain ⟨c0, c1, c2, c3⟩ := cPoly_table h2 h3
  obtain ⟨d0, d1, d2, d3⟩ := dPoly_table h2 h3
  rcases hb1 with rfl | rfl <;> rcases hb2 with rfl | rfl
  · exact ⟨by rw [show (0:F) + 2 * 0 = 0 by ring, c0]; ring,
           by rw [show (0:F) + 2 * 0 = 0 by ring, d0]; ring⟩
  · exact ⟨by rw [show (1:F) + 2 * 0 = 1 by ring, c1]; ring,
           by rw [show (1:F) + 2 * 0 = 1 by ring, d1]; ring⟩
  · exact ⟨by rw [show (0:F) + 2 * 1 = 2 by ring, c2]; ring,
           by rw [show (0:F) + 2 * 1 = 2 by ring, d2]; ring⟩
  · exact ⟨by rw [show (1:F) + 2 * 1 = 3 by ring, c3]; ring,
           by rw [show (1:F) + 2 * 1 = 3 by ring, d3]; ring⟩

/-- The row↔crumb sum reindexing — the structural core of the fold-level recoding.
    `EndoMul`'s `m` rows weight each row's 2-crumb contribution `2·g(2i) + g(2i+1)`
    by `4^(m-1-i)`; flattening to `EndoScalar`'s `2m` crumbs weights crumb `j` by
    `2^(2m-1-j)`. The two agree (the row's `×4 = ×2` twice splits across its two
    crumbs). Over any `CommRing` — used at `ℤ` (the GLV coefficients) and `F` (the
    `cPoly`/`dPoly` digits). -/
theorem sum_reindex {R : Type*} [CommRing R] (m : ℕ) (g : ℕ → R) :
    ∑ i ∈ Finset.range m, (4 : R) ^ (m - 1 - i) * (2 * g (2 * i) + g (2 * i + 1))
      = ∑ j ∈ Finset.range (2 * m), (2 : R) ^ (2 * m - 1 - j) * g j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : ∀ i ∈ Finset.range m, (4 : R) ^ (m + 1 - 1 - i) * (2 * g (2 * i) + g (2 * i + 1))
        = 4 * ((4 : R) ^ (m - 1 - i) * (2 * g (2 * i) + g (2 * i + 1))) := by
      intro i hi
      have : i < m := Finset.mem_range.mp hi
      rw [show m + 1 - 1 - i = (m - 1 - i) + 1 by omega, pow_succ]; ring
    have e2 : ∀ j ∈ Finset.range (2 * m), (2 : R) ^ (2 * m + 1 + 1 - 1 - j) * g j
        = 4 * ((2 : R) ^ (2 * m - 1 - j) * g j) := by
      intro j hj
      have : j < 2 * m := Finset.mem_range.mp hj
      rw [show 2 * m + 1 + 1 - 1 - j = (2 * m - 1 - j) + 2 by omega, pow_add]; ring
    rw [Finset.sum_range_succ, Finset.sum_congr rfl e1, ← Finset.mul_sum, ih,
      show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_congr rfl e2, ← Finset.mul_sum,
      show m + 1 - 1 - m = 0 by omega, show 2 * m + 1 + 1 - 1 - (2 * m) = 1 by omega,
      show 2 * m + 1 + 1 - 1 - (2 * m + 1) = 0 by omega]
    ring

open Kimchi.Gate.EndoScalar (cPoly dPoly cPoly_table dPoly_table) in
/-- The per-row digit equations — the gate-side source of the fold-level recoding
    identity. A satisfying row's GLV contribution `S = 4·P + c₁·T + c₂·φ(T)` has its
    integers pinned to `EndoScalar`'s digits: `(c₁ : F) = 2·dPoly(crumb₁) + dPoly(crumb₂)`
    (the `T`/`b` digits) and `(c₂ : F) = 2·cPoly(crumb₁) + cPoly(crumb₂)` (the `φ(T)`/`a`
    digits), where `crumbⱼ = b₂ⱼ + 2·b₂ⱼ₋₁` is window `j`'s `EndoScalar` crumb. (`sound`
    with the field digits read off the strengthened `selectQ` + `recoding_digit`.) -/
theorem row_digit (W : WeierstrassCurve.Affine F) (ha : (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0))
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (endo : F) (w : Witness F) (h : Holds endo w)
    (hT : W.Nonsingular w.xT w.yT) (hφT : W.Nonsingular (endo * w.xT) w.yT)
    (hP : W.Nonsingular w.xP w.yP) (hR : W.Nonsingular w.xR w.yR)
    (hS : W.Nonsingular w.xS w.yS)
    (hQ1 : W.Nonsingular ((1 + (endo - 1) * w.b1) * w.xT) ((2 * w.b2 - 1) * w.yT))
    (hQ2 : W.Nonsingular ((1 + (endo - 1) * w.b3) * w.xT) ((2 * w.b4 - 1) * w.yT))
    (hxne1 : w.xP ≠ (1 + (endo - 1) * w.b1) * w.xT)
    (htne1 : 2 * w.xP - w.s1 ^ 2 + (1 + (endo - 1) * w.b1) * w.xT ≠ 0)
    (hxne2 : w.xR ≠ (1 + (endo - 1) * w.b3) * w.xT)
    (htne2 : 2 * w.xR - w.s3 ^ 2 + (1 + (endo - 1) * w.b3) * w.xT ≠ 0) :
    ∃ c1 c2 : ℤ,
      Point.some _ _ hS = (4 : ℤ) • Point.some _ _ hP + c1 • Point.some _ _ hT
          + c2 • Point.some _ _ hφT
        ∧ (c1 : F) = 2 * dPoly (w.b2 + 2 * w.b1) + dPoly (w.b4 + 2 * w.b3)
        ∧ (c2 : F) = 2 * cPoly (w.b2 + 2 * w.b1) + cPoly (w.b4 + 2 * w.b3) := by
  obtain ⟨hReq, hSeq⟩ :=
    row_sound W ha endo w h hP hR hS hQ1 hQ2 hxne1 htne1 hxne2 htne2
  have hb := h
  simp only [Holds] at hb
  obtain ⟨_, _, _, _, _, _, _, hb1c, hb2c, hb3c, hb4c, _⟩ := hb
  have hb1 := bool_of_mul hb1c
  have hb2 := bool_of_mul hb2c
  have hb3 := bool_of_mul hb3c
  have hb4 := bool_of_mul hb4c
  obtain ⟨hcP1, hdP1⟩ := recoding_digit h2 h3 hb1 hb2
  obtain ⟨hcP2, hdP2⟩ := recoding_digit h2 h3 hb3 hb4
  rcases hb1 with hb1' | hb1' <;> rcases hb3 with hb3' | hb3'
  · -- b1 = 0 (Q₁ = ±T), b3 = 0 (Q₂ = ±T)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f, _⟩ := Kimchi.Gate.VarBaseMul.signed_target W ha hT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some _ _ hQ1 = e1 • Point.some _ _ hT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f, _⟩ := Kimchi.Gate.VarBaseMul.signed_target W ha hT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some _ _ hQ2 = e2 • Point.some _ _ hT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨2 * e1 + e2, 0, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
  · -- b1 = 0 (Q₁ = ±T), b3 = 1 (Q₂ = ±φT)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f, _⟩ := Kimchi.Gate.VarBaseMul.signed_target W ha hT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some _ _ hQ1 = e1 • Point.some _ _ hT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = endo * w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f, _⟩ := Kimchi.Gate.VarBaseMul.signed_target W ha hφT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some _ _ hQ2 = e2 • Point.some _ _ hφT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨2 * e1, e2, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
  · -- b1 = 1 (Q₁ = ±φT), b3 = 0 (Q₂ = ±T)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = endo * w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f, _⟩ := Kimchi.Gate.VarBaseMul.signed_target W ha hφT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some _ _ hQ1 = e1 • Point.some _ _ hφT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f, _⟩ := Kimchi.Gate.VarBaseMul.signed_target W ha hT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some _ _ hQ2 = e2 • Point.some _ _ hT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨e2, 2 * e1, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
  · -- b1 = 1 (Q₁ = ±φT), b3 = 1 (Q₂ = ±φT)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = endo * w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f, _⟩ := Kimchi.Gate.VarBaseMul.signed_target W ha hφT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some _ _ hQ1 = e1 • Point.some _ _ hφT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = endo * w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f, _⟩ := Kimchi.Gate.VarBaseMul.signed_target W ha hφT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some _ _ hQ2 = e2 • Point.some _ _ hφT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨0, 2 * e1 + e2, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring

open Kimchi.Gate.EndoScalar (cPoly) in
/-- `EndoScalar`'s `a`-digit (`cPoly`, the `φ(T)`/λ component) of crumb `j` built from
    the rows `g`: crumb `2i` is row `i`'s first window `(b₂,b₁)`, crumb `2i+1` its
    second `(b₄,b₃)`. -/
def aDigit (g : ℕ → Witness F) (j : ℕ) : F :=
  if j % 2 = 0 then cPoly ((g (j / 2)).b2 + 2 * (g (j / 2)).b1)
  else cPoly ((g (j / 2)).b4 + 2 * (g (j / 2)).b3)

open Kimchi.Gate.EndoScalar (dPoly) in
/-- `EndoScalar`'s `b`-digit (`dPoly`, the `T`/1 component) of crumb `j`. -/
def bDigit (g : ℕ → Witness F) (j : ℕ) : F :=
  if j % 2 = 0 then dPoly ((g (j / 2)).b2 + 2 * (g (j / 2)).b1)
  else dPoly ((g (j / 2)).b4 + 2 * (g (j / 2)).b3)

/-- The `2m`-crumb list the rows feed to `EndoScalar`: row `i` contributes its two
    windows `[b₂+2·b₁, b₄+2·b₃]` in order, so `crumbList[2i] = aDigit/bDigit`'s crumb
    `2i` and `crumbList[2i+1]` crumb `2i+1`. -/
def crumbList (g : ℕ → Witness F) (m : ℕ) : List F :=
  (List.range m).flatMap fun i => [(g i).b2 + 2 * (g i).b1, (g i).b4 + 2 * (g i).b3]

omit [DecidableEq F] in
/-- Each additional row appends its two window crumbs to the crumb list. -/
theorem crumbList_succ (g : ℕ → Witness F) (m : ℕ) :
    crumbList g (m + 1)
      = crumbList g m ++ [(g m).b2 + 2 * (g m).b1, (g m).b4 + 2 * (g m).b3] := by
  simp [crumbList, List.range_succ, List.flatMap_append]

omit [DecidableEq F] in
/-- The init bridge: `EndoScalar`'s `decomposeA`/`decomposeB` over the crumb
    list (folded from the `a = b = 2` init) is its `2·4^m` carry plus the
    Algorithm-2 digit sums — exactly `endoMul_ab`'s `(k₂:F)` / `(k₁:F)`. By induction
    on `m` (each row appends 2 crumbs; `List.foldl_append`). -/
theorem decompose_crumbList (g : ℕ → Witness F) (m : ℕ) :
    Kimchi.Circuit.EndoScalar.decomposeA (crumbList g m)
        = 2 * (4 : F) ^ m + ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * aDigit g j
      ∧ Kimchi.Circuit.EndoScalar.decomposeB (crumbList g m)
        = 2 * (4 : F) ^ m + ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * bDigit g j := by
  induction' m with m ih <;> simp_all +decide [ Nat.mul_succ, Finset.sum_range_succ ];
  · exact ⟨ rfl, rfl ⟩;
  · rw [ crumbList_succ, EndoScalar.decomposeA_append, EndoScalar.decomposeB_append ];
    simp_all +decide [ aDigit, bDigit ];
    norm_num [ Nat.add_div ] ; ring_nf ;
    constructor <;> rw [ Finset.sum_mul _ _ _ ] <;>
      rw [ Finset.sum_congr rfl fun x hx => ?_ ] <;> ring;
    · split_ifs <;>
        rw [ show 1 + m * 2 - x = (m * 2 - 1 - x) + 2 by
              have := Finset.mem_range.mp hx; omega ] <;> ring;
    · split_ifs <;>
        rw [ show 1 + m * 2 - x = (m * 2 - 1 - x) + 2 by
              have := Finset.mem_range.mp hx; omega ] <;> ring

end Kimchi.Circuit.EndoMul
