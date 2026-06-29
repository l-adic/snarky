import Kimchi.Gate.EndoMul
import Kimchi.Gate.EndoScalar
import Kimchi.Circuit.EndoScalar

/-!
# The `EndoMul ∘ EndoScalar` recoding kernel

The supporting machinery behind `EndoMul`'s capstone (`endoMul`): the proof that
`EndoMul`'s per-window GLV digits coincide with `EndoScalar`'s Algorithm-2 `cPoly`/`dPoly`
digits over the shared challenge crumbs. It is the technical bridge between the two gates —
pure digit/crumb bookkeeping, independent of the GLV point-fold (`chain_endo`) —
so it lives apart from `Kimchi.Circuit.EndoMul`, which assembles it into the point statement.

## Main results

* `recoding_digit` — the per-window correspondence: an `EndoMul` window's bits map to the
  `EndoScalar` crumb on which `cPoly`/`dPoly` reproduce the GLV window digit.
* `sum_reindex` — the row↔crumb reindexing lifting the per-window identity to the fold.
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
