import Kimchi.Gate.EndoMul
import Kimchi.Gate.EndoScalar
import Kimchi.Circuit.EndoScalar
import Kimchi.Circuit.VarBaseMul.Internal

/-!
# The `EndoMul` circuit: supporting development

Endomorphism-optimized (GLV) scalar multiplication composes `Kimchi.Gate.EndoMul` rows into a
full scalar multiplication of the base point. Each row contributes `S = 4·P + c₁·T + c₂·φ(T)` (the
gate's `sound`), so chaining `m` rows folds into `P_m = 4^m·P₀ + k₁·T + k₂·φ(T)`; on the Pasta
endomorphism `φ(T) = [λ]·T` this collapses to a single scalar multiple of `T`. This module collects
the definitions and lemmas on which the curve-specialized entry points (`{pallas,vesta}_endoMul`,
in `Kimchi.Circuit.EndoMul`) rest, together with the generic capstone `endoMul`.

The circuit is stated so the prover supplies only

* `Holds endo (g i)` at every step (the gate constraint),
* the **base** nonsingularity `hT`/`hφT` (one-time, row 0 — genuinely external),
* the **initial** accumulator `P₀ = 2(T + φT)` (one-time),
* the **threading** of columns (`(g (i+1)).xP = (g i).xS`, base shared).

Every intermediate accumulator's nonsingularity is *derived* — the gate's secant additions hand
back the output point on-curve (`gate_advance`), threaded through the chain — so there is no
per-row hypothesis bundle, only a coordinate side-condition `hxne` discharged at the curve layer.

## The `EndoMul ∘ EndoScalar` recoding kernel

EndoMul's per-window GLV digits coincide with EndoScalar's Algorithm-2 `cPoly`/`dPoly` digits over
the shared challenge crumbs. This is the technical bridge between the two gates — pure digit/crumb
bookkeeping, independent of the GLV point-fold.

* `recoding_digit` — the per-window correspondence: an `EndoMul` window's bits map to the
  `EndoScalar` crumb on which `cPoly`/`dPoly` reproduce the GLV window digit.
* `sum_reindex` — the row↔crumb reindexing lifting the per-window identity to the fold.
* `aDigit` / `bDigit` — the `cPoly` / `dPoly` digit of crumb `j` built from the rows.
* `crumbList` / `decompose_crumbList` — the `2m`-crumb list the rows feed to `EndoScalar`, and the
  init-aligned bridge to its `decomposeA`/`decomposeB`.

## Non-degeneracy

The per-row non-degeneracy facts the soundness needs, generic over the curve:

* `block_tne` — each `(P+Q)+P` block's *second*-addition condition `htne ≠ 0` is self-enforced by
  the gate constraints (the EndoMul analog of VarBaseMul's `tne_of_holds`).
* `combo_off_targets` — the geometric core of the *first*-addition condition `hxne`: a bounded
  two-base combination `[a]·T + [b]·φT` avoids `±T`/`±φT`.
* `selectQ'` — a bounded variant of `Gate.EndoMul.selectQ` that also returns the sign `e = ±1`.

## The GLV scalar-multiplication chain

The point-level fold and the capstone:

* `chain_endo` — the two-base group fold (pure group algebra).
* `gate_advance` — one `EndoMul` row, with the output point's nonsingularity *produced*, not given.
* `endoMul_ab` — the GLV-recoding chain: the coefficients `(k₂, k₁)` are `EndoScalar`'s `a`, `b`.
* `endoMul` — the capstone: the rows compute `[s]·T`, `s = EndoScalar.toField (crumbList g m) λ`.
* `accumulator_chain` — discharges the per-row `hxne` from the GLV short-basis bound.
-/
namespace Kimchi.Circuit.EndoMul

open Kimchi.Gate.EndoMul WeierstrassCurve.Affine
open Kimchi.Gate.EndoScalar (cPoly dPoly)

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The `EndoMul ∘ EndoScalar` recoding kernel -/

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

/-! ## Non-degeneracy

The first-addition condition `hxne` is `Pᵢ ∉ {±T, ±φT}` (same `x` ⟺ `±` point). Writing the
accumulator as `[a]·T + [b]·φT` and collapsing with the eigenvalue `φT = [λ]·T`, this reduces to
`a + b·λ ≢ {±1, ±λ} (mod order)` — four "no short relation" facts, supplied for the small
accumulator coefficients by the GLV bound (`Pasta.pallas_glv_no_short_relation`). The
second-addition condition is self-enforced by the gate constraints. -/

/-- One block's second-addition non-degeneracy, self-enforced. If `2·xI − s² + xq = 0`, the
    block constraint `(2·xI − s² + xq)·(…) = (xI − xO)·(2·yI)` gives `(xI − xO)·(2·yI) = 0`;
    with `xI ≠ xO` and char ≠ 2 this forces `yI = 0`, making `I` 2-torsion — ruled out on an
    odd-prime-order group. (The EndoMul analog of VarBaseMul's `tne_of_holds`.) -/
theorem block_tne (W : WeierstrassCurve.Affine F) [Fact (Nat.Prime W.order)]
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0) (h2 : (2 : F) ≠ 0) (hodd : W.order ≠ 2)
    {xI yI xO yO s xq : F} (hI : W.Nonsingular xI yI) (hxne : xI ≠ xO)
    (hc : (2 * xI - s ^ 2 + xq) * ((xI - xO) * s + yO + yI) = (xI - xO) * (2 * yI)) :
    2 * xI - s ^ 2 + xq ≠ 0 := by
  haveI : Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0) := ⟨ha⟩
  intro ht
  rw [ht, zero_mul] at hc
  have hyI : yI = 0 := by
    rcases mul_eq_zero.mp hc.symm with h | h
    · exact absurd h (sub_ne_zero_of_ne hxne)
    · exact (mul_eq_zero.mp h).resolve_left h2
  obtain ⟨ha1, -, ha3⟩ := ha
  have hneg : W.negY xI yI = yI := by simp [WeierstrassCurve.Affine.negY, ha1, ha3, hyI]
  have hself : -(Point.some _ _ hI) = Point.some _ _ hI := by
    rw [Point.neg_some]; exact some_congr W _ hI rfl hneg
  have hPne : Point.some _ _ hI ≠ 0 := Point.some_ne_zero hI
  have h2P : (2 : ℤ) • Point.some _ _ hI = 0 := by
    rw [two_zsmul]; nth_rewrite 2 [← hself]; rw [add_neg_cancel]
  have hlt : (2 : ℤ) < (W.order : ℤ) := by
    have : (2 : ℕ) < W.order :=
      lt_of_le_of_ne (Fact.out : Nat.Prime W.order).two_le (Ne.symm hodd)
    exact_mod_cast this
  exact Kimchi.Circuit.VarBaseMul.smul_ne_zero_of_lt W hPne (by norm_num) hlt h2P

/-- **GLV off-targets.** With the eigenvalue `φT = [λ]·T` and the four no-short-relation facts
    for the accumulator's offset coefficients, the two-base combination `[a]·T + [b]·φT` is none
    of `±T`, `±φT`. The geometric core of `hxne`. -/
theorem combo_off_targets (W : WeierstrassCurve.Affine F)
    [Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)] [Fact (Nat.Prime W.order)]
    {T φT : W.Point} (hTne : T ≠ 0) {lam : ℤ} (heig : φT = lam • T) {a b : ℤ}
    (h1 : ¬ (W.order : ℤ) ∣ (a - 1 + b * lam))
    (h2 : ¬ (W.order : ℤ) ∣ (a + 1 + b * lam))
    (h3 : ¬ (W.order : ℤ) ∣ (a + (b - 1) * lam))
    (h4 : ¬ (W.order : ℤ) ∣ (a + (b + 1) * lam)) :
    a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T
      ∧ a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT := by
  have combo : ∀ c : ℤ, a • T + b • φT = c • T ↔ (W.order : ℤ) ∣ (a + b * lam - c) := by
    intro c
    have e : a • T + b • φT - c • T = (a + b * lam - c) • T := by rw [heig]; module
    rw [← sub_eq_zero, e, Kimchi.Circuit.VarBaseMul.zsmul_eq_zero_iff_order_dvd W hTne]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hP
    exact h1 (by have := (combo 1).mp (hP.trans (one_zsmul T).symm)
                 rwa [show a + b * lam - 1 = a - 1 + b * lam by ring] at this)
  · intro hP
    exact h2 (by have := (combo (-1)).mp (hP.trans (neg_one_zsmul T).symm)
                 rwa [show a + b * lam - (-1) = a + 1 + b * lam by ring] at this)
  · intro hP
    exact h3 (by have := (combo lam).mp (hP.trans (by rw [heig]))
                 rwa [show a + b * lam - lam = a + (b - 1) * lam by ring] at this)
  · intro hP
    exact h4 (by have := (combo (-lam)).mp (hP.trans (by rw [heig]; simp))
                 rwa [show a + b * lam - -lam = a + (b + 1) * lam by ring] at this)

/-- A bounded variant of `Gate.EndoMul.selectQ` that additionally returns the integer fact
    `e = 1 ∨ e = -1` (the sign), which `selectQ` discards. Same case split, threading the fourth
    component of `Kimchi.Gate.VarBaseMul.signed_target`. -/
theorem selectQ' (W : WeierstrassCurve.Affine F) (ha : (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0))
    {endo b1 b2 xT yT : F}
    (hT : W.Nonsingular xT yT) (hφT : W.Nonsingular (endo * xT) yT)
    (hQ : W.Nonsingular ((1 + (endo - 1) * b1) * xT) ((2 * b2 - 1) * yT))
    (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 = 0 ∨ b2 = 1) :
    (∃ e : ℤ, Point.some _ _ hQ = e • Point.some _ _ hT ∧ (e = 1 ∨ e = -1))
      ∨ (∃ e : ℤ, Point.some _ _ hQ = e • Point.some _ _ hφT ∧ (e = 1 ∨ e = -1)) := by
  rcases hb1 with rfl | rfl
  · left
    have hx : (1 + (endo - 1) * 0) * xT = xT := by ring
    obtain ⟨e, he, _, hpm⟩ := Kimchi.Gate.VarBaseMul.signed_target W ha hT (hx ▸ hQ) hb2
    exact ⟨e, (some_congr W hQ (hx ▸ hQ) hx rfl).trans he, hpm⟩
  · right
    have hx : (1 + (endo - 1) * 1) * xT = endo * xT := by ring
    obtain ⟨e, he, _, hpm⟩ := Kimchi.Gate.VarBaseMul.signed_target W ha hφT (hx ▸ hQ) hb2
    exact ⟨e, (some_congr W hQ (hx ▸ hQ) hx rfl).trans he, hpm⟩

/-! ## The GLV scalar-multiplication chain -/

/-- The two-base GLV fold: chaining `P_{i+1} = 4·P_i + c₁ᵢ·T + c₂ᵢ·φT` over `m` rows
    gives `P_m = 4^m·P₀ + (∑ 4^(m-1-i)·c₁ᵢ)·T + (∑ 4^(m-1-i)·c₂ᵢ)·φT`. Pure group
    algebra (cf. VarBaseMul's `chain_scalarMul`, here with a second base). -/
theorem chain_endo (W : WeierstrassCurve.Affine F)
    (m : ℕ) (P : ℕ → W.Point) (T φT : W.Point) (c1 c2 : ℕ → ℤ)
    (hstep : ∀ i, i < m → P (i + 1) = (4 : ℤ) • P i + c1 i • T + c2 i • φT) :
    P m = (4 : ℤ) ^ m • P 0
        + (∑ i ∈ Finset.range m, (4 : ℤ) ^ (m - 1 - i) * c1 i) • T
        + (∑ i ∈ Finset.range m, (4 : ℤ) ^ (m - 1 - i) * c2 i) • φT := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : P (m + 1) = (4 : ℤ) • P m + c1 m • T + c2 m • φT :=
      hstep m (Nat.lt_succ_self m)
    have ih' := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hsum : ∀ c : ℕ → ℤ,
        (∑ i ∈ Finset.range (m + 1), (4 : ℤ) ^ (m + 1 - 1 - i) * c i)
          = (4 : ℤ) * (∑ i ∈ Finset.range m, (4 : ℤ) ^ (m - 1 - i) * c i) + c m := by
      intro c
      rw [Finset.sum_range_succ, Finset.mul_sum]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : m - i = (m - 1 - i) + 1 := by
        have := Finset.mem_range.mp hi; omega
      rw [hi', pow_succ]; ring
    rw [hs, ih', hsum c1, hsum c2, pow_succ']
    module

/-- Output-accumulator coordinates after `k` rows: row 0's input `xP`/`yP` when `k = 0`, else
    row `(k-1)`'s output `xS`/`yS` (so `accX g m` is the final accumulator's `x`). -/
def accX (g : ℕ → Witness F) : ℕ → F
  | 0 => (g 0).xP
  | k + 1 => (g k).xS

def accY (g : ℕ → Witness F) : ℕ → F
  | 0 => (g 0).yP
  | k + 1 => (g k).yS

/-- **Producing variant of `Gate.EndoMul.block_sound`.** Same `(P+Q)+P` window algebra, but the
    output accumulator's nonsingularity (`hR`) is *produced* (existential) via `secant_add`,
    rather than consumed as a hypothesis. This is the producer that `gate_advance` / the chain
    proofs call to derive per-row nonsingularity. -/
theorem block_produce (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    {xq yq xP yP s xR yR : F}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xq yq)
    (hxne : xP ≠ xq) (htne : 2 * xP - s ^ 2 + xq ≠ 0) (hxRne : xR ≠ xP)
    (hs : (xq - xP) * s = yq - yP)
    (hc2 : (2 * xP - s ^ 2 + xq) * ((xP - xR) * s + yR + yP) = (xP - xR) * (2 * yP))
    (hc3 : (yR + yP) ^ 2 = (xP - xR) ^ 2 * (s ^ 2 - xq + xR)) :
    ∃ hR : W.Nonsingular xR yR,
      Point.some _ _ hR = (Point.some _ _ hP + Point.some _ _ hQ) + Point.some _ _ hP := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  have hdiff1 : xP - xq ≠ 0 := sub_ne_zero.mpr hxne
  have hxRne0 : xP - xR ≠ 0 := sub_ne_zero.mpr (Ne.symm hxRne)
  have hl1 : s = (yP - yq) / (xP - xq) := by
    rw [eq_div_iff hdiff1]; linear_combination -hs
  set Mx : F := s * s - xP - xq with hMx
  set My : F := s * (xP - Mx) - yP with hMy
  set s2 : F := (My - yP) / (Mx - xP) with hs2
  clear_value s2 My Mx
  have htval : xP - Mx = 2 * xP - s ^ 2 + xq := by rw [hMx]; ring
  have htt : xP - Mx ≠ 0 := by rw [htval]; exact htne
  have hMxne : Mx ≠ xP := by intro hc; exact htt (by rw [hc]; ring)
  have hxine : Mx - xP ≠ 0 := sub_ne_zero.mpr hMxne
  obtain ⟨hM, hAdd1⟩ :=
    Kimchi.Gate.VarBaseMul.secant_add W ⟨ha1, ha2, ha3⟩ hP hQ hxne hl1 hMx hMy
  have hsr : s2 * (Mx - xP) = My - yP := by rw [hs2, div_mul_cancel₀]; exact hxine
  have key1' : (yR + yP) * (Mx - xP) = (xP - xR) * (My - yP) := by
    linear_combination -hc2 - (xP - xR) * hMy - ((xP - xR) * s + yR + yP) * htval
  have hcancel : (yR + yP) * (Mx - xP) = ((xP - xR) * s2) * (Mx - xP) := by
    rw [key1']; linear_combination -(xP - xR) * hsr
  have key1div : yR + yP = (xP - xR) * s2 := mul_right_cancel₀ hxine hcancel
  have hs2sq : s2 * s2 = s ^ 2 - xq + xR := by
    have hkey3 : (xP - xR) ^ 2 * (s2 * s2) = (xP - xR) ^ 2 * (s ^ 2 - xq + xR) := by
      rw [← hc3]
      linear_combination -((yR + yP) + (xP - xR) * s2) * key1div
    exact mul_left_cancel₀ (pow_ne_zero 2 hxRne0) hkey3
  have hxR_eq : xR = s2 * s2 - Mx - xP := by rw [hs2sq, hMx]; ring
  have hyR_eq : yR = s2 * (Mx - xR) - My := by
    have hyR' : yR = (xP - xR) * s2 - yP := by linear_combination key1div
    rw [hyR']; linear_combination -hsr
  obtain ⟨hR', hAdd2⟩ :=
    Kimchi.Gate.VarBaseMul.secant_add W ⟨ha1, ha2, ha3⟩ hM hP hMxne hs2 hxR_eq hyR_eq
  exact ⟨hR', by rw [hAdd1, hAdd2]⟩

/-- **The producing gate step.** Given the input accumulator on-curve (`hP`), the base
    (`hT`/`hφT`), the row constraints (`Holds`), and the two first-addition non-degeneracies
    (`hxne1`/`hxne2` — the second-addition `htne`s are self-enforced via `htne_of_holds`), the
    gate *produces* the output point on-curve (`hS`, existential — via the secant additions, not
    assumed) together with the GLV contribution. The `(c1, c2)` digit identities are the GLV
    window digits, plus the `|·| ≤ 3` bound used by the accumulator invariant. -/
theorem gate_advance (W : WeierstrassCurve.Affine F) [Fact (Nat.Prime W.order)]
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hodd : W.order ≠ 2)
    (endo : F) (w : Witness F) (h : Holds endo w)
    (hT : W.Nonsingular w.xT w.yT) (hφT : W.Nonsingular (endo * w.xT) w.yT)
    (hP : W.Nonsingular w.xP w.yP)
    (hxne1 : w.xP ≠ (1 + (endo - 1) * w.b1) * w.xT)
    (hxne2 : w.xR ≠ (1 + (endo - 1) * w.b3) * w.xT) :
    ∃ (hS : W.Nonsingular w.xS w.yS) (c1 c2 : ℤ),
      Point.some _ _ hS = (4 : ℤ) • Point.some _ _ hP
          + c1 • Point.some _ _ hT + c2 • Point.some _ _ hφT
        ∧ (c1 : F) = 2 * dPoly (w.b2 + 2 * w.b1) + dPoly (w.b4 + 2 * w.b3)
        ∧ (c2 : F) = 2 * cPoly (w.b2 + 2 * w.b1) + cPoly (w.b4 + 2 * w.b3)
        ∧ |c1| ≤ 3 ∧ |c2| ≤ 3 := by
  -- distinct-point facts and target nonsingularities
  obtain ⟨hxPxR, hxRxS⟩ := distinctPoints endo w h
  obtain ⟨hQ1, hQ2⟩ := targets_nonsingular W ha endo w h hT hφT
  -- the gate constraints
  have hb := h
  rw [holds_iff] at hb
  obtain ⟨hs1, hc2_1, hc3_1, hs3, hc2_2, hc3_2, _, hb1c, hb2c, hb3c, hb4c, _⟩ := hb
  have hb1 := bool_of_mul hb1c
  have hb2 := bool_of_mul hb2c
  have hb3 := bool_of_mul hb3c
  have hb4 := bool_of_mul hb4c
  -- window 1: produce `hR` (the self-enforced second-addition non-degeneracy via `block_tne`)
  have htne1 := block_tne W ha h2 hodd hP hxPxR hc2_1
  obtain ⟨hR, hReq⟩ :=
    block_produce W ha hP hQ1 hxne1 htne1 (Ne.symm hxPxR) hs1 hc2_1 hc3_1
  -- window 2: produce `hS`
  have htne2 := block_tne W ha h2 hodd hR hxRxS hc2_2
  obtain ⟨hS, hSeq⟩ :=
    block_produce W ha hR hQ2 hxne2 htne2 (Ne.symm hxRxS) hs3 hc2_2 hc3_2
  refine ⟨hS, ?_⟩
  -- recoding digit identities
  obtain ⟨hcP1, hdP1⟩ := recoding_digit h2 h3 hb1 hb2
  obtain ⟨hcP2, hdP2⟩ := recoding_digit h2 h3 hb3 hb4
  rcases hb1 with hb1' | hb1' <;> rcases hb3 with hb3' | hb3'
  · -- b1 = 0 (Q₁ = ±T), b3 = 0 (Q₂ = ±T)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f, he1pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some _ _ hQ1 = e1 • Point.some _ _ hT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f, he2pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some _ _ hQ2 = e2 • Point.some _ _ hT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨2 * e1 + e2, 0, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide
  · -- b1 = 0 (Q₁ = ±T), b3 = 1 (Q₂ = ±φT)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f, he1pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some _ _ hQ1 = e1 • Point.some _ _ hT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = endo * w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f, he2pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hφT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some _ _ hQ2 = e2 • Point.some _ _ hφT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨2 * e1, e2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide
  · -- b1 = 1 (Q₁ = ±φT), b3 = 0 (Q₂ = ±T)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = endo * w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f, he1pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hφT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some _ _ hQ1 = e1 • Point.some _ _ hφT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f, he2pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some _ _ hQ2 = e2 • Point.some _ _ hT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨e2, 2 * e1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide
  · -- b1 = 1 (Q₁ = ±φT), b3 = 1 (Q₂ = ±φT)
    have hxc1 : (1 + (endo - 1) * w.b1) * w.xT = endo * w.xT := by rw [hb1']; ring
    obtain ⟨e1, he1, he1f, he1pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hφT (hxc1 ▸ hQ1) hb2
    have hQ1e : Point.some _ _ hQ1 = e1 • Point.some _ _ hφT :=
      (some_congr W hQ1 (hxc1 ▸ hQ1) hxc1 rfl).trans he1
    have hxc2 : (1 + (endo - 1) * w.b3) * w.xT = endo * w.xT := by rw [hb3']; ring
    obtain ⟨e2, he2, he2f, he2pm⟩ :=
      Kimchi.Gate.VarBaseMul.signed_target W ha hφT (hxc2 ▸ hQ2) hb4
    have hQ2e : Point.some _ _ hQ2 = e2 • Point.some _ _ hφT :=
      (some_congr W hQ2 (hxc2 ▸ hQ2) hxc2 rfl).trans he2
    refine ⟨0, 2 * e1 + e2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hSeq, hReq, hQ1e, hQ2e]; module
    · rw [hdP1, hdP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rw [hcP1, hcP2]; push_cast [he1f, he2f]; rw [hb1', hb3']; ring
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide
    · rcases he1pm with rfl | rfl <;> rcases he2pm with rfl | rfl <;> decide

/-- **The GLV-recoding chain.** `m` `EndoMul` rows over `Holds` (with base + threading + initial +
    the per-row `hxne`) compute the final accumulator `= 4^m·P₀ + k₁·T + k₂·φT`; the field casts of
    the GLV coefficients `(k₂, k₁)` are exactly `EndoScalar`'s Algorithm-2 `a`, `b` digit-sums over
    the shared crumbs. Every intermediate accumulator's nonsingularity is *derived* via
    `gate_advance`, so the prover supplies only `Holds`. -/
theorem endoMul_ab (W : WeierstrassCurve.Affine F) [Fact (Nat.Prime W.order)]
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hodd : W.order ≠ 2) (endo : F)
    (m : ℕ) (g : ℕ → Witness F) (hholds : ∀ i, i < m → Holds endo (g i))
    (T φT : W.Point)
    (hTns : W.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hφTns : W.Nonsingular (endo * (g 0).xT) (g 0).yT) (hφTeq : φT = Point.some _ _ hφTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).xP = (g i).xS ∧ (g (i + 1)).yP = (g i).yS)
    (hP0ns : W.Nonsingular (g 0).xP (g 0).yP)
    (hxne : ∀ i, i < m → (g i).xP ≠ (1 + (endo - 1) * (g i).b1) * (g i).xT
                        ∧ (g i).xR ≠ (1 + (endo - 1) * (g i).b3) * (g i).xT) :
    ∃ (hfin : W.Nonsingular (accX g m) (accY g m)) (k1 k2 : ℤ),
      Point.some _ _ hfin = (4 : ℤ) ^ m • Point.some _ _ hP0ns + k1 • T + k2 • φT
        ∧ (k2 : F) = ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * aDigit g j
        ∧ (k1 : F) = ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * bDigit g j := by
  -- coordinate threading: row `i`'s input column equals the accumulator at step `i`
  have haccP : ∀ k, k < m → (g k).xP = accX g k ∧ (g k).yP = accY g k := by
    intro k hk
    cases k with
    | zero => exact ⟨rfl, rfl⟩
    | succ j => exact hthread j hk
  -- per-step accumulator nonsingularity, derived by threading `gate_advance`
  have key : ∀ k, k ≤ m → W.Nonsingular (accX g k) (accY g k) := by
    intro k
    induction k with
    | zero => intro _; exact hP0ns
    | succ j ih =>
      intro hj
      have hj' : j < m := by omega
      obtain ⟨hxP, hyP⟩ := haccP j hj'
      have hPj : W.Nonsingular (g j).xP (g j).yP := by rw [hxP, hyP]; exact ih (by omega)
      have hTj : W.Nonsingular (g j).xT (g j).yT := by
        obtain ⟨hx, hy⟩ := hbase j hj'; rw [hx, hy]; exact hTns
      have hφTj : W.Nonsingular (endo * (g j).xT) (g j).yT := by
        obtain ⟨hx, hy⟩ := hbase j hj'; rw [hx, hy]; exact hφTns
      obtain ⟨hxn1, hxn2⟩ := hxne j hj'
      obtain ⟨hSj, -⟩ :=
        gate_advance W ha h2 h3 hodd endo (g j) (hholds j hj') hTj hφTj hPj hxn1 hxn2
      exact hSj
  -- the accumulator chain as a point function over the derived per-step nonsingularity
  set P : ℕ → W.Point := fun k => if hk : k ≤ m then Point.some _ _ (key k hk) else 0 with hPdef
  have hPval : ∀ k (hk : k ≤ m), P k = Point.some _ _ (key k hk) := by
    intro k hk; rw [hPdef]; exact dif_pos hk
  -- per-row GLV contribution, read straight off `gate_advance` (no bundle, no `endoMul`)
  have hrow : ∀ i, i < m → ∃ c1 c2 : ℤ,
      P (i + 1) = (4 : ℤ) • P i + c1 • T + c2 • φT
        ∧ (c1 : F) = 2 * dPoly ((g i).b2 + 2 * (g i).b1) + dPoly ((g i).b4 + 2 * (g i).b3)
        ∧ (c2 : F) = 2 * cPoly ((g i).b2 + 2 * (g i).b1) + cPoly ((g i).b4 + 2 * (g i).b3) := by
    intro i hi
    obtain ⟨hxP, hyP⟩ := haccP i hi
    have hPi : W.Nonsingular (g i).xP (g i).yP := by rw [hxP, hyP]; exact key i (le_of_lt hi)
    have hTi : W.Nonsingular (g i).xT (g i).yT := by
      obtain ⟨hx, hy⟩ := hbase i hi; rw [hx, hy]; exact hTns
    have hφTi : W.Nonsingular (endo * (g i).xT) (g i).yT := by
      obtain ⟨hx, hy⟩ := hbase i hi; rw [hx, hy]; exact hφTns
    obtain ⟨hxn1, hxn2⟩ := hxne i hi
    obtain ⟨hS, c1, c2, hrel, hd1, hd2, -, -⟩ :=
      gate_advance W ha h2 h3 hodd endo (g i) (hholds i hi) hTi hφTi hPi hxn1 hxn2
    refine ⟨c1, c2, ?_, hd1, hd2⟩
    rw [hPval (i + 1) hi, hPval i (le_of_lt hi),
      some_congr W (key (i + 1) hi) hS rfl rfl,
      some_congr W (key i (le_of_lt hi)) hPi hxP.symm hyP.symm, hTeq,
      some_congr W hTns hTi (hbase i hi).1.symm (hbase i hi).2.symm, hφTeq,
      some_congr W hφTns hφTi (by rw [(hbase i hi).1]) (hbase i hi).2.symm]
    exact hrel
  choose! c1 c2 hc using hrow
  have hstep : ∀ i, i < m → P (i + 1) = (4 : ℤ) • P i + c1 i • T + c2 i • φT :=
    fun i hi => (hc i hi).1
  -- fold the chain and identify the scalar with `EndoScalar.toField` (cf. the old `endoMul_ab`)
  set k1 := ∑ i ∈ Finset.range m, (4 : ℤ) ^ (m - 1 - i) * c1 i with hk1def
  set k2 := ∑ i ∈ Finset.range m, (4 : ℤ) ^ (m - 1 - i) * c2 i with hk2def
  have hPm : P m = (4 : ℤ) ^ m • P 0 + k1 • T + k2 • φT := chain_endo W m P T φT c1 c2 hstep
  have hk2 : (k2 : F) = ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * aDigit g j := by
    rw [hk2def, ← sum_reindex m (aDigit g)]; push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < m := Finset.mem_range.mp hi
    have e1 : (2 * i) % 2 = 0 := by omega
    have e2 : (2 * i) / 2 = i := by omega
    have e3 : (2 * i + 1) % 2 = 1 := by omega
    have e4 : (2 * i + 1) / 2 = i := by omega
    have haE : aDigit g (2 * i) = cPoly ((g i).b2 + 2 * (g i).b1) := by simp [aDigit, e1, e2]
    have haO : aDigit g (2 * i + 1) = cPoly ((g i).b4 + 2 * (g i).b3) := by simp [aDigit, e3, e4]
    rw [haE, haO, ← (hc i hi').2.2]
  have hk1 : (k1 : F) = ∑ j ∈ Finset.range (2 * m), (2 : F) ^ (2 * m - 1 - j) * bDigit g j := by
    rw [hk1def, ← sum_reindex m (bDigit g)]; push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < m := Finset.mem_range.mp hi
    have e1 : (2 * i) % 2 = 0 := by omega
    have e2 : (2 * i) / 2 = i := by omega
    have e3 : (2 * i + 1) % 2 = 1 := by omega
    have e4 : (2 * i + 1) / 2 = i := by omega
    have hbE : bDigit g (2 * i) = dPoly ((g i).b2 + 2 * (g i).b1) := by simp [bDigit, e1, e2]
    have hbO : bDigit g (2 * i + 1) = dPoly ((g i).b4 + 2 * (g i).b3) := by simp [bDigit, e3, e4]
    rw [hbE, hbO, ← (hc i hi').2.1]
  refine ⟨key m (le_refl m), k1, k2, ?_, hk2, hk1⟩
  rw [← hPval m (le_refl m), hPm, hPval 0 (Nat.zero_le m),
    some_congr W (key 0 (Nat.zero_le m)) hP0ns rfl rfl]

/-- **EndoMul — the capstone.** At the real init `P₀ = 2(T + φT)` and eigenvalue `φT = [λ]·T`, the
    rows compute the final accumulator `= [s]·T` with `s = EndoScalar.toField (crumbList g m) λ`:
    EndoMul multiplies the base by exactly the scalar EndoScalar decodes. The prover supplies only
    `Holds` per row + base + threading + initial; the intermediate nonsingularity is derived and
    `hxne` is the lone coordinate side-condition (the curve layer discharges it via
    `accumulator_chain`). Specializes to the curves as `{pallas,vesta}_endoMul`. -/
theorem endoMul (W : WeierstrassCurve.Affine F) [Fact (Nat.Prime W.order)]
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hodd : W.order ≠ 2) (endo : F)
    (m : ℕ) (g : ℕ → Witness F) (hholds : ∀ i, i < m → Holds endo (g i))
    (T φT : W.Point)
    (hTns : W.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hφTns : W.Nonsingular (endo * (g 0).xT) (g 0).yT) (hφTeq : φT = Point.some _ _ hφTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).xP = (g i).xS ∧ (g (i + 1)).yP = (g i).yS)
    (hP0ns : W.Nonsingular (g 0).xP (g 0).yP)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T + (2 : ℤ) • φT)
    (hxne : ∀ i, i < m → (g i).xP ≠ (1 + (endo - 1) * (g i).b1) * (g i).xT
                        ∧ (g i).xR ≠ (1 + (endo - 1) * (g i).b3) * (g i).xT)
    (lam : ℤ) (heig : φT = lam • T) :
    ∃ (hfin : W.Nonsingular (accX g m) (accY g m)) (s : ℤ),
      Point.some _ _ hfin = s • T
        ∧ (s : F) = Kimchi.Circuit.EndoScalar.toField (crumbList g m) (lam : F) := by
  obtain ⟨hfin, k1, k2, hPm, hk2, hk1⟩ :=
    endoMul_ab W ha h2 h3 hodd endo m g hholds T φT hTns hTeq hφTns hφTeq hbase hthread hP0ns hxne
  refine ⟨hfin, 2 * 4 ^ m + k1 + (2 * 4 ^ m + k2) * lam, ?_, ?_⟩
  · rw [hPm, hP0, heig]; module
  · simp +decide [EndoScalar.toField, hk1, hk2]
    rw [decompose_crumbList g m |>.1, decompose_crumbList g m |>.2]; ring

/-- **Producing variant of `one_window`.** Given the bounded input accumulator form `[a]·T + [b]·φT`
    and a window's constraints, derives the window's first-addition non-degeneracy `hxne` and
    advances to the next bounded form, handing back the on-curve output point — the output
    accumulator's nonsingularity `hO` is *produced* (via `block_produce`) rather than consumed. -/
theorem one_window_produce (W : WeierstrassCurve.Affine F)
    [Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)] [Fact (Nat.Prime W.order)]
    (T φT : W.Point)
    (off : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → |a| < 2 ^ 126 → |b| < 2 ^ 126 →
      a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T
        ∧ a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT)
    {endo bf bs xT yT : F} (hT : W.Nonsingular xT yT) (hφT : W.Nonsingular (endo * xT) yT)
    (hTeq : T = Point.some _ _ hT) (hφTeq : φT = Point.some _ _ hφT)
    (hbf : bf = 0 ∨ bf = 1) (hbs : bs = 0 ∨ bs = 1)
    {xI yI xO yO s : F} (hI : W.Nonsingular xI yI)
    (a b : ℤ) (hIeq : Point.some _ _ hI = a • T + b • φT)
    (ha2 : 2 ≤ a) (haH : a < 2 ^ 126) (hb2 : 2 ≤ b) (hbH : b < 2 ^ 126)
    (hxIO : xO ≠ xI)
    (htne : 2 * xI - s ^ 2 + (1 + (endo - 1) * bf) * xT ≠ 0)
    (hs : ((1 + (endo - 1) * bf) * xT - xI) * s = (2 * bs - 1) * yT - yI)
    (hc2 : (2 * xI - s ^ 2 + (1 + (endo - 1) * bf) * xT) * ((xI - xO) * s + yO + yI)
        = (xI - xO) * (2 * yI))
    (hc3 : (yO + yI) ^ 2 = (xI - xO) ^ 2 * (s ^ 2 - (1 + (endo - 1) * bf) * xT + xO)) :
    xI ≠ (1 + (endo - 1) * bf) * xT
      ∧ ∃ (hO : W.Nonsingular xO yO) (a' b' : ℤ), Point.some _ _ hO = a' • T + b' • φT
          ∧ 2 * a - 1 ≤ a' ∧ a' ≤ 2 * a + 1 ∧ 2 * b - 1 ≤ b' ∧ b' ≤ 2 * b + 1 := by
  have ha' : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 := Fact.out
  have hQ := Kimchi.Gate.EndoMul.target_nonsingular W ha' hT hφT hbf hbs
  have hsel := selectQ' W ha' hT hφT hQ hbf hbs
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have haabs : |a| < 2 ^ 126 := by rw [abs_of_pos (by omega : (0 : ℤ) < a)]; exact haH
  have hbabs : |b| < 2 ^ 126 := by rw [abs_of_pos (by omega : (0 : ℤ) < b)]; exact hbH
  have hoff := off a b ha0 hb0 haabs hbabs
  have hxne : xI ≠ (1 + (endo - 1) * bf) * xT := by
    rcases hsel with ⟨e, hQe, he⟩ | ⟨e, hQe, he⟩ <;> rcases he with rfl | rfl <;>
      refine Kimchi.Circuit.VarBaseMul.x_ne_xT_of_ne_base W hI hQ ?_ ?_ <;>
      simp only [hIeq, hQe, ← hTeq, ← hφTeq, one_zsmul, neg_one_zsmul, neg_neg] <;>
      first
        | exact hoff.1 | exact hoff.2.1 | exact hoff.2.2.1 | exact hoff.2.2.2
  refine ⟨hxne, ?_⟩
  obtain ⟨hO, hO_eq⟩ := block_produce W ha' hI hQ hxne htne hxIO hs hc2 hc3
  refine ⟨hO, ?_⟩
  rcases hsel with ⟨e, hQe, he⟩ | ⟨e, hQe, he⟩
  · rcases he with rfl | rfl
    · exact ⟨2 * a + 1, 2 * b, by rw [hO_eq, hIeq, hQe, ← hTeq]; module,
        by omega, by omega, by omega, by omega⟩
    · exact ⟨2 * a - 1, 2 * b, by rw [hO_eq, hIeq, hQe, ← hTeq]; module,
        by omega, by omega, by omega, by omega⟩
  · rcases he with rfl | rfl
    · exact ⟨2 * a, 2 * b + 1, by rw [hO_eq, hIeq, hQe, ← hφTeq]; module,
        by omega, by omega, by omega, by omega⟩
    · exact ⟨2 * a, 2 * b - 1, by rw [hO_eq, hIeq, hQe, ← hφTeq]; module,
        by omega, by omega, by omega, by omega⟩

/-- **Deriving `hxne` from the GLV bound.** The fused induction: from the leaner hypotheses + the
    GLV off-targets fact `off` (`= combo_off_targets`), each accumulator point is `[A]·T + [B]·φT`
    with `A, B ∈ [4ⁱ+1, 3·4ⁱ−1]` (so `< 2¹²⁶`), which yields the per-row first-addition
    non-degeneracy `hxne`. The nonsingularity is derived inside the same induction (via
    `gate_advance`), not consumed from a bundle. -/
theorem accumulator_chain (W : WeierstrassCurve.Affine F)
    [Fact (W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)] [Fact (Nat.Prime W.order)]
    (h2 : (2 : F) ≠ 0) (hodd : W.order ≠ 2) (endo : F)
    (T φT : W.Point)
    (off : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → |a| < 2 ^ 126 → |b| < 2 ^ 126 →
      a • T + b • φT ≠ T ∧ a • T + b • φT ≠ -T
        ∧ a • T + b • φT ≠ φT ∧ a • T + b • φT ≠ -φT)
    (m : ℕ) (hbits : 4 * m ≤ 244) (g : ℕ → Witness F)
    (hholds : ∀ i, i < m → Holds endo (g i))
    (hTns : W.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hφTns : W.Nonsingular (endo * (g 0).xT) (g 0).yT) (hφTeq : φT = Point.some _ _ hφTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).xP = (g i).xS ∧ (g (i + 1)).yP = (g i).yS)
    (hP0ns : W.Nonsingular (g 0).xP (g 0).yP)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T + (2 : ℤ) • φT) :
    ∀ i, i < m → (g i).xP ≠ (1 + (endo - 1) * (g i).b1) * (g i).xT
                ∧ (g i).xR ≠ (1 + (endo - 1) * (g i).b3) * (g i).xT := by
  have ha' : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 := Fact.out
  -- coordinate threading: row `i`'s input column equals the accumulator at step `i`
  have haccP : ∀ k, k < m → (g k).xP = accX g k ∧ (g k).yP = accY g k := by
    intro k hk
    cases k with
    | zero => exact ⟨rfl, rfl⟩
    | succ j => exact hthread j hk
  -- the fused invariant: each step's accumulator is `[A]·T + [B]·φT`, bounded; nonsingularity
  -- is produced (`one_window_produce`) rather than consumed from a bundle.
  have inv : ∀ i, i ≤ m → ∃ (hPi : W.Nonsingular (accX g i) (accY g i)) (A B : ℤ),
      Point.some _ _ hPi = A • T + B • φT
        ∧ (4 : ℤ) ^ i + 1 ≤ A ∧ A ≤ 3 * 4 ^ i - 1
        ∧ (4 : ℤ) ^ i + 1 ≤ B ∧ B ≤ 3 * 4 ^ i - 1 := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨hP0ns, 2, 2, hP0, by norm_num, by norm_num, by norm_num, by norm_num⟩
    | succ i ih =>
      intro hi
      have hi' : i < m := by omega
      obtain ⟨hPi', A, B, hPeq, hAlo, hAhi, hBlo, hBhi⟩ := ih (by omega)
      -- power bookkeeping (verbatim from `accumulator_invariant`)
      have h2i : 2 * i ≤ 120 := by omega
      have h4i : (4 : ℤ) ^ i ≤ 2 ^ 120 := by
        calc (4 : ℤ) ^ i = 2 ^ (2 * i) := by rw [pow_mul]; norm_num
          _ ≤ 2 ^ 120 := pow_le_pow_right₀ (by norm_num) h2i
      have h4ipos : (1 : ℤ) ≤ 4 ^ i := one_le_pow₀ (by norm_num)
      have hsucc : (4 : ℤ) ^ (i + 1) = 4 * 4 ^ i := by rw [pow_succ]; ring
      have hp125 : (3 : ℤ) * 2 ^ 120 < 2 ^ 126 := by norm_num
      have hp126 : (6 : ℤ) * 2 ^ 120 < 2 ^ 126 := by norm_num
      have hAlo2 : (2 : ℤ) ≤ A := by omega
      have hBlo2 : (2 : ℤ) ≤ B := by omega
      have hAlt : A < 2 ^ 126 := by omega
      have hBlt : B < 2 ^ 126 := by omega
      -- transport the input accumulator to row `i`'s column coordinates
      obtain ⟨hxP, hyP⟩ := haccP i hi'
      have hPi : W.Nonsingular (g i).xP (g i).yP := by rw [hxP, hyP]; exact hPi'
      have hIeq : Point.some _ _ hPi = A • T + B • φT :=
        (some_congr W hPi hPi' hxP hyP).trans hPeq
      -- per-row base nonsingularity and `T`/`φT` identification (base shared via `hbase`)
      have hTi : W.Nonsingular (g i).xT (g i).yT := by
        obtain ⟨hx, hy⟩ := hbase i hi'; rw [hx, hy]; exact hTns
      have hφTi : W.Nonsingular (endo * (g i).xT) (g i).yT := by
        obtain ⟨hx, hy⟩ := hbase i hi'; rw [hx, hy]; exact hφTns
      have hTeqi : T = Point.some _ _ hTi :=
        hTeq.trans (some_congr W hTns hTi (hbase i hi').1.symm (hbase i hi').2.symm)
      have hφTeqi : φT = Point.some _ _ hφTi :=
        hφTeq.trans (some_congr W hφTns hφTi (by rw [(hbase i hi').1]) (hbase i hi').2.symm)
      -- per-row constraints
      obtain ⟨hxPxR, hxRxS⟩ := distinctPoints endo (g i) (hholds i hi')
      have hcon := hholds i hi'
      rw [holds_iff] at hcon
      obtain ⟨hs1, hc2_1, hc3_1, hs3, hc2_3, hc3_3, _, hb1c, hb2c, hb3c, hb4c, _⟩ := hcon
      have hb1 := bool_of_mul hb1c
      have hb2 := bool_of_mul hb2c
      have hb3 := bool_of_mul hb3c
      have hb4 := bool_of_mul hb4c
      -- window 1: P → R
      have htne1 := block_tne W ha' h2 hodd hPi hxPxR hc2_1
      obtain ⟨_, hR, AR, BR, hReq, hARlo, hARhi, hBRlo, hBRhi⟩ :=
        one_window_produce W T φT off hTi hφTi hTeqi hφTeqi hb1 hb2 hPi A B hIeq
          hAlo2 hAlt hBlo2 hBlt (Ne.symm hxPxR) htne1 hs1 hc2_1 hc3_1
      have hARlo2 : (2 : ℤ) ≤ AR := by omega
      have hBRlo2 : (2 : ℤ) ≤ BR := by omega
      have hARlt : AR < 2 ^ 126 := by omega
      have hBRlt : BR < 2 ^ 126 := by omega
      -- window 2: R → S
      have htne2 := block_tne W ha' h2 hodd hR hxRxS hc2_3
      obtain ⟨_, hS, AS, BS, hSeq, hASlo, hAShi, hBSlo, hBShi⟩ :=
        one_window_produce W T φT off hTi hφTi hTeqi hφTeqi hb3 hb4 hR AR BR hReq
          hARlo2 hARlt hBRlo2 hBRlt (Ne.symm hxRxS) htne2 hs3 hc2_3 hc3_3
      exact ⟨hS, AS, BS, hSeq, by rw [hsucc]; omega, by rw [hsucc]; omega,
        by rw [hsucc]; omega, by rw [hsucc]; omega⟩
  -- read off each row's first-addition non-degeneracy from the invariant
  intro i hi
  obtain ⟨hPi', A, B, hPeq, hAlo, hAhi, hBlo, hBhi⟩ := inv i (le_of_lt hi)
  have h2i : 2 * i ≤ 120 := by omega
  have h4i : (4 : ℤ) ^ i ≤ 2 ^ 120 := by
    calc (4 : ℤ) ^ i = 2 ^ (2 * i) := by rw [pow_mul]; norm_num
      _ ≤ 2 ^ 120 := pow_le_pow_right₀ (by norm_num) h2i
  have h4ipos : (1 : ℤ) ≤ 4 ^ i := one_le_pow₀ (by norm_num)
  have hp126 : (6 : ℤ) * 2 ^ 120 < 2 ^ 126 := by norm_num
  have hAlo2 : (2 : ℤ) ≤ A := by omega
  have hBlo2 : (2 : ℤ) ≤ B := by omega
  have hAlt : A < 2 ^ 126 := by omega
  have hBlt : B < 2 ^ 126 := by omega
  obtain ⟨hxP, hyP⟩ := haccP i hi
  have hPi : W.Nonsingular (g i).xP (g i).yP := by rw [hxP, hyP]; exact hPi'
  have hIeq : Point.some _ _ hPi = A • T + B • φT := (some_congr W hPi hPi' hxP hyP).trans hPeq
  have hTi : W.Nonsingular (g i).xT (g i).yT := by
    obtain ⟨hx, hy⟩ := hbase i hi; rw [hx, hy]; exact hTns
  have hφTi : W.Nonsingular (endo * (g i).xT) (g i).yT := by
    obtain ⟨hx, hy⟩ := hbase i hi; rw [hx, hy]; exact hφTns
  have hTeqi : T = Point.some _ _ hTi :=
    hTeq.trans (some_congr W hTns hTi (hbase i hi).1.symm (hbase i hi).2.symm)
  have hφTeqi : φT = Point.some _ _ hφTi :=
    hφTeq.trans (some_congr W hφTns hφTi (by rw [(hbase i hi).1]) (hbase i hi).2.symm)
  obtain ⟨hxPxR, hxRxS⟩ := distinctPoints endo (g i) (hholds i hi)
  have hcon := hholds i hi
  rw [holds_iff] at hcon
  obtain ⟨hs1, hc2_1, hc3_1, hs3, hc2_3, hc3_3, _, hb1c, hb2c, hb3c, hb4c, _⟩ := hcon
  have hb1 := bool_of_mul hb1c
  have hb2 := bool_of_mul hb2c
  have hb3 := bool_of_mul hb3c
  have hb4 := bool_of_mul hb4c
  -- window 1 derives the first conjunct (and hands back `R`)
  have htne1 := block_tne W ha' h2 hodd hPi hxPxR hc2_1
  obtain ⟨hxne1, hR, AR, BR, hReq, hARlo, hARhi, hBRlo, hBRhi⟩ :=
    one_window_produce W T φT off hTi hφTi hTeqi hφTeqi hb1 hb2 hPi A B hIeq
      hAlo2 hAlt hBlo2 hBlt (Ne.symm hxPxR) htne1 hs1 hc2_1 hc3_1
  have hARlo2 : (2 : ℤ) ≤ AR := by omega
  have hBRlo2 : (2 : ℤ) ≤ BR := by omega
  have hARlt : AR < 2 ^ 126 := by omega
  have hBRlt : BR < 2 ^ 126 := by omega
  -- window 2 derives the second conjunct
  have htne2 := block_tne W ha' h2 hodd hR hxRxS hc2_3
  obtain ⟨hxne2, _⟩ :=
    one_window_produce W T φT off hTi hφTi hTeqi hφTeqi hb3 hb4 hR AR BR hReq
      hARlo2 hARlt hBRlo2 hBRlt (Ne.symm hxRxS) htne2 hs3 hc2_3 hc3_3
  exact ⟨hxne1, hxne2⟩

end Kimchi.Circuit.EndoMul
