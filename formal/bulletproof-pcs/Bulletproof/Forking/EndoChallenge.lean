import Poseidon.FqSponge
import Pasta.Endo
import Mathlib

/-!
# The endo-expanded challenge map is injective and never zero (D3)

The deployed challenge domain is **not** the scalar field: `squeezeChallenge` squeezes a 128-bit
prechallenge and endo-expands it (`endoExpand`, Halo §6.2 `to_field_with_length`), so the round
challenges range over the image of `endoExpand` on `[0, 2¹²⁸)` — at most `2¹²⁸` values out of
`|F| ≈ 2²⁵⁴`. Instantiating the forking game at `α := F` would make its counting hypothesis
arithmetically unsatisfiable (the W5 scope doc's B3); the game must run over the **prechallenge**
domain, with acceptance composed through `endoExpand`. That transport needs exactly two facts,
proved here per curve:

* **injectivity on 128-bit inputs** — distinct prechallenges give distinct field challenges, so
  the fork tree's distinctness survives the composition;
* **nonvanishing** — an endo-expanded challenge is never `0`, so the nonzero side condition of
  the fork tree holds for *every* prechallenge (`Extractable`'s own nonzero guarantee on the
  prechallenge is not even needed).

## The argument

`endoExpand` computes `a·λ + b` where `(a, b)` accumulate over the 64 two-bit windows of the
prechallenge: both start at `2`, each step doubles both and adds `±1` to exactly one of them.
So over `ℤ` (the model `endoAcc`):

* `1 ≤ a, b ≤ 2⁶⁶` (`endoAcc_bound`) — the accumulators are *short*;
* the window bits are recoverable from `(a, b)` — exactly one of the pair is odd at each
  unwinding step — so `chal ↦ endoAcc chal` is injective on `[0, 2¹²⁸)` (`endoAcc_injOn`);
* two colliding challenges give `(a₁−a₂)·λ + (b₁−b₂) = 0` in `ZMod order` with differences
  bounded by `2⁶⁷ ≤ 2¹²⁶` — a **short GLV relation**, which `{vesta,pallas}_glv_no_short_relation`
  (`Pasta/Endo.lean`, certificate-backed) refutes unless both differences vanish; then
  `endoAcc_injOn` finishes. Nonvanishing is the same refutation at `(a, b)` itself, using
  `1 ≤ a`.

Only bits `0..127` are read (`List.range 64`), so `endoAcc_bound` needs no size hypothesis and
injectivity genuinely requires the `< 2¹²⁸` bounds.
-/

namespace Bulletproof.Forking

open Poseidon CompElliptic.Fields.Pasta

/-- The integer model of `endoExpand`'s accumulator fold: the same recursion over `ℤ × ℤ`. -/
private def endoAcc (chal : ℕ) : ℤ × ℤ :=
  (List.range 64).reverse.foldl
    (fun (ab : ℤ × ℤ) i =>
      let (a, b) := (2 * ab.1, 2 * ab.2)
      let s : ℤ := if chal.testBit (2 * i) then 1 else -1
      if chal.testBit (2 * i + 1) then (a + s, b) else (a, b + s))
    (2, 2)

/-! ## Structural step functions and the fold recursion

The accumulator fold's per-window step is factored out as `zstep` (the `ℤ` model, matching
`endoAcc`'s lambda body verbatim) and `fstep` (its `F` twin, matching `endoExpand`'s). The
closed forms and the commutation with `Int.cast` are then plain inductions on the window list. -/

/-- The integer per-window step, definitionally the body of `endoAcc`'s fold (the `let`s
inlined so structure projections reduce for `omega`). -/
private def zstep (n : ℕ) (ab : ℤ × ℤ) (i : ℕ) : ℤ × ℤ :=
  if n.testBit (2 * i + 1)
  then (2 * ab.1 + (if n.testBit (2 * i) then 1 else -1), 2 * ab.2)
  else (2 * ab.1, 2 * ab.2 + (if n.testBit (2 * i) then 1 else -1))

/-- The field per-window step, definitionally the body of `endoExpand`'s fold. -/
private def fstep {F : Type*} [Field F] (chal : ℕ) (ab : F × F) (i : ℕ) : F × F :=
  if chal.testBit (2 * i + 1)
  then (2 * ab.1 + (if chal.testBit (2 * i) then 1 else -1), 2 * ab.2)
  else (2 * ab.1, 2 * ab.2 + (if chal.testBit (2 * i) then 1 else -1))

/-- The window's low-bit sign `σ j = ±1`. -/
private def sigmaBit (n j : ℕ) : ℤ := if n.testBit (2 * j) then 1 else -1

/-- The window's high-bit sign `ε j = ±1` (chooses which accumulator receives `σ j`). -/
private def epsBit (n j : ℕ) : ℤ := if n.testBit (2 * j + 1) then 1 else -1

/-- `endoAcc` is the `zstep` fold, by definition. -/
private theorem endoAcc_eq_foldl (n : ℕ) :
    endoAcc n = (List.range 64).reverse.foldl (zstep n) (2, 2) := rfl

/-- Peel the top window off a reversed-range fold: window `k` is processed first. -/
private theorem foldl_reverse_range_succ {α : Type*} (f : α → ℕ → α) (a : α) (k : ℕ) :
    (List.range (k + 1)).reverse.foldl f a = (List.range k).reverse.foldl f (f a k) := by
  rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.foldl_cons]

/-! ## Target 1: the fold commutes with `Int.cast` -/

/-- One `fstep` on a cast pair equals the cast of one `zstep`. -/
private theorem fstep_cast {F : Type*} [Field F] (chal : ℕ) (p : ℤ × ℤ) (i : ℕ) :
    fstep chal ((p.1 : F), (p.2 : F)) i
      = (((zstep chal p i).1 : F), ((zstep chal p i).2 : F)) := by
  unfold fstep zstep
  split_ifs <;> simp only [Prod.mk.injEq] <;> constructor <;> push_cast <;> ring

/-- The `fstep` fold over any window list equals the cast of the `zstep` fold. -/
private theorem foldl_cast {F : Type*} [Field F] (chal : ℕ) (l : List ℕ) (p : ℤ × ℤ) :
    l.foldl (fstep chal) ((p.1 : F), (p.2 : F))
      = (((l.foldl (zstep chal) p).1 : F), ((l.foldl (zstep chal) p).2 : F)) := by
  induction l generalizing p with
  | nil => simp
  | cons i t ih =>
    simp only [List.foldl_cons]
    rw [fstep_cast]
    exact ih (zstep chal p i)

/-- `endoExpand` unfolded as the `fstep` fold. Unfolding both `endoExpand` and `fstep` makes the
two folds syntactically identical, so only structure eta on the (un-evaluated) fold result
remains — the 64-window reduction is never forced. -/
private theorem endoExpand_eq_fstep {F : Type*} [Field F] (lam : F) (chal : ℕ) :
    FqSponge.endoExpand lam chal
      = ((List.range 64).reverse.foldl (fstep chal) ((2 : F), (2 : F))).1 * lam
        + ((List.range 64).reverse.foldl (fstep chal) ((2 : F), (2 : F))).2 := by
  unfold FqSponge.endoExpand fstep
  dsimp only

/-- `endoExpand` is the cast of the integer model: the field fold commutes with `Int.cast`
step by step. -/
private theorem endoExpand_eq_endoAcc {F : Type*} [Field F] (lam : F) (chal : ℕ) :
    FqSponge.endoExpand lam chal
      = ((endoAcc chal).1 : F) * lam + ((endoAcc chal).2 : F) := by
  rw [endoExpand_eq_fstep, endoAcc_eq_foldl]
  have key : (List.range 64).reverse.foldl (fstep chal) ((2 : F), (2 : F))
      = ((((List.range 64).reverse.foldl (zstep chal) (2, 2)).1 : F),
          (((List.range 64).reverse.foldl (zstep chal) (2, 2)).2 : F)) := by
    have h := foldl_cast (F := F) chal (List.range 64).reverse ((2 : ℤ), (2 : ℤ))
    simpa using h
  rw [key]

/-! ## Target 2: the accumulators are short -/

/-- One `zstep` keeps both components in `[1, 2B+1]` given both start in `[1, B]`. -/
private theorem zstep_bounds (n : ℕ) (p : ℤ × ℤ) (i : ℕ) (B : ℤ)
    (h1 : 1 ≤ p.1) (h2 : p.1 ≤ B) (h3 : 1 ≤ p.2) (h4 : p.2 ≤ B) :
    1 ≤ (zstep n p i).1 ∧ (zstep n p i).1 ≤ 2 * B + 1 ∧
      1 ≤ (zstep n p i).2 ∧ (zstep n p i).2 ≤ 2 * B + 1 := by
  unfold zstep
  split_ifs <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The fold invariant: from a start in `[1, B]²`, after `l.length` windows both
components lie in `[1, (B+1)·2^l.length]`. -/
private theorem foldl_bound (n : ℕ) (l : List ℕ) :
    ∀ (p : ℤ × ℤ) (B : ℤ), 1 ≤ p.1 → p.1 ≤ B → 1 ≤ p.2 → p.2 ≤ B →
      1 ≤ (l.foldl (zstep n) p).1 ∧ (l.foldl (zstep n) p).1 ≤ (B + 1) * 2 ^ l.length ∧
        1 ≤ (l.foldl (zstep n) p).2 ∧ (l.foldl (zstep n) p).2 ≤ (B + 1) * 2 ^ l.length := by
  induction l with
  | nil =>
    intro p B h1 h2 h3 h4
    simp only [List.foldl_nil, List.length_nil, pow_zero, mul_one]
    omega
  | cons i t ih =>
    intro p B h1 h2 h3 h4
    simp only [List.foldl_cons, List.length_cons]
    obtain ⟨z1, z2, z3, z4⟩ := zstep_bounds n p i B h1 h2 h3 h4
    obtain ⟨a1, a2, a3, a4⟩ := ih (zstep n p i) (2 * B + 1) z1 z2 z3 z4
    have hpow : (B + 1) * 2 ^ (t.length + 1) = (2 * B + 1 + 1) * 2 ^ t.length := by
      rw [pow_succ]; ring
    refine ⟨a1, ?_, a3, ?_⟩
    · rw [hpow]; exact a2
    · rw [hpow]; exact a4

/-- The accumulators are short: both components of `endoAcc` lie in `[1, 2⁶⁶]`. The invariant is
`1 ≤ x ≤ B ⟹ 1 ≤ 2x ± 1 ≤ 2B + 1`, folded 64 times from `B = 2`. -/
private theorem endoAcc_bound (chal : ℕ) :
    1 ≤ (endoAcc chal).1 ∧ (endoAcc chal).1 ≤ 2 ^ 66 ∧
      1 ≤ (endoAcc chal).2 ∧ (endoAcc chal).2 ≤ 2 ^ 66 := by
  rw [endoAcc_eq_foldl]
  obtain ⟨b1, b2, b3, b4⟩ :=
    foldl_bound chal (List.range 64).reverse (2, 2) 2 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  simp only [List.length_reverse, List.length_range] at b2 b4
  have hle : (2 + 1) * (2 : ℤ) ^ 64 ≤ 2 ^ 66 := by norm_num
  exact ⟨b1, le_trans b2 hle, b3, le_trans b4 hle⟩

/-! ## Target 3: injectivity on 128-bit inputs

The route is closed-form: `(endoAcc n).1 + (endoAcc n).2 = 2⁶⁶ + ∑ σ_j 2^j` and
`(endoAcc n).1 − (endoAcc n).2 = ∑ ε_j σ_j 2^j`, both full-support signed sums. A full-support
signed representation is unique (the top digit is the sign, then recurse), so equal accumulators
force equal `σ` and `ε` digits, hence equal bits. -/

/-- The `±1` sign encodings determine the underlying bit. -/
private theorem signVal_inj {b c : Bool}
    (h : (if b then (1 : ℤ) else -1) = if c then 1 else -1) : b = c := by
  cases b <;> cases c <;> revert h <;> decide

/-- One `zstep`'s effect on the component sum: `+σ_k`. -/
private theorem zstep_sum (n : ℕ) (p : ℤ × ℤ) (k : ℕ) :
    (zstep n p k).1 + (zstep n p k).2 = 2 * (p.1 + p.2) + sigmaBit n k := by
  unfold zstep sigmaBit
  split_ifs <;> ring

/-- One `zstep`'s effect on the component difference: `+ε_k σ_k`. -/
private theorem zstep_diff (n : ℕ) (p : ℤ × ℤ) (k : ℕ) :
    (zstep n p k).1 - (zstep n p k).2 = 2 * (p.1 - p.2) + epsBit n k * sigmaBit n k := by
  unfold zstep epsBit sigmaBit
  split_ifs <;> ring

/-- Closed form for the component sum of a reversed-range `zstep` fold. -/
private theorem foldl_sum (n k : ℕ) (p : ℤ × ℤ) :
    ((List.range k).reverse.foldl (zstep n) p).1
      + ((List.range k).reverse.foldl (zstep n) p).2
      = (p.1 + p.2) * 2 ^ k + ∑ i ∈ Finset.range k, sigmaBit n i * 2 ^ i := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [foldl_reverse_range_succ, ih, zstep_sum, Finset.sum_range_succ, pow_succ]
    ring

/-- Closed form for the component difference of a reversed-range `zstep` fold. -/
private theorem foldl_diff (n k : ℕ) (p : ℤ × ℤ) :
    ((List.range k).reverse.foldl (zstep n) p).1
      - ((List.range k).reverse.foldl (zstep n) p).2
      = (p.1 - p.2) * 2 ^ k + ∑ i ∈ Finset.range k, epsBit n i * sigmaBit n i * 2 ^ i := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [foldl_reverse_range_succ, ih, zstep_diff, Finset.sum_range_succ, pow_succ]
    ring

/-- The accumulator sum in closed form. -/
private theorem endoAcc_sum (n : ℕ) :
    (endoAcc n).1 + (endoAcc n).2 = 2 ^ 66 + ∑ i ∈ Finset.range 64, sigmaBit n i * 2 ^ i := by
  rw [endoAcc_eq_foldl, foldl_sum]
  norm_num

/-- The accumulator difference in closed form. -/
private theorem endoAcc_diff (n : ℕ) :
    (endoAcc n).1 - (endoAcc n).2 = ∑ i ∈ Finset.range 64, epsBit n i * sigmaBit n i * 2 ^ i := by
  rw [endoAcc_eq_foldl, foldl_diff]
  simp

/-- A full-support `±1` signed sum over `range k` is bounded by `2^k − 1` in absolute value. -/
private theorem sum_bound (k : ℕ) (d : ℕ → ℤ) (hd : ∀ j < k, d j = 1 ∨ d j = -1) :
    (∑ j ∈ Finset.range k, d j * 2 ^ j) ≤ 2 ^ k - 1
      ∧ -(2 ^ k - 1) ≤ ∑ j ∈ Finset.range k, d j * 2 ^ j := by
  induction k with
  | zero => simp
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun j hj => hd j (by omega))
    have hdm := hd m (by omega)
    have h2 : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    have hpos : (0 : ℤ) < 2 ^ m := by positivity
    rw [Finset.sum_range_succ]
    rcases hdm with hdm | hdm <;> rw [hdm] <;> constructor <;> omega

/-- Full-support `±1` signed representations are unique: equal sums force equal digits. The top
digit is recovered as the sign (the lower digits are too small to flip it), then recurse. -/
private theorem signed_unique : ∀ (k : ℕ) (d e : ℕ → ℤ),
    (∀ j < k, d j = 1 ∨ d j = -1) → (∀ j < k, e j = 1 ∨ e j = -1) →
    (∑ j ∈ Finset.range k, d j * 2 ^ j = ∑ j ∈ Finset.range k, e j * 2 ^ j) →
    ∀ j < k, d j = e j := by
  intro k
  induction k with
  | zero => intro d e _ _ _ j hj; omega
  | succ m ih =>
    intro d e hd he heq j hj
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at heq
    obtain ⟨hdub, hdlb⟩ := sum_bound m d (fun i hi => hd i (by omega))
    obtain ⟨heub, helb⟩ := sum_bound m e (fun i hi => he i (by omega))
    have hdm := hd m (by omega)
    have hem := he m (by omega)
    have hpos : (0 : ℤ) < 2 ^ m := by positivity
    have hdme : d m = e m := by
      rcases hdm with hh | hh <;> rcases hem with hh' | hh' <;>
        simp only [hh, hh'] at heq ⊢ <;> omega
    have hLeq : ∑ i ∈ Finset.range m, d i * 2 ^ i = ∑ i ∈ Finset.range m, e i * 2 ^ i := by
      rw [hdme] at heq; exact add_right_cancel heq
    have htail := ih d e (fun i hi => hd i (by omega)) (fun i hi => he i (by omega)) hLeq
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj' | hj'
    · exact htail j hj'
    · subst hj'; exact hdme

/-- The window encoding is injective on 128-bit prechallenges: the accumulator pair determines
the bits. Unwinding one step, exactly one of the pair is odd — that parity is the window's high
bit, the odd component's residue mod 4 is the window's low bit — and the quotients recurse. -/
private theorem endoAcc_injOn {m n : ℕ} (hm : m < 2 ^ 128) (hn : n < 2 ^ 128)
    (h : endoAcc m = endoAcc n) : m = n := by
  -- From equal accumulators, the SUM and DIFF closed forms agree.
  have hsum : ∑ i ∈ Finset.range 64, sigmaBit m i * 2 ^ i
      = ∑ i ∈ Finset.range 64, sigmaBit n i * 2 ^ i := by
    have hm' := endoAcc_sum m
    have hn' := endoAcc_sum n
    rw [h] at hm'
    have : (2 : ℤ) ^ 66 + ∑ i ∈ Finset.range 64, sigmaBit m i * 2 ^ i
        = 2 ^ 66 + ∑ i ∈ Finset.range 64, sigmaBit n i * 2 ^ i := hm'.symm.trans hn'
    exact add_left_cancel this
  have hdiff : ∑ i ∈ Finset.range 64, epsBit m i * sigmaBit m i * 2 ^ i
      = ∑ i ∈ Finset.range 64, epsBit n i * sigmaBit n i * 2 ^ i := by
    have hm' := endoAcc_diff m
    have hn' := endoAcc_diff n
    rw [h] at hm'
    exact hm'.symm.trans hn'
  -- Digit uniqueness: σ agrees, then εσ agrees, hence ε agrees.
  have hσ : ∀ j < 64, sigmaBit m j = sigmaBit n j :=
    signed_unique 64 (sigmaBit m) (sigmaBit n)
      (fun j _ => by unfold sigmaBit; split_ifs <;> simp)
      (fun j _ => by unfold sigmaBit; split_ifs <;> simp) hsum
  have hεσ : ∀ j < 64, epsBit m j * sigmaBit m j = epsBit n j * sigmaBit n j :=
    signed_unique 64 (fun j => epsBit m j * sigmaBit m j) (fun j => epsBit n j * sigmaBit n j)
      (fun j _ => by dsimp only; unfold epsBit sigmaBit; split_ifs <;> simp)
      (fun j _ => by dsimp only; unfold epsBit sigmaBit; split_ifs <;> simp) hdiff
  have hε : ∀ j < 64, epsBit m j = epsBit n j := by
    intro j hj
    have h1 := hσ j hj
    have h2 := hεσ j hj
    have hne : sigmaBit n j ≠ 0 := by unfold sigmaBit; split_ifs <;> simp
    rw [h1] at h2
    exact mul_right_cancel₀ hne h2
  -- Bits agree everywhere, so m = n.
  apply Nat.eq_of_testBit_eq
  intro p
  rcases lt_or_ge p 128 with hp | hp
  · rcases Nat.even_or_odd p with ⟨r, hr⟩ | ⟨r, hr⟩
    · have hr64 : r < 64 := by omega
      have he := hσ r hr64
      unfold sigmaBit at he
      have hbit := signVal_inj he
      have hp2 : p = 2 * r := by omega
      rw [hp2]; exact hbit
    · have hr64 : r < 64 := by omega
      have he := hε r hr64
      unfold epsBit at he
      have hbit := signVal_inj he
      have hp2 : p = 2 * r + 1 := by omega
      rw [hp2]; exact hbit
  · have hmp : m.testBit p = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hp))
    have hnp : n.testBit p = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) hp))
    rw [hmp, hnp]

/-! ## The per-curve assemblies

`Fp = ZMod PALLAS_BASE_CARD` is the Vesta-side challenge field and `Fq = ZMod PALLAS_SCALAR_CARD`
the Pallas-side one; the specs' eigenvalues are the integer casts of `Pasta.{vesta,pallas}Lam`,
which is what the GLV no-short-relation certificates are stated about. -/

private theorem cast_short_relation_eq_zero {q : ℕ} [NeZero q] {lamZ a₁ b₁ a₂ b₂ : ℤ}
    (h : (a₁ : ZMod q) * ((lamZ : ℤ) : ZMod q) + (b₁ : ZMod q)
        = (a₂ : ZMod q) * ((lamZ : ℤ) : ZMod q) + (b₂ : ZMod q)) :
    ((((b₁ - b₂) + (a₁ - a₂) * lamZ : ℤ) : ZMod q)) = 0 := by
  push_cast
  linear_combination h

/-- **Vesta-side injectivity**: `endoExpand` at the Vesta spec's eigenvalue is injective on
128-bit prechallenges. -/
theorem endoExpand_vesta_injOn {m n : ℕ} (hm : m < 2 ^ 128) (hn : n < 2 ^ 128)
    (h : FqSponge.endoExpand FqVesta.spec.lam m = FqSponge.endoExpand FqVesta.spec.lam n) :
    m = n := by
  rw [endoExpand_eq_endoAcc, endoExpand_eq_endoAcc] at h
  by_cases hacc : endoAcc m = endoAcc n
  · exact endoAcc_injOn hm hn hacc
  · exfalso
    obtain ⟨h1m, h2m, h3m, h4m⟩ := endoAcc_bound m
    obtain ⟨h1n, h2n, h3n, h4n⟩ := endoAcc_bound n
    have hz := cast_short_relation_eq_zero (q := PALLAS_BASE_CARD) h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    refine Pasta.vesta_glv_no_short_relation (a := (endoAcc m).2 - (endoAcc n).2)
      (b := (endoAcc m).1 - (endoAcc n).1) ?_ (by simp [abs_le]; omega) (by simp [abs_le]; omega)
      ?_
    · by_contra hboth
      push Not at hboth
      exact hacc (Prod.ext (by omega) (by omega))
    · rw [Pasta.vesta_card]
      exact hz

/-- **Vesta-side nonvanishing**: an endo-expanded challenge is never zero — its accumulator pair
is a short GLV relation with `a ≥ 1`. No size hypothesis: only bits `0..127` are read. -/
theorem endoExpand_vesta_ne_zero (n : ℕ) :
    FqSponge.endoExpand FqVesta.spec.lam n ≠ 0 := by
  rw [endoExpand_eq_endoAcc]
  intro h
  obtain ⟨h1, h2, h3, h4⟩ := endoAcc_bound n
  have hz : ((((endoAcc n).2 + (endoAcc n).1 * (Pasta.vestaLam : ℤ) : ℤ)
      : ZMod PALLAS_BASE_CARD)) = 0 := by
    have := cast_short_relation_eq_zero (q := PALLAS_BASE_CARD)
      (a₁ := (endoAcc n).1) (b₁ := (endoAcc n).2) (a₂ := 0) (b₂ := 0)
      (by simpa using h)
    simpa using this
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  refine Pasta.vesta_glv_no_short_relation (a := (endoAcc n).2) (b := (endoAcc n).1)
    (Or.inr (by omega)) (by simp [abs_le]; omega) (by simp [abs_le]; omega) ?_
  rw [Pasta.vesta_card]
  exact hz

/-- **Pallas-side injectivity**: the twin at the Pallas spec's eigenvalue. -/
theorem endoExpand_pallas_injOn {m n : ℕ} (hm : m < 2 ^ 128) (hn : n < 2 ^ 128)
    (h : FqSponge.endoExpand FqPallas.spec.lam m = FqSponge.endoExpand FqPallas.spec.lam n) :
    m = n := by
  rw [endoExpand_eq_endoAcc, endoExpand_eq_endoAcc] at h
  by_cases hacc : endoAcc m = endoAcc n
  · exact endoAcc_injOn hm hn hacc
  · exfalso
    obtain ⟨h1m, h2m, h3m, h4m⟩ := endoAcc_bound m
    obtain ⟨h1n, h2n, h3n, h4n⟩ := endoAcc_bound n
    have hz := cast_short_relation_eq_zero (q := PALLAS_SCALAR_CARD) h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    refine Pasta.pallas_glv_no_short_relation (a := (endoAcc m).2 - (endoAcc n).2)
      (b := (endoAcc m).1 - (endoAcc n).1) ?_ (by simp [abs_le]; omega) (by simp [abs_le]; omega)
      ?_
    · by_contra hboth
      push Not at hboth
      exact hacc (Prod.ext (by omega) (by omega))
    · rw [Pasta.pallas_card]
      exact hz

/-- **Pallas-side nonvanishing**. -/
theorem endoExpand_pallas_ne_zero (n : ℕ) :
    FqSponge.endoExpand FqPallas.spec.lam n ≠ 0 := by
  rw [endoExpand_eq_endoAcc]
  intro h
  obtain ⟨h1, h2, h3, h4⟩ := endoAcc_bound n
  have hz : ((((endoAcc n).2 + (endoAcc n).1 * (Pasta.pallasLam : ℤ) : ℤ)
      : ZMod PALLAS_SCALAR_CARD)) = 0 := by
    have := cast_short_relation_eq_zero (q := PALLAS_SCALAR_CARD)
      (a₁ := (endoAcc n).1) (b₁ := (endoAcc n).2) (a₂ := 0) (b₂ := 0)
      (by simpa using h)
    simpa using this
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  refine Pasta.pallas_glv_no_short_relation (a := (endoAcc n).2) (b := (endoAcc n).1)
    (Or.inr (by omega)) (by simp [abs_le]; omega) (by simp [abs_le]; omega) ?_
  rw [Pasta.pallas_card]
  exact hz

end Bulletproof.Forking
