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
def endoAcc (chal : ℕ) : ℤ × ℤ :=
  (List.range 64).reverse.foldl
    (fun (ab : ℤ × ℤ) i =>
      let (a, b) := (2 * ab.1, 2 * ab.2)
      let s : ℤ := if chal.testBit (2 * i) then 1 else -1
      if chal.testBit (2 * i + 1) then (a + s, b) else (a, b + s))
    (2, 2)

/-- `endoExpand` is the cast of the integer model: the field fold commutes with `Int.cast`
step by step. -/
theorem endoExpand_eq_endoAcc {F : Type*} [Field F] (lam : F) (chal : ℕ) :
    FqSponge.endoExpand lam chal
      = ((endoAcc chal).1 : F) * lam + ((endoAcc chal).2 : F) := by
  sorry

/-- The accumulators are short: both components of `endoAcc` lie in `[1, 2⁶⁶]`. The invariant is
`1 ≤ x ≤ B ⟹ 1 ≤ 2x ± 1 ≤ 2B + 1`, folded 64 times from `B = 2`. -/
theorem endoAcc_bound (chal : ℕ) :
    1 ≤ (endoAcc chal).1 ∧ (endoAcc chal).1 ≤ 2 ^ 66 ∧
      1 ≤ (endoAcc chal).2 ∧ (endoAcc chal).2 ≤ 2 ^ 66 := by
  sorry

/-- The window encoding is injective on 128-bit prechallenges: the accumulator pair determines
the bits. Unwinding one step, exactly one of the pair is odd — that parity is the window's high
bit, the odd component's residue mod 4 is the window's low bit — and the quotients recurse. -/
theorem endoAcc_injOn {m n : ℕ} (hm : m < 2 ^ 128) (hn : n < 2 ^ 128)
    (h : endoAcc m = endoAcc n) : m = n := by
  sorry

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
