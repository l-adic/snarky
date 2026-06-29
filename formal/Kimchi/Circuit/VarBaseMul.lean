import Kimchi.Circuit.VarBaseMul.Basic
import Kimchi.Circuit.VarBaseMul.Ladder
import Kimchi.Circuit.VarBaseMul.NonDegen
import Kimchi.Circuit.VarBaseMul.Soundness
import Kimchi.Pasta

/-!
# The `VarBaseMul` circuit

The public module for variable-base scalar multiplication: it aggregates the circuit
definitions (`.Basic`), the number-theoretic ladder kernel (`.Ladder`), the group-order
non-degeneracy toolkit (`.NonDegen`), and the abstract soundness (`.Soundness`), and then
instantiates it at the real Pasta curves.

The abstract `varBaseMul_deployed_correct` / `varBaseMul_subwrap_correct` /
`varBaseMul_forbidden_correct` (in `.Soundness`) are proved over any `WeierstrassCurve.Affine`
carrying the short-shape and prime-order `Fact`s, and are `#print axioms`-clean. Here we expose
the two directions the deployed circuit actually uses, each at its concrete curve:

* `varBaseMul_scaleFast1` — `scaleFast1` / Type1 (Vesta): the scalar field is smaller
  than the circuit field, so there is no register range-check; soundness comes from the forbidden
  band (full width) or the sub-wrap regime (below it).
* `varBaseMul_scaleFast2` — `scaleFast2` / Type2 (Pallas): the caller splits the scalar and
  range-checks the high half, so soundness is the field-bound route.

A bare `varBaseMul` is never deployed on its own — only these two — so the field-bound Pallas
correctness is *inlined* into `scaleFast2`. The `Fact`s
are discharged from `Kimchi.Pasta`, the prime-order one through the trusted point count
(`pallas_card` / `vesta_card`). So these corollaries are the only things that depend on a
point-count axiom; the abstract development stays axiom-free.
-/

namespace Kimchi.Circuit.VarBaseMul

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine Kimchi.Shifted Kimchi.Pasta

/-! ## The `scaleFast1` / Type1 direction: soundness via the forbidden band (Vesta)

`scaleFast2` (the Pallas direction, below) range-checks the register, so its soundness is the
field-bound route (inlined into `varBaseMul_scaleFast2`). `scaleFast1` (the Vesta direction;
scalar field < circuit field) range-checks nothing and instead guards with a forbidden-value check.
Its soundness splits by chunk count `m` (`bitsUsed = 5m ≤ FieldSizeInBits = pastaFieldBits`): for
`m ≤ 50` the ladder fits below the order and every row is non-degenerate unconditionally
(`varBaseMul_subwrap_correct`); only the full width `m = 51` is the one-wrap case that needs the
forbidden band (`varBaseMul_forbidden_correct`).

The full-width `m = 51` case excludes the COMPLETE forbidden band, which is *stronger* than mina's
incomplete runtime guard; see `varBaseMul_forbidden_correct` for the faithfulness caveat. -/

/-- **scaleFast1 / Type1 on the real Vesta curve: correct + sound for any chunk count `m ∈ 1..51`.**
    The single hypothesis on the bit count is `hbits : 5 * m ≤ pastaFieldBits`
    (`bitsUsed ≤ FieldSizeInBits`). The forbidden-band exclusion `hnf` is required **only at the
    full width** `5m = pastaFieldBits` — a conditional hypothesis — because every smaller chunk
    count is in the sub-wrap regime and is sound with no guard at all. The proof dispatches:
    `5m ≤ pastaFieldBits - 5` → `varBaseMul_subwrap_correct` (`3·2^(5m) ≤ PALLAS_BASE_CARD` by
    computation); `5m = pastaFieldBits` → `varBaseMul_forbidden_correct`
    (one-wrap, regime bounds + `order ≡ 1 mod 4` discharged from the cardinal). See
    `varBaseMul_forbidden_correct` for the band-vs-deployed-check faithfulness caveat. -/
theorem varBaseMul_scaleFast1
    (m : ℕ) (g : ℕ → Witness VestaBaseField)
    (T : Vesta.curve.toAffine.Point) (s : ℤ) (hTne : T ≠ 0)
    (hholds : ∀ i, i < m → Holds (g i))
    (hTns : Vesta.curve.toAffine.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).x0 = (g i).x5 ∧ (g (i + 1)).y0 = (g i).y5)
    (hP0ns : Vesta.curve.toAffine.Nonsingular (g 0).x0 (g 0).y0)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (hbits : 5 * m ≤ pastaFieldBits)
    (hs : s = gateLadder g (5 * m))
    (hnf : 5 * m = pastaFieldBits → s ∉ forbiddenValues Vesta.curve.toAffine.order) :
    ∃ hfin : Vesta.curve.toAffine.Nonsingular (accX g m) (accY g m),
      Point.some _ _ hfin = s • T ∧ ∀ i, i < m → NonDegen (g i) := by
  rcases Nat.lt_or_ge (5 * m) pastaFieldBits with hlt | hge
  · -- sub-wrap: `5m` below `pastaFieldBits` with `5 ∣ 5m` ⟹ `5m ≤ pastaFieldBits - 5` ⟹ safe.
    refine varBaseMul_subwrap_correct Vesta.curve.toAffine m g T s hTne hholds hTns hTeq hbase
      hthread hP0ns hP0
      (by decide) ?_ hs
    rw [Kimchi.Pasta.vesta_card]
    have hp : (2 : ℕ) ^ (5 * m) ≤ 2 ^ (pastaFieldBits - 5) :=
      Nat.pow_le_pow_right (by norm_num) (by have : pastaFieldBits = 255 := rfl; omega)
    have : (3 : ℕ) * 2 ^ (pastaFieldBits - 5) ≤ PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
    omega
  · -- one-wrap: `5m = pastaFieldBits` exactly.
    have hfull : 5 * m = pastaFieldBits := by omega
    exact varBaseMul_forbidden_correct Vesta.curve.toAffine m g T s hTne hholds hTns hTeq hbase
      hthread hP0ns hP0
      (by decide)
      (by rw [Kimchi.Pasta.vesta_card, hfull]; norm_num [PALLAS_BASE_CARD])
      (by rw [Kimchi.Pasta.vesta_card, hfull]; norm_num [PALLAS_BASE_CARD])
      (by rw [Kimchi.Pasta.vesta_card]; norm_num [PALLAS_BASE_CARD])
      hs (hnf hfull)

/-! ## scaleFast2 / Type2: the parity-split entry point (Pallas direction)

`scaleFast2 base {sDiv2, sOdd}` does not call `varBaseMul` directly. It runs the inner
`varBaseMul base (Type1 sDiv2)`, asserts the high bits of the decomposition zero — forcing
`sDiv2 < 2^(pastaFieldBits-1)` — and applies the parity correction `if sOdd then g else g − base`.
So the inner register is `sDiv2 < 2^(pastaFieldBits-1) < p`, which discharges `hcanonical` via the
signed-ladder/register bridge (`gateLadder_eq_register`): no separate range hypothesis beyond
`sDiv2`'s bound. The field-bound non-degeneracy (the abstract `varBaseMul_deployed_correct`
instantiated at Pallas) is inlined below — a bare `varBaseMul` is never a deployed entry point on
its own. The split itself is modeled by `scalarMul_type2`. -/

/-- **scaleFast2 on the real Pallas curve.** The Type2 entry point: the scalar is split
    `s = 2·sDiv2 + sOdd`, the register `N` holds `sDiv2` (range-checked to
    `gateRegister g (5m) < 2^(pastaFieldBits-1)` — the deployed `sDiv2 < 2^(pastaFieldBits-1)`), the
    `m` gates run the inner `varBaseMul`, and the parity
    correction gives `result = if sOdd then P m else P m − T`. The output is `[n]·T` with
    `(n : F) = unshiftType2 (5m) (N m) sOdd = 2·(N m) + sOdd + 2^(5m)`. Non-degeneracy is *derived*
    from the range-check (`sDiv2 < 2^(pastaFieldBits-1) ≤ p` ⟹ `hcanonical` via
    `gateLadder_eq_register`), feeding the field-bound `varBaseMul_deployed_correct` (instantiated
    at Pallas, inlined) for `NonDegen`; then `scalarMul_type2` supplies the split + correction —
    matching the PureScript `scaleFast2` exactly. -/
theorem varBaseMul_scaleFast2
    (m : ℕ) (hm : 0 < m) (g : ℕ → Witness PallasBaseField)
    (T : Pallas.curve.toAffine.Point) (N : ℕ → PallasBaseField) (hTne : T ≠ 0)
    (hholds : ∀ i, i < m → Holds (g i))
    (hTns : Pallas.curve.toAffine.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).x0 = (g i).x5 ∧ (g (i + 1)).y0 = (g i).y5)
    (hP0ns : Pallas.curve.toAffine.Nonsingular (g 0).x0 (g 0).y0)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (hregIn : ∀ i, i < m → N i = (g i).n)
    (hregOut : ∀ i, i < m → N (i + 1) = (g i).nPrime)
    (hN0 : N 0 = 0)
    (hbits : 5 * m ≤ pastaFieldBits)
    (hsDiv2 : gateRegister g (5 * m) < 2 ^ (pastaFieldBits - 1))
    (hPmns : Pallas.curve.toAffine.Nonsingular (g (m - 1)).x5 (g (m - 1)).y5)
    (sOdd : PallasBaseField) (result : Pallas.curve.toAffine.Point)
    (hcorr : (sOdd = 1 ∧ result = Point.some _ _ hPmns)
        ∨ (sOdd = 0 ∧ result = Point.some _ _ hPmns - T)) :
    ∃ n : ℤ, result = n • T ∧ (n : PallasBaseField) = unshiftType2 (5 * m) (N m) sOdd := by
  sorry

end Kimchi.Circuit.VarBaseMul
