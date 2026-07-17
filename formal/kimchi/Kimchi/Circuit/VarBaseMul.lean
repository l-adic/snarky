import Kimchi.Circuit.VarBaseMul.Internal
import Pasta

/-!
# The `VarBaseMul` circuit

Variable-base scalar multiplication, instantiated at the real Pasta curves. The supporting
development — the accumulator and register recurrence folds, the number-theoretic ladder kernel,
the group-order non-degeneracy toolkit, and the abstract soundness — lives in
`Kimchi.Circuit.VarBaseMul.Internal`.

The generic soundness theorems `varBaseMul_subwrap_correct` and `varBaseMul_forbidden_correct` are
proved over any `WeierstrassCurve.Affine` carrying the short-shape and prime-order `Fact`s, and are
`#print axioms`-clean. This module exposes the two directions the deployed circuit actually uses,
each at its concrete curve:

* `varBaseMul_scaleFast1` — `scaleFast1` / Type1 (Vesta): the scalar field is smaller
  than the circuit field, so there is no register range-check; soundness comes from the forbidden
  band (full width) or the sub-wrap regime (below it).
* `varBaseMul_scaleFast2` — `scaleFast2` / Type2 (Pallas): the caller splits the scalar and
  range-checks the high half, so soundness is the field-bound route.

A bare `varBaseMul` is never deployed on its own — only these two — so the field-bound Pallas
correctness is *inlined* into `scaleFast2`. The `Fact`s
are discharged from `Pasta`, the prime-order one through the trusted point count
(`pallas_card` / `vesta_card`). So these corollaries are the only things that depend on a
point-count axiom; the abstract development stays axiom-free.
-/

namespace Kimchi.Circuit.VarBaseMul

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine Pasta.Shifted Pasta

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
    (m : ℕ) (g : ℕ → Witness Fq)
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
  have hodd : Vesta.curve.toAffine.order ≠ 2 := by rw [Pasta.vesta_card]; decide
  rcases Nat.lt_or_ge (5 * m) pastaFieldBits with hlt | hge
  · -- sub-wrap: `5m` below `pastaFieldBits` with `5 ∣ 5m` ⟹ `5m ≤ pastaFieldBits - 5` ⟹ safe.
    refine varBaseMul_subwrap_correct Vesta.curve.toAffine m g T s hTne hholds hTns hTeq hbase
      hthread hP0ns hP0
      (by decide) hodd ?_ hs
    rw [Pasta.vesta_card]
    have hp : (2 : ℕ) ^ (5 * m) ≤ 2 ^ (pastaFieldBits - 5) :=
      Nat.pow_le_pow_right (by norm_num) (by have : pastaFieldBits = 255 := rfl; omega)
    have : (3 : ℕ) * 2 ^ (pastaFieldBits - 5) ≤ PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
    omega
  · -- one-wrap: `5m = pastaFieldBits` exactly.
    have hfull : 5 * m = pastaFieldBits := by omega
    exact varBaseMul_forbidden_correct Vesta.curve.toAffine m g T s hTne hholds hTns hTeq hbase
      hthread hP0ns hP0
      (by decide) hodd
      (by rw [Pasta.vesta_card, hfull]; norm_num [PALLAS_BASE_CARD])
      (by rw [Pasta.vesta_card, hfull]; norm_num [PALLAS_BASE_CARD])
      (by rw [Pasta.vesta_card]; norm_num [PALLAS_BASE_CARD])
      hs (hnf hfull)

/-! ## scaleFast2 / Type2: the parity-split entry point (Pallas direction)

`scaleFast2 base {sDiv2, sOdd}` does not call `varBaseMul` directly. It runs the inner
`varBaseMul base (Type1 sDiv2)`, asserts the high bits of the decomposition zero — forcing
`sDiv2 < 2^(pastaFieldBits-1)` — and applies the parity correction `if sOdd then g else g − base`.
So the inner register is `sDiv2 < 2^(pastaFieldBits-1) < p`, which discharges `hcanonical` via the
signed-ladder/register bridge (`gateLadder_eq_register`): no separate range hypothesis beyond
`sDiv2`'s bound. The field-bound non-degeneracy at Pallas is inlined below — a bare `varBaseMul` is
never a deployed entry point on its own. The split itself is modeled by `scalarMul_type2`. -/

/-- **scaleFast2 on the real Pallas curve.** The Type2 entry point: the scalar is split
    `s = 2·sDiv2 + sOdd`, the register `N` holds `sDiv2` (range-checked to
    `gateRegister g (5m) < 2^(pastaFieldBits-1)` — the deployed `sDiv2 < 2^(pastaFieldBits-1)`), and
    the `m` gates run the inner `varBaseMul`. The prover supplies only the gate `Holds` per row +
    base + threading + the initial accumulator + the parity bit `sOdd ∈ {0,1}`; the final
    accumulator `Point.some _ _ hfin` (its nonsingularity *derived*, like `endoMul`) and the scalar
    `n` are *exposed in the conclusion*. The parity correction is stated on that accumulator:
    `if sOdd then P m else P m − T = [n]·T`, with `(n : F) = unshiftType2 (5m) (N m) sOdd =
    2·(N m) + sOdd + 2^(5m)`. Non-degeneracy comes from the range-check
    (`sDiv2 < 2^(pastaFieldBits-1) ≤ p` ⟹ `hcanonical` via `gateLadder_eq_register`), feeding
    `gateStep_chain` for the derived `GateStep`s; `scalarMul_type2` then supplies the split +
    correction — matching the PureScript `scaleFast2` exactly. -/
theorem varBaseMul_scaleFast2
    (m : ℕ) (hm : 0 < m) (g : ℕ → Witness Fp)
    (T : Pallas.curve.toAffine.Point) (N : ℕ → Fp) (hTne : T ≠ 0)
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
    (sOdd : Fp) (hsOdd : sOdd = 0 ∨ sOdd = 1) :
    ∃ (hfin : Pallas.curve.toAffine.Nonsingular (accX g m) (accY g m)) (n : ℤ),
      (n : Fp) = unshiftType2 (5 * m) (N m) sOdd
        ∧ ((sOdd = 1 ∧ Point.some _ _ hfin = n • T)
            ∨ (sOdd = 0 ∧ Point.some _ _ hfin - T = n • T)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have h2 : (2 : Fp) ≠ 0 := by decide
  have hodd : Pallas.curve.toAffine.order ≠ 2 := by rw [Pasta.pallas_card]; decide
  have hq : Pallas.curve.toAffine.order = PALLAS_SCALAR_CARD := Pasta.pallas_card
  have hcanon : gateLadder g (5 * (k + 1)) < 2 * (PALLAS_BASE_CARD : ℤ) + 2 ^ (5 * (k + 1)) := by
    rw [gateLadder_eq_register]
    have hp : (2 ^ (pastaFieldBits - 1) : ℤ) ≤ PALLAS_BASE_CARD := by
      exact_mod_cast two_pow_le_pallas_base
    linarith
  have hpow : (2 : ℕ) ^ (5 * (k + 1) - 1) ≤ 2 ^ (pastaFieldBits - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hND := Ladder.ladder_x_nondegen Pallas.curve.toAffine.order PALLAS_BASE_CARD (5 * (k + 1))
    (by rw [hq]; exact lt_of_le_of_lt hpow (by norm_num [PALLAS_SCALAR_CARD]))
    ((Fact.out : Nat.Prime Pallas.curve.toAffine.order).odd_of_ne_two hodd)
    (by rw [hq]; norm_num [PALLAS_SCALAR_CARD])
    (by rw [hq]
        have hc : PALLAS_BASE_CARD + 2 ^ (pastaFieldBits - 1) + 2 ≤ 2 * PALLAS_SCALAR_CARD := by
          norm_num [PALLAS_BASE_CARD, PALLAS_SCALAR_CARD]
        omega)
    (gateLadder g) (gateBitSign g) (gateLadder_zero g) (fun j _ => gateBitSign_eq g j)
    (fun j _ => gateLadder_succ g j) hcanon
  obtain ⟨gs, P, hTP, hin, hout, hP0P⟩ := gateStep_chain Pallas.curve.toAffine (k + 1) g T hTne
    hholds hTns hTeq hbase hthread hP0ns hP0 h2 hodd hND
  have hfin : Pallas.curve.toAffine.Nonsingular (accX g (k + 1)) (accY g (k + 1)) :=
    (gs k (by omega)).a5
  have hPm : P (k + 1) = Point.some _ _ hfin := hout k (by omega)
  obtain ⟨n, hnf, hcase⟩ := scalarMul_type2 Pallas.curve.toAffine ⟨rfl, rfl, rfl⟩ (k + 1) g gs T N P
    hTP hin hout hregIn hregOut hP0P hN0 sOdd hsOdd
  refine ⟨hfin, n, hnf, ?_⟩
  rcases hcase with ⟨ho, hr⟩ | ⟨ho, hr⟩
  · exact Or.inl ⟨ho, by rw [← hPm]; exact hr⟩
  · exact Or.inr ⟨ho, by rw [← hPm]; exact hr⟩

end Kimchi.Circuit.VarBaseMul
