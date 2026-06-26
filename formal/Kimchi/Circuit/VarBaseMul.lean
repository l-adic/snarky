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
instantiates the soundness at the real Pasta curve.

`varBaseMul_deployed_correct` is proved abstractly over any `WeierstrassCurve.Affine` carrying
the short-shape and prime-order `Fact`s, and is `#print axioms`-clean. Here we fix the curve to
each concrete Pasta curve in turn — `varBaseMul_pallas_correct` and `varBaseMul_vesta_correct`,
symmetric across the 2-cycle. The two `Fact`s are discharged from `Kimchi.Pasta`, the prime-order
one through the trusted point count (`pallas_card` / `vesta_card` respectively). So these
corollaries are the only things that depend on a point-count axiom; the abstract development
stays axiom-free.
-/

namespace Kimchi.Circuit.VarBaseMul

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine

/-- **The deployed VarBaseMul circuit is correct on the real Pallas curve.**
    `varBaseMul_deployed_correct` at `Pallas.curve.toAffine`, with `baseFieldOrder` fixed to the
    actual base-field cardinality `PALLAS_BASE_CARD` (the curve is over `ZMod PALLAS_BASE_CARD`).

    The only remaining hypotheses are the genuine ones: `hbits : 5 * m ≤ 255` — the circuit's
    `bitsUsed ≤ FieldSizeInBits` constraint (the Pasta fields are 255-bit) — and `hcanonical`. The
    regime facts `3 < order`, `2^(5m-1) < order`, and the 2-cycle size relation
    `p + 2^(5m-1) + 2 ≤ 2q` are *discharged* here from `hbits` and the known Pasta cardinals
    (`order = PALLAS_SCALAR_CARD` via `pallas_card`), not assumed.

    `hcanonical : s < 2·PALLAS_BASE_CARD + 2^(5m)` is the **range / canonical-form** condition,
    equivalent to "the scalar register `(s − 2^(5m) − 1)/2 < PALLAS_BASE_CARD`". It is a genuine
    soundness precondition, NOT implied by the scalar living in a field: the gate's register is the
    integer the `5m` witness bits spell out, ranging over `[0, 2^(5m))`, while only its residue
    mod `p` is a base-field element. A non-canonical encoding (register in `[p, 2^(5m))`, same field
    value) yields a larger ladder top whose intermediate accumulators can hit `±T`. `hcanonical`
    rules those out — it is the bit-decomposition range-check the circuit must enforce. -/
theorem varBaseMul_pallas_correct
    (m : ℕ) (g : ℕ → Witness PallasBaseField)
    (T : Pallas.curve.toAffine.Point) (P : ℕ → Pallas.curve.toAffine.Point) (s : ℤ)
    (hTne : T ≠ 0)
    (hd : ∀ i, i < m → GateData Pallas.curve.toAffine (g i))
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (hd i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (hd i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (hd i hi).a5)
    (hP0 : P 0 = (2 : ℤ) • T)
    (hbits : 5 * m ≤ 255)
    (hs : s = gateLadder g (5 * m))
    (hcanonical : s < 2 * (PALLAS_BASE_CARD : ℤ) + 2 ^ (5 * m)) :
    P m = s • T ∧ ∀ i, i < m → NonDegen (g i) := by
  have hq : Pallas.curve.toAffine.order = PALLAS_SCALAR_CARD := Kimchi.Pasta.pallas_card
  have hpow : (2 : ℕ) ^ (5 * m - 1) ≤ 2 ^ 254 := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine varBaseMul_deployed_correct Pallas.curve.toAffine m g PALLAS_BASE_CARD T P s
    hTne hd hT hin hout hP0 (by decide) ?_ ?_ ?_ hs hcanonical
  · rw [hq]; norm_num [PALLAS_SCALAR_CARD]
  · rw [hq]; exact lt_of_le_of_lt hpow (by norm_num [PALLAS_SCALAR_CARD])
  · rw [hq]
    have hc : PALLAS_BASE_CARD + 2 ^ 254 + 2 ≤ 2 * PALLAS_SCALAR_CARD := by
      norm_num [PALLAS_BASE_CARD, PALLAS_SCALAR_CARD]
    omega

/-- **The deployed VarBaseMul circuit is correct on the real Vesta curve.** The 2-cycle mirror of
    `varBaseMul_pallas_correct`, at `Vesta.curve.toAffine` (over `ZMod PALLAS_SCALAR_CARD`), with
    `baseFieldOrder` fixed to `PALLAS_SCALAR_CARD` and `order = PALLAS_BASE_CARD` (`vesta_card`).
    The regime facts are discharged from `hbits` and the Pasta cardinals; only the bit-width bound
    and `hcanonical` (the range / canonical-form condition `register < PALLAS_SCALAR_CARD`, as in
    `varBaseMul_pallas_correct`) remain. -/
theorem varBaseMul_vesta_correct
    (m : ℕ) (g : ℕ → Witness VestaBaseField)
    (T : Vesta.curve.toAffine.Point) (P : ℕ → Vesta.curve.toAffine.Point) (s : ℤ)
    (hTne : T ≠ 0)
    (hd : ∀ i, i < m → GateData Vesta.curve.toAffine (g i))
    (hT : ∀ i (hi : i < m), T = Point.some _ _ (hd i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some _ _ (hd i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (hd i hi).a5)
    (hP0 : P 0 = (2 : ℤ) • T)
    (hbits : 5 * m ≤ 255)
    (hs : s = gateLadder g (5 * m))
    (hcanonical : s < 2 * (PALLAS_SCALAR_CARD : ℤ) + 2 ^ (5 * m)) :
    P m = s • T ∧ ∀ i, i < m → NonDegen (g i) := by
  have hq : Vesta.curve.toAffine.order = PALLAS_BASE_CARD := Kimchi.Pasta.vesta_card
  have hpow : (2 : ℕ) ^ (5 * m - 1) ≤ 2 ^ 254 := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine varBaseMul_deployed_correct Vesta.curve.toAffine m g PALLAS_SCALAR_CARD T P s
    hTne hd hT hin hout hP0 (by decide) ?_ ?_ ?_ hs hcanonical
  · rw [hq]; norm_num [PALLAS_BASE_CARD]
  · rw [hq]; exact lt_of_le_of_lt hpow (by norm_num [PALLAS_BASE_CARD])
  · rw [hq]
    have hc : PALLAS_SCALAR_CARD + 2 ^ 254 + 2 ≤ 2 * PALLAS_BASE_CARD := by
      norm_num [PALLAS_BASE_CARD, PALLAS_SCALAR_CARD]
    omega

end Kimchi.Circuit.VarBaseMul
