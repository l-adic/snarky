import Kimchi.Gate.VarBaseMul

/-!
# The kimchi `EndoMul` gate

The endomorphism-optimized variable-base scalar-multiplication gate, transcribed
from proof-systems `kimchi/src/circuits/polynomials/endosclmul.rs` (the
`EC_endoscale` point constraint) and the PureScript `Snarky.Circuit.Kimchi.EndoMul`.

It is VarBaseMul's `(P + Q) + P` double-and-add, but each 2-bit window selects `Q`
from `{T, −T, φ(T), −φ(T)}` — the GLV optimization — using the curve endomorphism

      φ(x, y) = (endo · x, y)      (endo a primitive cube root of unity, φ(T) = [λ]T)

so that `[k]T = [k₁]T + [k₂]·φ(T)` with `k₁, k₂` half-width. Each row processes 4
bits = two windows `P → R → S`:

* `Q₁ = (xq₁, yq₁)`, `xq₁ = (1 + (endo−1)·b₁)·xT` (= `xT` or `endo·xT`),
  `yq₁ = (2·b₂ − 1)·yT` (sign) — so `b₁` picks `T` vs `φ(T)`, `b₂` the sign.
* `Q₂ = (xq₂, yq₂)` likewise from `(b₃, b₄)`.

The register threads `n' = 16·n + 8·b₁ + 4·b₂ + 2·b₃ + b₄`, and the accumulator is
initialized to `2·(T + φ(T))` to dodge the point at infinity.

The EC core (`(P + Q) + P` per window) reuses `Kimchi.Gate.VarBaseMul`'s
`secant_add` (general affine addition) and `signed_target` (the `±` selection); the
new ingredients are the endomorphism base-choice and the GLV `[k₁]T + [k₂]φ(T)`
accumulation.

## Main results

(in progress) — the constraint model `Witness` / `Holds` and the booleanity helper.
-/

namespace Kimchi.Gate.EndoMul

open WeierstrassCurve.Affine

variable {F : Type*} [Field F]

/-- One `EndoMul` row: base `T`, input accumulator `P`, the scalar register
    `n → n'`, the four bits, the two window slopes `s1`/`s3`, and the intermediate
    `R` and output `S` accumulator points. -/
structure Witness (F : Type*) where
  xT : F
  yT : F
  xP : F
  yP : F
  n : F
  nPrime : F
  b1 : F
  b2 : F
  b3 : F
  b4 : F
  s1 : F
  xR : F
  yR : F
  s3 : F
  xS : F
  yS : F

/-- The 11 gate constraints: two `(P+Q)+P` blocks (3 each, with `Q` the endo-and-
    sign-selected target), 4 booleanity checks, and the scalar-register decomposition.
    `endo` is the base-field endomorphism coefficient. -/
def Holds (endo : F) (w : Witness F) : Prop :=
  let xq1 := (1 + (endo - 1) * w.b1) * w.xT
  let yq1 := (2 * w.b2 - 1) * w.yT
  let xq2 := (1 + (endo - 1) * w.b3) * w.xT
  let yq2 := (2 * w.b4 - 1) * w.yT
  -- first window `P → R`, slope `s1`
  ((xq1 - w.xP) * w.s1 = yq1 - w.yP)
    ∧ ((2 * w.xP - w.s1 ^ 2 + xq1) * ((w.xP - w.xR) * w.s1 + w.yR + w.yP)
        = (w.xP - w.xR) * (2 * w.yP))
    ∧ ((w.yR + w.yP) ^ 2 = (w.xP - w.xR) ^ 2 * (w.s1 ^ 2 - xq1 + w.xR))
    -- second window `R → S`, slope `s3`
    ∧ ((xq2 - w.xR) * w.s3 = yq2 - w.yR)
    ∧ ((2 * w.xR - w.s3 ^ 2 + xq2) * ((w.xR - w.xS) * w.s3 + w.yS + w.yR)
        = (w.xR - w.xS) * (2 * w.yR))
    ∧ ((w.yS + w.yR) ^ 2 = (w.xR - w.xS) ^ 2 * (w.s3 ^ 2 - xq2 + w.xS))
    -- booleanity of the four bits
    ∧ (w.b1 * (w.b1 - 1) = 0)
    ∧ (w.b2 * (w.b2 - 1) = 0)
    ∧ (w.b3 * (w.b3 - 1) = 0)
    ∧ (w.b4 * (w.b4 - 1) = 0)
    -- scalar register
    ∧ (w.nPrime = 16 * w.n + 8 * w.b1 + 4 * w.b2 + 2 * w.b3 + w.b4)

/-- Booleanity: the constraint `b·(b−1) = 0` forces `b ∈ {0,1}` (field = domain). -/
theorem bool_of_mul {b : F} (h : b * (b - 1) = 0) : b = 0 ∨ b = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

end Kimchi.Gate.EndoMul
