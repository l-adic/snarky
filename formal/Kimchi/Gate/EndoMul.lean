import Kimchi.Gate.Generic

/-! # The kimchi `EndoMul` (endomorphism-accelerated scalar mul) gate.

Transcribed from proof-systems `.../polynomials/endosclmul.rs` (11 constraints; current +
next row; no coefficients). Two endo-scaled incomplete additions per row, processing 4
scalar bits, plus the scalar accumulation `n' = 16n + 8b1 + 4b2 + 2b3 + b4`.

Column layout — current row: `0,1 = xT,yT`, `4,5 = xP,yP` (acc in), `6 = n`,
`7,8 = xR,yR` (mid point), `9 = s1`, `10 = s3` (slopes), `11..14 = b1..b4` (bits).
Next row: `4,5 = xS,yS` (acc out), `6 = n'`.

The endomorphism scales the base x by `endo` (a base-field cube root of unity); the bit `b`
selects `φ` via `xq = (1 + (endo−1)·b)·xT`. `endo` here is the Pallas `endoBase` constant
(the dumped EndoMul circuits run over `Fp`, i.e. the Pallas base field). -/

namespace Kimchi.Gate.EndoMul

variable {F : Type*}

/-- The base-field endomorphism coefficient `endoBase` for the Pallas curve (`= Fp`),
    taken from the PureScript backend (`PastaCurve.js` `pallasEndoBase`). -/
def endo [CommRing F] : F :=
  20444556541222657078399132219657928148671392403212669005631716460534733845831

def holds [CommRing F] (curr next : Row F) : Prop :=
  let w := fun i => curr.getD i 0
  let wn := fun i => next.getD i 0
  let xq1 := (1 + (endo - 1) * w 11) * w 0
  let yq1 := (2 * w 12 - 1) * w 1
  let xq2 := (1 + (endo - 1) * w 13) * w 0
  let yq2 := (2 * w 14 - 1) * w 1
  w 11 * (w 11 - 1) = 0
  ∧ w 12 * (w 12 - 1) = 0
  ∧ w 13 * (w 13 - 1) = 0
  ∧ w 14 * (w 14 - 1) = 0
  -- first endo-addition (slope s1, mid point R)
  ∧ (xq1 - w 4) * w 9 - (yq1 - w 5) = 0
  ∧ (2 * w 4 - w 9 ^ 2 + xq1) * ((w 4 - w 7) * w 9 + w 8 + w 5) - (w 4 - w 7) * (2 * w 5) = 0
  ∧ (w 8 + w 5) ^ 2 - (w 4 - w 7) ^ 2 * (w 9 ^ 2 - xq1 + w 7) = 0
  -- second endo-addition (slope s3, output point S in next row)
  ∧ (xq2 - w 7) * w 10 - (yq2 - w 8) = 0
  ∧ (2 * w 7 - w 10 ^ 2 + xq2) * ((w 7 - wn 4) * w 10 + wn 5 + w 8) - (w 7 - wn 4) * (2 * w 8) = 0
  ∧ (wn 5 + w 8) ^ 2 - (w 7 - wn 4) ^ 2 * (w 10 ^ 2 - xq2 + wn 4) = 0
  -- scalar accumulation
  ∧ 16 * w 6 + 8 * w 11 + 4 * w 12 + 2 * w 13 + w 14 - wn 6 = 0

def ok [CommRing F] [DecidableEq F] (curr next : Row F) : Bool :=
  let w := fun i => curr.getD i 0
  let wn := fun i => next.getD i 0
  let xq1 := (1 + (endo - 1) * w 11) * w 0
  let yq1 := (2 * w 12 - 1) * w 1
  let xq2 := (1 + (endo - 1) * w 13) * w 0
  let yq2 := (2 * w 14 - 1) * w 1
  (w 11 * (w 11 - 1) == 0)
  && (w 12 * (w 12 - 1) == 0)
  && (w 13 * (w 13 - 1) == 0)
  && (w 14 * (w 14 - 1) == 0)
  && ((xq1 - w 4) * w 9 - (yq1 - w 5) == 0)
  && ((2 * w 4 - w 9 ^ 2 + xq1) * ((w 4 - w 7) * w 9 + w 8 + w 5) - (w 4 - w 7) * (2 * w 5) == 0)
  && ((w 8 + w 5) ^ 2 - (w 4 - w 7) ^ 2 * (w 9 ^ 2 - xq1 + w 7) == 0)
  && ((xq2 - w 7) * w 10 - (yq2 - w 8) == 0)
  && ((2 * w 7 - w 10 ^ 2 + xq2) * ((w 7 - wn 4) * w 10 + wn 5 + w 8)
        - (w 7 - wn 4) * (2 * w 8) == 0)
  && ((wn 5 + w 8) ^ 2 - (w 7 - wn 4) ^ 2 * (w 10 ^ 2 - xq2 + wn 4) == 0)
  && (16 * w 6 + 8 * w 11 + 4 * w 12 + 2 * w 13 + w 14 - wn 6 == 0)

theorem ok_iff [CommRing F] [DecidableEq F] (curr next : Row F) :
    ok curr next = true ↔ holds curr next := by
  simp only [ok, holds, Bool.and_eq_true, beq_iff_eq, and_assoc]

end Kimchi.Gate.EndoMul
