import Kimchi.Checker.Row

/-! # The kimchi `VarBaseMul` (variable-base scalar multiplication) gate (checker model).

Transcribed from proof-systems `.../polynomials/varbasemul.rs` (21 constraints). The gate
processes a 5-bit chunk of the scalar via incomplete EC addition, spanning the current row
(`VarBaseMul`) and the next row (`Zero`). No coefficients (witness-only).

Column layout — current row: `0,1 = xT,yT` (base), `2,3 = x0,y0` (acc in), `4,5 = n,n'`
(scalar acc), `7..14 = x1,y1,x2,y2,x3,y3,x4,y4` (acc steps). Next row:
`0,1 = x5,y5`, `2..6 = b0..b4` (bits), `7..11 = s0..s4` (slopes).

This is the **checker-facing**, row-based constraint model consumed by `Kimchi.Circuit`;
the soundness proof of variable-base scalar multiplication lives separately at
`Kimchi.Gate.VarBaseMul`. -/

namespace Kimchi.Checker.VarBaseMul

open Kimchi.Gate (Row)

variable {F : Type*}

/-- One incomplete-addition step: bit `b`, slope `s`, base `(xb,yb)`, input `(xin,yin)`,
    output `(xout,yout)`. The four constraints: booleanity, the slope identity, and the
    `(x,y)` output identities (with `t = 2·xin − s² + xb`, `u = 2·yin − t·s`). -/
def stepHolds [CommRing F] (xb yb xin yin xout yout b s : F) : Prop :=
  b * (b - 1) = 0
  ∧ (xin - xb) * s - (yin - (2 * b - 1) * yb) = 0
  ∧ (2 * yin - (2 * xin - s ^ 2 + xb) * s) ^ 2
      - (2 * xin - s ^ 2 + xb) ^ 2 * (xout - xb + s ^ 2) = 0
  ∧ (yout + yin) * (2 * xin - s ^ 2 + xb)
      - (xin - xout) * (2 * yin - (2 * xin - s ^ 2 + xb) * s) = 0

def stepOk [CommRing F] [DecidableEq F] (xb yb xin yin xout yout b s : F) : Bool :=
  (b * (b - 1) == 0)
  && ((xin - xb) * s - (yin - (2 * b - 1) * yb) == 0)
  && ((2 * yin - (2 * xin - s ^ 2 + xb) * s) ^ 2
        - (2 * xin - s ^ 2 + xb) ^ 2 * (xout - xb + s ^ 2) == 0)
  && ((yout + yin) * (2 * xin - s ^ 2 + xb)
        - (xin - xout) * (2 * yin - (2 * xin - s ^ 2 + xb) * s) == 0)

theorem stepOk_iff [CommRing F] [DecidableEq F] (xb yb xin yin xout yout b s : F) :
    stepOk xb yb xin yin xout yout b s = true ↔ stepHolds xb yb xin yin xout yout b s := by
  simp only [stepOk, stepHolds, Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- The 21 constraints: one binary-decomposition of the 5 bits into `n' = …`, then four
    constraints per bit (5 incomplete-addition steps chaining the accumulator). -/
def holds [CommRing F] (curr next : Row F) : Prop :=
  let w := fun i => curr.getD i 0
  let wn := fun i => next.getD i 0
  -- n' = b4 + 2(b3 + 2(b2 + 2(b1 + 2(b0 + 2·n))))
  (w 5 - (wn 6 + 2 * (wn 5 + 2 * (wn 4 + 2 * (wn 3 + 2 * (wn 2 + 2 * w 4)))))) = 0
  ∧ stepHolds (w 0) (w 1) (w 2) (w 3) (w 7) (w 8) (wn 2) (wn 7)
  ∧ stepHolds (w 0) (w 1) (w 7) (w 8) (w 9) (w 10) (wn 3) (wn 8)
  ∧ stepHolds (w 0) (w 1) (w 9) (w 10) (w 11) (w 12) (wn 4) (wn 9)
  ∧ stepHolds (w 0) (w 1) (w 11) (w 12) (w 13) (w 14) (wn 5) (wn 10)
  ∧ stepHolds (w 0) (w 1) (w 13) (w 14) (wn 0) (wn 1) (wn 6) (wn 11)

def ok [CommRing F] [DecidableEq F] (curr next : Row F) : Bool :=
  let w := fun i => curr.getD i 0
  let wn := fun i => next.getD i 0
  (w 5 - (wn 6 + 2 * (wn 5 + 2 * (wn 4 + 2 * (wn 3 + 2 * (wn 2 + 2 * w 4))))) == 0)
  && stepOk (w 0) (w 1) (w 2) (w 3) (w 7) (w 8) (wn 2) (wn 7)
  && stepOk (w 0) (w 1) (w 7) (w 8) (w 9) (w 10) (wn 3) (wn 8)
  && stepOk (w 0) (w 1) (w 9) (w 10) (w 11) (w 12) (wn 4) (wn 9)
  && stepOk (w 0) (w 1) (w 11) (w 12) (w 13) (w 14) (wn 5) (wn 10)
  && stepOk (w 0) (w 1) (w 13) (w 14) (wn 0) (wn 1) (wn 6) (wn 11)

theorem ok_iff [CommRing F] [DecidableEq F] (curr next : Row F) :
    ok curr next = true ↔ holds curr next := by
  simp only [ok, holds, stepOk_iff, Bool.and_eq_true, beq_iff_eq, and_assoc]

end Kimchi.Checker.VarBaseMul
