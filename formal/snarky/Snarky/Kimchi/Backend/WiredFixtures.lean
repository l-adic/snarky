import Snarky.Kimchi.Constraint
import Kimchi.Gate.Poseidon
import Kimchi.Columns
import Mathlib.Data.ZMod.Defs

/-!
# Sources for the wired-fragment checks

The source lists decided over a field of 113 elements: for each gate an accepted source with
its public variables, and the variants out of scope; and the index parameters the checks build
their indices at. They are data only. The wired-fragment
checks build their indices and satisfy them; the scope checker's checks run the checker on
them. One module holds them so that neither set of checks copies the other's sources.
-/

namespace Snarky.Kimchi

open Kimchi Snarky

namespace WiredFixture

/-- The carrier: the integers modulo `113`, a field with `16 ∣ 112` and seven cosets of the
sixteenth roots of unity; the sources use only its ring structure. -/
abbrev K := ZMod 113

/-! ## The index parameters -/

/-- The matrix the indices carry where no Poseidon block reads it. -/
def mds : Kimchi.Gate.Poseidon.Mds K :=
  { m00 := 0, m01 := 0, m02 := 0, m10 := 0, m11 := 0, m12 := 0, m20 := 0, m21 := 0, m22 := 0 }

/-- Powers of the generator `3`: one representative per coset of the sixteenth roots. -/
def shifts : Fin permCols → K := fun c => [1, 3, 9, 27, 81, 17, 51].getD c.val 0

/-- A small matrix for the Poseidon block: the rows `1 2 3`, `4 5 6`, `7 8 10`. -/
def poseidonMds : Kimchi.Gate.Poseidon.Mds K :=
  { m00 := 1, m01 := 2, m02 := 3, m10 := 4, m11 := 5, m12 := 6, m20 := 7, m21 := 8, m22 := 10 }

/-! ## A complete addition among `Basic` constraints -/

/-- A complete addition with an affine first abscissa and a scaled second ordinate, its
`inf` flag the merged variable. -/
def addition : AddComplete K :=
  { p1 := ⟨.add (.var 3) (.var 13), .var 4⟩, p2 := ⟨.var 5, .scale 2 (.var 6)⟩,
    p3 := ⟨.var 7, .var 8⟩, inf := .var 2, sameX := .var 9, s := .var 10, infZ := .var 11,
    x21Inv := .var 12 }

/-- A pin, a merge, the addition, a cache hit on the pin's constant, a Boolean on the merged
variable. -/
def source : List (KimchiConstraint K) :=
  [.basic (.equal (.var 0) (.const 5)), .basic (.equal (.var 1) (.var 2)),
    .addComplete addition, .basic (.equal (.var 14) (.const 5)), .basic (.boolean (.var 2))]

/-- The first source's public variables: the pinned variable and one of the merged pair. -/
def publicVars : List Variable := [0, 1]

/-- The addition with a constant in an unwired slot. -/
def constSource : List (KimchiConstraint K) :=
  [.basic (.equal (.var 0) (.const 5)), .basic (.equal (.var 1) (.var 2)),
    .addComplete { addition with sameX := .const 1 }, .basic (.equal (.var 14) (.const 5)),
    .basic (.boolean (.var 2))]

/-- An unwired operand named again by an equality of two variables: a merge, which writes
no cell. -/
def equalSource : List (KimchiConstraint K) :=
  source ++ [.basic (.equal (.var 9) (.var 16))]

/-- An unwired operand named again as a term of the sum. -/
def termSource : List (KimchiConstraint K) :=
  [.basic (.equal (.var 0) (.const 5)), .basic (.equal (.var 1) (.var 2)),
    .addComplete { addition with p1 := ⟨.add (.var 9) (.var 13), .var 4⟩ },
    .basic (.equal (.var 14) (.const 5)), .basic (.boolean (.var 2))]

/-- A source naming the counter's own variable. -/
def highSource : List (KimchiConstraint K) :=
  source ++ [.basic (.boolean (.var 20))]

/-! ## A challenge decomposition -/

/-- A round from the initial accumulators, its eight crumbs fresh, its outputs the variables
`8`, `9`, `10`. -/
def round1 : EndoScalarRound K :=
  { n0 := .const 0, n8 := .var 8, a0 := .const 2, a8 := .var 9, b0 := .const 2, b8 := .var 10,
    xs := #v[.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7] }

/-- One round, its output `n` accumulator public. -/
def endoSource : List (KimchiConstraint K) := [.endoScalar [round1]]

/-- The one-round decomposition's public variable: its output `n` accumulator. -/
def endoPublic : List Variable := [8]

/-- A second round threading the first's outputs into its accumulators, its crumbs fresh, its
outputs `19`, `20`, `21`. -/
def round2 : EndoScalarRound K :=
  { n0 := .var 8, n8 := .var 19, a0 := .var 9, a8 := .var 20, b0 := .var 10, b8 := .var 21,
    xs := #v[.var 11, .var 12, .var 13, .var 14, .var 15, .var 16, .var 17, .var 18] }

/-- Two rounds, the final `n` accumulator public. -/
def chainSource : List (KimchiConstraint K) := [.endoScalar [round1, round2]]

/-- The two-round decomposition's public variable: the final `n` accumulator. -/
def chainPublic : List Variable := [19]

/-- The chain with a crumb of the second round reused by a Boolean. -/
def reusedSource : List (KimchiConstraint K) :=
  chainSource ++ [.basic (.boolean (.var 12))]

/-- The second round with a crumb written as a sum. -/
def summedRound : EndoScalarRound K :=
  { round2 with
    xs := #v[.var 11, .var 12, .var 13, .add (.var 14) (.var 15), .var 15, .var 16, .var 17,
      .var 18] }

/-! ## A scalar multiplication -/

/-- A scale round from the base `(0, 1)` and the accumulator `(2, 3)`, its register pinned
to `0`, its middle accumulators `4` to `11`, its output register `12` and accumulator
`(13, 14)`, its bits `15` to `19` and slopes `20` to `24`. -/
def scale1 : ScaleRound K :=
  { acc0 := ⟨.var 2, .var 3⟩, acc1 := ⟨.var 4, .var 5⟩, acc2 := ⟨.var 6, .var 7⟩,
    acc3 := ⟨.var 8, .var 9⟩, acc4 := ⟨.var 10, .var 11⟩, acc5 := ⟨.var 13, .var 14⟩,
    bit0 := .var 15, bit1 := .var 16, bit2 := .var 17, bit3 := .var 18, bit4 := .var 19,
    slope0 := .var 20, slope1 := .var 21, slope2 := .var 22, slope3 := .var 23,
    slope4 := .var 24, nPrev := .const 0, nNext := .var 12, base := ⟨.var 0, .var 1⟩ }

/-- One round, its output accumulator public. -/
def scaleSource : List (KimchiConstraint K) := [.varBaseMul [scale1]]

/-- The one-round multiplication's public variables: its output accumulator. -/
def scalePublic : List Variable := [13, 14]

/-- A second round threading the first's output accumulator and register into its inputs, its
middle accumulators `25` to `32`, its output register `33` and accumulator `(34, 35)`, its
bits `36` to `40` and slopes `41` to `45`. -/
def scale2 : ScaleRound K :=
  { acc0 := ⟨.var 13, .var 14⟩, acc1 := ⟨.var 25, .var 26⟩, acc2 := ⟨.var 27, .var 28⟩,
    acc3 := ⟨.var 29, .var 30⟩, acc4 := ⟨.var 31, .var 32⟩, acc5 := ⟨.var 34, .var 35⟩,
    bit0 := .var 36, bit1 := .var 37, bit2 := .var 38, bit3 := .var 39, bit4 := .var 40,
    slope0 := .var 41, slope1 := .var 42, slope2 := .var 43, slope3 := .var 44,
    slope4 := .var 45, nPrev := .var 12, nNext := .var 33, base := ⟨.var 0, .var 1⟩ }

/-- Two rounds, the final accumulator public. -/
def scaleChainSource : List (KimchiConstraint K) := [.varBaseMul [scale1, scale2]]

/-- The two-round multiplication's public variables: the final accumulator. -/
def scaleChainPublic : List Variable := [34, 35]

/-- The one round with a slope reused by a Boolean. -/
def reusedScale : List (KimchiConstraint K) :=
  scaleSource ++ [.basic (.boolean (.var 20))]

/-- The one round with a middle accumulator's abscissa written as a sum. -/
def summedScale : ScaleRound K := { scale1 with acc1 := ⟨.add (.var 4) (.var 5), .var 5⟩ }

/-! ## An endomorphism multiplication -/

/-- A first round from the target `(0, 1)` and the accumulator `(2, 3)`, its register pinned
to `0`, its inverse `4`, midpoint `(5, 6)`, slopes `7`, `8` and bits `9` to `12`; its unplaced
output fields name the second round's inputs. -/
def emRound1 : EndoMulRound K :=
  { t := ⟨.var 0, .var 1⟩, p := ⟨.var 2, .var 3⟩, r := ⟨.var 5, .var 6⟩, s := ⟨.var 13, .var 14⟩,
    s1 := .var 7, s3 := .var 8, nAcc := .const 0, nAccNext := .var 15, bit0 := .var 9,
    bit1 := .var 10, bit2 := .var 11, bit3 := .var 12, inv := .var 4 }

/-- A second round from the same target, its accumulator `(13, 14)` and register `15` read as
the first's outputs, its inverse `16`, midpoint `(17, 18)`, slopes `19`, `20` and bits `21` to
`24`. -/
def emRound2 : EndoMulRound K :=
  { t := ⟨.var 0, .var 1⟩, p := ⟨.var 13, .var 14⟩, r := ⟨.var 17, .var 18⟩,
    s := ⟨.var 25, .var 26⟩, s1 := .var 19, s3 := .var 20, nAcc := .var 15, nAccNext := .var 27,
    bit0 := .var 21, bit1 := .var 22, bit2 := .var 23, bit3 := .var 24, inv := .var 16 }

/-- The two rounds at the coefficient `2`, the finals `(25, 26)` and `27`. -/
def emul : EndoMul K :=
  { state := [emRound1, emRound2], s := ⟨.var 25, .var 26⟩, nAcc := .var 27, endo := 2 }

/-- One multiplication, its finals public. -/
def endoMulSource : List (KimchiConstraint K) := [.endoMul emul]

/-- The endomorphism multiplication's public variables: its finals. -/
def endoMulPublic : List Variable := [25, 26, 27]

/-- The multiplication with a slope reused by a Boolean. -/
def reusedEndoMul : List (KimchiConstraint K) :=
  endoMulSource ++ [.basic (.boolean (.var 7))]

/-- The first round with its midpoint's abscissa written as a sum. -/
def summedEndoMul : EndoMul K :=
  { emul with state := [{ emRound1 with r := ⟨.add (.var 5) (.var 6), .var 6⟩ }, emRound2] }

/-! ## A Poseidon block -/

/-- Ten rounds' constants, distinct and nonzero across both windows. -/
def poseidonRc : List (K × K × K) :=
  [(1, 2, 3), (4, 5, 6), (7, 8, 9), (10, 11, 12), (13, 14, 15), (16, 17, 18), (19, 20, 21),
    (22, 23, 24), (25, 26, 27), (28, 29, 30)]

/-- Eleven states, the input `(0, 1, const 0)` then the variables `2` to `31` three per state;
the unwired positions of the first window are `3` to `10`, of the second `18` to `25`. -/
def pblock : PoseidonConstraint K :=
  { mds := ((1, 2, 3), (4, 5, 6), (7, 8, 10)), rc := poseidonRc,
    state := [(.var 0, .var 1, .const 0), (.var 2, .var 3, .var 4), (.var 5, .var 6, .var 7),
      (.var 8, .var 9, .var 10), (.var 11, .var 12, .var 13), (.var 14, .var 15, .var 16),
      (.var 17, .var 18, .var 19), (.var 20, .var 21, .var 22), (.var 23, .var 24, .var 25),
      (.var 26, .var 27, .var 28), (.var 29, .var 30, .var 31)] }

/-- One block, its output state public. -/
def poseidonSource : List (KimchiConstraint K) := [.poseidon pblock]

/-- The Poseidon block's public variables: its output state. -/
def poseidonPublic : List Variable := [29, 30, 31]

/-- The block with an unwired state element reused by a Boolean. -/
def reusedPoseidon : List (KimchiConstraint K) :=
  poseidonSource ++ [.basic (.boolean (.var 5))]

/-- The block with the third state's first element written as a sum. -/
def summedPoseidon : PoseidonConstraint K :=
  { pblock with state := pblock.state.take 2 ++ (.add (.var 5) (.var 6), .var 6, .var 7) ::
      pblock.state.drop 3 }

/-! ## A padding row -/

/-- A pin, then a padding row over the pinned variable, a bare variable, a sum, the pinned
constant, a bare variable, its double and a bare variable, then a Boolean on the row's second
operand. -/
def padSource : List (KimchiConstraint K) :=
  [.basic (.equal (.var 0) (.const 5)),
    .pad #v[.var 0, .var 1, .add (.var 1) (.var 2), .const 5, .var 3, .scale 2 (.var 3), .var 4],
    .basic (.boolean (.var 1))]

/-- The padded source's public variable: the pinned one. -/
def padPublic : List Variable := [0]

/-- The first lowering's source with a padding row naming the addition's unwired `sameX`. -/
def padReuse : List (KimchiConstraint K) :=
  source ++ [.pad #v[.var 9, .var 0, .var 0, .var 0, .var 0, .var 0, .var 0]]

end WiredFixture

end Snarky.Kimchi
