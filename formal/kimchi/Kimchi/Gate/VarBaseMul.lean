import Pasta.Basic
import Kimchi.Gate.AddComplete

/-!
# The kimchi `VarBaseMul` gate

The variable-base scalar-multiplication gate, transcribed from proof-systems
`kimchi/src/circuits/polynomials/varbasemul.rs`.

The gate processes 5 bits of a double-and-add scalar multiplication across two rows, the gate
row `i` and the next row `i+1`. Per bit `b` it computes

      Output = (Input + (2b − 1)·Target) + Input

without the intermediate y-coordinate. Writing `Input = (xi,yi)`, `Target = (xb,yb)`:

    s1 := (yi − (2b−1)·yb) / (xi − xb)
    rx := s1² − xi − xb                     -- x of the intermediate Input + (2b−1)·Target
    t  := xi − rx   (= 2xi − s1² + xb)
    u  := 2yi − t·s1
    s2 := u / t                             -- slope of the second addition
    xo := xb + s2² − s1²
    yo := (xi − xo)·s2 − yi

Cleared of divisions, each bit contributes 4 constraints (boolean, s1, xo, yo); one more ties
the running scalar `n` to `n'`: 5·4 + 1 = 21 constraints.

Witness layout (cols 0–14):

    row i  : xT yT x0 y0  n  n'  _  x1 y1 x2 y2 x3 y3 x4 y4
    row i+1: x5 y5 b0 b1 b2 b3 b4 s0 s1 s2 s3 s4

The accumulator runs (x0,y0) → … → (x5,y5) against the fixed target (xT,yT); s0…s4 are the
per-bit `s1` slopes and b0…b4 the bits.

This file holds the constraint model (`Witness`, `Holds`, the checker `ok`) and the witness
generator `build`. Soundness (`Kimchi.Gate.VarBaseMul.sound`: a satisfying gate computes
`P₅ = 32·P₀ + c·T` for an integer `c`), completeness and the multi-row chain live in
`Kimchi.Gate.Semantics.VarBaseMul`.
-/

namespace Kimchi.Gate.VarBaseMul

/-- The `VarBaseMul` witness cells across the gate row and the next row. -/
structure Witness (F : Type*) where
  /-- The x-coordinate of the fixed target `T` (gate row, col 0). -/
  xT : F
  /-- The y-coordinate of the fixed target `T` (gate row, col 1). -/
  yT : F
  /-- The x-coordinate of the input accumulator `P₀` (gate row, col 2). -/
  x0 : F
  /-- The y-coordinate of the input accumulator `P₀` (gate row, col 3). -/
  y0 : F
  /-- The x-coordinate of the accumulator `P₁` after bit 0 (gate row, col 7). -/
  x1 : F
  /-- The y-coordinate of the accumulator `P₁` after bit 0 (gate row, col 8). -/
  y1 : F
  /-- The x-coordinate of the accumulator `P₂` after bit 1 (gate row, col 9). -/
  x2 : F
  /-- The y-coordinate of the accumulator `P₂` after bit 1 (gate row, col 10). -/
  y2 : F
  /-- The x-coordinate of the accumulator `P₃` after bit 2 (gate row, col 11). -/
  x3 : F
  /-- The y-coordinate of the accumulator `P₃` after bit 2 (gate row, col 12). -/
  y3 : F
  /-- The x-coordinate of the accumulator `P₄` after bit 3 (gate row, col 13). -/
  x4 : F
  /-- The y-coordinate of the accumulator `P₄` after bit 3 (gate row, col 14). -/
  y4 : F
  /-- The x-coordinate of the output accumulator `P₅` (next row, col 0). -/
  x5 : F
  /-- The y-coordinate of the output accumulator `P₅` (next row, col 1). -/
  y5 : F
  /-- The input scalar register (gate row, col 4). -/
  n : F
  /-- The output scalar register `n' = 32·n + 16·b₀ + ⋯ + b₄` (gate row, col 5). -/
  nPrime : F
  /-- Bit 0: `1` adds `+T`, `0` adds `−T` in step 0 (next row, col 2). -/
  b0 : F
  /-- Bit 1: `1` adds `+T`, `0` adds `−T` in step 1 (next row, col 3). -/
  b1 : F
  /-- Bit 2: `1` adds `+T`, `0` adds `−T` in step 2 (next row, col 4). -/
  b2 : F
  /-- Bit 3: `1` adds `+T`, `0` adds `−T` in step 3 (next row, col 5). -/
  b3 : F
  /-- Bit 4: `1` adds `+T`, `0` adds `−T` in step 4 (next row, col 6). -/
  b4 : F
  /-- The first-addition slope of bit block 0 (next row, col 7). -/
  s0 : F
  /-- The first-addition slope of bit block 1 (next row, col 8). -/
  s1 : F
  /-- The first-addition slope of bit block 2 (next row, col 9). -/
  s2 : F
  /-- The first-addition slope of bit block 3 (next row, col 10). -/
  s3 : F
  /-- The first-addition slope of bit block 4 (next row, col 11). -/
  s4 : F

variable {F : Type*}

/-- Map a function across every witness cell. At a ring homomorphism this moves a witness
    between rings, e.g. from the column polynomials to their values at a domain node. -/
def Witness.map {R S : Type*} (f : R → S) (w : Witness R) : Witness S where
  xT := f w.xT
  yT := f w.yT
  x0 := f w.x0
  y0 := f w.y0
  x1 := f w.x1
  y1 := f w.y1
  x2 := f w.x2
  y2 := f w.y2
  x3 := f w.x3
  y3 := f w.y3
  x4 := f w.x4
  y4 := f w.y4
  x5 := f w.x5
  y5 := f w.y5
  n := f w.n
  nPrime := f w.nPrime
  b0 := f w.b0
  b1 := f w.b1
  b2 := f w.b2
  b3 := f w.b3
  b4 := f w.b4
  s0 := f w.s0
  s1 := f w.s1
  s2 := f w.s2
  s3 := f w.s3
  s4 := f w.s4

/-! ## The constraint expressions

The 21 constraint left-hand sides are defined once, as ring elements (`constraints`). The
relational spec `Holds`, the checker `ok` and the quotient layer's constraint polynomials
(the same list over `F[X]`) all read them. -/

/-- The 4 cleared constraint expressions of one bit block: boolean, `s1`, `xo`, `yo`. `b` is
    the bit, `(xb,yb)` the target, `s1` the first slope, `(xi,yi)` and `(xo,yo)` the input and
    output accumulators. -/
def singleBitCons [CommRing F] (b xb yb s1 xi yi xo yo : F) : List F :=
  let bSign := 2 * b - 1
  let s1sq  := s1 * s1
  let rx    := s1sq - xi - xb
  let t     := xi - rx           -- = 2·xi − s1² + xb
  let u     := 2 * yi - t * s1
  [ b * b - b                                              -- boolean
  , (xi - xb) * s1 - (yi - bSign * yb)                     -- constrain s1
  , u * u - t * t * (xo - xb + s1sq)                       -- constrain xo (via s2 = u/t)
  , (yo + yi) * t - (xi - xo) * u ]                        -- constrain yo

/-- One bit block holds: its four constraint expressions vanish. -/
def singleBitHolds [CommRing F] (b xb yb s1 xi yi xo yo : F) : Prop :=
  ∀ e ∈ singleBitCons b xb yb s1 xi yi xo yo, e = 0

/-- `singleBitHolds` as a 4-conjunction, with `t` and `u` written out. -/
theorem singleBitHolds_iff [CommRing F] (b xb yb s1 xi yi xo yo : F) :
    singleBitHolds b xb yb s1 xi yi xo yo ↔
      (b * b - b = 0)
      ∧ ((xi - xb) * s1 - (yi - (2 * b - 1) * yb) = 0)
      ∧ ((2 * yi - (xi - (s1 * s1 - xi - xb)) * s1) * (2 * yi - (xi - (s1 * s1 - xi - xb)) * s1)
          - (xi - (s1 * s1 - xi - xb)) * (xi - (s1 * s1 - xi - xb)) * (xo - xb + s1 * s1) = 0)
      ∧ ((yo + yi) * (xi - (s1 * s1 - xi - xb))
          - (xi - xo) * (2 * yi - (xi - (s1 * s1 - xi - xb)) * s1) = 0) := by
  simp only [singleBitHolds, singleBitCons, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true]

/-- The boolean constraint `b·b − b = 0` of a bit block. -/
theorem singleBitHolds.bool [CommRing F] {b xb yb s1 xi yi xo yo : F}
    (h : singleBitHolds b xb yb s1 xi yi xo yo) : b * b - b = 0 :=
  ((singleBitHolds_iff b xb yb s1 xi yi xo yo).mp h).1

/-! ## The whole gate: the scalar decomposition and the 5 chained bit blocks -/

/-- The running-scalar decomposition expression:
    `n' − (32·n + 16·b0 + 8·b1 + 4·b2 + 2·b3 + b4)`, in the Horner form the gate uses. -/
def decompCons [CommRing F] (w : Witness F) : F :=
  w.nPrime - (w.b4 + 2 * (w.b3 + 2 * (w.b2 + 2 * (w.b1 + 2 * (w.b0 + 2 * w.n)))))

/-- The running-scalar decomposition holds: `decompCons w = 0`. -/
def decompHolds [CommRing F] (w : Witness F) : Prop :=
  decompCons w = 0

/-- All 21 constraint expressions: the decomposition, then the 5 chained single-bit blocks
    over the accumulator chain `(x0,y0) → … → (x5,y5)`. -/
def constraints [CommRing F] (w : Witness F) : List F :=
  decompCons w
    :: (singleBitCons w.b0 w.xT w.yT w.s0 w.x0 w.y0 w.x1 w.y1
      ++ singleBitCons w.b1 w.xT w.yT w.s1 w.x1 w.y1 w.x2 w.y2
      ++ singleBitCons w.b2 w.xT w.yT w.s2 w.x2 w.y2 w.x3 w.y3
      ++ singleBitCons w.b3 w.xT w.yT w.s3 w.x3 w.y3 w.x4 w.y4
      ++ singleBitCons w.b4 w.xT w.yT w.s4 w.x4 w.y4 w.x5 w.y5)

/-- The relational spec: all 21 constraint expressions vanish. -/
def Holds [CommRing F] (w : Witness F) : Prop :=
  ∀ e ∈ constraints w, e = 0

instance [CommRing F] [DecidableEq F] (w : Witness F) : Decidable (Holds w) := by
  unfold Holds
  infer_instance

/-- `Holds` as the structured conjunction: the decomposition plus the five bit blocks. -/
theorem holds_iff [CommRing F] (w : Witness F) :
    Holds w ↔ decompHolds w
      ∧ singleBitHolds w.b0 w.xT w.yT w.s0 w.x0 w.y0 w.x1 w.y1
      ∧ singleBitHolds w.b1 w.xT w.yT w.s1 w.x1 w.y1 w.x2 w.y2
      ∧ singleBitHolds w.b2 w.xT w.yT w.s2 w.x2 w.y2 w.x3 w.y3
      ∧ singleBitHolds w.b3 w.xT w.yT w.s3 w.x3 w.y3 w.x4 w.y4
      ∧ singleBitHolds w.b4 w.xT w.yT w.s4 w.x4 w.y4 w.x5 w.y5 := by
  simp only [Holds, constraints, decompHolds, singleBitHolds, List.forall_mem_cons,
    List.forall_mem_append, and_assoc]

/-- The executable checker: every constraint expression evaluates to zero. -/
def ok [CommRing F] [DecidableEq F] (w : Witness F) : Bool :=
  (constraints w).all (· == 0)

/-! ## Reflection: the checker faithfully decides the constraints. -/

theorem ok_iff [CommRing F] [DecidableEq F] (w : Witness F) :
    ok w = true ↔ Holds w := by
  simp only [ok, Holds, List.all_eq_true, beq_iff_eq]

/-- The constraint expressions commute with ring homomorphisms applied cellwise via
    `Witness.map`. At `f = eval (ω^i)` this reads the quotient layer's constraint polynomials at
    a domain node as the gate constraints of that node's row. -/
theorem constraints_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (w : Witness R) :
    (constraints w).map f = constraints (w.map f) := by
  simp [constraints, singleBitCons, decompCons, Witness.map, map_ofNat]

/-! ## The witness generator

Given the bit, the input and the target, `stepBit` computes the first slope and the output.
It is purely algebraic: for boolean bits and nonzero denominators the generated chain
satisfies the constraints, on a curve or not (`Kimchi.Gate.VarBaseMul.complete`). -/

/-- One generated bit step: returns `(s1, xo, yo)`. Requires `xi ≠ xb` and `t ≠ 0`. -/
def stepBit [Field F] (b xb yb xi yi : F) : F × F × F :=
  let s1   := (yi - (2 * b - 1) * yb) / (xi - xb)
  let s1sq := s1 * s1
  let s2   := 2 * yi / (2 * xi + xb - s1sq) - s1
  let xo   := xb + s2 * s2 - s1sq
  let yo   := (xi - xo) * s2 - yi
  (s1, xo, yo)

/-- The full witness: 5 generated steps from `(x0,y0)` against the target `(xb,yb)`, with
    input scalar `n`. -/
def build [Field F] (xb yb x0 y0 n b0 b1 b2 b3 b4 : F) : Witness F :=
  let (s0, x1, y1) := stepBit b0 xb yb x0 y0
  let (s1, x2, y2) := stepBit b1 xb yb x1 y1
  let (s2, x3, y3) := stepBit b2 xb yb x2 y2
  let (s3, x4, y4) := stepBit b3 xb yb x3 y3
  let (s4, x5, y5) := stepBit b4 xb yb x4 y4
  { xT := xb, yT := yb
  , x0, y0, x1, y1, x2, y2, x3, y3, x4, y4, x5, y5
  , n, nPrime := b4 + 2 * (b3 + 2 * (b2 + 2 * (b1 + 2 * (b0 + 2 * n))))
  , b0, b1, b2, b3, b4, s0, s1, s2, s3, s4 }

end Kimchi.Gate.VarBaseMul
