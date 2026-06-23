/-
  Gates/VarBaseMul.lean

  The kimchi variable-base scalar-multiplication gate (`VarBaseMul`), transcribed
  from proof-systems `kimchi/src/circuits/polynomials/varbasemul.rs`.

  The gate processes 5 bits of a double-and-add scalar multiplication across two
  rows (a `VBSM` row and a `ZERO` row). Per bit it computes the EC operation

        Output = (Input − (2·b − 1)·Target) + Input          (i.e. 2·Input ∓ Target)

  using the efficient "(P+Q)+P without the intermediate Y" formula (1 mul, 2
  squarings, 2 divisions). Writing `Input = (xi,yi)`, `Target = (xb,yb)`:

      s1 := (yi − (2b−1)·yb) / (xi − xb)
      rx := s1² − xi − xb                     -- x of the intermediate Input∓Target
      t  := xi − rx   (= 2xi − s1² + xb)
      u  := 2yi − t·s1
      s2 := u / t                             -- slope of the second addition
      xo := xb + s2² − s1²
      yo := (xi − xo)·s2 − yi

  Cleared of divisions, each bit contributes 4 constraints (boolean, s1, xo, yo);
  one more constraint ties the running scalar `n → n'`. 5·4 + 1 = 21 constraints.

  Witness layout (cols 0–14 of the VBSM row `i`, then the ZERO row `i+1`):

    row i  : xT yT x0 y0  n  n'  _  x1 y1 x2 y2 x3 y3 x4 y4   (VBSM)
    row i+1: x5 y5 b0 b1 b2 b3 b4 s0 s1 s2 s3 s4              (ZERO)

  The accumulator chain is (x0,y0) → (x1,y1) → … → (x5,y5); `base = (xT,yT)` is
  the fixed target; `s0..s4` are the per-bit `s1` slopes; `b0..b4` the bits.

  This file is the faithful CONSTRAINT transcription + reflection + a runnable
  example. The semantic soundness theorem (each output equals `2·input ∓ target`
  in Mathlib's group) is the next step — see the note at the end.
-/
import Kimchi.Curve

namespace Kimchi.VarBaseMul

/-- The `VarBaseMul` witness columns spanning the VBSM + ZERO rows. -/
structure Witness (F : Type*) where
  xT : F
  yT : F
  x0 : F
  y0 : F
  x1 : F
  y1 : F
  x2 : F
  y2 : F
  x3 : F
  y3 : F
  x4 : F
  y4 : F
  x5 : F
  y5 : F
  n : F
  nPrime : F
  b0 : F
  b1 : F
  b2 : F
  b3 : F
  b4 : F
  s0 : F
  s1 : F
  s2 : F
  s3 : F
  s4 : F
deriving Repr

variable {F : Type*}

/-! ## One bit: the 4 constraints from `single_bit` (no division — `t`, `u` are
    the cleared forms). `b` the bit, `(xb,yb)` the target, `s1` the first slope,
    `(xi,yi)` the input acc, `(xo,yo)` the output acc. -/

def singleBitHolds [CommRing F] (b xb yb s1 xi yi xo yo : F) : Prop :=
  let bSign := 2 * b - 1
  let s1sq  := s1 * s1
  let rx    := s1sq - xi - xb
  let t     := xi - rx           -- = 2·xi − s1² + xb
  let u     := 2 * yi - t * s1
  (b * b - b = 0)                                          -- boolean
  ∧ ((xi - xb) * s1 - (yi - bSign * yb) = 0)               -- constrain s1
  ∧ (u * u - t * t * (xo - xb + s1sq) = 0)                 -- constrain xo (via s2 = u/t)
  ∧ ((yo + yi) * t - (xi - xo) * u = 0)                    -- constrain yo

def singleBitOk [CommRing F] [DecidableEq F] (b xb yb s1 xi yi xo yo : F) : Bool :=
  let bSign := 2 * b - 1
  let s1sq  := s1 * s1
  let rx    := s1sq - xi - xb
  let t     := xi - rx
  let u     := 2 * yi - t * s1
  (b * b - b == 0)
    && ((xi - xb) * s1 - (yi - bSign * yb) == 0)
    && (u * u - t * t * (xo - xb + s1sq) == 0)
    && ((yo + yi) * t - (xi - xo) * u == 0)

/-! ## The whole gate: the binary-decomposition constraint plus the 5 chained
    single-bit blocks. -/

/-- The running-scalar decomposition: `n' = 32·n + 16·b0 + 8·b1 + 4·b2 + 2·b3 + b4`,
    written in the Horner form the gate uses. -/
def decompHolds [CommRing F] (w : Witness F) : Prop :=
  w.nPrime - (w.b4 + 2 * (w.b3 + 2 * (w.b2 + 2 * (w.b1 + 2 * (w.b0 + 2 * w.n))))) = 0

/-- RELATIONAL spec: all 21 constraints. -/
def Holds [CommRing F] (w : Witness F) : Prop :=
  decompHolds w
  ∧ singleBitHolds w.b0 w.xT w.yT w.s0 w.x0 w.y0 w.x1 w.y1
  ∧ singleBitHolds w.b1 w.xT w.yT w.s1 w.x1 w.y1 w.x2 w.y2
  ∧ singleBitHolds w.b2 w.xT w.yT w.s2 w.x2 w.y2 w.x3 w.y3
  ∧ singleBitHolds w.b3 w.xT w.yT w.s3 w.x3 w.y3 w.x4 w.y4
  ∧ singleBitHolds w.b4 w.xT w.yT w.s4 w.x4 w.y4 w.x5 w.y5

/-- EXECUTABLE checker. -/
def ok [CommRing F] [DecidableEq F] (w : Witness F) : Bool :=
  (w.nPrime - (w.b4 + 2 * (w.b3 + 2 * (w.b2 + 2 * (w.b1 + 2 * (w.b0 + 2 * w.n))))) == 0)
    && singleBitOk w.b0 w.xT w.yT w.s0 w.x0 w.y0 w.x1 w.y1
    && singleBitOk w.b1 w.xT w.yT w.s1 w.x1 w.y1 w.x2 w.y2
    && singleBitOk w.b2 w.xT w.yT w.s2 w.x2 w.y2 w.x3 w.y3
    && singleBitOk w.b3 w.xT w.yT w.s3 w.x3 w.y3 w.x4 w.y4
    && singleBitOk w.b4 w.xT w.yT w.s4 w.x4 w.y4 w.x5 w.y5

/-! ## Reflection: the checker faithfully decides the constraints. -/

theorem singleBitOk_iff [CommRing F] [DecidableEq F] (b xb yb s1 xi yi xo yo : F) :
    singleBitOk b xb yb s1 xi yi xo yo = true ↔ singleBitHolds b xb yb s1 xi yi xo yo := by
  simp only [singleBitOk, singleBitHolds, Bool.and_eq_true, beq_iff_eq, and_assoc]

theorem ok_iff [CommRing F] [DecidableEq F] (w : Witness F) :
    ok w = true ↔ Holds w := by
  simp only [ok, Holds, decompHolds, Bool.and_eq_true, beq_iff_eq, singleBitOk_iff, and_assoc]

/-! ## A runnable example via the witness generator.

    Port of the Rust `single_bit_witness`: given the bit and `(Input, Target)`,
    compute `(s1, Output)`. It is purely algebraic — the constraints hold for the
    generated chain regardless of whether the points lie on a curve — so any
    inputs with non-vanishing denominators give a satisfying witness. -/

/-- One generated bit step: returns `(s1, xo, yo)`. Requires `xi ≠ xb` and `t ≠ 0`. -/
def stepBit [Field F] (b xb yb xi yi : F) : F × F × F :=
  let s1   := (yi - (2 * b - 1) * yb) / (xi - xb)
  let s1sq := s1 * s1
  let s2   := 2 * yi / (2 * xi + xb - s1sq) - s1
  let xo   := xb + s2 * s2 - s1sq
  let yo   := (xi - xo) * s2 - yi
  (s1, xo, yo)

/-- Build a full witness by chaining 5 generated steps from `(x0,y0)` with target
    `(xb,yb)`, bits `b0..b4`, and running scalar `n`. -/
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

instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- A concrete 5-bit step over `ZMod 97`: target `T = (3, 5)`, input acc `(10, 20)`,
    bits `[1, 0, 1, 1, 0]`, running scalar `n = 1`. -/
def egVBM : Witness (ZMod 97) := build 3 5 10 20 1 1 0 1 1 0

-- Prints `true`: the generated witness satisfies all 21 constraints. (A kernel
-- `decide`/`rfl` proof is out of reach here — the witness fields are ZMod field
-- inverses, which don't reduce in the kernel; `#eval` uses the compiler.)
#eval ok egVBM   -- true

/-! ## Soundness (next step).

    The semantic theorem characterizing this gate: under `IsShortShape W`,
    nonsingular acc/target points, and the per-bit non-degeneracy conditions
    (`xi ≠ xb`, `t ≠ 0`), each block forces

        Point.some xo yo  =  (Point.some xi yi − (2·bᵢ − 1) • Point.some xT yT)
                                + Point.some xi yi

    i.e. `output = 2·input ∓ target` in `W.Point`, and `nPrime` is the claimed
    scalar update. Proving it means showing the fused `s2 = u/t` formula equals
    the composite of two `add_some` applications (the `(P+Q)+P` trick) — a deeper
    argument than CompleteAdd's single addition, building directly on
    `Kimchi.AddComplete`. -/

end Kimchi.VarBaseMul
