import Pasta.Basic
import Kimchi.Gate.AddComplete

/-!
# The kimchi `VarBaseMul` gate

The variable-base scalar-multiplication gate, transcribed from proof-systems
`kimchi/src/circuits/polynomials/varbasemul.rs`.

The gate processes 5 bits of a double-and-add scalar multiplication across two
rows (a `VBSM` row and a `ZERO` row). Per bit it computes the EC operation

      Output = (Input + (2·b − 1)·Target) + Input          (= 2·Input + (2b−1)·Target)

using the efficient "(P+Q)+P without the intermediate Y" formula (1 mul, 2
squarings, 2 divisions). Writing `Input = (xi,yi)`, `Target = (xb,yb)`:

    s1 := (yi − (2b−1)·yb) / (xi − xb)
    rx := s1² − xi − xb                     -- x of the intermediate Input + (2b−1)·Target
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

The accumulator chain is (x0,y0) → (x1,y1) → … → (x5,y5); `base = (xT,yT)` is the
fixed target; `s0..s4` are the per-bit `s1` slopes; `b0..b4` the bits.

This file is the GATE: one 5-bit block. The CIRCUIT that chains gates into a
full scalar multiplication lives in `Kimchi.Gate.VarBaseMul`.

## Main result

`sound` — one satisfying gate computes `∃ c : ℤ, P₅ = 32·P₀ + c·T`
in Mathlib's elliptic-curve group: the integer-scalar interface the circuit
consumes.

## Supporting development

The faithful constraint model (`Witness` / `Holds` / `ok`) + reflection
(`ok_iff`), a runnable example, then the per-gate soundness ladder against
Mathlib's group law:

* `singleBit_sound` — one bit : `output = (input + Q) + input`
* `gate_scalarMul`  — 5 bits  : `P₅ = 32·P₀ + 16·Q₀ + ⋯ + Q₄`  (point form)
* `sound` — folds those `Qⱼ` into `±T` (the integer-scalar bridge)
-/

namespace Kimchi.Gate.VarBaseMul

/-- The `VarBaseMul` witness columns spanning the VBSM + ZERO rows. -/
structure Witness (F : Type*) where
  /-- The x-coordinate of the fixed target `T` (VBSM row, col 0). -/
  xT : F
  /-- The y-coordinate of the fixed target `T` (VBSM row, col 1). -/
  yT : F
  /-- The x-coordinate of the input accumulator `P₀` (VBSM row, col 2). -/
  x0 : F
  /-- The y-coordinate of the input accumulator `P₀` (VBSM row, col 3). -/
  y0 : F
  /-- The x-coordinate of the accumulator `P₁` after bit 0 (VBSM row, col 7). -/
  x1 : F
  /-- The y-coordinate of the accumulator `P₁` after bit 0 (VBSM row, col 8). -/
  y1 : F
  /-- The x-coordinate of the accumulator `P₂` after bit 1 (VBSM row, col 9). -/
  x2 : F
  /-- The y-coordinate of the accumulator `P₂` after bit 1 (VBSM row, col 10). -/
  y2 : F
  /-- The x-coordinate of the accumulator `P₃` after bit 2 (VBSM row, col 11). -/
  x3 : F
  /-- The y-coordinate of the accumulator `P₃` after bit 2 (VBSM row, col 12). -/
  y3 : F
  /-- The x-coordinate of the accumulator `P₄` after bit 3 (VBSM row, col 13). -/
  x4 : F
  /-- The y-coordinate of the accumulator `P₄` after bit 3 (VBSM row, col 14). -/
  y4 : F
  /-- The x-coordinate of the output accumulator `P₅` (ZERO row, col 0). -/
  x5 : F
  /-- The y-coordinate of the output accumulator `P₅` (ZERO row, col 1). -/
  y5 : F
  /-- The input scalar register (VBSM row, col 4). -/
  n : F
  /-- The output scalar register `n' = 32·n + 16·b₀ + 8·b₁ + 4·b₂ + 2·b₃ + b₄` (VBSM row, col 5). -/
  nPrime : F
  /-- Bit 0: selects `+T` (`b₀ = 1`) vs `−T` (`b₀ = 0`) in step 0 (ZERO row, col 2). -/
  b0 : F
  /-- Bit 1: selects `+T` (`b₁ = 1`) vs `−T` (`b₁ = 0`) in step 1 (ZERO row, col 3). -/
  b1 : F
  /-- Bit 2: selects `+T` (`b₂ = 1`) vs `−T` (`b₂ = 0`) in step 2 (ZERO row, col 4). -/
  b2 : F
  /-- Bit 3: selects `+T` (`b₃ = 1`) vs `−T` (`b₃ = 0`) in step 3 (ZERO row, col 5). -/
  b3 : F
  /-- Bit 4: selects `+T` (`b₄ = 1`) vs `−T` (`b₄ = 0`) in step 4 (ZERO row, col 6). -/
  b4 : F
  /-- The first-addition slope `s1` of bit block 0 (ZERO row, col 7). -/
  s0 : F
  /-- The first-addition slope `s1` of bit block 1 (ZERO row, col 8). -/
  s1 : F
  /-- The first-addition slope `s1` of bit block 2 (ZERO row, col 9). -/
  s2 : F
  /-- The first-addition slope `s1` of bit block 3 (ZERO row, col 10). -/
  s3 : F
  /-- The first-addition slope `s1` of bit block 4 (ZERO row, col 11). -/
  s4 : F
deriving Repr

variable {F : Type*}

/-- Map a function across every witness cell. Instantiating at a ring homomorphism moves a
    witness between rings — in particular between `Witness (Polynomial F)` (the column
    polynomials of the quotient layer) and `Witness F` (their values at a domain node). -/
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

The 21 constraint left-hand sides live here once, as ring elements (`singleBitCons` /
`decompCons` / `constraints`); the relational spec (`Holds`), the executable checker (`ok`),
and the quotient layer's constraint polynomials (which read the same list over `F[X]`) are
all defined from them. -/

/-- The 4 cleared constraint expressions of one bit block, from `single_bit` (no division —
    `t`, `u` are the cleared forms): boolean, `s1`, `xo`, `yo`. `b` the bit, `(xb,yb)` the
    target, `s1` the first slope, `(xi,yi)` the input acc, `(xo,yo)` the output acc. -/
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

/-- `singleBitHolds` as the readable 4-conjunction (the cleared `t`/`u` forms written out). -/
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

/-- The boolean constraint of a bit block, projected from `singleBitHolds` (its first
    expression). -/
theorem singleBitHolds.bool [CommRing F] {b xb yb s1 xi yi xo yo : F}
    (h : singleBitHolds b xb yb s1 xi yi xo yo) : b * b - b = 0 :=
  ((singleBitHolds_iff b xb yb s1 xi yi xo yo).mp h).1

/-! ## The whole gate: the binary-decomposition constraint plus the 5 chained
    single-bit blocks. -/

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

/-- RELATIONAL spec: all 21 constraint expressions vanish. -/
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

/-- EXECUTABLE checker: every constraint expression evaluates to zero. -/
def ok [CommRing F] [DecidableEq F] (w : Witness F) : Bool :=
  (constraints w).all (· == 0)

/-! ## Reflection: the checker faithfully decides the constraints. -/

theorem ok_iff [CommRing F] [DecidableEq F] (w : Witness F) :
    ok w = true ↔ Holds w := by
  simp only [ok, Holds, List.all_eq_true, beq_iff_eq]

/-- The constraint expressions commute with ring homomorphisms (applied cellwise via
    `Witness.map`): `constraints` is a natural transformation `Witness ⇒ List` over
    commutative rings. At `f = eval (ω^i) : F[X] →+* F` this turns the quotient layer's
    constraint polynomials' values at a domain node into the gate constraints of that
    node's row witness. -/
theorem constraints_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (w : Witness R) :
    (constraints w).map f = constraints (w.map f) := by
  simp [constraints, singleBitCons, decompCons, Witness.map, map_ofNat]

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

end Kimchi.Gate.VarBaseMul
