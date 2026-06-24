import Kimchi.Curve
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
full scalar multiplication lives in `Kimchi.Circuit.VarBaseMul`.

## Main result

`gate_scalarMul_int` — one satisfying gate computes `∃ c : ℤ, P₅ = 32·P₀ + c·T`
in Mathlib's elliptic-curve group: the integer-scalar interface the circuit
consumes.

## Supporting development

The faithful constraint model (`Witness` / `Holds` / `ok`) + reflection
(`ok_iff`), a runnable example, then the per-gate soundness ladder against
Mathlib's group law:

* `singleBit_sound` — one bit : `output = (input + Q) + input`
* `gate_scalarMul`  — 5 bits  : `P₅ = 32·P₀ + 16·Q₀ + ⋯ + Q₄`  (point form)
* `gate_scalarMul_int` — folds those `Qⱼ` into `±T` (the integer-scalar bridge)
-/

namespace Kimchi.Gate.VarBaseMul

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

/-! ## Soundness.

    Per bit, a satisfying block computes the double-and-add step

        output = (input + Q) + input        (= 2·input + (2·b − 1)·target)

    in the curve group, where `Q := (xb, (2b−1)·yb)` is the sign-selected target
    (`Q = target` when `b = 1`, `Q = −target` when `b = 0`, since on a short
    Weierstrass curve negation is `y ↦ −y`).

    The content is that the fused `s2 = u/t` formula — which skips the
    intermediate `Y` of `input + Q` — equals the slope of the SECOND addition, so
    the block is exactly the composite of two Mathlib affine additions. This
    builds on the already-proven `Kimchi.Gate.AddComplete`, whose `sound_point_*`
    theorems characterize one such addition. The non-degeneracy hypotheses
    `xi ≠ xb` (first addition non-vertical) and `2·xi + xb − s1² ≠ 0` (i.e.
    `t ≠ 0`, second addition non-vertical) are exactly when the two divisions are
    defined. -/

section Soundness

open WeierstrassCurve.Affine

variable [Field F] [DecidableEq F]

/-- One non-vertical (secant) affine addition, packaged with explicit output
    coordinates. If `(x₁,y₁)`, `(x₂,y₂)` are nonsingular points with `x₁ ≠ x₂`,
    and `ℓ, x₃, y₃` are the secant slope and resulting coordinates, then their
    group sum is the nonsingular point `(x₃, y₃)`.

    This is the secant specialization of
    `Kimchi.Gate.AddComplete.sound_point_noninf` (its first slope branch); unlike that
    theorem it carries no `y₁ ≠ 0` hypothesis, since the doubling branch is
    excluded by `x₁ ≠ x₂`. -/
lemma secant_add
    (W : WeierstrassCurve.Affine F) (ha : IsShortShape W)
    {x1 y1 x2 y2 : F}
    (h1 : W.Nonsingular x1 y1) (h2 : W.Nonsingular x2 y2)
    (hx : x1 ≠ x2)
    {l x3 y3 : F}
    (hl : l = (y1 - y2) / (x1 - x2))
    (hx3 : x3 = l * l - x1 - x2)
    (hy3 : y3 = l * (x1 - x3) - y1) :
    ∃ h3 : W.Nonsingular x3 y3,
      Point.some h1 + Point.some h2 = Point.some h3 := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  have hslope : W.slope x1 x2 y1 y2 = l := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx, hl]
  have hfin : ¬(x1 = x2 ∧ y1 = W.negY x2 y2) := fun hc => hx hc.1
  have hx3' : W.addX x1 x2 (W.slope x1 x2 y1 y2) = x3 := by
    rw [hslope]; simp only [WeierstrassCurve.Affine.addX, ha1, ha2]
    rw [hx3]; ring
  have hy3' : W.addY x1 x2 y1 (W.slope x1 x2 y1 y2) = y3 := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, ha1, ha2, ha3]
    rw [hy3, hx3]; ring
  rw [← hx3', ← hy3']
  exact ⟨WeierstrassCurve.Affine.nonsingular_add h1 h2 hfin,
         WeierstrassCurve.Affine.Point.add_some hfin⟩

/-- Per-bit soundness. A single-bit block that
    satisfies `singleBitHolds` computes `output = (input + Q) + input` in the
    group, where `Q = (xb, (2b−1)·yb)` is the sign-selected target. The output is
    a genuine nonsingular curve point (hence the `∃ hO`, mirroring
    `Kimchi.Gate.AddComplete.sound_point_noninf`).

    The block is exactly the composite of two affine additions: `R := I + Q`
    (first slope `s1`, non-vertical since `xi ≠ xb`) followed by `O := R + I`
    (second slope `s2 = u/t`, non-vertical since `t = 2·xi + xb − s1² ≠ 0`). The
    fused `s2 = u/t` formula skips the intermediate `Y` of `R`; we recover it from
    the `xo`/`yo` constraints, then close with `secant_add` twice.

    No booleanity hypothesis on `b` is needed: the algebraic argument holds for
    arbitrary `b`, since `Q`'s validity as a curve point is supplied directly by
    `hQ`. (At the gate level the `b ∈ {0,1}` constraint is what makes
    `Q = (2b−1)·target` equal `±target`.) -/
theorem singleBit_sound
    (W : WeierstrassCurve.Affine F) (ha : IsShortShape W)
    (b xb yb s1 xi yi xo yo : F)
    (hI : W.Nonsingular xi yi)
    (hQ : W.Nonsingular xb ((2 * b - 1) * yb))
    (hxne : xi ≠ xb)
    (htne : 2 * xi + xb - s1 * s1 ≠ 0)
    (h : singleBitHolds b xb yb s1 xi yi xo yo) :
    ∃ hO : W.Nonsingular xo yo,
      Point.some hO = (Point.some hI + Point.some hQ) + Point.some hI := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  simp only [singleBitHolds] at h
  obtain ⟨hbool, hc_s1, hc_xo, hc_yo⟩ := h
  have hdiff1 : xi - xb ≠ 0 := sub_ne_zero.mpr hxne
  -- the first addition `I + Q` has slope `s1`
  have hl1 : s1 = (yi - (2 * b - 1) * yb) / (xi - xb) := by
    rw [eq_div_iff hdiff1]; linear_combination hc_s1
  -- name the intermediate point `R = (rx, ry)` and the second slope `s2`
  set rx : F := s1 * s1 - xi - xb with hrx
  set ry : F := s1 * (xi - rx) - yi with hry
  set s2 : F := (ry - yi) / (rx - xi) with hs2
  clear_value s2 ry rx
  have htval : xi - rx = 2 * xi + xb - s1 * s1 := by rw [hrx]; ring
  have htt : xi - rx ≠ 0 := by rw [htval]; exact htne
  have hrxne : rx ≠ xi := by intro hc; exact htt (by rw [hc]; ring)
  have hxine : rx - xi ≠ 0 := sub_ne_zero.mpr hrxne
  -- first addition: `I + Q = R`
  obtain ⟨hR, hAdd1⟩ :=
    secant_add W ⟨ha1, ha2, ha3, ha4⟩ hI hQ hxne hl1 hrx hry
  -- the fused `s2 = u/t` is the slope of the second addition: `s2² = xo − xb + s1²`
  have hs2sq : s2 * s2 = xo - xb + s1 * s1 := by
    rw [hs2, div_mul_div_comm, div_eq_iff (mul_ne_zero hxine hxine), hry]
    linear_combination hc_xo
  have hxo : xo = s2 * s2 - rx - xi := by rw [hs2sq, hrx]; ring
  have hyo : yo = s2 * (rx - xo) - ry := by
    have hsr : s2 * (rx - xi) = ry - yi := by
      rw [hs2, div_mul_cancel₀]; exact hxine
    have hyo' : yo = (xi - xo) * s2 - yi := by
      rw [hs2]; field_simp
      linear_combination -hc_yo - (xi - xo) * hry
    rw [hyo']; linear_combination -hsr
  -- second addition: `R + I = O`
  obtain ⟨hO, hAdd2⟩ :=
    secant_add W ⟨ha1, ha2, ha3, ha4⟩ hR hI hrxne hs2 hxo hyo
  exact ⟨hO, by rw [hAdd1, hAdd2]⟩

/-- Full-gate scalar multiplication (STUB — body left to automation). Chaining
    `singleBit_sound` across all five blocks, a satisfying gate computes the
    double-and-add accumulation

        P₅ = 32·P₀ + 16·Q₀ + 8·Q₁ + 4·Q₂ + 2·Q₃ + Q₄

    in the curve group, where `Pᵢ = (xᵢ, yᵢ)` is the accumulator chain and
    `Qᵢ = (xT, (2bᵢ−1)·yT)` is the sign-selected target for bit `i` (so `Qᵢ = ±T`
    when `bᵢ ∈ {0,1}`). This is exactly variable-base scalar multiplication by the
    signed-binary digits `b₀..b₄`. The companion `decompHolds` constraint records
    the same digits in the scalar register `n → n' = 32n + 16b₀ + ⋯ + b₄`.

    `Pᵢ` nonsingularity and the per-step non-degeneracy (`xᵢ ≠ xT`, `tᵢ ≠ 0`) are
    hypotheses; booleanity of each `bᵢ` is available from `Holds` if needed. -/
theorem gate_scalarMul
    (W : WeierstrassCurve.Affine F) (ha : IsShortShape W) (w : Witness F)
    (h0 : W.Nonsingular w.x0 w.y0) (h1 : W.Nonsingular w.x1 w.y1)
    (h2 : W.Nonsingular w.x2 w.y2) (h3 : W.Nonsingular w.x3 w.y3)
    (h4 : W.Nonsingular w.x4 w.y4) (h5 : W.Nonsingular w.x5 w.y5)
    (hQ0 : W.Nonsingular w.xT ((2 * w.b0 - 1) * w.yT))
    (hQ1 : W.Nonsingular w.xT ((2 * w.b1 - 1) * w.yT))
    (hQ2 : W.Nonsingular w.xT ((2 * w.b2 - 1) * w.yT))
    (hQ3 : W.Nonsingular w.xT ((2 * w.b3 - 1) * w.yT))
    (hQ4 : W.Nonsingular w.xT ((2 * w.b4 - 1) * w.yT))
    (hxne0 : w.x0 ≠ w.xT) (hxne1 : w.x1 ≠ w.xT) (hxne2 : w.x2 ≠ w.xT)
    (hxne3 : w.x3 ≠ w.xT) (hxne4 : w.x4 ≠ w.xT)
    (htne0 : 2 * w.x0 + w.xT - w.s0 * w.s0 ≠ 0)
    (htne1 : 2 * w.x1 + w.xT - w.s1 * w.s1 ≠ 0)
    (htne2 : 2 * w.x2 + w.xT - w.s2 * w.s2 ≠ 0)
    (htne3 : 2 * w.x3 + w.xT - w.s3 * w.s3 ≠ 0)
    (htne4 : 2 * w.x4 + w.xT - w.s4 * w.s4 ≠ 0)
    (h : Holds w) :
    Point.some h5
      = (32 : ℕ) • Point.some h0
        + (16 : ℕ) • Point.some hQ0 + (8 : ℕ) • Point.some hQ1
        + (4 : ℕ) • Point.some hQ2 + (2 : ℕ) • Point.some hQ3
        + Point.some hQ4 := by
  obtain ⟨_hdecomp, hb0, hb1, hb2, hb3, hb4⟩ := h
  obtain ⟨_, e0⟩ := singleBit_sound W ha w.b0 w.xT w.yT w.s0 w.x0 w.y0 w.x1 w.y1
    h0 hQ0 hxne0 htne0 hb0
  obtain ⟨_, e1⟩ := singleBit_sound W ha w.b1 w.xT w.yT w.s1 w.x1 w.y1 w.x2 w.y2
    h1 hQ1 hxne1 htne1 hb1
  obtain ⟨_, e2⟩ := singleBit_sound W ha w.b2 w.xT w.yT w.s2 w.x2 w.y2 w.x3 w.y3
    h2 hQ2 hxne2 htne2 hb2
  obtain ⟨_, e3⟩ := singleBit_sound W ha w.b3 w.xT w.yT w.s3 w.x3 w.y3 w.x4 w.y4
    h3 hQ3 hxne3 htne3 hb3
  obtain ⟨_, e4⟩ := singleBit_sound W ha w.b4 w.xT w.yT w.s4 w.x4 w.y4 w.x5 w.y5
    h4 hQ4 hxne4 htne4 hb4
  -- match the existential outputs with the given nonsingularity proofs by proof irrelevance
  have eq1 : Point.some h1 = (Point.some h0 + Point.some hQ0) + Point.some h0 := e0
  have eq2 : Point.some h2 = (Point.some h1 + Point.some hQ1) + Point.some h1 := e1
  have eq3 : Point.some h3 = (Point.some h2 + Point.some hQ2) + Point.some h2 := e2
  have eq4 : Point.some h4 = (Point.some h3 + Point.some hQ3) + Point.some h3 := e3
  have eq5 : Point.some h5 = (Point.some h4 + Point.some hQ4) + Point.some h4 := e4
  rw [eq5, eq4, eq3, eq2, eq1]
  abel

omit [DecidableEq F] in
/-- Two affine points with the same `x` and provably-equal `y` are equal (proof
    irrelevance on the nonsingularity witness). -/
private lemma some_eq_some (W : WeierstrassCurve.Affine F) {x y y' : F}
    (h : W.Nonsingular x y) (h' : W.Nonsingular x y') (hy : y = y') :
    Point.some h = Point.some h' := by
  subst hy; rfl

omit [DecidableEq F] in
/-- Booleanity from the field constraint `b·b − b = 0`. -/
private lemma bool_of_sq {b : F} (h : b * b - b = 0) : b = 0 ∨ b = 1 := by
  have hmul : b * (b - 1) = 0 := by ring_nf; linear_combination h
  rcases mul_eq_zero.mp hmul with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (by linear_combination h1)

/-- The sign-selected target `Q = (xT, (2b−1)·yT)` is `±T` once `b ∈ {0,1}`:
    on a short Weierstrass curve negation is `y ↦ −y`, so `Q = (2b−1)•T` as an
    integer scalar multiple of `T = (xT, yT)`. -/
lemma signed_target
    (W : WeierstrassCurve.Affine F) (ha : IsShortShape W)
    {b xT yT : F}
    (hT : W.Nonsingular xT yT)
    (hQ : W.Nonsingular xT ((2 * b - 1) * yT))
    (hb : b = 0 ∨ b = 1) :
    ∃ e : ℤ, Point.some hQ = e • Point.some hT ∧ (e : F) = 2 * b - 1
           ∧ (e = 1 ∨ e = -1) := by
  obtain ⟨ha1, _, ha3, _⟩ := ha
  rcases hb with rfl | rfl
  · refine ⟨-1, ?_, by push_cast; ring, Or.inr rfl⟩
    rw [neg_one_zsmul, Point.neg_some]
    exact some_eq_some W hQ _ (by rw [WeierstrassCurve.Affine.negY, ha1, ha3]; ring)
  · refine ⟨1, ?_, by push_cast; ring, Or.inl rfl⟩
    rw [one_zsmul]
    exact some_eq_some W hQ hT (by ring)

/-- The bridge to the integer-scalar form. A
    satisfying gate computes `P₅ = 32·P₀ + c·T` for an integer `c` — the gate's
    signed 5-bit value `c = 16(2b₀−1) + 8(2b₁−1) + 4(2b₂−1) + 2(2b₃−1) + (2b₄−1)`.

    This folds `gate_scalarMul`'s point sum `16·Q₀ + ⋯ + Q₄` into `c·T`: each
    `Qᵢ = (xT, (2bᵢ−1)·yT)` is `±T` once `bᵢ ∈ {0,1}` (booleanity, available from
    the `b·b − b = 0` constraint inside `Holds`), since on a short curve negation
    is `y ↦ −y`. This is exactly the per-gate relation `chain_scalarMul` consumes,
    so it closes the gap between one gate and the arbitrary-length chain. -/
theorem gate_scalarMul_int
    (W : WeierstrassCurve.Affine F) (ha : IsShortShape W) (w : Witness F)
    (h0 : W.Nonsingular w.x0 w.y0) (h1 : W.Nonsingular w.x1 w.y1)
    (h2 : W.Nonsingular w.x2 w.y2) (h3 : W.Nonsingular w.x3 w.y3)
    (h4 : W.Nonsingular w.x4 w.y4) (h5 : W.Nonsingular w.x5 w.y5)
    (hT : W.Nonsingular w.xT w.yT)
    (hQ0 : W.Nonsingular w.xT ((2 * w.b0 - 1) * w.yT))
    (hQ1 : W.Nonsingular w.xT ((2 * w.b1 - 1) * w.yT))
    (hQ2 : W.Nonsingular w.xT ((2 * w.b2 - 1) * w.yT))
    (hQ3 : W.Nonsingular w.xT ((2 * w.b3 - 1) * w.yT))
    (hQ4 : W.Nonsingular w.xT ((2 * w.b4 - 1) * w.yT))
    (hxne0 : w.x0 ≠ w.xT) (hxne1 : w.x1 ≠ w.xT) (hxne2 : w.x2 ≠ w.xT)
    (hxne3 : w.x3 ≠ w.xT) (hxne4 : w.x4 ≠ w.xT)
    (htne0 : 2 * w.x0 + w.xT - w.s0 * w.s0 ≠ 0)
    (htne1 : 2 * w.x1 + w.xT - w.s1 * w.s1 ≠ 0)
    (htne2 : 2 * w.x2 + w.xT - w.s2 * w.s2 ≠ 0)
    (htne3 : 2 * w.x3 + w.xT - w.s3 * w.s3 ≠ 0)
    (htne4 : 2 * w.x4 + w.xT - w.s4 * w.s4 ≠ 0)
    (h : Holds w) :
    ∃ c : ℤ, Point.some h5 = (32 : ℤ) • Point.some h0 + c • Point.some hT
           ∧ (c : F) = 2 * w.nPrime - 64 * w.n - 31
           ∧ c.natAbs ≤ 31 := by
  -- the Q-point sum from the already-proven nat-smul gate soundness
  have main := gate_scalarMul W ha w h0 h1 h2 h3 h4 h5 hQ0 hQ1 hQ2 hQ3 hQ4
    hxne0 hxne1 hxne2 hxne3 hxne4 htne0 htne1 htne2 htne3 htne4 h
  -- booleanity of each bit from the `b·b − b = 0` constraint inside `Holds`
  obtain ⟨hdec, hbit0, hbit1, hbit2, hbit3, hbit4⟩ := h
  obtain ⟨e0, q0, he0, hd0⟩ := signed_target W ha hT hQ0 (bool_of_sq hbit0.1)
  obtain ⟨e1, q1, he1, hd1⟩ := signed_target W ha hT hQ1 (bool_of_sq hbit1.1)
  obtain ⟨e2, q2, he2, hd2⟩ := signed_target W ha hT hQ2 (bool_of_sq hbit2.1)
  obtain ⟨e3, q3, he3, hd3⟩ := signed_target W ha hT hQ3 (bool_of_sq hbit3.1)
  obtain ⟨e4, q4, he4, hd4⟩ := signed_target W ha hT hQ4 (bool_of_sq hbit4.1)
  refine ⟨16 * e0 + 8 * e1 + 4 * e2 + 2 * e3 + e4, ?_, ?_, ?_⟩
  · rw [main, q0, q1, q2, q3, q4]
    simp only [← natCast_zsmul, smul_smul]
    push_cast
    rw [add_smul, add_smul, add_smul, add_smul]
    abel
  · -- `c` matches the scalar register: `(c:F) = 2·n' − 64·n − 31`, from `decompHolds`.
    simp only [decompHolds] at hdec
    push_cast
    rw [he0, he1, he2, he3, he4]
    linear_combination -2 * hdec
  · -- magnitude: each signed digit is ±1, so `|c| ≤ 16+8+4+2+1 = 31`.
    rcases hd0 with rfl | rfl <;> rcases hd1 with rfl | rfl <;>
      rcases hd2 with rfl | rfl <;> rcases hd3 with rfl | rfl <;>
      rcases hd4 with rfl | rfl <;> decide

end Soundness

end Kimchi.Gate.VarBaseMul
