import Kimchi.Gate.VarBaseMul

/-!
# The kimchi `EndoMul` gate

The endomorphism-optimized variable-base scalar-multiplication gate, transcribed from
proof-systems `kimchi/src/circuits/polynomials/endosclmul.rs` and snarky-kimchi's
`EndoMul.purs`.

It is VarBaseMul's `(P + Q) + P` double-and-add, but each 2-bit window selects `Q` from
`{T, −T, φ(T), −φ(T)}` (the GLV optimization), using the curve endomorphism

      φ(x, y) = (endo · x, y)      (endo a primitive cube root of unity, φ(T) = [λ]T)

so that `[k]T = [k₁]T + [k₂]·φ(T)` with `k₁, k₂` half-width. Each row processes 4 bits, two
windows `P → R → S`:

* `Q₁ = (xq₁, yq₁)` with `xq₁ = (1 + (endo−1)·b₁)·xT` and `yq₁ = (2·b₂ − 1)·yT`: `b₁` picks
  `T` or `φ(T)`, `b₂` the sign.
* `Q₂ = (xq₂, yq₂)` likewise from `(b₃, b₄)`.

The register threads `n' = 16·n + 8·b₁ + 4·b₂ + 2·b₃ + b₄`, and the accumulator starts at
`2·(T + φ(T))` to avoid the point at infinity.

## The distinct-point check

The modeled gate has 12 constraints, the last being `(xP − xR)·(xR − xS)·inv = 1`
(o1-labs/proof-systems@64129ce4). It forces `xR ≠ xP` and `xS ≠ xR`; without it the
window constraints also admit the spurious `R = −P`.

## Contents

This file is the transcription: `Witness`, `constraints`, `Holds`, its checker `ok`, and
`constraints_map`. Soundness (`sound`, `endoMul`) and completeness (`complete`) are proved in
`Kimchi.Gate.Semantics.EndoMul`, reusing VarBaseMul's `secant_add` and `signed_target`.
-/

namespace Kimchi.Gate.EndoMul

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

/-- One `EndoMul` row: base `T`, input accumulator `P`, the scalar register
    `n → n'`, the four bits, the two window slopes `s1`/`s3`, and the intermediate
    `R` and output `S` accumulator points. -/
structure Witness (F : Type*) where
  /-- The x-coordinate of the base point `T`. -/
  xT : F
  /-- The y-coordinate of the base point `T`. -/
  yT : F
  /-- The x-coordinate of the input accumulator `P`. -/
  xP : F
  /-- The y-coordinate of the input accumulator `P`. -/
  yP : F
  /-- The input scalar register. -/
  n : F
  /-- The output scalar register `n' = 16·n + 8·b₁ + 4·b₂ + 2·b₃ + b₄`. -/
  nPrime : F
  /-- The first window's base-choice bit: `Q₁` built on `T` (`b₁ = 0`) or `φ(T)` (`b₁ = 1`). -/
  b1 : F
  /-- The first window's sign bit: `yq₁ = (2·b₂ − 1)·yT`. -/
  b2 : F
  /-- The second window's base-choice bit: `Q₂` built on `T` (`b₃ = 0`) or `φ(T)` (`b₃ = 1`). -/
  b3 : F
  /-- The second window's sign bit: `yq₂ = (2·b₄ − 1)·yT`. -/
  b4 : F
  /-- The first window's slope (through `P` and `Q₁`). -/
  s1 : F
  /-- The x-coordinate of the intermediate accumulator `R = (P + Q₁) + P`. -/
  xR : F
  /-- The y-coordinate of the intermediate accumulator `R = (P + Q₁) + P`. -/
  yR : F
  /-- The second window's slope (through `R` and `Q₂`). -/
  s3 : F
  /-- The x-coordinate of the output accumulator `S = (R + Q₂) + R`. -/
  xS : F
  /-- The y-coordinate of the output accumulator `S = (R + Q₂) + R`. -/
  yS : F
  /-- The witnessed inverse of `(xP − xR)·(xR − xS)`, for the distinct-point check. -/
  inv : F

/-- Map a function across every witness cell. At a ring homomorphism this moves a witness
    between `Witness (Polynomial F)` (the quotient layer's column polynomials) and `Witness F`
    (their values at a domain node). -/
def Witness.map {R S : Type*} (f : R → S) (w : Witness R) : Witness S where
  xT := f w.xT
  yT := f w.yT
  xP := f w.xP
  yP := f w.yP
  n := f w.n
  nPrime := f w.nPrime
  b1 := f w.b1
  b2 := f w.b2
  b3 := f w.b3
  b4 := f w.b4
  s1 := f w.s1
  xR := f w.xR
  yR := f w.yR
  s3 := f w.s3
  xS := f w.xS
  yS := f w.yS
  inv := f w.inv

/-- The 12 constraint expressions, in the deployed gate's order: four booleanity checks, two
    `(P + Q) + P` windows (three each, `Q` the endo-and-sign-selected target), the
    scalar-register decomposition, and the distinct-point check. `Holds`, the quotient layer
    and the linearization all read this one list. The order and the register's sign are
    load-bearing: `alphaCombo` weights position `k` by `α^k`. `endo` is the base-field
    endomorphism coefficient. -/
def constraints {R : Type*} [CommRing R] (endo : R) (w : Witness R) : List R :=
  let xq1 := (1 + (endo - 1) * w.b1) * w.xT
  let yq1 := (2 * w.b2 - 1) * w.yT
  let xq2 := (1 + (endo - 1) * w.b3) * w.xT
  let yq2 := (2 * w.b4 - 1) * w.yT
  -- booleanity of the four bits
  [ w.b1 * (w.b1 - 1)
  , w.b2 * (w.b2 - 1)
  , w.b3 * (w.b3 - 1)
  , w.b4 * (w.b4 - 1)
  -- first window `P → R`, slope `s1`
  , (xq1 - w.xP) * w.s1 - (yq1 - w.yP)
  , (2 * w.xP - w.s1 ^ 2 + xq1) * ((w.xP - w.xR) * w.s1 + w.yR + w.yP)
      - (w.xP - w.xR) * (2 * w.yP)
  , (w.yR + w.yP) ^ 2 - (w.xP - w.xR) ^ 2 * (w.s1 ^ 2 - xq1 + w.xR)
  -- second window `R → S`, slope `s3`
  , (xq2 - w.xR) * w.s3 - (yq2 - w.yR)
  , (2 * w.xR - w.s3 ^ 2 + xq2) * ((w.xR - w.xS) * w.s3 + w.yS + w.yR)
      - (w.xR - w.xS) * (2 * w.yR)
  , (w.yS + w.yR) ^ 2 - (w.xR - w.xS) ^ 2 * (w.s3 ^ 2 - xq2 + w.xS)
  -- scalar register: accumulator minus the next register
  , (16 * w.n + 8 * w.b1 + 4 * w.b2 + 2 * w.b3 + w.b4) - w.nPrime
  -- distinct-point check: `inv` makes `(xP−xR)·(xR−xS)` a unit
  , (w.xP - w.xR) * (w.xR - w.xS) * w.inv - 1 ]

/-- RELATIONAL spec: all 12 constraint expressions vanish. -/
def Holds (endo : F) (w : Witness F) : Prop :=
  ∀ e ∈ constraints endo w, e = 0

instance [DecidableEq F] (endo : F) (w : Witness F) : Decidable (Holds endo w) := by
  unfold Holds
  infer_instance

/-- EXECUTABLE checker — runnable on a concrete witness. -/
def ok (endo : F) (w : Witness F) : Bool :=
  (constraints endo w).all (· == 0)

/-- Reflection: the checker faithfully decides the relational constraints. -/
theorem ok_iff (endo : F) (w : Witness F) : ok endo w = true ↔ Holds endo w := by
  simp only [ok, Holds, List.all_eq_true, beq_iff_eq]

omit [DecidableEq F] in
/-- `Holds` as the readable 12-conjunction (what the soundness proofs destructure). -/
theorem holds_iff (endo : F) (w : Witness F) :
    Holds endo w ↔
      (((1 + (endo - 1) * w.b1) * w.xT - w.xP) * w.s1 = (2 * w.b2 - 1) * w.yT - w.yP)
      ∧ ((2 * w.xP - w.s1 ^ 2 + (1 + (endo - 1) * w.b1) * w.xT)
            * ((w.xP - w.xR) * w.s1 + w.yR + w.yP)
          = (w.xP - w.xR) * (2 * w.yP))
      ∧ ((w.yR + w.yP) ^ 2
          = (w.xP - w.xR) ^ 2 * (w.s1 ^ 2 - (1 + (endo - 1) * w.b1) * w.xT + w.xR))
      ∧ (((1 + (endo - 1) * w.b3) * w.xT - w.xR) * w.s3 = (2 * w.b4 - 1) * w.yT - w.yR)
      ∧ ((2 * w.xR - w.s3 ^ 2 + (1 + (endo - 1) * w.b3) * w.xT)
            * ((w.xR - w.xS) * w.s3 + w.yS + w.yR)
          = (w.xR - w.xS) * (2 * w.yR))
      ∧ ((w.yS + w.yR) ^ 2
          = (w.xR - w.xS) ^ 2 * (w.s3 ^ 2 - (1 + (endo - 1) * w.b3) * w.xT + w.xS))
      ∧ ((w.xP - w.xR) * (w.xR - w.xS) * w.inv = 1)
      ∧ (w.b1 * (w.b1 - 1) = 0)
      ∧ (w.b2 * (w.b2 - 1) = 0)
      ∧ (w.b3 * (w.b3 - 1) = 0)
      ∧ (w.b4 * (w.b4 - 1) = 0)
      ∧ (w.nPrime = 16 * w.n + 8 * w.b1 + 4 * w.b2 + 2 * w.b3 + w.b4) := by
  simp only [Holds, constraints, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, sub_eq_zero]
  constructor
  · rintro ⟨hb1, hb2, hb3, hb4, h1, h2, h3, h4, h5, h6, hn, hinv⟩
    exact ⟨h1, h2, h3, h4, h5, h6, hinv, hb1, hb2, hb3, hb4, hn.symm⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, hinv, hb1, hb2, hb3, hb4, hn⟩
    exact ⟨hb1, hb2, hb3, hb4, h1, h2, h3, h4, h5, h6, hn.symm, hinv⟩

omit [DecidableEq F] in
/-- `constraints` commutes with ring homomorphisms, applied cellwise by `Witness.map` and
    to `endo`. -/
theorem constraints_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (endo : R) (w : Witness R) :
    (constraints endo w).map f = constraints (f endo) (w.map f) := by
  simp [constraints, Witness.map, map_ofNat]

end Kimchi.Gate.EndoMul
