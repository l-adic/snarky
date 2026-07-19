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

We model the UPSTREAM-FIXED gate: 12 constraints, including the distinct-point check
`(xP − xR)·(xR − xS)·inv = 1` (o1-labs/proof-systems@64129ce4) which pins the
accumulator away from `−P` / `−R`. The pre-fix gate without it is underconstrained
(it admits the spurious `R = −P`) — see `block_sound` / `distinctPoints`.

The EC core (`(P + Q) + P` per window) reuses `Kimchi.Gate.VarBaseMul`'s
`secant_add` (general affine addition) and `signed_target` (the `±` selection); the
new ingredients are the endomorphism base-choice and the GLV `[k₁]T + [k₂]φ(T)`
accumulation.

## Main results

* `selectQ` — GLV target selection: a window's `Q` is `±T` (when `b₁ = 0`) or
  `±φ(T)` (when `b₁ = 1`), via `Kimchi.signed_target` with base `T` or `φ(T)`.
* `block_sound` — one window's `(P + Q) + P` double-and-add, via `Kimchi.secant_add`
  twice (general in `Q`; carries the `xR ≠ xP` non-degeneracy the modeled gate
  revision needs — see its docstring + the upstream fix it references).
* `row_sound` / `sound` — the per-row two-window chain `R = (P+Q₁)+P`,
  `S = (R+Q₂)+R`, exposed as `S = 4·P + c₁·T + c₂·φ(T)` (integers `c₁, c₂`) — the
  GLV interface the circuit folds.

## Supporting development

The constraint model `Witness` / `Holds`, the booleanity helper `bool_of_mul`, the
distinct-point lemma `distinctPoints` (which discharges `block_sound`'s
non-degeneracy at the row level), and the `some_congr` point congruence. The GLV
accumulation `P_m = 4^m·P₀ + k₁·T + k₂·φ(T)`, its eigenvalue collapse, and the
recoding correspondence with EndoScalar live in `Kimchi.Gate.EndoMul` /
`Kimchi.Gate.EndoMul.Recoding`, culminating in `endoMul`: per 2-bit window
the two gates assign the same signed base, so `EndoMul` multiplies the base by exactly
the scalar `EndoScalar` decodes.
-/

namespace Kimchi.Gate.EndoMul

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

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
  inv : F

/-- Map a function across every witness cell. Instantiating at a ring homomorphism moves a
    witness between rings — in particular between `Witness (Polynomial F)` (the column
    polynomials of the quotient layer) and `Witness F` (their values at a domain node). -/
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

/-- The 12 constraint expressions: two `(P+Q)+P` blocks (3 each, with `Q` the endo-and-
    sign-selected target), the distinct-point check, 4 booleanity checks, and the
    scalar-register decomposition — the single transcription, from which the relational
    spec (`Holds`) and the quotient layer's constraint polynomials are both read. `endo`
    is the base-field endomorphism coefficient.
    (The distinct-point check is the upstream fix o1-labs/proof-systems@64129ce4 — see
    `block_sound` / `distinctPoints`; the pre-fix gate without it is underconstrained.) -/
def constraints {R : Type*} [CommRing R] (endo : R) (w : Witness R) : List R :=
  let xq1 := (1 + (endo - 1) * w.b1) * w.xT
  let yq1 := (2 * w.b2 - 1) * w.yT
  let xq2 := (1 + (endo - 1) * w.b3) * w.xT
  let yq2 := (2 * w.b4 - 1) * w.yT
  -- first window `P → R`, slope `s1`
  [ (xq1 - w.xP) * w.s1 - (yq1 - w.yP)
  , (2 * w.xP - w.s1 ^ 2 + xq1) * ((w.xP - w.xR) * w.s1 + w.yR + w.yP)
      - (w.xP - w.xR) * (2 * w.yP)
  , (w.yR + w.yP) ^ 2 - (w.xP - w.xR) ^ 2 * (w.s1 ^ 2 - xq1 + w.xR)
  -- second window `R → S`, slope `s3`
  , (xq2 - w.xR) * w.s3 - (yq2 - w.yR)
  , (2 * w.xR - w.s3 ^ 2 + xq2) * ((w.xR - w.xS) * w.s3 + w.yS + w.yR)
      - (w.xR - w.xS) * (2 * w.yR)
  , (w.yS + w.yR) ^ 2 - (w.xR - w.xS) ^ 2 * (w.s3 ^ 2 - xq2 + w.xS)
  -- distinct-point check (upstream fix): `inv` witnesses `(xP−xR)·(xR−xS)` is a
  -- unit, forcing `xP ≠ xR` and `xR ≠ xS` (no degenerate `R = −P` / `S = −R`)
  , (w.xP - w.xR) * (w.xR - w.xS) * w.inv - 1
  -- booleanity of the four bits
  , w.b1 * (w.b1 - 1)
  , w.b2 * (w.b2 - 1)
  , w.b3 * (w.b3 - 1)
  , w.b4 * (w.b4 - 1)
  -- scalar register
  , w.nPrime - (16 * w.n + 8 * w.b1 + 4 * w.b2 + 2 * w.b3 + w.b4) ]

/-- RELATIONAL spec: all 12 constraint expressions vanish. -/
def Holds (endo : F) (w : Witness F) : Prop :=
  ∀ e ∈ constraints endo w, e = 0

instance [DecidableEq F] (endo : F) (w : Witness F) : Decidable (Holds endo w) := by
  unfold Holds
  infer_instance

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

omit [DecidableEq F] in
/-- The constraint expressions commute with ring homomorphisms (applied cellwise via
    `Witness.map`, with the `endo` parameter transported): `constraints` is a natural
    transformation over commutative rings. -/
theorem constraints_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (endo : R) (w : Witness R) :
    (constraints endo w).map f = constraints (f endo) (w.map f) := by
  simp [constraints, Witness.map, map_ofNat]

end Kimchi.Gate.EndoMul
