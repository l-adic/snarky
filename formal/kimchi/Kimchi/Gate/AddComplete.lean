import Pasta.Basic

/-!
# The kimchi complete-addition gate

Complete elliptic-curve point addition: the gate's 7 constraints over one row.

Transcribed from proof-systems `.../complete_add.rs`: the column layout
(cols 0–10: x1 y1 x2 y2 x3 y3 inf sameX s infZ x21Inv) and the 7 constraints.

The reference is Mathlib's affine group law (`WeierstrassCurve.Affine.slope / addX / addY`).
On a curve with `a₁ = a₂ = a₃ = a₄ = 0` its formulas are the gate's identities:

    slope (doubling) = 3x₁²/(2y₁)      ← c3 doubling: 2·s·y₁ = 3x₁²
    addX             = ℓ² − x₁ − x₂     ← c4: x₁+x₂+x₃ = s²
    addY             = ℓ(x₁ − x₃) − y₁  ← c5: y₃ = s(x₁−x₃) − y₁

and the sum of two affine points has coordinates `(addX, addY)` (`Point.add_some`).

## Main results

This file carries the constraint model; `Kimchi/Gate/Semantics/AddComplete.lean` proves:
* `sound` — for a satisfying witness, the sum `(x₁,y₁) + (x₂,y₂)` in
  `WeierstrassCurve.Affine.Point` is `0` when `inf = 1`, else `(x₃, y₃)`; it combines
  `sound_point_noninf`, `sound_point_inf` and `inf_boolean`.
* `build` / `complete_build` — the canonical row the honest prover fills, and the theorem
  that it satisfies the gate for on-curve inputs with `y₁ ≠ 0`; `complete` is the
  existential corollary.
-/

namespace Kimchi.Gate.AddComplete

/-- The gate's witness columns (cols 0–10). -/
structure Witness (F : Type*) where
  /-- The x-coordinate of the first addend `P₁` (column 0). -/
  x1 : F
  /-- The y-coordinate of the first addend `P₁` (column 1). -/
  y1 : F
  /-- The x-coordinate of the second addend `P₂` (column 2). -/
  x2 : F
  /-- The y-coordinate of the second addend `P₂` (column 3). -/
  y2 : F
  /-- The x-coordinate of the output sum `P₃` (column 4). -/
  x3 : F
  /-- The y-coordinate of the output sum `P₃` (column 5). -/
  y3 : F
  /-- The infinity flag: `1` when the sum is the point at infinity, else `0` (column 6). -/
  inf : F
  /-- The equal-x flag `sameX = (x₁ == x₂)`, pinned via the witnessed `x21Inv` (column 7). -/
  sameX : F
  /-- The addition slope — secant, or tangent in the doubling case (column 8). -/
  s : F
  /-- The witnessed inverse of `y₂ − y₁` when `inf = 1`, pinning the infinity flag (column 9). -/
  infZ : F
  /-- The witnessed inverse of `x₂ − x₁` when nonzero, pinning `sameX` (column 10). -/
  x21Inv : F

variable {F : Type*}

/-- Map a function across every witness cell; at a ring homomorphism it moves a witness
    between rings, e.g. from column polynomials to their values at a domain node. -/
def Witness.map {R S : Type*} (f : R → S) (w : Witness R) : Witness S where
  x1 := f w.x1
  y1 := f w.y1
  x2 := f w.x2
  y2 := f w.y2
  x3 := f w.x3
  y3 := f w.y3
  inf := f w.inf
  sameX := f w.sameX
  s := f w.s
  infZ := f w.infZ
  x21Inv := f w.x21Inv

/-! ## The 7 constraints

The constraint left-hand sides live once, in `constraints`; `Holds` and the quotient
layer's constraint polynomials (the same list over `F[X]`) are defined from them. `CommRing`
suffices: the only inverse, of `x₂ − x₁`, is witnessed as `x21Inv`. -/

/-- The gate's 7 constraint expressions. -/
def constraints [CommRing F] (w : Witness F) : List F :=
  let x21  := w.x2 - w.x1
  let y21  := w.y2 - w.y1
  let x1sq := w.x1 * w.x1
  -- c1, c2: `sameX = (x1 == x2)`, via the witnessed inverse `x21Inv`
  [ w.x21Inv * x21 - (1 - w.sameX)                                             -- c1
  , w.sameX * x21                                                              -- c2
  -- slope: sameX ? (2·s·y₁ = 3x₁²)  :  ((x₂−x₁)·s = y₂−y₁)
  , w.sameX * (2 * w.s * w.y1 - 3 * x1sq)
      + (1 - w.sameX) * (x21 * w.s - y21)                                      -- c3
  , w.x1 + w.x2 + w.x3 - w.s * w.s                                             -- c4  (x₃)
  , w.s * (w.x1 - w.x3) - w.y1 - w.y3                                          -- c5  (y₃)
  -- inf = sameX ∧ (y₁ ≠ y₂):
  , y21 * (w.sameX - w.inf)                                                    -- c6
  , y21 * w.infZ - w.inf ]                                                     -- c7

/-- The relational spec: all 7 constraint expressions vanish. -/
def Holds [CommRing F] (w : Witness F) : Prop :=
  ∀ e ∈ constraints w, e = 0

instance [CommRing F] [DecidableEq F] (w : Witness F) : Decidable (Holds w) := by
  unfold Holds
  infer_instance

/-- `Holds` as the conjunction c1–c7, the form the semantics proofs use. -/
theorem holds_iff [CommRing F] (w : Witness F) :
    Holds w ↔
      (w.x21Inv * (w.x2 - w.x1) - (1 - w.sameX) = 0)                           -- c1
      ∧ (w.sameX * (w.x2 - w.x1) = 0)                                          -- c2
      ∧ (w.sameX * (2 * w.s * w.y1 - 3 * (w.x1 * w.x1))
           + (1 - w.sameX) * ((w.x2 - w.x1) * w.s - (w.y2 - w.y1)) = 0)        -- c3
      ∧ (w.x1 + w.x2 + w.x3 - w.s * w.s = 0)                                   -- c4
      ∧ (w.s * (w.x1 - w.x3) - w.y1 - w.y3 = 0)                                -- c5
      ∧ ((w.y2 - w.y1) * (w.sameX - w.inf) = 0)                                -- c6
      ∧ ((w.y2 - w.y1) * w.infZ - w.inf = 0) := by                             -- c7
  simp only [Holds, constraints, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true]

/-- The constraint expressions commute with ring homomorphisms applied cellwise. At
    evaluation at a domain node, the constraint polynomials' values there are the gate
    constraints of that node's row. -/
theorem constraints_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (w : Witness R) :
    (constraints w).map f = constraints (w.map f) := by
  simp [constraints, Witness.map, map_ofNat]

end Kimchi.Gate.AddComplete
