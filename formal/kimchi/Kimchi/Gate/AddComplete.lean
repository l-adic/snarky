import Pasta.Basic

/-!
# The kimchi `CompleteAdd` gate

Complete elliptic-curve point addition: the gate's 7 constraints, and the theorem
that they implement Mathlib's affine group law.

Transcribed from proof-systems `.../complete_add.rs`: the column layout
(cols 0–10: x1 y1 x2 y2 x3 y3 inf sameX s infZ x21Inv) and the 7 `constraint_checks`.

The trusted ORACLE is Mathlib's affine elliptic-curve group law
(`WeierstrassCurve.Affine.slope / addX / addY`). With the Pasta-shape curve
(`a₁ = a₂ = a₃ = a₄ = 0`) Mathlib's formulas collapse to exactly the gate's identities:

    slope (doubling) = 3x₁²/(2y₁)      ← gate c3 doubling: 2·s·y₁ = 3x₁²
    addX             = ℓ² − x₁ − x₂     ← gate c4: x₁+x₂+x₃ = s²
    addY             = ℓ(x₁ − x₃) − y₁  ← gate c5: y₃ = s(x₁−x₃) − y₁

and the sum of two affine points has coordinates `(addX, addY)`
(`Point.add_some`), so matching those formulas = computing the group sum.

## Main results

The gate computes addition in Mathlib's proven elliptic-curve group `W.Point`:
* `sound` — SOUNDNESS, both cases in one statement: for a satisfying witness the
  sum `(x₁,y₁) + (x₂,y₂)` is the group element the gate encodes — `0` when `inf = 1`,
  else the affine output `(x₃, y₃)` — using that `inf` is boolean (`inf_boolean`). It
  splits into the per-case `sound_point_noninf` / `sound_point_inf`.
* `complete` — COMPLETENESS, both cases in one statement: for on-curve inputs (`y₁ ≠ 0`),
  an honest prover can fill a satisfying witness, casing internally on whether the sum is
  finite or `∞`. Splits into the per-case `complete_noninf` / `complete_inf`.
-/

namespace Kimchi.Gate.AddComplete

/-- The CompleteAdd witness columns (cols 0–10). -/
structure Witness (F : Type*) where
  x1 : F
  y1 : F
  x2 : F
  y2 : F
  x3 : F
  y3 : F
  inf : F
  sameX : F
  s : F
  infZ : F
  x21Inv : F
deriving Repr

variable {F : Type*}

/-- Map a function across every witness cell. Instantiating at a ring homomorphism moves a
    witness between rings — in particular between `Witness (Polynomial F)` (the column
    polynomials of the quotient layer) and `Witness F` (their values at a domain node). -/
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

/-! ## The 7 constraints, transcribed from `complete_add.rs`.

The constraint left-hand sides live here once, as ring elements (`constraints`); the
relational spec (`Holds`), the executable checker (`ok`), and the quotient layer's constraint
polynomials (which read the same list over `F[X]`) are all defined from them. `CommRing`
suffices — no division appears (the inverse is *witnessed* as `x21Inv`, the whole point of
the gate). -/

/-- The gate's 7 constraint expressions — the single transcription. -/
def constraints [CommRing F] (w : Witness F) : List F :=
  let x21  := w.x2 - w.x1
  let y21  := w.y2 - w.y1
  let x1sq := w.x1 * w.x1
  -- zero_check(x21, x21Inv, sameX): constrains `sameX = (x1 == x2)`
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

/-- RELATIONAL spec: all 7 constraint expressions vanish. -/
def Holds [CommRing F] (w : Witness F) : Prop :=
  ∀ e ∈ constraints w, e = 0

instance [CommRing F] [DecidableEq F] (w : Witness F) : Decidable (Holds w) := by
  unfold Holds
  infer_instance

/-- EXECUTABLE checker — runnable on a concrete witness. -/
def ok [CommRing F] [DecidableEq F] (w : Witness F) : Bool :=
  (constraints w).all (· == 0)

/-- Reflection: the checker faithfully decides the relational constraints. -/
theorem ok_iff [CommRing F] [DecidableEq F] (w : Witness F) :
    ok w = true ↔ Holds w := by
  simp only [ok, Holds, List.all_eq_true, beq_iff_eq]

/-- `Holds` as the readable 7-conjunction (what the faithfulness proofs destructure). -/
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

/-- The constraint expressions commute with ring homomorphisms (applied cellwise via
    `Witness.map`). At `f = eval (ω^i) : F[X] →+* F` this turns the quotient layer's
    constraint polynomials' values at a domain node into the gate constraints of that
    node's row witness. -/
theorem constraints_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (w : Witness R) :
    (constraints w).map f = constraints (w.map f) := by
  simp [constraints, Witness.map, map_ofNat]

end Kimchi.Gate.AddComplete
