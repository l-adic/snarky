import Kimchi.Circuit
import Kimchi.Circuit.VarBaseMul

/-!
# End-to-end soundness for a chained `VarBaseMul` circuit

The `AddComplete` milestone (`Circuits/AddCompleteStep.lean`) reconstructs a single dumped
gate row and proves it computes a genuine EC addition. This file takes the next rung: a
*chain* of `m` `VarBaseMul` gates — each spanning a `VarBaseMul`/`Zero` row pair, wired so
that gate `i`'s output accumulator feeds gate `i+1`'s input accumulator (and its scalar
register threads likewise) — is reconstructed as a concrete `Circuit`, and we prove that any
satisfying witness certifies variable-base scalar multiplication `[n]·T` in Mathlib's group.

The composition rests on two already-proven bodies of work:
* `Kimchi.Gate.VarBaseMul` — one row's 21 constraints compute one 5-bit incomplete-addition
  chunk (`sound`);
* `Kimchi.Circuit.VarBaseMul` — the abstract `m`-gate fold `scalarMul_baseMul`, which
  consumes per-row `GateStep`s plus *threading hypotheses* (`hin`/`hout`/`hregIn`/`hregOut`).

The new ingredient is the **bridge**: the ingested circuit's `Checker.VarBaseMul.holds` row
predicate equals the algebraic `Gate.VarBaseMul.Holds` of the witness read off the row pair
(`ofRows`), and the circuit's copy constraints (`copyHolds`) *supply* the threading
hypotheses the abstract fold assumes. Everything below is field-generic; the Pasta
instantiation is layered on top exactly as in `Circuit/VarBaseMul.lean`.
-/

namespace Kimchi.Gate.VarBaseMul

open Kimchi.Gate (Row)

variable {F : Type*}

/-- Read a `VarBaseMul` witness off the physical `VarBaseMul`/`Zero` row pair the dump emits.

    Column layout (proof-systems `varbasemul.rs`; see `Checker.VarBaseMul`) — the Lean field
    order is *semantic* (all six accumulator points, then scalar, bits, slopes) and differs
    from the physical column order:

      VBSM row (`curr`): `0,1 = xT,yT`, `2,3 = x0,y0` (acc in), `4,5 = n,n'`,
                         `7,8 = x1,y1`, `9,10 = x2,y2`, `11,12 = x3,y3`, `13,14 = x4,y4`
      ZERO row (`next`): `0,1 = x5,y5` (acc out), `2..6 = b0..b4`, `7..11 = s0..s4`. -/
def ofRows [Zero F] (curr next : Row F) : Witness F :=
  { xT := curr.getD 0 0, yT := curr.getD 1 0
  , x0 := curr.getD 2 0, y0 := curr.getD 3 0
  , n  := curr.getD 4 0, nPrime := curr.getD 5 0
  , x1 := curr.getD 7 0, y1 := curr.getD 8 0
  , x2 := curr.getD 9 0, y2 := curr.getD 10 0
  , x3 := curr.getD 11 0, y3 := curr.getD 12 0
  , x4 := curr.getD 13 0, y4 := curr.getD 14 0
  , x5 := next.getD 0 0, y5 := next.getD 1 0
  , b0 := next.getD 2 0, b1 := next.getD 3 0, b2 := next.getD 4 0
  , b3 := next.getD 5 0, b4 := next.getD 6 0
  , s0 := next.getD 7 0, s1 := next.getD 8 0, s2 := next.getD 9 0
  , s3 := next.getD 10 0, s4 := next.getD 11 0 }

/-- One incomplete-addition step: the checker's `stepHolds` is the algebraic gate's
    `singleBitHolds` (same four cleared constraints — `t = 2·xin − s² + xb`, `u = 2·yin − t·s`
    — modulo `b·(b−1) = b·b − b`). -/
theorem step_bridge [CommRing F] (xb yb xin yin xout yout b s : F) :
    Checker.VarBaseMul.stepHolds xb yb xin yin xout yout b s
      ↔ singleBitHolds b xb yb s xin yin xout yout := by
  rw [singleBitHolds_iff, Checker.VarBaseMul.stepHolds]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
    exact ⟨by linear_combination h1, by linear_combination h2,
           by linear_combination h3, by linear_combination h4⟩

/-- **The bridge.** The ingested circuit's row predicate for a `VarBaseMul`/`Zero` pair is
    exactly the algebraic gate's `Holds` on the witness read off the pair. So the full
    `Kimchi.Gate.VarBaseMul` soundness suite applies to any dumped row that the checker
    accepts. -/
theorem checker_holds_iff [CommRing F] (curr next : Row F) :
    Checker.VarBaseMul.holds curr next ↔ Holds (ofRows curr next) := by
  rw [holds_iff, Checker.VarBaseMul.holds]
  simp only [step_bridge, decompHolds, decompCons, ofRows]

end Kimchi.Gate.VarBaseMul

namespace Kimchi.Circuit.VarBaseMul

open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

/-- Equal coordinates give the same affine point (the nonsingularity proofs are irrelevant). -/
private theorem some_congr {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)
    {x x' y y' : F} (h : W.Nonsingular x y) (h' : W.Nonsingular x' y')
    (hx : x = x') (hy : y = y') :
    Point.some _ _ h = Point.some _ _ h' := by subst hx; subst hy; rfl

/-- **The composition theorem — variable-base scalar multiplication from a threaded chain.**

    Given `m ≥ 1` `VarBaseMul` gate steps `g 0 … g (m-1)` (each an honest `GateStep`: its 21
    constraints hold and its six accumulator points/base are nonsingular, with the per-row
    non-degeneracies), wired into a chain by

    * `hacc` — gate `i`'s output accumulator `(x5,y5)` equals gate `i+1`'s input `(x0,y0)`,
    * `hreg` — gate `i`'s output register `n'` equals gate `i+1`'s input register `n`,
    * `hbase` — every gate shares the base point `T = (xT,yT)`,

    and initialized so the first input accumulator is `[a]·T` (`hinit`), the chain's final
    output accumulator is `[n]·T` for an explicit integer scalar `n` pinned by the scalar
    register `(g 0).n → (g (m-1)).n'`. This is `Circuit.VarBaseMul.scalarMul_baseMul` with the
    threading hypotheses discharged from the chain wiring instead of assumed pointwise — the
    reusable bridge from a circuit's copy constraints to the abstract fold. -/
theorem chain_sound
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (m : ℕ) (hm : 0 < m) (g : ℕ → Kimchi.Gate.VarBaseMul.Witness F)
    (gs : ∀ i, i < m → GateStep W (g i))
    (hacc : ∀ i (_ : i + 1 < m), (g i).x5 = (g (i + 1)).x0 ∧ (g i).y5 = (g (i + 1)).y0)
    (hreg : ∀ i (_ : i + 1 < m), (g i).nPrime = (g (i + 1)).n)
    (hbase : ∀ i (_ : i < m), (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (a : ℤ)
    (hinit : Point.some _ _ (gs 0 hm).a0 = a • Point.some _ _ (gs 0 hm).hT) :
    ∃ n : ℤ,
      Point.some _ _ (gs (m - 1) (by omega)).a5 = n • Point.some _ _ (gs 0 hm).hT
      ∧ (n : F) = (32 : F) ^ m * (a : F) + 2 * (g (m - 1)).nPrime
                   - 2 * (32 : F) ^ m * (g 0).n - ((32 : F) ^ m - 1)
      ∧ n.natAbs ≤ 32 ^ m * a.natAbs + (32 ^ m - 1) := by
  -- the shared base point
  set T : W.Point := Point.some _ _ (gs 0 hm).hT with hTdef
  -- the accumulator points threaded through the chain
  let P : ℕ → W.Point := fun i =>
    if h : i < m then Point.some _ _ (gs i h).a0
    else Point.some _ _ (gs (m - 1) (by omega)).a5
  -- the scalar-register values threaded through the chain
  let N : ℕ → F := fun i => if h : i < m then (g i).n else (g (m - 1)).nPrime
  have hT : ∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT := by
    intro i hi
    exact some_congr W _ _ (hbase i hi).1.symm (hbase i hi).2.symm
  have hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).a0 := by
    intro i hi; simp only [P, dif_pos hi]
  have hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).a5 := by
    intro i hi
    by_cases hnext : i + 1 < m
    · simp only [P, dif_pos hnext]
      exact (some_congr W _ _ (hacc i hnext).1 (hacc i hnext).2).symm
    · have him : i = m - 1 := by omega
      simp only [P, dif_neg hnext]
      subst him; rfl
  have hregIn : ∀ i, i < m → N i = (g i).n := by
    intro i hi; simp only [N, dif_pos hi]
  have hregOut : ∀ i, i < m → N (i + 1) = (g i).nPrime := by
    intro i hi
    by_cases hnext : i + 1 < m
    · simp only [N, dif_pos hnext]; exact (hreg i hnext).symm
    · have him : i = m - 1 := by omega
      simp only [N, dif_neg hnext]; subst him; rfl
  have hP0 : P 0 = a • T := by rw [hin 0 hm, hTdef]; exact hinit
  obtain ⟨n, hn, hnf, hnb⟩ :=
    scalarMul_baseMul W ha m g gs T N a P hT hin hout hregIn hregOut hP0
  have hNm : N m = (g (m - 1)).nPrime := by
    have h := hregOut (m - 1) (by omega); rwa [Nat.sub_add_cancel hm] at h
  refine ⟨n, ?_, ?_, ?_⟩
  · rw [← hout (m - 1) (by omega), show m - 1 + 1 = m by omega, hn]
  · rw [hnf, hNm, hregIn 0 hm]
  · exact hnb

end Kimchi.Circuit.VarBaseMul
