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

The development proceeds in two rungs:
* `chain_sound` — the **abstract** composition: given per-row `GateStep`s and the threading
  as *hypotheses*, the chain computes `[n]·T`. The bridge `checker_holds_iff` is what lets a
  dumped, checker-accepted row supply a `GateStep.holds`.
* `circuit_sound` — the **gold standard** (matching `AddCompleteStep`): reconstruct the actual
  parametric `m`-gate circuit `vbmCircuit m` and *derive* both the threading and the 21 per-row
  constraints from its `Satisfies` relation — `copyHolds` supplies the wiring (`hacc`/`hreg`/
  `hbase`), `gatesHold` + `checker_holds_iff` supply each `Holds`. Only the curve-level
  nonsingularity / non-degeneracy remain hypotheses (bundled as `RowCurve`), exactly as
  `AddCompleteStep` keeps input nonsingularity as a hypothesis while deriving the gate identity.

Everything below is field-generic; the Pasta instantiation is layered on top exactly as in
`Circuit/VarBaseMul.lean`.
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

/-! ## Grounding the chain in a reconstructed `Circuit`

`chain_sound` above still *assumes* the threading (`hacc`/`hreg`/`hbase`) and each row's gate
identity (bundled in `GateStep.holds`). The gold standard set by `AddCompleteStep` is stronger:
reconstruct the *actual* ingested `Circuit` and derive both the wiring **and** the gate identities
from its `Satisfies` relation, leaving only the curve-level nonsingularity / non-degeneracy as
hypotheses (there the input points being on the curve; here the analogous per-row `RowCurve`). The
development below builds the parametric `m`-gate `VarBaseMul` circuit and closes that gap. -/

open Kimchi.Circuit (Cell Satisfies gatesHold copyHolds)

/-- `Array.ofFn` lookup below its length: the workhorse for reducing `gateAt`/`wires` on the
    parametric circuit's `Array.ofFn` gate list. -/
private theorem getD_ofFn_lt {α} (n : ℕ) (f : Fin n → α) (r : ℕ) (d : α) (h : r < n) :
    (Array.ofFn f).getD r d = f ⟨r, h⟩ := by
  rw [Array.getD, dif_pos (by simpa using h)]; simp [Array.getElem_ofFn]

/-- The curve-level per-row preconditions: this is `GateStep` **minus** the gate identity `Holds`
    (the six accumulator points and base are nonsingular; the ten `NonDegen` side conditions hold).
    `circuit_sound` derives `Holds` from the reconstructed circuit's `Satisfies` and assembles the
    full `GateStep` via `RowCurve.toGateStep` — mirroring how `AddCompleteStep` keeps input
    nonsingularity as a hypothesis while deriving the gate identity from `gatesHold`. -/
structure RowCurve (W : WeierstrassCurve.Affine F)
    (g : Kimchi.Gate.VarBaseMul.Witness F) : Prop where
  a0 : W.Nonsingular g.x0 g.y0
  a1 : W.Nonsingular g.x1 g.y1
  a2 : W.Nonsingular g.x2 g.y2
  a3 : W.Nonsingular g.x3 g.y3
  a4 : W.Nonsingular g.x4 g.y4
  a5 : W.Nonsingular g.x5 g.y5
  hT : W.Nonsingular g.xT g.yT
  x0 : g.x0 ≠ g.xT
  x1 : g.x1 ≠ g.xT
  x2 : g.x2 ≠ g.xT
  x3 : g.x3 ≠ g.xT
  x4 : g.x4 ≠ g.xT
  t0 : 2 * g.x0 + g.xT - g.s0 * g.s0 ≠ 0
  t1 : 2 * g.x1 + g.xT - g.s1 * g.s1 ≠ 0
  t2 : 2 * g.x2 + g.xT - g.s2 * g.s2 ≠ 0
  t3 : 2 * g.x3 + g.xT - g.s3 * g.s3 ≠ 0
  t4 : 2 * g.x4 + g.xT - g.s4 * g.s4 ≠ 0

/-- Combine the curve preconditions with a derived gate identity into a full `GateStep`. -/
def RowCurve.toGateStep {W : WeierstrassCurve.Affine F} {g : Kimchi.Gate.VarBaseMul.Witness F}
    (rc : RowCurve W g) (h : Holds g) : GateStep W g :=
  { a0 := rc.a0, a1 := rc.a1, a2 := rc.a2, a3 := rc.a3, a4 := rc.a4, a5 := rc.a5, hT := rc.hT
  , holds := h
  , x0 := rc.x0, x1 := rc.x1, x2 := rc.x2, x3 := rc.x3, x4 := rc.x4
  , t0 := rc.t0, t1 := rc.t1, t2 := rc.t2, t3 := rc.t3, t4 := rc.t4 }

/-- Copy wiring for gate `i`'s `VarBaseMul` row (`2·i`). Cols 0–1 wire the base to gate 0
    (shared `T`); for `i ≥ 1`, col 2–3 wire the input accumulator `(x0,y0)` to the previous gate's
    output `(x5,y5)` (the `Zero` row `2i−1`, cols 0–1), and col 4 wires the input register `n` to
    the previous gate's `n'` (the `VarBaseMul` row `2i−2`, col 5). Gate 0's row is all self-loops:
    its init is supplied by `hinit`, not by a copy constraint. -/
def vbmWires (i : ℕ) : Array Cell :=
  if i = 0 then #[(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)]
  else #[(0, 0), (0, 1), (2 * i - 1, 0), (2 * i - 1, 1), (2 * i - 2, 5), (2 * i, 5), (2 * i, 6)]

/-- Gate `i`'s `VarBaseMul` row (with the threading wires); the following `Zero` row carries no
    outgoing copies. -/
def vbmGate (i : ℕ) : Kimchi.Circuit.Gate F :=
  { kind := .varBaseMul, coeffs := #[], wires := vbmWires i }

/-- The all-`zero` companion row of each gate pair. -/
def vbmZero : Kimchi.Circuit.Gate F := { kind := .zero, coeffs := #[], wires := #[] }

/-- The reconstructed `m`-gate `VarBaseMul` circuit: `m` interleaved `VarBaseMul`/`Zero` row pairs
    (gate `i` at rows `2i`, `2i+1`), threaded by `vbmWires`. No public inputs — the chain's initial
    accumulator is pinned by `hinit`, exactly as `chain_sound` takes it. -/
def vbmCircuit (m : ℕ) : Kimchi.Circuit.Circuit F :=
  { publicInputSize := 0
  , gates := Array.ofFn (n := 2 * m) fun idx =>
      if idx.val % 2 = 0 then vbmGate (idx.val / 2) else vbmZero }

omit [Field F] [DecidableEq F] in
@[simp] theorem vbmCircuit_size (m : ℕ) : (vbmCircuit m (F := F)).gates.size = 2 * m := by
  simp [vbmCircuit]

omit [Field F] [DecidableEq F] in
/-- The `VarBaseMul` row of gate `i` reconstructs to `vbmGate i`. -/
theorem gateAt_vbm (m i : ℕ) (hi : i < m) :
    (vbmCircuit m (F := F)).gateAt (2 * i) = vbmGate i := by
  rw [Circuit.gateAt, vbmCircuit, getD_ofFn_lt _ _ _ _ (show 2 * i < 2 * m by omega)]
  show (if 2 * i % 2 = 0 then vbmGate (2 * i / 2) else vbmZero) = vbmGate i
  rw [if_pos (by omega), show 2 * i / 2 = i by omega]

/-- Wire lookups for a threading row (`i ≠ 0`): base to gate 0, accumulator/register to the
    previous gate. Each reduces the explicit `vbmWires` array literal. -/
theorem vbmWires_get0 (i : ℕ) (hi : i ≠ 0) (d : Cell) : (vbmWires i).getD 0 d = (0, 0) := by
  simp [vbmWires, hi]
theorem vbmWires_get1 (i : ℕ) (hi : i ≠ 0) (d : Cell) : (vbmWires i).getD 1 d = (0, 1) := by
  simp [vbmWires, hi]
theorem vbmWires_get2 (i : ℕ) (hi : i ≠ 0) (d : Cell) :
    (vbmWires i).getD 2 d = (2 * i - 1, 0) := by simp [vbmWires, hi]
theorem vbmWires_get3 (i : ℕ) (hi : i ≠ 0) (d : Cell) :
    (vbmWires i).getD 3 d = (2 * i - 1, 1) := by simp [vbmWires, hi]
theorem vbmWires_get4 (i : ℕ) (hi : i ≠ 0) (d : Cell) :
    (vbmWires i).getD 4 d = (2 * i - 2, 5) := by simp [vbmWires, hi]

/-- The witness read off gate `i`'s physical row pair. -/
private def gwit (w : Kimchi.Circuit.Witness F) (i : ℕ) : Kimchi.Gate.VarBaseMul.Witness F :=
  ofRows (w.row (2 * i)) (w.row (2 * i + 1))

/-- **End-to-end soundness for the reconstructed `VarBaseMul` chain.** Any witness satisfying
    `vbmCircuit m` — with the per-row curve preconditions `rc` and the initial accumulator pinned to
    `[a]·T` — certifies `[n]·T` for an explicit scalar `n`. Unlike `chain_sound`, the threading and
    the 21 per-row constraints are *derived* from `Satisfies` (`copyHolds` supplies the wiring,
    `gatesHold` + `checker_holds_iff` supply each `Holds`); only the curve nonsingularity /
    non-degeneracy remain hypotheses, as in `AddCompleteStep`. -/
theorem circuit_sound
    (W : WeierstrassCurve.Affine F) (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (m : ℕ) (hm : 0 < m) (w : Kimchi.Circuit.Witness F) (pub : Array F)
    (hsat : Satisfies (vbmCircuit m) w pub)
    (rc : ∀ i, i < m → RowCurve W (gwit w i))
    (a : ℤ)
    (hinit : Point.some _ _ (rc 0 hm).a0 = a • Point.some _ _ (rc 0 hm).hT) :
    ∃ n : ℤ,
      Point.some _ _ (rc (m - 1) (by omega)).a5 = n • Point.some _ _ (rc 0 hm).hT
      ∧ (n : F) = (32 : F) ^ m * (a : F) + 2 * (gwit w (m - 1)).nPrime
                   - 2 * (32 : F) ^ m * (gwit w 0).n - ((32 : F) ^ m - 1)
      ∧ n.natAbs ≤ 32 ^ m * a.natAbs + (32 ^ m - 1) := by
  obtain ⟨hgates, hcopy⟩ := hsat
  -- gate identity of each row, read from `gatesHold` through the checker bridge
  have hHolds : ∀ i (hi : i < m), Holds (gwit w i) := by
    intro i hi
    have hg := hgates (2 * i) (by rw [vbmCircuit_size]; omega)
    rw [gateAt_vbm m i hi] at hg
    have : Checker.VarBaseMul.holds (w.row (2 * i)) (w.row (2 * i + 1)) := hg
    exact (checker_holds_iff _ _).1 this
  -- assemble the per-row `GateStep` from the curve preconditions and the derived identity
  have gs : ∀ i (hi : i < m), GateStep W (gwit w i) :=
    fun i hi => (rc i hi).toGateStep (hHolds i hi)
  -- the threading, from `copyHolds` (`w.cell (r,c)` is defeq the matching `ofRows` projection)
  have hacc : ∀ i (_ : i + 1 < m),
      (gwit w i).x5 = (gwit w (i + 1)).x0 ∧ (gwit w i).y5 = (gwit w (i + 1)).y0 := by
    intro i hnext
    have hc2 := hcopy (2 * (i + 1)) (by rw [vbmCircuit_size]; omega) 2 (by omega)
    have hc3 := hcopy (2 * (i + 1)) (by rw [vbmCircuit_size]; omega) 3 (by omega)
    rw [gateAt_vbm m (i + 1) (by omega)] at hc2 hc3
    simp only [vbmGate, vbmWires_get2 (i + 1) (by omega),
      vbmWires_get3 (i + 1) (by omega)] at hc2 hc3
    rw [show 2 * (i + 1) - 1 = 2 * i + 1 by omega] at hc2 hc3
    exact ⟨hc2.symm, hc3.symm⟩
  have hreg : ∀ i (_ : i + 1 < m), (gwit w i).nPrime = (gwit w (i + 1)).n := by
    intro i hnext
    have hc4 := hcopy (2 * (i + 1)) (by rw [vbmCircuit_size]; omega) 4 (by omega)
    rw [gateAt_vbm m (i + 1) (by omega)] at hc4
    simp only [vbmGate, vbmWires_get4 (i + 1) (by omega)] at hc4
    rw [show 2 * (i + 1) - 2 = 2 * i by omega] at hc4
    exact hc4.symm
  have hbase : ∀ i (_ : i < m), (gwit w i).xT = (gwit w 0).xT ∧ (gwit w i).yT = (gwit w 0).yT := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; exact ⟨rfl, rfl⟩
    · have hc0 := hcopy (2 * i) (by rw [vbmCircuit_size]; omega) 0 (by omega)
      have hc1 := hcopy (2 * i) (by rw [vbmCircuit_size]; omega) 1 (by omega)
      rw [gateAt_vbm m i hi] at hc0 hc1
      simp only [vbmGate, vbmWires_get0 i (by omega), vbmWires_get1 i (by omega)] at hc0 hc1
      exact ⟨hc0, hc1⟩
  exact chain_sound W ha m hm (gwit w) gs hacc hreg hbase a hinit

end Kimchi.Circuit.VarBaseMul
