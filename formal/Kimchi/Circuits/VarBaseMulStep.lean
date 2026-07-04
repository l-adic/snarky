import Kimchi.Circuit
import Kimchi.Circuit.VarBaseMul
import Kimchi.Circuits.InitGrounding

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
    exact Point.some_congr _ _ (hbase i hi).1.symm (hbase i hi).2.symm
  have hin : ∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).a0 := by
    intro i hi; simp only [P, dif_pos hi]
  have hout : ∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).a5 := by
    intro i hi
    by_cases hnext : i + 1 < m
    · simp only [P, dif_pos hnext]
      exact (Point.some_congr _ _ (hacc i hnext).1 (hacc i hnext).2).symm
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

/-- Extract from `Satisfies (vbmCircuit m) w pub` the data the composition folds consume: each
    row's gate identity (`gatesHold` + `checker_holds_iff`) and the accumulator/register/base
    threading (`copyHolds`). Shared by `circuit_sound` and the Pasta specializations. -/
theorem satisfies_extract (m : ℕ) (w : Kimchi.Circuit.Witness F) (pub : Array F)
    (hsat : Satisfies (vbmCircuit m) w pub) :
    (∀ i, i < m → Holds (gwit w i))
    ∧ (∀ i, i < m → (gwit w i).xT = (gwit w 0).xT ∧ (gwit w i).yT = (gwit w 0).yT)
    ∧ (∀ i, i + 1 < m → (gwit w i).x5 = (gwit w (i + 1)).x0 ∧ (gwit w i).y5 = (gwit w (i + 1)).y0)
    ∧ (∀ i, i + 1 < m → (gwit w i).nPrime = (gwit w (i + 1)).n) := by
  obtain ⟨hgates, hcopy⟩ := hsat
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hnext => ?_, fun i hnext => ?_⟩
  · have hg := hgates (2 * i) (by rw [vbmCircuit_size]; omega)
    rw [gateAt_vbm m i hi] at hg
    have hck : Checker.VarBaseMul.holds (w.row (2 * i)) (w.row (2 * i + 1)) := hg
    exact (checker_holds_iff _ _).1 hck
  · rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; exact ⟨rfl, rfl⟩
    · have hc0 := hcopy (2 * i) (by rw [vbmCircuit_size]; omega) 0 (by omega)
      have hc1 := hcopy (2 * i) (by rw [vbmCircuit_size]; omega) 1 (by omega)
      rw [gateAt_vbm m i hi] at hc0 hc1
      simp only [vbmGate, vbmWires_get0 i (by omega), vbmWires_get1 i (by omega)] at hc0 hc1
      exact ⟨hc0, hc1⟩
  · have hc2 := hcopy (2 * (i + 1)) (by rw [vbmCircuit_size]; omega) 2 (by omega)
    have hc3 := hcopy (2 * (i + 1)) (by rw [vbmCircuit_size]; omega) 3 (by omega)
    rw [gateAt_vbm m (i + 1) (by omega)] at hc2 hc3
    simp only [vbmGate, vbmWires_get2 (i + 1) (by omega),
      vbmWires_get3 (i + 1) (by omega)] at hc2 hc3
    rw [show 2 * (i + 1) - 1 = 2 * i + 1 by omega] at hc2 hc3
    exact ⟨hc2.symm, hc3.symm⟩
  · have hc4 := hcopy (2 * (i + 1)) (by rw [vbmCircuit_size]; omega) 4 (by omega)
    rw [gateAt_vbm m (i + 1) (by omega)] at hc4
    simp only [vbmGate, vbmWires_get4 (i + 1) (by omega)] at hc4
    rw [show 2 * (i + 1) - 2 = 2 * i by omega] at hc4
    exact hc4.symm

/-- **End-to-end soundness for the reconstructed `VarBaseMul` chain.** Any witness satisfying
    `vbmCircuit m` — with the per-row curve preconditions `rc` and the initial accumulator pinned to
    `[a]·T` — certifies `[n]·T` for an explicit scalar `n`. The threading and the 21 per-row
    constraints are *derived* from `Satisfies` (via `satisfies_extract`); only the curve
    nonsingularity / non-degeneracy remain hypotheses, as in `AddCompleteStep`. -/
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
  obtain ⟨hHolds, hbase, hacc, hreg⟩ := satisfies_extract m w pub hsat
  exact chain_sound W ha m hm (gwit w)
    (fun i hi => (rc i hi).toGateStep (hHolds i hi)) hacc hreg hbase a hinit

/-! ## Pasta specializations

Routing `Satisfies` through the deployed Pasta roots `varBaseMul_scaleFast{1,2}` (which derive the
per-row `NonDegen` from the ladder toolkit and discharge the char/order side conditions by
computation) gives circuit soundness with **no curve non-degeneracy hypotheses** — only the base/
init nonsingularity (genuinely external) and the register range / forbidden-band bound. -/

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Kimchi.Pasta Kimchi.Shifted

/-- **Vesta / scaleFast1 (Type1).** From `Satisfies (vbmCircuit m) w pub` the reconstructed chain
    computes `[s]·T`; the per-row `NonDegen` is derived, not assumed. -/
theorem varBaseMul_circuit_scaleFast1
    (m : ℕ) (w : Kimchi.Circuit.Witness VestaBaseField) (pub : Array VestaBaseField)
    (hsat : Satisfies (vbmCircuit m) w pub)
    (T : Vesta.curve.toAffine.Point) (s : ℤ) (hTne : T ≠ 0)
    (hTns : Vesta.curve.toAffine.Nonsingular (gwit w 0).xT (gwit w 0).yT)
    (hTeq : T = Point.some _ _ hTns)
    (hP0ns : Vesta.curve.toAffine.Nonsingular (gwit w 0).x0 (gwit w 0).y0)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (hbits : 5 * m ≤ pastaFieldBits) (hs : s = gateLadder (gwit w) (5 * m))
    (hnf : 5 * m = pastaFieldBits → s ∉ forbiddenValues Vesta.curve.toAffine.order) :
    ∃ hfin : Vesta.curve.toAffine.Nonsingular (accX (gwit w) m) (accY (gwit w) m),
      Point.some _ _ hfin = s • T ∧ ∀ i, i < m → NonDegen (gwit w i) := by
  obtain ⟨hHolds, hbase, hacc, _⟩ := satisfies_extract m w pub hsat
  exact varBaseMul_scaleFast1 m (gwit w) T s hTne hHolds hTns hTeq hbase
    (fun i hi => ⟨(hacc i hi).1.symm, (hacc i hi).2.symm⟩) hP0ns hP0 hbits hs hnf

/-- **Pallas / scaleFast2 (Type2).** The parity-split entry point: from `Satisfies` (plus base/init
    and the register range-check `hsDiv2`) the chain computes `[n]·T` for the unshifted scalar,
    the register `N` threaded from `copyHolds`. -/
theorem varBaseMul_circuit_scaleFast2
    (m : ℕ) (hm : 0 < m) (w : Kimchi.Circuit.Witness PallasBaseField)
    (pub : Array PallasBaseField) (hsat : Satisfies (vbmCircuit m) w pub)
    (T : Pallas.curve.toAffine.Point) (hTne : T ≠ 0)
    (hTns : Pallas.curve.toAffine.Nonsingular (gwit w 0).xT (gwit w 0).yT)
    (hTeq : T = Point.some _ _ hTns)
    (hP0ns : Pallas.curve.toAffine.Nonsingular (gwit w 0).x0 (gwit w 0).y0)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (hN0 : (gwit w 0).n = 0)
    (hbits : 5 * m ≤ pastaFieldBits)
    (hsDiv2 : gateRegister (gwit w) (5 * m) < 2 ^ (pastaFieldBits - 1))
    (sOdd : PallasBaseField) (hsOdd : sOdd = 0 ∨ sOdd = 1) :
    ∃ (hfin : Pallas.curve.toAffine.Nonsingular (accX (gwit w) m) (accY (gwit w) m)) (n : ℤ),
      (n : PallasBaseField) = unshiftType2 (5 * m) (gwit w (m - 1)).nPrime sOdd
        ∧ ((sOdd = 1 ∧ Point.some _ _ hfin = n • T)
            ∨ (sOdd = 0 ∧ Point.some _ _ hfin - T = n • T)) := by
  obtain ⟨hHolds, hbase, hacc, hreg⟩ := satisfies_extract m w pub hsat
  set N : ℕ → PallasBaseField :=
    fun i => if _ : i < m then (gwit w i).n else (gwit w (m - 1)).nPrime with hNdef
  have hregIn : ∀ i, i < m → N i = (gwit w i).n := fun i hi => by simp only [N, dif_pos hi]
  have hregOut : ∀ i, i < m → N (i + 1) = (gwit w i).nPrime := by
    intro i hi
    by_cases hn : i + 1 < m
    · simp only [N, dif_pos hn]; exact (hreg i hn).symm
    · have him : i = m - 1 := by omega
      simp only [N, dif_neg hn]; subst him; rfl
  have hNinit : N 0 = 0 := by rw [hregIn 0 hm]; exact hN0
  have hNm : N m = (gwit w (m - 1)).nPrime := by
    have h := hregOut (m - 1) (by omega); rwa [Nat.sub_add_cancel hm] at h
  obtain ⟨hfin, n, hn, hcase⟩ := varBaseMul_scaleFast2 m hm (gwit w) T N hTne hHolds hTns hTeq hbase
    (fun i hi => ⟨(hacc i hi).1.symm, (hacc i hi).2.symm⟩) hP0ns hP0 hregIn hregOut hNinit
    hbits hsDiv2 sOdd hsOdd
  exact ⟨hfin, n, by rw [hn, hNm], hcase⟩

/-- **Scalar-field form (#6).** The `[s]·T` of `varBaseMul_circuit_scaleFast1` (Vesta), with the
    scalar reduced to its canonical representative in `[0, Vesta.order)` — an element of the Vesta
    scalar field `ZMod PALLAS_BASE_CARD = PallasBaseField` (the 2-cycle sister base field). -/
theorem varBaseMul_circuit_scaleFast1_scalar
    (m : ℕ) (w : Kimchi.Circuit.Witness VestaBaseField) (pub : Array VestaBaseField)
    (hsat : Satisfies (vbmCircuit m) w pub)
    (T : Vesta.curve.toAffine.Point) (s : ℤ) (hTne : T ≠ 0)
    (hTns : Vesta.curve.toAffine.Nonsingular (gwit w 0).xT (gwit w 0).yT)
    (hTeq : T = Point.some _ _ hTns)
    (hP0ns : Vesta.curve.toAffine.Nonsingular (gwit w 0).x0 (gwit w 0).y0)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (hbits : 5 * m ≤ pastaFieldBits) (hs : s = gateLadder (gwit w) (5 * m))
    (hnf : 5 * m = pastaFieldBits → s ∉ forbiddenValues Vesta.curve.toAffine.order) :
    ∃ (hfin : Vesta.curve.toAffine.Nonsingular (accX (gwit w) m) (accY (gwit w) m)) (k : ℤ),
      Point.some _ _ hfin = k • T ∧ 0 ≤ k ∧ k < (Vesta.curve.toAffine.order : ℤ) := by
  obtain ⟨hfin, hpt, _⟩ :=
    varBaseMul_circuit_scaleFast1 m w pub hsat T s hTne hTns hTeq hP0ns hP0 hbits hs hnf
  obtain ⟨k, hk, h0, hlt⟩ :=
    exists_canonical_scalar _ (Point.some _ _ hfin) T s (by rw [vesta_card]; decide) hpt
  exact ⟨hfin, k, hk, h0, hlt⟩

/-- **Init from a `CompleteAdd` doubling (#4 dataflow).** Composes
    `InitGrounding.completeAdd_doubles` with `varBaseMul_circuit_scaleFast1`: given the chain's
    `Satisfies` *and* a `CompleteAdd` row
    `dbl` fed the base twice (`x₁=x₂`, `y₁=y₂`) whose inputs are wired to gate 0's base
    (`hbaseX/Y`) and whose output is wired to gate 0's input accumulator (`houtX/Y`), the chain
    computes `[s]·T` — the init `P₀ = [2]·T` is *derived* from the doubling gate's proven
    `AddComplete` soundness (including its `inf = 0` flag: a doubling of a `y ≠ 0` point cannot
    land at infinity, `Point.add_self_ne_zero`). (`vbmCircuitGrounded_scaleFast1` below derives the
    four wiring equalities from `copyHolds`, exactly as `EndoScalar.esCircuitGrounded_sound` does
    for the constant-pinning case.) -/
theorem varBaseMul_scaleFast1_grounded
    (m : ℕ) (w : Kimchi.Circuit.Witness VestaBaseField) (pub : Array VestaBaseField)
    (hsat : Satisfies (vbmCircuit m) w pub)
    (T : Vesta.curve.toAffine.Point) (s : ℤ) (hTne : T ≠ 0)
    (hTns : Vesta.curve.toAffine.Nonsingular (gwit w 0).xT (gwit w 0).yT)
    (hTeq : T = Point.some _ _ hTns)
    (dbl : Kimchi.Gate.Row VestaBaseField)
    (hdblcons : Kimchi.Gate.AddComplete.Holds (Kimchi.Gate.AddComplete.ofRow dbl))
    (hx12 : (Kimchi.Gate.AddComplete.ofRow dbl).x1 = (Kimchi.Gate.AddComplete.ofRow dbl).x2)
    (hy12 : (Kimchi.Gate.AddComplete.ofRow dbl).y1 = (Kimchi.Gate.AddComplete.ofRow dbl).y2)
    (hbaseX : (Kimchi.Gate.AddComplete.ofRow dbl).x1 = (gwit w 0).xT)
    (hbaseY : (Kimchi.Gate.AddComplete.ofRow dbl).y1 = (gwit w 0).yT)
    (houtX : (Kimchi.Gate.AddComplete.ofRow dbl).x3 = (gwit w 0).x0)
    (houtY : (Kimchi.Gate.AddComplete.ofRow dbl).y3 = (gwit w 0).y0)
    (hbits : 5 * m ≤ pastaFieldBits) (hs : s = gateLadder (gwit w) (5 * m))
    (hnf : 5 * m = pastaFieldBits → s ∉ forbiddenValues Vesta.curve.toAffine.order) :
    ∃ hfin : Vesta.curve.toAffine.Nonsingular (accX (gwit w) m) (accY (gwit w) m),
      Point.some _ _ hfin = s • T ∧ ∀ i, i < m → NonDegen (gwit w i) := by
  have ha : Vesta.curve.toAffine.a₁ = 0 ∧ Vesta.curve.toAffine.a₂ = 0
      ∧ Vesta.curve.toAffine.a₃ = 0 ∧ Vesta.curve.toAffine.a₄ = 0 := ⟨rfl, rfl, rfl, rfl⟩
  -- the doubling's input point is `T`
  have hTca : Vesta.curve.toAffine.Nonsingular (Kimchi.Gate.AddComplete.ofRow dbl).x1
      (Kimchi.Gate.AddComplete.ofRow dbl).y1 := by rw [hbaseX, hbaseY]; exact hTns
  -- the base's y ≠ 0 is derived: an odd-order curve has no point on the x-axis
  have hy1 : (Kimchi.Gate.AddComplete.ofRow dbl).y1 ≠ 0 :=
    Point.y_ne_zero_of_odd_order rfl rfl vesta_order_odd hTca
  obtain ⟨h3, hdbl⟩ := Kimchi.Circuit.InitGrounding.completeAdd_doubles Vesta.curve.toAffine ha dbl
    hTca hx12 hy12 hdblcons hy1 (by decide)
  -- transport the produced output nonsingularity onto gate 0's input accumulator
  have hP0ns : Vesta.curve.toAffine.Nonsingular (gwit w 0).x0 (gwit w 0).y0 := by
    rw [← houtX, ← houtY]; exact h3
  have hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T := by
    rw [Point.some_congr hP0ns h3 houtX.symm houtY.symm, hdbl,
      Point.some_congr hTca hTns hbaseX hbaseY, ← hTeq]
  exact varBaseMul_circuit_scaleFast1 m w pub hsat T s hTne hTns hTeq hP0ns hP0 hbits hs hnf

/-! ## Fully grounded (Vesta): init reconstructed from a trailing `CompleteAdd` doubling row

`vbmCircuitGrounded m` appends a `CompleteAdd` row to `vbmCircuit m`, wired to double gate 0's base
into gate 0's input accumulator. Its soundness derives the four wiring equalities from `copyHolds`
(no longer hypotheses), feeding `varBaseMul_scaleFast1_grounded`. -/

/-- The trailing `CompleteAdd` doubling row: both inputs wired to gate 0's base `(0,0)/(0,1)`, its
    output wired to gate 0's input accumulator `(0,2)/(0,3)`; the `inf` column self-loops. -/
def caDoubleGate (m : ℕ) : Kimchi.Circuit.Gate F :=
  { kind := .completeAdd, coeffs := #[]
  , wires := #[(0, 0), (0, 1), (0, 0), (0, 1), (0, 2), (0, 3), (2 * m, 6)] }

/-- `vbmCircuit m` with a trailing `CompleteAdd` doubling row (at row `2m`). -/
def vbmCircuitGrounded (m : ℕ) : Kimchi.Circuit.Circuit F :=
  (vbmCircuit m).append #[caDoubleGate m]

omit [Field F] [DecidableEq F] in
@[simp] theorem vbmGrounded_size (m : ℕ) :
    (vbmCircuitGrounded m (F := F)).gates.size = 2 * m + 1 := by simp [vbmCircuitGrounded]

omit [Field F] [DecidableEq F] in
/-- The chain gate at `r < 2m` reconstructs the same in `vbmCircuitGrounded` as in `vbmCircuit`. -/
theorem gateAt_grounded_eq (m r : ℕ) (hr : r < 2 * m) :
    (vbmCircuitGrounded m (F := F)).gateAt r = (vbmCircuit m).gateAt r :=
  Circuit.gateAt_append_left _ _ r (by rw [vbmCircuit_size]; omega)

omit [Field F] [DecidableEq F] in
/-- The trailing row reconstructs to `caDoubleGate m`. -/
theorem gateAt_grounded_ca (m : ℕ) :
    (vbmCircuitGrounded m (F := F)).gateAt (2 * m) = caDoubleGate m := by
  have h := Circuit.gateAt_append_right (vbmCircuit m (F := F)) #[caDoubleGate m] 0 (by simp)
  simpa using h

/-- **Fully grounded VarBaseMul soundness (Vesta, #4 dataflow).** Any witness satisfying
    `vbmCircuitGrounded m` computes `[s]·T` — the init `P₀ = [2]·T` is *derived* from the trailing
    `CompleteAdd` doubling row, whose four wiring equalities are read off `copyHolds` and whose
    `inf = 0` flag is refuted-at-infinity rather than assumed, and `yT ≠ 0` is derived from the
    odd group order. The only remaining hypotheses are the base nonsingularity and the ladder
    bounds — the exact analogue of `EndoScalar.esCircuitGrounded_sound`. -/
theorem vbmCircuitGrounded_scaleFast1
    (m : ℕ) (w : Kimchi.Circuit.Witness VestaBaseField) (pub : Array VestaBaseField)
    (hsat : Satisfies (vbmCircuitGrounded m) w pub)
    (T : Vesta.curve.toAffine.Point) (s : ℤ) (hTne : T ≠ 0)
    (hTns : Vesta.curve.toAffine.Nonsingular (gwit w 0).xT (gwit w 0).yT)
    (hTeq : T = Point.some _ _ hTns)
    (hbits : 5 * m ≤ pastaFieldBits) (hs : s = gateLadder (gwit w) (5 * m))
    (hnf : 5 * m = pastaFieldBits → s ∉ forbiddenValues Vesta.curve.toAffine.order) :
    ∃ hfin : Vesta.curve.toAffine.Nonsingular (accX (gwit w) m) (accY (gwit w) m),
      Point.some _ _ hfin = s • T ∧ ∀ i, i < m → NonDegen (gwit w i) := by
  -- project the chain's `Satisfies` (the first `2m` gates are `vbmCircuit`'s, verbatim)
  have hchain : Satisfies (vbmCircuit m) w pub :=
    Satisfies.of_append (c := vbmCircuit m) (gs := #[caDoubleGate m]) hsat
  obtain ⟨hg, hc⟩ := hsat
  -- the doubling row's gate identity and its six copy constraints
  have hdblcons : Kimchi.Gate.AddComplete.Holds
      (Kimchi.Gate.AddComplete.ofRow (w.row (2 * m))) := by
    have hh := hg (2 * m) (by rw [vbmGrounded_size]; omega); rwa [gateAt_grounded_ca m] at hh
  have hc0 := hc (2 * m) (by rw [vbmGrounded_size]; omega) 0 (by omega)
  have hc1 := hc (2 * m) (by rw [vbmGrounded_size]; omega) 1 (by omega)
  have hc2 := hc (2 * m) (by rw [vbmGrounded_size]; omega) 2 (by omega)
  have hc3 := hc (2 * m) (by rw [vbmGrounded_size]; omega) 3 (by omega)
  have hc4 := hc (2 * m) (by rw [vbmGrounded_size]; omega) 4 (by omega)
  have hc5 := hc (2 * m) (by rw [vbmGrounded_size]; omega) 5 (by omega)
  rw [gateAt_grounded_ca m] at hc0 hc1 hc2 hc3 hc4 hc5
  simp only [caDoubleGate] at hc0 hc1 hc2 hc3 hc4 hc5
  -- name the wiring equalities in `AddComplete.ofRow` terms (defeq to the cells)
  have hbaseX : (Kimchi.Gate.AddComplete.ofRow (w.row (2 * m))).x1 = (gwit w 0).xT := hc0
  have hbaseY : (Kimchi.Gate.AddComplete.ofRow (w.row (2 * m))).y1 = (gwit w 0).yT := hc1
  have hx12 : (Kimchi.Gate.AddComplete.ofRow (w.row (2 * m))).x1
      = (Kimchi.Gate.AddComplete.ofRow (w.row (2 * m))).x2 := hc0.trans hc2.symm
  have hy12 : (Kimchi.Gate.AddComplete.ofRow (w.row (2 * m))).y1
      = (Kimchi.Gate.AddComplete.ofRow (w.row (2 * m))).y2 := hc1.trans hc3.symm
  have houtX : (Kimchi.Gate.AddComplete.ofRow (w.row (2 * m))).x3 = (gwit w 0).x0 := hc4
  have houtY : (Kimchi.Gate.AddComplete.ofRow (w.row (2 * m))).y3 = (gwit w 0).y0 := hc5
  exact varBaseMul_scaleFast1_grounded m w pub hchain T s hTne hTns hTeq (w.row (2 * m)) hdblcons
    hx12 hy12 hbaseX hbaseY houtX houtY hbits hs hnf

/-! ## A verifier sub-circuit: the IPA scale-and-combine term `p' = acc + [s]·T`

The atomic multi-scalar-multiplication term of the IPA opening check
(`addComplete acc (scaleFast1 g s)`, proof-systems `wrap_verifier`): a `VarBaseMul` chain computes
`[s]·T`, then a trailing `CompleteAdd` adds it to an accumulator point `acc`. This is the first
*verifier* operation assembled from the gate-composition proofs — genuine gate-output→gate-input
dataflow (the chain's output accumulator feeds the add's second input by a copy constraint), the
mirror of the init grounding above (there a `CompleteAdd` fed *into* the chain).

The soundness statement is the **full complete-add disjunction**: either the add's `inf` flag is
set and `acc + [s]·T = 0`, or the flag is clear and the output cells carry `acc + [s]·T` — no
branch is hypothesized away (unlike the doubling init, the vertical case is genuinely reachable
here: an adversarial `acc = -[s]·T` is legitimate input, and the gate must and does flag it). -/

/-- The trailing `CompleteAdd` combine row: input 1 `(x1,y1)` is the external accumulator `acc`
    (self-loops — supplied by hypothesis); input 2 `(x2,y2)` is wired to the chain's output
    accumulator (the last `Zero` row `2m−1`, cols 0/1); output and `inf` self-loop. -/
def caCombGate (m : ℕ) : Kimchi.Circuit.Gate F :=
  { kind := .completeAdd, coeffs := #[]
  , wires := #[(2 * m, 0), (2 * m, 1), (2 * m - 1, 0), (2 * m - 1, 1),
               (2 * m, 4), (2 * m, 5), (2 * m, 6)] }

/-- `vbmCircuit m` with a trailing `CompleteAdd` combine row (at row `2m`). -/
def scaleCombineCircuit (m : ℕ) : Kimchi.Circuit.Circuit F :=
  (vbmCircuit m).append #[caCombGate m]

omit [Field F] [DecidableEq F] in
@[simp] theorem scaleCombine_size (m : ℕ) :
    (scaleCombineCircuit m (F := F)).gates.size = 2 * m + 1 := by simp [scaleCombineCircuit]

omit [Field F] [DecidableEq F] in
theorem gateAt_sc_eq (m r : ℕ) (hr : r < 2 * m) :
    (scaleCombineCircuit m (F := F)).gateAt r = (vbmCircuit m).gateAt r :=
  Circuit.gateAt_append_left _ _ r (by rw [vbmCircuit_size]; omega)

omit [Field F] [DecidableEq F] in
theorem gateAt_sc_ca (m : ℕ) :
    (scaleCombineCircuit m (F := F)).gateAt (2 * m) = caCombGate m := by
  have h := Circuit.gateAt_append_right (vbmCircuit m (F := F)) #[caCombGate m] 0
    (by show 0 < 1; decide)
  rw [vbmCircuit_size] at h
  exact h

/-- **Scale-and-combine (an IPA MSM term), complete.** From `Satisfies (scaleCombineCircuit m)` the
    sub-circuit computes `p' = acc + [s]·T` with the full complete-add case split: the `VarBaseMul`
    chain gives `[s]·T` (`scaleFast1` on the projected chain `Satisfies`), its output feeds the
    trailing `CompleteAdd` by a `copyHolds`-derived wire, and `AddComplete.sound` yields either the
    flagged vertical case (`inf = 1`, `acc + [s]·T = 0`) or the affine sum in the output cells. -/
theorem scaleCombine_sound
    (m : ℕ) (hm : 0 < m) (w : Kimchi.Circuit.Witness VestaBaseField) (pub : Array VestaBaseField)
    (hsat : Satisfies (scaleCombineCircuit m) w pub)
    (T : Vesta.curve.toAffine.Point) (s : ℤ) (hTne : T ≠ 0)
    (hTns : Vesta.curve.toAffine.Nonsingular (gwit w 0).xT (gwit w 0).yT)
    (hTeq : T = Point.some _ _ hTns)
    (hP0ns : Vesta.curve.toAffine.Nonsingular (gwit w 0).x0 (gwit w 0).y0)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (hbits : 5 * m ≤ pastaFieldBits) (hs : s = gateLadder (gwit w) (5 * m))
    (hnf : 5 * m = pastaFieldBits → s ∉ forbiddenValues Vesta.curve.toAffine.order)
    (hacc : Vesta.curve.toAffine.Nonsingular
        (Kimchi.Gate.AddComplete.ofRow (w.row (2 * m))).x1
        (Kimchi.Gate.AddComplete.ofRow (w.row (2 * m))).y1) :
    ((Kimchi.Gate.AddComplete.ofRow (w.row (2 * m))).inf = 1
        ∧ Point.some _ _ hacc + s • T = 0)
    ∨ ((Kimchi.Gate.AddComplete.ofRow (w.row (2 * m))).inf = 0
        ∧ ∃ h3 : Vesta.curve.toAffine.Nonsingular
            (Kimchi.Gate.AddComplete.ofRow (w.row (2 * m))).x3
            (Kimchi.Gate.AddComplete.ofRow (w.row (2 * m))).y3,
          Point.some _ _ h3 = Point.some _ _ hacc + s • T) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have ha : Vesta.curve.toAffine.a₁ = 0 ∧ Vesta.curve.toAffine.a₂ = 0
      ∧ Vesta.curve.toAffine.a₃ = 0 ∧ Vesta.curve.toAffine.a₄ = 0 := ⟨rfl, rfl, rfl, rfl⟩
  -- the chain: [s]·T at the final accumulator
  have hchain : Satisfies (vbmCircuit (k + 1)) w pub :=
    Satisfies.of_append (c := vbmCircuit (k + 1)) (gs := #[caCombGate (k + 1)]) hsat
  obtain ⟨hg, hc⟩ := hsat
  obtain ⟨hfin, hptS, _⟩ :=
    varBaseMul_circuit_scaleFast1 (k + 1) w pub hchain T s hTne hTns hTeq hP0ns hP0 hbits hs hnf
  -- the combine row's gate identity and its chain-output wires
  have hcacons : Kimchi.Gate.AddComplete.Holds
      (Kimchi.Gate.AddComplete.ofRow (w.row (2 * (k + 1)))) := by
    have hh := hg (2 * (k + 1)) (by rw [scaleCombine_size]; omega)
    rwa [gateAt_sc_ca (k + 1)] at hh
  have hcc2 := hc (2 * (k + 1)) (by rw [scaleCombine_size]; omega) 2 (by omega)
  have hcc3 := hc (2 * (k + 1)) (by rw [scaleCombine_size]; omega) 3 (by omega)
  rw [gateAt_sc_ca (k + 1)] at hcc2 hcc3
  simp only [caCombGate] at hcc2 hcc3
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega] at hcc2 hcc3
  -- input 2 is the chain's output accumulator (defeq the ofRows cells)
  have hx2 : (Kimchi.Gate.AddComplete.ofRow (w.row (2 * (k + 1)))).x2
      = accX (gwit w) (k + 1) := hcc2
  have hy2 : (Kimchi.Gate.AddComplete.ofRow (w.row (2 * (k + 1)))).y2
      = accY (gwit w) (k + 1) := hcc3
  have h2 : Vesta.curve.toAffine.Nonsingular
      (Kimchi.Gate.AddComplete.ofRow (w.row (2 * (k + 1)))).x2
      (Kimchi.Gate.AddComplete.ofRow (w.row (2 * (k + 1)))).y2 := by
    rw [hx2, hy2]; exact hfin
  have heq2 : Point.some _ _ h2 = s • T := (Point.some_congr h2 hfin hx2 hy2).trans hptS
  -- the full complete-add case split (`acc`'s `y ≠ 0` derived from the odd group order)
  have hy1 : (Kimchi.Gate.AddComplete.ofRow (w.row (2 * (k + 1)))).y1 ≠ 0 :=
    Point.y_ne_zero_of_odd_order rfl rfl vesta_order_odd hacc
  rcases Kimchi.Gate.AddComplete.sound Vesta.curve.toAffine ha
      (Kimchi.Gate.AddComplete.ofRow (w.row (2 * (k + 1)))) hacc h2 hcacons hy1 (by decide) with
    ⟨hinf, hsum⟩ | ⟨hinf, h3, hsum⟩
  · exact Or.inl ⟨hinf, by rw [← heq2]; exact hsum⟩
  · exact Or.inr ⟨hinf, h3, by rw [← heq2]; exact hsum.symm⟩

end Kimchi.Circuit.VarBaseMul
