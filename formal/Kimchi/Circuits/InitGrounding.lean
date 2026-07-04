import Kimchi.Circuit
import Kimchi.Curve

/-!
# Grounding the chain's initial state (#4)

The `Circuits/*Step.lean` composition theorems take the chain's **initial state** as a hypothesis
(`ha0/hb0/hn0`, `hinit`, `hP0`). In the real dumped circuits that state is produced by *setup rows*
preceding the chain, and their gate + copy constraints pin it. This file proves the two techniques
by which setup rows source an init — the substance of #4 — as standalone, reusable lemmas; each
composes with the respective `circuit_sound` by feeding its conclusion in for the assumed init.

* **Constant-pinning** (`EndoMulScalar`'s `(a₀,b₀,n₀) = (2,2,0)`): a `Generic` setup row asserts a
  cell equals a constant and its copy constraint carries that into the first chain row's input cell.
* **Gate dataflow** (`VarBaseMul`'s `P₀ = [2]·T`): a preceding `CompleteAdd` row *doubles* the base;
  its already-proven `AddComplete` soundness gives `output = 2·T`, and a copy constraint threads it
  into the first chain gate's input accumulator. This is the first place two proven gates compose by
  *data flow* rather than mere co-satisfaction.

(The `EndoMulScalar` model here uses one `Generic` row per pinned constant — an idealization of the
real dump, which packs two into a single double-`Generic` row; the technique is identical.)
-/

namespace Kimchi.Circuit.InitGrounding

open Kimchi.Circuit (Gate Circuit Witness Satisfies)

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Constant-pinning (the `EndoMulScalar` init) -/

/-- A `Generic` setup row asserting `w[·][0] = c` (coeffs `[1,0,0,0,−c]`, no public input) and
    copying that value into `target` via its column-0 wire. -/
def genPin (c : F) (target : Nat × Nat) : Gate F :=
  { kind := .generic, coeffs := #[1, 0, 0, 0, -c], wires := #[target] }

omit [DecidableEq F] in
/-- `genPin`'s generic evaluation is `w[·][0] − c`. -/
theorem genPin_eval (c : F) (row : Kimchi.Gate.Row F) :
    Kimchi.Checker.Generic.eval (#[1, 0, 0, 0, -c] : Array F) row = row.getD 0 0 - c := by
  show (1 : F) * row.getD 0 0 + 0 * row.getD 1 0 + 0 * row.getD 2 0
        + 0 * (row.getD 0 0 * row.getD 1 0) + -c = row.getD 0 0 - c
  ring

/-- The three-row `EndoMulScalar` setup: pins `n₀ = 0`, `a₀ = 2`, `b₀ = 2` into the chain's first
    row `t` (its cols 0/2/3). -/
def esSetupCircuit (t : Nat) : Circuit F :=
  { publicInputSize := 0
  , gates := #[genPin 0 (t, 0), genPin 2 (t, 2), genPin 2 (t, 3)] }

/-- **Constant-pinning soundness.** Any witness satisfying `esSetupCircuit t` has the canonical
    `EndoMulScalar` init `(n₀,a₀,b₀) = (0,2,2)` at row `t` — so feeding this into
    `EndoScalar.circuit_sound` (at the shifted witness) discharges its `ha0/hb0/hn0`. -/
theorem esSetup_pins_init (t : Nat) (w : Witness F) (pub : Array F)
    (hsat : Satisfies (esSetupCircuit t) w pub) :
    (w.row t).getD 0 0 = 0 ∧ (w.row t).getD 2 0 = 2 ∧ (w.row t).getD 3 0 = 2 := by
  obtain ⟨hg, hc⟩ := hsat
  -- each setup row `r` forces `w[r][0] = c`, and its copy carries that into `(t, col)`.
  have pin : ∀ (r : Nat) (c : F) (col : Nat),
      (esSetupCircuit t (F := F)).gateAt r = genPin c (t, col) → r < 3 →
      (w.row t).getD col 0 = c := by
    intro r c col hgate hr
    have hgr := hg r (by rw [show (esSetupCircuit t (F := F)).gates.size = 3 from rfl]; omega)
    have hcr := hc r (by rw [show (esSetupCircuit t (F := F)).gates.size = 3 from rfl]; omega)
        0 (by omega)
    rw [hgate] at hgr hcr
    -- gate: `eval = pubTerm = 0` ⇒ `w[r][0] = c`
    have hval : (w.row r).getD 0 0 = c := by
      have : Kimchi.Checker.Generic.eval (#[1, 0, 0, 0, -c] : Array F) (w.row r)
          = (esSetupCircuit t (F := F)).pubTerm pub r := hgr.1
      rw [genPin_eval, show (esSetupCircuit t (F := F)).pubTerm pub r = 0 from rfl] at this
      exact sub_eq_zero.mp this
    -- copy: `w[r][0] = w[t][col]`, i.e. `(t,col)` holds `c`
    have hcopy : w.cell (r, 0) = w.cell (t, col) := hcr
    show w.cell (t, col) = c
    rw [← hcopy]; exact hval
  exact ⟨pin 0 0 0 rfl (by omega), pin 1 2 2 rfl (by omega), pin 2 2 3 rfl (by omega)⟩

/-! ## Gate dataflow (the `VarBaseMul` `[2]·T` init) -/

open WeierstrassCurve.Affine Kimchi.Gate

/-- **CompleteAdd doubles.** A satisfying `CompleteAdd` row whose two inputs are the *same* point
    `T` (`x₁ = x₂`, `y₁ = y₂` — the base fed in twice) computes `output = [2]·T` in the group. Its
    output cells then feed the first `VarBaseMul` gate's input accumulator by a copy constraint,
    discharging that chain's `hinit : P₀ = [2]·T`.

    No `inf` hypothesis: the full `AddComplete.sound` disjunction is used, and the infinity branch
    is *refuted* — a doubling of a `y ≠ 0` point cannot land at infinity
    (`Point.add_self_ne_zero`). -/
theorem completeAdd_doubles (W : WeierstrassCurve.Affine F)
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0 ∧ W.a₄ = 0) (row : Row F)
    (hT : W.Nonsingular (AddComplete.ofRow row).x1 (AddComplete.ofRow row).y1)
    (hx : (AddComplete.ofRow row).x1 = (AddComplete.ofRow row).x2)
    (hy : (AddComplete.ofRow row).y1 = (AddComplete.ofRow row).y2)
    (hcons : AddComplete.Holds (AddComplete.ofRow row))
    (hy1 : (AddComplete.ofRow row).y1 ≠ 0) (htwo : (2 : F) ≠ 0) :
    ∃ h3 : W.Nonsingular (AddComplete.ofRow row).x3 (AddComplete.ofRow row).y3,
      Point.some _ _ h3 = (2 : ℤ) • Point.some _ _ hT := by
  have h2 : W.Nonsingular (AddComplete.ofRow row).x2 (AddComplete.ofRow row).y2 := hx ▸ hy ▸ hT
  have heq : Point.some _ _ h2 = Point.some _ _ hT := Point.some_congr h2 hT hx.symm hy.symm
  rcases AddComplete.sound W ha (AddComplete.ofRow row) hT h2 hcons hy1 htwo with
    ⟨_, hsum⟩ | ⟨_, h3, hsum⟩
  · -- infinity branch: `T + T = 0` contradicts `y ≠ 0` (no affine 2-torsion off the x-axis)
    rw [heq] at hsum
    exact absurd hsum (Point.add_self_ne_zero W ha.1 ha.2.2.1 hT hy1 htwo)
  · exact ⟨h3, by rw [← hsum, heq, two_zsmul]⟩

end Kimchi.Circuit.InitGrounding
