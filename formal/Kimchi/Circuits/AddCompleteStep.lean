import Kimchi.Circuit

/-!
# End-to-end soundness for the `add_complete_step_circuit`

This is the milestone: the dumped circuit `add_complete_step_circuit` — 6 `Generic`
public-input rows feeding one `CompleteAdd` row — is reconstructed as a concrete
`Circuit`, and we prove that **any** witness satisfying it certifies a genuine
elliptic-curve addition of the public inputs.

The proof threads the three obligations of `Satisfies`:
* the `Generic` public rows give `w[k][0] = pub[k]` (public-input term folded in);
* the `CompleteAdd` row's copy constraints carry those into its cells 0–5
  (`x1,y1,x2,y2,x3,y3`) — *the one place the permutation is load-bearing*;
* the `CompleteAdd` gate identity is the already-proven `AddComplete.Holds`, so
  `AddComplete.sound_point` finishes the job.

No new gate polynomials are needed: this rests entirely on the proven `AddComplete`
suite plus the copy/public-input plumbing in `Kimchi.Circuit`.
-/

namespace Kimchi.Circuit

open Kimchi.Gate

variable {F : Type*} [Field F] [DecidableEq F]

/-- A public-input `Generic` row: `cl = 1` reading register 0, with col 0 wired to the
    `CompleteAdd` row's column `k`. (Coeffs `[1,0,0,0,0]` = the dump's copy row.) -/
def genPub (k : Nat) : Gate F :=
  { kind := .generic
  , coeffs := #[1, 0, 0, 0, 0]
  , wires := #[(6, k), (k, 1), (k, 2), (k, 3), (k, 4), (k, 5), (k, 6)] }

/-- The `add_complete_step_circuit`: 6 public-input `Generic` rows then one `CompleteAdd`
    row whose cols 0–5 wire back to each public row's register 0. -/
def addCompleteCircuit : Circuit F :=
  { publicInputSize := 6
  , gates := #[ genPub 0, genPub 1, genPub 2, genPub 3, genPub 4, genPub 5
              , { kind := .completeAdd, coeffs := #[]
                , wires := #[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 6)] } ] }

omit [DecidableEq F] in
/-- A `Generic` row with coeffs `[1,0,0,0,0]` evaluates to register 0. -/
theorem genEval (row : Row F) :
    Generic.eval (#[1, 0, 0, 0, 0] : Array F) row = row.getD 0 0 := by
  show (1 : F) * row.getD 0 0 + 0 * row.getD 1 0 + 0 * row.getD 2 0
        + 0 * (row.getD 0 0 * row.getD 1 0) + 0 = row.getD 0 0
  ring

/-- SOUNDNESS of the whole circuit. For any witness satisfying `addCompleteCircuit` on
    public inputs `pub = (x1,y1,x2,y2,x3,y3)` with `(x1,y1)`, `(x2,y2)` nonsingular points
    of a Pasta-shape curve (`y1 ≠ 0`, `2 ≠ 0`):

    * **the public inputs are exactly the CompleteAdd row's input cells** (`w[6][k] = pub[k]`
      — carried there by the copy constraints), and
    * **the gate computes their group sum**: either the `inf` flag is set and
      `(x1,y1) + (x2,y2) = 0`, or `(x3,y3)` is that sum.

    The nonsingularity proofs for the row-6 cells are existentially bound and reused, so the
    conclusion matches `AddComplete.sound_point` definitionally (no coordinate transport). -/
theorem addComplete_sound
    (W : WeierstrassCurve.Affine F) (ha : IsShortShape W)
    (w : Witness F) (pub : Array F)
    (h1 : W.Nonsingular (pub.getD 0 0) (pub.getD 1 0))
    (h2 : W.Nonsingular (pub.getD 2 0) (pub.getD 3 0))
    (hy1 : pub.getD 1 0 ≠ 0) (htwo : (2 : F) ≠ 0)
    (hsat : Satisfies addCompleteCircuit w pub) :
    (∀ k, k < 6 → w.cell (6, k) = pub.getD k 0)
    ∧ ∃ (H1 : W.Nonsingular (w.cell (6, 0)) (w.cell (6, 1)))
        (H2 : W.Nonsingular (w.cell (6, 2)) (w.cell (6, 3))),
        (w.cell (6, 6) = 1 ∧
            WeierstrassCurve.Affine.Point.some _ _ H1
              + WeierstrassCurve.Affine.Point.some _ _ H2 = 0)
        ∨ (w.cell (6, 6) = 0 ∧
            ∃ h3 : W.Nonsingular (w.cell (6, 4)) (w.cell (6, 5)),
              WeierstrassCurve.Affine.Point.some _ _ H1 + WeierstrassCurve.Affine.Point.some _ _ H2
                = WeierstrassCurve.Affine.Point.some _ _ h3) := by
  obtain ⟨hgates, hcopy⟩ := hsat
  have hsz : (addCompleteCircuit (F := F)).gates.size = 7 := rfl
  -- the `CompleteAdd` row's wire for col k points to (k, 0)
  have wireEq : ∀ k, k < 6 →
      ((addCompleteCircuit (F := F)).gateAt 6).wires.getD k (6, k) = (k, 0) := by
    intro k hk; interval_cases k <;> rfl
  -- the row-k gate is the public `Generic` gate
  have gateEq : ∀ k, k < 6 → (addCompleteCircuit (F := F)).gateAt k = genPub k := by
    intro k hk; interval_cases k <;> rfl
  -- each public coordinate lands in the CompleteAdd row's col k
  have key : ∀ k, k < 6 → w.cell (6, k) = pub.getD k 0 := by
    intro k hk
    have hc := hcopy 6 (by rw [hsz]; omega) k (by omega)
    rw [wireEq k hk] at hc
    have hg := hgates k (by rw [hsz]; omega)
    rw [gateEq k hk] at hg
    change Generic.eval (#[1, 0, 0, 0, 0] : Array F) (w.row k)
        = (addCompleteCircuit (F := F)).pubTerm pub k at hg
    rw [genEval] at hg
    have hpt : (addCompleteCircuit (F := F)).pubTerm pub k = pub.getD k 0 := by
      simp only [Circuit.pubTerm, addCompleteCircuit]; exact if_pos hk
    rw [hpt] at hg
    rw [hc]; exact hg
  -- the CompleteAdd gate identity holds at row 6
  have hH : AddComplete.Holds (AddComplete.ofRow (w.row 6)) := hgates 6 (by rw [hsz]; omega)
  refine ⟨key, ?_⟩
  -- transfer the input nonsingularity onto the row-6 cells via the bridge equalities
  have H1 : W.Nonsingular (w.cell (6, 0)) (w.cell (6, 1)) :=
    (key 1 (by omega)).symm ▸ (key 0 (by omega)).symm ▸ h1
  have H2 : W.Nonsingular (w.cell (6, 2)) (w.cell (6, 3)) :=
    (key 3 (by omega)).symm ▸ (key 2 (by omega)).symm ▸ h2
  have hy1' : w.cell (6, 1) ≠ 0 := (key 1 (by omega)).symm ▸ hy1
  -- the proven CompleteAdd soundness gives exactly the disjunction we want
  exact ⟨H1, H2,
    AddComplete.sound_point W ha (AddComplete.ofRow (w.row 6)) H1 H2 hH hy1' htwo⟩

end Kimchi.Circuit
