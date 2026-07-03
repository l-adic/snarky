import Kimchi.Circuit
import Kimchi.Circuit.EndoScalar
import Kimchi.Pasta

/-!
# End-to-end soundness for a chained `EndoMulScalar` circuit

The gold-standard companion to `Circuits/VarBaseMulStep.lean` and `EndoMulStep.lean`, for the
endo-scalar decomposition gate. A *chain* of `m+1` `EndoMulScalar` rows — each consuming eight
2-bit crumbs and accumulating the registers `(n, a, b)`, gate `i`'s output registers feeding gate
`i+1`'s input — is reconstructed as a concrete `Circuit`, and we prove any satisfying witness
computes the effective scalar `a·λ + b` and the raw register `n` of the whole challenge
(`chain_toField`).

## The two subtleties, versus the endo-mul gates

* **The checker's `a`/`b` constraints are `6·`-scaled.** The dumped gate clears the rational
  coefficients of the accumulator cubics `cPoly`/`dPoly` by multiplying by `6` (`c6 = 6·cPoly`,
  `d6 = 6·dPoly`; proof-systems `endomul_scalar.rs`). So the checker↔gate bridge needs `6` (hence
  `2` and `3`) invertible — a field/char precondition, not a curve one. The `6·` factor is peeled
  by `mul_left_cancel₀`, and the division lives entirely in the once-proved `c6_eq`/`d6_eq`.
* **Register threading uses real copy constraints.** Unlike `EndoMul` (consecutive rows share
  cells), each `EndoMulScalar` row carries its own input registers `(n0,a0,b0)` in cols 0,2,3 and
  outputs `(n8,a8,b8)` in cols 1,4,5. So gate `i+1`'s inputs are wired by the permutation to gate
  `i`'s outputs — `haStep`/`hbStep`/`hnStep` are derived from `copyHolds`.

The composition feeds the abstract fold `Kimchi.Circuit.EndoScalar.chain_toField`; the init
`(a0,b0,n0) = (2,2,0)` is a hypothesis (as `chain_toField` takes it), everything else is derived
from the reconstructed circuit's `Satisfies`.
-/

namespace Kimchi.Gate.EndoScalar

open Kimchi.Gate (Row)

variable {F : Type*}

/-- Read an `EndoMulScalar` witness off the gate's single row. Column layout (proof-systems
    `endomul_scalar.rs`; see `Checker.EndoScalar`): `0 = n0`, `1 = n8`, `2 = a0`, `3 = b0`,
    `4 = a8`, `5 = b8`, `6..13 = x0..x7` (the eight crumbs). -/
def ofRows [Zero F] (curr : Row F) : Witness F :=
  { a0 := curr.getD 2 0, b0 := curr.getD 3 0, n0 := curr.getD 0 0
  , a8 := curr.getD 4 0, b8 := curr.getD 5 0, n8 := curr.getD 1 0
  , crumbs := [curr.getD 6 0, curr.getD 7 0, curr.getD 8 0, curr.getD 9 0,
               curr.getD 10 0, curr.getD 11 0, curr.getD 12 0, curr.getD 13 0] }

/-- The checker's integer-coefficient `c6` is `6·cPoly` — clearing the accumulator cubic's
    rational coefficients. Needs `2, 3 ≠ 0`; this is the only place the division appears. -/
theorem c6_eq [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (x : F) :
    Kimchi.Checker.EndoScalar.c6 x = 6 * cPoly x := by
  have h6 : (6 : F) ≠ 0 := by
    have h : (6 : F) = 2 * 3 := by norm_num
    rw [h]; exact mul_ne_zero h2 h3
  rw [Kimchi.Checker.EndoScalar.c6, cPoly]; field_simp; ring

/-- The checker's integer-coefficient `d6` is `6·dPoly`. -/
theorem d6_eq [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (x : F) :
    Kimchi.Checker.EndoScalar.d6 x = 6 * dPoly x := by
  have h6 : (6 : F) ≠ 0 := by
    have h : (6 : F) = 2 * 3 := by norm_num
    rw [h]; exact mul_ne_zero h2 h3
  rw [Kimchi.Checker.EndoScalar.d6, dPoly, cPoly]; field_simp; ring

/-- The checker's range polynomial `crumb` is the gate's `crumbPoly` (both vanish on `{0,1,2,3}`);
    no division. -/
theorem crumb_eq [Field F] (x : F) :
    Kimchi.Checker.EndoScalar.crumb x = crumbPoly x := by
  simp only [Kimchi.Checker.EndoScalar.crumb, crumbPoly]; ring

/-- **The bridge.** With `2, 3 ≠ 0`, the ingested checker's 11-constraint row predicate is exactly
    the algebraic gate's `Holds` on the 8-crumb witness read off the row. The `n` fold and the eight
    range checks match `by ring`; the `a`/`b` folds match after peeling the checker's `6·`
    factor. -/
theorem checker_holds_iff [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (curr next : Row F) :
    Holds (ofRows curr) ↔ Kimchi.Checker.EndoScalar.holds curr next := by
  have h6 : (6 : F) ≠ 0 := by
    have h : (6 : F) = 2 * 3 := by norm_num
    rw [h]; exact mul_ne_zero h2 h3
  rw [holds_iff]
  simp only [ofRows, Kimchi.Checker.EndoScalar.holds, List.foldl_cons, List.foldl_nil,
    List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_const, and_true,
    c6_eq h2 h3, d6_eq h2 h3, crumb_eq]
  constructor
  · rintro ⟨hn, ha, hb, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination -hn
    · linear_combination -6 * ha
    · linear_combination -6 * hb
    · linear_combination hx0
    · linear_combination hx1
    · linear_combination hx2
    · linear_combination hx3
    · linear_combination hx4
    · linear_combination hx5
    · linear_combination hx6
    · linear_combination hx7
  · rintro ⟨hn, ha, hb, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination -hn
    · apply mul_left_cancel₀ h6; linear_combination -ha
    · apply mul_left_cancel₀ h6; linear_combination -hb
    · linear_combination hx0
    · linear_combination hx1
    · linear_combination hx2
    · linear_combination hx3
    · linear_combination hx4
    · linear_combination hx5
    · linear_combination hx6
    · linear_combination hx7

end Kimchi.Gate.EndoScalar

namespace Kimchi.Circuit.EndoScalar

open Kimchi.Gate.EndoScalar
open Kimchi.Circuit (Cell Satisfies gatesHold copyHolds)

variable {F : Type*} [Field F] [DecidableEq F]

/-- `Array.ofFn` lookup below its length (reduces `gateAt`/`wires` on the parametric gate list). -/
private theorem getD_ofFn_lt {α} (n : ℕ) (f : Fin n → α) (r : ℕ) (d : α) (h : r < n) :
    (Array.ofFn f).getD r d = f ⟨r, h⟩ := by
  rw [Array.getD, dif_pos (by simpa using h)]; simp [Array.getElem_ofFn]

/-- Copy wiring for gate `i`'s `EndoMulScalar` row: for `i ≥ 1`, cols 0/2/3 (the input registers
    `n0`/`a0`/`b0`) wire to gate `i−1`'s output registers `n8`/`a8`/`b8` (cols 1/4/5); the output
    cols and crumb cols are self-loops. Gate 0's row is all self-loops (its init is `hinit`). -/
def esWires (i : ℕ) : Array Cell :=
  if i = 0 then #[(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)]
  else #[(i - 1, 1), (i, 1), (i - 1, 4), (i - 1, 5), (i, 4), (i, 5), (i, 6)]

/-- Gate `i`'s `EndoMulScalar` row (with the register-threading wires). -/
def esGate (i : ℕ) : Kimchi.Circuit.Gate F :=
  { kind := .endoMulScalar, coeffs := #[], wires := esWires i }

/-- The reconstructed `(m+1)`-row `EndoMulScalar` chain (gate `i` at row `i`), threaded by
    `esWires`. No public inputs — the init `(a0,b0,n0)` is pinned by the caller. -/
def esCircuit (m : ℕ) : Kimchi.Circuit.Circuit F :=
  { publicInputSize := 0
  , gates := Array.ofFn (n := m + 1) fun idx => esGate idx.val }

omit [Field F] [DecidableEq F] in
@[simp] theorem esCircuit_size (m : ℕ) : (esCircuit m (F := F)).gates.size = m + 1 := by
  simp [esCircuit]

omit [Field F] [DecidableEq F] in
/-- The row of gate `i` reconstructs to `esGate i`. -/
theorem gateAt_es (m i : ℕ) (hi : i < m + 1) :
    (esCircuit m (F := F)).gateAt i = esGate i := by
  rw [Circuit.gateAt, esCircuit, getD_ofFn_lt _ _ _ _ hi]

omit [Field F] [DecidableEq F] in
theorem esWires_get0 (i : ℕ) (hi : i ≠ 0) (d : Cell) : (esWires i).getD 0 d = (i - 1, 1) := by
  simp [esWires, hi]

omit [Field F] [DecidableEq F] in
theorem esWires_get2 (i : ℕ) (hi : i ≠ 0) (d : Cell) : (esWires i).getD 2 d = (i - 1, 4) := by
  simp [esWires, hi]

omit [Field F] [DecidableEq F] in
theorem esWires_get3 (i : ℕ) (hi : i ≠ 0) (d : Cell) : (esWires i).getD 3 d = (i - 1, 5) := by
  simp [esWires, hi]

/-- The witness read off gate `i`'s row. -/
private def gwit (w : Kimchi.Circuit.Witness F) (i : ℕ) : Kimchi.Gate.EndoScalar.Witness F :=
  ofRows (w.row i)

/-- **End-to-end soundness for the reconstructed `EndoMulScalar` chain.** With `2, 3 ≠ 0` and the
    canonical init `(a0,b0,n0) = (2,2,0)` at row 0, any witness satisfying `esCircuit m` computes
    the effective scalar `a·λ + b` of the whole challenge and its raw register `n`. The per-row
    `Holds` is *derived* from `gatesHold` + `checker_holds_iff`, and the register threading from
    `copyHolds`; the composition is `Circuit.EndoScalar.chain_toField`. -/
theorem circuit_sound (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (lam : F)
    (m : ℕ) (w : Kimchi.Circuit.Witness F) (pub : Array F)
    (hsat : Satisfies (esCircuit m) w pub)
    (ha0 : (gwit w 0).a0 = 2) (hb0 : (gwit w 0).b0 = 2) (hn0 : (gwit w 0).n0 = 0) :
    (gwit w m).a8 * lam + (gwit w m).b8 = toField (chainCrumbs (gwit w) (m + 1)) lam
      ∧ (gwit w m).n8 = nReconstruct (chainCrumbs (gwit w) (m + 1)) := by
  obtain ⟨hgates, hcopy⟩ := hsat
  -- each row's gate identity, from `gatesHold` through the checker bridge
  have hHolds : ∀ i, i ≤ m → Holds (gwit w i) := by
    intro i hi
    have hg := hgates i (by rw [esCircuit_size]; omega)
    rw [gateAt_es m i (by omega)] at hg
    have hck : Kimchi.Checker.EndoScalar.holds (w.row i) (w.row (i + 1)) := hg
    exact (checker_holds_iff h2 h3 _ _).2 hck
  -- the register threading, from `copyHolds`
  have haStep : ∀ i, i < m → (gwit w (i + 1)).a0 = (gwit w i).a8 := by
    intro i hi
    have hc := hcopy (i + 1) (by rw [esCircuit_size]; omega) 2 (by omega)
    rw [gateAt_es m (i + 1) (by omega)] at hc
    simp only [esGate, esWires_get2 (i + 1) (by omega)] at hc
    rw [show i + 1 - 1 = i by omega] at hc
    exact hc
  have hbStep : ∀ i, i < m → (gwit w (i + 1)).b0 = (gwit w i).b8 := by
    intro i hi
    have hc := hcopy (i + 1) (by rw [esCircuit_size]; omega) 3 (by omega)
    rw [gateAt_es m (i + 1) (by omega)] at hc
    simp only [esGate, esWires_get3 (i + 1) (by omega)] at hc
    rw [show i + 1 - 1 = i by omega] at hc
    exact hc
  have hnStep : ∀ i, i < m → (gwit w (i + 1)).n0 = (gwit w i).n8 := by
    intro i hi
    have hc := hcopy (i + 1) (by rw [esCircuit_size]; omega) 0 (by omega)
    rw [gateAt_es m (i + 1) (by omega)] at hc
    simp only [esGate, esWires_get0 (i + 1) (by omega)] at hc
    rw [show i + 1 - 1 = i by omega] at hc
    exact hc
  exact chain_toField lam m (gwit w) hHolds ha0 hb0 hn0 haStep hbStep hnStep

/-! ## Pasta specializations

At the concrete Pasta scalar fields the char precondition `2, 3 ≠ 0` is discharged by `decide`, so
the reconstructed `EndoMulScalar` chain has no field/char side conditions — only the init. -/

open CompElliptic.Fields.Pasta

/-- `circuit_sound` at the Pallas base field: `2, 3 ≠ 0` by `decide`. -/
theorem pallas_circuit_sound (lam : PallasBaseField) (m : ℕ)
    (w : Kimchi.Circuit.Witness PallasBaseField) (pub : Array PallasBaseField)
    (hsat : Satisfies (esCircuit m) w pub)
    (ha0 : (gwit w 0).a0 = 2) (hb0 : (gwit w 0).b0 = 2) (hn0 : (gwit w 0).n0 = 0) :
    (gwit w m).a8 * lam + (gwit w m).b8 = toField (chainCrumbs (gwit w) (m + 1)) lam
      ∧ (gwit w m).n8 = nReconstruct (chainCrumbs (gwit w) (m + 1)) :=
  circuit_sound (by decide) (by decide) lam m w pub hsat ha0 hb0 hn0

/-- `circuit_sound` at the Vesta base field. -/
theorem vesta_circuit_sound (lam : VestaBaseField) (m : ℕ)
    (w : Kimchi.Circuit.Witness VestaBaseField) (pub : Array VestaBaseField)
    (hsat : Satisfies (esCircuit m) w pub)
    (ha0 : (gwit w 0).a0 = 2) (hb0 : (gwit w 0).b0 = 2) (hn0 : (gwit w 0).n0 = 0) :
    (gwit w m).a8 * lam + (gwit w m).b8 = toField (chainCrumbs (gwit w) (m + 1)) lam
      ∧ (gwit w m).n8 = nReconstruct (chainCrumbs (gwit w) (m + 1)) :=
  circuit_sound (by decide) (by decide) lam m w pub hsat ha0 hb0 hn0

end Kimchi.Circuit.EndoScalar
