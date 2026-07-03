import Kimchi.Circuit
import Kimchi.Circuit.EndoMul

/-!
# End-to-end soundness for a chained `EndoMul` circuit

The gold-standard companion to `Circuits/VarBaseMulStep.lean`, for the GLV endomorphism-accelerated
scalar-multiplication gate. A *chain* of `m` `EndoMul` rows — each processing four scalar bits via
two endo-scaled incomplete additions, gate `i`'s output accumulator feeding gate `i+1`'s input — is
reconstructed as a concrete `Circuit`, and we prove any satisfying witness certifies `[s]·T` (the
scalar `s = EndoScalar.toField (crumbList …) λ`) in Mathlib's group.

## The two subtleties, versus VarBaseMul

* **Threading is free.** `EndoMul` lays its gates on *consecutive* rows (gate `i` at row `i`,
  reading row `i+1` for its output `(xS,yS,n')`). Gate `i`'s output cells and gate `i+1`'s input are
  therefore the *same physical cells* — so `hthread` holds by `rfl`, no copy constraint required.
  Only the shared base `T = (xT,yT)` needs copy wiring (each row's cols 0–1 back to row 0).
* **The checker omits the distinct-point constraint.** The dumped `EndoMul` gate carries 11
  constraints (proof-systems `endosclmul.rs`); the algebraic `Gate.EndoMul.Holds` adds a 12th — the
  distinct-point check `(xP−xR)(xR−xS)·inv = 1` — which the pre-fix gate lacks (it is otherwise
  underconstrained; see `Gate/EndoMul.lean`). So the checker↔gate bridge (`checker_holds_iff`) is an
  iff only *up to* that distinctness: `ofRows` picks `inv := ((xP−xR)(xR−xS))⁻¹`, and the distinct-
  point non-degeneracy `(xP−xR)(xR−xS) ≠ 0` becomes a curve-level precondition — exactly as
  `AddCompleteStep` keeps input nonsingularity a hypothesis while deriving the gate identity.

The composition rests on the abstract fold `Kimchi.Circuit.EndoMul.endoMul`; everything is field-
generic (the Pasta instantiations `{pallas,vesta}_endoMul` are layered on top as before).
-/

namespace Kimchi.Gate.EndoMul

open Kimchi.Gate (Row)

variable {F : Type*}

/-- Read an `EndoMul` witness off the physical row pair (`curr` = the gate's row, `next` its
    successor holding the output). Column layout (proof-systems `endosclmul.rs`; see
    `Checker.EndoMul`): `curr` `0,1 = xT,yT`, `4,5 = xP,yP`, `6 = n`, `7,8 = xR,yR`, `9,10 = s1,s3`,
    `11..14 = b1..b4`; `next` `4,5 = xS,yS`, `6 = n'`. The distinct-point witness `inv` is *chosen*
    (the checker does not carry it) as the inverse making the 12th constraint hold exactly when the
    two additions are genuinely distinct. -/
def ofRows [Field F] (curr next : Row F) : Witness F :=
  { xT := curr.getD 0 0, yT := curr.getD 1 0
  , xP := curr.getD 4 0, yP := curr.getD 5 0, n := curr.getD 6 0
  , xR := curr.getD 7 0, yR := curr.getD 8 0
  , s1 := curr.getD 9 0, s3 := curr.getD 10 0
  , b1 := curr.getD 11 0, b2 := curr.getD 12 0, b3 := curr.getD 13 0, b4 := curr.getD 14 0
  , xS := next.getD 4 0, yS := next.getD 5 0, nPrime := next.getD 6 0
  , inv := ((curr.getD 4 0 - curr.getD 7 0) * (curr.getD 7 0 - next.getD 4 0))⁻¹ }

/-- **The bridge.** The ingested checker's 11-constraint row predicate, together with the distinct-
    point non-degeneracy, is exactly the algebraic gate's 12-constraint `Holds` on the witness read
    off the pair (at the checker's fixed `endo`). The 11 shared constraints match `by ring`; the
    12th (`inv`) reduces to `(xP−xR)(xR−xS) ≠ 0` because `ofRows` set `inv` to that product's
    inverse. -/
theorem checker_holds_iff [Field F] (curr next : Row F) :
    Holds Kimchi.Checker.EndoMul.endo (ofRows curr next)
      ↔ Kimchi.Checker.EndoMul.holds curr next
        ∧ ((ofRows curr next).xP - (ofRows curr next).xR)
            * ((ofRows curr next).xR - (ofRows curr next).xS) ≠ 0 := by
  rw [holds_iff]
  simp only [ofRows, Kimchi.Checker.EndoMul.holds]
  constructor
  · rintro ⟨A1, B1, C1, A2, B2, C2, INV, cb1, cb2, cb3, cb4, scal⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · linear_combination cb1
    · linear_combination cb2
    · linear_combination cb3
    · linear_combination cb4
    · linear_combination A1
    · linear_combination B1
    · linear_combination C1
    · linear_combination A2
    · linear_combination B2
    · linear_combination C2
    · linear_combination -scal
    · intro hd; rw [hd, zero_mul] at INV; exact zero_ne_one INV
  · rintro ⟨⟨cb1, cb2, cb3, cb4, cA1, cB1, cC1, cA2, cB2, cC2, cscal⟩, hdist⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination cA1
    · linear_combination cB1
    · linear_combination cC1
    · linear_combination cA2
    · linear_combination cB2
    · linear_combination cC2
    · exact mul_inv_cancel₀ hdist
    · linear_combination cb1
    · linear_combination cb2
    · linear_combination cb3
    · linear_combination cb4
    · linear_combination -cscal

end Kimchi.Gate.EndoMul

namespace Kimchi.Circuit.EndoMul

open Kimchi.Gate.EndoMul WeierstrassCurve.Affine
open Kimchi.Circuit (Cell Satisfies gatesHold copyHolds)

variable {F : Type*} [Field F] [DecidableEq F]

/-- `Array.ofFn` lookup below its length (reduces `gateAt`/`wires` on the parametric gate list). -/
private theorem getD_ofFn_lt {α} (n : ℕ) (f : Fin n → α) (r : ℕ) (d : α) (h : r < n) :
    (Array.ofFn f).getD r d = f ⟨r, h⟩ := by
  rw [Array.getD, dif_pos (by simpa using h)]; simp [Array.getElem_ofFn]

/-- Copy wiring for gate `i`'s `EndoMul` row: cols 0–1 wire the base `(xT,yT)` to gate 0's (shared
    `T`); the accumulator/register threading is *free* (consecutive rows share cells), so cols 2–6
    are self-loops. Gate 0's row is all self-loops. -/
def emWires (i : ℕ) : Array Cell :=
  if i = 0 then #[(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)]
  else #[(0, 0), (0, 1), (i, 2), (i, 3), (i, 4), (i, 5), (i, 6)]

/-- Gate `i`'s `EndoMul` row (with the base-sharing wires). -/
def emGate (i : ℕ) : Kimchi.Circuit.Gate F :=
  { kind := .endoMul, coeffs := #[], wires := emWires i }

/-- The reconstructed `m`-gate `EndoMul` circuit: `m` `EndoMul` rows (gate `i` at row `i`), the base
    shared to row 0. No public inputs — the init `P₀` is pinned by `hP0`. -/
def emCircuit (m : ℕ) : Kimchi.Circuit.Circuit F :=
  { publicInputSize := 0
  , gates := Array.ofFn (n := m) fun idx => emGate idx.val }

omit [Field F] [DecidableEq F] in
@[simp] theorem emCircuit_size (m : ℕ) : (emCircuit m (F := F)).gates.size = m := by
  simp [emCircuit]

omit [Field F] [DecidableEq F] in
/-- The row of gate `i` reconstructs to `emGate i`. -/
theorem gateAt_em (m i : ℕ) (hi : i < m) :
    (emCircuit m (F := F)).gateAt i = emGate i := by
  rw [Circuit.gateAt, emCircuit, getD_ofFn_lt _ _ _ _ hi]

omit [Field F] [DecidableEq F] in
theorem emWires_get0 (i : ℕ) (hi : i ≠ 0) (d : Cell) : (emWires i).getD 0 d = (0, 0) := by
  simp [emWires, hi]

omit [Field F] [DecidableEq F] in
theorem emWires_get1 (i : ℕ) (hi : i ≠ 0) (d : Cell) : (emWires i).getD 1 d = (0, 1) := by
  simp [emWires, hi]

/-- The witness read off gate `i`'s row pair (`i`, `i+1`). -/
private def gwit (w : Kimchi.Circuit.Witness F) (i : ℕ) : Kimchi.Gate.EndoMul.Witness F :=
  ofRows (w.row i) (w.row (i + 1))

/-- Extract from `Satisfies (emCircuit m) w pub` the data the `endoMul` fold consumes: each row's
    full 12-constraint `Holds` (`gatesHold` + `checker_holds_iff`, using the distinct-point `hdist`)
    and the shared base (`copyHolds`). Shared by `circuit_sound` and the Pasta specialization. -/
theorem satisfies_extract (m : ℕ) (w : Kimchi.Circuit.Witness F) (pub : Array F)
    (hsat : Satisfies (emCircuit m) w pub)
    (hdist : ∀ i, i < m →
        ((gwit w i).xP - (gwit w i).xR) * ((gwit w i).xR - (gwit w i).xS) ≠ 0) :
    (∀ i, i < m → Holds Kimchi.Checker.EndoMul.endo (gwit w i))
    ∧ (∀ i, i < m → (gwit w i).xT = (gwit w 0).xT ∧ (gwit w i).yT = (gwit w 0).yT) := by
  obtain ⟨hgates, hcopy⟩ := hsat
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hg := hgates i (by rw [emCircuit_size]; omega)
    rw [gateAt_em m i hi] at hg
    have hck : Kimchi.Checker.EndoMul.holds (w.row i) (w.row (i + 1)) := hg
    exact (checker_holds_iff _ _).2 ⟨hck, hdist i hi⟩
  · rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; exact ⟨rfl, rfl⟩
    · have hc0 := hcopy i (by rw [emCircuit_size]; omega) 0 (by omega)
      have hc1 := hcopy i (by rw [emCircuit_size]; omega) 1 (by omega)
      rw [gateAt_em m i hi] at hc0 hc1
      simp only [emGate, emWires_get0 i (by omega), emWires_get1 i (by omega)] at hc0 hc1
      exact ⟨hc0, hc1⟩

/-- **End-to-end soundness for the reconstructed `EndoMul` chain.** Any witness satisfying
    `emCircuit m` — with the base/init nonsingularity, the per-row curve non-degeneracies (`hxne`,
    the distinct-point `hdist`), and the eigenvalue `φT = [λ]·T` — certifies `[s]·T`, the scalar
    `s = EndoScalar.toField (crumbList …) λ`. The per-row `Holds` (all 12 constraints, `inv`
    included) and the base sharing are *derived* from `Satisfies` (`gatesHold` + `checker_holds_iff`
    and `copyHolds`); the threading is definitional. Only the curve-level facts remain hypotheses,
    matching `AddCompleteStep` / `VarBaseMulStep`. -/
theorem circuit_sound
    (W : WeierstrassCurve.Affine F) [Fact (Nat.Prime W.order)]
    (ha : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hodd : W.order ≠ 2)
    (m : ℕ) (w : Kimchi.Circuit.Witness F) (pub : Array F)
    (hsat : Satisfies (emCircuit m) w pub)
    (T φT : W.Point)
    (hTns : W.Nonsingular (gwit w 0).xT (gwit w 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hφTns : W.Nonsingular (Kimchi.Checker.EndoMul.endo * (gwit w 0).xT) (gwit w 0).yT)
    (hφTeq : φT = Point.some _ _ hφTns)
    (hP0ns : W.Nonsingular (gwit w 0).xP (gwit w 0).yP)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T + (2 : ℤ) • φT)
    (hxne : ∀ i, i < m →
        (gwit w i).xP ≠ (1 + (Kimchi.Checker.EndoMul.endo - 1) * (gwit w i).b1) * (gwit w i).xT
        ∧ (gwit w i).xR ≠ (1 + (Kimchi.Checker.EndoMul.endo - 1) * (gwit w i).b3) * (gwit w i).xT)
    (hdist : ∀ i, i < m →
        ((gwit w i).xP - (gwit w i).xR) * ((gwit w i).xR - (gwit w i).xS) ≠ 0)
    (lam : ℤ) (heig : φT = lam • T) :
    ∃ (hfin : W.Nonsingular (accX (gwit w) m) (accY (gwit w) m)) (s : ℤ),
      Point.some _ _ hfin = s • T
        ∧ (s : F) = Kimchi.Circuit.EndoScalar.toField (crumbList (gwit w) m) (lam : F) := by
  obtain ⟨hholds, hbase⟩ := satisfies_extract m w pub hsat hdist
  -- the accumulator/register threading is definitional (consecutive rows share cells)
  have hthread : ∀ i, i + 1 < m →
      (gwit w (i + 1)).xP = (gwit w i).xS ∧ (gwit w (i + 1)).yP = (gwit w i).yS :=
    fun i _ => ⟨rfl, rfl⟩
  exact endoMul W ha h2 h3 hodd Kimchi.Checker.EndoMul.endo m (gwit w) hholds T φT
    hTns hTeq hφTns hφTeq hbase hthread hP0ns hP0 hxne lam heig

/-! ## Pasta specialization

Routing `Satisfies` through the deployed `pallas_endoMul` (which derives the per-row `hxne` from the
GLV short-basis bound and the eigenvalue from `pallas_eigen`, and discharges the char/order side
conditions by computation) drops those hypotheses. The dumped `EndoMul` gate's endomorphism constant
`Checker.EndoMul.endo` now equals `pallas_endo` *definitionally* (both the same concrete numeral),
so no `endo = β` hypothesis is needed. The distinct-point `hdist` stays: the dumped gate omits that
constraint. -/

open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Kimchi.Pasta

/-- **Pallas.** From `Satisfies (emCircuit m) w pub` (plus base/init, the distinct-point `hdist`,
    and the GLV bit bound) the reconstructed chain computes `[s]·T` with
    `s = EndoScalar.toField (crumbList …) pallas_lam`. `hxne`, the eigenvalue, and the char/order
    side conditions are all discharged inside `pallas_endoMul`. -/
theorem pallas_endoMul_circuit
    (m : ℕ) (hbits : 4 * m ≤ 244) (w : Kimchi.Circuit.Witness PallasBaseField)
    (pub : Array PallasBaseField) (hsat : Satisfies (emCircuit m) w pub)
    (hdist : ∀ i, i < m →
        ((gwit w i).xP - (gwit w i).xR) * ((gwit w i).xR - (gwit w i).xS) ≠ 0)
    (T φT : Pallas.curve.toAffine.Point)
    (hTns : Pallas.curve.toAffine.Nonsingular (gwit w 0).xT (gwit w 0).yT)
    (hTeq : T = Point.some _ _ hTns)
    (hφTns : Pallas.curve.toAffine.Nonsingular (pallas_endo * (gwit w 0).xT) (gwit w 0).yT)
    (hφTeq : φT = Point.some _ _ hφTns)
    (hP0ns : Pallas.curve.toAffine.Nonsingular (gwit w 0).xP (gwit w 0).yP)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T + (2 : ℤ) • φT) :
    ∃ (hfin : Pallas.curve.toAffine.Nonsingular (accX (gwit w) m) (accY (gwit w) m)) (s : ℤ),
      Point.some _ _ hfin = s • T
        ∧ (s : PallasBaseField)
            = Kimchi.Circuit.EndoScalar.toField (crumbList (gwit w) m)
                (pallas_lam : PallasBaseField) := by
  -- `Checker.EndoMul.endo` and `pallas_endo` are the same concrete numeral, so `hholds` already
  -- has the `Holds pallas_endo` type `pallas_endoMul` expects (definitionally).
  obtain ⟨hholds, hbase⟩ := satisfies_extract m w pub hsat hdist
  have hthread : ∀ i, i + 1 < m →
      (gwit w (i + 1)).xP = (gwit w i).xS ∧ (gwit w (i + 1)).yP = (gwit w i).yS :=
    fun i _ => ⟨rfl, rfl⟩
  exact pallas_endoMul m hbits (gwit w) hholds T φT hTns hTeq hφTns hφTeq hbase hthread hP0ns hP0

end Kimchi.Circuit.EndoMul
