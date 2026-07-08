import Kimchi.Index.Soundness

/-!
# The full kimchi aggregate family

The single constraint family behind kimchi's one quotient check, as index data
(`linearization.rs`, `constraints_expr`). Kimchi allocates alpha powers in a shared pool:
all gate types combine their constraint lists with the *same* powers `α⁰..α²⁰` (the pool
is sized by the largest gate, VarBaseMul's 21 — "only the max number of constraints
matters"), which is sound because selectors are row-disjoint; the permutation's three
constraints are live on all rows simultaneously with the gates, so they get the next
three powers. The public polynomial enters once, in the generic gate's `α⁰` slot
("the generic gate must be associated with alpha^0 to make the later addition with the
public input work"): kimchi adds the interpolant of the *negated* public inputs, so the
slot-0 member here subtracts the positive interpolant, giving `E₁(i) − pub(i) = 0` at
generic rows — the `Generic.withPublic` row semantics, one public input per row in
column 0 of the first `publicCount` rows (`prover.rs`: `witness[0][0..cs.public]`).

So the family has `21 + 3` members:

* member `k < 21`: the cross-gate sum `∑ g, selectorPoly g · E_{g,k}` (a gate with fewer
  than `k+1` constraints contributes nothing — `getD` with default `0`), minus the
  public polynomial at `k = 0`;
* members `21..23`: the permutation constraints at the index's wiring data, for a given
  accumulator `z` and challenge pair `(β, γ)`.

The per-gate constraint lists are the single-source gate transcriptions
(`gateConstraints`), whose lengths match kimchi's `CONSTRAINTS` constants
(`gateConstraints_length_*`, definitional). Phase B's separation argument recovers
per-gate divisibility from the summed members via selector row-disjointness
(`selectorRow_disjoint`).
-/

namespace Kimchi.Index

open Polynomial Kimchi.Quotient

namespace Index

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ} [NeZero n]

/-- The (positive) public-input interpolant: `pub i` at the public rows, `0` beyond.
Kimchi commits to its negation and adds it into the generic `α⁰` slot. -/
noncomputable def pubPoly (idx : Index F n) (pub : Fin idx.publicCount → F) :
    Polynomial F :=
  columnPoly idx.omega (pubAt idx pub)

theorem eval_pubPoly (idx : Index F n) (pub : Fin idx.publicCount → F) (i : Fin n) :
    (idx.pubPoly pub).eval (idx.omega ^ (i : ℕ)) = pubAt idx pub i :=
  eval_columnPoly idx.omega_prim _ i

/-- The constraint list of a gate type, over the index's column interpolants — the
single-source gate transcriptions at the polynomial carrier. `zero` constrains
nothing. -/
noncomputable def gateConstraints (idx : Index F n) (wTab : Fin n → Fin 15 → F) :
    GateType → List (Polynomial F)
  | .zero => []
  | .generic => (genericArgument (F := F)).constraints
      (polyEnv idx.omega wTab idx.coeffTable)
  | .poseidon => Gate.Poseidon.constraints (Poseidon.rcPoly idx.omega idx.coeffTable)
      (Poseidon.polyWitness idx.omega wTab)
  | .completeAdd => Gate.AddComplete.constraints (AddComplete.polyWitness idx.omega wTab)
  | .varBaseMul => Gate.VarBaseMul.constraints (VarBaseMul.polyWitness idx.omega wTab)
  | .endoMul => Gate.EndoMul.constraints (C idx.endoBase)
      (EndoMul.polyWitness idx.omega wTab)
  | .endoScalar => Gate.EndoScalar.constraints
      (EndoScalar.polyWitness idx.omega wTab) (F := F)

/-- The shared gate alpha-pool size: kimchi registers the pool at the largest gate's
count — VarBaseMul's 21 (`linearization.rs`: "Only the max number of constraints
matters"). -/
def gateAlphaCount : ℕ := 21

/-- The permutation's alpha count (`permutation.rs`: `CONSTRAINTS = 3`). -/
def permAlphaCount : ℕ := 3

/-- The lengths of the gate transcriptions match kimchi's `CONSTRAINTS` constants. -/
theorem gateConstraints_length (idx : Index F n) (wTab : Fin n → Fin 15 → F) :
    (idx.gateConstraints wTab .zero).length = 0
      ∧ (idx.gateConstraints wTab .generic).length = 2
      ∧ (idx.gateConstraints wTab .poseidon).length = 15
      ∧ (idx.gateConstraints wTab .completeAdd).length = 7
      ∧ (idx.gateConstraints wTab .varBaseMul).length = 21
      ∧ (idx.gateConstraints wTab .endoMul).length = 12
      ∧ (idx.gateConstraints wTab .endoScalar).length = 11 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Selector row-disjointness: at any row, at most one gate type's selector is live —
the fact that makes kimchi's shared alpha pool sound. -/
theorem selectorRow_disjoint (idx : Index F n) {g g' : GateType} (hgg : g ≠ g')
    (i : Fin n) : idx.selectorRow g i = 0 ∨ idx.selectorRow g' i = 0 := by
  unfold selectorRow
  by_cases h : (idx.gates i).typ = g
  · exact Or.inr (if_neg fun h' => hgg (h.symm.trans h'))
  · exact Or.inl (if_neg h)

/-- The gate part of the aggregate member at power `k`: the cross-gate sum, minus the
public interpolant in the generic `α⁰` slot. -/
noncomputable def gateMember (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin 15 → F) (k : ℕ) : Polynomial F :=
  (∑ g : GateType,
      columnPoly idx.omega (idx.selectorRow g) * (idx.gateConstraints wTab g).getD k 0)
    - if k = 0 then idx.pubPoly pub else 0

open Kimchi.Quotient.Permutation in
/-- **The full kimchi aggregate family** — the `21 + 3` members of the one quotient
check, at a given accumulator `z` and permutation challenge pair `(β, γ)`: the shared
gate pool first, then the three permutation constraints at the index's wiring data. -/
noncomputable def fullFamily (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin 15 → F) (z : Polynomial F) (β γ : F) :
    Fin (gateAlphaCount + permAlphaCount) → Polynomial F :=
  fun k =>
    if h : (k : ℕ) < gateAlphaCount then
      idx.gateMember pub wTab k
    else
      Permutation.constraints idx.omega idx.zkRows z (idx.permWitnessPoly wTab)
        (Permutation.sigmaPoly idx.omega idx.shifts idx.wiringPerm) idx.shifts β γ
        (⟨0, Nat.pos_of_neZero n⟩ : Fin n)
        ⟨n - idx.zkRows, by have := idx.zk_pos; have := idx.zk_le; omega⟩
        ⟨(k : ℕ) - gateAlphaCount, by
          have := k.isLt
          simp only [gateAlphaCount, permAlphaCount] at *
          omega⟩

end Index

end Kimchi.Index
