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

/-! ## Separation: the shared pool collapses back to per-gate rows

`selectorRow` is one-hot at every row — `1` at the row's own gate type, `0` at every
other — so evaluating the `k`-th summed member at a domain node leaves exactly the live
gate's `k`-th constraint (minus the public value in slot `0`). Divisibility of the 21
summed members therefore pins, row by row, every constraint of whichever gate lives
there — the per-gate grip the shared alpha pool appeared to give up. The per-gate
`Argument.bridge` then carries the polynomial identities to `rowSatisfies`' cell
equations; the generic slot-`0` public subtraction lands on `withPublic` by
`Generic.withPublic_holds_iff`. -/

/-- The selector is `0` away from the row's own gate type (one-hotness, with
`selectorRow_eq_one`). -/
theorem selectorRow_eq_zero (idx : Index F n) {g : GateType} {i : Fin n}
    (htyp : (idx.gates i).typ ≠ g) : idx.selectorRow g i = 0 := by
  simp [selectorRow, htyp]

/-- Every gate's transcription fits inside the shared pool (VarBaseMul's 21). -/
theorem gateConstraints_length_le (idx : Index F n) (wTab : Fin n → Fin 15 → F)
    (g : GateType) : (idx.gateConstraints wTab g).length ≤ gateAlphaCount := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := idx.gateConstraints_length wTab
  cases g <;> simp [h0, h1, h2, h3, h4, h5, h6, gateAlphaCount]

/-- **Row collapse.** At a domain node, the `k`-th gate member evaluates to the live
gate's `k`-th constraint value, minus the public value in slot `0`: every other gate's
term dies with its selector. -/
theorem eval_gateMember (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin 15 → F) (k : ℕ) (i : Fin n) :
    (idx.gateMember pub wTab k).eval (idx.omega ^ (i : ℕ))
      = ((idx.gateConstraints wTab (idx.gates i).typ).getD k 0).eval
          (idx.omega ^ (i : ℕ))
        - (if k = 0 then pubAt idx pub i else 0) := by
  unfold gateMember
  rw [eval_sub]
  congr 1
  · rw [eval_finsetSum, Finset.sum_eq_single ((idx.gates i).typ)]
    · rw [eval_mul, eval_columnPoly idx.omega_prim, idx.selectorRow_eq_one rfl, one_mul]
    · intro g _ hg
      rw [eval_mul, eval_columnPoly idx.omega_prim, idx.selectorRow_eq_zero (Ne.symm hg),
        zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · split_ifs
    · exact idx.eval_pubPoly pub i
    · exact eval_zero

/-- **Member divisibility pins every slot at every row**: the live gate's `k`-th
constraint value is the public value in slot `0` and `0` beyond (slots past the gate's
list are the zero polynomial, so nothing is asserted vacuously — they evaluate to `0`
outright). -/
theorem eval_gateConstraints_of_dvd (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin 15 → F)
    (hdvd : ∀ k, k < gateAlphaCount → zH F n ∣ idx.gateMember pub wTab k)
    (i : Fin n) (k : ℕ) :
    ((idx.gateConstraints wTab (idx.gates i).typ).getD k 0).eval (idx.omega ^ (i : ℕ))
      = if k = 0 then pubAt idx pub i else 0 := by
  by_cases hk : k < gateAlphaCount
  · have h0 := (zH_dvd_iff idx.omega_prim (Nat.pos_of_neZero n) _).mp (hdvd k hk)
      (i : ℕ) i.isLt
    rw [idx.eval_gateMember] at h0
    exact sub_eq_zero.mp h0
  · have hlen := idx.gateConstraints_length_le wTab (idx.gates i).typ
    have hk' : gateAlphaCount ≤ k := Nat.le_of_not_lt hk
    have hpos : 0 < gateAlphaCount := by norm_num [gateAlphaCount]
    rw [List.getD_eq_default _ _ (by omega), eval_zero, if_neg (by omega)]

/-- All row constraint values vanish, given the eval bridge for the gate's polynomial
list and vanishing of every slot. -/
theorem allZero_of_bridge {P : List (Polynomial F)} {L : List F} {x : F}
    (hb : P.map (·.eval x) = L)
    (hvan : ∀ k : ℕ, (P.getD k 0).eval x = 0) :
    ∀ e ∈ L, e = 0 := by
  intro e he
  rw [← hb] at he
  obtain ⟨E, hE, rfl⟩ := List.mem_map.mp he
  obtain ⟨c, rfl⟩ := List.mem_iff_get.mp hE
  have hc := hvan (c : ℕ)
  rwa [List.getD_eq_getElem _ _ c.isLt, ← List.get_eq_getElem] at hc

/-- **Phase-B gate separation.** If `Z_H` divides all 21 summed gate members, every row
satisfies its gate branch of `rowSatisfies` — provided the public rows are generic
gates (kimchi's construction: the first `publicCount` rows *are* the public-input
generic rows). Selector one-hotness undoes the sharing: at a row of gate `g`, slot `k`
pins `g`'s `k`-th constraint, with the public value folded into the generic slot `0`
and vanishing outside the public region on every other gate. -/
theorem rowSatisfies_of_gateMember_dvd (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin 15 → F)
    (hpubgen : ∀ i : Fin n, (i : ℕ) < idx.publicCount → (idx.gates i).typ = .generic)
    (hdvd : ∀ k, k < gateAlphaCount → zH F n ∣ idx.gateMember pub wTab k) :
    ∀ i, rowSatisfies idx pub wTab i := by
  intro i
  have hvan := idx.eval_gateConstraints_of_dvd pub wTab hdvd i
  have hpub0 : (idx.gates i).typ ≠ .generic → pubAt idx pub i = 0 := fun hne => by
    unfold pubAt
    exact dif_neg fun h => hne (hpubgen i h)
  unfold rowSatisfies
  cases htyp : (idx.gates i).typ with
  | zero => trivial
  | generic =>
    simp only [htyp] at hvan
    rw [Gate.Generic.withPublic_holds_iff]
    have hb := (genericArgument (F := F)).bridge idx.omega_prim wTab idx.coeffTable i
    simp only [genericArgument, genericCellMap, Gate.Generic.constraints, List.map_cons,
      List.map_nil, List.cons.injEq, and_true] at hb
    obtain ⟨hb1, hb2⟩ := hb
    have h0 := hvan 0
    have h1 := hvan 1
    simp only [gateConstraints, genericArgument, genericCellMap, Gate.Generic.constraints,
      List.getD_cons_zero, List.getD_cons_succ, if_pos, one_ne_zero, if_neg,
      Nat.one_ne_zero, ite_false, ite_true] at h0 h1
    exact ⟨hb1 ▸ h0, hb2 ▸ h1⟩
  | poseidon =>
    have hvan0 : ∀ k : ℕ,
        ((idx.gateConstraints wTab .poseidon).getD k 0).eval (idx.omega ^ (i : ℕ)) = 0 :=
      fun k => by
        have h := hvan k
        rw [htyp] at h
        rw [h, hpub0 (by simp [htyp]), ite_self]
    exact allZero_of_bridge
      ((Poseidon.argument (F := F)).bridge idx.omega_prim wTab idx.coeffTable i) hvan0
  | completeAdd =>
    have hvan0 : ∀ k : ℕ,
        ((idx.gateConstraints wTab .completeAdd).getD k 0).eval (idx.omega ^ (i : ℕ))
          = 0 :=
      fun k => by
        have h := hvan k
        rw [htyp] at h
        rw [h, hpub0 (by simp [htyp]), ite_self]
    exact allZero_of_bridge
      ((AddComplete.argument (F := F)).bridge idx.omega_prim wTab idx.coeffTable i) hvan0
  | varBaseMul =>
    have hvan0 : ∀ k : ℕ,
        ((idx.gateConstraints wTab .varBaseMul).getD k 0).eval (idx.omega ^ (i : ℕ))
          = 0 :=
      fun k => by
        have h := hvan k
        rw [htyp] at h
        rw [h, hpub0 (by simp [htyp]), ite_self]
    exact allZero_of_bridge
      ((VarBaseMul.argument (F := F)).bridge idx.omega_prim wTab idx.coeffTable i) hvan0
  | endoMul =>
    have hvan0 : ∀ k : ℕ,
        ((idx.gateConstraints wTab .endoMul).getD k 0).eval (idx.omega ^ (i : ℕ)) = 0 :=
      fun k => by
        have h := hvan k
        rw [htyp] at h
        rw [h, hpub0 (by simp [htyp]), ite_self]
    exact allZero_of_bridge
      ((EndoMul.argument idx.endoBase).bridge idx.omega_prim wTab idx.coeffTable i) hvan0
  | endoScalar =>
    have hvan0 : ∀ k : ℕ,
        ((idx.gateConstraints wTab .endoScalar).getD k 0).eval (idx.omega ^ (i : ℕ))
          = 0 :=
      fun k => by
        have h := hvan k
        rw [htyp] at h
        rw [h, hpub0 (by simp [htyp]), ite_self]
    exact allZero_of_bridge
      ((EndoScalar.argument (F := F)).bridge idx.omega_prim wTab idx.coeffTable i) hvan0

/-- The gate branches of `rowSatisfies`, from divisibility of the **full family**: the
gate members are the first `gateAlphaCount` entries of `fullFamily`. -/
theorem rowSatisfies_of_fullFamily_dvd (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin 15 → F) (z : Polynomial F) (β γ : F)
    (hpubgen : ∀ i : Fin n, (i : ℕ) < idx.publicCount → (idx.gates i).typ = .generic)
    (hdvd : ∀ s, zH F n ∣ idx.fullFamily pub wTab z β γ s) :
    ∀ i, rowSatisfies idx pub wTab i :=
  idx.rowSatisfies_of_gateMember_dvd pub wTab hpubgen fun k hk => by
    have h := hdvd ⟨k, by omega⟩
    rwa [fullFamily, dif_pos hk] at h

/-! ## Alpha instantiation: the one quotient check

Kimchi folds the whole family under a single challenge `α` — powers `α⁰..α²³` weight the
members — and checks the fold against `t · Z_H` by evaluation. The library's deterministic
surrogate for "a random `α`, a random evaluation point" is the usual pair of injectivity
hypotheses (`Quotient/Lift.lean`): enough distinct challenges pin each member by the
Vandermonde argument (`dvd_separation`), enough distinct nodes pin the polynomial identity
(`zH_dvd_of_evals`). Specializing the composed engine `dvd_of_evalCheck` at `fullFamily`
turns the shape of the one production check into per-member divisibility, and the
separation argument takes it the rest of the way to the rows. -/

/-- **Divisibility of every family member from the aggregated eval-check** — the
`dvd_of_evalCheck` engine at the full `21 + 3` family. -/
theorem fullFamily_dvd_of_evalCheck (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin 15 → F) (z : Polynomial F) (β γ : F)
    {N : ℕ} (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin (gateAlphaCount + permAlphaCount) → F) (hα : Function.Injective α)
    (t : Fin (gateAlphaCount + permAlphaCount) → Polynomial F)
    (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s,
      (aggregate (α s) (idx.fullFamily pub wTab z β γ)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p,
      (aggregate (α s) (idx.fullFamily pub wTab z β γ)).eval (ζ p)
        = (t s * zH F n).eval (ζ p)) :
    ∀ s, zH F n ∣ idx.fullFamily pub wTab z β γ s :=
  dvd_of_evalCheck idx.omega_prim (Nat.pos_of_neZero n) ζ hζ α hα _ t D hD
    hCdeg htdeg hcheck

/-- **Phase-B assembly, gate side.** The aggregated eval-check over the full family —
the shape of kimchi's one quotient check — gives every row's gate branch of
`rowSatisfies`: `dvd_of_evalCheck` pins each of the `21 + 3` members, and the
separation argument collapses the shared pool back to the rows. -/
theorem rowSatisfies_of_evalCheck (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin 15 → F) (z : Polynomial F) (β γ : F)
    {N : ℕ} (ζ : Fin N → F) (hζ : Function.Injective ζ)
    (α : Fin (gateAlphaCount + permAlphaCount) → F) (hα : Function.Injective α)
    (t : Fin (gateAlphaCount + permAlphaCount) → Polynomial F)
    (D : ℕ) (hD : D < N)
    (hCdeg : ∀ s,
      (aggregate (α s) (idx.fullFamily pub wTab z β γ)).natDegree ≤ D)
    (htdeg : ∀ s, (t s * zH F n).natDegree ≤ D)
    (hcheck : ∀ s p,
      (aggregate (α s) (idx.fullFamily pub wTab z β γ)).eval (ζ p)
        = (t s * zH F n).eval (ζ p))
    (hpubgen : ∀ i : Fin n, (i : ℕ) < idx.publicCount → (idx.gates i).typ = .generic) :
    ∀ i, rowSatisfies idx pub wTab i :=
  idx.rowSatisfies_of_fullFamily_dvd pub wTab z β γ hpubgen
    (idx.fullFamily_dvd_of_evalCheck pub wTab z β γ ζ hζ α hα t D hD hCdeg htdeg hcheck)

end Index

end Kimchi.Index
