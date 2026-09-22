import Kimchi.Index.CopySoundness
import Kimchi.SchwartzZippel

/-!
# The full kimchi aggregate family

The constraint family behind kimchi's one quotient check, as index data (transcribes
`linearization.rs`). All gate types share one pool of alpha powers `α⁰..α²⁰`, sized by the
largest gate (VarBaseMul's 21); sharing is sound because selectors are row-disjoint. The
permutation's three constraints hold on every row alongside the gates, so they take the next
three powers. The public input enters once, in the generic gate's `α⁰` slot: kimchi adds the
interpolant of the negated public inputs, so the slot-`0` member here subtracts the positive
interpolant. At a generic row this is the `Generic.withPublic` row semantics, one public
input per row in column `0` of the first `publicCount` rows.

The family has `21 + 3` members:

* member `k < 21`: the cross-gate sum `∑ g, selectorPoly g · E_{g,k}`, minus the public
  polynomial at `k = 0`; a gate with fewer than `k + 1` constraints contributes `0`;
* members `21..23`: the permutation constraints at the index's wiring data, for an
  accumulator `z` and challenge pair `(β, γ)`.

The per-gate lists are the gate transcriptions (`gateConstraints`). Selector one-hotness
recovers per-gate divisibility from the summed members (`eval_gateMember`).
-/

namespace Kimchi.Index

open Polynomial Kimchi.Lift
open Kimchi.GrandProduct
open Kimchi.Lift.Gate


variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ} [NeZero n]

omit [DecidableEq F] [NeZero n] in
/-- A selector value of `1` names the row's gate type. -/
private theorem selectorRow_eq_one (idx : Index F n) {g : GateType} {i : Fin n}
    (htyp : (idx.gates i).typ = g) : idx.selectorRow g i = 1 := by
  simp [selectorRow, htyp]

/-- The public-input interpolant: `pub i` at the public rows, `0` beyond. Kimchi adds its
negation into the generic `α⁰` slot. -/
noncomputable def pubPoly (idx : Index F n) (pub : Fin idx.publicCount → F) :
    Polynomial F :=
  columnPoly idx.omega (pubAt idx pub)

omit [DecidableEq F] [NeZero n] in
private theorem eval_pubPoly (idx : Index F n) (pub : Fin idx.publicCount → F) (i : Fin n) :
    (idx.pubPoly pub).eval (idx.omega ^ (i : ℕ)) = pubAt idx pub i :=
  eval_columnPoly idx.omega_prim _ i

/-- The constraint list of a gate type: its gate transcription over the index's column
interpolants. -/
noncomputable def gateConstraints (idx : Index F n) (wTab : Fin n → Fin wCols → F) :
    GateType → List (Polynomial F)
  | .zero => []
  | .generic => (Generic.argument (F := F)).constraints
      (polyEnv idx.omega wTab idx.coeffTable)
  | .poseidon => Gate.Poseidon.constraints (idx.mds.map C)
      (Poseidon.rcPoly idx.omega idx.coeffTable) (Poseidon.polyWitness idx.omega wTab)
  | .completeAdd => Gate.AddComplete.constraints (AddComplete.polyWitness idx.omega wTab)
  | .varBaseMul => Gate.VarBaseMul.constraints (VarBaseMul.polyWitness idx.omega wTab)
  | .endoMul => Gate.EndoMul.constraints (C idx.endoBase)
      (EndoMul.polyWitness idx.omega wTab)
  | .endoScalar => Gate.EndoScalar.constraints
      (EndoScalar.polyWitness idx.omega wTab) (F := F)

/-- The shared gate alpha-pool size: the largest gate's constraint count, VarBaseMul's 21. -/
@[reducible] def gateAlphaCount : ℕ := 21

/-- The permutation's alpha count: one power per permutation constraint. -/
@[reducible] def permAlphaCount : ℕ := 3

omit [DecidableEq F] [NeZero n] in
/-- The constraint count of each gate transcription. -/
private theorem gateConstraints_length (idx : Index F n) (wTab : Fin n → Fin wCols → F) :
    (idx.gateConstraints wTab .zero).length = 0
      ∧ (idx.gateConstraints wTab .generic).length = 2
      ∧ (idx.gateConstraints wTab .poseidon).length = 15
      ∧ (idx.gateConstraints wTab .completeAdd).length = 7
      ∧ (idx.gateConstraints wTab .varBaseMul).length = 21
      ∧ (idx.gateConstraints wTab .endoMul).length = 12
      ∧ (idx.gateConstraints wTab .endoScalar).length = 11 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The gate part of the aggregate member at power `k`: the cross-gate sum, minus the
public interpolant in the generic `α⁰` slot. -/
noncomputable def gateMember (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (k : ℕ) : Polynomial F :=
  (∑ g : GateType,
      columnPoly idx.omega (idx.selectorRow g) * (idx.gateConstraints wTab g).getD k 0)
    - if k = 0 then idx.pubPoly pub else 0

open Kimchi.Permutation in
/-- The `21 + 3` members of the one quotient check at an accumulator `z` and challenge
pair `(β, γ)`: the shared gate pool, then the three permutation constraints. -/
noncomputable def fullFamily (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (z : Polynomial F) (β γ : F) :
    Fin (gateAlphaCount + permAlphaCount) → Polynomial F :=
  fun k =>
    if h : (k : ℕ) < gateAlphaCount then
      idx.gateMember pub wTab k
    else
      Permutation.constraints idx.omega idx.zkRows z (idx.permWitnessPoly wTab)
        (Permutation.sigmaPoly idx.omega idx.zkRows idx.shifts idx.wiringPerm) idx.shifts β γ
        (⟨0, Nat.pos_of_neZero n⟩ : Fin n) idx.unmaskedEnd
        ⟨(k : ℕ) - gateAlphaCount, by
          have := k.isLt
          simp only [gateAlphaCount, permAlphaCount] at *
          omega⟩

/-! ## Separation: the shared pool collapses back to per-gate rows

`selectorRow` is one-hot at every row, so at a domain node the `k`-th summed member leaves
only the live gate's `k`-th constraint, minus the public value in slot `0`. Divisibility of
the 21 gate members therefore pins every constraint of each row's gate. Each gate's
`Argument.bridge` carries the polynomial identities to the cell equations of `rowSatisfies`;
the public subtraction lands on `Generic.withPublic_holds_iff`. -/

omit [DecidableEq F] [NeZero n] in
/-- The selector is `0` away from the row's own gate type. -/
private theorem selectorRow_eq_zero (idx : Index F n) {g : GateType} {i : Fin n}
    (htyp : (idx.gates i).typ ≠ g) : idx.selectorRow g i = 0 := by
  simp [selectorRow, htyp]

omit [DecidableEq F] [NeZero n] in
/-- Every gate's transcription fits inside the shared pool (VarBaseMul's 21). -/
theorem gateConstraints_length_le (idx : Index F n) (wTab : Fin n → Fin wCols → F)
    (g : GateType) : (idx.gateConstraints wTab g).length ≤ gateAlphaCount := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := idx.gateConstraints_length wTab
  cases g <;> simp [h0, h1, h2, h3, h4, h5, h6, gateAlphaCount]

omit [DecidableEq F] [NeZero n] in
/-- **Row collapse.** At a domain node, the `k`-th gate member evaluates to the live
gate's `k`-th constraint, minus the public value in slot `0`; every other gate's term dies
with its selector. -/
private theorem eval_gateMember (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (k : ℕ) (i : Fin n) :
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

omit [DecidableEq F] in
/-- A non-generic row's constraints all vanish when `zH` divides the gate members: the
slot-`0` public term is `0` there, by `public_generic`. -/
private theorem gateConstraints_vanish_of_dvd (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F)
    (hdvd : ∀ k, k < gateAlphaCount → zH F n ∣ idx.gateMember pub wTab k)
    {i : Fin n} (hne : (idx.gates i).typ ≠ .generic) :
    ∀ E ∈ idx.gateConstraints wTab (idx.gates i).typ,
      E.eval (idx.omega ^ (i : ℕ)) = 0 := by
  intro E hE
  obtain ⟨c, rfl⟩ := List.mem_iff_get.mp hE
  have hk : (c : ℕ) < gateAlphaCount :=
    lt_of_lt_of_le c.isLt (idx.gateConstraints_length_le wTab _)
  have h := (zH_dvd_iff idx.omega_prim (Nat.pos_of_neZero n) _).mp (hdvd c hk)
    (i : ℕ) i.isLt
  rw [idx.eval_gateMember] at h
  have hpub0 : pubAt idx pub i = 0 := by
    unfold pubAt
    exact dif_neg fun hlt => hne (idx.public_generic i hlt)
  rw [hpub0, ite_self, sub_zero] at h
  rwa [List.getD_eq_getElem _ _ c.isLt, ← List.get_eq_getElem] at h

omit [DecidableEq F] in
/-- A generic row's public-folded gate holds when `zH` divides the gate members: slots
`0` and `1` pin the two generic constraints, the first to the public value. -/
private theorem generic_holds_of_dvd (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F)
    (hdvd : ∀ k, k < gateAlphaCount → zH F n ∣ idx.gateMember pub wTab k)
    {i : Fin n} (htyp : (idx.gates i).typ = .generic) :
    Gate.Generic.Holds
      (Gate.Generic.withPublic ⟨idx.coeffTable i, wTab i⟩ (pubAt idx pub i)) := by
  have hslot : ∀ k : ℕ, k < gateAlphaCount →
      ((idx.gateConstraints wTab .generic).getD k 0).eval (idx.omega ^ (i : ℕ))
        = if k = 0 then pubAt idx pub i else 0 := by
    intro k hk
    have h := (zH_dvd_iff idx.omega_prim (Nat.pos_of_neZero n) _).mp (hdvd k hk)
      (i : ℕ) i.isLt
    rw [idx.eval_gateMember, htyp] at h
    exact sub_eq_zero.mp h
  rw [Gate.Generic.withPublic_holds_iff]
  have hb := (Generic.argument (F := F)).bridge idx.omega_prim wTab idx.coeffTable i
  simp only [Generic.argument, Generic.cellMap, Gate.Generic.constraints, List.map_cons,
    List.map_nil, List.cons.injEq, and_true] at hb
  obtain ⟨hb1, hb2⟩ := hb
  have h0 := hslot 0 (by norm_num [gateAlphaCount])
  have h1 := hslot 1 (by norm_num [gateAlphaCount])
  simp only [gateConstraints, Generic.argument, Generic.cellMap, Gate.Generic.constraints,
    List.getD_cons_zero, List.getD_cons_succ, if_pos, one_ne_zero,
    ite_false] at h0 h1
  exact ⟨hb1 ▸ h0, hb2 ▸ h1⟩

omit [DecidableEq F] in
/-- Transport row-constraint vanishing along a gate's eval bridge. -/
private theorem forall_mem_zero_of_bridge {P : List (Polynomial F)} {L : List F} {x : F}
    (hb : P.map (·.eval x) = L) (hvan : ∀ E ∈ P, E.eval x = 0) :
    ∀ e ∈ L, e = 0 :=
  hb ▸ List.forall_mem_map.mpr hvan

omit [DecidableEq F] in
/-- **Gate separation.** If `zH` divides all 21 gate members, every row satisfies its
gate branch of `rowSatisfies`. -/
private theorem rowSatisfies_of_gateMember_dvd (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F)
    (hdvd : ∀ k, k < gateAlphaCount → zH F n ∣ idx.gateMember pub wTab k) :
    ∀ i, rowSatisfies idx pub wTab i := by
  intro i
  unfold rowSatisfies
  cases htyp : (idx.gates i).typ with
  | zero => trivial
  | generic => exact idx.generic_holds_of_dvd pub wTab hdvd htyp
  | poseidon =>
    have hvan := idx.gateConstraints_vanish_of_dvd pub wTab hdvd (i := i) (by simp [htyp])
    rw [htyp] at hvan
    exact forall_mem_zero_of_bridge
      ((Poseidon.argument idx.mds).bridge idx.omega_prim wTab idx.coeffTable i) hvan
  | completeAdd =>
    have hvan := idx.gateConstraints_vanish_of_dvd pub wTab hdvd (i := i) (by simp [htyp])
    rw [htyp] at hvan
    exact forall_mem_zero_of_bridge
      ((AddComplete.argument (F := F)).bridge idx.omega_prim wTab idx.coeffTable i) hvan
  | varBaseMul =>
    have hvan := idx.gateConstraints_vanish_of_dvd pub wTab hdvd (i := i) (by simp [htyp])
    rw [htyp] at hvan
    exact forall_mem_zero_of_bridge
      ((VarBaseMul.argument (F := F)).bridge idx.omega_prim wTab idx.coeffTable i) hvan
  | endoMul =>
    have hvan := idx.gateConstraints_vanish_of_dvd pub wTab hdvd (i := i) (by simp [htyp])
    rw [htyp] at hvan
    exact forall_mem_zero_of_bridge
      ((EndoMul.argument idx.endoBase).bridge idx.omega_prim wTab idx.coeffTable i) hvan
  | endoScalar =>
    have hvan := idx.gateConstraints_vanish_of_dvd pub wTab hdvd (i := i) (by simp [htyp])
    rw [htyp] at hvan
    exact forall_mem_zero_of_bridge
      ((EndoScalar.argument (F := F)).bridge idx.omega_prim wTab idx.coeffTable i) hvan

omit [DecidableEq F] in
/-- The gate branches of `rowSatisfies` from divisibility of `fullFamily`, whose first
`gateAlphaCount` entries are the gate members. -/
private theorem rowSatisfies_of_fullFamily_dvd (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (z : Polynomial F) (β γ : F)
    (hdvd : ∀ s, zH F n ∣ idx.fullFamily pub wTab z β γ s) :
    ∀ i, rowSatisfies idx pub wTab i :=
  idx.rowSatisfies_of_gateMember_dvd pub wTab fun k hk => by
    have h := hdvd ⟨k, by omega⟩
    rwa [fullFamily, dif_pos hk] at h

/-! ## Alpha instantiation: the one quotient check

Kimchi folds the family under one challenge `α`, weighting the members by `α⁰..α²³`, and
checks the fold against `t · zH` at one evaluation point `ζ`. The counting Schwartz–Zippel
argument of `Kimchi.SchwartzZippel` makes this deterministic: one `α` outside `badAlphas`
(at most `n · (K − 1)` values, `card_badAlphas_le`), one quotient `t` and one `ζ` outside
`badZetas` give divisibility of every member (`dvd_of_evalCheck`). The separation argument
takes that to the rows. -/

/-- Every member of `fullFamily` is `zH`-divisible once the aggregated eval-check passes:
`dvd_of_evalCheck` at this family. -/
private theorem fullFamily_dvd_of_evalCheck (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (z : Polynomial F) (β γ : F)
    (α : F) (hα : α ∉ badAlphas (idx.fullFamily pub wTab z β γ) idx.omega n)
    (t : Polynomial F)
    (ζ : F)
    (hζ : ζ ∉ badZetas (aggregate α (idx.fullFamily pub wTab z β γ)) t n)
    (hcheck : (aggregate α (idx.fullFamily pub wTab z β γ)).eval ζ
        = (t * zH F n).eval ζ) :
    ∀ s, zH F n ∣ idx.fullFamily pub wTab z β γ s :=
  dvd_of_evalCheck idx.omega_prim (idx.fullFamily pub wTab z β γ) α hα t ζ hζ hcheck

open Kimchi.Permutation in
omit [DecidableEq F] in
/-- Entries `21 + s` of `fullFamily` are the three permutation constraints. -/
private theorem fullFamily_perm (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (z : Polynomial F) (β γ : F) (s : Fin 3) :
    idx.fullFamily pub wTab z β γ (Fin.natAdd gateAlphaCount s)
      = Permutation.constraints idx.omega idx.zkRows z (idx.permWitnessPoly wTab)
          (Permutation.sigmaPoly idx.omega idx.zkRows idx.shifts idx.wiringPerm) idx.shifts β γ
          (⟨0, Nat.pos_of_neZero n⟩ : Fin n) idx.unmaskedEnd s := by
  rw [fullFamily, dif_neg (by show ¬gateAlphaCount + (s : ℕ) < gateAlphaCount; omega)]
  congr 1
  exact Fin.ext (by simp [Fin.natAdd])

open Kimchi.Permutation in
/-- **Copy-side assembly.** At a challenge pair `(β, γ)` outside `badBetas` / `badGammas`,
an accumulator whose `fullFamily` is `zH`-divisible forces equal values across every wire
of the unmasked region: `Index.copy_soundness_of_dvd` at the last three members. -/
private theorem copy_of_fullFamily_dvd (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F)
    (β γ : F)
    (hβ : β ∉ badBetas
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts (restrictCells idx.wiringPerm idx.wiring_region c).1
            * idx.omega
              ^ ((restrictCells idx.wiringPerm idx.wiring_region c).2 : ℕ))))
    (hγ : γ ∉ badGammas
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts (restrictCells idx.wiringPerm idx.wiring_region c).1
            * idx.omega
              ^ ((restrictCells idx.wiringPerm idx.wiring_region c).2 : ℕ))) β)
    (zg : Polynomial F)
    (hdvd : ∀ s, zH F n ∣ idx.fullFamily pub wTab zg β γ s) :
    ∀ c : Fin permCols × Fin (n - idx.zkRows),
      cellValue wTab (idx.wiringMap (embCell idx.zkRows c))
        = cellValue wTab (embCell idx.zkRows c) :=
  idx.copy_soundness_of_dvd wTab β γ hβ hγ zg fun s => by
    have h := hdvd (Fin.natAdd gateAlphaCount s)
    rwa [idx.fullFamily_perm] at h

/-! ## The satisfiability headline: the one quotient check gives satisfiability

The 21 gate members give every row's gate branch (`rowSatisfies`); the three permutation
members give the copy constraints on the unmasked region, and the `masked_identity` law
extends them over the zero-knowledge rows; the `public_generic` and `public_coeffs` laws
turn the slot-`0` member at the public rows into the public pinning. Together these are
`Satisfies`. -/

open Kimchi.Permutation in
/-- The whole-grid copy conjunct: the unmasked region from the permutation members, the
masked rows from the `masked_identity` law. -/
private theorem copyAll_of_fullFamily_dvd (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F)
    (β γ : F)
    (hβ : β ∉ badBetas
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts (restrictCells idx.wiringPerm idx.wiring_region c).1
            * idx.omega
              ^ ((restrictCells idx.wiringPerm idx.wiring_region c).2 : ℕ))))
    (hγ : γ ∉ badGammas
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts (restrictCells idx.wiringPerm idx.wiring_region c).1
            * idx.omega
              ^ ((restrictCells idx.wiringPerm idx.wiring_region c).2 : ℕ))) β)
    (zg : Polynomial F)
    (hdvd : ∀ s, zH F n ∣ idx.fullFamily pub wTab zg β γ s) :
    ∀ c : Fin permCols × Fin n, cellValue wTab (idx.wiringMap c) = cellValue wTab c := by
  intro c
  by_cases hc : (c.2 : ℕ) < n - idx.zkRows
  · have h := idx.copy_of_fullFamily_dvd pub wTab β γ hβ hγ zg hdvd
      (c.1, ⟨(c.2 : ℕ), hc⟩)
    have hemb : embCell idx.zkRows ((c.1, ⟨(c.2 : ℕ), hc⟩) :
        Fin permCols × Fin (n - idx.zkRows)) = c := Prod.ext rfl (Fin.ext rfl)
    rwa [hemb] at h
  · rw [show idx.wiringMap c = c from idx.masked_identity c (Nat.le_of_not_lt hc)]

omit [DecidableEq F] in
/-- The public-pinning conjunct: at a public row, the `public_coeffs` law collapses the
generic slot-`0` equation to `wTab i 0 = pub i`. -/
private theorem publicPinned_of_rowSatisfies (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (hrow : ∀ i, rowSatisfies idx pub wTab i) :
    ∀ i : Fin idx.publicCount,
      wTab ⟨(i : ℕ), by have h1 := idx.public_le; have h2 := idx.zk_le; omega⟩ 0
        = pub i := by
  intro i
  set r : Fin n :=
    ⟨(i : ℕ), by have h1 := idx.public_le; have h2 := idx.zk_le; omega⟩ with hr
  have hlt : (r : ℕ) < idx.publicCount := i.isLt
  have hgen := idx.public_generic r hlt
  have h := hrow r
  unfold rowSatisfies at h
  rw [hgen] at h
  have h1 := ((Gate.Generic.withPublic_holds_iff ⟨idx.coeffTable r, wTab r⟩ _).mp h).1
  have hq0 : idx.coeffTable r 0 = 1 := by
    show (idx.gates r).coeffs 0 = 1
    rw [idx.public_coeffs r hlt 0]; exact if_pos rfl
  have hq1 : idx.coeffTable r 1 = 0 := by
    show (idx.gates r).coeffs 1 = 0
    rw [idx.public_coeffs r hlt 1]; exact if_neg (by decide)
  have hq2 : idx.coeffTable r 2 = 0 := by
    show (idx.gates r).coeffs 2 = 0
    rw [idx.public_coeffs r hlt 2]; exact if_neg (by decide)
  have hq3 : idx.coeffTable r 3 = 0 := by
    show (idx.gates r).coeffs 3 = 0
    rw [idx.public_coeffs r hlt 3]; exact if_neg (by decide)
  have hq4 : idx.coeffTable r 4 = 0 := by
    show (idx.gates r).coeffs 4 = 0
    rw [idx.public_coeffs r hlt 4]; exact if_neg (by decide)
  have hpub : pubAt idx pub r = pub i := by
    unfold pubAt
    rw [dif_pos hlt]
  rw [← hpub]
  linear_combination (h1.symm.trans (by simp only [hq0, hq1, hq2, hq3, hq4]; ring)).symm

open Kimchi.Permutation in
/-- **Satisfiability, divisibility form.** At a challenge pair `(β, γ)` outside
`badBetas` / `badGammas`, an accumulator whose `fullFamily` is `zH`-divisible gives
`Satisfies idx pub wTab`. -/
private theorem satisfies_of_fullFamily_dvd (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F)
    (β γ : F)
    (hβ : β ∉ badBetas
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts (restrictCells idx.wiringPerm idx.wiring_region c).1
            * idx.omega
              ^ ((restrictCells idx.wiringPerm idx.wiring_region c).2 : ℕ))))
    (hγ : γ ∉ badGammas
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts (restrictCells idx.wiringPerm idx.wiring_region c).1
            * idx.omega
              ^ ((restrictCells idx.wiringPerm idx.wiring_region c).2 : ℕ))) β)
    (zg : Polynomial F)
    (hdvd : ∀ s, zH F n ∣ idx.fullFamily pub wTab zg β γ s) :
    Satisfies idx pub wTab := by
  have hrow : ∀ i, rowSatisfies idx pub wTab i :=
    idx.rowSatisfies_of_fullFamily_dvd pub wTab zg β γ hdvd
  exact ⟨hrow,
    idx.copyAll_of_fullFamily_dvd pub wTab β γ hβ hγ zg hdvd,
    idx.publicPinned_of_rowSatisfies pub wTab hrow⟩

open Kimchi.Permutation in
/-- **The satisfiability headline.** At a challenge pair `(β, γ)` outside the counted bad
sets, an accumulator whose aggregated `fullFamily` passes the eval-check against `t · zH`
at a good `(α, ζ)` gives `Satisfies idx pub wTab`. -/
theorem satisfies_of_evalCheck (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F)
    (β γ : F)
    (hβ : β ∉ badBetas
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts (restrictCells idx.wiringPerm idx.wiring_region c).1
            * idx.omega
              ^ ((restrictCells idx.wiringPerm idx.wiring_region c).2 : ℕ))))
    (hγ : γ ∉ badGammas
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
      (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
        ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
          idx.shifts (restrictCells idx.wiringPerm idx.wiring_region c).1
            * idx.omega
              ^ ((restrictCells idx.wiringPerm idx.wiring_region c).2 : ℕ))) β)
    (zg : Polynomial F)
    (α : F)
    (hα : α ∉ badAlphas (idx.fullFamily pub wTab zg β γ) idx.omega n)
    (t : Polynomial F)
    (ζ : F)
    (hζ : ζ ∉ badZetas (aggregate α (idx.fullFamily pub wTab zg β γ)) t n)
    (hcheck : (aggregate α (idx.fullFamily pub wTab zg β γ)).eval ζ
        = (t * zH F n).eval ζ) :
    Satisfies idx pub wTab :=
  idx.satisfies_of_fullFamily_dvd pub wTab β γ hβ hγ zg
    (idx.fullFamily_dvd_of_evalCheck pub wTab zg β γ α hα t ζ hζ hcheck)

/-! ## Completeness: the gate members of a satisfied table

The converse of the separation argument. At a satisfied row the live gate's constraints
vanish, the generic slot `0` carrying exactly the public value the member subtracts, and
every other gate's term dies with its selector. So every gate member vanishes on the whole
domain and is divisible by `zH`. -/

omit [DecidableEq F] in
/-- Transport row-constraint vanishing back across a gate's eval bridge. -/
private theorem forall_mem_eval_of_bridge {P : List (Polynomial F)} {L : List F} {x : F}
    (hb : P.map (·.eval x) = L) (hall : ∀ e ∈ L, e = 0) :
    ∀ E ∈ P, E.eval x = 0 :=
  List.forall_mem_map.mp (hb.symm ▸ hall)

omit [DecidableEq F] in
/-- A `List.getD` slot of a list of vanishing evaluations vanishes; out of range it is
the zero default. -/
private theorem eval_getD_zero_of_vanish {P : List (Polynomial F)} {x : F}
    (h : ∀ E ∈ P, E.eval x = 0) (k : ℕ) : (P.getD k 0).eval x = 0 := by
  rcases Nat.lt_or_ge k P.length with hk | hk
  · rw [List.getD_eq_getElem _ _ hk]
    exact h _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ hk, eval_zero]

omit [DecidableEq F] in
/-- A satisfied non-generic row's constraints all vanish: the converse of
`gateConstraints_vanish_of_dvd`. -/
private theorem gateConstraints_vanish_of_rowSatisfies (idx : Index F n)
    (pub : Fin idx.publicCount → F) (wTab : Fin n → Fin wCols → F) {i : Fin n}
    (hrow : rowSatisfies idx pub wTab i) (hne : (idx.gates i).typ ≠ .generic) :
    ∀ E ∈ idx.gateConstraints wTab (idx.gates i).typ,
      E.eval (idx.omega ^ (i : ℕ)) = 0 := by
  unfold rowSatisfies at hrow
  cases htyp : (idx.gates i).typ with
  | zero => simp [gateConstraints]
  | generic => exact absurd htyp hne
  | poseidon =>
    rw [htyp] at hrow
    exact forall_mem_eval_of_bridge
      ((Poseidon.argument idx.mds).bridge idx.omega_prim wTab idx.coeffTable i) hrow
  | completeAdd =>
    rw [htyp] at hrow
    exact forall_mem_eval_of_bridge
      ((AddComplete.argument (F := F)).bridge idx.omega_prim wTab idx.coeffTable i) hrow
  | varBaseMul =>
    rw [htyp] at hrow
    exact forall_mem_eval_of_bridge
      ((VarBaseMul.argument (F := F)).bridge idx.omega_prim wTab idx.coeffTable i) hrow
  | endoMul =>
    rw [htyp] at hrow
    exact forall_mem_eval_of_bridge
      ((EndoMul.argument idx.endoBase).bridge idx.omega_prim wTab idx.coeffTable i) hrow
  | endoScalar =>
    rw [htyp] at hrow
    exact forall_mem_eval_of_bridge
      ((EndoScalar.argument (F := F)).bridge idx.omega_prim wTab idx.coeffTable i) hrow

omit [DecidableEq F] in
/-- **Row completeness.** Every gate member evaluates to `0` at a satisfied row. -/
private theorem eval_gateMember_of_rowSatisfies (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) {i : Fin n}
    (hrow : rowSatisfies idx pub wTab i) (k : ℕ) :
    (idx.gateMember pub wTab k).eval (idx.omega ^ (i : ℕ)) = 0 := by
  rw [idx.eval_gateMember]
  by_cases hgen : (idx.gates i).typ = .generic
  · -- the generic slots carry the public-folded equations
    unfold rowSatisfies at hrow
    rw [hgen] at hrow
    obtain ⟨h1, h2⟩ := (Gate.Generic.withPublic_holds_iff _ _).mp hrow
    have hb := (Generic.argument (F := F)).bridge idx.omega_prim wTab idx.coeffTable i
    simp only [Generic.argument, Generic.cellMap, Gate.Generic.constraints, List.map_cons,
      List.map_nil, List.cons.injEq, and_true] at hb
    obtain ⟨hb1, hb2⟩ := hb
    rw [hgen]
    match k with
    | 0 =>
      simp only [gateConstraints, Generic.argument, Generic.cellMap,
        Gate.Generic.constraints, List.getD_cons_zero, ite_true]
      exact sub_eq_zero.mpr (hb1.trans h1)
    | 1 =>
      simp only [gateConstraints, Generic.argument, Generic.cellMap,
        Gate.Generic.constraints, List.getD_cons_succ, List.getD_cons_zero,
        Nat.one_ne_zero, ite_false, sub_zero]
      exact hb2.trans h2
    | (m + 2) =>
      simp only [gateConstraints, Generic.argument, Generic.cellMap,
        Gate.Generic.constraints, List.getD_cons_succ, List.getD_nil, eval_zero,
        Nat.succ_ne_zero, ite_false, sub_zero]
  · -- non-generic rows: all slots vanish and the public term is 0
    have hpub0 : pubAt idx pub i = 0 := by
      unfold pubAt
      exact dif_neg fun hlt => hgen (idx.public_generic i hlt)
    rw [hpub0, ite_self, sub_zero]
    exact eval_getD_zero_of_vanish
      (idx.gateConstraints_vanish_of_rowSatisfies pub wTab hrow hgen) k

omit [DecidableEq F] in
/-- **Gate-member completeness.** Every gate member of a satisfied table is divisible by
`zH`, at every slot. -/
private theorem gateMember_dvd_of_rowSatisfies (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F)
    (hrow : ∀ i, rowSatisfies idx pub wTab i) (k : ℕ) :
    zH F n ∣ idx.gateMember pub wTab k := by
  rw [zH_dvd_iff idx.omega_prim (Nat.pos_of_neZero n)]
  intro i hi
  exact idx.eval_gateMember_of_rowSatisfies pub wTab (hrow ⟨i, hi⟩) k


/-! ## Completeness: the permutation members and the headline

A satisfied table admits honest quotient data at every nondegenerate challenge pair. The
copy conjunct gives the grand-product identity by reindexing, and the honest accumulator
telescopes it through the three permutation constraints. No challenge grid is needed. -/

open Kimchi.Permutation in
omit [DecidableEq F] in
/-- **Permutation completeness.** At a nondegenerate `(β, γ)`, a copy-invariant witness
admits an accumulator whose three permutation constraints are `zH`-divisible. -/
private theorem permConstraints_dvd_of_copy (idx : Index F n) (wTab : Fin n → Fin wCols → F)
    (β γ : F)
    (hnd : Nondegenerate idx.omega idx.zkRows (idx.permWitnessPoly wTab) idx.shifts
      idx.wiringPerm β γ)
    (hcopy : ∀ c : Fin permCols × Fin n,
      cellValue wTab (idx.wiringMap c) = cellValue wTab c) :
    ∃ z : Polynomial F, ∀ s, zH F n ∣ Permutation.constraints idx.omega idx.zkRows z
      (idx.permWitnessPoly wTab)
      (Permutation.sigmaPoly idx.omega idx.zkRows idx.shifts idx.wiringPerm) idx.shifts β γ
      (⟨0, Nat.pos_of_neZero n⟩ : Fin n) idx.unmaskedEnd s := by
  have hcopy' : ∀ c : Fin permCols × Fin (n - idx.zkRows),
      ((idx.permWitnessPoly wTab) (idx.wiringPerm (embCell idx.zkRows c)).1).eval
          (idx.omega ^ (((idx.wiringPerm (embCell idx.zkRows c)).2 : Fin n) : ℕ))
        = ((idx.permWitnessPoly wTab) c.1).eval (idx.omega ^ ((c.2 : ℕ))) := by
    intro c
    rw [idx.eval_permWitnessPoly,
      show (idx.omega ^ ((c.2 : ℕ)) : F)
        = idx.omega ^ (((embCell idx.zkRows c).2 : Fin n) : ℕ) from rfl,
      idx.eval_permWitnessPoly]
    simpa using hcopy (embCell idx.zkRows c)
  exact constraints_dvd_of_prods idx.omega_prim (Nat.pos_of_neZero n)
    (by have := idx.zk_three; omega : 2 ≤ idx.zkRows)
    idx.zk_le _ _ idx.shifts β γ
    (fun j hj => sigmaSide_eval_ne_zero idx.omega_prim hnd hj)
    (prod_shiftSide_eq_prod_sigmaSide idx.omega_prim _ idx.shifts idx.wiringPerm
      idx.wiring_region β γ hcopy')

omit [DecidableEq F] in
/-- The gate members of the full family: the entries below `gateAlphaCount`. -/
private theorem fullFamily_gate (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (z : Polynomial F) (β γ : F)
    (k : Fin (gateAlphaCount + permAlphaCount)) (hk : (k : ℕ) < gateAlphaCount) :
    idx.fullFamily pub wTab z β γ k = idx.gateMember pub wTab k := by
  rw [fullFamily, dif_pos hk]

open Kimchi.Permutation in
omit [DecidableEq F] in
/-- **The completeness headline.** At every nondegenerate challenge pair, a satisfied table
admits an accumulator `z` making all of `fullFamily` `zH`-divisible. The converse of
`satisfies_of_fullFamily_dvd`. -/
private theorem fullFamily_dvd_of_satisfies (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F)
    (hsat : Satisfies idx pub wTab) (β γ : F)
    (hnd : Nondegenerate idx.omega idx.zkRows (idx.permWitnessPoly wTab) idx.shifts
      idx.wiringPerm β γ) :
    ∃ z : Polynomial F, ∀ s, zH F n ∣ idx.fullFamily pub wTab z β γ s := by
  obtain ⟨hrow, hcopy, -⟩ := hsat
  obtain ⟨z, hz⟩ := idx.permConstraints_dvd_of_copy wTab β γ hnd hcopy
  refine ⟨z, fun s => ?_⟩
  by_cases hk : (s : ℕ) < gateAlphaCount
  · rw [idx.fullFamily_gate pub wTab z β γ s hk]
    exact idx.gateMember_dvd_of_rowSatisfies pub wTab hrow s
  · obtain ⟨j, rfl⟩ : ∃ j : Fin 3, s = Fin.natAdd gateAlphaCount j := by
      refine ⟨⟨(s : ℕ) - gateAlphaCount, ?_⟩, Fin.ext ?_⟩
      · have := s.isLt
        simp only [gateAlphaCount, permAlphaCount] at *
        omega
      · simp only [Fin.natAdd]
        omega
    rw [idx.fullFamily_perm]
    exact hz j


/-! ## Project-local Mathlib supplement — pigeonhole on an injective family -/

omit [Field F] in
/-- An injective family `f : Fin m → F` has some value outside any finset `B` with
`B.card < m`. -/
private theorem exists_notMem_of_card_lt {m : ℕ} {f : Fin m → F}
    (hf : Function.Injective f) (B : Finset F) (hB : B.card < m) :
    ∃ i, f i ∉ B := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ.image f) ⊆ B := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact h i
  have hcard : (Finset.univ.image f).card = m := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have := Finset.card_le_card hsub
  omega

/-! ## The characterization: satisfiability as one divisibility -/

open Kimchi.Permutation in
/-- **The characterization.** In a large enough field, a table satisfies the index iff
honest quotient data exists at every nondegenerate challenge pair. Backward picks a good
pair from a nondegenerate grid (`exists_nondegenerate_grid`) by pigeonhole and applies
`satisfies_of_fullFamily_dvd`. The field bound `hF` sizes that grid; `Nondegenerate` says
why it ranges over all `n` rows; `hF` holds at Pasta sizes. -/
theorem satisfies_iff_fullFamily_dvd [Fintype F] (idx : Index F n)
    (pub : Fin idx.publicCount → F) (wTab : Fin n → Fin wCols → F)
    (hF : (7 * n + 1) * (7 * n + 1) ≤ Fintype.card F) :
    Satisfies idx pub wTab
      ↔ ∀ β γ, Nondegenerate idx.omega idx.zkRows (idx.permWitnessPoly wTab)
          idx.shifts idx.wiringPerm β γ →
          ∃ z : Polynomial F, ∀ s, zH F n ∣ idx.fullFamily pub wTab z β γ s := by
  constructor
  · exact fun hsat β γ hnd => idx.fullFamily_dvd_of_satisfies pub wTab hsat β γ hnd
  · intro h
    obtain ⟨b, g, hb, hg, hnd⟩ := exists_nondegenerate_grid idx.zkRows
      (idx.permWitnessPoly wTab) idx.shifts idx.wiringPerm hF (ω := idx.omega)
    -- the (value, address) pair multisets of the index wiring (as in `copy_soundness_of_dvd`)
    have hcard₁ : Multiset.card
        (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
          ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
            idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
          = 7 * (n - idx.zkRows) := by
      rw [Multiset.card_map]
      show (Finset.univ : Finset (Fin permCols × Fin (n - idx.zkRows))).card = _
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have hcard₂ : Multiset.card
        (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
          ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
            idx.shifts (restrictCells idx.wiringPerm idx.wiring_region c).1
              * idx.omega
                ^ ((restrictCells idx.wiringPerm idx.wiring_region c).2 : ℕ)))
          = 7 * (n - idx.zkRows) := by
      rw [Multiset.card_map]
      show (Finset.univ : Finset (Fin permCols × Fin (n - idx.zkRows))).card = _
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    -- pigeonhole: the bad sets have card ≤ 7·(n−zkRows) < 7·(n−zkRows)+1, so the
    -- injective grid families `b`, `g` each hit a good challenge outside them.
    obtain ⟨a, ha⟩ := exists_notMem_of_card_lt hb
      (badBetas
        (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
          ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
            idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
        (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
          ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
            idx.shifts (restrictCells idx.wiringPerm idx.wiring_region c).1
              * idx.omega
                ^ ((restrictCells idx.wiringPerm idx.wiring_region c).2 : ℕ))))
      (by
        refine lt_of_le_of_lt (card_badBetas_le _ _) ?_
        rw [hcard₁, hcard₂]
        omega)
    obtain ⟨c, hc⟩ := exists_notMem_of_card_lt hg
      (badGammas
        (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
          ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
            idx.shifts c.1 * idx.omega ^ (c.2 : ℕ)))
        (Finset.univ.val.map fun c : Fin permCols × Fin (n - idx.zkRows) =>
          ((idx.permWitnessPoly wTab c.1).eval (idx.omega ^ (c.2 : ℕ)),
            idx.shifts (restrictCells idx.wiringPerm idx.wiring_region c).1
              * idx.omega
                ^ ((restrictCells idx.wiringPerm idx.wiring_region c).2 : ℕ)))
        (b a))
      (by
        refine lt_of_le_of_lt (card_badGammas_le _ _ _) ?_
        rw [hcard₁, hcard₂]
        omega)
    obtain ⟨z, hz⟩ := h (b a) (g c) (hnd a c)
    exact idx.satisfies_of_fullFamily_dvd pub wTab (b a) (g c) ha hc z hz


end Kimchi.Index
