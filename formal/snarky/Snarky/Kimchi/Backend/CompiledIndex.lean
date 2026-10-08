import Snarky.Kimchi.Backend.IndexSpec

/-!
# The index of a compiled circuit

`compiledIndex?` builds a kimchi index from a compiled source's own gate table, and
`compiledIndex?_indexOf` proves that the index it returns is that source's: every successful
construction satisfies `IndexOf`, the premise the lifting theorems take. Construction can
fail, and nothing here says it succeeds.

The construction has three stages. `gateTable?` turns the assembled gate list into a table on
the domain, preserving it exactly: it rejects a list longer than the domain, a row with more
coefficients than the coefficient columns, and a wire target outside the table, rather than
truncating or reducing any of them, and pads the remaining rows with zero gates wired to
themselves. `indexOfGates?` checks that every constraint's parameters are the index's and that
the rows fit before the masked rows, then hands the table to `Index.build?`, which checks the
rest. `compiledIndex?` applies it to the source's assembled gates.

## Main definitions

- `gateTable?`: an assembled gate list as a table on the domain.
- `indexOfGates?`, `compiledIndex?`: the index of a gate list, and of a compiled source.

## Main results

- `gateTable?_isSome_iff`, `gateTable?_padding`: when the table is built, and what its
  padding rows are.
- `compiledIndex?_indexOf`: the index a successful construction returns is the source's.
- `gateDataOf_reduceBuilt`: a built circuit's gates are its source's, whatever its result.

## Implementation notes

The table reads an array built once from the converted rows, since `Index.build?` reads the
table many times; `arrayTable` keeps the array out of the returned function's body, where the
compiler would rebuild it on every read. The parameters, the domain size and the masked-row
count are the caller's, as a deployment fixes them. The assembly's wiring goes through a hash
map the kernel cannot evaluate; the checks decide concrete instances through the class-based
gates, `directGates_eq_classGates`, which this module does not import.
-/

open Kimchi Kimchi.Index

namespace Snarky.Kimchi

open Snarky

variable {F : Type}

/-! ## The gate table -/

section Table

variable [Zero F]

/-- A padding row: a zero gate with zero coefficients, each cell wired to itself. -/
private def zeroGateRow {n : ℕ} (i : Fin n) : GateRow F n :=
  { typ := .zero, coeffs := fun _ => 0, wires := fun c => (c, i) }

/-- An emitted row's conditions on a table of `n` rows: no more coefficients than the
coefficient columns, and every wire target inside the table. -/
private def RowFits (n : ℕ) (g : AssembledGate F) : Prop :=
  g.coeffs.length ≤ coeffCols ∧ ∀ c : Fin permCols, g.wires[c].col < permCols ∧ g.wires[c].row < n

private instance (n : ℕ) (g : AssembledGate F) : Decidable (RowFits n g) := by
  unfold RowFits
  infer_instance

/-- An emitted row as a table row, `none` when it does not fit the table. -/
private def gateRow? (n : ℕ) (g : AssembledGate F) : Option (GateRow F n) :=
  if h : RowFits n g then
    some { typ := g.kind, coeffs := fun c => g.coeffs.getD c.val 0,
           wires := fun c => (⟨g.wires[c].col, (h.2 c).1⟩, ⟨g.wires[c].row, (h.2 c).2⟩) }
  else none

/-- The emitted rows converted and pushed onto `acc`, `none` when one does not fit: a loop, so
that a table of any size takes no stack. -/
private def gateRowsInto (n : ℕ) : Array (GateRow F n) → List (AssembledGate F) →
    Option (Array (GateRow F n))
  | acc, [] => some acc
  | acc, g :: gs =>
    match gateRow? n g with
    | some r => gateRowsInto n (acc.push r) gs
    | none => none

private theorem gateRow?_isSome_iff (n : ℕ) (g : AssembledGate F) :
    (gateRow? n g).isSome ↔ RowFits n g := by
  unfold gateRow?
  split <;> simp_all

private theorem gateRow?_eq_some {n : ℕ} {g : AssembledGate F} {r : GateRow F n}
    (h : gateRow? n g = some r) :
    r.typ = g.kind ∧ (∀ c : Fin coeffCols, r.coeffs c = g.coeffs.getD c.val 0) ∧
      ∀ c : Fin permCols,
        (r.wires c).1.val = g.wires[c].col ∧ (r.wires c).2.val = g.wires[c].row := by
  unfold gateRow? at h
  split at h
  · cases h
    exact ⟨rfl, fun _ => rfl, fun _ => ⟨rfl, rfl⟩⟩
  · cases h

private theorem gateRowsInto_isSome_iff (n : ℕ) :
    (acc : Array (GateRow F n)) → (gs : List (AssembledGate F)) →
      ((gateRowsInto n acc gs).isSome ↔ ∀ g ∈ gs, RowFits n g)
  | acc, [] => by simp [gateRowsInto]
  | acc, g :: gs => by
    rw [List.forall_mem_cons, ← gateRow?_isSome_iff, gateRowsInto.eq_2]
    cases h : gateRow? n g with
    | none => simp
    | some r =>
      simp only [Option.isSome_some, true_and]
      exact gateRowsInto_isSome_iff n (acc.push r) gs

private theorem gateRowsInto_eq_some (n : ℕ) :
    (acc : Array (GateRow F n)) → (gs : List (AssembledGate F)) → (arr : Array (GateRow F n)) →
      gateRowsInto n acc gs = some arr →
      ∃ hsize : arr.size = acc.size + gs.length,
        (∀ (i : ℕ) (hi : i < acc.size), arr[i]'(by omega) = acc[i]) ∧
        ∀ (i : ℕ) (hi : i < gs.length), gateRow? n gs[i] = some (arr[acc.size + i]'(by omega))
  | acc, [], arr, h => by
    simp only [gateRowsInto, Option.some.injEq] at h
    subst h
    exact ⟨by simp, fun _ _ => rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | acc, g :: gs, arr, h => by
    rw [gateRowsInto.eq_2] at h
    split at h
    · rename_i r hr
      obtain ⟨hsize, hpre, hrest⟩ := gateRowsInto_eq_some n (acc.push r) gs arr h
      have hsize' : arr.size = acc.size + (g :: gs).length := by
        simp only [Array.size_push] at hsize
        simp only [List.length_cons]
        omega
      refine ⟨hsize', fun i hi => ?_, fun i hi => ?_⟩
      · rw [hpre i (by simp; omega), Array.getElem_push_lt]
      · cases i with
        | zero =>
          have h0 := hpre acc.size (by simp)
          rw [Array.getElem_push_eq] at h0
          have e : arr[acc.size + 0]'(by simp only [List.length_cons] at hsize'; omega) =
              arr[acc.size]'(by simp only [List.length_cons] at hsize'; omega) :=
            getElem_congr_idx (Nat.add_zero _)
          rw [List.getElem_cons_zero, e, h0]
          exact hr
        | succ k =>
          have hk' : k < gs.length := by simp only [List.length_cons] at hi; omega
          have hk := hrest k hk'
          have e : arr[(acc.push r).size + k]'(by simp only [Array.size_push] at hsize ⊢; omega) =
              arr[acc.size + (k + 1)]'(by simp only [List.length_cons] at hsize'; omega) :=
            getElem_congr_idx (by simp; omega)
          rw [List.getElem_cons_succ, hk, e]
    · cases h

/-- The table over an array of converted rows: the array's row where there is one, a padding
row beyond. Kept apart from `gateTable?` and never inlined, so that the array is a value the
returned function captures: written inline, the two functions merge and every read rebuilds
the array. -/
@[noinline] private def arrayTable {n : ℕ} (arr : Array (GateRow F n)) : Fin n → GateRow F n :=
  fun i => if h : i.val < arr.size then arr[i.val] else zeroGateRow i

/-- The table of an assembled gate list on `n` rows: each emitted row converted, and zero
gates wired to themselves beyond them. `none` when the list is longer than the table, or a
row has more coefficients than the coefficient columns or a wire target outside the table. -/
def gateTable? (gates : List (AssembledGate F)) (n : ℕ) : Option (Fin n → GateRow F n) :=
  if gates.length ≤ n then
    match gateRowsInto n #[] gates with
    | some arr => some (arrayTable arr)
    | none => none
  else none

/-- The table is built exactly when the list fits the table and every row fits it. -/
theorem gateTable?_isSome_iff (gates : List (AssembledGate F)) (n : ℕ) :
    (gateTable? gates n).isSome ↔ gates.length ≤ n ∧ ∀ g ∈ gates,
      g.coeffs.length ≤ coeffCols ∧
        ∀ c : Fin permCols, g.wires[c].col < permCols ∧ g.wires[c].row < n := by
  unfold gateTable?
  split
  · rename_i hlen
    have h := gateRowsInto_isSome_iff n #[] gates
    simp only [RowFits] at h
    rw [← h]
    cases gateRowsInto n #[] gates <;> simp [hlen]
  · rename_i hlen
    simp [hlen]

/-- A built table's emitted rows are the list's: the same gate type, coefficients and wire
targets. -/
private theorem gateTable?_emitted {gates : List (AssembledGate F)} {n : ℕ}
    {t : Fin n → GateRow F n}
    (h : gateTable? gates n = some t) (i : Fin n) (hi : i.val < gates.length) :
    (t i).typ = gates[i.val].kind ∧
      (∀ c : Fin coeffCols, (t i).coeffs c = gates[i.val].coeffs.getD c.val 0) ∧
      ∀ c : Fin permCols, ((t i).wires c).1.val = gates[i.val].wires[c].col ∧
        ((t i).wires c).2.val = gates[i.val].wires[c].row := by
  unfold gateTable? at h
  split at h
  · split at h
    · rename_i arr harr
      cases h
      obtain ⟨hsize, -, hrow⟩ := gateRowsInto_eq_some n #[] gates arr harr
      have hi' : i.val < arr.size := by simp at hsize; omega
      simp only [arrayTable, dif_pos hi']
      have e : arr[(#[] : Array (GateRow F n)).size + i.val]'(by simp at hsize ⊢; omega) =
          arr[i.val] := getElem_congr_idx (by simp)
      exact gateRow?_eq_some ((hrow i.val hi).trans (congrArg some e))
    · cases h
  · cases h

/-- A built table's rows beyond the list are zero gates with zero coefficients, each cell
wired to itself. -/
theorem gateTable?_padding {gates : List (AssembledGate F)} {n : ℕ} {t : Fin n → GateRow F n}
    (h : gateTable? gates n = some t) (i : Fin n) (hi : gates.length ≤ i.val) :
    (t i).typ = .zero ∧ (∀ c : Fin coeffCols, (t i).coeffs c = 0) ∧
      ∀ c : Fin permCols, (t i).wires c = (c, i) := by
  unfold gateTable? at h
  split at h
  · split at h
    · rename_i arr harr
      cases h
      obtain ⟨hsize, -, -⟩ := gateRowsInto_eq_some n #[] gates arr harr
      have hi' : ¬ i.val < arr.size := by simp at hsize; omega
      simp only [arrayTable, dif_neg hi']
      exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩
    · cases h
  · cases h

end Table

/-! ## The index -/

section Index

variable [Field F] [DecidableEq F]

/-- The index of an assembled gate list for a source: `none` unless every constraint's
parameters are the given ones, the list fits before the masked rows, `gateTable?` builds the
table, and `Index.build?` accepts it: the domain a power of two with a primitive root and coset
shifts, the masked-row count in range, the wiring a permutation keeping the masked rows apart
and fixing them, the public rows generic with a unit first coefficient, the masked rows zero
gates, and no two-row gate on the last unmasked row. -/
def indexOfGates? (gates : List (AssembledGate F)) (source : List (KimchiConstraint F))
    (publicCount n zkRows : ℕ) (omega endoBase : F) (mds : Gate.Poseidon.Mds F)
    (shifts : Fin permCols → F) : Option (Index F n) :=
  if (∀ c ∈ source, c.ParamsAgree mds endoBase) ∧ gates.length ≤ n - zkRows then
    (gateTable? gates n).bind fun t => Index.build? t publicCount zkRows omega endoBase mds shifts
  else none

/-- The index of a compiled source: `indexOfGates?` on its assembled gates at its public
variables. -/
def compiledIndex? (source : List (KimchiConstraint F)) (publicVars : List Variable)
    (nv : Variable) (n zkRows : ℕ) (omega endoBase : F) (mds : Gate.Poseidon.Mds F)
    (shifts : Fin permCols → F) : Option (Index F n) :=
  indexOfGates? (directGates source publicVars nv) source publicVars.length n zkRows omega
    endoBase mds shifts

/-- **The compiled index corresponds to its source.** An index `compiledIndex?` returns has
the source's public count, parameters, rows, coefficients and wiring. -/
theorem compiledIndex?_indexOf {source : List (KimchiConstraint F)} {publicVars : List Variable}
    {nv : Variable} {n zkRows : ℕ} {omega endoBase : F} {mds : Gate.Poseidon.Mds F}
    {shifts : Fin permCols → F} {idx : Index F n}
    (h : compiledIndex? source publicVars nv n zkRows omega endoBase mds shifts = some idx) :
    IndexOf source publicVars nv idx := by
  unfold compiledIndex? indexOfGates? at h
  split at h
  · rename_i hcond
    obtain ⟨t, ht, hb⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hg, hpc, hzk, he, hm⟩ := Index.build?_eq_some hb
    exact
      { publicCount := hpc
        params := fun c hc => by rw [hm, he]; exact hcond.1 c hc
        fits := by rw [hzk]; exact hcond.2
        typ := fun i hi => by rw [hg]; exact (gateTable?_emitted ht i hi).1
        coeffs := fun i hi c => by rw [hg]; exact (gateTable?_emitted ht i hi).2.1 c
        wires := fun i hi c => by rw [hg]; exact (gateTable?_emitted ht i hi).2.2 c }
  · cases h

end Index

/-! ## The compiler's gates -/

section Compiled

variable [Field F] [DecidableEq F]

/-- A built circuit's assembled gates at any public variables are its source's: the
assembly reads the constraints and the counter, never the stored result. -/
theorem gateDataOf_reduceBuilt {α : Type} (b : Built (KimchiConstraint F) α)
    (publicVars : List Variable) :
    (gateDataOf (reduceBuilt b) publicVars).2.1 = directGates b.constraints publicVars b.nextVar :=
  rfl

end Compiled

end Snarky.Kimchi
