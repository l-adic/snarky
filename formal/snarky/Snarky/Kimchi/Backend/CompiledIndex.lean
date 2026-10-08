import Snarky.Kimchi.Backend.Direct

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
- `classGates`: the gate list with the class-based wiring.

## Main results

- `gateTable?_isSome_iff`, `gateTable?_emitted`, `gateTable?_padding`: when the table is
  built, and what each of its rows is.
- `compiledIndex?_indexOf`: the index a successful construction returns is the source's.
- `gateDataOf_reduceBuilt`: a built circuit's gates are its source's, whatever its result.
- `directGates_eq_classGates`: the assembled gates are the class-based ones.

## Implementation notes

The table reads an array built once from the converted rows, since `Index.build?` reads the
table many times. The parameters, the domain size and the masked-row count are the caller's,
as a deployment fixes them. The assembly's wiring goes through a hash map the kernel cannot
evaluate; `classGates` is the same list computed from the classes, so a concrete instance is
decided by rewriting with `directGates_eq_classGates` and evaluating the rest unchanged.
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

/-- The emitted rows as table rows, `none` when one does not fit. -/
private def gateRows? (n : ℕ) : List (AssembledGate F) → Option (List (GateRow F n))
  | [] => some []
  | g :: gs =>
    match gateRow? n g, gateRows? n gs with
    | some r, some rs => some (r :: rs)
    | _, _ => none

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

private theorem gateRows?_isSome_iff (n : ℕ) :
    (gs : List (AssembledGate F)) → ((gateRows? n gs).isSome ↔ ∀ g ∈ gs, RowFits n g)
  | [] => by simp [gateRows?]
  | g :: gs => by
    rw [List.forall_mem_cons, ← gateRow?_isSome_iff, ← gateRows?_isSome_iff n gs,
      gateRows?.eq_2]
    cases gateRow? n g <;> cases gateRows? n gs <;> simp

private theorem gateRows?_eq_some (n : ℕ) :
    (gs : List (AssembledGate F)) → (rs : List (GateRow F n)) → gateRows? n gs = some rs →
      ∃ hlen : rs.length = gs.length, ∀ (i : ℕ) (hi : i < gs.length),
        gateRow? n gs[i] = some (rs[i]'(hlen ▸ hi))
  | [], rs, h => by
    simp only [gateRows?, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | g :: gs, rs, h => by
    rw [gateRows?.eq_2] at h
    split at h
    · rename_i r rs' hr hrs
      cases h
      obtain ⟨hlen, hrs'⟩ := gateRows?_eq_some n gs rs' hrs
      refine ⟨by simp [hlen], fun i hi => ?_⟩
      cases i with
      | zero => exact hr
      | succ k => exact hrs' k (by simpa using hi)
    · cases h

/-- The table of an assembled gate list on `n` rows: each emitted row converted, and zero
gates wired to themselves beyond them. `none` when the list is longer than the table, or a
row has more coefficients than the coefficient columns or a wire target outside the table. -/
def gateTable? (gates : List (AssembledGate F)) (n : ℕ) : Option (Fin n → GateRow F n) :=
  if gates.length ≤ n then
    (gateRows? n gates).map fun rows =>
      let arr := rows.toArray
      fun i => if h : i.val < arr.size then arr[i.val] else zeroGateRow i
  else none

/-- The table is built exactly when the list fits the table and every row fits it. -/
theorem gateTable?_isSome_iff (gates : List (AssembledGate F)) (n : ℕ) :
    (gateTable? gates n).isSome ↔ gates.length ≤ n ∧ ∀ g ∈ gates,
      g.coeffs.length ≤ coeffCols ∧
        ∀ c : Fin permCols, g.wires[c].col < permCols ∧ g.wires[c].row < n := by
  unfold gateTable?
  split
  · rename_i hlen
    rw [Option.isSome_map, gateRows?_isSome_iff]
    simp only [RowFits, hlen, true_and]
  · rename_i hlen
    simp [hlen]

/-- A built table's emitted rows are the list's: the same gate type, coefficients and wire
targets. -/
theorem gateTable?_emitted {gates : List (AssembledGate F)} {n : ℕ} {t : Fin n → GateRow F n}
    (h : gateTable? gates n = some t) (i : Fin n) (hi : i.val < gates.length) :
    (t i).typ = gates[i.val].kind ∧
      (∀ c : Fin coeffCols, (t i).coeffs c = gates[i.val].coeffs.getD c.val 0) ∧
      ∀ c : Fin permCols, ((t i).wires c).1.val = gates[i.val].wires[c].col ∧
        ((t i).wires c).2.val = gates[i.val].wires[c].row := by
  unfold gateTable? at h
  split at h
  · obtain ⟨rows, hrows, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hlen, hrow⟩ := gateRows?_eq_some n gates rows hrows
    have hi' : i.val < rows.toArray.size := by simp [hlen, hi]
    simp only [dif_pos hi']
    exact gateRow?_eq_some (by simpa using hrow i.val hi)
  · cases h

/-- A built table's rows beyond the list are zero gates with zero coefficients, each cell
wired to itself. -/
theorem gateTable?_padding {gates : List (AssembledGate F)} {n : ℕ} {t : Fin n → GateRow F n}
    (h : gateTable? gates n = some t) (i : Fin n) (hi : gates.length ≤ i.val) :
    (t i).typ = .zero ∧ (∀ c : Fin coeffCols, (t i).coeffs c = 0) ∧
      ∀ c : Fin permCols, (t i).wires c = (c, i) := by
  unfold gateTable? at h
  split at h
  · obtain ⟨rows, hrows, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hlen, -⟩ := gateRows?_eq_some n gates rows hrows
    have hi' : ¬ i.val < rows.toArray.size := by simp [hlen]; omega
    simp only [dif_neg hi']
    exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩
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

/-- The gate list with the class-based wiring: the production assembly, each wire target read
from the classes rather than the hash map. -/
def classGates (roots : Array Variable) (rows : List (KimchiRow F)) : List (AssembledGate F) :=
  rows.zipIdx.map fun (row, i) =>
    { kind := row.kind,
      wires := ⟨⟨[classTarget roots rows i 0, classTarget roots rows i 1,
                  classTarget roots rows i 2, classTarget roots rows i 3,
                  classTarget roots rows i 4, classTarget roots rows i 5,
                  classTarget roots rows i 6]⟩, by simp⟩,
      coeffs := row.coeffs }

/-- The assembled gates are the class-based ones. -/
theorem directGates_eq_classGates (source : List (KimchiConstraint F))
    (publicVars : List Variable) (nv : Variable) :
    directGates source publicVars nv =
      classGates (directRoots source nv) (directRows source publicVars nv) := by
  rw [directGates_eq]
  unfold assembleGates classGates
  simp only [wireTarget_eq]

end Compiled

end Snarky.Kimchi
