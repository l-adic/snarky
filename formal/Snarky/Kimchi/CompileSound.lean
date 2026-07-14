import Snarky.Kimchi.Compile
import Snarky.Laws

/-!
# Compilation is honest: a successful prover run satisfies the compiled index

The general theorem behind `Snarky.Kimchi.Compile.check`: whenever `compile` succeeds on
a DSL circuit, the witness table it stores **satisfies the wired index it built** —
`Kimchi.Index.Satisfies`, copy constraints included (`satisfies_of_compile`).

The three conjuncts of `Satisfies` are proved separately:

* **rows** (`rowSatisfies_gateTableOf`) — a packed row's cells hold its two slots'
  operand evaluations, so `GateConstraint.holds` of both slot constraints (delivered for
  every emitted constraint by `Snarky.prove_sound`, threaded through the packing by
  `pack_mem`) is exactly the row's `Gate.Generic.Holds` — slot 1 in cells `w₀w₁w₂`
  against `q₀…q₄`, slot 2 in `w₃w₄w₅` against `q₅…q₉` (trivial when the slot is empty);
  padding rows are constraint-free `zero` gates.
* **copy** (`cellValue_wireOf`) — *unconditional*: a wired-together pair of cells holds
  the same variable (`cellVar_wireOf`, because a copy cycle `cellsOf` is closed under its
  own cyclic successor `nextIn`), and `tabOf` reads a cell through its variable, so both
  cells carry the same value whatever the assignment.
* **public** — vacuous: `compile` builds indices with `publicCount = 0`.

The provenance is definitional: `Index.build?` stores the constructed `gateTableOf`
verbatim (`build?_gates`), so the index's rows, coefficients, and wiring are the
compiler's own functions.
-/

namespace Snarky.Kimchi.Compile

open Snarky Snarky.Kimchi Kimchi.Index CompElliptic.Fields.Pasta

/-! ## `Index.build?` provenance -/

/-- `Index.build?` stores its arguments verbatim: a built index's gate table and public
count are the ones supplied. -/
theorem build?_gates {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    {gates : Fin n → GateRow F n} {pc zk : ℕ} {ω e : F} {sh : Fin 7 → F} {idx : Index F n}
    (h : Index.build? gates pc zk ω e sh = some idx) :
    idx.gates = gates ∧ idx.publicCount = pc := by
  unfold Index.build? at h
  split at h
  · injection h with h'
    subst h'
    exact ⟨rfl, rfl⟩
  · cases h

/-! ## The copy conjunct -/

/-- Every cell is enumerated. -/
theorem mem_allCells {n : ℕ} (c : Fin 7 × Fin n) : c ∈ allCells n :=
  List.mem_flatMap.mpr
    ⟨c.2, List.mem_finRange c.2, List.mem_map.mpr ⟨c.1, List.mem_finRange c.1, rfl⟩⟩

/-- A cell is in `v`'s copy cycle exactly when it holds `v`. -/
theorem mem_cellsOf {rows : List RowSlots} {n : ℕ} {v : Variable}
    {c : Fin 7 × Fin n} : c ∈ cellsOf rows n v ↔ cellVar rows c = some v := by
  simp [cellsOf, List.mem_filter, mem_allCells]

/-- The cyclic successor stays in the list. -/
theorem nextIn_mem {β : Type*} [BEq β] [LawfulBEq β] {l : List β} {c : β} (hc : c ∈ l) :
    nextIn l c ∈ l := by
  have hlen : 0 < l.length := List.length_pos_of_mem hc
  rw [nextIn, List.getD_eq_getElem _ _ (Nat.mod_lt _ hlen)]
  exact List.getElem_mem _

/-- The wiring successor of a cell holding `v` holds `v` too — a copy cycle is closed
under its own successor map. -/
theorem cellVar_wireOf {rows : List RowSlots} {n : ℕ} {c : Fin 7 × Fin n}
    {v : Variable} (h : cellVar rows c = some v) :
    cellVar rows (wireOf rows c) = some v := by
  have hw : wireOf rows c = nextIn (cellsOf rows n v) c := by
    unfold wireOf
    rw [h]
  rw [hw]
  exact mem_cellsOf.mp (nextIn_mem (mem_cellsOf.mpr h))

/-- `tabOf` reads a variable-holding cell through its variable: the cell's value is the
variable's evaluation, whatever the assignment. -/
theorem cellValue_tabOf {rows : List RowSlots} {env : Assignments Fp} {n : ℕ}
    {c : Fin 7 × Fin n} {v : Variable} (h : cellVar rows c = some v) :
    cellValue (tabOf rows env n) c = evalD env (some (.var v)) := by
  have hval : cellValue (tabOf rows env n) c
      = evalD env (rows[(c.2 : ℕ)]?.bind fun p => slotOperand p (c.1 : ℕ)) := rfl
  obtain ⟨x, hx, hxv⟩ := Option.bind_eq_some_iff.mp h
  cases x with
  | var v' =>
    obtain rfl : v' = v := by simpa [varOf?] using hxv
    rw [hval, hx]
  | const k => simp [varOf?] at hxv
  | add a b => simp [varOf?] at hxv
  | scale k y => simp [varOf?] at hxv

/-- **The copy conjunct, unconditionally**: wired-together cells of `tabOf` agree — both
read the same variable's evaluation. -/
theorem cellValue_wireOf (rows : List RowSlots) (env : Assignments Fp)
    {n : ℕ} (c : Fin 7 × Fin n) :
    cellValue (tabOf rows env n) (wireOf rows c) = cellValue (tabOf rows env n) c := by
  cases h : cellVar rows c with
  | none =>
    have hw : wireOf rows c = c := by
      unfold wireOf
      rw [h]
    rw [hw]
  | some v =>
    rw [cellValue_tabOf (cellVar_wireOf h), cellValue_tabOf h]

/-! ## The row conjunct -/

/-- Packing preserves membership: every slot constraint of a packed row came from the
constraint stream. -/
theorem pack_mem {cons : List (GateConstraint Fp)} {p : RowSlots} (hp : p ∈ pack cons) :
    p.1 ∈ cons ∧ ∀ c ∈ p.2, c ∈ cons := by
  induction cons using pack.induct with
  | case1 c1 c2 rest ih =>
    rcases List.mem_cons.mp hp with rfl | hp'
    · refine ⟨List.mem_cons_self .., fun c hc => ?_⟩
      obtain rfl : c2 = c := by simpa using hc
      exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · obtain ⟨h1, h2⟩ := ih hp'
      exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1),
        fun c hc => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (h2 c hc))⟩
  | case2 c =>
    obtain rfl : p = (c, none) := by simpa [pack] using hp
    exact ⟨List.mem_cons_self .., fun c' hc' => by simp at hc'⟩
  | case3 => cases hp

/-- A held pair of slot constraints is a satisfied Generic row: slot 1 in cells
`w₀w₁w₂` against `q₀…q₄`, slot 2 in `w₃w₄w₅` against `q₅…q₉` (trivial when empty). -/
theorem holds_row {rows : List RowSlots} {env : Assignments Fp} {n : ℕ}
    {i : Fin n} {p : RowSlots} (hrow : rows[(i : ℕ)]? = some p)
    (h1 : p.1.holds env = true) (h2 : ∀ c ∈ p.2, c.holds env = true) :
    Kimchi.Gate.Generic.Holds ⟨coeffsAt (some p), tabOf rows env n i⟩ := by
  obtain ⟨c1, oc2⟩ := p
  rw [Kimchi.Gate.Generic.holds_iff]
  refine ⟨?_, ?_⟩
  · unfold GateConstraint.holds at h1
    split at h1
    next x y z hx hy hz =>
      have w0 : tabOf rows env n i 0 = x := by
        unfold tabOf
        rw [hrow]
        show evalD env (some c1.a) = x
        simp only [evalD, hx]
      have w1 : tabOf rows env n i 1 = y := by
        unfold tabOf
        rw [hrow]
        show evalD env (some c1.b) = y
        simp only [evalD, hy]
      have w2 : tabOf rows env n i 2 = z := by
        unfold tabOf
        rw [hrow]
        show evalD env (some c1.o) = z
        simp only [evalD, hz]
      show c1.q0 * tabOf rows env n i 0 + c1.q1 * tabOf rows env n i 1
          + c1.q2 * tabOf rows env n i 2
          + c1.q3 * (tabOf rows env n i 0 * tabOf rows env n i 1) + c1.q4 = 0
      rw [w0, w1, w2]
      exact of_decide_eq_true h1
    next => exact absurd h1 Bool.false_ne_true
  · cases oc2 with
    | none =>
      show (0 : Fp) * tabOf rows env n i 3 + 0 * tabOf rows env n i 4
          + 0 * tabOf rows env n i 5
          + 0 * (tabOf rows env n i 3 * tabOf rows env n i 4) + 0 = 0
      ring
    | some c2 =>
      have hh2 := h2 c2 rfl
      unfold GateConstraint.holds at hh2
      split at hh2
      next x y z hx hy hz =>
        have w3 : tabOf rows env n i 3 = x := by
          unfold tabOf
          rw [hrow]
          show evalD env (some c2.a) = x
          simp only [evalD, hx]
        have w4 : tabOf rows env n i 4 = y := by
          unfold tabOf
          rw [hrow]
          show evalD env (some c2.b) = y
          simp only [evalD, hy]
        have w5 : tabOf rows env n i 5 = z := by
          unfold tabOf
          rw [hrow]
          show evalD env (some c2.o) = z
          simp only [evalD, hz]
        show c2.q0 * tabOf rows env n i 3 + c2.q1 * tabOf rows env n i 4
            + c2.q2 * tabOf rows env n i 5
            + c2.q3 * (tabOf rows env n i 3 * tabOf rows env n i 4) + c2.q4 = 0
        rw [w3, w4, w5]
        exact of_decide_eq_true hh2
      next => exact absurd hh2 Bool.false_ne_true

/-- Every row of the compiled table satisfies its gate: packed rows through `holds_row`,
padding rows vacuously (`zero` gates constrain nothing). -/
theorem rowSatisfies_gateTableOf {rows : List RowSlots} {env : Assignments Fp}
    {n : ℕ} [NeZero n] {idx : Index Fp n}
    (hg : idx.gates = gateTableOf rows n) (hpc : idx.publicCount = 0)
    (pub : Fin idx.publicCount → Fp)
    (hall : ∀ p ∈ rows, p.1.holds env = true ∧ ∀ c ∈ p.2, c.holds env = true)
    (i : Fin n) :
    rowSatisfies idx pub (tabOf rows env n) i := by
  have htyp : (idx.gates i).typ = if (i : ℕ) < rows.length then .generic else .zero := by
    rw [hg]; rfl
  by_cases hi : (i : ℕ) < rows.length
  · have hrow : rows[(i : ℕ)]? = some rows[(i : ℕ)] := List.getElem?_eq_getElem hi
    have hpub : pubAt idx pub i = 0 := by
      simp [pubAt, hpc]
    have hq : idx.coeffTable i = coeffsAt (some rows[(i : ℕ)]) := by
      show (idx.gates i).coeffs = _
      rw [hg]
      show coeffsAt rows[(i : ℕ)]? = _
      rw [hrow]
    obtain ⟨hh1, hh2⟩ := hall rows[(i : ℕ)] (List.getElem_mem hi)
    unfold rowSatisfies
    rw [htyp, if_pos hi]
    show Kimchi.Gate.Generic.Holds
      (Kimchi.Gate.Generic.withPublic ⟨idx.coeffTable i, tabOf rows env n i⟩
        (pubAt idx pub i))
    rw [hpub, Kimchi.Gate.Generic.withPublic_zero, hq]
    exact holds_row hrow hh1 hh2
  · unfold rowSatisfies
    rw [htyp, if_neg hi]
    exact trivial

/-! ## The headline -/

/-- **Compilation is honest.** Whenever `compile` succeeds, the witness table it stores
satisfies the wired index it built — rows, copy constraints, and public pins. Composes
`Snarky.prove_sound` (every emitted constraint holds on the prover's final assignment)
with the row and copy conjuncts above, threading the packing through `pack_mem`; the
provenance is `build?_gates`. -/
theorem satisfies_of_compile {α : Type} {m : CircuitM Fp (GateConstraint Fp) α}
    {out : Compiled} (h : compile m = .ok out) :
    haveI : NeZero out.n := out.nz
    Satisfies out.idx (fun _ => 0) out.tab := by
  unfold compile at h
  split at h
  · cases h
  next a nv env hp =>
    split at h
    · cases h
    next idx hb =>
      injection h with h'
      subst h'
      dsimp only
      obtain ⟨hg, hpc⟩ := build?_gates hb
      haveI : NeZero (paddedSize (pack (constraints m)).length) :=
        ⟨(Nat.two_pow_pos _).ne'⟩
      have hall : ∀ con ∈ constraints m, con.holds env = true :=
        prove_sound (holds := GateConstraint.holds)
          (fun _con _ _ hle hh => GateConstraint.holds_mono hle hh) hp
      have hall' : ∀ p ∈ pack (constraints m),
          p.1.holds env = true ∧ ∀ c ∈ p.2, c.holds env = true := fun p hp' =>
        ⟨hall _ (pack_mem hp').1, fun c hc => hall _ ((pack_mem hp').2 c hc)⟩
      refine ⟨fun i => rowSatisfies_gateTableOf hg hpc _ hall' i, fun c => ?_, fun i => ?_⟩
      · have hw : idx.wiringMap c = wireOf (pack (constraints m)) c := by
          show wiringMapOf idx.gates c = _
          rw [hg]; rfl
        rw [hw]
        exact cellValue_wireOf (pack (constraints m)) env c
      · exact absurd i.isLt (by omega)

end Snarky.Kimchi.Compile
