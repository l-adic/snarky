import Snarky.Kimchi.Compile
import Snarky.Laws

/-!
# Compilation is honest: a successful prover run satisfies the compiled index

The general theorem behind `Snarky.Kimchi.Compile.check`: whenever `compile` succeeds on
a DSL circuit, the witness table it stores **satisfies the wired index it built** —
`Kimchi.Index.Satisfies`, copy constraints included (`satisfies_of_compile`).

The three conjuncts of `Satisfies` are proved separately:

* **rows** (`rowSatisfies_gateTableOf`) — constraint rows are Generic gates whose cells
  hold the operand evaluations, so `GateConstraint.holds` (delivered for every emitted
  constraint by `Snarky.prove_sound`) is exactly the row's `Gate.Generic.Holds`; padding
  rows are constraint-free `zero` gates.
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
theorem mem_cellsOf {cons : List (GateConstraint Fp)} {n : ℕ} {v : Variable}
    {c : Fin 7 × Fin n} : c ∈ cellsOf cons n v ↔ cellVar cons c = some v := by
  simp [cellsOf, List.mem_filter, mem_allCells]

/-- The cyclic successor stays in the list. -/
theorem nextIn_mem {β : Type*} [BEq β] [LawfulBEq β] {l : List β} {c : β} (hc : c ∈ l) :
    nextIn l c ∈ l := by
  have hlen : 0 < l.length := List.length_pos_of_mem hc
  rw [nextIn, List.getD_eq_getElem _ _ (Nat.mod_lt _ hlen)]
  exact List.getElem_mem _

/-- The wiring successor of a cell holding `v` holds `v` too — a copy cycle is closed
under its own successor map. -/
theorem cellVar_wireOf {cons : List (GateConstraint Fp)} {n : ℕ} {c : Fin 7 × Fin n}
    {v : Variable} (h : cellVar cons c = some v) :
    cellVar cons (wireOf cons c) = some v := by
  have hw : wireOf cons c = nextIn (cellsOf cons n v) c := by
    unfold wireOf
    rw [h]
  rw [hw]
  exact mem_cellsOf.mp (nextIn_mem (mem_cellsOf.mpr h))

/-- `tabOf` reads a variable-holding cell through its variable: the cell's value is the
variable's evaluation, whatever the assignment. -/
theorem cellValue_tabOf {cons : List (GateConstraint Fp)} {env : Assignments Fp} {n : ℕ}
    {c : Fin 7 × Fin n} {v : Variable} (h : cellVar cons c = some v) :
    cellValue (tabOf cons env n) c = evalD env (some (.var v)) := by
  have hval : cellValue (tabOf cons env n) c
      = evalD env (cons[(c.2 : ℕ)]?.bind fun con => operandAt con (c.1 : ℕ)) := rfl
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
theorem cellValue_wireOf (cons : List (GateConstraint Fp)) (env : Assignments Fp)
    {n : ℕ} (c : Fin 7 × Fin n) :
    cellValue (tabOf cons env n) (wireOf cons c) = cellValue (tabOf cons env n) c := by
  cases h : cellVar cons c with
  | none =>
    have hw : wireOf cons c = c := by
      unfold wireOf
      rw [h]
    rw [hw]
  | some v =>
    rw [cellValue_tabOf (cellVar_wireOf h), cellValue_tabOf h]

/-! ## The row conjunct -/

/-- A held constraint is a satisfied Generic row: the row whose coefficients are the
constraint's and whose cells are `tabOf`'s reads at row `i`. -/
theorem holds_row {cons : List (GateConstraint Fp)} {env : Assignments Fp} {n : ℕ}
    {i : Fin n} {con : GateConstraint Fp} (hcon : cons[(i : ℕ)]? = some con)
    (hh : con.holds env = true) :
    Kimchi.Gate.Generic.Holds ⟨coeffsAt (some con), tabOf cons env n i⟩ := by
  unfold GateConstraint.holds at hh
  split at hh
  next x y z hx hy hz =>
    have w0 : tabOf cons env n i 0 = x := by
      unfold tabOf
      rw [hcon]
      show evalD env (some con.a) = x
      simp only [evalD, hx]
    have w1 : tabOf cons env n i 1 = y := by
      unfold tabOf
      rw [hcon]
      show evalD env (some con.b) = y
      simp only [evalD, hy]
    have w2 : tabOf cons env n i 2 = z := by
      unfold tabOf
      rw [hcon]
      show evalD env (some con.o) = z
      simp only [evalD, hz]
    rw [Kimchi.Gate.Generic.holds_iff]
    constructor
    · show con.q0 * tabOf cons env n i 0 + con.q1 * tabOf cons env n i 1
          + con.q2 * tabOf cons env n i 2
          + con.q3 * (tabOf cons env n i 0 * tabOf cons env n i 1) + con.q4 = 0
      rw [w0, w1, w2]
      exact of_decide_eq_true hh
    · show (0 : Fp) * tabOf cons env n i 3 + 0 * tabOf cons env n i 4
          + 0 * tabOf cons env n i 5
          + 0 * (tabOf cons env n i 3 * tabOf cons env n i 4) + 0 = 0
      ring
  next => exact absurd hh Bool.false_ne_true

/-- Every row of the compiled table satisfies its gate: constraint rows through
`holds_row`, padding rows vacuously (`zero` gates constrain nothing). -/
theorem rowSatisfies_gateTableOf {cons : List (GateConstraint Fp)} {env : Assignments Fp}
    {n : ℕ} [NeZero n] {idx : Index Fp n}
    (hg : idx.gates = gateTableOf cons n) (hpc : idx.publicCount = 0)
    (pub : Fin idx.publicCount → Fp)
    (hall : ∀ con ∈ cons, con.holds env = true) (i : Fin n) :
    rowSatisfies idx pub (tabOf cons env n) i := by
  have htyp : (idx.gates i).typ = if (i : ℕ) < cons.length then .generic else .zero := by
    rw [hg]; rfl
  by_cases hi : (i : ℕ) < cons.length
  · have hcon : cons[(i : ℕ)]? = some cons[(i : ℕ)] := List.getElem?_eq_getElem hi
    have hpub : pubAt idx pub i = 0 := by
      simp [pubAt, hpc]
    have hq : idx.coeffTable i = coeffsAt (some cons[(i : ℕ)]) := by
      show (idx.gates i).coeffs = _
      rw [hg]
      show coeffsAt cons[(i : ℕ)]? = _
      rw [hcon]
    unfold rowSatisfies
    rw [htyp, if_pos hi]
    show Kimchi.Gate.Generic.Holds
      (Kimchi.Gate.Generic.withPublic ⟨idx.coeffTable i, tabOf cons env n i⟩
        (pubAt idx pub i))
    rw [hpub, Kimchi.Gate.Generic.withPublic_zero, hq]
    exact holds_row hcon (hall cons[(i : ℕ)] (List.getElem_mem hi))
  · unfold rowSatisfies
    rw [htyp, if_neg hi]
    exact trivial

/-! ## The headline -/

/-- **Compilation is honest.** Whenever `compile` succeeds, the witness table it stores
satisfies the wired index it built — rows, copy constraints, and public pins. Composes
`Snarky.prove_sound` (every emitted constraint holds on the prover's final assignment)
with the row and copy conjuncts above; the provenance is `build?_gates`. -/
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
      haveI : NeZero (paddedSize (constraints m).length) := ⟨(Nat.two_pow_pos _).ne'⟩
      have hall : ∀ con ∈ constraints m, con.holds env = true :=
        prove_sound (holds := GateConstraint.holds)
          (fun _con _ _ hle hh => GateConstraint.holds_mono hle hh) hp
      refine ⟨fun i => rowSatisfies_gateTableOf hg hpc _ hall i, fun c => ?_, fun i => ?_⟩
      · have hw : idx.wiringMap c = wireOf (constraints m) c := by
          show wiringMapOf idx.gates c = _
          rw [hg]; rfl
        rw [hw]
        exact cellValue_wireOf (constraints m) env c
      · exact absurd i.isLt (by omega)

end Snarky.Kimchi.Compile
