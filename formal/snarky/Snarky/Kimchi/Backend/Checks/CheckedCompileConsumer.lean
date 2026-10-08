import Snarky.Kimchi.Backend.CheckedCompile
import Snarky.DSL.Field

/-!
# A consumer of checked compilation

A small circuit, written against the supported interface only: it multiplies its two inputs,
then the product by the first input. It is compiled with `compile`, and with `compileWith`
keeping the first product as an internal cell. For each compilation, a checked index and a table
satisfying it at a public input, read in the order of the public variables, give a valuation
satisfying every compiled constraint and taking the public input's values at the public
variables.

The typed corollaries read that valuation through the compiled layout: split the public input
into its input and output fields, and the input bundle reads as any value encoding the first,
the body's output as any value encoding the second.

The statements name the compiled circuit, its public variables, the checked index and its
accessors, and nothing about how lifting is proved. The circuit is over any field and the
index over any domain, so the module needs no fixtures. The checked-compilation checks obtain
the checked indices from `checkBuilt?` and decide the tables' satisfaction.

## Main definitions

- `circuit`, `circuitWith`: the circuit, without and with its kept cell.
- `built`, `builtWith`: their compilations by `compile` and `compileWith`.

## Main results

- `compile_lifts`, `compileWith_lifts`: lifting each compilation.
- `compile_reads_lifts`, `compileWith_reads_lifts`: the lifted valuation's typed readings.
-/

open Kimchi

namespace Snarky.Kimchi.CheckedConsumer

open Snarky

variable (F : Type) [Field F] [DecidableEq F]

/-- The circuit's body: the product of the inputs, kept as a cell, times the first input. -/
def circuitWith (p : FVar F × FVar F) : CircuitM F (KimchiConstraint F) (FVar F × FVar F) := do
  let z ← mul p.1 p.2
  let w ← mul z p.1
  pure (w, z)

/-- The circuit without the kept cell. -/
def circuit (p : FVar F × FVar F) : CircuitM F (KimchiConstraint F) (FVar F) :=
  Prod.fst <$> circuitWith F p

/-- The circuit compiled by `compile`. -/
def built : Built (KimchiConstraint F) (FVar F × FVar F) :=
  compile (a := F × F) (b := F) (circuit F)

/-- The circuit compiled by `compileWith`, the first product kept in the result. -/
def builtWith : Built (KimchiConstraint F) ((FVar F × FVar F) × FVar F) :=
  compileWith (a := F × F) (b := F) (circuitWith F)

variable {F}

/-- A compilation's public variables, for the circuit's input and output types. -/
abbrev publicVarsOf {β : Type} (b : Built (KimchiConstraint F) (β × FVar F)) : List Variable :=
  compiledPublicVars (F := F) (a := F × F) (b := F) b

/-- **Lifting the compiled circuit.** A checked index of the circuit compiled by `compile`, and
a table satisfying it at the public input `pub`, give a valuation satisfying every compiled
constraint and taking the values of `pub` at the public variables. -/
theorem compile_lifts {n : ℕ} [NeZero n]
    (checked : CheckedIndex (built F).constraints (publicVarsOf (built F)) (built F).nextVar n)
    (pub : Fin (publicVarsOf (built F)).length → F) (table : Fin n → Fin wCols → F)
    (hsat : checked.index.Satisfies (fun j => pub (Fin.cast checked.publicCount_eq j)) table) :
    ∃ V : Valuation F, (∀ con ∈ (built F).constraints, KimchiConstraint.Holds V con) ∧
      ∀ i, V (publicVarsOf (built F))[i] = pub i := by
  obtain ⟨V, hV, hpub⟩ := checked.lift _ table hsat
  exact ⟨V, hV, fun i => by rw [hpub i]; exact congrArg pub (Fin.ext (by simp))⟩

/-- The same lifting for the circuit compiled by `compileWith` with its kept cell. -/
theorem compileWith_lifts {n : ℕ} [NeZero n]
    (checked : CheckedIndex (builtWith F).constraints (publicVarsOf (builtWith F))
      (builtWith F).nextVar n)
    (pub : Fin (publicVarsOf (builtWith F)).length → F) (table : Fin n → Fin wCols → F)
    (hsat : checked.index.Satisfies (fun j => pub (Fin.cast checked.publicCount_eq j)) table) :
    ∃ V : Valuation F, (∀ con ∈ (builtWith F).constraints, KimchiConstraint.Holds V con) ∧
      ∀ i, V (publicVarsOf (builtWith F))[i] = pub i := by
  obtain ⟨V, hV, hpub⟩ := checked.lift _ table hsat
  exact ⟨V, hV, fun i => by rw [hpub i]; exact congrArg pub (Fin.ext (by simp))⟩

/-- **Typed lifting of the compiled circuit.** Where the public input splits into the input
fields `pubIn` and the output fields `pubOut`, the valuation `compile_lifts` gives reads the
input bundle as any `x` encoding to `pubIn` and the body's output as any `y` encoding to
`pubOut`. -/
theorem compile_reads_lifts {n : ℕ} [NeZero n]
    (checked : CheckedIndex (built F).constraints (publicVarsOf (built F)) (built F).nextVar n)
    (pub : Fin (publicVarsOf (built F)).length → F) (table : Fin n → Fin wCols → F)
    (hsat : checked.index.Satisfies (fun j => pub (Fin.cast checked.publicCount_eq j)) table)
    (pubIn : Vector F 2) (pubOut : Vector F 1)
    (hsplit : List.ofFn pub = pubIn.toList ++ pubOut.toList) :
    ∃ V : Valuation F, (∀ con ∈ (built F).constraints, KimchiConstraint.Holds V con) ∧
      (∀ x : F × F, CircuitType.Reads V (inputVar (F := F) (a := F × F)) x ↔
        CircuitType.valueToFields (F := F) x = pubIn) ∧
      ∀ y : F, CircuitType.Reads V (built F).result.1 y ↔
        CircuitType.valueToFields (F := F) y = pubOut := by
  obtain ⟨V, hV, hpub⟩ := compile_lifts checked pub table hsat
  refine ⟨V, hV, compile_reads hV pubIn pubOut ?_⟩
  change (publicVarsOf (built F)).map V = _
  rw [← hsplit]
  exact List.ext_getElem (by simp) fun i hi _ => by
    simp only [List.getElem_map, List.getElem_ofFn]
    exact hpub ⟨i, by simpa using hi⟩

/-- The same typed lifting for the circuit compiled by `compileWith`: the body's output is
`result.1.1`, the kept cell staying in `result.1.2`. -/
theorem compileWith_reads_lifts {n : ℕ} [NeZero n]
    (checked : CheckedIndex (builtWith F).constraints (publicVarsOf (builtWith F))
      (builtWith F).nextVar n)
    (pub : Fin (publicVarsOf (builtWith F)).length → F) (table : Fin n → Fin wCols → F)
    (hsat : checked.index.Satisfies (fun j => pub (Fin.cast checked.publicCount_eq j)) table)
    (pubIn : Vector F 2) (pubOut : Vector F 1)
    (hsplit : List.ofFn pub = pubIn.toList ++ pubOut.toList) :
    ∃ V : Valuation F, (∀ con ∈ (builtWith F).constraints, KimchiConstraint.Holds V con) ∧
      (∀ x : F × F, CircuitType.Reads V (inputVar (F := F) (a := F × F)) x ↔
        CircuitType.valueToFields (F := F) x = pubIn) ∧
      ∀ y : F, CircuitType.Reads V (builtWith F).result.1.1 y ↔
        CircuitType.valueToFields (F := F) y = pubOut := by
  obtain ⟨V, hV, hpub⟩ := compileWith_lifts checked pub table hsat
  refine ⟨V, hV, compileWith_reads hV pubIn pubOut ?_⟩
  change (publicVarsOf (builtWith F)).map V = _
  rw [← hsplit]
  exact List.ext_getElem (by simp) fun i hi _ => by
    simp only [List.getElem_map, List.getElem_ofFn]
    exact hpub ⟨i, by simpa using hi⟩

end Snarky.Kimchi.CheckedConsumer
