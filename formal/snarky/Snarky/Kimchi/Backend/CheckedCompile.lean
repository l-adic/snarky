import Snarky.Kimchi.Backend.CompiledIndex
import Snarky.Kimchi.Backend.ScopedCheck

/-!
# Checked compilation

`CheckedIndex.check?` runs the two checks lifting needs: the scope checker, then the index
constructor. On success it returns the constructor's index with the two premises of
`KimchiConstraint.Wired.holds_of_satisfies` as proofs. `CheckedIndex.lift` then turns any table
satisfying that index into a valuation satisfying the source and reading its public variables as
the public input, with no further premise. `checkBuilt?` checks a compiled circuit at its
constraints, its public variables and its counter.

## Main definitions

- `CheckedIndex`: an index with proofs that its source is in scope and that it is the source's.
- `CheckFailure`: why a check fails: the scope checker's failure, or the index constructor.
- `CheckedIndex.check?`, `checkBuilt?`: the checked index of a source, and of a compiled
  circuit.
- `CheckedIndex.publicIndex`: a public variable's row in the checked index.

## Main results

- `CheckedIndex.lift`: a table satisfying a checked index yields a valuation satisfying the
  source, at the public input.
- `CheckedIndex.check?_index`, `checkBuilt?_index`: the checked index is the constructor's,
  built from the compiler's own gate table.
- `CheckedIndex.check?_isOk_iff`: the check succeeds exactly when the source is in scope and
  the constructor builds an index.
- `CheckedIndex.publicCount_eq`, `CheckedIndex.publicIndex_val`: one public row per public
  variable, at its position in the list.

## Implementation notes

The scope checker runs first and once. Its failure is the one reported, the index is built only
for a source in scope, and the scope proof is `checkScoped_eq_true_iff` at its verdict. A
certificate is indexed by its source, public variables and counter, so it names the compilation
it checks.
`checkBuilt?` takes a built circuit rather than a program, covering `compile` and `compileWith`
alike; the cells `compileWith` keeps stay in the result and are not public. The public
variables are the assembly's (`compiledPublicVars`); the public input is read at them, not
through the input and output encodings.
-/

open Kimchi Kimchi.Index

namespace Snarky.Kimchi

open Snarky

variable {F : Type}

/-- Why a check fails: the scope checker's failure, or the index constructor's. -/
inductive CheckFailure where
  /-- The source is out of scope, for the reason given. -/
  | scope (f : ScopedFailure)
  /-- The source is in scope, but the constructor builds no index. -/
  | index

section Checked

variable [Field F] [DecidableEq F]

/-- An index with the premises lifting needs: its source is in scope, and it is the source's.
It is obtained from `CheckedIndex.check?` or `checkBuilt?`; the two proof fields are its internal
certificate, read by `CheckedIndex.lift`. -/
structure CheckedIndex (source : List (KimchiConstraint F)) (publicVars : List Variable)
    (nv : Variable) (n : ℕ) where
  /-- The index. -/
  index : Index F n
  /-- The source is in scope. -/
  admissible : KimchiConstraint.Wired.Scoped nv source publicVars
  /-- The index is the source's. -/
  corresponds : IndexOf source publicVars nv index

/-- The checked index of a source: the scope checker's failure if it finds one, otherwise
`compiledIndex?`'s index, or `.index` if it builds none. -/
def CheckedIndex.check? (source : List (KimchiConstraint F)) (publicVars : List Variable)
    (nv : Variable) (n zkRows : ℕ) (omega endoBase : F) (mds : Gate.Poseidon.Mds F)
    (shifts : Fin permCols → F) : Except CheckFailure (CheckedIndex source publicVars nv n) :=
  match hs : scopedFailure? nv source publicVars with
  | some f => .error (.scope f)
  | none =>
    match hi : compiledIndex? source publicVars nv n zkRows omega endoBase mds shifts with
    | some idx =>
      .ok ⟨idx, checkScoped_eq_true_iff.mp (by rw [checkScoped, hs]; rfl),
        compiledIndex?_indexOf hi⟩
    | none => .error .index

variable {source : List (KimchiConstraint F)} {publicVars : List Variable} {nv : Variable}
  {n zkRows : ℕ} {omega endoBase : F} {mds : Gate.Poseidon.Mds F} {shifts : Fin permCols → F}

/-- A checked index is the constructor's. -/
theorem CheckedIndex.check?_index {c : CheckedIndex source publicVars nv n}
    (h : check? source publicVars nv n zkRows omega endoBase mds shifts = .ok c) :
    compiledIndex? source publicVars nv n zkRows omega endoBase mds shifts = some c.index := by
  unfold check? at h
  split at h
  · cases h
  · split at h
    · rename_i idx hi
      cases h
      exact hi
    · cases h

/-- The check succeeds exactly when the scope checker accepts and the constructor builds an
index. -/
theorem CheckedIndex.check?_isOk_iff :
    (check? source publicVars nv n zkRows omega endoBase mds shifts).isOk = true ↔
      checkScoped nv source publicVars = true ∧
        (compiledIndex? source publicVars nv n zkRows omega endoBase mds shifts).isSome = true := by
  unfold check? checkScoped
  split
  · rename_i hs
    simp [hs, Except.isOk, Except.toBool]
  · rename_i hs
    split
    · rename_i hi
      simp [hs, hi, Except.isOk, Except.toBool]
    · rename_i hi
      simp [hs, hi, Except.isOk, Except.toBool]

/-- A public variable's position among the index's public rows. -/
def CheckedIndex.publicIndex (c : CheckedIndex source publicVars nv n) :
    Fin publicVars.length → Fin c.index.publicCount :=
  c.corresponds.publicIndex

/-- A checked index has one public row per public variable. -/
theorem CheckedIndex.publicCount_eq (c : CheckedIndex source publicVars nv n) :
    c.index.publicCount = publicVars.length :=
  c.corresponds.publicCount

/-- A public variable's row is its position in the list. -/
@[simp] theorem CheckedIndex.publicIndex_val (c : CheckedIndex source publicVars nv n)
    (i : Fin publicVars.length) : (c.publicIndex i).val = i.val :=
  rfl

/-- **Checked lifting.** A table satisfying a checked index yields a valuation satisfying every
source constraint and reading the public variables as the public input. -/
theorem CheckedIndex.lift [NeZero n] (c : CheckedIndex source publicVars nv n)
    (pub : Fin c.index.publicCount → F) (wTab : Fin n → Fin wCols → F)
    (hsat : c.index.Satisfies pub wTab) :
    ∃ V : Valuation F, (∀ con ∈ source, KimchiConstraint.Holds V con) ∧
      ∀ i : Fin publicVars.length, V publicVars[i] = pub (c.publicIndex i) :=
  KimchiConstraint.Wired.holds_of_satisfies c.admissible c.corresponds pub wTab hsat

end Checked

/-! ## Compiled circuits -/

section Built

variable [Field F] [DecidableEq F] {a avar b bvar β : Type}

/-- The checked index of a compiled circuit: `CheckedIndex.check?` at its constraints, its
public variables and its counter. -/
def checkBuilt? [CircuitType F a avar] [CircuitType F b bvar]
    (built : Built (KimchiConstraint F) (β × bvar)) (n zkRows : ℕ) (omega endoBase : F)
    (mds : Gate.Poseidon.Mds F) (shifts : Fin permCols → F) :
    Except CheckFailure (CheckedIndex built.constraints
      (compiledPublicVars (F := F) (a := a) (b := b) built) built.nextVar n) :=
  CheckedIndex.check? built.constraints (compiledPublicVars (F := F) (a := a) (b := b) built)
    built.nextVar n zkRows omega endoBase mds shifts

/-- A compiled circuit's checked index is built from the compiler's gate table at the
circuit's public variables. -/
theorem checkBuilt?_index [CircuitType F a avar] [CircuitType F b bvar]
    {built : Built (KimchiConstraint F) (β × bvar)} {n zkRows : ℕ} {omega endoBase : F}
    {mds : Gate.Poseidon.Mds F} {shifts : Fin permCols → F}
    {c : CheckedIndex built.constraints
      (compiledPublicVars (F := F) (a := a) (b := b) built) built.nextVar n}
    (h : checkBuilt? (a := a) (b := b) built n zkRows omega endoBase mds shifts = .ok c) :
    indexOfGates?
        (gateDataOf (reduceBuilt built) (compiledPublicVars (F := F) (a := a) (b := b) built)).2.1
        built.constraints (compiledPublicVars (F := F) (a := a) (b := b) built).length n zkRows
        omega endoBase mds shifts = some c.index :=
  CheckedIndex.check?_index h

end Built

end Snarky.Kimchi
