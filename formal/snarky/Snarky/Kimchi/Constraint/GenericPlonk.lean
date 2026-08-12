import Snarky.Constraint.Basic
import Snarky.Kimchi.Constraint.Reduction

/-!
# The Basic-constraint reducer

Port of `Snarky.Constraint.Kimchi.GenericPlonk`
(packages/snarky-kimchi/src/Snarky/Constraint/Kimchi/GenericPlonk.purs): `reduce`, the
fan-out from the DSL's four `Basic` constraints to `PlonkReductionM` emissions. Each
operand is reduced to `c·v` form first (in PS source order — emission order is fixture
bytes, K2), then one generic or equals constraint is emitted, dispatching on which
operands degenerated to constants.

Name map: `reduce` keeps its name; the case dispatch keeps PS's coefficient
patterns verbatim.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- The three all-constant contradiction sites (`r1cs`, `square`, `boolean`) throw in PS;
  the total Lean rendering emits the corresponding unsatisfiable generic row
  (`c = lhs − rhs`), the same move `Reduction.lean`'s equality op makes. Reachable
  behaviour is unchanged; a statically-false constraint compiles to an unsatisfiable
  system. The prover interpreter consequently SUCCEEDS where PS would crash — the
  emission is a no-op there (the kimchi prover checks nothing per constraint).

No semantics is stated here: the meaning of the emitted encodings and the
faithfulness of this reducer are deliberately not part of this package. The `decide`
examples below pin the emission shapes.

The PS test surface (`test/Test/Snarky/Circuit/Kimchi/GenericTest.purs`) exercises
the circuit layer end to end (an EC-addition circuit compiled through this reducer);
there are no module-level QuickCheck rows. The `decide` examples below stand in: one
emission per `Basic` constructor, traced, and a prover run.
-/

namespace Snarky.Kimchi

open Snarky

variable {F : Type} {m : Type → Type}

/-- Reduce one `Basic` constraint to its kimchi emissions (PS `reduce`): reduce every
operand to `c·v` form, then emit the one generic (or equals) constraint for the
surviving shape. The coefficient patterns are PS's, case for case. -/
def reduce [Add F] [Mul F] [Sub F] [Zero F] [One F] [Neg F] [DecidableEq F] [Monad m]
    [PlonkReductionM F m] : Basic F → m Unit
  | .r1cs left right output => do
    let l ← reduceAffineExpression left.reduceToAffineExpression
    let r ← reduceAffineExpression right.reduceToAffineExpression
    let o ← reduceAffineExpression output.reduceToAffineExpression
    match l.1, r.1, o.1 with
    | some vl, some vr, some vo =>
      addGenericPlonkConstraint
        { cl := 0, vl := some vl, cr := 0, vr := some vr, co := o.2, vo := some vo,
          m := -(l.2 * r.2), c := 0 }
    | some vl, some vr, none =>
      addGenericPlonkConstraint
        { cl := 0, vl := some vl, cr := 0, vr := some vr, co := 0, vo := none,
          m := l.2 * r.2, c := -o.2 }
    | some vl, none, some vo =>
      addGenericPlonkConstraint
        { cl := l.2 * r.2, vl := some vl, cr := 0, vr := none, co := -o.2,
          vo := some vo, m := 0, c := 0 }
    | none, some vr, some vo =>
      addGenericPlonkConstraint
        { cl := 0, vl := none, cr := l.2 * r.2, vr := some vr, co := -o.2,
          vo := some vo, m := 0, c := 0 }
    | some vl, none, none =>
      addGenericPlonkConstraint
        { cl := l.2 * r.2, vl := some vl, cr := 0, vr := none, co := 0, vo := none,
          m := 0, c := -o.2 }
    | none, some vr, none =>
      addGenericPlonkConstraint
        { cl := 0, vl := none, cr := l.2 * r.2, vr := some vr, co := 0, vo := none,
          m := 0, c := -o.2 }
    | none, none, some vo =>
      addGenericPlonkConstraint
        { cl := 0, vl := none, cr := 0, vr := none, co := o.2, vo := some vo, m := 0,
          c := -(l.2 * r.2) }
    | none, none, none =>
      if l.2 * r.2 = o.2 then pure ()
      else
        addGenericPlonkConstraint
          { cl := 0, vl := none, cr := 0, vr := none, co := 0, vo := none, m := 0,
            c := l.2 * r.2 - o.2 }
  | .square a b => do
    let x ← reduceAffineExpression a.reduceToAffineExpression
    let y ← reduceAffineExpression b.reduceToAffineExpression
    match x.1, y.1 with
    | some x1, some x2 =>
      addGenericPlonkConstraint
        { cl := 0, vl := some x1, cr := 0, vr := some x1, co := -y.2, vo := some x2,
          m := x.2 * x.2, c := 0 }
    | some x1, none =>
      addGenericPlonkConstraint
        { cl := 0, vl := some x1, cr := 0, vr := some x1, co := 0, vo := none,
          m := x.2 * x.2, c := -y.2 }
    | none, some x2 =>
      addGenericPlonkConstraint
        { cl := 0, vl := none, cr := 0, vr := none, co := y.2, vo := some x2, m := 0,
          c := -(x.2 * x.2) }
    | none, none =>
      if x.2 * x.2 = y.2 then pure ()
      else
        addGenericPlonkConstraint
          { cl := 0, vl := none, cr := 0, vr := none, co := 0, vo := none, m := 0,
            c := x.2 * x.2 - y.2 }
  | .equal a b => do
    let l ← reduceAffineExpression a.reduceToAffineExpression
    let r ← reduceAffineExpression b.reduceToAffineExpression
    addEqualsConstraint { cl := l.2, vl := l.1, cr := r.2, vr := r.1 }
  | .boolean b => do
    let x ← reduceAffineExpression b.reduceToAffineExpression
    match x.1 with
    | none =>
      if x.2 * x.2 = x.2 then pure ()
      else
        addGenericPlonkConstraint
          { cl := 0, vl := none, cr := 0, vr := none, co := 0, vo := none, m := 0,
            c := x.2 * x.2 - x.2 }
    | some v =>
      addGenericPlonkConstraint
        { cl := -x.2, vl := some v, cr := 0, vr := some v, co := 0, vo := none,
          m := x.2 * x.2, c := 0 }

/-! ## Examples (no module-level PS QuickCheck rows; these stand in) -/

/-- One multiplication over three variables emits the single product row. -/
example :
    Id.run ((reduce (m := TraceM Int) (.r1cs (.var 0) (.var 1) (.var 2))).run
        ⟨3, [], []⟩) =
      ((), ⟨3, [⟨0, some 0, 0, some 1, 1, some 2, -1, 0⟩], []⟩) := by decide

/-- Booleanity of a variable emits the self-product row. -/
example :
    Id.run ((reduce (m := TraceM Int) (.boolean (.var 0))).run ⟨1, [], []⟩) =
      ((), ⟨1, [⟨-1, some 0, 0, some 0, 0, none, 1, 0⟩], []⟩) := by decide

/-- Equating a variable with a constant emits one equals constraint. -/
example :
    Id.run ((reduce (m := TraceM Int) (.equal (.var 0) (.const 7))).run
        ⟨1, [], []⟩) =
      ((), ⟨1, [], [⟨1, some 0, 7, none⟩]⟩) := by decide

/-- A consistent all-constant square emits nothing (the PS-throw rendering's live
branch). -/
example :
    Id.run ((reduce (m := TraceM Int) (.square (.const 3) (.const 9))).run
        ⟨0, [], []⟩) =
      ((), ⟨0, [], []⟩) := by decide

/-- The prover ignores emissions: reducing the product constraint on a satisfying
table succeeds without allocating. -/
example :
    ((reduce (m := PlonkProver Int) (.r1cs (.var 0) (.var 1) (.var 2))).run
        ⟨3, fun v =>
          if v = 0 then some 2 else if v = 1 then some 3 else
          if v = 2 then some 6 else none⟩).toOption.map (fun p => p.2.nextVariable) =
      some 3 := by decide

end Snarky.Kimchi
