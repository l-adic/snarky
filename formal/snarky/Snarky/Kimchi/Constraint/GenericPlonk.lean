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
  (`c = lhs − rhs`), the same move `Reduction.lean`'s equality op makes.
  Contradiction-free circuits behave identically; a statically-false constraint
  compiles to an unsatisfiable system where PS crashes at construction, and the
  prover interpreter SUCCEEDS where PS's would crash — the emission is a no-op there
  (the kimchi prover checks nothing per constraint).

No semantics is stated here: the meaning of the emitted encodings and the
faithfulness of this reducer are deliberately not part of this package; the
byte-equality corpus is the oracle.

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

/-- The `Basic` reducer is a seam: the branches consume reduced results, which agree,
and every tail is counter-inert. -/
theorem reduce_seam [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F]
    [DecidableEq F] (c : Basic F) :
    Seam (reduce (m := PlonkBuilder F) c) (reduce (m := PlonkProver F) c) := by
  rcases c with ⟨l, r, o⟩ | ⟨a, b⟩ | ⟨a, b⟩ | v <;> simp only [reduce]
  · refine Seam.bind (reduceAffineExpression_seam _) fun l' => ?_
    refine Seam.bind (reduceAffineExpression_seam _) fun r' => ?_
    refine Seam.bind (reduceAffineExpression_seam _) fun o' => ?_
    rcases l'.1 with _ | vl <;> rcases r'.1 with _ | vr <;> rcases o'.1 with _ | vo
    all_goals try exact addGeneric_seam _
    exact Seam.ite (fun _ => Seam.pure _) fun _ => addGeneric_seam _
  · refine Seam.bind (reduceAffineExpression_seam _) fun l' => ?_
    refine Seam.bind (reduceAffineExpression_seam _) fun r' => ?_
    exact addEquals_seam _
  · refine Seam.bind (reduceAffineExpression_seam _) fun x => ?_
    refine Seam.bind (reduceAffineExpression_seam _) fun y => ?_
    rcases x.1 with _ | x1 <;> rcases y.1 with _ | x2
    all_goals try exact addGeneric_seam _
    exact Seam.ite (fun _ => Seam.pure _) fun _ => addGeneric_seam _
  · refine Seam.bind (reduceAffineExpression_seam _) fun x => ?_
    rcases x.1 with _ | xv
    · exact Seam.ite (fun _ => Seam.pure _) fun _ => addGeneric_seam _
    · exact addGeneric_seam _

end Snarky.Kimchi
