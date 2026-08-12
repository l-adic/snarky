import Snarky.Circuit.DSL.Assert

/-!
# Sealing an expression to a single variable

Port of `Snarky.Circuit.DSL.Utils` (packages/snarky/src/Snarky/Circuit/DSL/Utils.purs):
`seal` reduces an expression to something that will not
expand under further operations — a lone unit-coefficient variable or a lone constant
passes through; anything else is witnessed into a fresh variable pinned by one `equal`
constraint.

Name map: `seal` becomes `sealVar` — `seal` is Lean's irreducibility command token,
unusable as a definition name (the `exists` → `witness` precedent); the witnessing
branch stays the named helper `sealCore` (the `mulCore`/`invCore` manner). No law is
stated here.
-/

namespace Snarky

variable {F c : Type u}

/-- `seal`'s witnessing branch: witness the expression's value into a fresh variable
and pin it with one `equal` constraint. Split out as a named unit
uniformly. -/
private def sealCore [Add F] [Mul F] [DecidableEq F] [BasicSystem F c] (x : FVar F) :
    CircuitM F c (FVar F) := do
  let y ← witness (val := F) (AsProver.readCVar x)
  assertEqual x y
  pure y

/-- Reduce an expression to a single variable if it is complex (PS `seal`; see the
name map above): a lone
unit-coefficient variable or a lone constant (under `CVar.reduceToAffineExpression`)
passes through unchanged; otherwise the value is witnessed into a fresh variable
constrained equal to the expression. -/
def sealVar [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c]
    (x : FVar F) : CircuitM F c (FVar F) :=
  match x.reduceToAffineExpression with
  | ⟨none, [(v, k)]⟩ => if k = 1 then pure (.var v) else sealCore x
  | ⟨some k, []⟩ => pure (.const k)
  | _ => sealCore x

end Snarky
