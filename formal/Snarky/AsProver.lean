import Snarky.CVar

/-!
# The prover-side witness monad

Port of the `AsProver` monad from `Snarky.Circuit.DSL.Monad`
(packages/snarky/src/Snarky/Circuit/DSL/Monad.purs, lines 111–122). In PureScript an
`AsProver f r a` is a function from a prover context to `Effect a`; here it is the pure
reader-except stack over the current `Assignments` — witness computations read assigned
values and may fail, nothing else.

Deliberate deviation from PS: the advice row `r` (the `Run r` oracle layer and its
`AdviceHandler`) is dropped in this port; it can be reintroduced later as an extra reader
parameter without disturbing anything built on top.

`AsProver` values are what the deep-embedded `CircuitM` (see `Snarky.Monad`) stores at its
`existsOp`/`assignOp` nodes: the embedding is deep in the circuit structure but *shallow*
in the witness functions, which stay semantic. The constraint builder provably never runs
them (`Snarky.Laws.build_eq_of_sameShape`).
-/

namespace Snarky

/-- A prover-only witness computation: read the current assignments, produce a value or
fail (PS `AsProver f r a`, minus the advice row). `ReaderT`/`Except` supply the `Monad` and
`LawfulMonad` instances. -/
abbrev AsProver (F : Type u) : Type u → Type u :=
  ReaderT (Assignments F) (Except EvalError)

namespace AsProver

/-- Read the value of an affine expression from the current assignments (PS `readCVar`). -/
def readCVar [Add F] [Mul F] (x : CVar F) : AsProver F F :=
  fun env => x.eval env

/-- Fail with a message (PS `throwAsProver`). -/
def throw (msg : String) : AsProver F α :=
  fun _ => .error (.custom msg)

/-- Run a witness computation against an assignment (PS `runAsProver`, minus `Effect`). -/
def run (p : AsProver F α) (env : Assignments F) : Except EvalError α :=
  p env

end AsProver

end Snarky
