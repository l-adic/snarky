import Snarky.CVar
import Snarky.AsProver
import Snarky.Monad
import Snarky.Builder
import Snarky.Prover
import Snarky.Vec
import Snarky.Constraint.Basic
import Snarky.Constraint.R1CS
import Snarky.Types
import Snarky.DSL
import Snarky.Laws
import Snarky.Example

/-!
# Snarky — the circuit-building DSL, deep-embedded

Root module of the `Snarky` library: a Lean port of the PureScript circuit DSL
(`Snarky.Circuit.DSL.Monad` and its two backend interpreters). See each module's header
for the correspondence with the `.purs` sources, and `Snarky/Laws.lean` for the theorems
the embedding exists to state.
-/
