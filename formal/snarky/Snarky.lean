import Snarky.Circuit.CVar
import Snarky.Backend.Assignments
import Snarky.Circuit.Types
import Snarky.Circuit.DSL.Monad
import Snarky.Circuit.DSL.Field
import Snarky.Circuit.DSL.Boolean
import Snarky.Circuit.DSL.Assert
import Snarky.Backend.Builder
import Snarky.Backend.Prover
import Snarky.Vec
import Snarky.Constraint.Basic
import Snarky.DSL
import Snarky.Example

/-!
# Snarky — the circuit-building DSL, deep-embedded

Root module of the `Snarky` library: a Lean port of the PureScript circuit DSL
(`Snarky.Circuit.DSL.Monad` and its two backend interpreters). See each module's header
for the correspondence with the `.purs` sources. The theorems the embedding exists to
state live beside their subjects: the interpreter laws in `Backend/{Builder,Prover}`, the
D12 gadget laws beside their gadgets in `Circuit/DSL/{Field,Boolean}`.
-/
