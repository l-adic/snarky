import Snarky.CVar
import Snarky.AsProver
import Snarky.Monad

/-!
# Snarky — the circuit-building DSL, deep-embedded

Root module of the `Snarky` library: a Lean port of the PureScript circuit DSL
(`Snarky.Circuit.DSL.Monad`). This first slice is the monad itself — `CVar` expressions,
the prover-side `AsProver` witness monad, and the deep-embedded `CircuitM` op tree with
its `LawfulMonad` instance. The two interpreters (constraint builder and witness prover,
mirroring `Snarky.Backend.Builder`/`Prover`) and the interpreter laws land in follow-up
modules.
-/
