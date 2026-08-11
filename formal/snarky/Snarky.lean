import Snarky.Circuit.CVar
import Snarky.Backend.Assignments
import Snarky.Circuit.Types
import Snarky.Circuit.DSL.Monad
import Snarky.Circuit.DSL.Field
import Snarky.Circuit.DSL.Boolean
import Snarky.Circuit.DSL.Assert
import Snarky.Circuit.DSL.Bits
import Snarky.Circuit.DSL.Agreement
import Snarky.Backend.Builder
import Snarky.Backend.Prover
import Snarky.Backend.WP
import Snarky.Backend.Compile
import Snarky.Vec
import Snarky.Constraint.Basic
import Snarky.DSL
import Snarky.Example

/-!
# Snarky — the circuit-building DSL, deep-embedded

Root module of the `Snarky` library: a Lean port of the PureScript circuit DSL
(`packages/snarky`), aligned with it module by module — the completed sign-off walk is
recorded in `formal/docs/snarky-ps-alignment.md`, and each module header carries its own
name map against the `.purs` source. The theorems the embedding exists to state live
beside their subjects.

## The layout

- `Circuit/CVar` — affine expressions over circuit variables, their folds, and the
  affine-reduction pipeline with its correctness law.
- `Circuit/Types` — the value/variable duality (`CircuitType`) and the base instances,
  with their round-trip laws.
- `Circuit/DSL/Monad` — the reified op tree `CircuitM` (constraint type abstract) and the
  `witness`/`readVar`/`assignVars` layer; `Circuit/DSL/{Field,Boolean,Assert,Bits}` — the
  gadgets, each beside its soundness/completeness laws; `DSL` — the PS-export barrel.
- `Backend/Assignments` — the prover's witness table and its extension order.
- `Backend/{Builder,Prover}` — the two interpreters, with the interpreter laws
  (witness-independence, allocation agreement, completeness, the bind laws).
- `Backend/WP` — the `Std.Do` weakest-precondition interpretation of `build`, the
  soundness reading the gadget triple laws are stated in.
- `Backend/Compile` — whole-circuit `compile`/`solve` and the seam `solve_complete`.
- `Constraint/Basic` — the concrete reference constraint model.
- `Vec` — kernel-reduction-friendly vector utilities (everything here is validated by
  `decide`).
- `Example` — the framework showcase (the walked `cubic` circuit) and the executable
  edges no triple states.

The `Snarky.Kimchi.*` bridge — a DSL constraint's check agrees with the verified
Generic-gate checker — is deliberately NOT imported here: it pulls Mathlib in wholesale
via `Kimchi`, while this root's only Mathlib touch is `Example`'s targeted `ZMod` import.
-/
