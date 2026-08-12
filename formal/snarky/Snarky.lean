import Snarky.Circuit.CVar
import Snarky.Backend.Assignments
import Snarky.Circuit.Types
import Snarky.Circuit.DSL.Monad
import Snarky.Circuit.DSL.Field
import Snarky.Circuit.DSL.Boolean
import Snarky.Circuit.DSL.Assert
import Snarky.Circuit.DSL.Bits
import Snarky.Circuit.DSL.Utils
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

## The proof architecture

Every gadget carries one law per reading, stated as a `Std.Do` triple in a schematic
shape (`Sound` for the builder reading, `Complete` for the prover reading — both in
`Backend/WP`) and registered with `@[spec]`. A composed circuit's proof walks its
do-block: `simp only` with the circuit's definition, then `mvcgen` — which applies each
callee's registered law — then `simp [circuitVal]` (the value-reading simp set
registered in `Circuit/CVar`), leaving arithmetic for `grind`/`ring`. The prover
reading is selected by the constraint tag `ProverC`; `sound_spec_iff` and
`complete_spec_iff` convert either law to its interpreter-level statement, and
`post_of_prove` ties an honest run to the soundness relation; `Example` runs the
whole recipe on one circuit.

## The layout

- `Circuit/CVar` — affine expressions over circuit variables, their folds, and the
  affine-reduction pipeline with its correctness law.
- `Circuit/Types` — the value/variable duality (`CircuitType`) and the base instances,
  with their round-trip laws.
- `Circuit/DSL/Monad` — the reified op tree `CircuitM` (constraint type abstract) and the
  `witness`/`readVar`/`assignVars` layer; `Circuit/DSL/{Field,Boolean,Assert,Bits}` — the
  gadgets, each beside its soundness/completeness laws; `DSL` — the PS-export barrel.
- `Backend/Assignments` — the prover's witness table with its extension order, and the
  total `Valuation` the soundness reading quantifies over, with the bridges between the
  two.
- `Backend/{Builder,Prover}` — the two interpreters, with the interpreter laws
  (witness-independence, allocation agreement, completeness, the bind laws).
- `Backend/WP` — the `Std.Do` weakest-precondition interpretations of `build` and
  `prove` (the two readings the gadget triples are stated in), the spec shapes, and the
  primitive/loop specs.
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
