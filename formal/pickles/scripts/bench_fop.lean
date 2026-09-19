import PicklesFixture
import Snarky.Compile

/-!
# What the prover interpreter costs on a real circuit

`Snarky.prove` walks a circuit's `AsProver` bodies and fills the witness table. Nothing in
the tree has ever run it on anything the size of a verifier gadget, so this driver times it
on `finalize_other_proof` at the step side's deployed parameters: `build` for the rows,
`prove` for the witness, and the five output bits read back off the table it produced.

The input is a placeholder, not a deployed proof — the bits are expected to read 0. What is
being measured is the walk, not the verdict.

Run: `lake exe bench-fop` from `formal/`.
-/

open Snarky Pickles PicklesFixture CompElliptic.Fields.Pasta

/-- A placeholder input at the deployed round count: every cell zero but the domain the step
side is compiled at. -/
def dummyInput : StepFop StepIPARounds :=
  let z : StepFop StepIPARounds :=
    CircuitType.fieldsToValue (Vector.replicate (CircuitType.size Fp (StepFop StepIPARounds)) 0)
  (z.1, z.2.1, z.2.2.1, z.2.2.2.1, 16)

def main : IO Unit := do
  let nv := CircuitType.size Fp (StepFop StepIPARounds)
  let iv : StepFopVar StepIPARounds := inputVar (F := Fp) (a := StepFop StepIPARounds)
  let m := fopStepOn iv
  IO.println s!"input cells: {nv}"
  let t0 ← IO.monoMsNow
  let built := build m nv
  IO.println s!"build: {built.constraints.length} constraints, {built.nextVar} variables"
  let t1 ← IO.monoMsNow
  let st := seed (F := Fp) (avar := StepFopVar StepIPARounds) dummyInput
  match prove m st.nv st.env with
  | .error e =>
    let t2 ← IO.monoMsNow
    IO.println s!"build_ms={t1 - t0}  prove_ms={t2 - t1}"
    throw (IO.userError s!"prove failed: {repr e}")
  | .ok p =>
    let t2 ← IO.monoMsNow
    let read (b : BoolVar Fp) : ℕ := ((b : CVar Fp).val p.assignments.get).val
    IO.println s!"build_ms={t1 - t0}  prove_ms={t2 - t1}"
    IO.println s!"bits: finalized={read p.result.finalized} xiCorrect={read p.result.xiCorrect} \
      bCorrect={read p.result.bCorrect} cipCorrect={read p.result.cipCorrect} \
      plonkOk={read p.result.plonkOk}"
