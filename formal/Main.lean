import Kimchi.Json

/-! Ingest a dumped `(circuit, witness)` JSON and run the verified plonkish checker over
    the Pasta base field. This is the realized version of the original placeholder: the
    object both the PureScript prover and the Lean proofs refer to is the dumped gate
    list, and `Kimchi.Circuit.check` (faithful by `check_iff`) decides its satisfaction. -/

def main (args : List String) : IO Unit := do
  let path : System.FilePath := args.headD "fixtures/add_complete_step.json"
  let ok ← Kimchi.Json.loadAndCheck path
  IO.println s!"check {path} = {ok}"
  if !ok then IO.Process.exit 1
