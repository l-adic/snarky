import Kimchi.Json

/-! Ingest dumped `(circuit, witness)` JSON and run the verified plonkish checker over the
    Pasta base field. This is the realized version of the original placeholder: the object
    both the PureScript prover and the Lean proofs refer to is the dumped gate list, and
    `Kimchi.Circuit.check` (faithful by `check_iff`) decides its satisfaction.

    Usage: `lean --run Main.lean [path …]`. With explicit paths it checks those; with no
    arguments it checks **every** `fixtures/*.json` in one process (one import load, rather
    than re-paying it per file). Exits non-zero if any fixture fails. -/

def checkOne (path : System.FilePath) : IO Bool := do
  let ok ← Kimchi.Json.loadAndCheck path
  IO.println s!"check {path} = {ok}"
  pure ok

def main (args : List String) : IO Unit := do
  let paths ← match args with
    | [] => do
      let entries ← System.FilePath.readDir "fixtures"
      let jsons := entries.filterMap fun e =>
        if e.fileName.endsWith ".json" then some e.path else none
      pure (jsons.qsort (·.toString < ·.toString)).toList
    | _ => pure (args.map System.FilePath.mk)
  let mut allOk := true
  for p in paths do
    let ok ← checkOne p
    allOk := allOk && ok
  unless allOk do IO.Process.exit 1
