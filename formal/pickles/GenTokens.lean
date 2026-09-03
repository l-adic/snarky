import PicklesFixture.TokenParser
import PicklesFixture.Emit

/-!
# `gen-tokens` — the linearization token codegen

Reads `pickles-codegen`'s Rust dump and writes the Lean token modules, mirroring what
`Generator.purs` does for PureScript. Driven by `make gen-linearization-lean` at the repo
root; the output is committed, so this runs on a proof-systems bump, not per build.

    LINEARIZATION_JSON_DIR   where fp.json / fq.json live
    LINEARIZATION_LEAN_DIR   where Fp.lean / Fq.lean are written
-/

open Pickles.Fixture

def emit (jsonDir leanDir file name defName field : String) : IO Unit := do
  let toks ← readLinearization s!"{jsonDir}/{file}.json"
  let path := s!"{leanDir}/{name}.lean"
  IO.FS.writeFile path (moduleSrc defName field toks)
  IO.println s!"wrote {path} ({toks.size} tokens)"

def main : IO Unit := do
  let jsonDir := (← IO.getEnv "LINEARIZATION_JSON_DIR").getD
    "../../packages/pickles-codegen/rust/output"
  let leanDir := (← IO.getEnv "LINEARIZATION_LEAN_DIR").getD "Pickles/Linearization"
  IO.FS.createDirAll leanDir
  emit jsonDir leanDir "fp" "Fp" "fpTokens" "Fp"
  emit jsonDir leanDir "fq" "Fq" "fqTokens" "Fq"
