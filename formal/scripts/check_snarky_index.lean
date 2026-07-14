/-
Compile the DSL multiply circuit to a *wired* kimchi index and check that the stored
witness satisfies it — copy constraints (variable sharing through the permutation),
gate rows, and all. This exercises `Snarky.Kimchi.Compile.compile`: DSL circuit → gate
table + wiring cycles → `Kimchi.Fixture.PS.build` (domain synthesis + `Index.build?`) →
`Kimchi.Index.Satisfies`.

Run from `formal/`:  lake env lean scripts/check_snarky_index.lean
(Requires a prior `lake build Snarky`.)
-/
import Snarky.Kimchi.Compile

open Snarky.Kimchi.Compile

def main : IO Unit := do
  if check then
    IO.println "✓ the DSL mul circuit compiles to a wired kimchi index its witness satisfies"
  else
    throw (IO.userError "compiled index is not satisfied by its witness")

#eval main
