import Kimchi.Sponge.Poseidon
import Lean.Data.Json

/-!
# Poseidon sponge check against mina_poseidon traces

Runs the `fq_kimchi` sponge (`Kimchi.Sponge`, `Poseidon.lean`) over absorb/squeeze traces
recorded from proof-systems `mina_poseidon` (`fixtures/poseidon_fq_vectors.json`, produced by
`tools/ipa-fixture-dump`'s `poseidon_dump`) and compares every squeezed element.

Run (after `lake build Kimchi`): `scripts/check_sponge_vectors.sh`.
-/

open Lean Kimchi.Sponge CompElliptic.Fields.Pasta

abbrev Fq := VestaBaseField

def parseFq (j : Json) : Except String Fq := do
  match (← j.getStr?).toNat? with
  | some n => return (n : Fq)
  | none => throw "not a decimal natural"

structure Op where
  isAbsorb : Bool
  values : Array Fq

def parseOp (j : Json) : Except String Op := do
  match ← (← j.getObjVal? "op").getStr? with
  | "absorb" => return ⟨true, ← (← (← j.getObjVal? "values").getArr?).mapM parseFq⟩
  | "squeeze" => return ⟨false, ← (← (← j.getObjVal? "expect").getArr?).mapM parseFq⟩
  | op => throw s!"unknown op: {op}"

/-- Run one trace; `true` iff every squeeze matches the recorded output. -/
def runCase (ops : Array Op) : Bool :=
  (ops.foldl
    (fun (acc : State Fq × Bool) op =>
      let (sp, ok) := acc
      if op.isAbsorb then
        (absorb Fq.params sp op.values.toList, ok)
      else
        let (outs, sp) := squeezeN Fq.params sp op.values.size
        (sp, ok && decide (outs = op.values.toList)))
    (Fq.init, true)).2

def main : IO Unit := do
  let raw ← IO.FS.readFile "fixtures/poseidon_fq_vectors.json"
  let cases ← match Json.parse raw >>= fun j => do
      (← (← j.getObjVal? "cases").getArr?).mapM fun c => do
        (← (← c.getObjVal? "ops").getArr?).mapM parseOp with
    | .ok cs => pure cs
    | .error e => throw (IO.userError s!"vector parse error: {e}")
  let mut failed := 0
  for h : i in [0:cases.size] do
    let ok := runCase cases[i]
    IO.println s!"case {i}: {if ok then "OK" else "FAILED"}"
    unless ok do failed := failed + 1
  unless failed = 0 do
    throw (IO.userError s!"{failed} sponge vector case(s) FAILED")
  IO.println "✓ the Poseidon sponge matches mina_poseidon on all traces"

#eval main
