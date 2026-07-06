import Kimchi.Sponge.Poseidon
import Lean.Data.Json

/-!
# Poseidon sponge checks against mina_poseidon traces

Runs the `fq_kimchi` and `fp_kimchi` sponges (`Kimchi.Sponge`, `Poseidon.lean`) over
absorb/squeeze traces recorded from proof-systems `mina_poseidon`
(`fixtures/poseidon_{fq,fp}_vectors.json`, produced by `tools/fixture-dump`'s
`sponge_dump`) and compares every squeezed element.

Run (after `lake build Kimchi`): `scripts/check_sponge_vectors.sh`.
-/

open Lean Kimchi.Sponge CompElliptic.Fields.Pasta

structure Op (F : Type) where
  isAbsorb : Bool
  values : Array F

def parseOp {F : Type} (parseF : Json → Except String F) (j : Json) :
    Except String (Op F) := do
  match ← (← j.getObjVal? "op").getStr? with
  | "absorb" => return ⟨true, ← (← (← j.getObjVal? "values").getArr?).mapM parseF⟩
  | "squeeze" => return ⟨false, ← (← (← j.getObjVal? "expect").getArr?).mapM parseF⟩
  | op => throw s!"unknown op: {op}"

/-- Run one trace; `true` iff every squeeze matches the recorded output. -/
def runCase {F : Type} [Field F] [DecidableEq F] (params : Params F) (ops : Array (Op F)) :
    Bool :=
  (ops.foldl
    (fun (acc : State F × Bool) op =>
      let (sp, ok) := acc
      if op.isAbsorb then
        (absorb params sp op.values.toList, ok)
      else
        let (outs, sp) := squeezeN params sp op.values.size
        (sp, ok && decide (outs = op.values.toList)))
    (Kimchi.Sponge.init, true)).2

def checkFile {F : Type} [Field F] [DecidableEq F] (params : Params F)
    (parseF : Json → Except String F) (path : String) : IO Bool := do
  let raw ← IO.FS.readFile path
  let cases ← match Json.parse raw >>= fun j => do
      (← (← j.getObjVal? "cases").getArr?).mapM fun c => do
        (← (← c.getObjVal? "ops").getArr?).mapM (parseOp parseF) with
    | .ok cs => pure cs
    | .error e => throw (IO.userError s!"{path}: vector parse error: {e}")
  let failed := cases.foldl (fun n c => if runCase params c then n else n + 1) 0
  IO.println s!"{path}: {cases.size - failed}/{cases.size} OK"
  return failed = 0

def parseZMod {n : ℕ} (j : Json) : Except String (ZMod n) := do
  match (← j.getStr?).toNat? with
  | some k => return (k : ZMod n)
  | none => throw "not a decimal natural"

def main : IO Unit := do
  let okFq ← checkFile Fq.params (parseZMod (n := PALLAS_SCALAR_CARD))
    "fixtures/poseidon_fq_vectors.json"
  let okFp ← checkFile Fp.params (parseZMod (n := PALLAS_BASE_CARD))
    "fixtures/poseidon_fp_vectors.json"
  unless okFq && okFp do
    throw (IO.userError "sponge vector case(s) FAILED")
  IO.println "✓ the Poseidon sponges over both Pasta fields match mina_poseidon"

#eval main
