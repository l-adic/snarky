import Kimchi.Sponge.Poseidon
import Kimchi.Fixture.Check
import Lean.Data.Json

/-!
# Poseidon sponge checks against mina_poseidon traces

Runs the `fq_kimchi` and `fp_kimchi` sponges (`Kimchi.Sponge`, `Poseidon.lean`) over
absorb/squeeze traces recorded from proof-systems `mina_poseidon`
(`fixtures/poseidon_{fq,fp}_vectors.json`, produced by `tools/fixture-dump`'s
`sponge_dump`) and compares every squeezed element.

Run (after `lake build Kimchi`): `scripts/check_sponge_vectors.sh`.
-/

open Lean Kimchi.Sponge Kimchi.Fixture CompElliptic.Fields.Pasta

structure Op (F : Type) where
  isAbsorb : Bool
  values : Array F

def parseOp {F : Type} (parseF : Json → Except String F) (j : Json) :
    Except String (Op F) := do
  match ← (← j.getObjVal? "op").getStr? with
  | "absorb" => return ⟨true, ← parseArrOf parseF (← j.getObjVal? "values")⟩
  | "squeeze" => return ⟨false, ← parseArrOf parseF (← j.getObjVal? "expect")⟩
  | op => throw s!"unknown op: {op}"

/-- One op's transition and verdict: absorb freely, squeeze against the expectation. -/
def step {F : Type} [Field F] [DecidableEq F] (params : Params F) (sp : State F) (op : Op F) :
    State F × Bool :=
  if op.isAbsorb then
    (absorb params sp op.values.toList, true)
  else
    let (outs, sp) := squeezeN params sp op.values.size
    (sp, decide (outs = op.values.toList))

def checkFile {F : Type} [Field F] [DecidableEq F] (params : Params F)
    (parseF : Json → Except String F) (path : String) : IO Bool :=
  checkCases (parseOp parseF) Kimchi.Sponge.init (step params) path

def main : IO Unit := do
  let okFq ← checkFile Fq.params (parseZMod (n := PALLAS_SCALAR_CARD))
    "fixtures/poseidon_fq_vectors.json"
  let okFp ← checkFile Fp.params (parseZMod (n := PALLAS_BASE_CARD))
    "fixtures/poseidon_fp_vectors.json"
  unless okFq && okFp do
    throw (IO.userError "sponge vector case(s) FAILED")
  IO.println "✓ the Poseidon sponges over both Pasta fields match mina_poseidon"

#eval main
