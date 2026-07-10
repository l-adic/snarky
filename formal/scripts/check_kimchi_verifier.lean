import Kimchi.Fixture.Kimchi
import Lean.Data.Json

/-! The executable kimchi verifier against a production proof
(`fixtures/kimchi_proof_vesta.json`, from `tools/fixture-dump`'s `kimchi_proof_dump`):
`kimchiVerify` — both sponge schedules, the scalar side through the fixture-pinned
closed forms, the `to_batch` assembly, and the warm-started IPA check — must ACCEPT
the complete wire proof that production `verify` accepts, and reject corruptions of
an evaluation, the quotient commitment, and `ft_eval1`. This is the composed
adjudication: every transcription judgment in `Kimchi/Verifier/Kimchi.lean` (absorb
orders, the public-commitment blinding, the warm-sponge handoff) either reproduces
production's accept bit or fails here. -/

open Lean Kimchi.Fixture Kimchi.Fixture.Ipa Kimchi.Fixture.Kimchi Kimchi.Verifier

abbrev C := IpaVesta.curve

def main : IO Unit := do
  let path := "fixtures/kimchi_proof_vesta.json"
  let raw ← IO.FS.readFile path
  let r : Except String (_ × KimchiVK C × KimchiProof C × Array C.ScalarField) := do
    let j ← Json.parse raw
    let vk ← parseVK C KimchiVesta.frParams j
    let σ ← parseSRSAt C vk.domainLog2 j
    let proof ← parseKimchiProof C j
    let pub ← parseArrOf (parseZMod (n := C.scalar)) (← j.getObjVal? "public")
    return (σ, vk, proof, pub)
  match r with
  | .error e => throw (IO.userError s!"{path}: fixture parse error: {e}")
  | .ok (σ, vk, proof, pub) =>
    let ok := kimchiVerify C σ vk proof pub
    let badEval := { proof with
      z := { proof.z with zeta := proof.z.zeta + 1 } }
    let badComm := { proof with tComm := proof.tComm.modify 0 (· + σ.h) }
    let badFt := { proof with ftEval1 := proof.ftEval1 + 1 }
    let r1 := !kimchiVerify C σ vk badEval pub
    let r2 := !kimchiVerify C σ vk badComm pub
    let r3 := !kimchiVerify C σ vk badFt pub
    IO.println s!"{path}: verify: {if ok then "ACCEPT" else "REJECT"}, \
      corrupted z eval: {if r1 then "REJECT (expected)" else "ACCEPT (BUG)"}, \
      corrupted t comm: {if r2 then "REJECT (expected)" else "ACCEPT (BUG)"}, \
      corrupted ft_eval1: {if r3 then "REJECT (expected)" else "ACCEPT (BUG)"}"
    unless ok && r1 && r2 && r3 do
      throw (IO.userError "kimchi verifier check FAILED")
    IO.println "✓ the executable kimchi verifier accepts the production proof and \
      rejects corruptions"

#eval main
