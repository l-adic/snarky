import Kimchi.Verifier.Kimchi
import Kimchi.Fixture.Ipa
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

open Lean Kimchi.Fixture Kimchi.Fixture.Ipa Kimchi.Verifier

abbrev C := IpaVesta.curve
abbrev F := C.ScalarField

def parseF : Json → Except String F := parseZMod

def parsePE (j : Json) : Except String (F × F) := do
  let a ← parseArrOf parseF j
  unless a.size = 2 do throw s!"expected an evaluation pair, got {a.size} entries"
  return (a.getD 0 0, a.getD 1 0)

def main : IO Unit := do
  let path := "fixtures/kimchi_proof_vesta.json"
  let raw ← IO.FS.readFile path
  let r : Except String (KimchiVK C × KimchiProof C × Array F) := do
    let j ← Json.parse raw
    let fld (k : String) : Except String Json := j.getObjVal? k
    let nat (k : String) : Except String ℕ := do
      match (← (← fld k).getStr?).toNat? with
      | some v => pure v
      | none => throw s!"field {k} is not a numeral"
    let n ← nat "n"
    let g ← parseArrOf (parsePt C) (← fld "srs_g")
    let k := Nat.log2 n
    unless 2 ^ k = n ∧ g.size = n do throw "srs/domain size mismatch"
    let srs : Kimchi.Commitment.IPA.SRS C.Point :=
      { k := k
        g := fun i => g.getD i 0
        h := ← parsePt C (← fld "srs_h")
        U := 0 }
    let vk : KimchiVK C :=
      { domainLog2 := k
        omega := ← parseF (← fld "omega")
        srs := srs
        sigmaComm := ← parseArrOf (parsePt C) (← fld "sigma_comm")
        coefficientsComm := ← parseArrOf (parsePt C) (← fld "coefficients_comm")
        genericComm := ← parsePt C (← fld "generic_comm")
        poseidonComm := ← parsePt C (← fld "psm_comm")
        completeAddComm := ← parsePt C (← fld "complete_add_comm")
        mulComm := ← parsePt C (← fld "mul_comm")
        emulComm := ← parsePt C (← fld "emul_comm")
        endomulScalarComm := ← parsePt C (← fld "endomul_scalar_comm")
        shifts := ← parseArrOf parseF (← fld "shifts")
        zkRows := ← nat "zk_rows"
        endo := ← parseF (← fld "endo")
        digest := ← parseZMod (← fld "digest")
        lagrangeBasis := ← parseArrOf (parsePt C) (← fld "lagrange_basis")
        frParams := KimchiVesta.frParams }
    let proof : KimchiProof C :=
      { wComm := ← parseArrOf (parsePt C) (← fld "w_comm")
        zComm := ← parsePt C (← fld "z_comm")
        tComm := ← parseArrOf (parsePt C) (← fld "t_comm")
        w := ← parseArrOf parsePE (← fld "evals_w")
        z := ← parsePE (← fld "evals_z")
        s := ← parseArrOf parsePE (← fld "evals_s")
        coefficients := ← parseArrOf parsePE (← fld "evals_coefficients")
        genericSelector := ← parsePE (← fld "evals_generic_selector")
        poseidonSelector := ← parsePE (← fld "evals_poseidon_selector")
        completeAddSelector := ← parsePE (← fld "evals_complete_add_selector")
        mulSelector := ← parsePE (← fld "evals_mul_selector")
        emulSelector := ← parsePE (← fld "evals_emul_selector")
        endomulScalarSelector := ← parsePE (← fld "evals_endomul_scalar_selector")
        ftEval1 := ← parseF (← fld "ft_eval1")
        opening := ← parseProof C j }
    let pub ← parseArrOf parseF (← fld "public")
    return (vk, proof, pub)
  match r with
  | .error e => throw (IO.userError s!"{path}: fixture parse error: {e}")
  | .ok (vk, proof, pub) =>
    let ok := kimchiVerify C vk proof pub
    let badEval := { proof with z := (proof.z.1 + 1, proof.z.2) }
    let badComm := { proof with tComm := proof.tComm.modify 0 (· + vk.srs.h) }
    let badFt := { proof with ftEval1 := proof.ftEval1 + 1 }
    let r1 := !kimchiVerify C vk badEval pub
    let r2 := !kimchiVerify C vk badComm pub
    let r3 := !kimchiVerify C vk badFt pub
    IO.println s!"{path}: verify: {if ok then "ACCEPT" else "REJECT"}, \
      corrupted z eval: {if r1 then "REJECT (expected)" else "ACCEPT (BUG)"}, \
      corrupted t comm: {if r2 then "REJECT (expected)" else "ACCEPT (BUG)"}, \
      corrupted ft_eval1: {if r3 then "REJECT (expected)" else "ACCEPT (BUG)"}"
    unless ok && r1 && r2 && r3 do
      throw (IO.userError "kimchi verifier check FAILED")
    IO.println "✓ the executable kimchi verifier accepts the production proof and \
      rejects corruptions"

#eval main
