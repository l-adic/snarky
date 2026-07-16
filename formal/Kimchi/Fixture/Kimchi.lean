import Kimchi.Verifier.Kimchi
import Kimchi.Fixture.Ipa

/-!
# Kimchi wire-proof fixture ingestion

Decoders for the complete kimchi proof + verifier-key fixture (`tools/fixture-dump`'s
`kimchi_proof_dump`), shared by the fixture scripts: the proof record, the verifier
key (SRS separate — it is universal, not part of the key), and the public input. Built
on the shared element decoders (`Kimchi/Fixture/Parse.lean`) and the IPA plumbing
(`parsePt`/`parseSRSAt`/`parseProof`, `Kimchi/Fixture/Ipa.lean`). The fr-sponge
Poseidon parameters are not wire data — the caller pins them (the per-curve
`KimchiVesta.frParams`/`KimchiPallas.frParams`).
-/

namespace Kimchi.Fixture.Kimchi

open FixtureKit

open Lean Kimchi.Fixture Kimchi.Fixture.Ipa Kimchi.Verifier

/-- A `[zeta, zeta_omega]` evaluation pair. -/
def parsePointEval (C : Ipa.CommitmentCurve) (j : Json) :
    Except String (PointEval C.ScalarField) := do
  let a ← parseArrOf (parseZMod (n := C.scalar)) j
  unless a.size = 2 do throw s!"expected an evaluation pair, got {a.size} entries"
  return { zeta := a.getD 0 0, zetaOmega := a.getD 1 0 }

/-- The kimchi proof wire record. -/
def parseKimchiProof (C : Ipa.CommitmentCurve) (j : Json) :
    Except String (KimchiProof C) := do
  let fld (k : String) : Except String Json := j.getObjVal? k
  let pe := parsePointEval C
  return { wComm := ← parseArrOf (parsePt C) (← fld "w_comm")
           zComm := ← parsePt C (← fld "z_comm")
           tComm := ← parseArrOf (parsePt C) (← fld "t_comm")
           w := ← parseArrOf pe (← fld "evals_w")
           z := ← pe (← fld "evals_z")
           s := ← parseArrOf pe (← fld "evals_s")
           coefficients := ← parseArrOf pe (← fld "evals_coefficients")
           genericSelector := ← pe (← fld "evals_generic_selector")
           poseidonSelector := ← pe (← fld "evals_poseidon_selector")
           completeAddSelector := ← pe (← fld "evals_complete_add_selector")
           mulSelector := ← pe (← fld "evals_mul_selector")
           emulSelector := ← pe (← fld "evals_emul_selector")
           endomulScalarSelector := ← pe (← fld "evals_endomul_scalar_selector")
           ftEval1 := ← parseZMod (← fld "ft_eval1")
           opening := ← parseProof C j }

/-- The verifier key (SRS excluded — parse it with `parseSRSAt` at
`Nat.log2 n`), with the fr-sponge parameters pinned by the caller. -/
def parseVK (C : Ipa.CommitmentCurve)
    (frParams : Poseidon.Params C.ScalarField) (j : Json) :
    Except String (KimchiVK C) := do
  let fld (k : String) : Except String Json := j.getObjVal? k
  let nat (k : String) : Except String ℕ := do
    match (← (← fld k).getStr?).toNat? with
    | some v => pure v
    | none => throw s!"field {k} is not a numeral"
  let n ← nat "n"
  return { domainLog2 := Nat.log2 n
           omega := ← parseZMod (← fld "omega")
           sigmaComm := ← parseArrOf (parsePt C) (← fld "sigma_comm")
           coefficientsComm := ← parseArrOf (parsePt C) (← fld "coefficients_comm")
           genericComm := ← parsePt C (← fld "generic_comm")
           poseidonComm := ← parsePt C (← fld "psm_comm")
           completeAddComm := ← parsePt C (← fld "complete_add_comm")
           mulComm := ← parsePt C (← fld "mul_comm")
           emulComm := ← parsePt C (← fld "emul_comm")
           endomulScalarComm := ← parsePt C (← fld "endomul_scalar_comm")
           shifts := ← parseArrOf (parseZMod (n := C.scalar)) (← fld "shifts")
           zkRows := ← nat "zk_rows"
           endo := ← parseZMod (← fld "endo")
           digest := ← parseZMod (← fld "digest")
           lagrangeBasis := ← parseArrOf (parsePt C) (← fld "lagrange_basis")
           frParams := frParams }

end Kimchi.Fixture.Kimchi
