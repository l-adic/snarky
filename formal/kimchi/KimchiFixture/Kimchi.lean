import Kimchi.Verifier.Kimchi
import BulletproofFixture
import FixtureKit.Parse
import Lean.Data.Json

/-!
# Chunked kimchi wire-proof fixture ingestion

Decoders for the CHUNKED kimchi proof + verifier-key records
(`Kimchi/Verifier/Kimchi.lean`), reading both fixture formats:

* the chunked format (`kimchi_proof_{vesta,pallas}_nc2.json`, from `tools/fixture-dump`'s
  `kimchi_proof_dump_nc2`): every commitment a chunk ARRAY of points, every evaluation
  `[[ζ-chunks], [ζω-chunks]]`, plus the proof-carried `evals_public`;
* the one-chunk format (`kimchi_proof_vesta.json`): bare points and `[ζ, ζω]` scalar
  pairs, decoded as singleton chunk vectors — so the one-chunk fixture runs through the
  chunked verifier (the no-regression adjudication).

The two are distinguished per field by the first element's shape (coordinate/value
strings vs nested arrays); `evals_public` is absent in the one-chunk format and decodes
to `none`.
-/

open Bulletproof

namespace Kimchi.Fixture

open FixtureKit

open Lean Bulletproof.Fixture Kimchi.Verifier Kimchi.Verifier

/-- A chunked commitment: a bare `[x, y]` point (one-chunk format — first element a
coordinate string) as a singleton, else an array of points. -/
def parseComm (C : Ipa.CommitmentCurve) (j : Json) : Except String (Array C.Point) := do
  match (← j.getArr?).toList with
  | [] => throw "empty commitment"
  | Json.str _ :: _ => return #[← parsePt C j]
  | _ => parseArrOf (parsePt C) j

/-- A chunked evaluation pair: `[ζ, ζω]` value strings (one-chunk format) as singleton
chunk vectors, else `[[ζ-chunks], [ζω-chunks]]`. -/
def parseEval (C : Ipa.CommitmentCurve) (j : Json) :
    Except String (Kimchi.Verifier.PointEvaluations (Array C.ScalarField)) := do
  let a ← j.getArr?
  unless a.size = 2 do throw s!"expected an evaluation pair, got {a.size} entries"
  match a[0]! with
  | Json.str _ =>
    return { zeta := #[← parseZMod (n := C.scalar) a[0]!]
             zetaOmega := #[← parseZMod (n := C.scalar) a[1]!] }
  | _ =>
    return { zeta := ← parseArrOf (parseZMod (n := C.scalar)) a[0]!
             zetaOmega := ← parseArrOf (parseZMod (n := C.scalar)) a[1]! }

/-- The chunked kimchi proof wire record. `evals_public` is optional wire data: absent
(the one-chunk format) decodes to `none`. -/
def parseKimchiProof (C : Ipa.CommitmentCurve) (j : Json) :
    Except String (KimchiProof C) := do
  let fld (k : String) : Except String Json := j.getObjVal? k
  let pe := parseEval C
  let evals : ProofEvaluations (Array C.ScalarField) :=
    { w := ← parseArrOf pe (← fld "evals_w")
      z := ← pe (← fld "evals_z")
      s := ← parseArrOf pe (← fld "evals_s")
      coefficients := ← parseArrOf pe (← fld "evals_coefficients")
      genericSelector := ← pe (← fld "evals_generic_selector")
      poseidonSelector := ← pe (← fld "evals_poseidon_selector")
      completeAddSelector := ← pe (← fld "evals_complete_add_selector")
      mulSelector := ← pe (← fld "evals_mul_selector")
      emulSelector := ← pe (← fld "evals_emul_selector")
      endomulScalarSelector := ← pe (← fld "evals_endomul_scalar_selector") }
  let pubEvals ← match (fld "evals_public").toOption with
    | some pj => some <$> pe pj
    | none => pure none
  return { wComm := ← parseArrOf (parseComm C) (← fld "w_comm")
           zComm := ← parseComm C (← fld "z_comm")
           tComm := ← parseArrOf (parsePt C) (← fld "t_comm")
           evals
           pubEvals
           ftEval1 := ← parseZMod (← fld "ft_eval1")
           opening := ← parseProof C j }

/-- The chunked verifier key (SRS excluded — parse it with `parseSRSAt` at
`Nat.log2 max_poly_size`), with the fr-sponge parameters pinned by the caller. -/
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
           sigmaComm := ← parseArrOf (parseComm C) (← fld "sigma_comm")
           coefficientsComm := ← parseArrOf (parseComm C) (← fld "coefficients_comm")
           genericComm := ← parseComm C (← fld "generic_comm")
           poseidonComm := ← parseComm C (← fld "psm_comm")
           completeAddComm := ← parseComm C (← fld "complete_add_comm")
           mulComm := ← parseComm C (← fld "mul_comm")
           emulComm := ← parseComm C (← fld "emul_comm")
           endomulScalarComm := ← parseComm C (← fld "endomul_scalar_comm")
           shifts := ← parseArrOf (parseZMod (n := C.scalar)) (← fld "shifts")
           zkRows := ← nat "zk_rows"
           endo := ← parseZMod (← fld "endo")
           digest := ← parseZMod (← fld "digest")
           lagrangeBasis := ← parseArrOf (parseComm C) (← fld "lagrange_basis")
           frParams := frParams }

end Kimchi.Fixture
