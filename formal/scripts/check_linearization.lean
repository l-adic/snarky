import Kimchi.Verifier.Linearization
import Kimchi.Verifier.Ipa
import Kimchi.Fixture.Parse
import Lean.Data.Json

/-! The verifier's scalar side against production (`fixtures/linearization_vesta.json`,
from `tools/fixture-dump`'s `linearization_dump`): the closed-form linearization of
`Kimchi/Verifier/Linearization.lean` must reproduce, on a real proof's challenges and
combined evaluations, the production values of the permutation vanishing evaluation,
`perm_scalars`, the token-evaluated `linearization.constant_term`, and `ft_eval0`. This
is where the expression framework's compiled token stream is adjudicated by value — it
never appears in a Lean statement. -/

open Lean Kimchi.Fixture Kimchi.Verifier Kimchi.Verifier.Linearization

abbrev C := IpaVesta.curve
abbrev F := C.ScalarField

def parseF : Json → Except String F := parseZMod

/-- A `[zeta, zeta_omega]` evaluation pair. -/
def parsePE (j : Json) : Except String (F × F) := do
  let a ← parseArrOf parseF j
  unless a.size = 2 do throw s!"expected an evaluation pair, got {a.size} entries"
  return (a.getD 0 0, a.getD 1 0)

def main : IO Unit := do
  let path := "fixtures/linearization_vesta.json"
  let raw ← IO.FS.readFile path
  let r : Except String Bool := do
    let j ← Json.parse raw
    let fld (k : String) : Except String Json := j.getObjVal? k
    let nat (k : String) : Except String ℕ := do
      match (← (← fld k).getStr?).toNat? with
      | some v => pure v
      | none => throw s!"field {k} is not a numeral"
    let n ← nat "n"
    let zkRows ← nat "zk_rows"
    let ω ← parseF (← fld "omega")
    let shiftsArr ← parseArrOf parseF (← fld "shifts")
    let endo ← parseF (← fld "endo")
    let α ← parseF (← fld "alpha")
    let β ← parseF (← fld "beta")
    let γ ← parseF (← fld "gamma")
    let ζ ← parseF (← fld "zeta")
    let zkpmZ ← parseF (← fld "zkpm_zeta")
    let pubArr ← parseArrOf (parseArrOf parseF) (← fld "public_evals")
    let wArr ← parseArrOf parsePE (← fld "w")
    let zPE ← parsePE (← fld "z")
    let sArr ← parseArrOf parsePE (← fld "s")
    let cArr ← parseArrOf parsePE (← fld "coefficients")
    let genPE ← parsePE (← fld "generic_selector")
    let posPE ← parsePE (← fld "poseidon_selector")
    let addPE ← parsePE (← fld "complete_add_selector")
    let mulPE ← parsePE (← fld "mul_selector")
    let emulPE ← parsePE (← fld "emul_selector")
    let endoselPE ← parsePE (← fld "endomul_scalar_selector")
    let ftEval0Target ← parseF (← fld "ft_eval0")
    let permTarget ← parseF (← fld "perm_scalar")
    let constTarget ← parseF (← fld "constant_term")
    unless (← fld "index_terms") == Json.mkObj [] do
      throw "expected an empty index_terms object (all selectors are evaluated)"
    unless wArr.size = 15 ∧ sArr.size = 6 ∧ cArr.size = 15 ∧ shiftsArr.size = 7 do
      throw "unexpected column counts"
    let e : Evals F :=
      { w := fun i => (wArr.getD i (0, 0)).1
        wOmega := fun i => (wArr.getD i (0, 0)).2
        z := zPE.1, zOmega := zPE.2
        s := fun i => (sArr.getD i (0, 0)).1
        coeffs := fun i => (cArr.getD i (0, 0)).1
        genericSelector := genPE.1, poseidonSelector := posPE.1
        completeAddSelector := addPE.1, mulSelector := mulPE.1
        emulSelector := emulPE.1, endoScalarSelector := endoselPE.1 }
    let shifts : Fin 7 → F := fun i => shiftsArr.getD i 0
    let pubEval := (pubArr.getD 0 #[]).getD 0 0
    let gc ← fld "gate_combined"
    let gateTarget (k : String) : Except String F := do parseF (← gc.getObjVal? k)
    let gEnv := evalEnv e
    let gates : List (String × F × F) :=
      [ ("generic", e.genericSelector
          * alphaCombo α ((Kimchi.Quotient.genericArgument (F := F)).constraints gEnv),
          ← gateTarget "generic"),
        ("poseidon", e.poseidonSelector
          * alphaCombo α ((Kimchi.Quotient.Poseidon.argument (F := F)).constraints gEnv),
          ← gateTarget "poseidon"),
        ("completeAdd", e.completeAddSelector
          * alphaCombo α ((Kimchi.Quotient.AddComplete.argument (F := F)).constraints gEnv),
          ← gateTarget "completeAdd"),
        ("varBaseMul", e.mulSelector
          * alphaCombo α ((Kimchi.Quotient.VarBaseMul.argument (F := F)).constraints gEnv),
          ← gateTarget "varBaseMul"),
        ("endoMul", e.emulSelector
          * alphaCombo α ((Kimchi.Quotient.EndoMul.argument endo).constraints gEnv),
          ← gateTarget "endoMul"),
        ("endoScalar", e.endoScalarSelector
          * alphaCombo α ((Kimchi.Quotient.EndoScalar.argument (F := F)).constraints gEnv),
          ← gateTarget "endoScalar") ]
    let gateReport := String.intercalate ", " (gates.map fun (name, mine, target) =>
      s!"{name}: {if mine = target then "✓" else "✗"}")
    let hGates := gates.all fun (_, mine, target) => mine = target
    let hZkpm := decide (zkpmEval n zkRows ω ζ = zkpmZ)
    let hPerm := decide (permScalar β γ α zkpmZ e = permTarget)
    let hConst := decide (gateLinearization endo α e = constTarget)
    let hFt := decide (ftEval0 n zkRows ω shifts endo α β γ ζ pubEval e = ftEval0Target)
    dbgTrace s!"{path}: zkpm: {if hZkpm then "✓" else "✗"}, \
      perm scalar: {if hPerm then "✓" else "✗"}, \
      gates [{gateReport}], \
      constant term: {if hConst then "✓" else "✗"}, \
      ft_eval0: {if hFt then "✓" else "✗"}" fun _ =>
    pure (hZkpm && hPerm && hGates && hConst && hFt)
  match r with
  | .error e => throw (IO.userError s!"{path}: {e}")
  | .ok false => throw (IO.userError "linearization check FAILED")
  | .ok true => IO.println "✓ the closed-form linearization matches the production \
      scalar side (zkpm, perm_scalars, constant term, ft_eval0)"

#eval main
