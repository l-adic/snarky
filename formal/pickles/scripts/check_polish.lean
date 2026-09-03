import Kimchi.Protocol.Linearization
import Kimchi.Verifier.Kimchi
import Bulletproof.Wire
import Pickles.Linearization.Spec
import Pickles.Linearization.Fp
import FixtureKit.Parse
import Lean.Data.Json

/-!
# The token interpreter against production

The deployed linearization is a compiled `PolishToken` program;
`kimchi/scripts/check_linearization.lean` checks the closed-form `gateLinearization`
against production's `constant_term`, and this driver checks the ported program against
both. Two checks, on the same fixture pair:

1. `evaluate tokens env = constant_term` — the ported stack machine reproduces production's
   own scalar, so the port is faithful to the Rust it was transcribed from.
2. `evaluate tokens env = gateLinearization endo mds α e` — the token stream and the closed
   form agree at the production challenges.

The second is a numerical instance of the reflection certificate
(`Pickles.Reflect.evaluate_fpTokens`), checked at production's challenges rather than
symbolically.

## What the live stream exercises

Only 1539 of the 4220 tokens are reachable: the seven top-level `SkipIfNot` guards
(`RangeCheck0/1`, `ForeignField{Add,Mul}`, `Xor`, `Rot`, `LookupTables`) are all disabled in
the modelled fragment, and every remaining guard nests inside one of them. What survives
uses `Witness`, `Coefficient` and the six modelled gates' `Index` columns; the `Literal`,
`Mds` and `EndoCoefficient` constants; and `Alpha` alone among the challenges.

So `beta`, `gamma`, `jointCombiner`, `unnormalizedLagrangeBasis` and
`vanishesOnZeroKnowledgeAndPreviousRows` are not adjudicated here: they are permutation-
and lookup-side, outside the constant term, which is why `gateLinearization` does not take
them either.
-/

open Lean FixtureKit Bulletproof Kimchi.Protocol Kimchi.Protocol.Linearization
open Pickles.Linearization
open scoped Kimchi

abbrev C := IpaVesta.curve
abbrev F := C.ScalarField

/-- A `[zeta, zeta_omega]` evaluation pair. -/
def parsePE (j : Json) : Except String (F × F) := do
  let a ← parseArrOf (parseZMod (n := _)) j
  unless a.size = 2 do throw s!"expected an evaluation pair, got {a.size} entries"
  return (a.getD 0 0, a.getD 1 0)

/-- Adjudicate one fixture pair: production's evaluations against the deployed token
stream for the same curve. -/
def runFixture (evalPath : String) : IO Unit := do
  let toks := fpTokens
  let raw ← IO.FS.readFile evalPath
  let r : Except String (Bool × Bool × F) := do
    let j ← Json.parse raw
    let fld (k : String) : Except String Json := j.getObjVal? k
    let f (k : String) : Except String F := do parseZMod (← fld k)
    let endo ← f "endo"
    let α ← f "alpha"
    let β ← f "beta"
    let γ ← f "gamma"
    let zkpmZ ← f "zkpm_zeta"
    let constTarget ← f "constant_term"
    let wArr ← parseArrOf parsePE (← fld "w")
    let cArr ← parseArrOf parsePE (← fld "coefficients")
    let zPE ← parsePE (← fld "z")
    let sArr ← parseArrOf parsePE (← fld "s")
    let genPE ← parsePE (← fld "generic_selector")
    let posPE ← parsePE (← fld "poseidon_selector")
    let addPE ← parsePE (← fld "complete_add_selector")
    let mulPE ← parsePE (← fld "mul_selector")
    let emulPE ← parsePE (← fld "emul_selector")
    let endoselPE ← parsePE (← fld "endomul_scalar_selector")
    unless wArr.size = wCols ∧ cArr.size = coeffCols ∧ sArr.size = sigmaRows do
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
    let M := Kimchi.Verifier.mdsOfParams IpaVesta.curve.frParams
    let mine : F := evaluate (e.toEnv endo M α β γ 0 zkpmZ (fun _ _ => 0) LookupEvals.zero
      (fun _ => false)) toks
    return (decide (mine = constTarget),
            decide (mine = gateLinearization endo M α e),
            constTarget)
  match r with
  | .error err => throw (IO.userError s!"{evalPath}: {err}")
  | .ok (hProd, hClosed, target) =>
    -- Non-vacuity: a zero target would let both checks pass without witnessing anything.
    if target = 0 then
      throw (IO.userError s!"{evalPath}: constant_term is ZERO — adjudicated vacuously")
    IO.println s!"{evalPath} ({toks.size} tokens): \
      vs production constant_term: {if hProd then "✓" else "✗"}, \
      vs closed-form gateLinearization: {if hClosed then "✓" else "✗"}"
    unless hProd && hClosed do
      throw (IO.userError s!"{evalPath}: polish-interpreter check FAILED")

def main : IO Unit := do
  let kdir := (← IO.getEnv "KIMCHI_FIXTURES_DIR").getD "../kimchi/fixtures"
  -- `IpaVesta.curve.ScalarField` is Fp (Pallas's base field), so the Fp stream is the
  -- one these fixtures pair with. The dump is named by FIELD for exactly this reason:
  -- named by curve it reads the wrong way round, and the mistake is quiet — five of the
  -- six gates use only the literals 0..3, identical in both Pasta fields, so only
  -- EndoScalar's large constants disagree.
  runFixture s!"{kdir}/linearization_vesta.json"
  runFixture s!"{kdir}/linearization_vesta_emul.json"
  IO.println "✓ the ported token interpreter reproduces production's constant_term, and \
    agrees with the closed-form gate linearization, on both circuits"

#eval main
