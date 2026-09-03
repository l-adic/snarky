import Kimchi.Protocol.Linearization
import Kimchi.Verifier.Kimchi
import Bulletproof.Wire
import Pickles.Linearization.Spec
import Pickles.Linearization.Fp
import Pickles.Linearization.Fq
import Pasta.Endo
import FixtureKit.Parse
import Lean.Data.Json

/-!
# The token interpreter against production

The deployed linearization is a compiled `PolishToken` program;
`kimchi/scripts/check_linearization.lean` checks the closed-form `gateLinearization`
against production's `constant_term`, and this driver checks the ported program against
both. Two checks, on the same fixture pair the closed form is checked against and on the
Pallas-side fixture, which is what anchors the `Fq` stream's constants:

1. `evaluate tokens env = constant_term` — the ported stack machine reproduces production's
   own scalar, so the port is faithful to the Rust it was transcribed from.
2. `evaluate tokens env = gateLinearization endo mds α e` — the token stream and the closed
   form agree at the production challenges.

The second is a numerical instance of the reflection certificate
(`Pickles.Reflect.evaluate_fpTokens`), checked at production's challenges rather than
symbolically.

## What the live stream exercises

The endomorphism constant each certificate is decided against (`Pasta.pallasEndo` for
`Fp`, `Pasta.vestaEndo` for `Fq`) must equal the fixture's recorded `endo`, and the MDS
matrix enters the token evaluation, so a pass anchors both to production.

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

/-- A `[zeta, zeta_omega]` evaluation pair. -/
def parsePE {n : ℕ} (j : Json) : Except String (ZMod n × ZMod n) := do
  let a ← parseArrOf (parseZMod (n := n)) j
  unless a.size = 2 do throw s!"expected an evaluation pair, got {a.size} entries"
  return (a.getD 0 0, a.getD 1 0)

/-- Adjudicate one fixture against the deployed token stream `toks` for the same curve,
with the Lean side's MDS matrix `mds` and endomorphism constant `endo`. The fixture's
recorded `endo` must equal `endo`: that is what anchors the constant the certificate is
decided against to production. -/
def runFixture {n : ℕ} [Fact n.Prime] (toks : Array PolishToken)
    (mds : Kimchi.Gate.Poseidon.Mds (ZMod n)) (endo : ZMod n) (evalPath : String) :
    IO Unit := do
  let raw ← IO.FS.readFile evalPath
  let r : Except String (Bool × Bool × ZMod n) := do
    let j ← Json.parse raw
    let fld (k : String) : Except String Json := j.getObjVal? k
    let f (k : String) : Except String (ZMod n) := do parseZMod (← fld k)
    let endoRec ← f "endo"
    unless endoRec = endo do
      throw "the fixture's recorded endo is not the Lean constant"
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
    let e : Evals (ZMod n) :=
      { w := fun i => (wArr.getD i (0, 0)).1
        wOmega := fun i => (wArr.getD i (0, 0)).2
        z := zPE.1, zOmega := zPE.2
        s := fun i => (sArr.getD i (0, 0)).1
        coeffs := fun i => (cArr.getD i (0, 0)).1
        genericSelector := genPE.1, poseidonSelector := posPE.1
        completeAddSelector := addPE.1, mulSelector := mulPE.1
        emulSelector := emulPE.1, endoScalarSelector := endoselPE.1 }
    let mine : ZMod n := evaluate (e.toEnv endo mds α β γ 0 zkpmZ (fun _ _ => 0)
      LookupEvals.zero (fun _ => false)) toks
    return (decide (mine = constTarget),
            decide (mine = gateLinearization endo mds α e),
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
  -- one the vesta fixtures pair with, and the pallas fixture pairs with the Fq stream.
  -- The dump is named by field for exactly this reason: named by curve it reads the
  -- wrong way round, and the mistake is quiet — five of the six gates use only the
  -- literals 0..3, identical in both Pasta fields, so only EndoScalar's large constants
  -- disagree. The endo constants and MDS matrices are the ones `Pickles.Reflect`'s
  -- certificates are decided against, so a pass here anchors each certificate's
  -- constants to production.
  let mdsP := Kimchi.Verifier.mdsOfParams IpaVesta.curve.frParams
  let mdsQ := Kimchi.Verifier.mdsOfParams IpaPallas.curve.frParams
  runFixture fpTokens mdsP Pasta.pallasEndo s!"{kdir}/linearization_vesta.json"
  runFixture fpTokens mdsP Pasta.pallasEndo s!"{kdir}/linearization_vesta_emul.json"
  runFixture fqTokens mdsQ Pasta.vestaEndo s!"{kdir}/linearization_pallas.json"
  IO.println "✓ the ported token interpreter reproduces production's constant_term, and \
    agrees with the closed-form gate linearization, on both circuits and both fields"

#eval main
