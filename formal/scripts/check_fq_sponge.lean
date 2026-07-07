import Kimchi.Sponge.GroupMap
import Kimchi.Fixture.Trace
import Lean.Data.Json

/-!
# Fq-sponge and map-to-curve checks against proof-systems vectors

Replays op traces of `DefaultFqSponge` over both Pasta curves
(`fixtures/fq_sponge_vectors.json` for Vesta, `fixtures/fq_sponge_pallas_vectors.json` for
Pallas): every ordered pair of op kinds — scalar, point, and infinity absorption, raw field
squeezes, 128-bit prechallenges, endo-expanded effective challenges — plus longer mixed
sequences; the Pallas traces exercise the high-bits/low-bit `absorb_fr` branch. Replayed
through the sponge layer (`Kimchi/Sponge/FqSponge.lean`), and the SvdW
map (`fixtures/group_map_vectors.json`, `t ↦ to_group(t)`) through
`Kimchi/Sponge/GroupMap.lean`, comparing every output with the recorded production values.
All vector files are produced by `tools/fixture-dump` (`sponge_dump`) directly from
`mina_poseidon` / `groupmap` — independent of any proof.

Run (after `lake build Kimchi`): `scripts/check_fq_sponge.sh`.
-/

open Lean Kimchi.Fixture Kimchi.Sponge Kimchi.Sponge.FqSponge
open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Curves.Pasta

/-- One trace operation: an absorption input or an expected squeeze output. -/
inductive VOp {F : Type} [Field F] (E : SWCurve F) (Fr : Type)
  | absorbFr (x : Fr)
  | absorbG (P : SWPoint E)
  | challengeFq (expect : F)
  | challenge (expect : Fr)
  | squeezeChallenge (expect : Fr)

def parseOp {F Fr : Type} [Field F] [DecidableEq F] (E : SWCurve F)
    (pF : Json → Except String F) (pFr : Json → Except String Fr) (j : Json) :
    Except String (VOp E Fr) := do
  match ← (← j.getObjVal? "op").getStr? with
  | "absorb_fr" => return .absorbFr (← pFr (← j.getObjVal? "value"))
  | "absorb_g" => return .absorbG (← parseSWPoint pF E (← j.getObjVal? "point"))
  | "absorb_g_inf" => return .absorbG 0
  | "challenge_fq" => return .challengeFq (← pF (← j.getObjVal? "expect"))
  | "challenge" => return .challenge (← pFr (← j.getObjVal? "expect"))
  | "squeeze_challenge" => return .squeezeChallenge (← pFr (← j.getObjVal? "expect"))
  | op => throw s!"unknown op: {op}"

/-- One op's transition and verdict: absorptions are free, squeezes compare against the
expectation. -/
def step {base scalar : ℕ} [Field (ZMod base)] [Field (ZMod scalar)]
    (spec : Spec base scalar) {E : SWCurve (ZMod base)} (s : FqSponge.S base)
    (op : VOp E (ZMod scalar)) : FqSponge.S base × Bool :=
  match op with
  | .absorbFr x => (absorbFr spec s x, true)
  | .absorbG P => (absorbG spec s P, true)
  | .challengeFq e => let (x, s) := challengeFq spec s; (s, decide (x = e))
  | .challenge e => let (x, s) := challenge spec s; (s, decide (x = e))
  | .squeezeChallenge e => let (x, s) := squeezeChallenge spec s; (s, decide (x = e))

def checkSponge {base scalar : ℕ} [Field (ZMod base)] [Field (ZMod scalar)]
    (spec : Spec base scalar) (E : SWCurve (ZMod base)) (path : String) : IO Bool :=
  Trace.check (parseOp E (parseZMod (n := base)) (parseZMod (n := scalar))) FqSponge.init
    (step spec) path

def checkGroupMap {q : ℕ} [Field (ZMod q)] [DecidableEq (ZMod q)]
    (toGroup : ZMod q → ZMod q × ZMod q) (path : String) : IO Bool := do
  let parseF : Json → Except String (ZMod q) := parseZMod
  let raw ← IO.FS.readFile path
  let vs ← match Json.parse raw >>= fun j => do
      (← (← j.getObjVal? "vectors").getArr?).mapM fun v => do
        return (← parseF (← v.getObjVal? "t"),
                ← parseF (← v.getObjVal? "x"), ← parseF (← v.getObjVal? "y")) with
    | .ok vs => pure vs
    | .error e => throw (IO.userError s!"{path}: vectors parse error: {e}")
  let failed := vs.foldl
    (fun n (v : _ × _ × _) => if toGroup v.1 = (v.2.1, v.2.2) then n else n + 1) 0
  IO.println s!"{path}: {vs.size - failed}/{vs.size} OK"
  return failed = 0

def main : IO Unit := do
  let okV ← checkSponge FqVesta.spec Vesta.curve "fixtures/fq_sponge_vectors.json"
  let okP ← checkSponge FqPallas.spec Pallas.curve "fixtures/fq_sponge_pallas_vectors.json"
  let okGV ← checkGroupMap (fun t => let u := GroupMapVesta.toGroup t; (u.x, u.y))
    "fixtures/group_map_vectors.json"
  let okGP ← checkGroupMap (fun t => let u := GroupMapPallas.toGroup t; (u.x, u.y))
    "fixtures/group_map_pallas_vectors.json"
  unless okV && okP && okGV && okGP do
    throw (IO.userError "Fq-sponge / group-map vector check FAILED")
  IO.println
    "✓ the Fq-sponges over both Pasta curves and the map-to-curve match proof-systems"

#eval main
