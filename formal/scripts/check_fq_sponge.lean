import Kimchi.Sponge.GroupMap
import Kimchi.Fixture.Check
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

/-- One trace operation: an absorption input or an expected squeeze output. -/
inductive VOp (Fq Fr : Type)
  | absorbFr (x : Fr)
  | absorbG (p : Fq × Fq)
  | absorbGInfinity
  | challengeFq (expect : Fq)
  | challenge (expect : Fr)
  | squeezeChallenge (expect : Fr)

def parseOp {Fq Fr : Type} (pFq : Json → Except String Fq) (pFr : Json → Except String Fr)
    (j : Json) : Except String (VOp Fq Fr) := do
  match ← (← j.getObjVal? "op").getStr? with
  | "absorb_fr" => return .absorbFr (← pFr (← j.getObjVal? "value"))
  | "absorb_g" => return .absorbG (← parsePoint pFq (← j.getObjVal? "point"))
  | "absorb_g_inf" => return .absorbGInfinity
  | "challenge_fq" => return .challengeFq (← pFq (← j.getObjVal? "expect"))
  | "challenge" => return .challenge (← pFr (← j.getObjVal? "expect"))
  | "squeeze_challenge" => return .squeezeChallenge (← pFr (← j.getObjVal? "expect"))
  | op => throw s!"unknown op: {op}"

/-- One op's transition and verdict: absorptions are free, squeezes compare against the
expectation. -/
def step {q p : ℕ} [Field (ZMod q)] [Field (ZMod p)] (spec : Spec q p) (s : FqSponge.S q)
    (op : VOp (ZMod q) (ZMod p)) : FqSponge.S q × Bool :=
  match op with
  | .absorbFr x => (absorbFr spec s x, true)
  | .absorbG pt => (absorbG spec s pt, true)
  | .absorbGInfinity => (absorbGInfinity spec s, true)
  | .challengeFq e => let (x, s) := challengeFq spec s; (s, decide (x = e))
  | .challenge e => let (x, s) := challenge spec s; (s, decide (x = e))
  | .squeezeChallenge e => let (x, s) := squeezeChallenge spec s; (s, decide (x = e))

def checkSponge {q p : ℕ} [Field (ZMod q)] [Field (ZMod p)] (spec : Spec q p)
    (path : String) : IO Bool :=
  checkCases (parseOp (parseZMod (n := q)) (parseZMod (n := p))) FqSponge.init (step spec)
    path

def checkGroupMap : IO Bool := do
  let parseFq : Json → Except String FqVesta.Fq := parseZMod
  let raw ← IO.FS.readFile "fixtures/group_map_vectors.json"
  let vs ← match Json.parse raw >>= fun j => do
      (← (← j.getObjVal? "vectors").getArr?).mapM fun v => do
        return (← parseFq (← v.getObjVal? "t"),
                ← parseFq (← v.getObjVal? "x"), ← parseFq (← v.getObjVal? "y")) with
    | .ok vs => pure vs
    | .error e => throw (IO.userError s!"group_map vectors parse error: {e}")
  let failed := vs.foldl
    (fun n (v : _ × _ × _) =>
      let u := GroupMapVesta.toGroup v.1
      if (u.x, u.y) = (v.2.1, v.2.2) then n else n + 1) 0
  IO.println s!"fixtures/group_map_vectors.json: {vs.size - failed}/{vs.size} OK"
  return failed = 0

def main : IO Unit := do
  let okV ← checkSponge FqVesta.spec "fixtures/fq_sponge_vectors.json"
  let okP ← checkSponge FqPallas.spec "fixtures/fq_sponge_pallas_vectors.json"
  let okG ← checkGroupMap
  unless okV && okP && okG do
    throw (IO.userError "Fq-sponge / group-map vector check FAILED")
  IO.println
    "✓ the Fq-sponges over both Pasta curves and the map-to-curve match proof-systems"

#eval main
