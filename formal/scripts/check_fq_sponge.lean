import Kimchi.Sponge.GroupMap
import Lean.Data.Json

/-!
# Fq-sponge and map-to-curve checks against proof-systems vectors

Replays op traces of `DefaultFqSponge<VestaParameters>` (`fixtures/fq_sponge_vectors.json` —
scalar and point absorption, raw field squeezes, 128-bit prechallenges, endo-expanded
effective challenges) through the sponge layer (`Kimchi/Sponge/FqSponge.lean`), and the SvdW
map (`fixtures/group_map_vectors.json`, `t ↦ to_group(t)`) through
`Kimchi/Sponge/GroupMap.lean`, comparing every output with the recorded production values.
Both vector files are produced by `tools/fixture-dump` (`sponge_dump`) directly from
`mina_poseidon` / `groupmap` — independent of any proof.

Run (after `lake build Kimchi`): `scripts/check_fq_sponge.sh`.
-/

open Lean Kimchi.Sponge Kimchi.Sponge.FqVesta

def parseNat (s : String) : Except String ℕ :=
  match s.toNat? with
  | some n => .ok n
  | none => .error s!"not a decimal natural: {s.take 40}"

def parseFq (j : Json) : Except String Fq := do
  return ((← parseNat (← j.getStr?)) : ℕ)

def parseFr (j : Json) : Except String Fr := do
  return ((← parseNat (← j.getStr?)) : ℕ)

def parsePt (j : Json) : Except String (Fq × Fq) := do
  let a ← j.getArr?
  unless a.size = 2 do throw "point is not a coordinate pair"
  return (← parseFq a[0]!, ← parseFq a[1]!)

/-- One trace operation: an absorption input or an expected squeeze output. -/
inductive VOp
  | absorbFr (x : Fr)
  | absorbG (p : Fq × Fq)
  | challengeFq (expect : Fq)
  | challenge (expect : Fr)
  | squeezeChallenge (expect : Fr)

def parseOp (j : Json) : Except String VOp := do
  match ← (← j.getObjVal? "op").getStr? with
  | "absorb_fr" => return .absorbFr (← parseFr (← j.getObjVal? "value"))
  | "absorb_g" => return .absorbG (← parsePt (← j.getObjVal? "point"))
  | "challenge_fq" => return .challengeFq (← parseFq (← j.getObjVal? "expect"))
  | "challenge" => return .challenge (← parseFr (← j.getObjVal? "expect"))
  | "squeeze_challenge" => return .squeezeChallenge (← parseFr (← j.getObjVal? "expect"))
  | op => throw s!"unknown op: {op}"

/-- Run one trace; `true` iff every output matches. -/
def runCase (ops : Array VOp) : Bool :=
  (ops.foldl
    (fun (acc : S × Bool) op =>
      let (s, ok) := acc
      match op with
      | .absorbFr x => (absorbFr s x, ok)
      | .absorbG p => (absorbG s p, ok)
      | .challengeFq e => let (x, s) := challengeFq s; (s, ok && decide (x = e))
      | .challenge e => let (x, s) := challenge s; (s, ok && decide (x = e))
      | .squeezeChallenge e =>
        let (x, s) := squeezeChallenge s; (s, ok && decide (x = e)))
    (init, true)).2

def checkSponge : IO Bool := do
  let raw ← IO.FS.readFile "fixtures/fq_sponge_vectors.json"
  let cases ← match Json.parse raw >>= fun j => do
      (← (← j.getObjVal? "cases").getArr?).mapM fun c => do
        (← (← c.getObjVal? "ops").getArr?).mapM parseOp with
    | .ok cs => pure cs
    | .error e => throw (IO.userError s!"fq_sponge vectors parse error: {e}")
  let mut failed := 0
  for h : i in [0:cases.size] do
    unless runCase cases[i] do failed := failed + 1
  IO.println s!"fq-sponge op traces: {cases.size - failed}/{cases.size} OK"
  return failed = 0

def checkGroupMap : IO Bool := do
  let raw ← IO.FS.readFile "fixtures/group_map_vectors.json"
  let vs ← match Json.parse raw >>= fun j => do
      (← (← j.getObjVal? "vectors").getArr?).mapM fun v => do
        return (← parseFq (← v.getObjVal? "t"),
                ← parseFq (← v.getObjVal? "x"), ← parseFq (← v.getObjVal? "y")) with
    | .ok vs => pure vs
    | .error e => throw (IO.userError s!"group_map vectors parse error: {e}")
  let failed := vs.foldl
    (fun n (v : Fq × Fq × Fq) =>
      if GroupMapVesta.toGroup v.1 = (v.2.1, v.2.2) then n else n + 1) 0
  IO.println s!"group-map vectors:   {vs.size - failed}/{vs.size} OK"
  return failed = 0

def main : IO Unit := do
  let ok1 ← checkSponge
  let ok2 ← checkGroupMap
  unless ok1 && ok2 do
    throw (IO.userError "Fq-sponge / group-map vector check FAILED")
  IO.println "✓ the Fq-sponge and map-to-curve match proof-systems on all vectors"

#eval main
