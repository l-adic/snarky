import KimchiFixture.Cache
import CompElliptic.Fields.Pasta
import Lean.Data.Json

/-!
# The proof-cache decoder against the Rust-produced fixture

`KimchiFixture.Cache` reads PureScript's proof cache — the verification key in
`vkRawToJson`'s shape, the proof in arkworks serde with compressed points. Nothing in Lean
read either encoding before, so this driver checks the decoder against an independent
witness: `kimchi_proof_pallas_pickles.json`, the same wrap key and proof rendered by Rust in
the decimal format `KimchiFixture.Kimchi` has always read.

The key is compared through the cache: `SimpleChain.json`'s wrap bucket carries the same key
under the same digest. The proof is compared through the file the fixture was rendered from,
`simple_chain/wrap1/proof.serde.json`: no cached proof is that fixture's statement — the
sideload fixture and the `SimpleChain` spec prove different chains — but the file is the
same serde encoding the cache stores. Every field is compared. A compressed point decoded
to the wrong root, a little-endian slip, a swapped `zeta`/`zeta_omega`, a chunk in the wrong
order — each shows up as a named mismatch here rather than as a `kimchiVerify` rejection.

Run from `formal/` or from `kimchi/`; `KIMCHI_FIXTURES_DIR`, `PROOF_CACHE` and `SERDE_PROOF`
override the defaults: `lake env lean --run kimchi/scripts/check_cache_decode.lean`.
-/

open Lean Bulletproof Kimchi.Verifier Kimchi.Verifier.Wire Kimchi.Fixture

/-- The wrap side's commitment curve. -/
abbrev CP := IpaPallas.curve

/-- The digest Rust recorded for simple_chain's wrap key — the entry under test. -/
def wrapDigest : String :=
  "4279052005494948743128055706375583678382362068038840518138978030458004318946"

/-- A point list as coordinate pairs, for comparison. -/
def ptCoords (ps : Array CP.Point) : List (CP.BaseField × CP.BaseField) :=
  ps.toList.map fun p => (p.x, p.y)

/-- One named comparison. -/
def check1 {α : Type} [DecidableEq α] (name : String) (a b : α) : Bool × String :=
  (a = b, s!"  {if a = b then "✓" else "✗"} {name}")

/-- The first of the candidate paths that exists — the package-relative default from the
package directory, the workspace-relative one from `formal/`. -/
def firstExisting (candidates : List String) : IO String := do
  for c in candidates do
    if ← System.FilePath.pathExists c then return c
  throw (IO.userError s!"none of {candidates} exists")

def main : IO Unit := do
  let dir ← match ← IO.getEnv "KIMCHI_FIXTURES_DIR" with
    | some d => pure d
    | none => firstExisting ["fixtures", "kimchi/fixtures"]
  let cachePath ← match ← IO.getEnv "PROOF_CACHE" with
    | some p => pure p
    | none => firstExisting (
        ["../../packages/pickles/test/fixtures/proof-cache/SimpleChain.json",
         "../packages/pickles/test/fixtures/proof-cache/SimpleChain.json"])
  let serdePath ← match ← IO.getEnv "SERDE_PROOF" with
    | some p => pure p
    | none => firstExisting (
        ["../../packages/pickles/test/fixtures/simple_chain/wrap1/proof.serde.json",
         "../packages/pickles/test/fixtures/simple_chain/wrap1/proof.serde.json"])
  let fx ← IO.FS.readFile s!"{dir}/kimchi_proof_pallas_pickles.json"
  let (rvk, rproof) ← match do
      let j ← Json.parse fx
      pure (← parseVK CP j, ← parseKimchiProof CP j) with
    | .error e => throw (IO.userError s!"fixture: {e}")
    | .ok r => pure r
  let (entries, skipped) ← match Cache.parseFile CP rvk.endo
      CompElliptic.Fields.Pasta.pallasBase.sqrt? (← IO.FS.readFile cachePath) with
    | .error e => throw (IO.userError s!"cache: {e}")
    | .ok es => pure es
  IO.println s!"{cachePath}: {entries.size} Pallas-side entries decoded, \
    {skipped} Vesta-side bucket(s) skipped"
  let some e := entries.find? (·.vkDigest = wrapDigest)
    | throw (IO.userError s!"no entry with digest {wrapDigest}")
  let vk := e.vk
  let checks : List (Bool × String) :=
    [ check1 "vk.domainLog2" vk.domainLog2 rvk.domainLog2
    , check1 "vk.omega" vk.omega rvk.omega
    , check1 "vk.sigmaComm" (vk.sigmaComm.toList.map ptCoords) (rvk.sigmaComm.toList.map ptCoords)
    , check1 "vk.coefficientsComm" (vk.coefficientsComm.toList.map ptCoords)
        (rvk.coefficientsComm.toList.map ptCoords)
    , check1 "vk.genericComm" (ptCoords vk.genericComm) (ptCoords rvk.genericComm)
    , check1 "vk.poseidonComm" (ptCoords vk.poseidonComm) (ptCoords rvk.poseidonComm)
    , check1 "vk.completeAddComm" (ptCoords vk.completeAddComm) (ptCoords rvk.completeAddComm)
    , check1 "vk.mulComm" (ptCoords vk.mulComm) (ptCoords rvk.mulComm)
    , check1 "vk.emulComm" (ptCoords vk.emulComm) (ptCoords rvk.emulComm)
    , check1 "vk.endomulScalarComm" (ptCoords vk.endomulScalarComm) (ptCoords rvk.endomulScalarComm)
    , check1 "vk.shifts" vk.shifts.toList rvk.shifts.toList
    , check1 "vk.zkRows" vk.zkRows rvk.zkRows
    , check1 "vk.prevChallenges" vk.prevChallenges rvk.prevChallenges
    , check1 "vk.digest" vk.digest rvk.digest ]
  for (_, line) in checks do IO.println line
  -- The proof, from the serde file the fixture was rendered from.
  let p ← match Json.parse (← IO.FS.readFile serdePath) >>= fun sj =>
      Cache.parseProof CP CompElliptic.Fields.Pasta.pallasBase.sqrt? sj with
    | .error e => throw (IO.userError s!"serde proof: {e}")
    | .ok v => pure v
  let pchecks : List (Bool × String) :=
    [ check1 "proof.wComm" (p.wComm.toList.map ptCoords) (rproof.wComm.toList.map ptCoords)
    , check1 "proof.zComm" (ptCoords p.zComm) (ptCoords rproof.zComm)
    , check1 "proof.tComm" (ptCoords p.tComm) (ptCoords rproof.tComm)
    , check1 "proof.ftEval1" p.ftEval1 rproof.ftEval1
    , check1 "proof.evals.w" (p.evals.w.toList.map fun a => (a.zeta, a.zetaOmega))
        (rproof.evals.w.toList.map fun a => (a.zeta, a.zetaOmega))
    , check1 "proof.evals.z" (p.evals.z.zeta, p.evals.z.zetaOmega)
        (rproof.evals.z.zeta, rproof.evals.z.zetaOmega)
    , check1 "proof.evals.s" (p.evals.s.toList.map fun a => (a.zeta, a.zetaOmega))
        (rproof.evals.s.toList.map fun a => (a.zeta, a.zetaOmega))
    , check1 "proof.evals.coefficients"
        (p.evals.coefficients.toList.map fun a => (a.zeta, a.zetaOmega))
        (rproof.evals.coefficients.toList.map fun a => (a.zeta, a.zetaOmega))
    , check1 "proof.evals.selectors"
        ([p.evals.genericSelector, p.evals.poseidonSelector, p.evals.completeAddSelector,
          p.evals.mulSelector, p.evals.emulSelector, p.evals.endomulScalarSelector].map
          fun a => (a.zeta, a.zetaOmega))
        ([rproof.evals.genericSelector, rproof.evals.poseidonSelector,
          rproof.evals.completeAddSelector, rproof.evals.mulSelector, rproof.evals.emulSelector,
          rproof.evals.endomulScalarSelector].map fun a => (a.zeta, a.zetaOmega))
    , check1 "proof.pubEvals" (p.pubEvals.map fun a => (a.zeta, a.zetaOmega))
        (rproof.pubEvals.map fun a => (a.zeta, a.zetaOmega))
    , check1 "proof.opening.lr"
        (p.opening.lr.toList.map fun (l, r) => ((l.x, l.y), (r.x, r.y)))
        (rproof.opening.lr.toList.map fun (l, r) => ((l.x, l.y), (r.x, r.y)))
    , check1 "proof.opening.delta" (p.opening.delta.x, p.opening.delta.y)
        (rproof.opening.delta.x, rproof.opening.delta.y)
    , check1 "proof.opening.z1" p.opening.z1 rproof.opening.z1
    , check1 "proof.opening.z2" p.opening.z2 rproof.opening.z2
    , check1 "proof.opening.sg" (p.opening.sg.x, p.opening.sg.y)
        (rproof.opening.sg.x, rproof.opening.sg.y)
    , check1 "proof.prevChallenges"
        (p.prevChallenges.toList.map fun r => (ptCoords r.comm, r.chals))
        (rproof.prevChallenges.toList.map fun r => (ptCoords r.comm, r.chals)) ]
  for (_, line) in pchecks do IO.println line
  let step := match e.step with
    | some (d, pi) => s!"step link: digest {d.take 12}…, public input {pi.length} chars"
    | none => "step link: none"
  IO.println step
  unless checks.all (·.1) do throw (IO.userError "VK decode mismatch")
  unless pchecks.all (·.1) do throw (IO.userError "proof decode mismatch")
  IO.println "✓ the cache decoder agrees with the Rust-produced fixture on every field"

#eval main
