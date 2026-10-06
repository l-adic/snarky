import PicklesFixture.ApplicationFromShape
import PicklesFixture.ApplicationVerify

/-!
Reconstruct applications from their sidecars and shared SRSs, then compare every step and wrap
constraint system with the independent circuit dumps. With `LINKS=<app>,…`, also execute the
reconstructed circuits on cached advice, decide source and backend satisfaction, compare public
inputs, and apply the application verification and handover capstones directly.

Run from `formal/` with `PICKLES_DUMP_DIR` set. `PICKLES_PROOF_CACHE_DIR` selects the caches;
`LINKS_JOBS` controls the witness workers. Every selected cache entry must be covered.
The fixture manifest fixes the required application/tag list; selections never discover files.
-/

open Lean Snarky Pickles Pickles.Application PicklesFixture PicklesFixture.Application
open Bulletproof CompElliptic.Fields.Pasta Kimchi.Fixture Kimchi.Fixture.PS

private structure ProofCache where
  app : String
  wraps : Array (Cache.Entry CW)
  steps : Array (Cache.Entry CS)

private def cacheKey {C : Ipa.KimchiCurve} (p : Cache.Entry C) :=
  (p.vkDigest, p.publicInputKey)

private def verdict {p : Nat} [Fact p.Prime] (name : String) (r : CircuitRun p)
    (pub : Array (ZMod p)) : IO Bool := do
  let holds := @decide _ r.holds
  let same := r.pub == pub.toList
  IO.println s!"{name}: source constraints {holds}, backend satisfaction {r.satisfies}, \
    cached public input {same}"
  return holds && r.satisfies && same

private def verifyCached (C : Ipa.KimchiCurve) (name : String) (σ : SRS C.Point)
    (memo : Memo) (e : Cache.Entry C) : IO Bool := do
  let ⟨nc, vk, p⟩ ← IO.ofExcept (e.checked σ.k)
  let L ← basisFor C name σ nc e
  unless Kimchi.Verifier.kimchiVerifyWith C σ vk L p e.publicInput do return false
  for a in p.olds do
    let ok ← memoized memo.acc s!"{name}/{σ.k}/{a.sg.x.val}/{a.sg.y.val}/{a.u.toList.map (·.val)}"
      (fun _ => accOk σ a)
    unless ok do throw (IO.userError "cached proof carries an invalid old accumulator")
  return true

private def runApplications (S : Setup) (caches : List ProofCache) (workers : Nat) (memo : Memo)
    (covered : IO.Ref (List (String × String × String))) :
    List (String × ImportedApplication) → List ((D : Shape) × Context S D) → IO Unit
  | [], contexts => do
    for cache in caches do
      for p in cache.steps do
        unless (cache.app, cacheKey p) ∈ (← covered.get) do
          throw (IO.userError s!"{cache.app}: uncovered step proof {p.publicInputKey.take 20}")
      for p in cache.wraps do
        unless (cache.app, cacheKey p) ∈ (← covered.get) do
          throw (IO.userError s!"{cache.app}: uncovered wrap proof {p.publicInputKey.take 20}")
    validate contexts
  | (name, A) :: rest, contexts => do
    let app := (name.splitOn "/").head!
    let some cache := caches.find? (·.app == app)
      | throw (IO.userError s!"missing proof cache for {name}")
    let (run, context) ← runner S A app name
    let mut jobs : Array (IO Bool) := #[]
    for b in List.finRange A.shape.branches do
      let vk := A.assembled.wiring.backend.stepKeys[b].cvk
      for p in cache.steps.filter (·.vkDigest == toString vk.digest.val) do
        let prevs ← IO.ofExcept (stepPrevsOf (A.shape.slots b) cache.wraps cache.steps p)
        let wrappers := cache.wraps.filter (·.step == some (cacheKey p))
        unless wrappers.size == 1 do
          throw (IO.userError s!"{name}/{b.val}: expected exactly one cached wrap for the step")
        let some q := wrappers[0]? | throw (IO.userError "missing wrap")
        unless q.vkDigest == toString A.assembled.wiring.backend.wrapKey.cvk.digest.val do
          throw (IO.userError "the cached wrap uses another application's key")
        covered.modify ((app, cacheKey p) :: (app, cacheKey q) :: ·)
        jobs := jobs.push do
          let ok ← verdict s!"{name}/{b.val} step" (← run.step b.val p prevs.toArray) p.publicInput
          let accepted ← verifyCached CS "vesta" S.stepSrs.σ memo p
          IO.println s!"  cached step verifier: {accepted}"
          return ok && accepted
        jobs := jobs.push do
          let ok ← verdict s!"{name}/{b.val} wrap"
            (← run.wrap b.val p q prevs.toArray) q.publicInput
          let accepted ← verifyCached CW "pallas" S.wrapSrs.σ memo q
          IO.println s!"  cached wrap verifier: {accepted}"
          return ok && accepted
    unless !jobs.isEmpty do throw (IO.userError s!"{name}: no cached executions")
    IO.println s!"{name}: {jobs.size} runs on {workers} workers"
    (← IO.getStdout).flush
    unless (← runPool workers jobs).all id do throw (IO.userError s!"{name}: a run failed")
    runApplications S caches workers memo covered rest (contexts ++ [⟨A.shape, context⟩])

def main : IO Unit := do
  let some dir ← IO.getEnv "PICKLES_DUMP_DIR"
    | throw (IO.userError "PICKLES_DUMP_DIR is not set")
  let links ← IO.getEnv "LINKS"
  let apps ← IO.ofExcept (Manifest.select links)
  Manifest.checkFiles dir apps
  let σW ← srsAt CW "pallas" pallasBase.sqrt? (← IO.mkRef []) WrapIPARounds
  let σS ← srsAt CS "vesta" vestaBase.sqrt? (← IO.mkRef []) StepIPARounds
  let some wrap := Srs.check σW | throw (IO.userError "invalid wrap SRS")
  let some step := Srs.check σS | throw (IO.userError "invalid step SRS")
  loadApplications dir apps wrap step fun imported => do
    compareApplications dir imported
    if links.isNone then return
    let cacheDir := (← IO.getEnv "PICKLES_PROOF_CACHE_DIR").getD
      "../packages/pickles/test/fixtures/proof-cache"
    let caches ← apps.mapM fun app => do
      let raw ← IO.FS.readFile (System.FilePath.mk cacheDir / s!"{app.name}.json")
      let (wraps, _) ← IO.ofExcept (Cache.parseFile CW fqSide.endo pallasBase.sqrt? raw)
      let (steps, _) ← IO.ofExcept (Cache.parseFile CS fpSide.endo vestaBase.sqrt? raw)
      return (⟨app.name, wraps, steps⟩ : ProofCache)
    let some (_, first) := imported.head? | throw (IO.userError "no reconstructed applications")
    let workers := ((← IO.getEnv "LINKS_JOBS").bind String.toNat?).getD 4
    unless workers > 0 do throw (IO.userError "LINKS_JOBS must be positive")
    runApplications first.setup caches workers (← Memo.new) (← IO.mkRef []) imported []
