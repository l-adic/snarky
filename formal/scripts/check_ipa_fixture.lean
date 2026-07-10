import Kimchi.Fixture.Ipa

/-! End-to-end IPA compatibility over the unified chunked schema, both production
chunk-fold mechanisms:

* combine-then-open (`ipa_{opening,batch,chunked2,chunked3}_{vesta,pallas}.json`): the
  chunk layer's recombination formulas must reproduce the production combination — the
  `y = x^(2^k)`-power MSM of the chunk points against the production `chunk_commitment`,
  the `y`-power fold of the chunk evaluations against the combined value (both
  identities at one chunk) — and the executable verifier must accept the combined claim
  and reject a corrupted one.
* chunked batch (`ipa_chunked_{batch,ragged}_{vesta,pallas}.json` — uniform 2/2 and
  ragged 1/3 chunk counts, the latter exercising the prefix-sum segment offsets): the
  chunked-batch combiners must reproduce the production segment-stream combination
  (`combine_commitments` at `rand_base = 1`, `combined_inner_product`), and the
  executable verifier must accept the FLATTENED segment view — the flattening lemmas,
  adjudicated end-to-end — and reject a corrupted one. -/

open Lean Kimchi.Fixture.Ipa Kimchi.Verifier

def checkFixture (C : Ipa.CommitmentCurve) (curveName : String) (path : String) :
    IO Bool := do
  let raw ← IO.FS.readFile path
  let (σ, fx) ← match Json.parse raw >>= fun j => do
      return (← parseSRS C j, ← parseRaw C curveName j) with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"{path}: fixture parse error: {e}")
  let nc := (fx.chunkComms.getD 0 #[]).size
  -- recombination against production, per polynomial (per point for the evals)
  let y := fx.xs.getD 0 0 ^ (2 ^ σ.k)
  let hComm := decide (∀ i < fx.chunkComms.size,
    recombinePoint C y (fx.chunkComms.getD i #[]) = fx.combinedComms.getD i 0)
  let hEval := decide (∀ i < fx.chunkEvals.size, ∀ j < fx.xs.size,
    recombineScalar C (fx.xs.getD j 0 ^ (2 ^ σ.k))
        ((fx.chunkEvals.getD i #[]).getD j #[])
      = (fx.evals.getD i #[]).getD j 0)
  let inp := fx.toInput
  let ok := Ipa.verify C σ inp
  let bad := { inp with evals := inp.evals.modify 0 (·.modify 0 (· + 1)) }
  let rejected := !Ipa.verify C σ bad
  IO.println s!"{path}: {fx.chunkComms.size} poly(s) × {fx.xs.size} point(s) × \
    {nc} chunk(s) — recombine comm: {if hComm then "✓" else "✗"}, \
    recombine eval: {if hEval then "✓" else "✗"}, \
    verify: {if ok then "ACCEPT" else "REJECT"}, \
    corrupted: {if rejected then "REJECT (expected)" else "ACCEPT (BUG)"}"
  return hComm && hEval && ok && rejected

def checkBatchFixture (C : Ipa.CommitmentCurve) (curveName : String) (path : String) :
    IO Bool := do
  let raw ← IO.FS.readFile path
  let (σ, fx) ← match Json.parse raw >>= fun j => do
      return (← parseSRS C j, ← parseRawBatch C curveName j) with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"{path}: fixture parse error: {e}")
  -- the chunked-batch combiners against the production segment-stream combination
  let hComm := decide (segmentCombinePoint C fx.polyscale fx.chunkComms
    = fx.batchCombined)
  let hCip := decide (segmentCombineScalar C fx.polyscale fx.evalscale fx.chunkEvals
    = fx.cip)
  -- the flattened segment view through the nc = 1 verifier: the flattening lemmas,
  -- adjudicated end-to-end against the production opening
  let inp := fx.toFlatInput
  let ok := Ipa.verify C σ inp
  let bad := { inp with evals := inp.evals.modify 0 (·.modify 0 (· + 1)) }
  let rejected := !Ipa.verify C σ bad
  IO.println s!"{path}: {fx.chunkComms.size} poly(s) × {fx.xs.size} point(s), \
    chunks {fx.chunkComms.map (·.size)}, batched — \
    segment comm: {if hComm then "✓" else "✗"}, \
    segment cip: {if hCip then "✓" else "✗"}, \
    flat verify: {if ok then "ACCEPT" else "REJECT"}, \
    corrupted: {if rejected then "REJECT (expected)" else "ACCEPT (BUG)"}"
  return hComm && hCip && ok && rejected

def main : IO Unit := do
  let mut allOk := true
  for name in ["opening", "batch", "chunked2", "chunked3"] do
    allOk := allOk
      && (← checkFixture IpaVesta.curve "vesta" s!"fixtures/ipa_{name}_vesta.json")
    allOk := allOk
      && (← checkFixture IpaPallas.curve "pallas" s!"fixtures/ipa_{name}_pallas.json")
  for name in ["chunked_batch", "chunked_ragged"] do
    allOk := allOk && (← checkBatchFixture IpaVesta.curve "vesta"
      s!"fixtures/ipa_{name}_vesta.json")
    allOk := allOk && (← checkBatchFixture IpaPallas.curve "pallas"
      s!"fixtures/ipa_{name}_pallas.json")
  unless allOk do throw (IO.userError "IPA fixture check FAILED")
  IO.println "✓ recombination and the segment stream match production and the \
    verifier accepts, both mechanisms, both curves"

#eval main
