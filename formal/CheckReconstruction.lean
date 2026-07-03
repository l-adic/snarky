import Kimchi.Json
import Kimchi.Circuits.VarBaseMulStep
import Kimchi.Circuits.EndoMulStep
import Kimchi.Circuits.EndoScalarStep
import Kimchi.Circuits.PoseidonStep

/-! # Validate the reconstructed step-circuits against real dumps

The `Circuits/*Step.lean` composition proofs are stated over hand-written reconstructions of the
dumped circuits (`vbmCircuit`/`emCircuit`/`esCircuit`) — their column layout and copy wiring were,
until now, only an *audit-level* correspondence to what snarky actually emits. This runnable closes
that gap empirically: it takes each committed multi-gate fixture, slices the witness down to its
gate chain, and confirms the reconstruction's executable `check` returns `true` on the real witness
(and `false` once a single cell is tampered). So the reconstruction's `ofRows` column reads and the
`copyHolds` threading it assumes are machine-verified against the real prover output.

Fixture layouts (from the committed dumps; see `formal/fixtures/`):

* `varbasemul_step`: rows 0–4 `Generic`, row 5 `CompleteAdd` (init `[2]T`), rows **6–107** the
  51 `VarBaseMul`/`Zero` pairs, row 108 `Generic` — matches `vbmCircuit 51` (102 rows).
* `endomul_step`: rows 0–5 `Generic`, rows 6–7 `CompleteAdd`, rows **8–39** the 32 `EndoMul` rows,
  row 40 `Zero` (the last gate's output row) — matches `emCircuit 32` (32 gates + output row).
* `endoscalar_step`: rows 0–2 `Generic`, rows **3–10** the 8 `EndoMulScalar` rows, row 11
  `Generic` — matches `esCircuit 7` (8 rows).

Run: `lake env lean --run CheckReconstruction.lean` (or `make lean-check-reconstruction`). Exits
non-zero if any reconstruction fails to accept the real chain or fails to reject the tamper. -/

open Kimchi.Json Kimchi.Circuit Kimchi.Field

/-- Slice witness rows `[lo, hi)` into a fresh 0-based witness (the gate chain; setup rows gone). -/
def sliceWitness (w : Witness Fp) (lo hi : Nat) : Witness Fp :=
  { rows := (Array.range (hi - lo)).map (fun i => w.row (lo + i)) }

/-- Perturb one cell `(r, c)` by `+1` — the negative control. -/
def tamperCell (w : Witness Fp) (r c : Nat) : Witness Fp :=
  { rows := (Array.range w.rows.size).map fun i =>
      if i = r then (w.row i).modify c (· + 1) else w.row i }

/-- Parse a fixture into the Lean model (circuit + row-major witness). -/
def loadDump (path : System.FilePath) : IO (Circuit Fp × Witness Fp) := do
  let s ← IO.FS.readFile path
  match Lean.Json.parse s >>= Lean.fromJson? (α := JCircuit) with
  | .error e => throw (IO.userError s!"failed to load {path}: {e}")
  | .ok jc => return (toCircuit jc, toWitness jc)

/-- A fixture's witness only (column-major → row-major). -/
def loadWitness (path : System.FilePath) : IO (Witness Fp) := do
  return (← loadDump path).2

/-- Slice `[lo, hi)` of a fixture's witness and confirm the reconstruction `recon` accepts the real
    chain and rejects a one-cell tamper (at row 0, col 0 — always a constrained base/register). -/
def checkRecon (name : String) (path : System.FilePath) (recon : Circuit Fp)
    (lo hi : Nat) : IO Bool := do
  let w ← loadWitness path
  let wS := sliceWitness w lo hi
  let accepts := check recon wS #[]
  let rejects := !check recon (tamperCell wS 0 0) #[]
  IO.println s!"{name}: accepts real chain = {accepts}, rejects tampered = {rejects}"
  pure (accepts && rejects)

open Kimchi.Circuit.VarBaseMul (vbmCircuit scaleCombineCircuit)
open Kimchi.Circuit.EndoMul (emCircuit)
open Kimchi.Circuit.EndoScalar (esCircuit)
open Kimchi.Circuit.Poseidon (posCircuit)

/-- Poseidon needs the reconstruction's per-row round constants, which come from the dumped gates
    (rows `lo …`). Confirm `posCircuit m` (with those constants) accepts the sliced chain. -/
def checkReconPoseidon (path : System.FilePath) (m lo hi : Nat) : IO Bool := do
  let (c, w) ← loadDump path
  let coeffs : Nat → Array Fp := fun i => (c.gateAt (lo + i)).coeffs
  let recon := posCircuit m coeffs
  let wS := sliceWitness w lo hi
  let accepts := check recon wS #[]
  let rejects := !check recon (tamperCell wS 0 0) #[]
  IO.println s!"poseidon   → posCircuit {m}: accepts real chain = {accepts}, \
    rejects tampered = {rejects}"
  pure (accepts && rejects)

def main : IO Unit := do
  let mut ok := true
  ok := ok && (← checkRecon "varbasemul → vbmCircuit 51" "fixtures/varbasemul_step.json"
    (vbmCircuit 51) 6 108)
  ok := ok && (← checkRecon "endomul    → emCircuit 32" "fixtures/endomul_step.json"
    (emCircuit 32) 8 41)
  ok := ok && (← checkRecon "endoscalar → esCircuit 7" "fixtures/endoscalar_step.json"
    (esCircuit 7) 3 11)
  ok := ok && (← checkReconPoseidon "fixtures/poseidon_step.json" 11 6 18)
  -- the verifier sub-circuit: chain rows 8..109 + the combine CompleteAdd at 110
  ok := ok && (← checkRecon "scale-combine → scaleCombineCircuit 51"
    "fixtures/scale_combine_step.json" (scaleCombineCircuit 51) 8 111)
  unless ok do
    IO.eprintln "reconstruction mismatch: a hand-written step-circuit disagrees with the dump"
    IO.Process.exit 1
