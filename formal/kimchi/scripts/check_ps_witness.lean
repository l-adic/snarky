import Kimchi.Fixture.PS

/-! Check every witness-carrying PureScript harness result against the index model:
scan `circuits/results/*.json`, ingest each comparison's `purescript` side through
`Kimchi.Fixture.PS.build` (padding + domain synthesis, every law decided by
`Index.build?`), and decide `Satisfies` on the dumped witness — the checker is the
`Decidable` instance of the predicate itself. Corruptions of a constrained gate cell, a
wired cell, and a public input must each be rejected (targets derived from the index;
an absent target is reported and skipped). Fails if any check fails or the scan finds
no witnesses. -/

open Lean Kimchi.Index Kimchi.Fixture.PS CompElliptic.Fields.Pasta

def resultsDir : IO System.FilePath := do
  match (← IO.getEnv "KIMCHI_PS_RESULTS_DIR") with
  | some d => return d
  | none   => return ".." / "packages" / "pickles-circuit-diffs" / "circuits" / "results"

/-- The checks for one ingested instance, named for the report. `none` = no target. -/
def checks (inst : Instance) : List (String × Option Bool) :=
  haveI : NeZero inst.n := inst.nz
  let wit := inst.wit
  let sat (w : Fin inst.n → Fin 15 → Fp) (p : Fin inst.idx.publicCount → Fp) : Bool :=
    decide (Satisfies inst.idx p w)
  -- Corruption targets derived from the index: a constrained non-generic row (all
  -- modeled gates read column 0) and a nontrivially wired cell.
  let gateRow? : Option (Fin inst.n) := (List.finRange inst.n).find? fun i =>
    (inst.idx.gates i).typ != GateType.zero && (inst.idx.gates i).typ != GateType.generic
  let wired? : Option (Fin 7 × Fin inst.n) := (List.finRange inst.n).findSome? fun r =>
    ((List.finRange 7).find? fun col => inst.idx.wiringMap (col, r) != (col, r)).map
      fun col => (col, r)
  let bump (r : Fin inst.n) (c : ℕ) : Fin inst.n → Fin 15 → Fp :=
    fun i c' => if i = r ∧ (c' : ℕ) = c then wit.tab i c' + 1 else wit.tab i c'
  [ ("Satisfies (decided from the predicate)", some (sat wit.tab wit.pub)),
    ("corrupted gate cell rejected", gateRow?.map fun r => !sat (bump r 0) wit.pub),
    ("corrupted wired cell rejected",
      wired?.map fun (col, r) => !sat (bump r (col : ℕ)) wit.pub),
    ("corrupted public input rejected",
      if inst.idx.publicCount = 0 then none
      else some (!sat wit.tab (fun i => wit.pub i + 1))) ]

def main : IO Unit := do
  let resultsDir ← resultsDir
  let entries ← resultsDir.readDir
  let jsons := (entries.filterMap fun e =>
    if e.fileName.endsWith ".json" then some e.path else none).qsort
      (·.toString < ·.toString)
  let mut checked := 0
  let mut allOk := true
  for p in jsons do
    let raw ← IO.FS.readFile p
    match Json.parse raw >>= parseComparison? with
    | .error e => do
        allOk := false
        IO.println s!"✗ {p.fileName.getD p.toString}: parse error: {e}"
    | .ok none => pure ()
    | .ok (some fx) => do
        checked := checked + 1
        let name := p.fileName.getD p.toString
        match Kimchi.Fixture.PS.build fx with
        | .error e => do
            allOk := false
            IO.println s!"✗ {name}: {e}"
        | .ok inst => do
            let results := checks inst
            for (check, r) in results do
              match r with
              | some ok => IO.println s!"  {if ok then "✓" else "✗"} {name}: {check}"
              | none => IO.println s!"  - {name}: {check} (no target, skipped)"
            unless results.all (fun (_, r) => r != some false) do allOk := false
  IO.println s!"checked {checked} witness-carrying result(s)"
  unless checked > 0 do
    throw (IO.userError "no witnesses found — run the harness with \
      CIRCUIT_DIFFS_WITNESS_EXPORT=1 first")
  unless allOk do throw (IO.userError "PS witness check FAILED")

#eval main
