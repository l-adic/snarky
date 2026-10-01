/-
The capstones' constant premises, decided on the circuit-diffs dumps' constants: what the
handover theorems (`wrapStep_kimchiVerify`, `stepWrap_kimchiVerify`, `StepWrapRun.Hands`)
assume of the keys, the Lagrange tables and the rules beyond their types, checked on the
constants each main circuit's dump carries (`PicklesFixture.Constants`).

Per circuit: a wrap main's `h` is the step SRS's blinding base and its keys' index points and
its bases are finite (`wrapMainHyps`); a step main's `h` is the wrap SRS's, the dummy `sg` is
finite, and each slot's table fits its key's domain with finite bases and correction sum
(`stepMainHyps`), at no more slots than its tag's width. Across circuits: each wrap branch's
slot count is its rule's (`branchRules`), each slot is at the width of the wrap circuit whose
proofs it verifies (`slotTags`) and reads its source rules' statement size (`stepRuleSizes`),
and the wrap mains share one padding.

Every main dump must be present: the cross-circuit checks need all of them. The dumps are the
PS suite's gitignored export (`npx spago test -p pickles-circuit-diffs`); CI runs this check
against the exports its own commit just produced, beside the dump comparison.

Run from `formal/`:  lake exe check-premises
(`KIMCHI_PS_RESULTS_DIR` overrides the default export location, `BULLETPROOF_FIXTURES_DIR`
the blinding bases' fixtures).
-/
import PicklesFixture.Premises
import PicklesFixture.Rules

open Lean Snarky Snarky.Kimchi Kimchi CompElliptic.Fields.Pasta
open PicklesFixture

/-- A step main's dump name, slot count, and slots' widths at the tag's width `w`. -/
def stepMainShape {n : ℕ} (name : String) (w : ℕ) (k : StepMainConsts n) :
    String × ℕ × List ℕ :=
  (name, n, k.slots.toList.map fun s => s.source.width w)

/-- Which rule each wrap main's branch is compiled from, by dump name: the sources whose statement
size a slot verifying that wrap main reads (`stepRuleSizes`). Each branch's slot count is checked
to be its rule's, which checks the table. -/
def branchRules : List (String × ℕ × String) :=
  [ ("wrap_main_n2_circuit", 0, "step_main_simple_chain_n2_circuit"),
    ("wrap_main_tree_proof_return_circuit", 0, "step_main_tree_proof_return_circuit"),
    ("wrap_main_two_phase_chain_circuit", 0, "step_main_two_phase_chain_make_zero_circuit"),
    ("wrap_main_two_phase_chain_circuit", 1, "step_main_two_phase_chain_increment_circuit") ]

/-- Which wrap main's proofs each step main's slot verifies, by dump name, where both are
dumped. The handover theorems need the slot at that wrap circuit's width (`wrapStep_kimchiVerify`'s
`hwi`, `StepWrapRun.Hands`). Two slots are not listed: the import's self slot, whose width the
constants parser (`stepMainOf`) pins to its own tag's, and tree-proof-return's slot 0, which
verifies `No_recursion_return`, whose wrap main is not dumped. -/
def slotTags : List (String × ℕ × String) :=
  [ ("step_main_simple_chain_n2_circuit", 0, "wrap_main_n2_circuit"),
    ("step_main_simple_chain_n2_circuit", 1, "wrap_main_n2_circuit"),
    ("step_main_tree_proof_return_circuit", 1, "wrap_main_tree_proof_return_circuit"),
    ("step_main_two_phase_chain_increment_circuit", 0, "wrap_main_two_phase_chain_circuit"),
    ("step_main_import_two_phase_chain_circuit", 0, "wrap_main_two_phase_chain_circuit") ]

open Pickles in
/-- A rule's statement sizes, from its type: each slot's previous statement's cell count, and the
cell count of the application state it emits, its input's and its output's. -/
def ruleSizes {n : ℕ} (inVal outVal : Type) {inVar outVar : Type} [CircuitType Fp inVal inVar]
    [CircuitType Fp outVal outVar] {ss : Fin n → ℕ}
    (_ : inVar → CircuitM Fp C (((i : Fin n) → PrevStatement (ss i)) × outVar)) : List ℕ × ℕ :=
  ((List.finRange n).map ss, CircuitType.size Fp inVal + CircuitType.size Fp outVal)

/-- The transcribed rules' statement sizes, by their step main's dump name. The handover theorems'
`Hands` has a slot read a previous statement of its source rule's application-state size. -/
def stepRuleSizes : List (String × List ℕ × ℕ) :=
  [ ("step_main_simple_chain_n2_circuit", ruleSizes Fp Unit simpleChainN2Rule),
    ("step_main_two_phase_chain_make_zero_circuit", ruleSizes Fp Unit makeZeroRule),
    ("step_main_two_phase_chain_increment_circuit", ruleSizes Fp Unit incrementRule),
    ("step_main_tree_proof_return_circuit", ruleSizes Unit Fp fun _ => treeProofReturnRule),
    ("step_main_import_two_phase_chain_circuit",
      ruleSizes Unit Fp fun _ => importTwoPhaseChainRule) ]

def main : IO Unit := do
  let dir ← resultsDir
  let fdir := (← IO.getEnv "BULLETPROOF_FIXTURES_DIR").getD "bulletproof-pcs/fixtures"
  let hStepPt ← blindingBase Bulletproof.IpaPallas.curve s!"{fdir}/ipa_batch_pallas.json"
  let hWrapPt ← blindingBase Bulletproof.IpaVesta.curve s!"{fdir}/ipa_batch_vesta.json"
  let wrapMains ← wrapMainDumps.mapM fun (name, bp, mpv, nc) => do
    let k ← readConstants (dir / s!"{name}.json") (wrapMainOf nc)
    let m := CircuitType.size Fp (Pickles.StepStatement (Pickles.UnfVal 15) Fp mpv)
    let some tables := wrapMainTables? bp nc m k.lagrange
      | throw (IO.userError (s!"{name}: Lagrange bases are not {m} rows of {bp + 1}: " ++
          s!"{k.lagrange.size} rows of lengths {(k.lagrange.toList.map List.length).eraseDups}"))
    if let .error e := wrapMainHyps k tables hWrapPt then throw (IO.userError s!"{name}: {e}")
    pure (name, k.stepWidths, k.dummy)
  IO.println s!"✓ the wrap mains' keys and tables ({wrapMains.length} circuits)"
  let stepShapes ← stepMainDumps.mapM fun (name, n, w) => do
    let k ← readConstants (dir / s!"{name}.json") (stepMainOf n w)
    if let .error e := stepMainHyps k hStepPt then throw (IO.userError s!"{name}: {e}")
    unless n ≤ w do throw (IO.userError s!"{name}: {n} slots exceed the tag's width {w}")
    pure (stepMainShape name w k)
  IO.println s!"✓ the step mains' slots and tables ({stepShapes.length} circuits)"
  let mut branches := 0
  for (wname, b, sname) in branchRules do
    let some (_, widths, _) := wrapMains.find? (·.1 == wname)
      | throw (IO.userError s!"{wname} is not a wrap main dump")
    let some (_, n, _) := stepShapes.find? (·.1 == sname)
      | throw (IO.userError s!"{sname} is not a step main dump")
    let some w := widths[b]? | throw (IO.userError s!"{wname} has no branch {b}")
    unless w == n do
      throw (IO.userError s!"{wname}: branch {b} has {w} slots, its rule {sname} has {n}")
    branches := branches + 1
  IO.println s!"✓ branch slot counts are their rules' ({branches} branches)"
  let mut slots := 0
  for (sname, i, wname) in slotTags do
    let some (_, _, ws) := stepShapes.find? (·.1 == sname)
      | throw (IO.userError s!"{sname} is not a step main dump")
    let some (_, _, mpv, _) := wrapMainDumps.find? (·.1 == wname)
      | throw (IO.userError s!"{wname} is not a wrap main dump")
    let some wi := ws[i]? | throw (IO.userError s!"{sname} has no slot {i}")
    unless wi == mpv do
      throw (IO.userError s!"{sname}: slot {i} has width {wi}, {wname} verifies {mpv}")
    slots := slots + 1
  IO.println s!"✓ slots are at their wrap circuits' widths ({slots} slots)"
  let mut reads := 0
  for (sname, i, wname) in slotTags do
    let some (_, ss, _) := stepRuleSizes.find? (·.1 == sname)
      | throw (IO.userError s!"{sname} has no transcribed rule")
    let some si := ss[i]? | throw (IO.userError s!"{sname} has no slot {i}")
    for (wname', _, rname) in branchRules do
      unless wname' == wname do continue
      let some (_, _, sa) := stepRuleSizes.find? (·.1 == rname)
        | throw (IO.userError s!"{rname} has no transcribed rule")
      unless si == sa do
        throw (IO.userError
          s!"{sname}: slot {i} reads {si} statement cells, {rname} emits {sa}")
      reads := reads + 1
  IO.println s!"✓ slots read their sources' statement sizes ({reads} slot-branch pairs)"
  let dummies := wrapMains.map (·.2.2)
  unless dummies.all fun d => decide (some d = dummies.head?) do
    throw (IO.userError "the wrap mains' padding challenges differ")
  IO.println s!"✓ the wrap mains share one padding ({dummies.length} circuits)"
