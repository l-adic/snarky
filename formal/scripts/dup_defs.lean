import Pickles

/-!
# Which definitions say the same thing without saying so?

The signature of a restatement is two `def … : Prop` that unfold to the same formula while
neither mentions the other, so nothing connects their consumers. Arity and argument order
differ between such a pair, so a same-arity `isDefEq` sweep misses it.

The test here is a fingerprint: delta-unfold a definition's body through the package's own
`Prop`-valued definitions, then take the set of constants that survive — the wire functions
and connectives the statement is ultimately about. Two definitions with the same fingerprint
are candidates for one statement said twice. The pair is reported only when neither body
mentions the other, since a delegation is the fix, not the defect. Structure projections are
skipped: a structure's `Prop`-valued fields all unfold to projections of the same structure.

`DUP_PREFIX` (default `Pickles`) selects the namespace.

Run from `formal/`: `lake env lean scripts/dup_defs.lean`.
-/

open Lean Lean.Meta

namespace DupDefs

def isAuxiliary (n : Name) : Bool :=
  n.hasMacroScopes ||
    ((privateToUserName? n).getD n).components.any fun c =>
      let s := c.toString
      s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "inst"

/-- A `def`, not a structure projection, whose result type, after its binders, is `Prop`. -/
def propDef? (env : Environment) (n : Name) : Option DefinitionVal :=
  if env.isProjectionFn n then none else
  match env.find? n with
  | some (.defnInfo v) =>
    let rec peel : Expr → Bool
      | .forallE _ _ b _ => peel b
      | e => e.isProp
    if peel v.type then some v else none
  | _ => none

/-- The constants of a body, with the package's own `Prop` definitions replaced by their
own constants, transitively: what the statement is ultimately about. -/
partial def fingerprint (env : Environment) (props : NameSet) (e : Expr) : NameSet :=
  let rec go (seen : NameSet) (acc : NameSet) : List Name → NameSet
    | [] => acc
    | n :: rest =>
      if seen.contains n then go seen acc rest
      else if props.contains n then
        match propDef? env n with
        | some v => go (seen.insert n) acc (v.value.getUsedConstants.toList ++ rest)
        | none => go (seen.insert n) (acc.insert n) rest
      else go (seen.insert n) (acc.insert n) rest
  go ∅ ∅ e.getUsedConstants.toList

/-- One formula stated twice, arguments swapped: the self-test's pair. -/
def SelfTest.leBoth (x y : ℕ) : Prop := x ≤ y ∧ y ≤ x

/-- `SelfTest.leBoth`, restated. -/
def SelfTest.leBoth' (y x : ℕ) : Prop := y ≤ x ∧ x ≤ y

end DupDefs

open DupDefs in
run_cmd do
  let env ← getEnv
  let pref := ((← IO.getEnv "DUP_PREFIX").getD "Pickles").toName
  let mut props : NameSet := ∅
  for (n, _) in env.constants.map₁.toList do
    if pref.isPrefixOf ((privateToUserName? n).getD n) && !isAuxiliary n
        && (propDef? env n).isSome then props := props.insert n
  let names := props.toList.toArray.qsort fun a b => a.toString < b.toString
  let mut fps : Array (Name × NameSet × NameSet) := #[]
  for n in names do
    let some v := propDef? env n | continue
    fps := fps.push (n, fingerprint env props v.value, v.value.getUsedConstants.foldl
      (fun s c => s.insert c) ∅)
  IO.println s!"{fps.size} Prop-valued definitions under {pref}"
  let mut hits := 0
  for i in [0 : fps.size] do
    for j in [i + 1 : fps.size] do
      let (a, fa, ba) := fps[i]!
      let (b, fb, bb) := fps[j]!
      unless fa.toList == fb.toList do continue
      if ba.contains b || bb.contains a then continue   -- a delegation, not a restatement
      hits := hits + 1
      IO.println s!"  RESTATEMENT?  {a}  ≡  {b}"
  IO.println s!"{hits} unconnected pair(s) with one fingerprint"
  -- self-test: a restatement with its arguments swapped shares a fingerprint
  let some a := propDef? env `DupDefs.SelfTest.leBoth | throwError "self-test: missing"
  let some b := propDef? env `DupDefs.SelfTest.leBoth' | throwError "self-test: missing"
  unless (fingerprint env ∅ a.value).toList == (fingerprint env ∅ b.value).toList do
    throwError "self-test failed: a swapped-argument restatement has a different fingerprint"
  IO.println "self-test: a swapped-argument restatement shares its fingerprint"
