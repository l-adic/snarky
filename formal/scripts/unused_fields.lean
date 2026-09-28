import Pickles

/-!
# Which hypothesis fields does a proof actually use?

`FIELD_ROOTS` (comma-separated theorems, default: the capstones of `pickles/roots.txt`) and
`FIELD_STRUCTS` (comma-separated structure names, default: the tie records). For each
structure, reports which of its fields' projections never occur anywhere in the roots' proof
terms — a field no proof reads is a hypothesis the statement does not need.

Decided by the constant walk: `h.mask` elaborates to `Pickles.IvpHyps.mask h`, so a used field
leaves its projection constant in some proof term.

Run from `formal/`: `lake env lean scripts/unused_fields.lean`.
-/

open Lean

namespace UnusedFields

def declValue? : ConstantInfo → Option Expr
  | .defnInfo v => some v.value | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value | _ => none

def directDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci => match declValue? ci with
    | some v => ci.type.getUsedConstants ++ v.getUsedConstants
    | none => ci.type.getUsedConstants

def isOurs (n : Name) : Bool :=
  let n := (privateToUserName? n).getD n
  (`Kimchi).isPrefixOf n || (`Pasta).isPrefixOf n || (`Poseidon).isPrefixOf n
    || (`FixtureKit).isPrefixOf n || (`Bulletproof).isPrefixOf n || (`Snarky).isPrefixOf n
    || (`Schnorr).isPrefixOf n || (`Pickles).isPrefixOf n

partial def reachable (env : Environment) (roots : Array Name) : NameSet :=
  let rec go (seen : NameSet) : List Name → NameSet
    | [] => seen
    | n :: rest =>
      let fresh := (directDeps env n).filter fun d => isOurs d && !seen.contains d
      go (fresh.foldl (·.insert ·) seen) (fresh.toList ++ rest)
  go (roots.foldl (·.insert ·) ∅) roots.toList

def namesOf (s : String) (dflt : List Name) : List Name :=
  if s.trimAscii.isEmpty then dflt
  else (s.splitOn ",").filterMap fun t =>
    let t := t.trimAscii.toString
    if t.isEmpty then none else some t.toName

end UnusedFields

open UnusedFields in
run_cmd do
  let env ← getEnv
  let roots := namesOf ((← IO.getEnv "FIELD_ROOTS").getD "")
    [ `Pickles.stepProof_kimchiVerify_vesta, `Pickles.wrapProof_kimchiVerify_pallas,
      `Pickles.stepWrap_kimchiVerify, `Pickles.wrapStep_kimchiVerify ]
  let structs := namesOf ((← IO.getEnv "FIELD_STRUCTS").getD "")
    [ `Pickles.IvpHyps, `Pickles.IvpTies, `Pickles.FopTies ]
  for r in roots do unless env.contains r do throwError "root {r} missing"
  let live := reachable env roots.toArray
  for s in structs do
    let some info := getStructureInfo? env s | throwError "{s} is not a structure"
    let mut used : Array Name := #[]
    let mut unused : Array Name := #[]
    for f in info.fieldNames do
      let proj := s ++ f
      if live.contains proj then used := used.push f else unused := unused.push f
    -- a `casesOn`/`rec` destructuring reads every field at once, so per-field is undecidable
    let cased := live.contains (s ++ `casesOn) || live.contains (s ++ `rec)
    if cased then
      IO.println s!"\n## {s}: destructured wholesale (casesOn/rec reachable) — per-field \
        undecidable by this walk"
    else
      IO.println s!"\n## {s}: {used.size} of {info.fieldNames.size} fields used"
      for f in unused do IO.println s!"  UNUSED  {f}"
