/-
Dead-code / reachability report for the Kimchi library.

Lean has no export-list mechanism, so `roots.txt` is the manifest that *defines* the public API
surface. This script treats it as the root set: it imports `Kimchi`, walks the constant-dependency
graph (each declaration's type + value), and lists every authored declaration — kimchi and
the extracted pasta/poseidon/bulletproof-pcs packages — NOT
reachable from the roots. Auto-generated decls (recursors, constructors, projections, and
`match_`/`proof_`/`eq_` auxiliaries) are excluded — they are noise, not authored code.

Run from `formal/`:  lake env lean scripts/deadcode.lean   (or: scripts/deadcode.sh)
-/
import Kimchi

open Lean

set_option linter.deprecated false

namespace Kimchi.DeadCode

/-- A declaration's defining body, if any. NOTE: `ConstantInfo.value?` returns `none` for
    theorems (it guards against accidental proof dependence), so we pattern-match the proof out
    directly — otherwise the walk sees only *type* dependencies and massively under-reports. -/
def declValue? : ConstantInfo → Option Expr
  | .defnInfo v   => some v.value
  | .thmInfo v    => some v.value
  | .opaqueInfo v => some v.value
  | _             => none

/-- Constants directly referenced by `n`: those appearing in its type and, if any, its body. -/
def directDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    match declValue? ci with
    | some v => ci.type.getUsedConstants ++ v.getUsedConstants
    | none   => ci.type.getUsedConstants

/-- Is `n` an auto-generated / internal name (or the analyzer's own code) rather than an
    authored library declaration? -/
def isAuxiliary (env : Environment) (n : Name) : Bool :=
  if n.hasMacroScopes then true
  else if (`Kimchi.DeadCode).isPrefixOf n then true            -- this analyzer's own decls
  else if (env.getProjectionFnInfo? n).isSome then true        -- structure field projections
  else match env.find? n with
    | some (.ctorInfo _) => true                               -- constructors
    | some (.recInfo _)  => true                               -- recursors
    | _ => match n with
      | .str _ s =>
          [ "rec", "recOn", "casesOn", "brecOn", "below", "ibelow", "binductionOn",
            "noConfusion", "noConfusionType", "toCtorIdx", "ctorIdx", "ofNat", "sizeOf",
            "sizeOf_spec", "injEq", "inj", "eq_def", "congr_simp", "mk" ].contains s
          || s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "eq_"
          || s.startsWith "_"
      | _ => false

/-- Is `n` one of ours — authored in this repo's packages (kimchi + the extracted
    pasta / poseidon / bulletproof-pcs packages)? -/
def isOurs (n : Name) : Bool :=
  (`Kimchi).isPrefixOf n || (`Pasta).isPrefixOf n || (`Poseidon).isPrefixOf n
    || (`FixtureKit).isPrefixOf n || (`Bulletproof).isPrefixOf n

/-- Transitive closure of the dependency graph from `roots`, restricted to our packages'
    edges (Mathlib/CompElliptic never reference our code, so nothing of ours is reachable
    that way). -/
partial def reachable (env : Environment) (roots : Array Name) : NameSet :=
  let rec go (seen : NameSet) : List Name → NameSet
    | [] => seen
    | n :: rest =>
      let fresh := (directDeps env n).filter fun d =>
        isOurs d && !seen.contains d
      go (fresh.foldl (·.insert ·) seen) (fresh.toList ++ rest)
  go (roots.foldl (·.insert ·) ∅) roots.toList

end Kimchi.DeadCode

run_cmd do
  let env ← getEnv
  let manifests := ["roots.txt", "pasta/roots.txt", "poseidon/roots.txt",
    "bulletproof-pcs/roots.txt"]
  let mut raw := ""
  for m in manifests do
    raw := raw ++ (← IO.FS.readFile m) ++ "\n"
  -- parse roots.txt: one fully-qualified name per line; skip blanks and `--` comments
  let mut roots : Array Name := #[]
  let mut missing : Array Name := #[]
  for line in raw.splitOn "\n" do
    let t := line.trim
    if t.isEmpty || t.startsWith "--" then continue
    let n := t.toName
    if env.contains n then roots := roots.push n else missing := missing.push n
  let live := Kimchi.DeadCode.reachable env roots
  -- all authored Kimchi.* declarations
  let authored : Array Name :=
    (env.constants.fold (init := #[]) fun acc n _ =>
      if Kimchi.DeadCode.isOurs n && !Kimchi.DeadCode.isAuxiliary env n then acc.push n
      else acc)
    |>.qsort (·.toString < ·.toString)
  let dead := authored.filter fun n => !live.contains n
  IO.println s!"roots: {roots.size} resolved, {missing.size} missing"
  for n in missing do IO.println s!"  ⚠ root not in env: {n}"
  IO.println s!"authored decls (all packages): {authored.size}   \
live: {authored.size - dead.size}   dead: {dead.size}"
  IO.println "── dead (authored, unreachable from roots) ──"
  if dead.isEmpty then IO.println "  (none)"
  for n in dead do IO.println s!"  {n}"
