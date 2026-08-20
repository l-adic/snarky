/-
Dead-code gate for the workspace.

Lean has no export-list mechanism, so the packages' `roots.txt` manifests *define* the public
API surface. This script treats their union as the root set: it imports the libraries, walks
the constant-dependency graph (each declaration's type + value), and FAILS (nonzero exit) if
any authored declaration — kimchi, pasta, poseidon, bulletproof-pcs, and the fixture libs —
is not reachable from the roots. Auto-generated decls (recursors, constructors, projections,
derive/`match_` auxiliaries, syntax parser descriptors) are excluded: they are noise, not
authored code.

Script surface: a root inside a `-- script-surface:begin` / `-- script-surface:end` block in
a manifest declares a declaration consumed by the `scripts/` drivers rather than the library.
The gate additionally checks each such name textually appears in some scripts/ file, so the
blocks cannot rot into general exemption dumps. A trailing `-- synthesis: ...` comment
exempts a line from the textual check (instances are found by class resolution, not by name).

All five packages are audited. `snarky/roots.txt` declares the DSL's port surface (the
PS-export mirrors, the Lean-only laws, and the `Example` exhibits), so `Snarky.*`
declarations sit under the same dead-zero contract as the rest of the tree; its internal
machinery must stay reachable from that declared surface.

The SIZE of that deferral, measured (temporarily widening `isAudited` to all of `isOurs`, then
restoring): **76 authored `Snarky.*` declarations, of which 43 are unreachable from the
manifest's 8 roots and 33 are credited.** So the headline "dead 0 of 1558" is dead-0 over 1558
of 1634 authored declarations, and the unaudited remainder is 43, not 3 and not 300. Those 43
are overwhelmingly plain DSL surface — `assertEq`, `mul`, `witness`, `existsVars`,
`addConstraint`, `fresh`, `readVar`, `mapVec`, the `CircuitM` monad instances, the
`CheckedType`/`CircuitType` classes, the `Example` demo circuit — which is why closing the
deferral is a design decision (which combinators are API of the port) rather than a deletion
pass, and why rooting them liberally would make the gate vacuous for this package.

Run from `formal/` (the aggregator workspace):  scripts/deadcode.sh
-/
import Kimchi
import Poseidon
import Snarky
import Snarky.Kimchi.Backend.Compile
import Snarky.Kimchi.Circuit.AddComplete
import Snarky.Kimchi.Circuit.Poseidon
import Snarky.Kimchi.Circuit.RangeCheck
import Snarky.Kimchi.Circuit.Sponge
import Snarky.Kimchi.Circuit.RandomOracle
import Snarky.Kimchi.Circuit.Utils
import Snarky.Kimchi.Circuit.EndoScalar
import Snarky.Kimchi.Circuit.EndoMul
import Snarky.Kimchi.Circuit.VarBaseMul
import Snarky.Kimchi.Circuit.GroupMap
import Snarky.Kimchi.Semantics
-- The fixture-decoding libraries are not part of any package's main library, so import them
-- explicitly: their declarations are authored code, and some are declared roots.
import KimchiFixture.Kimchi
import KimchiFixture.PS
import BulletproofFixture
import FixtureKit.Parse
import FixtureKit.Trace

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

/-- Name components that only compiler-generated auxiliaries carry. -/
def generatedComponents : List String :=
  [ "rec", "recOn", "casesOn", "brecOn", "below", "ibelow", "binductionOn",
    "noConfusion", "noConfusionType", "toCtorIdx", "ctorIdx", "ofNat", "sizeOf",
    "sizeOf_spec", "injEq", "inj", "eq_def", "congr_simp", "mk",
    "ctorElim", "ctorElimType", "proxyType", "proxyTypeEquiv", "ext", "ext_iff" ]

/-- Is `n` an auto-generated / internal name (or the analyzer's own code) rather than an
    authored library declaration? Env lookups use the (possibly `_private.`-mangled) name;
    name-shape checks use the demangled one — otherwise every `private` declaration reads
    as auxiliary through its `_private` component and escapes the audit. -/
def isAuxiliary (env : Environment) (n : Name) : Bool :=
  let u := (privateToUserName? n).getD n
  if n.hasMacroScopes then true
  else if (`Kimchi.DeadCode).isPrefixOf u then true            -- this analyzer's own decls
  else if (env.getProjectionFnInfo? n).isSome then true        -- structure field projections
  else match env.find? n with
    | some (.ctorInfo _) => true                               -- constructors
    | some (.recInfo _)  => true                               -- recursors
    | some ci =>
      -- syntax parser descriptors: used at parse time, invisible to any constant walk
      if ci.type.isConstOf ``Lean.ParserDescr
          || ci.type.isConstOf ``Lean.TrailingParserDescr then true
      -- per-constructor auxiliaries (`Foo.someCtor.elim` and friends)
      else if (env.find? n.getPrefix).any (fun p => p matches .ctorInfo _) then true
      else
        let comps := u.components.map (·.toString)
        -- any component that only generated code carries, anywhere in the name
        comps.any (fun c => generatedComponents.contains c || c.startsWith "_"
          || c.startsWith "match_" || c.startsWith "proof_")
        -- children of instances (derive-generated `.repr` / `.decEq` / `.default` …)
          || comps.dropLast.any (fun c => c.startsWith "inst")
          || (match n with
              | .str _ s =>
                  s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "eq_"
              | _ => false)
    | none => false

/-- Is `n` traversable — authored in this repo's packages? `private` declarations get a
    mangled `_private.<module>.0.`-prefixed name, so demangle first — otherwise the walk
    refuses to enter them and everything referenced only *through* a private helper reports
    dead. -/
def isOurs (n : Name) : Bool :=
  let n := (privateToUserName? n).getD n
  (`Kimchi).isPrefixOf n || (`Pasta).isPrefixOf n || (`Poseidon).isPrefixOf n
    || (`FixtureKit).isPrefixOf n || (`Bulletproof).isPrefixOf n || (`Snarky).isPrefixOf n

/-- Is `n` under the dead-zero contract? Everything traversable — all five packages
    declare their surface. -/
def isAudited (n : Name) : Bool :=
  isOurs n

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
  let manifests := ["kimchi/roots.txt", "pasta/roots.txt", "poseidon/roots.txt",
    "bulletproof-pcs/roots.txt", "snarky/roots.txt"]
  -- parse the manifests: one fully-qualified name per line, optional trailing `-- comment`;
  -- `--` lines and blanks are ignored; `script-surface` markers delimit the script surface
  let mut roots : Array Name := #[]
  let mut missing : Array Name := #[]
  let mut surface : Array (Name × Bool) := #[]   -- (name, exempt-from-textual-check)
  for m in manifests do
    let mut inSurface := false
    for line in (← IO.FS.readFile m).splitOn "\n" do
      let t := line.trim
      if t = "-- script-surface:begin" then inSurface := true
      else if t = "-- script-surface:end" then inSurface := false
      else if t.isEmpty || t.startsWith "--" then continue
      else
        let (nameStr, note) := match t.splitOn " -- " with
          | n :: rest => (n.trim, String.intercalate " -- " rest)
          | [] => (t, "")
        let n := nameStr.toName
        if env.contains n then roots := roots.push n else missing := missing.push n
        if inSurface then surface := surface.push (n, note.startsWith "synthesis")
  -- the script corpus: every file under the packages' scripts/ dirs (this analyzer excluded)
  let scriptDirs := ["scripts", "pasta/scripts", "poseidon/scripts",
    "bulletproof-pcs/scripts", "kimchi/scripts", "snarky/scripts"]
  let mut corpus := ""
  for d in scriptDirs do
    for e in (← System.FilePath.readDir d) do
      if (← e.path.isDir) then continue
      if e.fileName = "deadcode.lean" then continue
      corpus := corpus ++ (← IO.FS.readFile e.path)
  let mut unanchored : Array Name := #[]
  for (n, exempt) in surface do
    if !exempt && (corpus.splitOn n.getString!).length ≤ 1 then
      unanchored := unanchored.push n
  let live := Kimchi.DeadCode.reachable env roots
  -- all authored declarations under the dead-zero contract
  let authored : Array Name :=
    (env.constants.fold (init := #[]) fun acc n _ =>
      if Kimchi.DeadCode.isAudited n && !Kimchi.DeadCode.isAuxiliary env n then acc.push n
      else acc)
    |>.qsort (·.toString < ·.toString)
  let dead := authored.filter fun n => !live.contains n
  IO.println s!"roots: {roots.size} resolved, {missing.size} missing"
  for n in missing do IO.println s!"  ⚠ root not in env: {n}"
  for n in unanchored do
    IO.println s!"  ⚠ script-surface root not found in any scripts/ file: {n}"
  IO.println s!"authored decls (audited packages): {authored.size}   \
live: {authored.size - dead.size}   dead: {dead.size}"
  if dead.isEmpty then IO.println "── no dead code ──"
  else
    IO.println "── dead (authored, unreachable from roots) ──"
    for n in dead do IO.println s!"  {n}"
  unless missing.isEmpty && unanchored.isEmpty && dead.isEmpty do
    throwError "dead-code gate FAILED: {dead.size} dead, {missing.size} missing roots, \
{unanchored.size} unanchored script-surface roots"
