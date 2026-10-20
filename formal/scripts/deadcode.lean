/-
Dead-code gate for the workspace.

Lean has no export-list mechanism, so the roots say what the tree is for. They come from three
sources:

* the CI drivers: every executable and `--run` script `.github/workflows/{lean,test}.yml`
  invokes (`ciDrivers`), read as module data from their compiled oleans rather than imported
  (each declares `main`). Whatever a driver references is alive. The drivers must be built
  first; lean.yml's compile step and scripts/deadcode.sh do that;
* the axiom gates' root lists, `snarky/scripts/check_axioms.lean` and
  `pickles/scripts/check_axioms.lean`: the results those packages stand behind although nothing
  executable consumes them (the completeness laws, the capstones, the decided regression
  endpoints), read as the files' unclosed backquoted name literals. The audited list is those
  packages' one manifest;
* the `roots.txt` manifests of kimchi, pasta, poseidon and bulletproof-pcs, as before. A root
  inside a `-- script-surface:begin` / `-- script-surface:end` block there declares a declaration
  consumed by the `scripts/` drivers, and must appear textually in some scripts/ file as a whole
  name; a trailing `-- synthesis: ...` comment exempts a line from that check.

Three rules root what a constant walk cannot see: `rfl` theorems (`simp` and `dsimp` rewrite with
them definitionally, from the simp set or a `simp only` list, and leave no constant in the proof
term), `Coe`-class instances (unfolded at elaboration) and registered elaborators and macros
(invoked by the elaborator, referenced by nothing). The walk itself follows a `partial def`'s
compiled body (`._unsafe_rec`) and an `implemented_by` target, which the kernel-facing value
omits.

Audited: kimchi, pasta, poseidon, bulletproof-pcs, snarky, pickles and the PicklesFixture
library. Auto-generated declarations (recursors, constructors, projections, derive/`match_`
auxiliaries, syntax parser descriptors) are excluded: they are noise, not authored code. The gate
FAILS (nonzero exit) on any unreachable authored declaration, a root missing from the
environment, an unbuilt driver, or an unanchored script-surface root.

Run from `formal/` (the aggregator workspace):  scripts/deadcode.sh
-/
import Kimchi
import Kimchi.Index.CompareChecks
import Kimchi.Index.InterpolationChecks
import Poseidon
import Snarky
import Snarky.Kimchi.Backend.Compile
import Snarky.Kimchi.Backend.Internal.Direct
import Snarky.Kimchi.Backend.Internal.Wiring
import Snarky.Kimchi.Backend.Checks.DirectChecks
import Snarky.Kimchi.Backend.Internal.Wired
import Snarky.Kimchi.Backend.Checks.WiredChecks
import Snarky.Kimchi.Backend.Checks.WiredFixtures
import Snarky.Kimchi.Backend.Checks.Table
import Snarky.Kimchi.Backend.Internal.UnionFind
import Snarky.Kimchi.Backend.Internal.Reduction
import Snarky.Kimchi.Backend.Admissibility
import Snarky.Kimchi.Backend.ScopedCheck
import Snarky.Kimchi.Backend.Checks.ScopedCheckChecks
import Snarky.Kimchi.Backend.IndexSpec
import Snarky.Kimchi.Backend.CompiledIndex
import Snarky.Kimchi.Backend.Checks.CompiledIndexChecks
import Snarky.Kimchi.Backend.CheckedCompile
import Snarky.Kimchi.Backend.Checks.CheckedCompileConsumer
import Snarky.Kimchi.Backend.Checks.CheckedCompileChecks
import Snarky.Kimchi.Backend.Internal.Trace
import Snarky.Kimchi.Backend.Checks.TraceChecks
import Snarky.Kimchi.Backend.Internal.TraceSemantics
import Snarky.Kimchi.Backend.Internal.RowCorrespondence
import Snarky.Kimchi.Backend.Internal.Receipts
import Snarky.Kimchi.Circuit.AddComplete
import Snarky.Kimchi.Circuit.Poseidon
import Snarky.Kimchi.Circuit.RangeCheck
import Snarky.Kimchi.Circuit.Sponge
import Snarky.Kimchi.Circuit.RandomOracle
import Snarky.Kimchi.Circuit.EndoScalar
import Snarky.Kimchi.Circuit.EndoMul
import Snarky.Kimchi.Circuit.VarBaseMul
import Snarky.Kimchi.Circuit.GroupMap
import Snarky.Kimchi.Semantics
import Snarky.Prover.WP
import Pickles
-- The fixture-decoding libraries are not part of any package's main library, so import them
-- explicitly: their declarations are authored code, and some are declared roots.
import KimchiFixture.Kimchi
import KimchiFixture.PS
import KimchiFixture.Cache
import BulletproofFixture
import BulletproofFixture.SRSLoader
import PicklesFixture
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
def usedBy (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    match declValue? ci with
    | some v => ci.type.getUsedConstants ++ v.getUsedConstants
    | none   => ci.type.getUsedConstants

/-- `usedBy`, plus the compiled body of a `partial def` (`n._unsafe_rec`) and an `implemented_by`
    target, both of which the kernel-facing value omits. -/
def directDeps (env : Environment) (n : Name) : Array Name :=
  let implBy := match Compiler.implementedByAttr.getParam? env n with
    | some t => #[t]
    | none => #[]
  usedBy env n ++ usedBy env (n ++ `_unsafe_rec) ++ implBy

/-- Name components that only compiler-generated auxiliaries carry. -/
def generatedComponents : List String :=
  [ "rec", "recOn", "casesOn", "brecOn", "below", "ibelow", "binductionOn",
    "noConfusion", "noConfusionType", "toCtorIdx", "ctorIdx", "ofNat", "ofNat_ctorIdx",
    "sizeOf",
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
        -- unescaped: a component with a bracket would otherwise print as `«_aux…»`
        let comps := u.components.map (·.toString (escape := false))
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
    || (`Pickles).isPrefixOf n || (`PicklesFixture).isPrefixOf n

/-- Is `n` under the dead-zero contract? Everything traversable — every package and the
    PicklesFixture library declare their surface. -/
def isAudited (n : Name) : Bool :=
  isOurs n

/-- Transitive closure of the dependency graph from `roots`, restricted to our packages'
    edges. Mathlib/CompElliptic never reference our code, so their edges need not be followed. -/
partial def reachable (env : Environment) (roots : Array Name) : NameSet :=
  let rec go (seen : NameSet) : List Name → NameSet
    | [] => seen
    | n :: rest =>
      let fresh := (directDeps env n).filter fun d => isOurs d && !seen.contains d
      go (fresh.foldl (·.insert ·) seen) (fresh.toList ++ rest)
  go (roots.foldl (·.insert ·) ∅) roots.toList

/-- Whether `id` occurs in `s` as a whole name component rather than inside a longer name, as
`sgOk` does inside `sgOkWith`. -/
def mentions (s id : String) : Bool :=
  let idChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'
  let parts := s.splitOn id
  (parts.zip parts.tail).any fun (a, b) =>
    (a.isEmpty || !idChar a.back) && (b.isEmpty || !idChar b.front)

/-- The CI drivers, by olean basename under `scripts/` on the search path: every executable and
`--run` script `.github/workflows/{lean,test}.yml` invokes. -/
def ciDrivers : List String :=
  [ "check_cs", "check_tags", "check_slot_chunks", "check_rule_replay",
    "check_application_inputs", "check_application_indices", "certify_application",
    "check_application_keys", "check_terminal", "check_application_layouts",
    "check_application_manifest", "check_sg_ok" ]

/-- The library declarations a driver references, from every constant its olean defines. -/
def frontier (sp : SearchPath) (driver : String) : IO (Array Name) := do
  let rel : System.FilePath := "scripts" / (driver ++ ".olean")
  let some root ← sp.findM? (fun r => (r / rel).pathExists)
    | throw (IO.userError s!"scripts/{driver}.olean is not built: build the CI drivers first \
(scripts/deadcode.sh does)")
  let (data, _) ← readModuleData (root / rel)
  let mut out : NameSet := {}
  for ci in data.constants do
    let deps := ci.type.getUsedConstants ++ ((declValue? ci).map (·.getUsedConstants)).getD #[]
    for d in deps do
      if isOurs d then out := out.insert d
  return out.toArray

/-- The backquoted name literals of a Lean source, `` `Foo.bar `` as in a `List Name`: unclosed,
and preceded (whitespace and line comments aside) by a list or expression delimiter. A
docstring's closed `` `Foo.bar` `` or prose like `` a `namespace Foo` block `` is not one.
Guillemets are dropped. -/
def nameLiterals (src : String) : Array String := Id.run do
  -- line comments carry no literals and would hide the delimiter before the next entry
  let src := String.intercalate "\n" (src.splitOn "\n" |>.map fun l =>
    match l.splitOn "--" with | first :: _ => first | [] => l)
  let cs := src.toList.toArray
  let idChar (c : Char) : Bool :=
    c.isAlphanum || c == '.' || c == '_' || c == '?' || c == '!' || c == '\'' || c == '«'
      || c == '»'
  let mut out := #[]
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '`' && (i == 0 || cs[i-1]! != '`') then
      let mut k := i
      while k > 0 && (cs[k-1]! == ' ' || cs[k-1]! == '\n') do k := k - 1
      let inContext := k == 0 || "[,(=".contains cs[k-1]!
      let mut j := i + 1
      while j < cs.size && idChar cs[j]! do j := j + 1
      if inContext && j > i + 1 && (j >= cs.size || cs[j]! != '`') then
        let s := String.mk (cs.extract (i + 1) j).toList
        out := out.push ((s.replace "«" "").replace "»" "")
      i := j
    else i := i + 1
  return out

end Kimchi.DeadCode

run_cmd do
  let env ← getEnv
  let mut roots : Array Name := #[]
  let mut missing : Array String := #[]
  -- the manifests: one fully-qualified name per line, optional trailing `-- comment`; `--` lines
  -- and blanks are ignored; `script-surface` markers delimit the script surface
  let manifests := ["kimchi/roots.txt", "pasta/roots.txt", "poseidon/roots.txt",
    "bulletproof-pcs/roots.txt"]
  let mut surface : Array (Name × Bool) := #[]   -- (name, exempt-from-textual-check)
  let mut manifestCount := 0
  for m in manifests do
    let mut inSurface := false
    for line in (← IO.FS.readFile m).splitOn "\n" do
      let t := line.trimAscii.toString
      if t = "-- script-surface:begin" then inSurface := true
      else if t = "-- script-surface:end" then inSurface := false
      else if t.isEmpty || t.startsWith "--" then continue
      else
        let (nameStr, note) := match t.splitOn " -- " with
          | n :: rest => (n.trimAscii.toString, String.intercalate " -- " rest)
          | [] => (t, "")
        let n := nameStr.toName
        if env.contains n then
          roots := roots.push n
          manifestCount := manifestCount + 1
        else missing := missing.push nameStr
        if inSurface then surface := surface.push (n, note.startsWith "synthesis")
  -- the axiom gates' lists: a literal naming a module or a namespace is not a root
  let mut auditCount := 0
  for f in ["snarky/scripts/check_axioms.lean", "pickles/scripts/check_axioms.lean"] do
    for s in Kimchi.DeadCode.nameLiterals (← IO.FS.readFile f) do
      let n := s.toName
      if env.contains n then
        roots := roots.push n
        auditCount := auditCount + 1
      else if env.header.moduleNames.contains n || env.isNamespace n then continue
      else missing := missing.push s!"{s} ({f})"
  -- the CI drivers' frontiers
  let sp ← searchPathRef.get
  let mut driverCount := 0
  for d in Kimchi.DeadCode.ciDrivers do
    let f ← Kimchi.DeadCode.frontier sp d
    roots := roots ++ f
    driverCount := driverCount + f.size
  -- the rules
  let audited : Array Name := env.constants.fold (init := #[]) fun acc n _ =>
    if Kimchi.DeadCode.isAudited n then acc.push n else acc
  let authored :=
    (audited.filter (!Kimchi.DeadCode.isAuxiliary env ·)).qsort (·.toString < ·.toString)
  let mut rflRoots : Array Name := #[]
  for n in audited do
    if ← Elab.Command.liftCoreM (Meta.isRflTheorem n) then rflRoots := rflRoots.push n
  let instances := Meta.instanceExtension.getState env
  let coeRoots := audited.filter fun n =>
    match env.find? n with
    | some ci =>
      instances.instanceNames.contains n &&
        (match ci.type.getForallBody.getAppFn.constName? with
         | some c => c.getRoot.toString.startsWith "Coe"
         | none => false)
    | none => false
  let fromTable {γ} (st : KeyedDeclsAttribute.ExtensionState γ) : Array Name :=
    st.table.toList.foldl (init := #[]) fun acc (_, es) => acc ++ (es.map (·.declName)).toArray
  let elabRoots := (fromTable (Elab.Tactic.tacticElabAttribute.ext.getState env)
    ++ fromTable (Elab.macroAttribute.ext.getState env)
    ++ fromTable (Elab.Term.termElabAttribute.ext.getState env)
    ++ fromTable (Elab.Command.commandElabAttribute.ext.getState env)).filter
      Kimchi.DeadCode.isAudited
  -- the script corpus: every file under the packages' scripts/ dirs (this analyzer excluded)
  let scriptDirs := ["scripts", "pasta/scripts", "poseidon/scripts",
    "bulletproof-pcs/scripts", "kimchi/scripts", "snarky/scripts",
    "pickles/scripts"]
  let mut corpus := ""
  for d in scriptDirs do
    for e in (← System.FilePath.readDir d) do
      if (← e.path.isDir) then continue
      if e.fileName = "deadcode.lean" then continue
      corpus := corpus ++ (← IO.FS.readFile e.path)
  let mut unanchored : Array Name := #[]
  for (n, exempt) in surface do
    if !exempt && !Kimchi.DeadCode.mentions corpus n.getString! then
      unanchored := unanchored.push n
  let liveBase := Kimchi.DeadCode.reachable env roots
  let onlyByRule (r : Array Name) :=
    (r.filter (!liveBase.contains ·)).filter (authored.contains ·)
  let live := Kimchi.DeadCode.reachable env (roots ++ rflRoots ++ coeRoots ++ elabRoots)
  let dead := authored.filter (!live.contains ·)
  IO.println s!"roots: {manifestCount} from manifests, {auditCount} from the axiom gates, \
{driverCount} from {Kimchi.DeadCode.ciDrivers.length} CI drivers, {missing.size} missing"
  IO.println s!"rules: {rflRoots.size} rfl theorems ({(onlyByRule rflRoots).size} authored kept \
alive by the rule alone), {coeRoots.size} coercion instances, {elabRoots.size} elaborators"
  for s in missing do IO.println s!"  ⚠ root not in env: {s}"
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
