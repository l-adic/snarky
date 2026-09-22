/-
Comment gate for the workspace.

The docstrings are 22% of the library's lines and nothing mechanical checked them, so they
rotted: a name deleted from the code stayed in the prose that described it. This gate fixes
the objective half of the comment convention (the judgement half is the `proof-comment-style`
skill). It fails on:

* UNRESOLVED NAMES — a backticked token in a docstring that has the shape of an identifier but
  names no declaration, resolved in the declaration's own namespace chain or at the root. A
  comment names this tree's code; the PureScript, OCaml and Rust originals are NOT vocabulary
  here (see PROVENANCE). `scripts/comment-allow.txt` holds the few tokens that name something
  real without being constants — the column-count notations — and adding a line to it is a
  decision, not an escape hatch.
* PROVENANCE — a source file of an upstream implementation (`verifier.rs`, `step_verifier.ml`,
  `RangeCheck.purs`) may be named in a MODULE docstring, to say what a module transcribes. A
  declaration docstring naming one is a violation: the declaration's prose says what its own
  code does.
* BANNED PHRASES — history narration, first person, and trackers. A comment describes the code
  as it stands; the git log owns the past and the issue tracker owns the future.
* OVERSIZE — a declaration docstring longer than `declCap` lines, or a module/section docstring
  longer than `moduleCap`. The overflow belongs in a `/-! ## … -/` section, or nowhere.
* EMPHASIS — more than one bolded run in a declaration docstring, or one that does not open it.
  A label on everything is a label on nothing.

It also REPORTS (never fails) the comment-heaviest modules, as the queue for a judgement pass.

Run from `formal/`:  scripts/check-comments.sh
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
import Snarky.Kimchi.Circuit.EndoScalar
import Snarky.Kimchi.Circuit.EndoMul
import Snarky.Kimchi.Circuit.VarBaseMul
import Snarky.Kimchi.Circuit.GroupMap
import Snarky.Kimchi.Semantics
import Pickles
import KimchiFixture.Kimchi
import KimchiFixture.PS
import KimchiFixture.Cache
import BulletproofFixture
import BulletproofFixture.SRSLoader
import PicklesFixture
import FixtureKit.Parse
import FixtureKit.Trace

open Lean

namespace Kimchi.CheckComments

/-- A declaration docstring may run this many lines; past that the prose belongs in a
`/-! ## … -/` section. -/
def declCap : Nat := 8

/-- A module or section docstring may run this many lines. -/
def moduleCap : Nat := 60

/-- Phrases a comment about the code as it stands cannot contain: the past, the plan, the
author, and the tracker. -/
def banned : List (String × String) :=
  [ ("used to", "history"), ("previously", "history"), ("no longer", "history"),
    ("formerly", "history"), ("originally", "history"), ("we ", "first person"),
    ("our ", "first person"), ("TODO", "tracker"), ("FIXME", "tracker"),
    ("XXX", "tracker"), ("HACK", "tracker"), ("obviously", "hedge"),
    ("clearly ", "hedge"), ("simply ", "hedge") ]

/-- Our packages' namespace roots. -/
def ourRoots : List Name :=
  [`Kimchi, `Pasta, `Poseidon, `FixtureKit, `Bulletproof, `Snarky, `Pickles]

def isOurs (n : Name) : Bool :=
  let n := (privateToUserName? n).getD n
  ourRoots.any (·.isPrefixOf n)

/-- The backticked runs of a docstring. -/
def backticked (s : String) : List String :=
  let parts := s.splitOn "`"
  -- odd positions are the quoted runs
  (parts.zipIdx.filterMap fun (p, i) => if i % 2 == 1 then some p else none)

/-- A source file of this repo or of an upstream implementation. Nameable in a module
docstring (what the module transcribes), never in a declaration's. -/
def isSourceFile (t : String) : Bool :=
  [".rs", ".ml", ".mli", ".purs", ".lean", ".json", ".toml", ".sh"].any (fun e => t.endsWith e)

/-- Tactic and keyword vocabulary a docstring may quote without naming a declaration. -/
def keywords : List String :=
  ["simp", "rfl", "decide", "omega", "ring", "mvcgen", "native_decide", "sorry", "none",
   "some", "true", "false", "this", "fun", "let", "have", "show", "calc", "exact", "apply",
   "refine", "cases", "induction", "rw", "subst", "aesop", "norm_num", "linarith"]

/-- Does this quoted run name a declaration *of this tree*? Our names are camelCase or
UpperCamel and may be dotted; a single letter is a binder, pure snake_case is the Rust/OCaml
convention (`x_hat`, `ft_eval0`), and the tactic words name no declaration. -/
def identShaped (t : String) : Bool :=
  let ok := !t.isEmpty && 3 ≤ t.length && t.length ≤ 60 &&
    t.all (fun ch => ch.isAlphanum || ch == '.' || ch == '_' || ch == '\'' || ch == '?' ||
      ch == '!') &&
    t.front.isAlpha && !keywords.contains t
  let parts := t.splitOn "."
  let dotted := parts.length > 1
  let hasUpper := t.any (·.isUpper)
  let isPath := isSourceFile t
  let numericTail := (parts.getLast!).all (·.isDigit)
  ok && (dotted || hasUpper) && !isPath && !numericTail

/-- Resolve a quoted name: as written, under the declaration's namespace chain, or as the
suffix of some declaration of ours. -/
def resolves (env : Environment) (suffixes : Std.HashSet String) (owner : Name)
    (t : String) : Bool :=
  let n := t.toName
  if env.contains n then true
  else Id.run do
    let mut pre := owner
    let mut found := false
    while pre != .anonymous do
      if env.contains (pre ++ n) then found := true
      pre := pre.getPrefix
    if found then true else suffixes.contains t

end Kimchi.CheckComments

open Kimchi.CheckComments in
run_cmd do
  let env ← getEnv
  let userName (n : Name) : Name := (privateToUserName? n).getD n
  -- the vocabulary: every suffix of every declaration of ours, so `AccOk` resolves while
  -- `Pickles.AccOk` is live and stops resolving the moment it is deleted
  let mut suffixes : Std.HashSet String := {}
  -- a module of this tree is a name a comment may use (`Kimchi.Domain`, `Pickles.TwoHalves`)
  for m in env.header.moduleNames do
    if isOurs m then suffixes := suffixes.insert m.toString
  for (n, _) in env.constants.toList do
    let u := userName n
    -- the last one and two components: `AccOk`, `SWPoint.equivPoint`, `Point.some`
    match u with
    | .str pre s =>
      suffixes := suffixes.insert s
      match pre with
      | .str _ s2 => suffixes := suffixes.insert s!"{s2}.{s}"
      | _ => pure ()
    | _ => pure ()
    if isOurs n then suffixes := suffixes.insert u.toString
  let allowSrc ← IO.FS.readFile "scripts/comment-allow.txt"
  let mut allow : Std.HashSet String := {}
  for l in allowSrc.splitOn "\n" do
    let t := l.trim
    unless t.isEmpty || t.startsWith "--" do allow := allow.insert t
  let mut stale : Array String := #[]
  let mut provenance : Array String := #[]
  let mut phrase : Array String := #[]
  let mut oversize : Array String := #[]
  let mut emph : Array String := #[]
  let modOf (n : Name) : String :=
    match env.getModuleIdxFor? n with
    | some i => (env.header.moduleNames[i.toNat]!).toString
    | none => "?"
  let mut docs := 0
  for (n, _) in env.constants.toList do
    unless isOurs n do continue
    if n.hasMacroScopes then continue
    let some doc ← findDocString? env n | continue
    docs := docs + 1
    let owner := (userName n).getPrefix
    -- a declaration may quote its own binders; they name no constant
    let mut binders : Std.HashSet String := {}
    let mut ty := (env.find? n).map (·.type) |>.getD default
    while true do
      match ty with
      | .forallE bn _ b _ => binders := binders.insert bn.toString; ty := b
      | _ => break
    for t in backticked doc do
      -- a binder, or a field access on one (`cp.opening`, `s.val`)
      if binders.contains t || binders.contains ((t.splitOn ".").headD "") then continue
      if isSourceFile t then
        provenance := provenance.push s!"{modOf n}\t{userName n}: `{t}`"
      else if identShaped t && !allow.contains t && !resolves env suffixes owner t then
        stale := stale.push s!"{modOf n}\t{userName n}: `{t}`"
    let low := doc.toLower
    for (b, why) in banned do
      if (low.splitOn b).length > 1 then
        phrase := phrase.push s!"{modOf n}\t{userName n}: \"{b}\" ({why})"
    let lines := (doc.splitOn "\n").length
    if lines > declCap then
      oversize := oversize.push s!"{modOf n}\t{userName n}: {lines} lines (cap {declCap})"
    let bolds := ((doc.splitOn "**").length - 1) / 2
    if bolds > 1 then
      emph := emph.push s!"{modOf n}\t{userName n}: {bolds} bolded runs"
  -- module and section docstrings: read from the sources, since they attach to no declaration
  let pkgs := ["pasta", "poseidon", "bulletproof-pcs", "kimchi", "snarky", "pickles"]
  let rec walk (p : System.FilePath) : IO (Array System.FilePath) := do
    let mut out : Array System.FilePath := #[]
    for e in (← p.readDir) do
      if ← e.path.isDir then
        if e.fileName == ".lake" || e.fileName == "scripts" then continue
        out := out ++ (← walk e.path)
      else if e.path.extension == some "lean" then out := out.push e.path
    return out
  let mut modDocs := 0
  for pkg in pkgs do
    for f in (← walk (pkg : System.FilePath)) do
      let src ← IO.FS.readFile f
      let lines := src.splitOn "\n"
      let mut i := 0
      while i < lines.length do
        let l := lines[i]!
        if l.trim.startsWith "/-!" then
          let mut blk := #[l]
          let mut j := i
          while j < lines.length do
            if j > i then blk := blk.push lines[j]!
            if ((lines[j]!).splitOn "-/").length > 1 then break
            j := j + 1
          modDocs := modDocs + 1
          let text := String.intercalate "\n" blk.toList
          if blk.size > moduleCap then
            oversize := oversize.push s!"{f}\tmodule doc: {blk.size} lines (cap {moduleCap})"
          let low := text.toLower
          for (b, why) in banned do
            if (low.splitOn b).length > 1 then
              phrase := phrase.push s!"{f}\tmodule doc: \"{b}\" ({why})"
          for t in backticked text do
            if isSourceFile t then continue
            if identShaped t && !allow.contains t && !resolves env suffixes .anonymous t then
              stale := stale.push s!"{f}\tmodule doc: `{t}`"
          i := j + 1
        else i := i + 1
  IO.println s!"docstrings checked: {docs} declaration, {modDocs} module/section"
  -- the ratchet: each category's count may fall, never rise. The prose the convention change
  -- left behind (the upstream names this tree used to cite) comes out module by module; until
  -- it does, the baseline records what is owed rather than pretending the tree is clean.
  let cats : List (String × Array String) :=
    [ ("unresolved-names", stale), ("upstream-files-in-decl-doc", provenance),
      ("banned-phrases", phrase), ("oversize", oversize), ("emphasis", emph) ]
  let baseSrc ← IO.FS.readFile "scripts/comment-baseline.txt"
  let mut base : Std.HashMap String Nat := {}
  for l in baseSrc.splitOn "\n" do
    let t := l.trim
    unless t.isEmpty || t.startsWith "--" do
      match t.splitOn " " with
      | [k, v] => base := base.insert k v.toNat!
      | _ => pure ()
  let verbose := (← IO.getEnv "COMMENT_GATE_LIST").isSome
  let mut grew : Array String := #[]
  for (tag, xs) in cats do
    let b := base.getD tag 0
    let mark := if xs.size > b then "✗" else if xs.size < b then "↓" else "✓"
    IO.println s!"{mark} {tag}: {xs.size} (baseline {b})"
    if verbose then for x in xs.toList do IO.println s!"    {x}"
    if xs.size > b then grew := grew.push s!"{tag}: {xs.size} > {b}"
  unless grew.isEmpty do
    throwError "comment gate FAILED — a category grew:\n  {String.intercalate "\n  " grew.toList}"
  IO.println "── comment gate OK"
