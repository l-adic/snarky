import Kimchi
import Lean

/-!
# Spec-surface extractor (dev tooling — NOT part of the library)

Renders, for a set of headline declarations, their statements + the transitive closure
of the definitions / structures they (and their assumptions) rest on. Proofs are never
traversed, so only the *statement surface* appears — helper lemmas used solely inside
proofs are excluded. Each entry carries the Lean signature, a GitHub source link, and
its direct `Kimchi` dependencies (the blueprint `\uses` edges).

Driven by `make lean-docs`: roots come from `roots.txt` (the CI sorry-gate list + the
Pasta instantiation); output is `blueprint.md` → HTML (`pandoc`) → PDF (`weasyprint`,
since this project's LaTeX toolchain can't load OTF fonts).
-/

open Lean Meta Elab Command

namespace Render

def repoBase : String := "https://github.com/l-adic/snarky/blob/add-lean-endomul/formal/"

def isOurs (n : Name) : Bool := (`Kimchi).isPrefixOf n && !n.isInternal

/-- Expressions to traverse for dependency collection: a theorem contributes only its
    TYPE (statement + assumptions), never its proof; a data `def` its type and value; a
    `Prop`-valued def (a packaged proof) only its type; a structure its constructor (=
    its fields). -/
def traverseExprs (ci : ConstantInfo) : MetaM (List Expr) := do
  let env ← getEnv
  match ci with
  | .defnInfo d =>
    if (← Meta.isProp d.type) then return [d.type] else return [d.type, d.value]
  | .inductInfo i => return i.type :: i.ctors.filterMap (fun c => (env.find? c).map (·.type))
  | _ => return [ci.type]

/-- The `Kimchi` constants directly referenced in a declaration's signature (and, for a
    data def, its value). -/
def directDeps (n : Name) : MetaM (List Name) := do
  let env ← getEnv
  let some ci := env.find? n | return []
  let exprs ← traverseExprs ci
  let consts := exprs.foldl (fun s e => e.getUsedConstants.foldl (·.insert ·) s) (∅ : NameSet)
  return consts.toList.filter (fun m => isOurs m && m != n)

partial def collect : List Name → NameSet → MetaM NameSet
  | [], acc => return acc
  | n :: rest, acc => do
    if acc.contains n then collect rest acc
    else match (← getEnv).find? n with
      | none => collect rest acc
      | some ci =>
        let acc := acc.insert n
        let exprs ← traverseExprs ci
        let consts := exprs.foldl (fun s e => e.getUsedConstants.foldl (·.insert ·) s) (∅ : NameSet)
        collect ((consts.toList.filter (fun m => isOurs m && !acc.contains m)) ++ rest) acc

/-- Compiler-generated declarations to skip: projections, constructors, recursors, and
    the usual auto-gen suffixes — the structure itself already shows the fields. -/
def autoGenSuffix : List String :=
  ["rec", "recOn", "casesOn", "mk", "injEq", "noConfusion", "noConfusionType", "below",
   "brecOn", "ndrec", "sizeOf", "toCtorIdx", "ofNat", "rawCast", "binductionOn", "ind"]

def shouldRender (n : Name) : MetaM Bool := do
  let env ← getEnv
  if env.isProjectionFn n then return false
  if let .str _ last := n then if autoGenSuffix.contains last then return false
  match env.find? n with
  | some (.ctorInfo _) | some (.recInfo _) | some (.quotInfo _) => return false
  | some _ => return true
  | none => return false

/-- Drop the `.{u_1}` universe annotation `ppSignature` prints after the name. -/
def stripUniv (s : String) : String :=
  match s.splitOn ".{" with
  | [a, b] => a ++ (b.dropWhile (· != '}')).drop 1
  | _ => s

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom"
  | .inductInfo _ => "structure" | _ => "def"

def locOf (n : Name) : MetaM (String × Nat) := do
  let env ← getEnv
  let mod := match env.getModuleIdxFor? n with
    | some idx => (env.header.moduleNames[idx.toNat]!).toString
    | none => "?"
  let line := match (← findDeclarationRanges? n) with
    | some r => r.range.pos.line | none => 0
  return (mod, line)

def renderOne (n : Name) : MetaM String := do
  let env ← getEnv
  let some ci := env.find? n | return ""
  let doc := (← findDocString? env n).getD ""
  let sigName := match ci with | .inductInfo i => i.ctors.head! | _ => n
  let mut body := stripUniv ((← Lean.PrettyPrinter.ppSignature sigName).fmt.pretty 80)
  if let .inductInfo _ := ci then body := body.replace s!"{sigName}" s!"{n}"
  if let .defnInfo d := ci then
    unless (← Meta.isProp d.type) do body := body ++ " :=\n  " ++ (← ppExpr d.value).pretty 76
  let (mod, line) ← locOf n
  let src := s!"{repoBase}{mod.replace "." "/"}.lean#L{line}"
  let deps ← (← directDeps n).filterMapM
    (fun d => do return if (← shouldRender d) then some s!"`{d}`" else none)
  let depsLine := if deps.isEmpty then "" else s!"**Uses:** {String.intercalate ", " deps}\n\n"
  let kind := kindOf ci
  let docBlock := if doc.isEmpty then "" else s!"{doc}\n\n"
  let head := s!"#### `{n}` — {kind}\n\n{docBlock}```lean\n{kind} {body}\n```\n\n"
  return head ++ depsLine ++ s!"[source]({src})\n\n---\n\n"

def run (roots : List Name) : MetaM String := do
  let names ← collect roots {}
  let withLoc ← names.toList.mapM (fun n => do return (n, ← locOf n))
  let sorted := withLoc.toArray.qsort (fun a b =>
    if a.2.1 == b.2.1 then a.2.2 < b.2.2 else a.2.1 < b.2.1)
  let mut out := "% kimchi formalization — statements and definitions\n\n"
  let mut curMod := ""
  for (n, mod, _) in sorted do
    if ← shouldRender n then
      if mod != curMod then curMod := mod; out := out ++ s!"\n# {mod}\n\n"
      out := out ++ (← renderOne n)
  return out

end Render

-- Roots are read from `roots.txt` (one fully-qualified declaration name per line),
-- generated by `make lean-docs`.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let content ← IO.FS.readFile "roots.txt"
  let roots := (content.splitOn "\n").filterMap (fun l =>
    let l := l.replace "\r" ""
    if l.isEmpty then none else some l.toName)
  let md ← liftTermElabM (Render.run roots)
  IO.FS.writeFile "blueprint.md" md
  logInfo s!"wrote blueprint.md ({md.length} bytes, {roots.length} roots)"
