import Lean.Elab.Tactic.SolveByElim
import Lean.Elab.Tactic.RCases
import Mathlib.Tactic.CasesM
import Snarky.Tactic.Attr
import Snarky.Prover

/-!
# The completeness walker

`complete_walk` mechanizes the straight-line portion of a `_complete` proof: on a
goal `Complete pre (g₁ >>= fun x₁ => …) post` it walks the bind chain, and at each
bind it selects the gadget's registered `@[complete_law]`, synthesizes the frame's
`Mono` witness from the `@[complete_mono]` vocabulary, discharges the adapter by
search over the context — pinning the law's witness values by unification, so the
laws are applied with no value arguments at all — absorbs `assumption`-shaped side
conditions, and defers the rest as verification conditions behind the main goal.
It stops at the chain's `pure` (or at a bind with no registered law), leaving the
main goal first and the deferred conditions after it: what remains is the
value-level postcondition and the leaked side conditions — arithmetic and state
guarantees, no prover plumbing.

The per-step kernel is the `Complete.seq`/`Complete.imp` shape every hand
conversion used, with its holes solved in dependency order: the law's `apply`
pins the program (values stay metavariables), the adapter's search pins the
values, and only then is the continuation entered, with a fully concrete type.
A destructuring bind (`let (a, b) ← …`) is followed by splitting the introduced
pair under the source binder names, so the walk continues through the reduced
match.

The walk is atomic per step: a failing step is rolled back, never left half
applied. Loops, state-indexed invariants and `instantiate`-shaped preconditions
are out of scope by design — those proofs stay on the combinators.
-/

namespace Snarky.Tactic

open Lean Meta Elab Tactic

/-- Assemble a `Mono` witness for the step's precondition from the
`@[complete_mono]` vocabulary, at reducible transparency so the `ReadsAs`-style
abbreviations stay opaque atoms. -/
macro "complete_mono_tac" : tactic =>
  `(tactic| apply_rules (config := { transparency := .reducible, maxDepth := 80 })
      using $(Lean.mkIdent `complete_mono))

/-- A candidate's conclusion key: its head constant, and — for a reading — the
head constant of the subject (the variable argument), when it has one. Lookup
tries only candidates whose key can match the goal's, which is what keeps the
search linear where `solve_by_elim` was multiplicative in the table. -/
def conclusionKey (ty : Expr) : MetaM (Option (Name × Option Name)) :=
  Meta.forallTelescopeReducing ty fun _ body => do
    let body := body.cleanupAnnotations
    let some h := body.getAppFn.constName? | return none
    if h == ``Snarky.CircuitType.ReadsAs then
      let args := body.getAppArgs
      if args.size ≥ 2 then
        let subj := (args[args.size - 2]!).cleanupAnnotations
        return some (h, subj.getAppFn.constName?)
      else
        return some (h, none)
    else
      return some (h, none)

/-- Whether a candidate keyed `ck` can serve a goal keyed `gk`: heads equal, and
a keyed subject only against the same subject former (an unkeyed conclusion —
a bound-variable subject — is tried against anything of the right head). -/
def keyServes (gk ck : Name × Option Name) : Bool :=
  gk.1 == ck.1 && (ck.2.isNone || gk.2 == ck.2)

/-- The backward reading search: keyed candidate lookup — local hypotheses
first, then the `@[complete_reads]` table in reverse registration order — with
reducible-transparency `apply` and premise recursion. `apply`'s unification is
what pins a law's elided witness values, which is the capability the engine
exists to keep (indexed off-the-shelf search declines goals with assignable
metavariables). -/
partial def solveAtom (rules : Array (Expr × (Name × Option Name)))
    (g : MVarId) (fuel : Nat) : Elab.Tactic.TacticM Bool := g.withContext do
  if fuel == 0 then return false
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let some gh := ty.getAppFn.constName? | return false
  let gk : Name × Option Name ←
    if gh == ``Snarky.CircuitType.ReadsAs then
      let args := ty.getAppArgs
      if args.size ≥ 2 then
        let subj ← Meta.withReducible <|
          Meta.whnfCore (args[args.size - 2]!).cleanupAnnotations
        pure (gh, subj.getAppFn.constName?)
      else pure (gh, none)
    else pure (gh, none)
  -- local hypotheses, most recent first, then the table
  let hyps ← g.getNondepPropHyps
  let mut cands : Array (Expr × (Name × Option Name)) := #[]
  for h in hyps.reverse do
    if let some k ← conclusionKey (← h.getType) then
      cands := cands.push (.fvar h, k)
  let allCands := cands ++ rules
  for (e, ck) in allCands do
    unless keyServes gk ck do continue
    let s ← Tactic.saveState
    let ok ← try
        let gs ← Meta.withReducible <| g.apply e
        let mut ok := true
        for g' in gs do
          if ← g'.isAssigned then continue
          unless ← solveAtom rules g' (fuel - 1) do
            ok := false
            break
        pure ok
      catch _ =>
        pure false
    if ok then return true
    s.restore
  return false

/-- The table, keyed — reverse registration so downstream rules shadow. -/
def readsRules : Elab.Tactic.TacticM (Array (Expr × (Name × Option Name))) := do
  let names ← Lean.labelled `complete_reads
  let mut out : Array (Expr × (Name × Option Name)) := #[]
  for n in names.reverse do
    if let some k ← conclusionKey (← getConstInfo n).type then
      out := out.push (← Lean.Meta.mkConstWithFreshMVarLevels n, k)
  return out

/-- One adapter atom, by the keyed backward search — see `solveAtom`. -/
elab "complete_reads_search" : tactic => do
  let g ← Elab.Tactic.getMainGoal
  unless ← solveAtom (← readsRules) g 12 do
    throwError "complete_reads_search: no derivation for this atom"
  Elab.Tactic.replaceMainGoal []

/-- Fails unless the goal is a reading-family atom — the only goals the forward
saturation can help, so the expensive retry is never spent on a side condition
(a torsion `≠`, a finiteness guard) that a designed stop leaves unprovable. -/
elab "complete_reads_goal_guard" : tactic => do
  let ty := (← instantiateMVars (← (← getMainGoal).getType)).cleanupAnnotations
  let ok := match ty.getAppFn.constName? with
    | some n =>
      n == ``Snarky.CircuitType.ReadsAs || n == `Snarky.Kimchi.OnCurveAs ||
      n == `Snarky.Kimchi.SpongeVar.Reads || n == ``List.Forall₂
    | none => false
  unless ok do throwError "not a reading-family goal"

/-- The saturated retry — the same engine; the name survives only so the
rescue's saturation has a seam to run in. -/
macro "complete_reads_search_deep" : tactic =>
  `(tactic| complete_reads_search)

/-- Saturate the context forward with the `@[complete_reads_fwd]` projections:
for every hypothesis a projection applies to, its conclusion joins the context —
bounded passes, no duplicates. Projections run forward because their conclusions
are unkeyed and would match every goal backward. -/
elab "complete_reads_saturate" : tactic => do
  let fwd ← Lean.labelled `complete_reads_fwd
  -- each rule keyed by its (single) premise's head constant, for a cheap pre-filter
  let keyed ← fwd.mapM fun f => do
    let ty := (← getConstInfo f).type
    let key ← Meta.forallTelescopeReducing ty fun xs _ => do
      match xs.back? with
      | some x => pure (← instantiateMVars (← Meta.inferType x)).getAppFn.constName?
      | none => pure none
    pure (f, key)
  for _ in [0:1] do
    let added ← Elab.Tactic.withMainContext do
      let hyps ← (← getMainGoal).getNondepPropHyps
      let mut seen : Array Expr := #[]
      for h in hyps do
        seen := seen.push ((← h.getType).consumeMData)
      let mut added := false
      for h in hyps do
        let hHead := ((← h.getType).consumeMData).getAppFn.constName?
        for (f, key) in keyed do
          if key.isSome && key ≠ hHead then continue
          -- probe without committing: failed applications leave no state behind
          let cand ← Meta.withNewMCtxDepth <| Elab.Tactic.tryTactic? <| do
            let e ← Meta.mkAppM f #[.fvar h]
            let t ← instantiateMVars (← Meta.inferType e)
            if t.hasMVar then failure
            pure t
          let some t := cand | continue
          if seen.contains t.consumeMData then continue
          seen := seen.push t.consumeMData
          added := true
          let e ← Meta.mkAppM f #[.fvar h]
          let g ← (← getMainGoal).assert (← mkFreshUserName `hfwd) t e
          let (_, g) ← g.intro1P
          replaceMainGoal [g]
      pure added
    unless added do return

/-- Discharge a step's adapter — the entailment from the accumulated context to
the selected law's precondition: split the context, saturate it forward with the
projections, split the goal into atoms, and search each atom independently, so
failures stay local instead of backtracking across the conjunction. -/
macro "complete_ctx" : tactic =>
  `(tactic| ((try casesm* _ ∧ _);
             (try with_reducible and_intros);
             all_goals first
               | exact trivial
               | complete_reads_search
               | (complete_reads_goal_guard;
                  (try complete_reads_saturate);
                  complete_reads_search_deep)))

/-- The head constant of a `Complete` statement's program, through binders — the
cheap pre-filter key for law lookup. `none` when it has no stable head. -/
def lawProgramHead : Expr → Option Name
  | .forallE _ _ b _ => lawProgramHead b
  | e =>
    let args := e.getAppArgs
    if e.getAppFn.isConstOf ``Snarky.Complete && args.size ≥ 3 then
      let fn := (args[args.size - 2]!).cleanupAnnotations.getAppFn
      if fn.isConst then some fn.constName! else none
    else none

/-- Apply the first `@[complete_law]` lemma whose program unifies with the
goal's, in reverse registration order so downstream composite laws shadow the
primitive laws matching their unfolded prefixes. The law's non-program arguments
are left as goals: values for the adapter's unification, side conditions for
`assumption` or deferral. -/
elab "complete_apply_law" : tactic => do
  let laws ← Lean.labelled `complete_law
  let g ← getMainGoal
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let args := ty.getAppArgs
  let goalHead : Option Name :=
    if ty.getAppFn.isConstOf ``Snarky.Complete && args.size ≥ 3 then
      let fn := (args[args.size - 2]!).cleanupAnnotations.getAppFn
      if fn.isConst then some fn.constName! else none
    else none
  for law in laws.reverse do
    -- skip a law whose program cannot match: unifying against a stuck recursive
    -- program (a loop combinator, say) is expensive enough to matter times the table
    if let (some gh, some lh) := (goalHead, lawProgramHead (← getConstInfo law).type) then
      if gh ≠ lh then continue
    let s ← Tactic.saveState
    try
      let gs ← g.apply (← mkConstWithFreshMVarLevels law)
      replaceMainGoal gs
      return
    catch _ =>
      s.restore
  throwError "complete_apply_law: no @[complete_law] lemma applies to this program"

/-- One step of the walk, introducing the bind's value as `x`: the proven kernel
shape, its holes solved in dependency order (`Mono` witness, law, adapter, side
conditions, continuation). `case'` lets the law's value goals and deferred side
conditions rejoin the goal list instead of demanding closure inside the step. -/
def completeStep (x : Ident) : TacticM Unit := withFreshMacroScope do
  let s1 ← `(tactic| apply Snarky.Complete.seq ?mono
      (Snarky.Complete.imp ?adp (fun _ _ h => h) ?law) ?kont)
  let s2 ← `(tactic| case mono => ((try simp only []); complete_mono_tac))
  let s3 ← `(tactic| case' law => complete_apply_law)
  let s4 ← `(tactic| case adp => (intro st h; (try simp only [] at h); complete_ctx))
  let s5 ← `(tactic| all_goals try with_reducible assumption)
  let s6 ← `(tactic| case' kont => intro $x:ident)
  -- without this, a failing case body is RECOVERED (logged and admitted as sorry)
  -- and the walk would march on past a step it did not actually prove
  withoutRecover <| evalTactic (← `(tactic| ($s1; $s2; $s3; $s4; $s5; $s6)))

/-- From a goal `Complete pre prog post`, the continuation of `prog`'s head bind,
or `none` when `prog` is not a bind (the walk's stop condition). Reduction is
`whnfCore` only — matches on introduced pairs reduce, gadget definitions never
unfold, so the walk cannot fall into an unregistered gadget's body. -/
def extractCont (ty : Expr) : MetaM (Option Expr) := do
  let ty := (← instantiateMVars ty).cleanupAnnotations
  unless ty.getAppFn.isConstOf ``Snarky.Complete do return none
  let args := ty.getAppArgs
  unless args.size ≥ 3 do return none
  let rec go (e : Expr) : Nat → MetaM (Option Expr)
    | 0 => return none
    | fuel + 1 => do
      let e := e.cleanupAnnotations
      let fn := e.getAppFn
      if fn.isConstOf ``Bind.bind then
        return some e.getAppArgs.back!
      let e' ← whnfCore e
      if e' == e then return none else go e' fuel
  go args[args.size - 2]! 4

/-- The binder names of a destructuring bind's match alternative — the pattern's
variables, in order — for splitting the introduced tuple under its source names.
A match alternative is exactly one lambda per pattern variable (its body is a
program term, never a lambda), so collecting the leading binders is the arity. -/
def altBinderNames (body : Expr) : Array Name :=
  match body.getAppArgs.back? with
  | some alt => go alt #[]
  | none => #[]
where
  /-- Collect the leading lambda binders. -/
  go : Expr → Array Name → Array Name
    | .lam n _ b _, acc => go b (acc.push n.eraseMacroScopes)
    | _, acc => acc

/-- A do-binder name fit for reintroduction: macro scopes erased, anonymous and
`_` binders replaced. -/
def stepName (n : Name) : Name :=
  let n := n.eraseMacroScopes
  if n.isAnonymous || n == `_ then Name.mkSimple "a" else n

/-- The walk: step while the goal's program is a bind with a registered law,
rolling back and stopping at the first bind the kernel cannot handle. -/
partial def walk : TacticM Unit := do
  let some k ← extractCont (← (← getMainGoal).getType) | return
  unless k.isLambda do return
  let isPair := k.bindingDomain!.getAppFn.isConstOf ``Prod
  let s ← Tactic.saveState
  try
    if isPair then
      let xi := mkIdent (Name.mkSimple "__sf")
      completeStep xi
      let collected := (altBinderNames k.bindingBody!).map stepName
      let names := if collected.size ≥ 2 then collected else #[`fst, `snd]
      -- split the nested product pairwise, innermost last
      let mut cur := xi
      for i in [0 : names.size - 2] do
        let ni := mkIdent names[i]!
        let tmp := mkIdent (Name.mkSimple s!"__sf{i}")
        evalTactic (← `(tactic| obtain ⟨$ni:ident, $tmp:ident⟩ := $cur:ident))
        cur := tmp
      let a := mkIdent names[names.size - 2]!
      let b := mkIdent names[names.size - 1]!
      evalTactic (← `(tactic| obtain ⟨$a:ident, $b:ident⟩ := $cur:ident))
    else
      completeStep (mkIdent (stepName k.bindingName!))
  catch _ =>
    s.restore
    return
  walk

/-- Walk the goal's bind chain — see the module docstring. -/
elab "complete_walk" : tactic => walk

end Snarky.Tactic
