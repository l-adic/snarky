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

/-- Discharge a step's adapter — the entailment from the accumulated context to
the selected law's precondition — by splitting the context and backward search
over the local facts, at reducible transparency. Unification against the context
is what pins the law's elided witness values. -/
macro "complete_ctx" : tactic =>
  `(tactic| ((try casesm* _ ∧ _);
             solve_by_elim (config := { transparency := .reducible, maxDepth := 16 })
               [And.intro]))

/-- Apply the first `@[complete_law]` lemma whose program unifies with the
goal's, in reverse registration order so downstream composite laws shadow the
primitive laws matching their unfolded prefixes. The law's non-program arguments
are left as goals: values for the adapter's unification, side conditions for
`assumption` or deferral. -/
elab "complete_apply_law" : tactic => do
  let laws ← Lean.labelled `complete_law
  let g ← getMainGoal
  for law in laws.reverse do
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
      (Snarky.Complete.imp ?adp (fun _ _ h => h) ?law) ?k)
  let s2 ← `(tactic| case mono => complete_mono_tac)
  let s3 ← `(tactic| case' law => complete_apply_law)
  let s4 ← `(tactic| case adp => (intro st h; complete_ctx))
  let s5 ← `(tactic| all_goals try assumption)
  let s6 ← `(tactic| case' k => intro $x:ident)
  evalTactic (← `(tactic| ($s1; $s2; $s3; $s4; $s5; $s6)))

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

/-- The binder names of a destructuring bind's match alternative, for splitting
the introduced pair under its source names. -/
def altNames (body : Expr) : Name × Name :=
  match body.getAppArgs.back? with
  | some (.lam n1 _ (.lam n2 _ _ _) _) => (n1.eraseMacroScopes, n2.eraseMacroScopes)
  | _ => (`fst, `snd)

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
      let (n1, n2) := altNames k.bindingBody!
      let i1 := mkIdent (stepName n1)
      let i2 := mkIdent (stepName n2)
      evalTactic (← `(tactic| obtain ⟨$i1:ident, $i2:ident⟩ := $xi:ident))
    else
      completeStep (mkIdent (stepName k.bindingName!))
  catch _ =>
    s.restore
    return
  walk

/-- Walk the goal's bind chain — see the module docstring. -/
elab "complete_walk" : tactic => walk

end Snarky.Tactic
