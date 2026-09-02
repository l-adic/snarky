import Pickles.Linearization.Types

/-!
# The linearization stack machine

The interpreter for `PolishToken` programs, ported from
`packages/pickles/src/Pickles/Linearization/Interpreter.purs` — itself OCaml
`plonk_checks.ml`'s expression evaluator.

## One interpreter, not two

The PureScript has `evaluate` (pure, over `Env a`) and `evaluateM` (in circuit, over
`EnvM f n`, where `mul` and `pow` emit constraints). They are separate functions because
PureScript has no cheap way to abstract "pure or monadic". Here they are ONE definition,
generic in the monad: `m := Id` recovers the pure reading, and the circuit reading is the
same function at the constraint-building monad.

That is not cosmetic. It makes "the circuit interpreter agrees with the pure one" a
simulation over the ENVIRONMENT — pointwise-related environments give related results —
rather than a lockstep argument over two similar-but-different control flows. The shared
control flow never enters the proof. It also matches the house idiom next door
(`Snarky.BasicSystem` / `LawfulBasicSystem` with `Builder V c`).

The two optimisations that make PureScript's `evaluateM` differ from its `evaluate` do not
live here:

* the **Alpha+Pow peephole** (`Challenge Alpha` followed by `Pow n` collapsing to a lookup
  of `α^n`, saving constraints because `alphaPow` reads a precomputed table while `pow`
  emits) becomes a token pre-pass, correct under the environment law
  `pow (alphaPow 1) n = alphaPow n`;
* the **ζⁿ⁻¹ memo** becomes the circuit environment's own business — which is why
  `unnormalizedLagrangeBasis` is monadic here, exactly as `EnvM` splits it into
  `computeZetaToNMinus1` and `lagrangeBasis`.

Relocating both keeps this file a single shared control flow, and turns each divergence
into a named lemma instead of a structural difference.

## Faithful junk

The deployed interpreter is **total by defaulting**, and that is modelled, not repaired.
Every stack underflow, every out-of-range `Load`, every index past the end of the program
silently advances rather than failing, and the final answer is the top of the stack or zero
if the stack is empty. A malformed program therefore computes garbage rather than an error.

This is deliberate: an `Option`-returning interpreter would be cleaner mathematics and a
different program, and the object of study is the one that ships. The statement that the
deployed streams never reach a default branch belongs to a well-formedness predicate over a
concrete program, where it is decidable — not to this definition.

## Fuel, not well-founded recursion

`SkipIfNot` evaluates both of its branches by re-entering the loop at nested bounds, and
jumps advance the position by a count carried in the token, so the recursion is not
structural in the program. Rather than a well-founded measure — which CLAUDE.md warns
against in executable paths, since it obstructs kernel reduction — the loop takes a fuel
budget. `evaluate` supplies `toks.size`, which suffices because the position strictly
increases along every path and is bounded by the end position; that is the fuel-sufficiency
statement the well-formedness layer discharges.
-/

namespace Pickles.Linearization

/-- The interpreter's environment: how the abstract stack machine's operations are realised
at a particular carrier and monad. Mirrors PureScript's `Env a` and `EnvM f n`, unified.

Additive operations are pure because they are free in circuit (`CVar` addition is affine);
multiplicative ones are monadic because they emit constraints. The pure reading takes
`m := Id`, at which every monadic field is an ordinary function. -/
structure Env (m : Type → Type) (F : Type) where
  /-- Addition. Pure: free in circuit. -/
  add : F → F → F
  /-- Subtraction. Pure: free in circuit. -/
  sub : F → F → F
  /-- Multiplication. Monadic: emits a constraint in circuit. -/
  mul : F → F → m F
  /-- Exponentiation by a literal exponent. Monadic: emits constraints in circuit. -/
  pow : F → Nat → m F
  /-- The evaluation of a column at a row. -/
  var : Column → CurrOrNext → F
  /-- Post-processing of a cell reading. Identity in the deployed environments; kept
  because the PureScript carries it. -/
  cell : F → F
  /-- `α^n`. A lookup into precomputed powers in circuit, which is what the Alpha+Pow
  peephole exists to reach. -/
  alphaPow : Nat → F
  /-- Entry `(row, col)` of the Poseidon MDS matrix. -/
  mds : Nat → Nat → F
  /-- The curve's endomorphism coefficient. -/
  endoCoefficient : F
  /-- A numeric literal, already decoded from its hex string by the token parser. -/
  literal : Nat → F
  /-- The zero-knowledge/previous-rows vanishing evaluation. -/
  vanishesOnZeroKnowledgeAndPreviousRows : F
  /-- The unnormalized Lagrange basis at a signed offset. Monadic: the circuit
  implementation computes `ζⁿ⁻¹` once and divides, and owns that memo itself. -/
  unnormalizedLagrangeBasis : Bool → Int → m F
  /-- The lookup joint combiner. Outside the modelled fragment. -/
  jointCombiner : F
  /-- The permutation challenge `β`. -/
  beta : F
  /-- The permutation challenge `γ`. -/
  gamma : F
  /-- Select between the branches of a feature-flag conditional. The branches are THUNKS,
  so the branch not taken is never forced — which is how an environment that disables every
  optional feature (as the deployed pure environment does, and as the modelled fragment
  requires) evaluates none of the dead code. -/
  ifFeature : FeatureFlag → (Unit → m F) → (Unit → m F) → m F

/-- The machine state: an operand stack, an append-only store for shared subexpressions,
and a program counter. A concrete structure by requirement — CLAUDE.md's warning that state
threaded through executable folds must be data, since function-valued state is eta-expanded
and the fold goes exponential. -/
structure EvalState (F : Type) where
  /-- The operand stack; the top is the last element. -/
  stack : Array F
  /-- The store, appended to by `Store` and indexed by `Load`. -/
  store : Array F
  /-- The index of the next token to execute. -/
  position : Nat

namespace EvalState

variable {F : Type}

/-- The empty state at the start of a program. -/
def init : EvalState F := ⟨#[], #[], 0⟩

/-- Move to the next token. -/
def advance (s : EvalState F) : EvalState F := { s with position := s.position + 1 }

/-- Push a value. -/
def push (v : F) (s : EvalState F) : EvalState F := { s with stack := s.stack.push v }

/-- Pop one value, or `none` on underflow. -/
def pop (s : EvalState F) : Option (F × EvalState F) :=
  match s.stack.back? with
  | some v => some (v, { s with stack := s.stack.pop })
  | none => none

/-- Pop two values, or `none` on underflow. The first component is the DEEPER operand, so
`pop2` reads `a op b` in source order. -/
def pop2 (s : EvalState F) : Option (F × F × EvalState F) :=
  match s.pop with
  | some (b, s₁) => match s₁.pop with
    | some (a, s₂) => some (a, b, s₂)
    | none => none
  | none => none

end EvalState

open EvalState

variable {m : Type → Type} {F : Type}

/-- A constant's value. -/
def evalConstant (env : Env m F) : ConstantTerm → F
  | .endoCoefficient => env.endoCoefficient
  | .mds row col => env.mds row col
  | .literal v => env.literal v

/-- A challenge's value. `Alpha` reads `α^1`; the fused `α^n` reading is the peephole's
business, not this function's. -/
def evalChallenge (env : Env m F) : ChallengeTerm → F
  | .alpha => env.alphaPow 1
  | .beta => env.beta
  | .gamma => env.gamma
  | .jointCombiner => env.jointCombiner

/-- The top of the stack, or zero when it is empty — the deployed interpreter's answer for
an exhausted stack. -/
def topOrZero (env : Env m F) (s : EvalState F) : F :=
  s.stack.back?.getD (env.literal 0)

/-- Execute `toks` from `s.position` until `endPos`, within a fuel budget.

The `SkipIfNot` case is where the layout is decoded: the marker at `p` is followed by
`n` tokens of enabled-branch, a `SkipIf` marker, then the disabled-branch. Both branches are
evaluated from the SAME starting state and contribute only their top-of-stack value —
execution then resumes past both with that value pushed onto the ORIGINAL stack, so a
branch's own stack and store effects are discarded. That discarding is what makes excising
a dead branch safe: its stores never reach the outer store, so `Load` indices cannot
shift. -/
def evalLoop [Monad m] (env : Env m F) (toks : Array PolishToken) :
    Nat → Nat → EvalState F → m (EvalState F)
  | 0, _, s => pure s
  | fuel + 1, endPos, s =>
    if s.position ≥ endPos then pure s
    else match toks[s.position]? with
      | none => pure s
      | some tok => match tok with
        | .constant c =>
            evalLoop env toks fuel endPos (push (evalConstant env c) (advance s))
        | .challenge c =>
            evalLoop env toks fuel endPos (push (evalChallenge env c) (advance s))
        | .cell col row =>
            evalLoop env toks fuel endPos (push (env.cell (env.var col row)) (advance s))
        | .vanishesOnZeroKnowledgeAndPreviousRows =>
            evalLoop env toks fuel endPos
              (push env.vanishesOnZeroKnowledgeAndPreviousRows (advance s))
        | .dup =>
            match s.stack.back? with
            | some top => evalLoop env toks fuel endPos (push top (advance s))
            | none => evalLoop env toks fuel endPos (advance s)
        | .add =>
            match s.pop2 with
            | some (a, b, s') => evalLoop env toks fuel endPos (push (env.add a b) (advance s'))
            | none => evalLoop env toks fuel endPos (advance s)
        | .sub =>
            match s.pop2 with
            | some (a, b, s') => evalLoop env toks fuel endPos (push (env.sub a b) (advance s'))
            | none => evalLoop env toks fuel endPos (advance s)
        | .mul =>
            match s.pop2 with
            | some (a, b, s') => do
                let r ← env.mul a b
                evalLoop env toks fuel endPos (push r (advance s'))
            | none => evalLoop env toks fuel endPos (advance s)
        | .pow n =>
            match s.pop with
            | some (v, s') => do
                let r ← env.pow v n
                evalLoop env toks fuel endPos (push r (advance s'))
            | none => evalLoop env toks fuel endPos (advance s)
        | .unnormalizedLagrangeBasis zk off => do
            let r ← env.unnormalizedLagrangeBasis zk off
            evalLoop env toks fuel endPos (push r (advance s))
        | .store =>
            match s.pop with
            | some (v, s') =>
                evalLoop env toks fuel endPos
                  (push v (advance { s' with store := s'.store.push v }))
            | none => evalLoop env toks fuel endPos (advance s)
        | .load i =>
            match s.store[i]? with
            | some v => evalLoop env toks fuel endPos (push v (advance s))
            | none => evalLoop env toks fuel endPos (advance s)
        | .skipIf _ n =>
            evalLoop env toks fuel endPos { s with position := s.position + 1 + n }
        | .skipIfNot f n => do
            let trueEnd := s.position + 1 + n
            let countFalse := match toks[trueEnd]? with
              | some (.skipIf _ c) => c
              | _ => 0
            let falseEnd := trueEnd + 1 + countFalse
            let res ← env.ifFeature f
              (fun _ => do
                let s₁ ← evalLoop env toks fuel trueEnd { s with position := s.position + 1 }
                pure (topOrZero env s₁))
              (fun _ => do
                let s₁ ← evalLoop env toks fuel falseEnd { s with position := trueEnd + 1 }
                pure (topOrZero env s₁))
            evalLoop env toks fuel endPos (push res { s with position := falseEnd })

/-- Run a whole program: the value it leaves on top of the stack, or zero.

The fuel budget is the program length. That suffices because the position strictly
increases at every step and is bounded by the end position, so no execution path visits
more than `toks.size` tokens — the fuel-sufficiency fact the well-formedness layer states
and discharges. -/
def evaluate [Monad m] (env : Env m F) (toks : Array PolishToken) : m F := do
  let s ← evalLoop env toks toks.size toks.size EvalState.init
  pure (topOrZero env s)

end Pickles.Linearization
