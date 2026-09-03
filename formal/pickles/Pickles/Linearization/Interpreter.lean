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

theorem pop_position {s s' : EvalState F} {v : F} (h : s.pop = some (v, s')) :
    s'.position = s.position := by
  simp only [EvalState.pop] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
  · exact absurd h (by simp)

theorem pop2_position {s s' : EvalState F} {a b : F} (h : s.pop2 = some (a, b, s')) :
    s'.position = s.position := by
  simp only [EvalState.pop2] at h
  split at h
  · rename_i b₁ s₁ h₁
    split at h
    · rename_i a₁ s₂ h₂
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.2, pop_position h₂, pop_position h₁]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Apply `φ` to every cell of the stack and store; the position is unchanged. -/
def map {S : Type} (φ : F → S) (s : EvalState F) : EvalState S :=
  ⟨s.stack.map φ, s.store.map φ, s.position⟩

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

/-- The length of a disabled branch: the count carried by the `SkipIf` marker at
`trueEnd`, or zero when there is none. -/
def falseCount (toks : Array PolishToken) (trueEnd : Nat) : Nat :=
  match toks[trueEnd]? with
  | some (.skipIf _ c) => c
  | _ => 0

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
        | .challenge .alpha =>
            -- The Alpha+Pow peephole. Rust's `to_polish` only ever emits `Alpha` as part
            -- of `Expr::Pow(alpha, n)`, so the pair fuses to one table lookup; the
            -- fallback is defensive and fires on no deployed stream. It is what keeps the
            -- α-sites free in circuit — 95 of the 474 rows at the deployed length — and it
            -- is value-preserving wherever `alphaPow n` reads as `α^n`.
            match toks[s.position + 1]? with
            | some (.pow n) =>
                evalLoop env toks fuel endPos
                  (push (env.alphaPow n) { s with position := s.position + 2 })
            | _ => evalLoop env toks fuel endPos (push (env.alphaPow 1) (advance s))
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
            let falseEnd := trueEnd + 1 + falseCount toks trueEnd
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


/-! ## Where the α-table is read

`alphaPow` is reached from exactly one place: the Alpha+Pow peephole, at `n` when `Alpha`
is followed by `Pow n` and at `1` otherwise. So the exponents a run can read are a
SYNTACTIC property of the program, listable by inspecting the array — and a run is
insensitive to the table anywhere else. That is what lets a FINITE precomputed table
discharge every α-obligation of a concrete stream: the obligation is stated on
`alphaExponents toks`, and for the deployed streams that list is decided once, from the
array, rather than assumed. -/

/-- The exponents at which running `toks` may read `alphaPow`: `n` for each `Alpha` the
peephole fuses with a following `Pow n`, and `1` for each it does not. -/
def alphaExponents (toks : Array PolishToken) : List Nat :=
  (List.range toks.size).filterMap fun i =>
    match (toks[i]? : Option PolishToken) with
    | some (.challenge .alpha) =>
      match (toks[i + 1]? : Option PolishToken) with
      | some (.pow n) => some n
      | _ => some 1
    | _ => none

/-- A fused `Alpha`/`Pow n` reads exponent `n`. -/
theorem mem_alphaExponents_of_pow {toks : Array PolishToken} {i n : Nat}
    (hi : toks[i]? = some (.challenge .alpha)) (hp : toks[i + 1]? = some (.pow n)) :
    n ∈ alphaExponents toks := by
  have hlt : i < toks.size := (Array.getElem?_eq_some_iff.mp hi).1
  simp only [alphaExponents, List.mem_filterMap, List.mem_range]
  exact ⟨i, hlt, by simp [hi, hp]⟩

/-- An unfused `Alpha` reads exponent `1`. -/
theorem mem_alphaExponents_one {toks : Array PolishToken} {i : Nat}
    (hi : toks[i]? = some (.challenge .alpha))
    (hp : ∀ n, toks[i + 1]? ≠ some (.pow n)) :
    1 ∈ alphaExponents toks := by
  have hlt : i < toks.size := (Array.getElem?_eq_some_iff.mp hi).1
  simp only [alphaExponents, List.mem_filterMap, List.mem_range]
  refine ⟨i, hlt, ?_⟩
  cases h : toks[i + 1]? with
  | none => simp [hi]
  | some t =>
    cases t with
    | pow n => exact absurd h (hp n)
    | _ => simp [hi]

/-- `env` with its α-table replaced. -/
def Env.withAlphaPow (env : Env m F) (g : Nat → F) : Env m F := { env with alphaPow := g }

/-- **A run reads the α-table only at `alphaExponents`.** Two environments differing only
in the table, and agreeing there, run identically — for every fuel, bound and start.

Every case but the peephole's is `ih` then `rfl`: once the recursive call is rewritten,
the two sides differ only in a projection of the updated record, which is definitional. -/
theorem evalLoop_withAlphaPow [Monad m] (env : Env m F) (g : Nat → F)
    (toks : Array PolishToken) (hg : ∀ n ∈ alphaExponents toks, g n = env.alphaPow n) :
    ∀ (fuel endPos : Nat) (s : EvalState F),
      evalLoop (env.withAlphaPow g) toks fuel endPos s = evalLoop env toks fuel endPos s := by
  intro fuel
  induction fuel with
  | zero => intro endPos s; rfl
  | succ fuel ih =>
    intro endPos s
    rw [evalLoop, evalLoop]
    split
    · rfl
    · cases htok : toks[s.position]? with
      | none => rfl
      | some tok =>
        cases tok with
        | challenge c =>
          cases c with
          | alpha =>
            cases hp : toks[s.position + 1]? with
            | some t =>
              cases t with
              | pow n =>
                simp only [ih]
                simp only [Env.withAlphaPow, hg n (mem_alphaExponents_of_pow htok hp)]
              | _ =>
                simp only [ih]
                simp only [Env.withAlphaPow,
                  hg 1 (mem_alphaExponents_one htok (fun _ h => by rw [hp] at h; cases h))]
            | none =>
              simp only [ih]
              simp only [Env.withAlphaPow,
                hg 1 (mem_alphaExponents_one htok (fun _ h => by rw [hp] at h; cases h))]
          | _ => simp only [ih] <;> rfl
        | _ => simp only [ih] <;> rfl

/-- **The entry point reads the α-table only at `alphaExponents`.** -/
theorem evaluate_withAlphaPow [Monad m] (env : Env m F) (g : Nat → F)
    (toks : Array PolishToken) (hg : ∀ n ∈ alphaExponents toks, g n = env.alphaPow n) :
    evaluate (env.withAlphaPow g) toks = evaluate env toks := by
  simp only [evaluate, evalLoop_withAlphaPow env g toks hg]
  rfl


/-! ## Where a disabled-features run goes

With every feature disabled, `SkipIfNot` runs its second branch only, so the positions a
run visits are again a property of the program: `visited` walks the array with
`evalLoop`'s control flow and no stack. A token the walk never reaches cannot influence
the result, which is how `evaluate_withUlb` removes `unnormalizedLagrangeBasis` from the
statement about the deployed streams: the walk decides that no visited position holds one,
so the environment's implementation of it is irrelevant. -/

/-- The positions a run with every feature disabled visits, from `pos` up to `endPos`
within `fuel` steps. Mirrors `evalLoop`. -/
def visited (toks : Array PolishToken) : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | fuel + 1, endPos, pos =>
    if pos ≥ endPos then []
    else match (toks[pos]? : Option PolishToken) with
      | none => []
      | some (.challenge .alpha) =>
        match (toks[pos + 1]? : Option PolishToken) with
        | some (.pow _) => pos :: visited toks fuel endPos (pos + 2)
        | _ => pos :: visited toks fuel endPos (pos + 1)
      | some (.skipIf _ n) => pos :: visited toks fuel endPos (pos + 1 + n)
      | some (.skipIfNot _ n) =>
        pos :: (visited toks fuel (pos + 1 + n + 1 + falseCount toks (pos + 1 + n))
            (pos + 1 + n + 1)
          ++ visited toks fuel endPos (pos + 1 + n + 1 + falseCount toks (pos + 1 + n)))
      | some _ => pos :: visited toks fuel endPos (pos + 1)

/-- The positions a full run with every feature disabled visits. -/
def visitedAll (toks : Array PolishToken) : List Nat := visited toks toks.size toks.size 0

/-- Whether a token is an `unnormalizedLagrangeBasis`. -/
def PolishToken.isUlb : PolishToken → Bool
  | .unnormalizedLagrangeBasis _ _ => true
  | _ => false

/-- No `unnormalizedLagrangeBasis` at position `i`. -/
def noUlbAt (toks : Array PolishToken) (i : Nat) : Bool :=
  match toks[i]? with
  | some t => !t.isUlb
  | none => true

/-- `env` with its Lagrange-basis implementation replaced. -/
def Env.withUlb (env : Env m F) (g : Bool → Int → m F) : Env m F :=
  { env with unnormalizedLagrangeBasis := g }

/-- A run with every feature disabled that visits no `unnormalizedLagrangeBasis` does not
depend on the environment's implementation of it. -/
theorem evalLoop_withUlb [Monad m] (env : Env m F) (g : Bool → Int → m F)
    (toks : Array PolishToken) (hdis : ∀ f (t n : Unit → m F), env.ifFeature f t n = n ()) :
    ∀ (fuel endPos : Nat) (s : EvalState F),
      (∀ i ∈ visited toks fuel endPos s.position, noUlbAt toks i = true) →
      evalLoop (env.withUlb g) toks fuel endPos s = evalLoop env toks fuel endPos s := by
  intro fuel
  induction fuel with
  | zero => intro endPos s _; rfl
  | succ fuel ih =>
    intro endPos s hvis
    rw [evalLoop, evalLoop]
    by_cases hge : s.position ≥ endPos
    · simp only [if_pos hge]
    · simp only [if_neg hge]
      simp only [visited, if_neg hge] at hvis
      cases htok : toks[s.position]? with
      | none => rfl
      | some tok =>
        simp only [htok] at hvis
        -- the continuation's obligation, for a next state whose position is known
        have next : ∀ (pos : Nat) (st : EvalState F), st.position = pos →
            (∀ i ∈ visited toks fuel endPos pos, noUlbAt toks i = true) →
            evalLoop (env.withUlb g) toks fuel endPos st = evalLoop env toks fuel endPos st :=
          fun pos st hst h => ih endPos st (hst ▸ h)
        cases tok with
        | unnormalizedLagrangeBasis zk off =>
          have := hvis s.position (List.mem_cons_self ..)
          simp [noUlbAt, htok, PolishToken.isUlb] at this
        | challenge c =>
          cases c with
          | alpha =>
            cases hp : toks[s.position + 1]? with
            | some t =>
              cases t with
              | pow n =>
                simp only [hp] at hvis
                exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
              | _ =>
                simp only [hp] at hvis
                exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
            | none =>
              simp only [hp] at hvis
              exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | _ => exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | dup =>
          cases s.stack.back? with
          | none => exact next _ s.advance rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | some top =>
            exact next _ (push top s.advance) rfl
              (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | add =>
          cases hp : s.pop2 with
          | none => exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | some p =>
            exact next (s.position + 1) _ (by simp [push, advance, pop2_position hp])
              (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | sub =>
          cases hp : s.pop2 with
          | none => exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | some p =>
            exact next (s.position + 1) _ (by simp [push, advance, pop2_position hp])
              (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | mul =>
          cases hp : s.pop2 with
          | none => exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | some p =>
            exact congrArg (env.mul p.1 p.2.1 >>= ·) (funext fun r =>
              next (s.position + 1) (push r p.2.2.advance)
                (by simp [push, advance, pop2_position hp])
                (fun i hi => hvis i (List.mem_cons_of_mem _ hi)))
        | pow n =>
          cases hp : s.pop with
          | none => exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | some p =>
            exact congrArg (env.pow p.1 n >>= ·) (funext fun r =>
              next (s.position + 1) (push r p.2.advance)
                (by simp [push, advance, pop_position hp])
                (fun i hi => hvis i (List.mem_cons_of_mem _ hi)))
        | store =>
          cases hp : s.pop with
          | none => exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | some p =>
            exact next (s.position + 1) _ (by simp [push, advance, pop_position hp])
              (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | load i =>
          dsimp only
          cases s.store[i]? with
          | none => exact next _ s.advance rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | some v =>
            exact next _ (push v s.advance) rfl
              (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | skipIfNot f n =>
          have hdis' : ∀ f (t n : Unit → m F), (env.withUlb g).ifFeature f t n = n () := hdis
          simp only [hdis, hdis']
          have hfalse := ih (s.position + 1 + n + 1 + falseCount toks (s.position + 1 + n))
            { s with position := s.position + 1 + n + 1 }
            (fun i hi => hvis i (List.mem_cons_of_mem _ (List.mem_append_left _ hi)))
          have hcont : ∀ res, evalLoop (env.withUlb g) toks fuel endPos
                (push res { s with
                  position := s.position + 1 + n + 1 + falseCount toks (s.position + 1 + n) })
              = evalLoop env toks fuel endPos
                (push res { s with
                  position := s.position + 1 + n + 1 + falseCount toks (s.position + 1 + n) }) :=
            fun res => next _ _ rfl
              (fun i hi => hvis i (List.mem_cons_of_mem _ (List.mem_append_right _ hi)))
          rw [hfalse]
          exact congrArg (bind _) (funext hcont)
        | _ => exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))

/-- The entry point, for a stream no disabled-features run reads
`unnormalizedLagrangeBasis` in. -/
theorem evaluate_withUlb [Monad m] (env : Env m F) (g : Bool → Int → m F)
    (toks : Array PolishToken) (hdis : ∀ f (t n : Unit → m F), env.ifFeature f t n = n ())
    (hvis : ∀ i ∈ visitedAll toks, noUlbAt toks i = true) :
    evaluate (env.withUlb g) toks = evaluate env toks := by
  simp only [evaluate, evalLoop_withUlb env g toks hdis toks.size toks.size EvalState.init hvis]
  rfl

end Pickles.Linearization
