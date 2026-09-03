import Pickles.Linearization.Types

/-!
# The linearization stack machine

The interpreter for `PolishToken` programs, ported from
`packages/pickles/src/Pickles/Linearization/Interpreter.purs`, itself OCaml
`plonk_checks.ml`'s expression evaluator.

## Main definitions

* `Env m F`: the operations of the machine at a carrier `F` and a monad `m`. The pure
  reading is `m := Id`; the circuit reading is the same interpreter at `CircuitM`, where
  `mul` and `pow` emit constraints.
* `evalLoop`, `evaluate`: the machine and its entry point.
* `alphaExponents`: the exponents at which a run may read the α-table, a syntactic
  property of the program.
* `visited`: the positions a run visits with every feature disabled.

## Main results

* `evaluate_withAlphaPow`: a run reads the α-table only at `alphaExponents`.
* `evaluate_withUlb`: a run with every feature disabled that visits no
  `unnormalizedLagrangeBasis` does not depend on its implementation.

## Implementation notes

The PureScript has two interpreters, `evaluate` and `evaluateM`, because it cannot cheaply
abstract over the monad. Here there is one, so "the circuit interpreter agrees with the
pure one" is a statement about environments rather than about two control flows. The two
optimisations that distinguish `evaluateM` are relocated: the Alpha+Pow peephole (an
`alpha` followed by `pow n` reads the precomputed `α^n` instead of exponentiating) is part
of the machine, and the `ζⁿ - 1` memo is the circuit environment's own business, which is
why `unnormalizedLagrangeBasis` is monadic.

The deployed interpreter is total by defaulting: a stack underflow, an out-of-range `load`
or a position past the end of the program advances silently, and the answer is the top of
the stack or zero. That is modelled as is, since the object of study is the program that
ships.

`SkipIfNot` re-enters the loop at nested bounds and jumps advance by a count carried in
the token, so the recursion is not structural. The loop takes a fuel budget instead of a
well-founded measure, which would obstruct kernel reduction; `evaluate` supplies
`toks.size`, which suffices because the position strictly increases along every path.
-/

namespace Pickles.Linearization

/-- The machine's operations at a carrier `F` and a monad `m`, unifying the PureScript
`Env a` and `EnvM f n`. Affine operations are pure, since they are free in circuit;
constraint-emitting ones are monadic. -/
structure Env (m : Type → Type) (F : Type) where
  /-- Addition. -/
  add : F → F → F
  /-- Subtraction. -/
  sub : F → F → F
  /-- Multiplication; emits a constraint in circuit. -/
  mul : F → F → m F
  /-- Exponentiation by a literal exponent; emits constraints in circuit. -/
  pow : F → Nat → m F
  /-- The evaluation of a column at a row. -/
  var : Column → CurrOrNext → F
  /-- Post-processing of a cell reading; the identity in the deployed environments. -/
  cell : F → F
  /-- `α^n`; a lookup into a precomputed table in circuit. -/
  alphaPow : Nat → F
  /-- Entry `(row, col)` of the Poseidon MDS matrix. -/
  mds : Nat → Nat → F
  /-- The curve's endomorphism coefficient. -/
  endoCoefficient : F
  /-- A numeric literal. -/
  literal : Nat → F
  /-- The zero-knowledge/previous-rows vanishing evaluation. -/
  vanishesOnZeroKnowledgeAndPreviousRows : F
  /-- The unnormalized Lagrange basis at a signed offset. -/
  unnormalizedLagrangeBasis : Bool → Int → m F
  /-- The lookup joint combiner. -/
  jointCombiner : F
  /-- The permutation challenge `β`. -/
  beta : F
  /-- The permutation challenge `γ`. -/
  gamma : F
  /-- Select between the branches of a feature-flag conditional. The branches are thunks,
  so the branch not taken is never forced. -/
  ifFeature : FeatureFlag → (Unit → m F) → (Unit → m F) → m F

/-- The machine state: an operand stack, an append-only store for shared subexpressions,
and a program counter. -/
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

/-- Pop two values, or `none` on underflow. The first component is the deeper operand, so
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

/-- A challenge's value; `alpha` reads `α^1`. -/
def evalChallenge (env : Env m F) : ChallengeTerm → F
  | .alpha => env.alphaPow 1
  | .beta => env.beta
  | .gamma => env.gamma
  | .jointCombiner => env.jointCombiner

/-- The top of the stack, or zero when it is empty. -/
def topOrZero (env : Env m F) (s : EvalState F) : F :=
  s.stack.back?.getD (env.literal 0)

/-- The length of a disabled branch: the count carried by the `SkipIf` marker at
`trueEnd`, or zero when there is none. -/
def falseCount (toks : Array PolishToken) (trueEnd : Nat) : Nat :=
  match toks[trueEnd]? with
  | some (.skipIf _ c) => c
  | _ => 0

/-- Execute `toks` from `s.position` until `endPos`, within a fuel budget.

In the `skipIfNot` case the marker is followed by `n` tokens of enabled branch, a `skipIf`
marker, then the disabled branch. Both branches run from the same starting state and
contribute only their top-of-stack value, which is pushed onto the original stack; a
branch's own stack and store effects are discarded. -/
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

/-- Run a whole program: the value it leaves on top of the stack, or zero. The fuel budget
is the program length, which suffices because the position strictly increases. -/
def evaluate [Monad m] (env : Env m F) (toks : Array PolishToken) : m F := do
  let s ← evalLoop env toks toks.size toks.size EvalState.init
  pure (topOrZero env s)


/-! ## Where the α-table is read

`alphaPow` is reached only from the Alpha+Pow peephole, at `n` when `alpha` is followed by
`pow n` and at `1` otherwise, so the exponents a run can read are a syntactic property of
the program. A run is insensitive to the table anywhere else, which is what lets a finite
precomputed table discharge every α-obligation of a concrete stream. -/

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

/-- `env` with its α-table replaced by `g`. -/
def Env.withAlphaPow (env : Env m F) (g : Nat → F) : Env m F := { env with alphaPow := g }

/-- Two environments differing only in the α-table, and agreeing on `alphaExponents toks`,
run identically for every fuel, bound and start. -/
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

/-- `evaluate` reads the α-table only at `alphaExponents toks`. -/
theorem evaluate_withAlphaPow [Monad m] (env : Env m F) (g : Nat → F)
    (toks : Array PolishToken) (hg : ∀ n ∈ alphaExponents toks, g n = env.alphaPow n) :
    evaluate (env.withAlphaPow g) toks = evaluate env toks := by
  simp only [evaluate, evalLoop_withAlphaPow env g toks hg]
  rfl


/-! ## Where a disabled-features run goes

With every feature disabled, `skipIfNot` runs its second branch only, so the positions a
run visits are again a property of the program: `visited` walks the array with
`evalLoop`'s control flow and no stack. A token the walk never reaches cannot influence the
result. -/

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

/-- `env` with its Lagrange-basis implementation replaced by `g`. -/
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

/-- `evaluate` with every feature disabled does not depend on the Lagrange-basis
implementation when the run visits no `unnormalizedLagrangeBasis`. -/
theorem evaluate_withUlb [Monad m] (env : Env m F) (g : Bool → Int → m F)
    (toks : Array PolishToken) (hdis : ∀ f (t n : Unit → m F), env.ifFeature f t n = n ())
    (hvis : ∀ i ∈ visitedAll toks, noUlbAt toks i = true) :
    evaluate (env.withUlb g) toks = evaluate env toks := by
  simp only [evaluate, evalLoop_withUlb env g toks hdis toks.size toks.size EvalState.init hvis]
  rfl

end Pickles.Linearization
