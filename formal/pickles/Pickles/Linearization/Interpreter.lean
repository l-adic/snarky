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
* `visitedAll`: the positions a run visits under a feature predicate, a syntactic
  property of the program; `readsWithin`: what a position reads.
* `Env.agreeAt`: two environments read one position of the program alike.

## Main results

* `evaluate_congr`: two environments that agree at every visited position run alike. This
  is what lets a statement about a concrete stream discharge, from the array alone, the
  obligations on parts of the environment the stream never reads.

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

private theorem pop_position {s s' : EvalState F} {v : F} (h : s.pop = some (v, s')) :
    s'.position = s.position := by
  simp only [EvalState.pop] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
  · exact absurd h (by simp)

private theorem pop2_position {s s' : EvalState F} {a b : F} (h : s.pop2 = some (a, b, s')) :
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
private def falseCount (toks : Array PolishToken) (trueEnd : Nat) : Nat :=
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


/-! ## Where a run goes, and what it reads there

`ifFeature` decides each conditional by a feature predicate, so the positions a run visits
are a property of the program and the predicate: `visited` walks the array with
`evalLoop`'s control flow and no stack. A run depends on its environment only at the
visited positions, and only through the operation the token there invokes; `evaluate_congr`
makes that precise. -/

/-- The positions a run under the feature predicate `feat` visits, from `pos` up to
`endPos` within `fuel` steps. Mirrors `evalLoop`. -/
private def visited (toks : Array PolishToken) (feat : FeatureFlag → Bool) :
    Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | fuel + 1, endPos, pos =>
    if pos ≥ endPos then []
    else match (toks[pos]? : Option PolishToken) with
      | none => []
      | some (.challenge .alpha) =>
        match (toks[pos + 1]? : Option PolishToken) with
        | some (.pow _) => pos :: visited toks feat fuel endPos (pos + 2)
        | _ => pos :: visited toks feat fuel endPos (pos + 1)
      | some (.skipIf _ n) => pos :: visited toks feat fuel endPos (pos + 1 + n)
      | some (.skipIfNot f n) =>
        pos :: ((if feat f then visited toks feat fuel (pos + 1 + n) (pos + 1)
            else visited toks feat fuel (pos + 1 + n + 1 + falseCount toks (pos + 1 + n))
              (pos + 1 + n + 1))
          ++ visited toks feat fuel endPos (pos + 1 + n + 1 + falseCount toks (pos + 1 + n)))
      | some _ => pos :: visited toks feat fuel endPos (pos + 1)

/-- The positions a full run under `feat` visits. Irreducible: unifying two statements
about a concrete stream must not evaluate the walk, which would reduce the array's length
by `Nat.rec` and exhaust the recursion depth. -/
@[irreducible] def visitedAll (toks : Array PolishToken) (feat : FeatureFlag → Bool) :
    List Nat :=
  visited toks feat toks.size toks.size 0

/-- The exponent at which position `i` reads the α-table, if it reads it. -/
@[irreducible] def alphaExponentAt (toks : Array PolishToken) (i : Nat) : Option Nat :=
  match (toks[i]? : Option PolishToken) with
  | some (.challenge .alpha) =>
    some (match (toks[i + 1]? : Option PolishToken) with
      | some (.pow n) => n
      | _ => 1)
  | _ => none

/-- Position `i` does not read the Lagrange basis. -/
@[irreducible] def noUlbAt (toks : Array PolishToken) (i : Nat) : Bool :=
  match (toks[i]? : Option PolishToken) with
  | some (.unnormalizedLagrangeBasis _ _) => false
  | _ => true

/-- Position `i` reads the α-table at an exponent at most `bound`, if at all, and does not
read the Lagrange basis. Decidable, so a concrete stream establishes it over
`visitedAll` by computation. The syntactic predicates are irreducible for the reason
`visitedAll` is: they index the array, whose bounds check reduces its length. -/
@[irreducible] def readsWithin (toks : Array PolishToken) (bound i : Nat) : Bool :=
  noUlbAt toks i && (alphaExponentAt toks i).all (· ≤ bound)

theorem readsWithin_noUlb {toks : Array PolishToken} {bound i : Nat}
    (h : readsWithin toks bound i = true) : noUlbAt toks i = true := by
  unfold readsWithin at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem readsWithin_alpha {toks : Array PolishToken} {bound i n : Nat}
    (h : readsWithin toks bound i = true) (hn : alphaExponentAt toks i = some n) : n ≤ bound := by
  unfold readsWithin at h
  have := (Bool.and_eq_true_iff.mp h).2
  simp [hn] at this
  exact this

/-- `env₁` and `env₂` read position `i` of `toks` alike: the operation the token there
invokes gives the same result in both. -/
@[irreducible] def Env.agreeAt (env₁ env₂ : Env m F) (toks : Array PolishToken) (i : Nat) : Prop :=
  match (toks[i]? : Option PolishToken) with
  | some (.constant c) => evalConstant env₁ c = evalConstant env₂ c
  | some (.challenge .alpha) =>
    match (toks[i + 1]? : Option PolishToken) with
    | some (.pow n) => env₁.alphaPow n = env₂.alphaPow n
    | _ => env₁.alphaPow 1 = env₂.alphaPow 1
  | some (.challenge c) => evalChallenge env₁ c = evalChallenge env₂ c
  | some (.cell col row) => env₁.cell (env₁.var col row) = env₂.cell (env₂.var col row)
  | some .vanishesOnZeroKnowledgeAndPreviousRows =>
    env₁.vanishesOnZeroKnowledgeAndPreviousRows = env₂.vanishesOnZeroKnowledgeAndPreviousRows
  | some (.unnormalizedLagrangeBasis zk off) =>
    env₁.unnormalizedLagrangeBasis zk off = env₂.unnormalizedLagrangeBasis zk off
  | some (.pow n) => ∀ v, env₁.pow v n = env₂.pow v n
  | some .add => ∀ a b, env₁.add a b = env₂.add a b
  | some .sub => ∀ a b, env₁.sub a b = env₂.sub a b
  | some .mul => ∀ a b, env₁.mul a b = env₂.mul a b
  | _ => True

/-- Two environments whose conditionals are decided by `feat`, whose zero literals agree,
and which agree at every position the run visits, run alike for every fuel, bound and
start. -/
private theorem evalLoop_congr [Monad m] (env₁ env₂ : Env m F) (toks : Array PolishToken)
    (feat : FeatureFlag → Bool)
    (hif₁ : ∀ f (t n : Unit → m F), env₁.ifFeature f t n = if feat f then t () else n ())
    (hif₂ : ∀ f (t n : Unit → m F), env₂.ifFeature f t n = if feat f then t () else n ())
    (hlit : env₁.literal 0 = env₂.literal 0) :
    ∀ (fuel endPos : Nat) (s : EvalState F),
      (∀ i ∈ visited toks feat fuel endPos s.position, env₁.agreeAt env₂ toks i) →
      evalLoop env₁ toks fuel endPos s = evalLoop env₂ toks fuel endPos s := by
  have htop : ∀ s : EvalState F, topOrZero env₁ s = topOrZero env₂ s := by
    intro s; simp [topOrZero, hlit]
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
        have next : ∀ (pos : Nat) (st : EvalState F), st.position = pos →
            (∀ i ∈ visited toks feat fuel endPos pos, env₁.agreeAt env₂ toks i) →
            evalLoop env₁ toks fuel endPos st = evalLoop env₂ toks fuel endPos st :=
          fun pos st hst h => ih endPos st (hst ▸ h)
        cases tok with
        | constant c =>
          dsimp only at hvis ⊢
          have hs := hvis s.position (List.mem_cons_self ..)
          simp only [Env.agreeAt, htok] at hs
          rw [hs]; exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | challenge c =>
          dsimp only at hvis ⊢
          cases c with
          | alpha =>
            dsimp only at hvis ⊢
            cases hp : toks[s.position + 1]? with
            | some t =>
              cases t with
              | pow n =>
                simp only [hp] at hvis ⊢
                have hs := hvis s.position (List.mem_cons_self ..)
                simp only [Env.agreeAt, htok, hp] at hs
                rw [hs]; exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
              | _ =>
                simp only [hp] at hvis ⊢
                have hs := hvis s.position (List.mem_cons_self ..)
                simp only [Env.agreeAt, htok, hp] at hs
                rw [hs]; exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
            | none =>
              simp only [hp] at hvis ⊢
              have hs := hvis s.position (List.mem_cons_self ..)
              simp only [Env.agreeAt, htok, hp] at hs
              rw [hs]; exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | _ =>
            dsimp only at hvis ⊢
            have hs := hvis s.position (List.mem_cons_self ..)
            simp only [Env.agreeAt, htok] at hs
            rw [hs]; exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | cell col row =>
          dsimp only at hvis ⊢
          have hs := hvis s.position (List.mem_cons_self ..)
          simp only [Env.agreeAt, htok] at hs
          rw [hs]; exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | vanishesOnZeroKnowledgeAndPreviousRows =>
          dsimp only at hvis ⊢
          have hs := hvis s.position (List.mem_cons_self ..)
          simp only [Env.agreeAt, htok] at hs
          rw [hs]; exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | unnormalizedLagrangeBasis zk off =>
          dsimp only at hvis ⊢
          have hs := hvis s.position (List.mem_cons_self ..)
          simp only [Env.agreeAt, htok] at hs
          rw [hs]
          exact congrArg (env₂.unnormalizedLagrangeBasis zk off >>= ·) (funext fun r =>
            next _ (push r s.advance) rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi)))
        | dup =>
          dsimp only at hvis ⊢
          cases s.stack.back? with
          | none => exact next _ s.advance rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | some top =>
            exact next _ (push top s.advance) rfl
              (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | add =>
          dsimp only at hvis ⊢
          have hs := hvis s.position (List.mem_cons_self ..)
          simp only [Env.agreeAt, htok] at hs
          cases hp : s.pop2 with
          | none => exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | some p =>
            obtain ⟨a, b, s'⟩ := p
            dsimp only
            rw [hs]
            exact next (s.position + 1) _ (by simp [push, advance, pop2_position hp])
              (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | sub =>
          dsimp only at hvis ⊢
          have hs := hvis s.position (List.mem_cons_self ..)
          simp only [Env.agreeAt, htok] at hs
          cases hp : s.pop2 with
          | none => exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | some p =>
            obtain ⟨a, b, s'⟩ := p
            dsimp only
            rw [hs]
            exact next (s.position + 1) _ (by simp [push, advance, pop2_position hp])
              (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | mul =>
          dsimp only at hvis ⊢
          have hs := hvis s.position (List.mem_cons_self ..)
          simp only [Env.agreeAt, htok] at hs
          cases hp : s.pop2 with
          | none => exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | some p =>
            obtain ⟨a, b, s'⟩ := p
            dsimp only
            rw [hs]
            exact congrArg (env₂.mul a b >>= ·) (funext fun r =>
              next (s.position + 1) (push r s'.advance)
                (by simp [push, advance, pop2_position hp])
                (fun i hi => hvis i (List.mem_cons_of_mem _ hi)))
        | pow n =>
          dsimp only at hvis ⊢
          have hs := hvis s.position (List.mem_cons_self ..)
          simp only [Env.agreeAt, htok] at hs
          cases hp : s.pop with
          | none => exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | some p =>
            obtain ⟨v, s'⟩ := p
            dsimp only
            rw [hs]
            exact congrArg (env₂.pow v n >>= ·) (funext fun r =>
              next (s.position + 1) (push r s'.advance)
                (by simp [push, advance, pop_position hp])
                (fun i hi => hvis i (List.mem_cons_of_mem _ hi)))
        | store =>
          dsimp only at hvis ⊢
          cases hp : s.pop with
          | none => exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | some p =>
            exact next (s.position + 1) _ (by simp [push, advance, pop_position hp])
              (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | load i =>
          dsimp only at hvis ⊢
          cases s.store[i]? with
          | none => exact next _ s.advance rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
          | some v =>
            exact next _ (push v s.advance) rfl
              (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | skipIf f n =>
          dsimp only at hvis ⊢
          exact next _ _ rfl (fun i hi => hvis i (List.mem_cons_of_mem _ hi))
        | skipIfNot f n =>
          dsimp only at hvis ⊢
          simp only [hif₁, hif₂]
          have hcont : ∀ res, evalLoop env₁ toks fuel endPos
                (push res { s with
                  position := s.position + 1 + n + 1 + falseCount toks (s.position + 1 + n) })
              = evalLoop env₂ toks fuel endPos
                (push res { s with
                  position := s.position + 1 + n + 1 + falseCount toks (s.position + 1 + n) }) :=
            fun res => next _ _ rfl
              (fun i hi => hvis i (List.mem_cons_of_mem _ (List.mem_append_right _ hi)))
          by_cases hf : feat f
          · simp only [if_pos hf] at hvis ⊢
            have hbr := ih (s.position + 1 + n) { s with position := s.position + 1 }
              (fun i hi => hvis i (List.mem_cons_of_mem _ (List.mem_append_left _ hi)))
            rw [hbr]
            simp only [htop]
            exact congrArg (bind _) (funext hcont)
          · simp only [if_neg hf] at hvis ⊢
            have hbr := ih (s.position + 1 + n + 1 + falseCount toks (s.position + 1 + n))
              { s with position := s.position + 1 + n + 1 }
              (fun i hi => hvis i (List.mem_cons_of_mem _ (List.mem_append_left _ hi)))
            rw [hbr]
            simp only [htop]
            exact congrArg (bind _) (funext hcont)

/-- Two environments whose conditionals are decided by `feat`, whose zero literals agree,
and which agree at every position a full run visits, evaluate alike. -/
theorem evaluate_congr [Monad m] (env₁ env₂ : Env m F) (toks : Array PolishToken)
    (feat : FeatureFlag → Bool) (hvis : ∀ i ∈ visitedAll toks feat, env₁.agreeAt env₂ toks i)
    (hif₁ : ∀ f (t n : Unit → m F), env₁.ifFeature f t n = if feat f then t () else n ())
    (hif₂ : ∀ f (t n : Unit → m F), env₂.ifFeature f t n = if feat f then t () else n ())
    (hlit : env₁.literal 0 = env₂.literal 0) :
    evaluate env₁ toks = evaluate env₂ toks := by
  unfold visitedAll at hvis
  simp only [evaluate,
    evalLoop_congr env₁ env₂ toks feat hif₁ hif₂ hlit toks.size toks.size EvalState.init hvis]
  simp [topOrZero, hlit]

end Pickles.Linearization
