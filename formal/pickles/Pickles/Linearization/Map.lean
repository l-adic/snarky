import Pickles.Linearization.Interpreter

/-!
# Transporting a run along a carrier map

The reflection route computes the linearization once over a polynomial algebra and reads
the answer back at the field through an evaluation homomorphism. For that to work the
interpreter has to COMMUTE with the homomorphism: running over polynomials and then
evaluating must agree with evaluating first and running over the field.

`Env` cannot simply be mapped — its operations take carrier elements as INPUTS, so pushing
`φ : R → S` forward would need a section of `φ`. What holds instead is a relation:
`Compatible φ e₁ e₂` says `φ` intertwines the two environments operation by operation.
`evalLoop_map` then shows the whole machine preserves it, and `evaluate_map` is the
corollary at the entry point.

The induction is on the fuel and never mentions the token array's contents, so it costs
nothing per token — which is what keeps the reflection's expense confined to the one
decidable equality over polynomials.
-/

namespace Pickles.Linearization

variable {R S : Type} (φ : R → S)

/-- Push a carrier map through the machine state: both arrays cell by cell, position
unchanged. -/
private def EvalState.map (s : EvalState R) : EvalState S :=
  ⟨s.stack.map φ, s.store.map φ, s.position⟩

/-- `φ` intertwines two environments: every operation, and every constant, agrees across
it. The branch clause is conditional rather than pointwise — `ifFeature` receives thunks,
so what is required is that related branches give related results. -/
structure Compatible (e₁ : Env Id R) (e₂ : Env Id S) : Prop where
  /-- Addition is intertwined. -/
  add : ∀ a b, φ (e₁.add a b) = e₂.add (φ a) (φ b)
  /-- Subtraction is intertwined. -/
  sub : ∀ a b, φ (e₁.sub a b) = e₂.sub (φ a) (φ b)
  /-- Multiplication is intertwined. -/
  mul : ∀ a b, φ (e₁.mul a b) = e₂.mul (φ a) (φ b)
  /-- Exponentiation is intertwined. -/
  pow : ∀ v n, φ (e₁.pow v n) = e₂.pow (φ v) n
  /-- Cell readings agree. -/
  var : ∀ c r, φ (e₁.var c r) = e₂.var c r
  /-- Cell post-processing is intertwined. -/
  cell : ∀ x, φ (e₁.cell x) = e₂.cell (φ x)
  /-- The α-powers agree. -/
  alphaPow : ∀ n, φ (e₁.alphaPow n) = e₂.alphaPow n
  /-- The MDS entries agree. -/
  mds : ∀ r c, φ (e₁.mds r c) = e₂.mds r c
  /-- The endomorphism coefficients agree. -/
  endoCoefficient : φ e₁.endoCoefficient = e₂.endoCoefficient
  /-- Literals agree. -/
  literal : ∀ v, φ (e₁.literal v) = e₂.literal v
  /-- The zero-knowledge vanishing evaluations agree. -/
  vanishes : φ e₁.vanishesOnZeroKnowledgeAndPreviousRows
    = e₂.vanishesOnZeroKnowledgeAndPreviousRows
  /-- The Lagrange bases agree. -/
  ulb : ∀ zk off, φ (e₁.unnormalizedLagrangeBasis zk off)
    = e₂.unnormalizedLagrangeBasis zk off
  /-- The joint combiners agree. -/
  jointCombiner : φ e₁.jointCombiner = e₂.jointCombiner
  /-- The `β` challenges agree. -/
  beta : φ e₁.beta = e₂.beta
  /-- The `γ` challenges agree. -/
  gamma : φ e₁.gamma = e₂.gamma
  /-- The left environment takes the DISABLED branch. -/
  ifFeatureLeft : ∀ (f : FeatureFlag) (t n : Unit → Id R), e₁.ifFeature f t n = n ()
  /-- And so does the right one. Stating this rather than a conditional intertwining
  clause is what makes the `skipIfNot` case a single recursion instead of two: the regime
  is the modelled fragment, where every optional feature is off, which is exactly what
  `Evals.toEnv` fixes. The enabled branches are then never evaluated on either side. -/
  ifFeatureRight : ∀ (f : FeatureFlag) (t n : Unit → Id S), e₂.ifFeature f t n = n ()

variable {φ}

-- Oriented to move `.map φ` INWARD. The reverse orientation reads more naturally but its
-- left-hand side is the higher-order pattern `push (φ v) (s.map φ)`, which neither `rw`
-- nor `simp` fires reliably; inward, every left-hand side is first-order. Each case then
-- closes with `simpa using ih …`, so the hypothesis is normalised the same way.
@[simp] private theorem map_push (v : R) (s : EvalState R) :
    (EvalState.push v s).map φ = EvalState.push (φ v) (s.map φ) := by
  simp [EvalState.push, EvalState.map]

@[simp] private theorem map_advance (s : EvalState R) :
    (EvalState.advance s).map φ = EvalState.advance (s.map φ) := by
  simp [EvalState.advance, EvalState.map]

@[simp] private theorem map_position (s : EvalState R) : (s.map φ).position = s.position := rfl

@[simp] private theorem map_withPos (s : EvalState R) (p : Nat) :
    ({ s with position := p } : EvalState R).map φ
      = ({ s.map φ with position := p } : EvalState S) := by
  simp [EvalState.map]

@[simp] private theorem map_withStore (v : R) (s : EvalState R) :
    ({ s with store := s.store.push v } : EvalState R).map φ
      = ({ s.map φ with store := (s.map φ).store.push (φ v) } : EvalState S) := by
  simp [EvalState.map]

@[simp] private theorem map_back? (s : EvalState R) :
    (s.map φ).stack.back? = s.stack.back?.map φ := by simp [EvalState.map]

@[simp] private theorem map_store_get (s : EvalState R) (i : Nat) :
    (s.map φ).store[i]? = s.store[i]?.map φ := by simp [EvalState.map]

/-- Popping commutes: the mapped state pops the mapped value and the mapped remainder. -/
private theorem map_pop (s : EvalState R) :
    (s.map φ).pop = s.pop.map (fun p => (φ p.1, p.2.map φ)) := by
  cases h : s.stack.back? with
  | none => simp [EvalState.pop, EvalState.map, h]
  | some v => simp [EvalState.pop, EvalState.map, h, Array.map_pop]

/-- Popping two commutes. -/
private theorem map_pop2 (s : EvalState R) :
    (s.map φ).pop2 = s.pop2.map (fun p => (φ p.1, φ p.2.1, p.2.2.map φ)) := by
  simp only [EvalState.pop2, map_pop]
  cases h : s.pop with
  | none => simp [h]
  | some p =>
    cases h2 : p.2.pop with
    | none => simp [h, h2, map_pop]
    | some q => simp [h, h2, map_pop]

/-! ## The machine commutes -/

variable {e₁ : Env Id R} {e₂ : Env Id S}

private theorem map_evalConstant (h : Compatible φ e₁ e₂) (c : ConstantTerm) :
    φ (evalConstant e₁ c) = evalConstant e₂ c := by
  cases c <;> simp [evalConstant, h.endoCoefficient, h.mds, h.literal]

private theorem map_evalChallenge (h : Compatible φ e₁ e₂) (c : ChallengeTerm) :
    φ (evalChallenge e₁ c) = evalChallenge e₂ c := by
  cases c <;> simp [evalChallenge, h.alphaPow, h.beta, h.gamma, h.jointCombiner]

private theorem map_topOrZero (h : Compatible φ e₁ e₂) (s : EvalState R) :
    φ (topOrZero e₁ s) = topOrZero e₂ (s.map φ) := by
  simp only [topOrZero, map_back?]
  cases s.stack.back? <;> simp [h.literal]

/-- **The machine commutes with a compatible carrier map.** Running over `S` from the
mapped state is running over `R` and mapping the result — for every fuel, bound and
starting state.

The induction is on the fuel alone. Each token case is the same three steps: rewrite the
environment operation through `Compatible`, push the map past `push`/`advance`/`pop`, and
apply the hypothesis. The `skipIfNot` case is the only one that recurses twice, and it
discharges both of `ifFeature`'s branch obligations from the same hypothesis. -/
private theorem evalLoop_map (h : Compatible φ e₁ e₂) (toks : Array PolishToken) :
    ∀ (fuel endPos : Nat) (s : EvalState R),
      evalLoop e₂ toks fuel endPos (s.map φ)
        = (evalLoop e₁ toks fuel endPos s).map φ := by
  intro fuel
  induction fuel with
  | zero => intro endPos s; rfl
  | succ fuel ih =>
    intro endPos s
    rw [evalLoop, evalLoop]
    simp only [map_position]
    split
    · rfl
    · cases htok : toks[s.position]? with
      | none => rfl
      | some tok =>
        cases tok with
        | constant c =>
          simpa [← map_evalConstant h] using
            ih endPos (EvalState.push (evalConstant e₁ c) s.advance)
        | challenge c =>
          simpa [← map_evalChallenge h] using
            ih endPos (EvalState.push (evalChallenge e₁ c) s.advance)
        | cell col row =>
          simpa [← h.cell, ← h.var] using
            ih endPos (EvalState.push (e₁.cell (e₁.var col row)) s.advance)
        | vanishesOnZeroKnowledgeAndPreviousRows =>
          simpa [← h.vanishes] using
            ih endPos (EvalState.push e₁.vanishesOnZeroKnowledgeAndPreviousRows s.advance)
        | dup =>
          cases hb : s.stack.back? with
          | none => simpa [hb] using ih endPos s.advance
          | some v => simpa [hb] using ih endPos (EvalState.push v s.advance)
        | add =>
          cases hp : s.pop2 with
          | none => simpa [map_pop2, hp] using ih endPos s.advance
          | some p =>
            simpa [map_pop2, hp, ← h.add] using
              ih endPos (EvalState.push (e₁.add p.1 p.2.1) p.2.2.advance)
        | sub =>
          cases hp : s.pop2 with
          | none => simpa [map_pop2, hp] using ih endPos s.advance
          | some p =>
            simpa [map_pop2, hp, ← h.sub] using
              ih endPos (EvalState.push (e₁.sub p.1 p.2.1) p.2.2.advance)
        | mul =>
          cases hp : s.pop2 with
          | none => simpa [map_pop2, hp] using ih endPos s.advance
          | some p =>
            simpa [map_pop2, hp, ← h.mul] using
              ih endPos (EvalState.push (e₁.mul p.1 p.2.1) p.2.2.advance)
        | pow n =>
          cases hp : s.pop with
          | none => simpa [map_pop, hp] using ih endPos s.advance
          | some p =>
            simpa [map_pop, hp, ← h.pow] using
              ih endPos (EvalState.push (e₁.pow p.1 n) p.2.advance)
        | unnormalizedLagrangeBasis zk off =>
          simpa [← h.ulb] using
            ih endPos (EvalState.push (e₁.unnormalizedLagrangeBasis zk off) s.advance)
        | store =>
          cases hp : s.pop with
          | none => simpa [map_pop, hp] using ih endPos s.advance
          | some p =>
            simpa [map_pop, hp] using ih endPos
              (EvalState.push p.1
                (EvalState.advance { p.2 with store := p.2.store.push p.1 }))
        | load i =>
          cases hb : s.store[i]? with
          | none => simpa [hb] using ih endPos s.advance
          | some v => simpa [hb] using ih endPos (EvalState.push v s.advance)
        | skipIf f n =>
          simpa using ih endPos { s with position := s.position + 1 + n }
        | skipIfNot f n =>
          -- Both branches are runs of the same machine from a repositioned state, so one
          -- lemma discharges both of `ifFeature`'s obligations.
          have key : ∀ (bound pos : Nat),
              φ (topOrZero e₁ (evalLoop e₁ toks fuel bound { s with position := pos }))
                = topOrZero e₂
                    (evalLoop e₂ toks fuel bound { s.map φ with position := pos }) := by
            intro bound pos
            rw [map_topOrZero h, ← ih bound { s with position := pos }]
            simp
          dsimp only
          rw [h.ifFeatureLeft, h.ifFeatureRight]
          simpa [key] using ih endPos
            (EvalState.push
              (topOrZero e₁ (evalLoop e₁ toks fuel
                (s.position + 1 + n + 1 +
                  match toks[s.position + 1 + n]? with
                  | some (.skipIf _ c) => c
                  | _ => 0)
                { s with position := s.position + 1 + n + 1 }))
              { s with position := s.position + 1 + n + 1 +
                  match toks[s.position + 1 + n]? with
                  | some (.skipIf _ c) => c
                  | _ => 0 })

/-- **The entry point commutes.** -/
theorem evaluate_map (h : Compatible φ e₁ e₂) (toks : Array PolishToken) :
    evaluate e₂ toks = φ (evaluate e₁ toks) := by
  simp only [evaluate, Id.run, bind, pure]
  rw [show (EvalState.init : EvalState S) = (EvalState.init : EvalState R).map φ from by
    simp [EvalState.init, EvalState.map]]
  rw [evalLoop_map h toks, ← map_topOrZero h]

end Pickles.Linearization
