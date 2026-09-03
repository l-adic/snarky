import Pickles.Linearization.Spec

/-!
# Transporting a run along an algebra homomorphism

The reflection route computes the linearization once over a polynomial algebra and reads
the answer back at the field through an evaluation homomorphism. For that to work the
interpreter has to commute with the homomorphism: running over polynomials and then
evaluating must agree with evaluating first and running over the field.

`evaluate_map` is that statement for `Evals.toEnv`: for an `F`-algebra homomorphism
`φ : R →ₐ[F] S`, the run over `S` at the transported inputs is `φ` of the run over `R`.
Every operation of `toEnv` is a ring operation or an `algebraMap`, so each case of the
induction is one of `map_add`, `map_mul`, `map_pow` or `φ.commutes`. The induction is on
the fuel and never mentions the token array's contents.
-/

namespace Pickles.Linearization

open Kimchi.Protocol.Linearization

variable {R S : Type} {φ : R → S}

/-! ## `EvalState.map` -/

-- Oriented to move `.map φ` inward, so every left-hand side is first-order.
@[simp] private theorem map_push (v : R) (s : EvalState R) :
    (EvalState.push v s).map φ = EvalState.push (φ v) (s.map φ) := by
  simp [EvalState.push, EvalState.map]

@[simp] private theorem map_advance (s : EvalState R) :
    (EvalState.advance s).map φ = EvalState.advance (s.map φ) := by
  simp [EvalState.advance, EvalState.map]

@[simp] theorem map_position (s : EvalState R) : (s.map φ).position = s.position := rfl

@[simp] private theorem map_withPos (s : EvalState R) (p : Nat) :
    ({ s with position := p } : EvalState R).map φ
      = ({ s.map φ with position := p } : EvalState S) := by
  simp [EvalState.map]

@[simp] private theorem map_withStore (v : R) (s : EvalState R) :
    ({ s with store := s.store.push v } : EvalState R).map φ
      = ({ s.map φ with store := (s.map φ).store.push (φ v) } : EvalState S) := by
  simp [EvalState.map]

@[simp] theorem map_back? (s : EvalState R) :
    (s.map φ).stack.back? = s.stack.back?.map φ := by simp [EvalState.map]

@[simp] private theorem map_store_get (s : EvalState R) (i : Nat) :
    (s.map φ).store[i]? = s.store[i]?.map φ := by simp [EvalState.map]

theorem map_pop (s : EvalState R) :
    (s.map φ).pop = s.pop.map (fun p => (φ p.1, p.2.map φ)) := by
  cases h : s.stack.back? with
  | none => simp [EvalState.pop, EvalState.map, h]
  | some v => simp [EvalState.pop, EvalState.map, h, Array.map_pop]

theorem map_pop2 (s : EvalState R) :
    (s.map φ).pop2 = s.pop2.map (fun p => (φ p.1, φ p.2.1, p.2.2.map φ)) := by
  simp only [EvalState.pop2, map_pop]
  cases s.pop with
  | none => simp
  | some p =>
    cases h2 : p.2.pop with
    | none => simp [h2, map_pop]
    | some q => simp [h2, map_pop]

/-! ## The machine commutes -/

variable {F : Type} [Field F] [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
  (φ : R →ₐ[F] S) (endo : F) (mds : Kimchi.Gate.Poseidon.Mds F) (α β γ jc van : R)
  (ulb : Bool → Int → R) (lk : LookupEvals R) (feat : FeatureFlag → Bool) (e : Evals R)

private theorem toEnv_var (c : Column) (r : CurrOrNext) :
    φ ((e.toEnv endo mds α β γ jc van ulb lk feat).var c r)
      = ((e.map φ).toEnv endo mds (φ α) (φ β) (φ γ) (φ jc) (φ van)
          (fun zk off => φ (ulb zk off)) (lk.map φ) feat).var c r := by
  cases c with
  | index g => cases g <;> cases r <;> simp [Evals.toEnv, Evals.map]
  | witness i => cases r <;> simp [Evals.toEnv, Evals.map, apply_dite (f := φ), map_zero]
  | coefficient i =>
    cases r <;> simp [Evals.toEnv, Evals.map, apply_dite (f := φ), map_zero]
  | _ => cases r <;> simp [Evals.toEnv, LookupEvals.map]

private theorem toEnv_mds (r c : Nat) :
    φ ((e.toEnv endo mds α β γ jc van ulb lk feat).mds r c)
      = ((e.map φ).toEnv endo mds (φ α) (φ β) (φ γ) (φ jc) (φ van)
          (fun zk off => φ (ulb zk off)) (lk.map φ) feat).mds r c := by
  match r, c with
  | 0, 0 | 0, 1 | 0, 2 | 1, 0 | 1, 1 | 1, 2 | 2, 0 | 2, 1 | 2, 2 => exact φ.commutes _
  | _ + 3, _ | _, _ + 3 => simp [Evals.toEnv]

private theorem toEnv_constant (t : ConstantTerm) :
    φ (evalConstant (e.toEnv endo mds α β γ jc van ulb lk feat) t)
      = evalConstant ((e.map φ).toEnv endo mds (φ α) (φ β) (φ γ) (φ jc) (φ van)
          (fun zk off => φ (ulb zk off)) (lk.map φ) feat) t := by
  cases t with
  | mds r c => exact toEnv_mds φ endo mds α β γ jc van ulb lk feat e r c
  | _ => simp [evalConstant, φ.commutes]

private theorem toEnv_challenge (t : ChallengeTerm) :
    φ (evalChallenge (e.toEnv endo mds α β γ jc van ulb lk feat) t)
      = evalChallenge ((e.map φ).toEnv endo mds (φ α) (φ β) (φ γ) (φ jc) (φ van)
          (fun zk off => φ (ulb zk off)) (lk.map φ) feat) t := by
  cases t <;> simp [evalChallenge]

private theorem toEnv_topOrZero (s : EvalState R) :
    φ (topOrZero (e.toEnv endo mds α β γ jc van ulb lk feat) s)
      = topOrZero ((e.map φ).toEnv endo mds (φ α) (φ β) (φ γ) (φ jc) (φ van)
          (fun zk off => φ (ulb zk off)) (lk.map φ) feat) (s.map φ) := by
  simp only [topOrZero, map_back?]
  cases s.stack.back? <;> simp

/-- The machine commutes with an algebra homomorphism: running over `S` from the mapped
state is running over `R` and mapping the result, for every fuel, bound and start. -/
private theorem evalLoop_map (toks : Array PolishToken) :
    ∀ (fuel endPos : Nat) (s : EvalState R),
      evalLoop ((e.map φ).toEnv endo mds (φ α) (φ β) (φ γ) (φ jc) (φ van)
          (fun zk off => φ (ulb zk off)) (lk.map φ) feat) toks fuel endPos (s.map φ)
        = (evalLoop (e.toEnv endo mds α β γ jc van ulb lk feat) toks fuel endPos s).map φ := by
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
          simpa [← toEnv_constant] using
            ih endPos (EvalState.push (evalConstant _ c) s.advance)
        | challenge c =>
          cases c with
          | alpha =>
            cases hp : toks[s.position + 1]? with
            | some t =>
              cases t with
              | pow n =>
                simpa [hp] using
                  ih endPos (EvalState.push (α ^ n) { s with position := s.position + 2 })
              | _ =>
                simpa [hp] using ih endPos (EvalState.push α s.advance)
            | none =>
              simpa [hp] using ih endPos (EvalState.push α s.advance)
          | _ =>
            simpa [← toEnv_challenge] using
              ih endPos (EvalState.push (evalChallenge _ _) s.advance)
        | cell col row =>
          simpa [← toEnv_var] using
            ih endPos (EvalState.push ((e.toEnv endo mds α β γ jc van ulb lk feat).var col row)
              s.advance)
        | vanishesOnZeroKnowledgeAndPreviousRows =>
          simpa using ih endPos (EvalState.push van s.advance)
        | dup =>
          cases hb : s.stack.back? with
          | none => simpa [hb] using ih endPos s.advance
          | some v => simpa [hb] using ih endPos (EvalState.push v s.advance)
        | add =>
          cases hp : s.pop2 with
          | none => simpa [map_pop2, hp] using ih endPos s.advance
          | some p =>
            simpa [map_pop2, hp] using
              ih endPos (EvalState.push (p.1 + p.2.1) p.2.2.advance)
        | sub =>
          cases hp : s.pop2 with
          | none => simpa [map_pop2, hp] using ih endPos s.advance
          | some p =>
            simpa [map_pop2, hp] using
              ih endPos (EvalState.push (p.1 - p.2.1) p.2.2.advance)
        | mul =>
          cases hp : s.pop2 with
          | none => simpa [map_pop2, hp] using ih endPos s.advance
          | some p =>
            simpa [map_pop2, hp] using
              ih endPos (EvalState.push (p.1 * p.2.1) p.2.2.advance)
        | pow n =>
          cases hp : s.pop with
          | none => simpa [map_pop, hp] using ih endPos s.advance
          | some p =>
            simpa [map_pop, hp] using
              ih endPos (EvalState.push (p.1 ^ n) p.2.advance)
        | unnormalizedLagrangeBasis zk off =>
          simpa using ih endPos (EvalState.push (ulb zk off) s.advance)
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
          -- lemma serves both; the conditional is `if feat f` on either side.
          have key : ∀ (bound pos : Nat),
              φ (topOrZero (e.toEnv endo mds α β γ jc van ulb lk feat)
                  (evalLoop (e.toEnv endo mds α β γ jc van ulb lk feat) toks fuel bound
                    { s with position := pos }))
                = topOrZero ((e.map φ).toEnv endo mds (φ α) (φ β) (φ γ) (φ jc) (φ van)
                      (fun zk off => φ (ulb zk off)) (lk.map φ) feat)
                    (evalLoop ((e.map φ).toEnv endo mds (φ α) (φ β) (φ γ) (φ jc) (φ van)
                      (fun zk off => φ (ulb zk off)) (lk.map φ) feat) toks fuel bound
                      { s.map φ with position := pos }) := by
            intro bound pos
            rw [toEnv_topOrZero, ← ih bound { s with position := pos }]
            simp
          simp only [Evals.toEnv_ifFeature, bind, pure]
          by_cases hf : feat f
          · simp only [if_pos hf]
            rw [← key (s.position + 1 + n) (s.position + 1)]
            simpa using ih endPos
              (EvalState.push (topOrZero (e.toEnv endo mds α β γ jc van ulb lk feat)
                (evalLoop (e.toEnv endo mds α β γ jc van ulb lk feat) toks fuel
                  (s.position + 1 + n) { s with position := s.position + 1 }))
                { s with position := s.position + 1 + n + 1 +
                    match toks[s.position + 1 + n]? with
                    | some (.skipIf _ c) => c
                    | _ => 0 })
          · simp only [if_neg hf]
            rw [← key]
            simpa using ih endPos
              (EvalState.push (topOrZero (e.toEnv endo mds α β γ jc van ulb lk feat)
                (evalLoop (e.toEnv endo mds α β γ jc van ulb lk feat) toks fuel
                  (s.position + 1 + n + 1 +
                    match toks[s.position + 1 + n]? with
                    | some (.skipIf _ c) => c
                    | _ => 0)
                  { s with position := s.position + 1 + n + 1 }))
                { s with position := s.position + 1 + n + 1 +
                    match toks[s.position + 1 + n]? with
                    | some (.skipIf _ c) => c
                    | _ => 0 })

/-- Running `toEnv` over `S` at the transported inputs is `φ` of the run over `R`. -/
theorem evaluate_map (toks : Array PolishToken) :
    evaluate ((e.map φ).toEnv endo mds (φ α) (φ β) (φ γ) (φ jc) (φ van)
        (fun zk off => φ (ulb zk off)) (lk.map φ) feat) toks
      = φ (evaluate (e.toEnv endo mds α β γ jc van ulb lk feat) toks) := by
  simp only [evaluate, bind, pure]
  rw [show (EvalState.init : EvalState S) = (EvalState.init : EvalState R).map φ from by
    simp [EvalState.init, EvalState.map]]
  rw [evalLoop_map φ endo mds α β γ jc van ulb lk feat e toks, ← toEnv_topOrZero]

end Pickles.Linearization
