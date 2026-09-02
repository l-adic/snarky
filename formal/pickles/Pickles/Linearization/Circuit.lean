import Pickles.Linearization.Map
import Snarky.DSL.Field
import Pickles.Linearization.Spec

set_option mvcgen.warning false

/-!
# The interpreter in circuit

`Pickles.Linearization.evaluate` is generic in its monad, so the in-circuit reading of a
token stream is not a second interpreter — it is the same one at `CircuitM`, where `mul`
and `pow` emit constraints instead of returning values. What has to be proved is that the
constraints it emits PIN the result: every satisfying valuation reads the circuit's output
as the value the pure interpreter computes.

That is the relational half of the house pattern (`Snarky.mul_spec` and its siblings),
and it is the statement the pickles verifier needs. Composed with
`Pickles.Reflect.evaluate_fpTokens`, which identifies the pure reading with
`Kimchi.Protocol.Linearization.gateLinearization`, it says the circuit computes the gate
contribution to `ftEval0` — the wire protocol's own quantity, not a restatement of it.

It is RELATIVE faithfulness throughout: that the circuit computes what the wire verifier
computes. Whether the wire verifier is sound is a different question and out of scope.

## Why a second relation

`Compatible` relates two environments by a carrier map, and will not serve here: the pure
environment's `mul` is a function while the circuit's is monadic, so there is no map to
push through it. `CircuitCompatible` is its sibling — plain equations on the affine
operations, which are free in circuit and return values directly, and weakest-precondition
triples on the constraint-emitting ones.
-/

namespace Pickles.Linearization

open Std.Do Snarky
open scoped Kimchi

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]

/-- A circuit environment computes a pure one, under a valuation. The affine fields agree
on the nose; the constraint-emitting fields agree in the sense that any satisfying
valuation reads their result correctly. -/
structure CircuitCompatible (V : Valuation F)
    (ce : Env (CircuitM F (Builder V c)) (FVar F)) (pe : Env Id F) : Prop where
  /-- Addition agrees; it is affine, so no constraint is emitted. -/
  add : ∀ x y, (ce.add x y).val V = pe.add (x.val V) (y.val V)
  /-- Subtraction agrees. -/
  sub : ∀ x y, (ce.sub x y).val V = pe.sub (x.val V) (y.val V)
  /-- Multiplication is pinned by the constraints it emits. -/
  mul : ∀ x y, ⦃⌜True⌝⦄ ce.mul x y ⦃⇓ a _ => ⌜a.val V = pe.mul (x.val V) (y.val V)⌝⦄
  /-- Exponentiation is pinned by the constraints it emits. -/
  pow : ∀ x n, ⦃⌜True⌝⦄ ce.pow x n ⦃⇓ a _ => ⌜a.val V = pe.pow (x.val V) n⌝⦄
  /-- Cell readings agree. -/
  var : ∀ col row, (ce.var col row).val V = pe.var col row
  /-- Cell post-processing agrees. -/
  cell : ∀ x, (ce.cell x).val V = pe.cell (x.val V)
  /-- The α-powers agree — a table lookup in circuit, so affine. -/
  alphaPow : ∀ n, (ce.alphaPow n).val V = pe.alphaPow n
  /-- The MDS entries agree. -/
  mds : ∀ r c, (ce.mds r c).val V = pe.mds r c
  /-- The endomorphism coefficients agree. -/
  endoCoefficient : ce.endoCoefficient.val V = pe.endoCoefficient
  /-- Literals agree. -/
  literal : ∀ v, (ce.literal v).val V = pe.literal v
  /-- The zero-knowledge vanishing evaluations agree. -/
  vanishes : ce.vanishesOnZeroKnowledgeAndPreviousRows.val V
    = pe.vanishesOnZeroKnowledgeAndPreviousRows
  /-- The Lagrange bases agree, up to the constraints emitted. -/
  ulb : ∀ zk off, ⦃⌜True⌝⦄ ce.unnormalizedLagrangeBasis zk off
    ⦃⇓ a _ => ⌜a.val V = pe.unnormalizedLagrangeBasis zk off⌝⦄
  /-- The joint combiners agree. -/
  jointCombiner : ce.jointCombiner.val V = pe.jointCombiner
  /-- The `β` challenges agree. -/
  beta : ce.beta.val V = pe.beta
  /-- The `γ` challenges agree. -/
  gamma : ce.gamma.val V = pe.gamma
  /-- Related branches select related results. Conditional rather than pinned to the
  disabled branch, so the enabled case stays stateable — the feature predicate is a
  parameter of both environments. -/
  ifFeature : ∀ (f : FeatureFlag) (t₁ n₁ : CircuitM F (Builder V c) (FVar F)) (t₂ n₂ : F),
    ⦃⌜True⌝⦄ t₁ ⦃⇓ a _ => ⌜a.val V = t₂⌝⦄ → ⦃⌜True⌝⦄ n₁ ⦃⇓ a _ => ⌜a.val V = n₂⌝⦄ →
      ⦃⌜True⌝⦄ ce.ifFeature f (fun _ => t₁) (fun _ => n₁)
        ⦃⇓ a _ => ⌜a.val V = pe.ifFeature f (fun _ => t₂) (fun _ => n₂)⌝⦄

/-! ## The machine is pinned -/

variable [LawfulBasicSystem F c] {V : Valuation F}
  {ce : Env (CircuitM F (Builder V c)) (FVar F)} {pe : Env Id F}

/-- Constants read the same on both sides. -/
private theorem circ_evalConstant (h : CircuitCompatible V ce pe) (t : ConstantTerm) :
    (evalConstant ce t).val V = evalConstant pe t := by
  cases t <;> simp [evalConstant, h.endoCoefficient, h.mds, h.literal]

/-- Challenges read the same on both sides. -/
private theorem circ_evalChallenge (h : CircuitCompatible V ce pe) (t : ChallengeTerm) :
    (evalChallenge ce t).val V = evalChallenge pe t := by
  cases t <;> simp [evalChallenge, h.alphaPow, h.beta, h.gamma, h.jointCombiner]

/-- The answer read off a finished state agrees on both sides. -/
private theorem circ_topOrZero (h : CircuitCompatible V ce pe) (s : EvalState (FVar F)) :
    (topOrZero ce s).val V = topOrZero pe (s.map (·.val V)) := by
  simp only [topOrZero, map_back?]
  cases s.stack.back? <;> simp [h.literal]

/-- Reading a state cell by cell under the valuation. -/
private abbrev rd (s : EvalState (FVar F)) : EvalState F := s.map (·.val V)

/-- **The machine is pinned by the constraints it emits.** Any satisfying valuation reads
the circuit run's final state as the pure run's, from the read of the same start.

The induction is on the fuel and never inspects the token array. Each affine case rewrites
with the corresponding `CircuitCompatible` equation and applies the hypothesis; each
constraint-emitting case discharges through the corresponding triple. -/
private theorem evalLoop_spec (h : CircuitCompatible V ce pe)
    (hdc : ∀ f (t n : Unit → CircuitM F (Builder V c) (FVar F)), ce.ifFeature f t n = n ())
    (hdp : ∀ f (t n : Unit → Id F), pe.ifFeature f t n = n ())
    (toks : Array PolishToken) :
    ∀ (fuel endPos : Nat) (cs : EvalState (FVar F)),
      ⦃⌜True⌝⦄
      evalLoop ce toks fuel endPos cs
      ⦃⇓ s _ => ⌜rd (V := V) s = evalLoop pe toks fuel endPos (rd (V := V) cs)⌝⦄ := by
  intro fuel
  induction fuel with
  | zero => intro endPos cs; simp only [evalLoop]; mvcgen
  | succ fuel ih =>
    intro endPos cs
    rw [evalLoop, evalLoop]
    simp only [map_position]
    split
    · mvcgen
    · cases htok : toks[cs.position]? with
      | none => mvcgen
      | some tok =>
        cases tok with
        | constant t =>
          simpa [circ_evalConstant h] using
            ih endPos (EvalState.push (evalConstant ce t) cs.advance)
        | challenge t =>
          cases t with
          | alpha =>
            cases hp : toks[cs.position + 1]? with
            | some u =>
              cases u with
              | pow n =>
                simpa [hp, h.alphaPow] using
                  ih endPos (EvalState.push (ce.alphaPow n)
                    { cs with position := cs.position + 2 })
              | _ =>
                simpa [hp, h.alphaPow] using
                  ih endPos (EvalState.push (ce.alphaPow 1) cs.advance)
            | none =>
              simpa [hp, h.alphaPow] using
                ih endPos (EvalState.push (ce.alphaPow 1) cs.advance)
          | _ =>
            simpa [circ_evalChallenge h] using
              ih endPos (EvalState.push (evalChallenge ce _) cs.advance)
        | cell col row =>
          simpa [h.cell, h.var] using
            ih endPos (EvalState.push (ce.cell (ce.var col row)) cs.advance)
        | vanishesOnZeroKnowledgeAndPreviousRows =>
          simpa [h.vanishes] using
            ih endPos (EvalState.push ce.vanishesOnZeroKnowledgeAndPreviousRows cs.advance)
        | dup =>
          cases hb : cs.stack.back? with
          | none => simpa [hb] using ih endPos cs.advance
          | some v => simpa [hb] using ih endPos (EvalState.push v cs.advance)
        | add =>
          cases hp : cs.pop2 with
          | none => simpa [map_pop2, hp] using ih endPos cs.advance
          | some p =>
            simpa [map_pop2, hp, h.add] using
              ih endPos (EvalState.push (ce.add p.1 p.2.1) p.2.2.advance)
        | sub =>
          cases hp : cs.pop2 with
          | none => simpa [map_pop2, hp] using ih endPos cs.advance
          | some p =>
            simpa [map_pop2, hp, h.sub] using
              ih endPos (EvalState.push (ce.sub p.1 p.2.1) p.2.2.advance)
        | load i =>
          cases hb : cs.store[i]? with
          | none => simpa [hb] using ih endPos cs.advance
          | some v => simpa [hb] using ih endPos (EvalState.push v cs.advance)
        | store =>
          cases hp : cs.pop with
          | none => simpa [map_pop, hp] using ih endPos cs.advance
          | some p =>
            simpa [map_pop, hp] using ih endPos
              (EvalState.push p.1
                (EvalState.advance { p.2 with store := p.2.store.push p.1 }))
        | skipIf f n =>
          simpa using ih endPos { cs with position := cs.position + 1 + n }
        | mul =>
          cases hp : cs.pop2 with
          | none => simpa [map_pop2, hp] using ih endPos cs.advance
          | some p =>
            simp only [map_pop2, hp, Option.map_some]
            have hmul := h.mul
            mvcgen [hmul, ih]
            all_goals (intro hh; simp_all; try rfl)
        | pow n =>
          cases hp : cs.pop with
          | none => simpa [map_pop, hp] using ih endPos cs.advance
          | some p =>
            simp only [map_pop, hp, Option.map_some]
            have hpow := h.pow
            mvcgen [hpow, ih]
            all_goals (intro hh; simp_all; try rfl)
        | unnormalizedLagrangeBasis zk off =>
          have hulb := h.ulb
          mvcgen [hulb, ih]
          all_goals (intro hh; simp_all; try rfl)
        | skipIfNot f n =>
          -- `hdc`/`hdp` pin both environments to the disabled branch, so only one
          -- recursion is entered. `CircuitCompatible.ifFeature` itself stays conditional:
          -- the SPECIALISATION lives in this theorem's statement, where it is visible,
          -- rather than in the relation, where it would make the enabled case unstateable.
          have key : ∀ (bound pos : Nat),
              ⦃⌜True⌝⦄
              (do let s₁ ← evalLoop ce toks fuel bound { cs with position := pos }
                  pure (topOrZero ce s₁))
              ⦃⇓ a _ => ⌜a.val V
                = topOrZero pe (evalLoop pe toks fuel bound
                    { rd (V := V) cs with position := pos })⌝⦄ := by
            intro bound pos
            mvcgen [ih]
            rename_i hh
            rw [circ_topOrZero h]
            simp only [rd] at hh
            rw [hh]
            simp [rd, EvalState.map]
          dsimp only
          rw [hdc, hdp]
          mvcgen [key, ih]
          all_goals (intro hh; simp_all [circ_topOrZero h]; try rfl)

open Std.Do in
/-- **The entry point is pinned.** Any satisfying valuation reads the circuit's answer as
the pure interpreter's. Registered as a `@[spec]` so consumers compose it with `mvcgen`,
matching `Snarky.mul_spec` and its siblings. -/
@[spec] theorem evaluate_spec (h : CircuitCompatible V ce pe)
    (hdc : ∀ f (t n : Unit → CircuitM F (Builder V c) (FVar F)), ce.ifFeature f t n = n ())
    (hdp : ∀ f (t n : Unit → Id F), pe.ifFeature f t n = n ())
    (toks : Array PolishToken) :
    ⦃⌜True⌝⦄
    evaluate ce toks
    ⦃⇓ a _ => ⌜a.val V = evaluate pe toks⌝⦄ := by
  simp only [evaluate]
  have hloop := evalLoop_spec h hdc hdp toks
  mvcgen [hloop]
  rename_i hh
  rw [circ_topOrZero h]
  simp only [rd] at hh
  rw [hh]
  simp only [evaluate, EvalState.init, EvalState.map, Array.map_empty]
  rfl

/-! ## A concrete environment

Everything above quantifies over an environment satisfying `CircuitCompatible`; this
exhibits one. The circuit's inputs are variables already allocated by the caller — the
proof's evaluations and challenges — together with the PRECOMPUTED table of α-powers.

That table is the reason `alphaPow` sits on the affine side of `CircuitCompatible`: in
circuit it is a lookup, costing nothing, where computing `α^n` per occurrence would emit
rows at each of the stream's 124 α-sites. It has to be built before the interpreter runs
and handed in, exactly as `precomputeAlphaPowers` does in the PureScript. -/

/-- All lookup columns as the circuit constant zero — the modelled fragment's
instantiation. `LookupEvals.zero` will not serve: `FVar` has no `Zero` instance, the
circuit's zero being the constant expression rather than a field element. -/
def lookupZero [Zero F] : Kimchi.Protocol.Linearization.LookupEvals (FVar F) where
  sorted _ _ := .const 0
  aggreg _ := .const 0
  table _ := .const 0
  runtimeTable _ := .const 0
  runtimeSelector _ := .const 0
  kindIndex _ := .const 0

/-- Read under any valuation, the circuit's zero columns are the field's. -/
@[simp] theorem lookupZero_map [Field F] {V : Valuation F} :
    (lookupZero (F := F)).map (·.val V)
      = Kimchi.Protocol.Linearization.LookupEvals.zero := by
  simp [lookupZero, Kimchi.Protocol.Linearization.LookupEvals.map,
    Kimchi.Protocol.Linearization.LookupEvals.zero]

/-- The variables a circuit reading of the stream is given. -/
structure Inputs (F : Type) where
  /-- The proof's evaluations, as circuit variables. -/
  evals : Kimchi.Protocol.Linearization.Evals (FVar F)
  /-- `α^n`, precomputed by the caller. -/
  alphaPows : Nat → FVar F
  /-- The permutation challenge `β`. -/
  beta : FVar F
  /-- The permutation challenge `γ`. -/
  gamma : FVar F
  /-- The lookup joint combiner. -/
  jointCombiner : FVar F
  /-- The zero-knowledge vanishing evaluation. -/
  vanishes : FVar F

open Kimchi.Protocol.Linearization in
/-- The in-circuit environment. `add`/`sub` are the affine folds and emit nothing; `mul`
and `pow` are the gadgets; the gate parameters and literals enter as constants.

`unnormalizedLagrangeBasis` is the constant zero rather than a gadget. The deployed stream
reaches it zero times — both occurrences sit inside feature-flagged branches that the
modelled fragment disables — so a real implementation would be unreachable code, and
pinning it here keeps the pure side literally the one `Pickles.Reflect.evaluate_fpTokens`
speaks about. -/
def Inputs.toEnv [Field F] [DecidableEq F] [BasicSystem F c] (endo : F)
    (mds : Kimchi.Gate.Poseidon.Mds F) (lk : Kimchi.Protocol.Linearization.LookupEvals (FVar F))
    (feat : FeatureFlag → Bool) (inp : Inputs F) : Env (CircuitM F c) (FVar F) where
  add := CVar.add_
  sub := CVar.sub_
  mul := Snarky.mul
  pow := Snarky.pow
  cell x := x
  var col row := match col, row with
    | .witness i, .curr => if h : i < wCols then inp.evals.w ⟨i, h⟩ else .const 0
    | .witness i, .next => if h : i < wCols then inp.evals.wOmega ⟨i, h⟩ else .const 0
    | .coefficient i, _ => if h : i < coeffCols then inp.evals.coeffs ⟨i, h⟩ else .const 0
    | .index .generic, _ => inp.evals.genericSelector
    | .index .poseidon, _ => inp.evals.poseidonSelector
    | .index .completeAdd, _ => inp.evals.completeAddSelector
    | .index .varBaseMul, _ => inp.evals.mulSelector
    | .index .endoMul, _ => inp.evals.emulSelector
    | .index .endoMulScalar, _ => inp.evals.endoScalarSelector
    | .lookupSorted i, row => lk.sorted i row
    | .lookupAggreg, row => lk.aggreg row
    | .lookupTable, row => lk.table row
    | .lookupRuntimeTable, row => lk.runtimeTable row
    | .lookupRuntimeSelector, row => lk.runtimeSelector row
    | .lookupKindIndex p, _ => lk.kindIndex p
    | .index _, _ => .const 0
  alphaPow n := inp.alphaPows n
  mds r c := match r, c with
    | 0, 0 => .const mds.m00 | 0, 1 => .const mds.m01 | 0, 2 => .const mds.m02
    | 1, 0 => .const mds.m10 | 1, 1 => .const mds.m11 | 1, 2 => .const mds.m12
    | 2, 0 => .const mds.m20 | 2, 1 => .const mds.m21 | 2, 2 => .const mds.m22
    | _, _ => .const 0
  endoCoefficient := .const endo
  literal v := .const (v : F)
  vanishesOnZeroKnowledgeAndPreviousRows := inp.vanishes
  unnormalizedLagrangeBasis _ _ := pure (.const 0)
  jointCombiner := inp.jointCombiner
  beta := inp.beta
  gamma := inp.gamma
  ifFeature f onTrue onFalse := if feat f then onTrue () else onFalse ()

open Kimchi.Protocol.Linearization in
/-- **The concrete environment computes the specified one.** Under any satisfying
valuation, the circuit environment's readings are the pure environment built from those
same readings — provided the α-table reads as the powers of `α`, which is the caller's
obligation and what `precomputeAlphaPowers` discharges. -/
theorem inputs_circuitCompatible [LawfulBasicSystem F c] {V : Valuation F} (endo : F)
    (mds : Kimchi.Gate.Poseidon.Mds F)
    (lk : Kimchi.Protocol.Linearization.LookupEvals (FVar F))
    (feat : FeatureFlag → Bool) (inp : Inputs F) (α : F)
    (htab : ∀ n, (inp.alphaPows n).val V = α ^ n) :
    CircuitCompatible V (c := c) (inp.toEnv endo mds lk feat)
      ((inp.evals.map (·.val V)).toEnv endo mds α (inp.beta.val V) (inp.gamma.val V)
        (inp.jointCombiner.val V) (inp.vanishes.val V) (fun _ _ => 0)
        (lk.map (·.val V)) feat) where
  add x y := by simp [Inputs.toEnv, Evals.toEnv]
  sub x y := by simp [Inputs.toEnv, Evals.toEnv]
  mul x y := Snarky.mul_spec x y
  pow x n := Snarky.pow_spec x n
  var col row := by
    cases col with
    | index g => cases g <;> cases row <;> simp [Inputs.toEnv, Evals.toEnv, Evals.map]
    | witness i =>
      cases row <;> simp [Inputs.toEnv, Evals.toEnv, Evals.map] <;> split <;> simp
    | coefficient i =>
      cases row <;> simp [Inputs.toEnv, Evals.toEnv, Evals.map] <;> split <;> simp
    | _ => cases row <;> simp [Inputs.toEnv, Evals.toEnv, LookupEvals.map]
  cell _ := rfl
  alphaPow n := by simp [Inputs.toEnv, Evals.toEnv, htab]
  mds r c := by
    match r, c with
    | 0, 0 | 0, 1 | 0, 2 | 1, 0 | 1, 1 | 1, 2 | 2, 0 | 2, 1 | 2, 2 =>
      simp [Inputs.toEnv, Evals.toEnv]
    | _ + 3, _ | _, _ + 3 => simp [Inputs.toEnv, Evals.toEnv]
  endoCoefficient := by simp [Inputs.toEnv, Evals.toEnv]
  literal v := by simp [Inputs.toEnv, Evals.toEnv]
  vanishes := rfl
  ulb zk off := by
    show ⦃⌜True⌝⦄ (pure (.const 0) : CircuitM F (Builder V c) (FVar F))
      ⦃⇓ a _ => ⌜a.val V = (0 : F)⌝⦄
    mvcgen
  jointCombiner := rfl
  beta := rfl
  gamma := rfl
  ifFeature f t₁ n₁ t₂ n₂ ht hn := by
    simp only [Inputs.toEnv, Evals.toEnv]
    split <;> assumption

end Pickles.Linearization
