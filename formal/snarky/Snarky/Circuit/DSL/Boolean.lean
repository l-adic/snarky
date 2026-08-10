import Snarky.Circuit.DSL.Field

-- `mvcgen` is experimental; this option is its acknowledged-use switch (see the
-- `Backend/WP` module docstring for the adoption rationale).
set_option mvcgen.warning false

/-!
# Boolean gadgets

Port of `Snarky.Circuit.DSL.Boolean` (packages/snarky/src/Snarky/Circuit/DSL/Boolean.purs):
the `IfThenElse` selection class with its base instances, the boolean constants,
`not`/`and`/`or`, `xor`, and the array combinators `any`/`all`. PS parks
`not_`/`and_`/`or_` in its Monad module to dodge orphan instances; Lean has no orphan
restriction, so they live here with their family and its laws (`DSL/Field`'s `neq`,
below this module, inlines `not`'s one-line retag rather than import it).

Name map (D7): `if_` → `select` (`if` is a Lean keyword; the class keeps its PS name
`IfThenElse`), `not_` → `not`, `and_` → `and`, `or_` → `or`, `xor_` → `xor` (shadow
core's Bool functions, type-resolved), `any_` → `any`, `all_` → `all` (likewise),
`true_`/`false_` keep their underscores (`true`/`false` are keywords — the same clash
rationale as `CVar`'s smart constructors).

Deviations from the PS original (per `formal/docs/snarky-ps-alignment.md`):
- The PS class fundeps (`c -> f`, `var -> f`) are not modelled — the class stays
  three-parameter (the `Constraint/Basic` precedent); PS puts `PrimeField`/`BasicSystem`
  on the method, here they sit on the instances that need them.
- Instance coverage is the base set: `FVar` (the gadget), `BoolVar` (the same gadget
  under retag — PS coerces), `PUnit`, and the pair, whose components select SECOND
  BEFORE FIRST — PS mirrors OCaml's reverse array evaluation order, and the pair
  instance preserves that. The PS `Vector` and `Record` instances and the
  `GIfThenElse`/`RIfThenElse` deriving machinery land with their first consumers (D8;
  a monadic vector zip needs a kernel-reducible helper in `Snarky/Vec.lean` first).
- `xor` witnesses its bit at `UnChecked Bool` — the typed skip-the-check door (D11),
  verbatim PS — and pins it with the single constraint `2a · b = a + b − r`. Its
  constant cases mirror PS's guard chain, including the fall-through to the witnessing
  branch on a non-bit constant.
- `any`/`all` mirror PS's size cases: empty → constant, one → itself, two →
  `or`/`and`, three or more → the sum test (`any` is `neq (sum …) 0` — PS spells the
  same circuit `not ∘ equals_`; `all` is `equals (length) (sum …)`).

D9 survey (the `snarky-test-utils` Boolean spec), in the D12 form: the `not` row is
`not_eval` (pure gadget, so its law is evaluation-level); the `and`/`or`/`xor`
and `if` rows land as triple laws for `and`/`or` (`*_spec`/`*_complete_spec`),
triple laws for `xor` and `select` (`*_spec`/`*_complete_spec`), stated through the
`CircuitType Bool` encoding
(`if bb then 1 else 0` — the relation the faithfulness arc composes through); the
`all`/`any` rows' three-plus cases need a cast-injectivity hypothesis (a sum of `n` bits
detects `n` only below the characteristic) and are the recorded open obligation of walk
step 10. Fixed-input `decide` examples in `Snarky.Example`.

Public results: the D12 gadget laws, beside their gadgets — `not_eval`, and the triple
pairs `and`, `or`, `xor`, `select` as `*_spec`/`*_complete_spec` over the two readings;
the `all`/`any` rows' three-plus cases need a cast-injectivity hypothesis (a sum of `n`
bits detects `n` only below the characteristic) and are deferred to their first
consumer.
-/

namespace Snarky

/-! ## Conditional selection -/

/-- Conditional selection of circuit values by a boolean variable (PS `IfThenElse`;
its `if_` is `select` — `if` is a Lean keyword). The PS fundeps are not modelled. -/
class IfThenElse (F c : Type) (var : Type) where
  /-- `select b t e` is `t` where `b` holds and `e` where it does not (PS `if_`). -/
  select : BoolVar F → var → var → CircuitM F c var

export IfThenElse (select)

/-- `select`'s witness computation: read the selector, then the chosen branch.
Public only for the gadget laws. -/
def selectWit {F : Type} [Field F] [DecidableEq F] (b : BoolVar F) (t e : FVar F) :
    AsProver F F := do
  let bv ← AsProver.readCVar ↑b
  if bv = 1 then AsProver.readCVar t else AsProver.readCVar e

/-- `select`'s witnessing branch for field variables: witness the chosen value `r`, pin
it with `b · (t − e) = r − e`. Split out so the gadget laws below quantify over it
uniformly. -/
def selectCore {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]
    (b : BoolVar F) (t e : FVar F) : CircuitM F c (FVar F) := do
  let r ← witness (val := F) (selectWit b t e)
  addConstraint (BasicSystem.r1cs ↑b (CVar.sub_ t e) (CVar.sub_ r e))
  pure r

/-- Field variables select by the arithmetic mux `b · (t − e) + e` (PS's base `if_`
instance): a constant selector folds to the chosen branch, two constant branches fold to
the pure affine mux (no witness, no constraint), and otherwise the choice is witnessed
and pinned by one `r1cs` constraint. -/
instance {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] :
    IfThenElse F c (FVar F) where
  select b t e :=
    match (↑b : CVar F) with
    | .const bv => pure (if bv = 1 then t else e)
    | _ =>
      match t, e with
      | .const tv, .const ev =>
        pure (CVar.add_ (.scale tv ↑b) (CVar.scale_ ev (CVar.sub_ (.const 1) ↑b)))
      | t, e => selectCore b t e

/-- Boolean variables select through the field mux, retagged (PS coerces): the mux of
two bits is a bit. -/
instance {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] :
    IfThenElse F c (BoolVar F) where
  select b x y := do
    let r ← select (var := FVar F) b ↑x ↑y
    pure (.unchecked r)

/-- Nothing to select (PS `Unit` instance). -/
instance {F c : Type} : IfThenElse F c PUnit where
  select _ _ _ := pure PUnit.unit

/-- Pairs select componentwise, SECOND BEFORE FIRST — PS mirrors OCaml's reverse array
evaluation order (PS `Tuple` instance). -/
instance {F c : Type} {a b : Type} [IfThenElse F c a] [IfThenElse F c b] :
    IfThenElse F c (a × b) where
  select s p q := do
    let snd ← select s p.2 q.2
    let fst ← select s p.1 q.1
    pure (fst, snd)

/-! ## Constants and combinators -/

/-- The constant true bit (PS `true_`; the underscore stays — `true` is a keyword). -/
def true_ {F : Type} [One F] : BoolVar F := .unchecked (.const 1)

/-- The constant false bit (PS `false_`; the underscore stays — `false` is a keyword). -/
def false_ {F : Type} [Zero F] : BoolVar F := .unchecked (.const 0)

/-- Negate a boolean variable: `1 − b`, pure — no constraint (PS `not_`), through the
`BoolVar.unchecked` door (D11): boolean because `b` is. The name shadows core `not`
inside the `Snarky` namespace; type-directed resolution disambiguates at use sites.
`DSL/Field`'s `neq`, below this module, inlines the same retag. -/
def not {F : Type u} [Add F] [Sub F] [Zero F] [One F] [Neg F] [DecidableEq F]
    (b : BoolVar F) : BoolVar F :=
  .unchecked (CVar.sub_ (.const 1) ↑b)

/-- `not` computes boolean negation: the bit encoding of `!bb` (the `CircuitType Bool`
encoding — the relation the gadget laws speak through). Pure gadget, so its law is
evaluation-level, like `sum_eval`. -/
theorem not_eval {F : Type u} [CommRing F] [DecidableEq F] {b : BoolVar F}
    {env : Assignments F} {bb : Bool}
    (hb : (↑b : CVar F).eval env = .ok (if bb then 1 else 0)) :
    (↑(Snarky.not b) : CVar F).eval env = .ok (if !bb then 1 else 0) := by
  have h := CVar.eval_sub_ (rfl : (CVar.const (1 : F)).eval env = .ok 1) hb
  show (CVar.sub_ (.const 1) ↑b).eval env = _
  rw [h]
  cases bb <;> simp

/-- Conjoin boolean variables: the product, retagged (PS `and_` is `mul_` under
`coerce`) — boolean because a product of bits is a bit (`Snarky.and_sound`). -/
def and {F c : Type u} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c]
    (a b : BoolVar F) : CircuitM F c (BoolVar F) := do
  let r ← mul ↑a ↑b
  pure (.unchecked r)

/-- Disjoin boolean variables by De Morgan: `¬(¬a ∧ ¬b)` (PS `or_`). -/
def or {F c : Type u} [Add F] [Sub F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [BasicSystem F c] (a b : BoolVar F) : CircuitM F c (BoolVar F) := do
  let r ← and (Snarky.not a) (Snarky.not b)
  pure (Snarky.not r)

/-- `xor`'s witness computation: the inequality bit. Public only for the gadget laws in
the gadget laws. -/
def xorWit {F : Type} [Add F] [Mul F] [DecidableEq F] (a b : BoolVar F) :
    AsProver F (UnChecked Bool) := do
  let av ← AsProver.readCVar ↑a
  let bv ← AsProver.readCVar ↑b
  pure ⟨decide (av ≠ bv)⟩

/-- `xor`'s witnessing branch: witness the bit at `UnChecked Bool` (the typed
skip-the-check door, verbatim PS) and pin it with `2a · b = a + b − r`. Split out so the
gadget laws below quantify over it uniformly. -/
def xorCore {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (a b : BoolVar F) :
    CircuitM F c (BoolVar F) := do
  let res ← witness (val := UnChecked Bool) (xorWit a b)
  addConstraint (BasicSystem.r1cs (CVar.add_ (↑a : CVar F) ↑a) ↑b
    (CVar.sub_ (CVar.add_ ↑a ↑b) ↑res.val))
  pure res.val

/-- Exclusive or (PS `xor_`): both constant folds, one-constant simplifications (a zero
selects the other operand, a one selects its negation, anything else falls through to
the witnessing branch, as PS's guard chain does), otherwise `xorCore`. -/
def xor {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (a b : BoolVar F) :
    CircuitM F c (BoolVar F) :=
  match (↑a : CVar F), (↑b : CVar F) with
  | .const av, .const bv => pure (.unchecked (.const (if av = bv then 0 else 1)))
  | .const av, _ =>
    if av = 0 then pure b else if av = 1 then pure (Snarky.not b) else xorCore a b
  | _, .const bv =>
    if bv = 0 then pure a else if bv = 1 then pure (Snarky.not a) else xorCore a b
  | _, _ => xorCore a b

/-- Any of a list of bits (PS `any_`): empty is false, a singleton is itself, a pair is
`or`, and three or more test the bit-sum against zero — `neq (sum …) 0`, the circuit PS
spells `not ∘ equals_`. -/
def any {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]
    (xs : List (BoolVar F)) : CircuitM F c (BoolVar F) :=
  match xs with
  | [] => pure false_
  | [a] => pure a
  | [a, b] => Snarky.or a b
  | _ => neq (sum (xs.map BoolVar.toCVar)) (.const 0)

/-- All of a list of bits (PS `all_`): empty is true, a singleton is itself, a pair is
`and`, and three or more test the bit-sum against the length. -/
def all {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]
    (xs : List (BoolVar F)) : CircuitM F c (BoolVar F) :=
  match xs with
  | [] => pure true_
  | [a] => pure a
  | [a, b] => Snarky.and a b
  | _ => equals (.const (xs.length : F)) (sum (xs.map BoolVar.toCVar))

/-! ## The gadget laws (D12)

As in `DSL/Field`: interpreter-form laws beside their gadgets, `and`/`or`'s here with
their family (`DSL/Monad` cannot host interpreter theorems — the cycle). -/

/-! ### `and`/`or` — composed from `mul`, `not`

The boolean laws speak through `Snarky.bit`, the `CircuitType Bool` encoding — the
relation form the faithfulness arc composes over. -/

open Std.Do in
/-- **`and` soundness triple**: on bit operands the result reads as the conjunction
bit. Generic over any lawful backend. -/
@[spec] theorem and_spec {F c : Type} [Add F] [CommMonoidWithZero F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (a b : BoolVar F) (Q : PostCond (BoolVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : BoolVar F) => ∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab && bb)) Q⦄
    Snarky.and (c := c) a b
    ⦃Q⦄ := by
  simp only [Snarky.and]
  mvcgen
  rename_i hpre
  intro r _nv' hr _
  refine hpre (.unchecked r) _ fun ab bb ha hb => ?_
  simp only [circuitVal, hr, ha, hb]

open Std.Do in
/-- **`and` completeness triple** (prover reading): on bit operands the run succeeds
and the result reads as the conjunction bit in the final table. -/
@[spec] theorem and_complete_spec {F : Type} [Add F] [CommMonoidWithZero F]
    [DecidableEq F] (a b : BoolVar F) (ab bb : Bool)
    (Q : PostCond (BoolVar F)
      (.arg (ProverState F) (.except EvalError .pure))) :
    Triple (m := ProverM F) (Snarky.and (c := Basic F) a b)
      (ProverSpec
        (fun env => (↑a : CVar F).eval env = .ok (bit ab) ∧
          (↑b : CVar F).eval env = .ok (bit bb))
        (fun _ (r : BoolVar F) env' => (↑r : CVar F).eval env' = .ok (bit (ab && bb))) Q) Q := by
  intro st hpre
  obtain ⟨⟨ha, hb⟩, hk⟩ := hpre
  simp only [Snarky.and, ProverM.retag_bind, WPMonad.wp_bind,
    PredTrans.apply_Bind_bind]
  refine mul_complete_spec ↑a ↑b _ st
    ⟨⟨by rw [ha]; rfl, by rw [hb]; rfl⟩, fun r st' hr hle => ?_⟩
  simp only [wp, PredTrans.apply, prove]
  intro hf
  refine hk (.unchecked r) ⟨st'.nv, st'.env, hf⟩ ?_ hle
  show r.eval st'.env = _
  rw [hr _ _ ha hb, bit_mul]

open Std.Do in
/-- **`or` soundness triple**, composed by `mvcgen` from `and_spec` on the negated
bits (De Morgan). Generic over any lawful backend. -/
@[spec] theorem or_spec {F c : Type} [CommRing F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (a b : BoolVar F) (Q : PostCond (BoolVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : BoolVar F) => ∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab || bb)) Q⦄
    Snarky.or (c := c) a b
    ⦃Q⦄ := by
  have hnot : ∀ (x : BoolVar F) (xb : Bool) (V : Valuation F),
      (↑x : CVar F).val V = bit xb →
        (↑(Snarky.not x) : CVar F).val V = bit (!xb) := by
    intro x xb V hx
    cases xb <;> simp [Snarky.not, circuitVal, hx]
  simp only [Snarky.or]
  mvcgen
  rename_i hpre
  intro r _nv' hr _
  refine hpre (Snarky.not r) _ fun ab bb ha hb => ?_
  have hr' := hr (!ab) (!bb) (hnot a ab _ ha) (hnot b bb _ hb)
  cases ab <;> cases bb <;> simp_all [Snarky.not, circuitVal]

open Std.Do in
/-- **`or` completeness triple** (prover reading): on bit operands the run succeeds
and the result reads as the disjunction bit in the final table. -/
@[spec] theorem or_complete_spec {F : Type} [CommRing F] [NoZeroDivisors F]
    [DecidableEq F] (a b : BoolVar F) (ab bb : Bool)
    (Q : PostCond (BoolVar F)
      (.arg (ProverState F) (.except EvalError .pure))) :
    Triple (m := ProverM F) (Snarky.or (c := Basic F) a b)
      (ProverSpec
        (fun env => (↑a : CVar F).eval env = .ok (bit ab) ∧
          (↑b : CVar F).eval env = .ok (bit bb))
        (fun _ (r : BoolVar F) env' => (↑r : CVar F).eval env' = .ok (bit (ab || bb))) Q) Q := by
  intro st hpre
  obtain ⟨⟨ha, hb⟩, hk⟩ := hpre
  simp only [Snarky.or, ProverM.retag_bind, WPMonad.wp_bind,
    PredTrans.apply_Bind_bind]
  refine and_complete_spec (Snarky.not a) (Snarky.not b) (!ab) (!bb) _ st
    ⟨⟨not_eval ha, not_eval hb⟩, fun r st' hr hle => ?_⟩
  simp only [wp, PredTrans.apply, prove]
  intro hf
  refine hk (Snarky.not r) ⟨st'.nv, st'.env, hf⟩ ?_ hle
  show (CVar.sub_ ((.const 1 : CVar F)) ↑r).eval st'.env = _
  rw [CVar.eval_sub_ rfl hr]
  cases ab <;> cases bb <;> simp [bit]

/-! ### `xor` (Circuit/DSL/Boolean)

The `any`/`all` combinators' three-plus cases are the OPEN OBLIGATION of walk step 10:
a sum of `n` bits detects `n` only below the field characteristic, so their laws need a
cast-injectivity hypothesis and the bit-counting lemma — deferred to the step that first
consumes them. -/

/-- The field engine of `xor` soundness: the constraint `2a · b = a + b − r` pins `r` to
the xor bit. -/
private theorem xor_pin {F : Type u} [CommRing F] {ab bb : Bool} {rv : F}
    (h : ((bit ab : F) + bit ab) * bit bb = bit ab + bit bb - rv) :
    rv = bit (ab ^^ bb) := by
  have h' : rv = (bit ab : F) + bit bb - (bit ab + bit ab) * bit bb := by
    rw [eq_sub_iff_add_eq] at h ⊢
    rw [← h]
    ring
  rw [h']
  cases ab <;> cases bb <;> simp [bit]

/-- The honest `xorCore` run. -/
private theorem xorCore_run {F : Type} [Field F] [DecidableEq F] {a b : BoolVar F}
    {nv : Nat} {env : Assignments F} {ab bb : Bool}
    (ha : (↑a : CVar F).eval env = .ok (bit ab))
    (hb : (↑b : CVar F).eval env = .ok (bit bb))
    (hfresh : env.FreshFrom nv) :
    prove Basic.holds (xorCore (c := Basic F) a b) nv env
      = .ok ⟨.unchecked (.var nv), nv + 1, env.extend nv (bit (ab ^^ bb))⟩ := by
  have hnv : env nv = none := hfresh nv (Nat.le_refl nv)
  have hle : env.Le (env.extend nv (bit (ab ^^ bb))) := by
    intro v w hv
    simp only [Assignments.extend]
    split
    · next h => rw [h, hnv] at hv; cases hv
    · exact hv
  have hwit : (xorWit a b env).map
      (CircuitType.valueToFields (F := F) (val := UnChecked Bool))
      = .ok ⟨#[bit (ab ^^ bb)], rfl⟩ := by
    cases hab : ab <;> cases hbb : bb <;>
      simp [xorWit, AsProver.readCVar, ha, hb, hab, hbb, Bind.bind, ReaderT.bind,
        Except.bind, Pure.pure, ReaderT.pure, Except.pure, Except.map,
        CircuitType.valueToFields, bit, one_ne_zero]
  have hext : env.extendPairs
      ((allocRange nv 1).toList.zip
        (⟨#[bit (ab ^^ bb)], rfl⟩ : Vector F 1).toList)
      = .ok (env.extend nv (bit (ab ^^ bb))) := by
    show env.extendPairs [(nv, bit (ab ^^ bb))] = .ok _
    simp [Assignments.extendPairs, hnv]
  have hch : Basic.holds
      (.r1cs (CVar.add_ a.toCVar a.toCVar) b.toCVar
        (CVar.sub_ (CVar.add_ a.toCVar b.toCVar) (.var nv)))
      (env.extend nv (bit (ab ^^ bb))) = true := by
    have ha' := CVar.eval_le hle ha
    have hb' := CVar.eval_le hle hb
    have haa : (CVar.add_ (a.toCVar) (a.toCVar)).eval (env.extend nv (bit (ab ^^ bb)))
        = .ok ((bit ab : F) + bit ab) := by
      rw [CVar.eval_add_]; simp [CVar.eval, ha']
    have hvnv : (CVar.var nv).eval (env.extend nv (bit (ab ^^ bb)))
        = .ok (bit (ab ^^ bb)) := by simp [CVar.eval, Assignments.extend]
    have hab : (CVar.add_ (a.toCVar) (b.toCVar)).eval (env.extend nv (bit (ab ^^ bb)))
        = .ok ((bit ab : F) + bit bb) := by
      rw [CVar.eval_add_]; simp [CVar.eval, ha', hb']
    have hsub := CVar.eval_sub_ hab hvnv
    simp only [Basic.holds, haa, hb', hsub, decide_eq_true_eq]
    cases ab <;> cases bb <;> simp [bit]
  show prove Basic.holds (.existsOp 1 (fun e => (xorWit a b e).map _) _) nv env = _
  simp only [prove, hwit, hext]
  show prove Basic.holds
    (.addConstraintOp (.r1cs (CVar.add_ a.toCVar a.toCVar) b.toCVar
        (CVar.sub_ (CVar.add_ a.toCVar b.toCVar) (.var nv)))
      (.pure (BoolVar.unchecked (.var nv)))) (nv + 1)
    (env.extend nv (bit (ab ^^ bb))) = _
  simp only [prove, hch, if_true]

/-- The `a`-constant guard chain of `xor`, completeness side. -/
private theorem xor_complete_constA {F : Type} [Field F] [DecidableEq F]
    {a b : BoolVar F} {nv : Nat} {env : Assignments F} {ab bb : Bool} {av : F}
    (hA : (↑a : CVar F) = .const av)
    (ha : (↑a : CVar F).eval env = .ok (bit ab))
    (hb : (↑b : CVar F).eval env = .ok (bit bb))
    (hfresh : env.FreshFrom nv) :
    ∃ out, prove Basic.holds (if av = 0 then pure b else if av = 1 then pure (Snarky.not b)
        else xorCore (c := Basic F) a b) nv env = .ok out ∧
      out.result.toCVar.eval out.assignments = .ok (bit (ab ^^ bb)) ∧
      out.assignments.FreshFrom out.nextVar := by
  have hav : av = bit ab := by rw [hA] at ha; simpa [CVar.eval] using ha
  split_ifs with h0 h1
  · have : ab = false := by
      cases ab
      · rfl
      · exact absurd (hav.symm.trans h0) (by simp [bit])
    subst this
    exact ⟨_, rfl, by simpa using hb, hfresh⟩
  · have : ab = true := by
      cases ab
      · exact absurd (hav ▸ h1) (by simp [bit])
      · rfl
    subst this
    refine ⟨_, rfl, ?_, hfresh⟩
    show (CVar.sub_ (.const 1) _).eval env = _
    rw [CVar.eval_sub_ rfl hb]
    cases bb <;> simp [bit]
  · rcases bit_cases hav with h | h
    · exact absurd h h0
    · exact absurd h h1

/-- The `b`-constant guard chain of `xor`, completeness side. -/
private theorem xor_complete_constB {F : Type} [Field F] [DecidableEq F]
    {a b : BoolVar F} {nv : Nat} {env : Assignments F} {ab bb : Bool} {bv : F}
    (hB : (↑b : CVar F) = .const bv)
    (ha : (↑a : CVar F).eval env = .ok (bit ab))
    (hb : (↑b : CVar F).eval env = .ok (bit bb))
    (hfresh : env.FreshFrom nv) :
    ∃ out, prove Basic.holds (if bv = 0 then pure a else if bv = 1 then pure (Snarky.not a)
        else xorCore (c := Basic F) a b) nv env = .ok out ∧
      out.result.toCVar.eval out.assignments = .ok (bit (ab ^^ bb)) ∧
      out.assignments.FreshFrom out.nextVar := by
  have hbv : bv = bit bb := by rw [hB] at hb; simpa [CVar.eval] using hb
  split_ifs with h0 h1
  · have : bb = false := by
      cases bb
      · rfl
      · exact absurd (hbv.symm.trans h0) (by simp [bit])
    subst this
    exact ⟨_, rfl, by simpa using ha, hfresh⟩
  · have : bb = true := by
      cases bb
      · exact absurd (hbv ▸ h1) (by simp [bit])
      · rfl
    subst this
    refine ⟨_, rfl, ?_, hfresh⟩
    show (CVar.sub_ (.const 1) _).eval env = _
    rw [CVar.eval_sub_ rfl ha]
    cases ab <;> simp [bit]
  · rcases bit_cases hbv with h | h
    · exact absurd h h0
    · exact absurd h h1

open Std.Do in
/-- **`xor` soundness triple**: on bit operands the result reads as the xor bit —
the constant branches fold through the guards, the core row pins via `xor_pin`.
Generic over any lawful backend. -/
@[spec] theorem xor_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (a b : BoolVar F) (Q : PostCond (BoolVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : BoolVar F) => ∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab ^^ bb)) Q⦄
    Snarky.xor (c := c) a b
    ⦃Q⦄ := by
  intro s hpre
  obtain ⟨V, nv⟩ := s
  cases hA : (↑a : CVar F) <;> cases hB : (↑b : CVar F) <;>
    simp only [Snarky.xor, hA, hB]
  case const.const av bv =>
    intro _
    refine hpre _ nv fun ab bb ha hb => ?_
    rw [hA] at ha
    rw [hB] at hb
    replace ha : av = bit ab := ha
    replace hb : bv = bit bb := hb
    subst ha; subst hb
    cases ab <;> cases bb <;> simp [circuitVal, bit]
  case const.var av v | const.add av x y | const.scale av k x =>
    split_ifs with h0 h1
    · intro _
      refine hpre b nv fun ab bb ha hb => ?_
      rw [hA] at ha
      replace ha : av = bit ab := ha
      have hab : ab = false := by
        cases ab
        · rfl
        · exact absurd (ha.symm.trans h0) (by simp [bit])
      subst hab
      simpa using hb
    · intro _
      refine hpre (Snarky.not b) nv fun ab bb ha hb => ?_
      rw [hA] at ha
      replace ha : av = bit ab := ha
      have hab : ab = true := by
        cases ab
        · exact absurd (ha ▸ h1) (by simp [bit])
        · rfl
      subst hab
      cases bb <;> simp [Snarky.not, circuitVal, hb]
    · intro hsat
      refine hpre (.unchecked (.var nv)) _ fun ab bb ha hb => ?_
      have h := LawfulBasicSystem.holds_r1cs V _ _ _ (hsat _ (List.mem_cons_self ..))
      simp only [circuitVal] at h
      rw [ha, hb] at h
      exact xor_pin h
  case var.const v bv | add.const x y bv | scale.const k x bv =>
    split_ifs with h0 h1
    · intro _
      refine hpre a nv fun ab bb ha hb => ?_
      rw [hB] at hb
      replace hb : bv = bit bb := hb
      have hbb : bb = false := by
        cases bb
        · rfl
        · exact absurd (hb.symm.trans h0) (by simp [bit])
      subst hbb
      simpa using ha
    · intro _
      refine hpre (Snarky.not a) nv fun ab bb ha hb => ?_
      rw [hB] at hb
      replace hb : bv = bit bb := hb
      have hbb : bb = true := by
        cases bb
        · exact absurd (hb ▸ h1) (by simp [bit])
        · rfl
      subst hbb
      cases ab <;> simp [Snarky.not, circuitVal, ha]
    · intro hsat
      refine hpre (.unchecked (.var nv)) _ fun ab bb ha hb => ?_
      have h := LawfulBasicSystem.holds_r1cs V _ _ _ (hsat _ (List.mem_cons_self ..))
      simp only [circuitVal] at h
      rw [ha, hb] at h
      exact xor_pin h
  all_goals
    (intro hsat
     refine hpre (.unchecked (.var nv)) _ fun ab bb ha hb => ?_
     have h := LawfulBasicSystem.holds_r1cs V _ _ _ (hsat _ (List.mem_cons_self ..))
     simp only [circuitVal] at h
     rw [ha, hb] at h
     exact xor_pin h)

open Std.Do in
/-- **`xor` completeness triple** (prover reading): on bit operands the run succeeds
and the result reads as the xor bit in the final table. -/
@[spec] theorem xor_complete_spec {F : Type} [Field F] [DecidableEq F]
    (a b : BoolVar F) (ab bb : Bool)
    (Q : PostCond (BoolVar F)
      (.arg (ProverState F) (.except EvalError .pure))) :
    Triple (m := ProverM F) (Snarky.xor (c := Basic F) a b)
      (ProverSpec
        (fun env => (↑a : CVar F).eval env = .ok (bit ab) ∧
          (↑b : CVar F).eval env = .ok (bit bb))
        (fun _ (r : BoolVar F) env' => (↑r : CVar F).eval env' = .ok (bit (ab ^^ bb))) Q) Q := by
  intro st hpre
  obtain ⟨⟨ha, hb⟩, hk⟩ := hpre
  simp only [wp, PredTrans.apply, Snarky.xor]
  cases hA : (↑a : CVar F) <;> cases hB : (↑b : CVar F)
  case const.const av bv =>
    have hav : av = bit ab := by rw [hA] at ha; simpa [CVar.eval] using ha
    have hbv : bv = bit bb := by rw [hB] at hb; simpa [CVar.eval] using hb
    subst hav; subst hbv
    intro hf
    refine hk _ ⟨_, _, hf⟩ ?_ (Assignments.Le.refl st.env)
    show Except.ok _ = _
    cases ab <;> cases bb <;> simp [bit]
  case const.var av v | const.add av x y | const.scale av k x =>
    obtain ⟨o, hrun, heval, -⟩ := xor_complete_constA hA ha hb st.fresh
    rw [hrun]
    intro hf
    exact hk _ ⟨_, _, hf⟩ heval (prove_assignments_le hrun)
  case var.const v bv | add.const x y bv | scale.const k x bv =>
    obtain ⟨o, hrun, heval, -⟩ := xor_complete_constB hB ha hb st.fresh
    rw [hrun]
    intro hf
    exact hk _ ⟨_, _, hf⟩ heval (prove_assignments_le hrun)
  all_goals
    (rw [xorCore_run ha hb st.fresh]
     intro hf
     refine hk _ ⟨_, _, hf⟩ ?_ (Assignments.le_extend_self st.fresh _)
     show (CVar.var st.nv).eval _ = _
     simp [CVar.eval, Assignments.extend])

/-! ### `select` (Circuit/DSL/Boolean, the `IfThenElse` field instance) -/

/-- The honest `selectCore` run. -/
private theorem selectCore_run {F : Type} [Field F] [DecidableEq F]
    {b : BoolVar F} {t e : FVar F} {nv : Nat} {env : Assignments F} {bb : Bool}
    {tv ev : F}
    (hb : (↑b : CVar F).eval env = .ok (bit bb))
    (ht : t.eval env = .ok tv) (he : e.eval env = .ok ev)
    (hfresh : env.FreshFrom nv) :
    prove Basic.holds (selectCore (c := Basic F) b t e) nv env
      = .ok ⟨.var nv, nv + 1, env.extend nv (if bb then tv else ev)⟩ := by
  have hnv : env nv = none := hfresh nv (Nat.le_refl nv)
  have hle : env.Le (env.extend nv (if bb then tv else ev)) := by
    intro v w hv
    simp only [Assignments.extend]
    split
    · next h => rw [h, hnv] at hv; cases hv
    · exact hv
  have hw : selectWit b t e env = .ok (if bb then tv else ev) := by
    cases bb <;>
      simp [selectWit, AsProver.readCVar, hb, ht, he, Bind.bind, ReaderT.bind,
        Except.bind, bit]
  have hch : Basic.holds
      (.r1cs b.toCVar (CVar.sub_ t e) (CVar.sub_ (.var nv) e))
      (env.extend nv (if bb then tv else ev)) = true := by
    have hb' := CVar.eval_le hle hb
    have ht' := CVar.eval_le hle ht
    have he' := CVar.eval_le hle he
    have hvnv : (CVar.var nv).eval (env.extend nv (if bb then tv else ev))
        = .ok (if bb then tv else ev) := by simp [CVar.eval, Assignments.extend]
    have hsub₁ := CVar.eval_sub_ ht' he'
    have hsub₂ := CVar.eval_sub_ hvnv he'
    simp only [Basic.holds, hb', hsub₁, hsub₂, decide_eq_true_eq]
    cases bb <;> simp [bit]
  exact prove_witnessCore hw hfresh hch

/-- The evaluation of the constant-branches affine mux, over an arbitrary selector
expression. -/
private theorem select_mux_eval {F : Type} [Field F] [DecidableEq F] {bc : CVar F}
    {bb : Bool} {env : Assignments F} {tv' ev' tv ev : F}
    (hb : bc.eval env = .ok (bit bb))
    (ht : (CVar.const tv').eval env = .ok tv) (he : (CVar.const ev').eval env = .ok ev) :
    (CVar.add_ (.scale tv' bc)
      (CVar.scale_ ev' (CVar.sub_ (.const 1) bc))).eval env
      = .ok (if bb then tv else ev) := by
  have htv : tv' = tv := by simpa [CVar.eval] using ht
  have hev : ev' = ev := by simpa [CVar.eval] using he
  rw [← htv, ← hev]
  rw [CVar.eval_add_]
  have h₁ : (CVar.scale tv' bc).eval env = .ok (tv' * bit bb) := by
    simp [CVar.eval, hb]
  have h₂ := CVar.eval_scale_
    (CVar.eval_sub_ (rfl : (CVar.const (1 : F)).eval env = .ok 1) hb) ev'
  set X := CVar.scale tv' bc with hX
  set Y := CVar.scale_ ev' (CVar.sub_ (.const 1) bc) with hY
  simp only [CVar.eval, h₁, h₂]
  cases bb <;> simp [bit]

/-- The field engine of `select` soundness: the row `b · (t − e) = r − e` pins `r` to
the chosen branch. -/
private theorem select_pin {F : Type} [Field F] {bb : Bool} {bv tv ev rv : F}
    (h : bv * (tv - ev) = rv - ev) (hbv : bv = bit bb) :
    rv = if bb then tv else ev := by
  subst hbv
  cases bb
  · show rv = ev
    have h0 : (0 : F) = rv - ev := by
      rw [← h]
      show (0 : F) = (bit false : F) * (tv - ev)
      simp [bit]
    exact (sub_eq_zero.mp h0.symm).symm ▸ rfl
  · show rv = tv
    have h1 : tv - ev = rv - ev := by
      rw [← h]
      show _ = (bit true : F) * (tv - ev)
      simp [bit]
    exact (sub_left_inj.mp h1).symm

/-- What `selectCore` builds at any backend: one fresh variable, one `r1cs` row. -/
private theorem build_selectCore' {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] (b : BoolVar F) (t e : FVar F) (nv : Nat) :
    build (selectCore (c := c) b t e) nv
      = ⟨.var nv, nv + 1,
         [BasicSystem.r1cs ↑b (CVar.sub_ t e) (CVar.sub_ (.var nv) e)]⟩ := rfl

open Std.Do in
/-- **`select` soundness triple**: on a bit selector the result reads as the chosen
branch — the constant selector folds to a branch, two constant branches fold to the
affine mux, and otherwise the `r1cs` row pins the choice. Generic over any lawful
backend. -/
@[spec] theorem select_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (b : BoolVar F) (t e : FVar F)
    (Q : PostCond (FVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V r => ∀ bb : Bool,
        (↑b : CVar F).val V = bit bb → r.val V = if bb then t.val V else e.val V) Q⦄
    select (c := c) b t e
    ⦃Q⦄ := by
  intro s hpre hsat
  obtain ⟨V, nv⟩ := s
  refine hpre _ _ fun bb hb => ?_
  show (build (match (↑b : CVar F) with
    | .const bv => pure (if bv = 1 then t else e)
    | _ => match t, e with
      | .const tv, .const ev =>
        pure (CVar.add_ (.scale tv ↑b) (CVar.scale_ ev (CVar.sub_ (.const 1) ↑b)))
      | t, e => selectCore b t e) nv).result.val V = _
  replace hsat : ∀ con ∈ (build (match (↑b : CVar F) with
    | .const bv => pure (if bv = 1 then t else e)
    | _ => match t, e with
      | .const tv, .const ev =>
        pure (CVar.add_ (.scale tv ↑b) (CVar.scale_ ev (CVar.sub_ (.const 1) ↑b)))
      | t, e => selectCore b t e) nv).constraints,
      ConstraintHolds.Holds V con := hsat
  cases hB : (↑b : CVar F) <;> rw [hB] at hsat
  case const bv =>
    rw [hB] at hb
    replace hb : bv = bit bb := hb
    subst hb
    show (build (pure (if (bit bb : F) = 1 then t else e) :
      CircuitM F c (FVar F)) nv).result.val V = _
    cases bb <;> simp [bit] <;> rfl
  all_goals
    cases t <;> cases e <;> dsimp only at hsat ⊢ <;>
      first
      | (rw [build_selectCore'] at hsat ⊢
         have h := LawfulBasicSystem.holds_r1cs V _ _ _ (hsat _ (List.mem_cons_self ..))
         simp only [circuitVal] at h
         exact select_pin h hb)
      | (show (CVar.add_ (CVar.scale _ _) (CVar.scale_ _ _)).val V = _
         rw [← hB]
         simp only [circuitVal, hb]
         cases bb <;> simp [bit])

open Std.Do in
/-- **`select` completeness triple** (prover reading): on a bit selector the run
succeeds and the result reads as the chosen branch in the final table. -/
@[spec] theorem select_complete_spec {F : Type} [Field F] [DecidableEq F]
    (b : BoolVar F) (t e : FVar F) (bb : Bool)
    (Q : PostCond (FVar F)
      (.arg (ProverState F) (.except EvalError .pure))) :
    Triple (m := ProverM F) (select (c := Basic F) b t e)
      (ProverSpec
        (fun env => (↑b : CVar F).eval env = .ok (bit bb) ∧
          (t.eval env).isOk ∧ (e.eval env).isOk)
        (fun env r env' => ∀ tv ev, t.eval env = .ok tv → e.eval env = .ok ev →
          r.eval env' = .ok (if bb then tv else ev)) Q) Q := by
  intro st hpre
  obtain ⟨⟨hb, hokt, hoke⟩, hk⟩ := hpre
  obtain ⟨tv, ht⟩ := CVar.evalOk hokt
  obtain ⟨ev, he⟩ := CVar.evalOk hoke
  have hval : ∀ {r : FVar F} {env' : Assignments F},
      r.eval env' = .ok (if bb then tv else ev) →
      ∀ t' e', t.eval st.env = .ok t' → e.eval st.env = .ok e' →
        r.eval env' = .ok (if bb then t' else e') := by
    intro r env' heval t' e' ht' he'
    rw [ht] at ht'; rw [he] at he'
    injection ht' with ht'; injection he' with he'
    exact ht' ▸ he' ▸ heval
  simp only [wp, PredTrans.apply, select]
  cases hB : (↑b : CVar F)
  case const bv =>
    rw [hB] at hb
    have hbv : bv = bit bb := by simpa [CVar.eval] using hb
    subst hbv
    intro hf
    refine hk _ ⟨_, _, hf⟩ (hval ?_) (Assignments.Le.refl st.env)
    cases bb <;> simp [bit] <;> [exact he; exact ht]
  all_goals
    cases t <;> cases e <;> dsimp only <;>
      first
      | (intro hf
         refine hk _ ⟨_, _, hf⟩ (hval ?_) (Assignments.Le.refl st.env)
         exact select_mux_eval (hB ▸ hb) ht he)
      | (rw [selectCore_run hb ht he st.fresh]
         intro hf
         refine hk _ ⟨_, _, hf⟩ (hval ?_) (Assignments.le_extend_self st.fresh _)
         show (CVar.var st.nv).eval _ = _
         simp [CVar.eval, Assignments.extend])

end Snarky
