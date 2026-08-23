import Snarky.Circuit.DSL.Field

-- `mvcgen` is experimental; this option is its acknowledged-use switch (see the
-- `Backend/WP` module docstring for the adoption rationale).
set_option mvcgen.warning false

/-!
# Boolean gadgets

Port of `Snarky.Circuit.DSL.Boolean` (packages/snarky/src/Snarky/Circuit/DSL/Boolean.purs):
the `IfThenElse` selection class with its base instances, the boolean constants,
`not`/`and`/`or`, `xor`, and the list combinators `any`/`all`. PS parks
`not_`/`and_`/`or_` in its Monad module to dodge orphan instances; Lean has no orphan
restriction, so they live here with their family and its laws.

Name map: `if_` → `select` (`if` is a Lean keyword; the class keeps its PS name
`IfThenElse`), `not_` → `not`, `and_` → `and`, `or_` → `or`, `xor_` → `xor` (shadowing
core's Bool functions, type-resolved), `any_` → `any`, `all_` → `all`;
`true_`/`false_` keep their underscores (`true`/`false` are keywords).

Deviations from the PS original (ledger: `formal/docs/snarky-ps-alignment.md`):
- The PS class fundeps are not modelled; instance coverage is the base set (`FVar`,
  `BoolVar`, `PUnit`, and the pair, whose components select SECOND BEFORE FIRST — PS
  mirrors OCaml's reverse array evaluation order). The `select` laws cover the `FVar`
  instance; the others delegate to it (or select nothing) and carry no laws of their
  own.
- `xor` witnesses its bit at `UnChecked Bool`, verbatim PS, pinned by the single
  constraint `2a · b = a + b − r`; its constant cases mirror PS's guard chain.
- `any`/`all` mirror PS's size cases: empty → constant, one → itself, two →
  `or`/`and`, three or more → the sum test.

The laws are stated through the `CircuitType Bool` encoding (`bit`). The sum-based
cases carry a cast-injectivity hypothesis — a sum of `n` bits detects a count only
below the field characteristic — introduced in their own section below.
-/

namespace Snarky

/-! ## Conditional selection -/

/-- Conditional selection of circuit values by a boolean variable (PS `IfThenElse`;
its `if_` is `select` — `if` is a Lean keyword). The PS fundeps are not modelled. -/
class IfThenElse (F c : Type) (var : Type) where
  /-- `select b t e` is `t` where `b` holds and `e` where it does not (PS `if_`). -/
  select : BoolVar F → var → var → CircuitM F c var

export IfThenElse (select)

/-- `select`'s witness computation: read the selector, then the chosen branch. -/
private def selectWit {F : Type} [Field F] [DecidableEq F] (b : BoolVar F) (t e : FVar F) :
    AsProver F F := do
  let bv ← AsProver.readCVar ↑b
  if bv = 1 then AsProver.readCVar t else AsProver.readCVar e

/-- The value-level answer of `select` — the pure mirror both readings state their
posts through. -/
def selectPure {F : Type u} (bb : Bool) (tv ev : F) : F := if bb then tv else ev

attribute [circuitVal] selectPure

/-- `select`'s witnessing branch for field variables: witness the chosen value `r`, pin
it with `b · (t − e) = r − e`. Split out so the gadget laws below quantify over it
uniformly. -/
private def selectCore {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]
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
`BoolVar.unchecked` door: boolean because `b` is. The name shadows core `not`
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

/-- `not`'s expression is in scope when the operand's is. -/
theorem not_scoped {F : Type} [Add F] [Sub F] [Zero F] [One F] [Neg F] [DecidableEq F]
    {st : ProverState F} {b : BoolVar F} (hb : (↑b : CVar F).Scoped st) :
    (↑(Snarky.not b) : CVar F).Scoped st :=
  CVar.Scoped.sub_ (CVar.scoped_const _ _) hb

/-- `not` reads as the negated bit. -/
theorem not_val {F : Type u} [CommRing F] [DecidableEq F] {V : Valuation F} {b : BoolVar F}
    {bb : Bool} (hb : (↑b : CVar F).val V = bit bb) :
    (↑(Snarky.not b) : CVar F).val V = bit (!bb) := by
  show (CVar.sub_ (.const 1) ↑b).val V = _
  rw [CVar.val_sub_, hb]
  cases bb <;> simp [bit, CVar.val]

/-- Conjoin boolean variables: the product, retagged (PS `and_` is `mul_` under
`coerce`) — boolean because a product of bits is a bit (`Snarky.and_spec`). -/
def and {F c : Type u} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c]
    (a b : BoolVar F) : CircuitM F c (BoolVar F) := do
  let r ← mul ↑a ↑b
  pure (.unchecked r)

/-- Disjoin boolean variables by De Morgan: `¬(¬a ∧ ¬b)` (PS `or_`). -/
def or {F c : Type u} [Add F] [Sub F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [BasicSystem F c] (a b : BoolVar F) : CircuitM F c (BoolVar F) := do
  let r ← and (Snarky.not a) (Snarky.not b)
  pure (Snarky.not r)

/-- `xor`'s witness computation: the inequality bit. -/
private def xorWit {F : Type} [Add F] [Mul F] [DecidableEq F] (a b : BoolVar F) :
    AsProver F (UnChecked Bool) := do
  let av ← AsProver.readCVar ↑a
  let bv ← AsProver.readCVar ↑b
  pure ⟨decide (av ≠ bv)⟩

/-- `xor`'s witnessing branch: witness the bit at `UnChecked Bool` (the typed
skip-the-check door, verbatim PS) and pin it with `2a · b = a + b − r`. Split out so the
gadget laws below quantify over it uniformly. -/
private def xorCore {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (a b : BoolVar F) :
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

/-! ## The gadget laws -/

/-! ### `and`/`or` — composed from `mul`, `not`

The boolean laws speak through `Snarky.bit`, the `CircuitType Bool` encoding. -/

open Std.Do in
/-- `and`: on bit operands the result reads as the conjunction bit. -/
@[spec] theorem and_spec {F c : Type} {V : Valuation F} [Add F] [CommMonoidWithZero F]
    [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (a b : BoolVar F) :
    ⦃⌜True⌝⦄
    Snarky.and (c := Builder V c) a b
    ⦃⇓ r _ => ⌜∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab && bb)⌝⦄ := by
  simp only [Snarky.and]
  mvcgen
  rename_i r _ hr
  intro ab bb ha hb
  simp only [circuitVal, hr, ha, hb]

/-- The state and result of `and`'s honest run: `mul`, retagged. -/
def andRun {F : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] (st : ProverState F)
    (a b : BoolVar F) : ProverState F × BoolVar F :=
  let r := mulRun st ↑a ↑b
  (r.1, .unchecked r.2)

/-- `and`'s honest run lands at `andRun`. -/
theorem and_run {F c : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {a b : BoolVar F}
    (st : ProverState F) (ha : (↑a : CVar F).Scoped st) (hb : (↑b : CVar F).Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (Snarky.and (c := c) a b) st.nv st.env
      = .ok ((andRun st a b).1.out (andRun st a b).2) := by
  simp only [Snarky.and, prove_bind, mul_run st ha hb, Except.bind, andRun]
  rfl

/-- `andRun` reads, through the bit's expression, as the conjunction. -/
theorem andRun_grants {F : Type} [Add F] [CommMonoidWithZero F] [DecidableEq F]
    {st : ProverState F} {a b : BoolVar F} {ab bb : Bool}
    (ha : (↑a : CVar F).Scoped st) (hb : (↑b : CVar F).Scoped st)
    (hav : (↑a : CVar F).val st.env.toValuation = bit ab)
    (hbv : (↑b : CVar F).val st.env.toValuation = bit bb) :
    Grants F st ((andRun st a b).1, ↑(andRun st a b).2) (bit (ab && bb)) := by
  have h := mulRun_grants ha hb
  exact Grants.fvar h.le h.fvar_scoped (by
    show (mulRun st ↑a ↑b).2.val (mulRun st ↑a ↑b).1.env.toValuation = _
    rw [h.fvar_val, hav, hbv, bit_mul])

open Std.Do in
/-- `or`: on bit operands the result reads as the disjunction bit — `and` on the
negated bits, by De Morgan. -/
@[spec] theorem or_spec {F c : Type} {V : Valuation F} [CommRing F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (a b : BoolVar F) :
    ⦃⌜True⌝⦄
    Snarky.or (c := Builder V c) a b
    ⦃⇓ r _ => ⌜∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab || bb)⌝⦄ := by
  have hnot : ∀ (x : BoolVar F) (xb : Bool) (V : Valuation F),
      (↑x : CVar F).val V = bit xb →
        (↑(Snarky.not x) : CVar F).val V = bit (!xb) := by
    intro x xb V hx
    cases xb <;> simp [Snarky.not, circuitVal, hx]
  simp only [Snarky.or]
  mvcgen
  rename_i r _ hr
  intro ab bb ha hb
  have hr' := hr (!ab) (!bb) (hnot a ab _ ha) (hnot b bb _ hb)
  cases ab <;> cases bb <;> simp_all [Snarky.not, circuitVal]

/-- The state and result of `or`'s honest run: De Morgan over `andRun`. -/
def orRun {F : Type} [CommRing F] [DecidableEq F] (st : ProverState F) (a b : BoolVar F) :
    ProverState F × BoolVar F :=
  let r := andRun st (Snarky.not a) (Snarky.not b)
  (r.1, Snarky.not r.2)

/-- `or`'s honest run lands at `orRun`. -/
theorem or_run {F c : Type} [CommRing F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {a b : BoolVar F}
    (st : ProverState F) (ha : (↑a : CVar F).Scoped st) (hb : (↑b : CVar F).Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (Snarky.or (c := c) a b) st.nv st.env
      = .ok ((orRun st a b).1.out (orRun st a b).2) := by
  simp only [Snarky.or, prove_bind, and_run st (not_scoped ha) (not_scoped hb), Except.bind,
    orRun]
  rfl

/-- `orRun` reads, through the bit's expression, as the disjunction. -/
theorem orRun_grants {F : Type} [CommRing F] [DecidableEq F]
    {st : ProverState F} {a b : BoolVar F} {ab bb : Bool}
    (ha : (↑a : CVar F).Scoped st) (hb : (↑b : CVar F).Scoped st)
    (hav : (↑a : CVar F).val st.env.toValuation = bit ab)
    (hbv : (↑b : CVar F).val st.env.toValuation = bit bb) :
    Grants F st ((orRun st a b).1, ↑(orRun st a b).2) (bit (ab || bb)) := by
  have h := andRun_grants (not_scoped ha) (not_scoped hb) (not_val hav) (not_val hbv)
  have hv : (↑(andRun st (Snarky.not a) (Snarky.not b)).2 : CVar F).val
      (andRun st (Snarky.not a) (Snarky.not b)).1.env.toValuation = bit (!ab && !bb) := h.fvar_val
  exact Grants.fvar h.le (not_scoped h.fvar_scoped) (by
    show (↑(Snarky.not (andRun st (Snarky.not a) (Snarky.not b)).2) : CVar F).val
      (andRun st (Snarky.not a) (Snarky.not b)).1.env.toValuation = _
    rw [not_val hv]
    simp)

/-! ### The sum-based combinators (`any`/`all`)

A sum of `n` bits detects `n` only below the field characteristic, so the three-plus
cases' laws carry a cast-injectivity hypothesis (`hchar`, up to the list length plus
one — the slack covers the one-hot constant of `assertExactlyOne`, which shares this
toolkit). The bit lists enter through `ReadBits`/`EvalBits`, one relation per
reading. -/

/-- All operands read as the given bits under a valuation — the componentwise
hypothesis the sum-based soundness laws quantify over. -/
def ReadBits [Add F] [Mul F] [Zero F] [One F] (V : Valuation F)
    (bs : List (BoolVar F)) (bl : List Bool) : Prop :=
  List.Forall₂ (fun (b : BoolVar F) bb => (↑b : CVar F).val V = bit bb) bs bl

/-- All operands read as the given bits in the table — the prover reading's
counterpart of `ReadBits`. -/
def EvalBits [Add F] [Mul F] [Zero F] [One F] (env : Assignments F)
    (bs : List (BoolVar F)) (bl : List Bool) : Prop :=
  List.Forall₂ (fun (b : BoolVar F) bb => (↑b : CVar F).eval env = .ok (bit bb)) bs bl

/-- Related lists have equal lengths — `Forall₂`'s length law, stated locally to keep
the targeted imports. -/
theorem forall₂_length {α β : Type u} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') : l.length = l'.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa using ih

/-- The encodings of a bit list sum to its true-count. -/
private theorem bitSum {F : Type} [Semiring F] :
    ∀ bl : List Bool, (bl.map (bit (F := F))).sum = (bl.count true : F) := by
  intro bl
  induction bl with
  | nil => simp
  | cons b bl ih =>
    cases b <;> simp [ih, bit, add_comm]

/-- The bit-sum evaluates to the true-count in the table. -/
theorem sum_bits_eval {F : Type} [Semiring F] [DecidableEq F] {env : Assignments F} :
    ∀ {bs : List (BoolVar F)} {bl : List Bool}, EvalBits env bs bl →
      (sum (bs.map BoolVar.toCVar)).eval env = .ok (bl.count true : F) := by
  intro bs bl h
  rw [← bitSum bl]
  refine sum_eval ?_
  induction h with
  | nil => rfl
  | cons hb _ ih => simp only [List.map_cons, ih, hb]

/-- The bit-sum reads as the true-count under a valuation. -/
theorem sum_bits_val {F : Type} [Semiring F] [DecidableEq F] {V : Valuation F} :
    ∀ {bs : List (BoolVar F)} {bl : List Bool}, ReadBits V bs bl →
      (sum (bs.map BoolVar.toCVar)).val V = (bl.count true : F) := by
  intro bs bl h
  have h' : EvalBits V.toAssignments bs bl := by
    induction h with
    | nil => exact .nil
    | cons hb _ ih => exact .cons (by rw [CVar.eval_toAssignments, hb]) ih
  have := sum_bits_eval h'
  rw [CVar.eval_toAssignments] at this
  injection this

/-- No true bit means a zero count, and back. -/
theorem count_true_eq_zero {bl : List Bool} : bl.count true = 0 ↔ bl.any id = false := by
  rw [List.count_eq_zero, List.any_eq_false]
  constructor
  · intro h x hx
    cases x
    · simp
    · exact absurd hx h
  · intro h hx
    exact absurd (h true hx) (by simp)

/-- Every bit true means a full count, and back. -/
theorem count_true_eq_length {bl : List Bool} :
    bl.count true = bl.length ↔ bl.all id = true := by
  rw [List.count_eq_length, List.all_eq_true]
  constructor
  · intro h x hx
    exact (h x hx).symm
  · intro h x hx
    exact (h x hx).symm

/-- A bit-sum over evaluable operands evaluates, whatever their values — what
discharges the composed gadgets' `isOk` preconditions. -/
theorem sum_evalOk {F : Type} [Semiring F] [DecidableEq F] {env : Assignments F} :
    ∀ {bs : List (BoolVar F)}, (∀ b ∈ bs, (((b : BoolVar F) : CVar F).eval env).isOk) →
      ((sum (bs.map BoolVar.toCVar)).eval env).isOk := by
  suffices h : ∀ (l : List (BoolVar F)) (acc : CVar F), ((acc.eval env).isOk) →
      (∀ b ∈ l, (((b : BoolVar F) : CVar F).eval env).isOk) →
      (((l.map BoolVar.toCVar).foldl CVar.add_ acc).eval env).isOk by
    intro bs hbs
    exact h bs (.const 0) rfl hbs
  intro l
  induction l with
  | nil =>
    intro acc hacc _
    simpa using hacc
  | cons b t ih =>
    intro acc hacc hall
    obtain ⟨av, ha⟩ := CVar.evalOk hacc
    obtain ⟨bv, hb⟩ := CVar.evalOk (hall b (List.mem_cons_self ..))
    refine ih _ ?_ (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    rw [CVar.eval_add_ ha hb]
    rfl

/-- Bit-reading operands read as SOME bit list — names the list a `ReadsBit`
hypothesis promises, for use inside a proof. -/
theorem exists_evalBits {F : Type} [Add F] [Mul F] [Zero F] [One F]
    {env : Assignments F} :
    ∀ {bs : List (BoolVar F)}, (∀ b ∈ bs, ReadsBit ((b : BoolVar F) : CVar F) env) →
      ∃ bl, EvalBits env bs bl := by
  intro bs
  induction bs with
  | nil => exact fun _ => ⟨[], .nil⟩
  | cons b t ih =>
    intro h
    obtain ⟨bb, hb⟩ := (h b (List.mem_cons_self ..)).exists_bit
    obtain ⟨bl, hbl⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨bb :: bl, .cons hb hbl⟩

open Std.Do in
/-- `any`: on bit operands the result reads as the list's disjunction, given
cast-injectivity up to the length — a sum of bits detects zero only below the
characteristic. -/
@[spec] theorem any_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (xs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ xs.length + 1 → k ≤ xs.length + 1 → (j : F) = k → j = k) :
    ⦃⌜True⌝⦄
    Snarky.any (c := Builder V c) xs
    ⦃⇓ r _ => ⌜∀ bl : List Bool, ReadBits V xs bl →
        (↑r : CVar F).val V = bit (bl.any id)⌝⦄ := by
  match xs, hchar with
  | [], _ =>
    simp only [Snarky.any]
    intro nv _ _ bl hbl
    cases hbl
    rfl
  | [a], _ =>
    simp only [Snarky.any]
    intro nv _ _ bl hbl
    obtain - | ⟨hb, hnil⟩ := hbl
    cases hnil
    simpa using hb
  | [a, b], _ =>
    simp only [Snarky.any]
    mvcgen
    intro hr bl hbl
    obtain - | ⟨ha', htl⟩ := hbl
    obtain - | ⟨hb', hnil⟩ := htl
    cases hnil
    simpa using hr _ _ ha' hb'
  | x₁ :: x₂ :: x₃ :: t, hchar =>
    simp only [Snarky.any]
    set xs := x₁ :: x₂ :: x₃ :: t with hxs
    mvcgen
    intro hr bl hbl
    have hsum := sum_bits_val (V := V) hbl
    have hlen := forall₂_length hbl
    have hcount : bl.count true ≤ xs.length + 1 := by
      have := List.count_le_length (a := true) (l := bl)
      omega
    rw [hr, hsum]
    simp only [neqPure]
    show (if (bl.count true : F) = (CVar.const 0).val V then 0 else 1) = _
    by_cases hz : bl.any id = false
    · rw [hz]
      have h0 : bl.count true = 0 := count_true_eq_zero.mpr hz
      rw [h0]
      simp [CVar.val, bit]
    · have hz' : bl.any id = true := by revert hz; cases bl.any id <;> simp
      rw [hz']
      have hne : bl.count true ≠ 0 := by
        intro h0
        rw [count_true_eq_zero.mp h0] at hz'
        cases hz'
      have : (bl.count true : F) ≠ (0 : F) := by
        intro hcast
        exact hne (hchar _ 0 hcount (by omega) (by simpa using hcast))
      simp only [CVar.val]
      rw [if_neg (by simpa using this)]
      rfl

/-- The state and result of `any`'s honest run: `any`'s cases over `orRun` and `neqRun`. -/
def anyRun {F : Type} [Field F] [DecidableEq F] (st : ProverState F) (xs : List (BoolVar F)) :
    ProverState F × BoolVar F :=
  match xs with
  | [] => (st, false_)
  | [a] => (st, a)
  | [a, b] => orRun st a b
  | _ => neqRun st (sum (xs.map BoolVar.toCVar)) (.const 0)

/-- `any`'s honest run lands at `anyRun`. -/
theorem any_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {xs : List (BoolVar F)}
    (st : ProverState F) (hxs : ∀ b ∈ xs, (↑b : CVar F).Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (Snarky.any (c := c) xs) st.nv st.env
      = .ok ((anyRun st xs).1.out (anyRun st xs).2) := by
  match xs with
  | [] => rfl
  | [a] => rfl
  | [a, b] => exact or_run st (hxs a (by simp)) (hxs b (by simp))
  | _ :: _ :: _ :: _ =>
    exact neq_run st (CVar.Scoped.sum (List.forall_mem_map.mpr hxs)) (CVar.scoped_const _ _)

/-- `anyRun` reads, through the bit's expression, as the list's disjunction, given the
cast injectivity the bit-sum needs. -/
theorem anyRun_grants {F : Type} [Field F] [DecidableEq F] {st : ProverState F}
    {xs : List (BoolVar F)} (hxs : ∀ b ∈ xs, (↑b : CVar F).Scoped st)
    (hchar : ∀ j k : Nat, j ≤ xs.length + 1 → k ≤ xs.length + 1 → (j : F) = k → j = k)
    {bl : List Bool} (hbl : ReadBits st.env.toValuation xs bl) :
    Grants F st ((anyRun st xs).1, ↑(anyRun st xs).2) (bit (bl.any id)) := by
  match xs, hchar with
  | [], _ =>
    cases hbl
    exact Grants.fvar (Assignments.Le.refl _) trivial rfl
  | [a], _ =>
    obtain - | ⟨hb, hnil⟩ := hbl
    cases hnil
    exact Grants.fvar (Assignments.Le.refl _) (hxs a (by simp)) (by simpa using hb)
  | [a, b], _ =>
    obtain - | ⟨ha', htl⟩ := hbl
    obtain - | ⟨hb', hnil⟩ := htl
    cases hnil
    simpa using orRun_grants (hxs a (by simp)) (hxs b (by simp)) ha' hb'
  | x₁ :: x₂ :: x₃ :: t, hchar =>
    simp only [anyRun]
    set xs := x₁ :: x₂ :: x₃ :: t with hxs'
    have h := neqRun_grants (CVar.Scoped.sum (List.forall_mem_map.mpr hxs))
      (CVar.scoped_const (st := st) (0 : F))
    refine ⟨h.le, h.scope, ?_⟩
    rw [h.read, sum_bits_val hbl]
    have hlen := forall₂_length hbl
    have hcount : bl.count true ≤ xs.length + 1 := by
      have := List.count_le_length (a := true) (l := bl)
      omega
    simp only [neqPure]
    show (if (bl.count true : F) = (CVar.const 0).val _ then 0 else 1) = _
    by_cases hz : bl.any id = false
    · rw [hz]
      have h0 : bl.count true = 0 := count_true_eq_zero.mpr hz
      rw [h0]
      simp [CVar.val, bit]
    · have hz' : bl.any id = true := by revert hz; cases bl.any id <;> simp
      rw [hz']
      have hne : bl.count true ≠ 0 := by
        intro h0
        rw [count_true_eq_zero.mp h0] at hz'
        cases hz'
      have : (bl.count true : F) ≠ (0 : F) := by
        intro hcast
        exact hne (hchar _ 0 hcount (by omega) (by simpa using hcast))
      simp only [CVar.val]
      rw [if_neg (by simpa using this)]
      rfl

open Std.Do in
/-- `all`: on bit operands the result reads as the list's conjunction, given
cast-injectivity up to the length — the full count is detected only below the
characteristic. -/
@[spec] theorem all_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (xs : List (BoolVar F))
    (hchar : ∀ j k : Nat, j ≤ xs.length + 1 → k ≤ xs.length + 1 → (j : F) = k → j = k) :
    ⦃⌜True⌝⦄
    Snarky.all (c := Builder V c) xs
    ⦃⇓ r _ => ⌜∀ bl : List Bool, ReadBits V xs bl →
        (↑r : CVar F).val V = bit (bl.all id)⌝⦄ := by
  match xs, hchar with
  | [], _ =>
    simp only [Snarky.all]
    intro nv _ _ bl hbl
    cases hbl
    rfl
  | [a], _ =>
    simp only [Snarky.all]
    intro nv _ _ bl hbl
    obtain - | ⟨hb, hnil⟩ := hbl
    cases hnil
    simpa using hb
  | [a, b], _ =>
    simp only [Snarky.all]
    mvcgen
    intro hr bl hbl
    obtain - | ⟨ha', htl⟩ := hbl
    obtain - | ⟨hb', hnil⟩ := htl
    cases hnil
    simpa using hr _ _ ha' hb'
  | x₁ :: x₂ :: x₃ :: t, hchar =>
    simp only [Snarky.all]
    set xs := x₁ :: x₂ :: x₃ :: t with hxs
    mvcgen
    intro hr bl hbl
    have hsum := sum_bits_val (V := V) hbl
    have hlen := forall₂_length hbl
    have hcount : bl.count true ≤ xs.length + 1 := by
      have := List.count_le_length (a := true) (l := bl)
      omega
    rw [hr, hsum]
    simp only [equalsPure]
    show (if (CVar.const (xs.length : F)).val V = (bl.count true : F) then 1 else 0) = _
    by_cases hall : bl.all id = true
    · rw [hall]
      have hc : bl.count true = bl.length := count_true_eq_length.mpr hall
      simp only [CVar.val]
      rw [if_pos (by rw [hc, hlen]), bit_true]
    · have hall' : bl.all id = false := by revert hall; cases bl.all id <;> simp
      rw [hall']
      have hc : bl.count true ≠ bl.length := fun hcc =>
        absurd (count_true_eq_length.mp hcc) (by rw [hall']; simp)
      have hne : ¬((xs.length : F) = (bl.count true : F)) := by
        intro hcast
        have := hchar _ _ (by omega) hcount hcast
        omega
      simp only [CVar.val]
      rw [if_neg hne, bit_false]

/-- The state and result of `all`'s honest run: `all`'s cases over `andRun` and
`equalsRun`. -/
def allRun {F : Type} [Field F] [DecidableEq F] (st : ProverState F) (xs : List (BoolVar F)) :
    ProverState F × BoolVar F :=
  match xs with
  | [] => (st, true_)
  | [a] => (st, a)
  | [a, b] => andRun st a b
  | _ => equalsRun st (.const (xs.length : F)) (sum (xs.map BoolVar.toCVar))

/-- `all`'s honest run lands at `allRun`. -/
theorem all_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {xs : List (BoolVar F)}
    (st : ProverState F) (hxs : ∀ b ∈ xs, (↑b : CVar F).Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (Snarky.all (c := c) xs) st.nv st.env
      = .ok ((allRun st xs).1.out (allRun st xs).2) := by
  match xs with
  | [] => rfl
  | [a] => rfl
  | [a, b] => exact and_run st (hxs a (by simp)) (hxs b (by simp))
  | _ :: _ :: _ :: _ =>
    exact equals_run st (CVar.scoped_const _ _) (CVar.Scoped.sum (List.forall_mem_map.mpr hxs))

/-- `allRun` reads, through the bit's expression, as the list's conjunction, given the
cast injectivity the bit-sum needs. -/
theorem allRun_grants {F : Type} [Field F] [DecidableEq F] {st : ProverState F}
    {xs : List (BoolVar F)} (hxs : ∀ b ∈ xs, (↑b : CVar F).Scoped st)
    (hchar : ∀ j k : Nat, j ≤ xs.length + 1 → k ≤ xs.length + 1 → (j : F) = k → j = k)
    {bl : List Bool} (hbl : ReadBits st.env.toValuation xs bl) :
    Grants F st ((allRun st xs).1, ↑(allRun st xs).2) (bit (bl.all id)) := by
  match xs, hchar with
  | [], _ =>
    cases hbl
    exact Grants.fvar (Assignments.Le.refl _) trivial rfl
  | [a], _ =>
    obtain - | ⟨hb, hnil⟩ := hbl
    cases hnil
    exact Grants.fvar (Assignments.Le.refl _) (hxs a (by simp)) (by simpa using hb)
  | [a, b], _ =>
    obtain - | ⟨ha', htl⟩ := hbl
    obtain - | ⟨hb', hnil⟩ := htl
    cases hnil
    simpa using andRun_grants (hxs a (by simp)) (hxs b (by simp)) ha' hb'
  | x₁ :: x₂ :: x₃ :: t, hchar =>
    simp only [allRun]
    set xs := x₁ :: x₂ :: x₃ :: t with hxs'
    have h := equalsRun_grants (CVar.scoped_const (st := st) (xs.length : F))
      (CVar.Scoped.sum (List.forall_mem_map.mpr hxs))
    refine ⟨h.le, h.scope, ?_⟩
    rw [h.read, sum_bits_val hbl]
    have hlen := forall₂_length hbl
    have hcount : bl.count true ≤ xs.length + 1 := by
      have := List.count_le_length (a := true) (l := bl)
      omega
    simp only [equalsPure]
    show (if (CVar.const (xs.length : F)).val _ = (bl.count true : F) then 1 else 0) = _
    by_cases hall : bl.all id = true
    · rw [hall]
      have hc : bl.count true = bl.length := count_true_eq_length.mpr hall
      simp only [CVar.val]
      rw [if_pos (by rw [hc, hlen]), bit_true]
    · have hall' : bl.all id = false := by revert hall; cases bl.all id <;> simp
      rw [hall']
      have hc : bl.count true ≠ bl.length := fun hcc =>
        absurd (count_true_eq_length.mp hcc) (by rw [hall']; simp)
      have hne : ¬((xs.length : F) = (bl.count true : F)) := by
        intro hcast
        have := hchar _ _ (by omega) hcount hcast
        omega
      simp only [CVar.val]
      rw [if_neg hne, bit_false]

/-! ### `xor` -/

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

open Std.Do in
/-- `xor`: on bit operands the result reads as the xor bit — the constant branches fold
through the guards, the core row pins via `xor_pin`. -/
@[spec] theorem xor_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (a b : BoolVar F) :
    ⦃⌜True⌝⦄
    Snarky.xor (c := Builder V c) a b
    ⦃⇓ r _ => ⌜∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab ^^ bb)⌝⦄ := by
  intro nv _
  cases hA : (↑a : CVar F) <;> cases hB : (↑b : CVar F) <;>
    simp only [Snarky.xor, hA, hB]
  case const.const av bv =>
    intro _ ab bb ha hb
    replace ha : av = bit ab := ha
    replace hb : bv = bit bb := hb
    subst ha; subst hb
    cases ab <;> cases bb <;> simp [circuitVal, bit]
  case const.var av v | const.add av x y | const.scale av k x =>
    split_ifs with h0 h1
    · intro _ ab bb ha hb
      replace ha : av = bit ab := ha
      have hab : ab = false := by
        cases ab
        · rfl
        · exact absurd (ha.symm.trans h0) (by simp [bit])
      subst hab
      rw [← hB] at hb
      simpa using hb
    · intro _ ab bb ha hb
      replace ha : av = bit ab := ha
      have hab : ab = true := by
        cases ab
        · exact absurd (ha ▸ h1) (by simp [bit])
        · rfl
      subst hab
      rw [← hB] at hb
      cases bb <;> simp [Snarky.not, circuitVal, hb]
    · intro hsat ab bb ha hb
      have h := LawfulBasicSystem.holds_r1cs V _ _ _ (hsat _ (List.mem_cons_self ..))
      simp only [circuitVal] at h
      rw [← hA] at ha
      rw [← hB] at hb
      rw [ha, hb] at h
      exact xor_pin h
  case var.const v bv | add.const x y bv | scale.const k x bv =>
    split_ifs with h0 h1
    · intro _ ab bb ha hb
      replace hb : bv = bit bb := hb
      have hbb : bb = false := by
        cases bb
        · rfl
        · exact absurd (hb.symm.trans h0) (by simp [bit])
      subst hbb
      rw [← hA] at ha
      simpa using ha
    · intro _ ab bb ha hb
      replace hb : bv = bit bb := hb
      have hbb : bb = true := by
        cases bb
        · exact absurd (hb ▸ h1) (by simp [bit])
        · rfl
      subst hbb
      rw [← hA] at ha
      cases ab <;> simp [Snarky.not, circuitVal, ha]
    · intro hsat ab bb ha hb
      have h := LawfulBasicSystem.holds_r1cs V _ _ _ (hsat _ (List.mem_cons_self ..))
      simp only [circuitVal] at h
      rw [← hA] at ha
      rw [← hB] at hb
      rw [ha, hb] at h
      exact xor_pin h
  all_goals
    (intro hsat ab bb ha hb
     have h := LawfulBasicSystem.holds_r1cs V _ _ _ (hsat _ (List.mem_cons_self ..))
     simp only [circuitVal] at h
     rw [← hA] at ha
     rw [← hB] at hb
     rw [ha, hb] at h
     exact xor_pin h)

/-- The state and result of `xorCore`'s honest run: the inequality bit, allocated. -/
private def xorCoreRun {F : Type} [Field F] [DecidableEq F] (st : ProverState F)
    (a b : BoolVar F) : ProverState F × BoolVar F :=
  (st.extendMany [bit (decide ((↑a : CVar F).val st.env.toValuation
      ≠ (↑b : CVar F).val st.env.toValuation))],
    .unchecked (.var st.nv))

/-- The state and result of `xor`'s honest run — its guard chain, read at the table. -/
def xorRun {F : Type} [Field F] [DecidableEq F] (st : ProverState F) (a b : BoolVar F) :
    ProverState F × BoolVar F :=
  match (↑a : CVar F), (↑b : CVar F) with
  | .const av, .const bv => (st, .unchecked (.const (if av = bv then 0 else 1)))
  | .const av, _ =>
    if av = 0 then (st, b) else if av = 1 then (st, Snarky.not b) else xorCoreRun st a b
  | _, .const bv =>
    if bv = 0 then (st, a) else if bv = 1 then (st, Snarky.not a) else xorCoreRun st a b
  | _, _ => xorCoreRun st a b

/-- `xorCore`'s honest run on bit operands: one slot, the xor bit, its row accepted. -/
private theorem xorCore_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {a b : BoolVar F} {ab bb : Bool}
    (st : ProverState F) (ha : (↑a : CVar F).Scoped st) (hb : (↑b : CVar F).Scoped st)
    (hav : (↑a : CVar F).val st.env.toValuation = bit ab)
    (hbv : (↑b : CVar F).val st.env.toValuation = bit bb) :
    prove (Checker.holds (F := F) (c := c)) (xorCore (c := c) a b) st.nv st.env
      = .ok ((xorCoreRun st a b).1.out (xorCoreRun st a b).2) := by
  have hle := st.le_extendMany [bit (decide ((↑a : CVar F).val st.env.toValuation
    ≠ (↑b : CVar F).val st.env.toValuation))]
  simp only [xorCore, xorCoreRun, prove_bind]
  rw [prove_witness_run (w := xorWit a b) st
    (.bind (.readCVar ha) fun _ => .bind (.readCVar hb) fun _ => trivial)
    (v := ⟨decide ((↑a : CVar F).val st.env.toValuation ≠ (↑b : CVar F).val st.env.toValuation)⟩)
    (by simp [xorWit, Except.bind])]
  have hvals : (CircuitType.valueToFields (F := F) (var := UnChecked (BoolVar F))
      (⟨decide ((↑a : CVar F).val st.env.toValuation ≠ (↑b : CVar F).val st.env.toValuation)⟩ :
        UnChecked Bool)).toList
      = [bit (decide ((↑a : CVar F).val st.env.toValuation
          ≠ (↑b : CVar F).val st.env.toValuation))] := rfl
  have hvars : CircuitType.fieldsToVar (F := F) (val := UnChecked Bool)
      (mapVec CVar.var (allocRange st.nv (CircuitType.size F (UnChecked Bool))))
      = ⟨.unchecked (.var st.nv)⟩ := rfl
  simp only [hvals, hvars, Except.bind, BoolVar.toCVar_unchecked]
  rw [prove_addConstraint _ (LawfulChecker.holds_r1cs
    (CVar.Scoped.add_ (ha.of_le hle) (ha.of_le hle)) (hb.of_le hle)
    (CVar.Scoped.sub_ (CVar.Scoped.add_ (ha.of_le hle) (hb.of_le hle)) (by simp))
    (by
      simp only [CVar.val_add_, CVar.val_sub_, CVar.val, CVar.val_of_le hle ha,
        CVar.val_of_le hle hb, ProverState.get_extendMany_head]
      rw [hav, hbv]
      cases ab <;> cases bb <;> simp [bit]))]
  rfl

/-- `xor`'s honest run on bit operands lands at `xorRun`. -/
theorem xor_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {a b : BoolVar F} {ab bb : Bool}
    (st : ProverState F) (ha : (↑a : CVar F).Scoped st) (hb : (↑b : CVar F).Scoped st)
    (hav : (↑a : CVar F).val st.env.toValuation = bit ab)
    (hbv : (↑b : CVar F).val st.env.toValuation = bit bb) :
    prove (Checker.holds (F := F) (c := c)) (Snarky.xor (c := c) a b) st.nv st.env
      = .ok ((xorRun st a b).1.out (xorRun st a b).2) := by
  have hcore := xorCore_run (c := c) st ha hb hav hbv
  unfold Snarky.xor xorRun
  cases hA : (↑a : CVar F) <;> cases hB : (↑b : CVar F) <;> (try dsimp only) <;>
    (try split_ifs) <;> first | rfl | exact hcore

/-- `xorRun` reads, through the bit's expression, as the xor bit. -/
theorem xorRun_grants {F : Type} [Field F] [DecidableEq F] {st : ProverState F}
    {a b : BoolVar F} {ab bb : Bool}
    (ha : (↑a : CVar F).Scoped st) (hb : (↑b : CVar F).Scoped st)
    (hav : (↑a : CVar F).val st.env.toValuation = bit ab)
    (hbv : (↑b : CVar F).val st.env.toValuation = bit bb) :
    Grants F st ((xorRun st a b).1, ↑(xorRun st a b).2) (bit (ab ^^ bb)) := by
  have hcore : Grants F st ((xorCoreRun st a b).1, ↑(xorCoreRun st a b).2) (bit (ab ^^ bb)) :=
    Grants.fvar (st.le_extendMany _) (by simp [xorCoreRun, BoolVar.toCVar_unchecked]) (by
      simp only [xorCoreRun, BoolVar.toCVar_unchecked, CVar.val, ProverState.get_extendMany_head,
        hav, hbv]
      cases ab <;> cases bb <;> simp [bit])
  unfold xorRun
  cases hA : (↑a : CVar F) <;> cases hB : (↑b : CVar F) <;> (try dsimp only)
  case const.const av bv =>
    rw [hA] at hav
    rw [hB] at hbv
    simp only [CVar.val] at hav hbv
    subst hav
    subst hbv
    exact Grants.fvar (Assignments.Le.refl _) trivial
      (by cases ab <;> cases bb <;> simp [CVar.val, BoolVar.toCVar_unchecked, bit])
  case const.var av v | const.add av x y | const.scale av k x =>
    rw [hA] at hav
    simp only [CVar.val] at hav
    split_ifs with h0 h1
    · have hab : ab = false := by
        cases ab
        · rfl
        · exact absurd (hav.symm.trans h0) (by simp [bit])
      subst hab
      exact Grants.fvar (Assignments.Le.refl _) hb (by simpa using hbv)
    · have hab : ab = true := by
        cases ab
        · exact absurd (hav ▸ h1) (by simp [bit])
        · rfl
      subst hab
      exact Grants.fvar (Assignments.Le.refl _) (not_scoped hb) (by rw [not_val hbv]; simp)
    · exact hcore
  case var.const v bv | add.const x y bv | scale.const k x bv =>
    rw [hB] at hbv
    simp only [CVar.val] at hbv
    split_ifs with h0 h1
    · have hbb : bb = false := by
        cases bb
        · rfl
        · exact absurd (hbv.symm.trans h0) (by simp [bit])
      subst hbb
      exact Grants.fvar (Assignments.Le.refl _) ha (by simpa using hav)
    · have hbb : bb = true := by
        cases bb
        · exact absurd (hbv ▸ h1) (by simp [bit])
        · rfl
      subst hbb
      exact Grants.fvar (Assignments.Le.refl _) (not_scoped ha) (by rw [not_val hav]; simp)
    · exact hcore
  all_goals exact hcore

/-! ### `select` (the `IfThenElse` field instance) -/

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
/-- `select`: on a bit selector the result reads as the chosen branch — a constant
selector folds to a branch, two constant branches fold to the affine mux, and otherwise
the `r1cs` row pins the choice. -/
@[spec] theorem select_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (b : BoolVar F) (t e : FVar F) :
    ⦃⌜True⌝⦄
    select (c := Builder V c) b t e
    ⦃⇓ r _ => ⌜∀ bb : Bool,
        (↑b : CVar F).val V = bit bb → r.val V = selectPure bb (t.val V) (e.val V)⌝⦄ := by
  intro nv _ hsat bb hb
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
    cases bb <;> simp [selectPure, bit] <;> rfl
  all_goals
    cases t <;> cases e <;> dsimp only at hsat ⊢ <;>
      first
      | (rw [build_selectCore'] at hsat ⊢
         have h := LawfulBasicSystem.holds_r1cs V _ _ _ (hsat _ (List.mem_cons_self ..))
         simp only [circuitVal] at h
         simpa only [selectPure] using select_pin h hb)
      | (show (CVar.add_ (CVar.scale _ _) (CVar.scale_ _ _)).val V = _
         rw [← hB]
         simp only [circuitVal, hb]
         cases bb <;> simp [bit])

/-- The state and result of `selectCore`'s honest run: the chosen value, allocated. -/
private def selectCoreRun {F : Type} [Field F] [DecidableEq F] (st : ProverState F)
    (b : BoolVar F) (t e : FVar F) : ProverState F × FVar F :=
  (st.extendMany [if (↑b : CVar F).val st.env.toValuation = 1 then t.val st.env.toValuation
      else e.val st.env.toValuation],
    .var st.nv)

/-- The state and result of the field `select`'s honest run — its folding, read at the
table. -/
def selectRun {F : Type} [Field F] [DecidableEq F] (st : ProverState F) (b : BoolVar F)
    (t e : FVar F) : ProverState F × FVar F :=
  match (↑b : CVar F) with
  | .const bv => (st, if bv = 1 then t else e)
  | _ =>
    match t, e with
    | .const tv, .const ev =>
      (st, CVar.add_ (.scale tv ↑b) (CVar.scale_ ev (CVar.sub_ (.const 1) ↑b)))
    | t, e => selectCoreRun st b t e

/-- `selectCore`'s honest run on a bit selector: one slot, the chosen value, its row
accepted. -/
private theorem selectCore_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {b : BoolVar F} {t e : FVar F}
    {bb : Bool} (st : ProverState F) (hb : (↑b : CVar F).Scoped st) (ht : t.Scoped st)
    (he : e.Scoped st) (hbv : (↑b : CVar F).val st.env.toValuation = bit bb) :
    prove (Checker.holds (F := F) (c := c)) (selectCore (c := c) b t e) st.nv st.env
      = .ok ((selectCoreRun st b t e).1.out (selectCoreRun st b t e).2) := by
  have hle := st.le_extendMany [if (↑b : CVar F).val st.env.toValuation = 1
    then t.val st.env.toValuation else e.val st.env.toValuation]
  simp only [selectCore, selectCoreRun, prove_bind]
  rw [prove_witness_run (w := selectWit b t e) st
    (.bind (.readCVar hb) fun _ => by split <;> first | exact .readCVar ht | exact .readCVar he)
    (v := if (↑b : CVar F).val st.env.toValuation = 1 then t.val st.env.toValuation
      else e.val st.env.toValuation)
    (by
      simp only [selectWit, AsProver.bind_eq, AsProver.eval_bind, AsProver.eval_readCVar,
        Except.bind]
      split_ifs <;> simp)]
  simp only [valueToFields_fvar_toList, fieldsToVar_fvar_alloc, Except.bind]
  rw [prove_addConstraint _ (LawfulChecker.holds_r1cs (hb.of_le hle)
    (CVar.Scoped.sub_ (ht.of_le hle) (he.of_le hle)) (CVar.Scoped.sub_ (by simp) (he.of_le hle))
    (by
      simp only [CVar.val_sub_, CVar.val, CVar.val_of_le hle hb, CVar.val_of_le hle ht,
        CVar.val_of_le hle he, ProverState.get_extendMany_head]
      rw [hbv]
      cases bb <;> simp [bit]))]
  rfl

/-- The field `select`'s honest run on a bit selector lands at `selectRun`. -/
theorem select_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {b : BoolVar F} {t e : FVar F}
    {bb : Bool} (st : ProverState F) (hb : (↑b : CVar F).Scoped st) (ht : t.Scoped st)
    (he : e.Scoped st) (hbv : (↑b : CVar F).val st.env.toValuation = bit bb) :
    prove (Checker.holds (F := F) (c := c)) (select (c := c) b t e) st.nv st.env
      = .ok ((selectRun st b t e).1.out (selectRun st b t e).2) := by
  have hcore := selectCore_run (c := c) st hb ht he hbv
  show prove _ (match (↑b : CVar F) with
    | .const bv => pure (if bv = 1 then t else e)
    | _ => match t, e with
      | .const tv, .const ev =>
        pure (CVar.add_ (.scale tv ↑b) (CVar.scale_ ev (CVar.sub_ (.const 1) ↑b)))
      | t, e => selectCore b t e) st.nv st.env = _
  unfold selectRun
  cases hB : (↑b : CVar F) <;> (try dsimp only)
  case const bv => rfl
  all_goals cases t <;> cases e <;> (try dsimp only) <;> first | rfl | exact hcore

/-- `selectRun` reads as the chosen branch. -/
theorem selectRun_grants {F : Type} [Field F] [DecidableEq F] {st : ProverState F}
    {b : BoolVar F} {t e : FVar F} {bb : Bool} (hb : (↑b : CVar F).Scoped st)
    (ht : t.Scoped st) (he : e.Scoped st) (hbv : (↑b : CVar F).val st.env.toValuation = bit bb) :
    Grants F st (selectRun st b t e)
      (selectPure bb (t.val st.env.toValuation) (e.val st.env.toValuation)) := by
  have hcore : Grants F st (selectCoreRun st b t e)
      (selectPure bb (t.val st.env.toValuation) (e.val st.env.toValuation)) :=
    Grants.fvar (st.le_extendMany _) (by simp) (by
      simp only [CVar.val, ProverState.get_extendMany_head, hbv, selectPure]
      cases bb <;> simp [bit])
  unfold selectRun
  cases hB : (↑b : CVar F) <;> (try dsimp only)
  case const bv =>
    rw [hB] at hbv
    simp only [CVar.val] at hbv
    subst hbv
    exact Grants.fvar (Assignments.Le.refl _) (by cases bb <;> simp [bit, ht, he])
      (by cases bb <;> simp [bit, selectPure])
  all_goals
    cases t <;> cases e <;> (try dsimp only) <;>
      first
      | exact hcore
      | exact Grants.fvar (Assignments.Le.refl _)
          (CVar.Scoped.add_ (hB ▸ hb)
            (CVar.Scoped.scale_ _ (CVar.Scoped.sub_ (CVar.scoped_const _ _) (hB ▸ hb))))
          (by
            have hbv' := hB ▸ hbv
            simp only [CVar.val_add_, CVar.val_scale_, CVar.val_sub_, CVar.val] at hbv' ⊢
            rw [hbv']
            cases bb <;> simp [bit, selectPure])

end Snarky
