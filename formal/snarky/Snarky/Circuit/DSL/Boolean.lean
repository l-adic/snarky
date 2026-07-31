import Snarky.Circuit.DSL.Field

/-!
# Boolean gadgets

Port of `Snarky.Circuit.DSL.Boolean` (packages/snarky/src/Snarky/Circuit/DSL/Boolean.purs):
the `IfThenElse` selection class with its base instances, the boolean constants, `xor`,
and the array combinators `any`/`all`. The primitives `not`/`and`/`or` live in
`Circuit/DSL/Monad`, their PS home.

Name map (D7): `if_` → `select` (`if` is a Lean keyword; the class keeps its PS name
`IfThenElse`), `xor_` → `xor` (shadows core's `xor`, type-resolved), `any_` → `any`,
`all_` → `all` (likewise), `true_`/`false_` keep their underscores (`true`/`false` are
keywords — the same clash rationale as `CVar`'s smart constructors).

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
`not_eval` (`Circuit/DSL/Monad` — pure gadget, evaluation-level); the `and`/`or`/`xor`
and `if` rows land as `Snarky.and_sound`/`or_sound`/`xor_sound`/`select_sound` and their
completeness twins in `Snarky.Laws`, stated through the `CircuitType Bool` encoding
(`if bb then 1 else 0` — the relation the faithfulness arc composes through); the
`all`/`any` rows' three-plus cases need a cast-injectivity hypothesis (a sum of `n` bits
detects `n` only below the characteristic) and are recorded there as the open obligation
of this step. Fixed-input `decide` examples in `Snarky.Example`.

Public results: none here — the gadget laws live in `Snarky.Laws` (D3/D12);
`xorWit`/`xorCore` are public only as the named internals those laws quantify over.
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
Public only for the gadget laws in `Snarky.Laws`. -/
def selectWit {F : Type} [Field F] [DecidableEq F] (b : BoolVar F) (t e : FVar F) :
    AsProver F F := do
  let bv ← AsProver.readCVar ↑b
  if bv = 1 then AsProver.readCVar t else AsProver.readCVar e

/-- `select`'s witnessing branch for field variables: witness the chosen value `r`, pin
it with `b · (t − e) = r − e`. Split out so the gadget laws in `Snarky.Laws` quantify
over it uniformly. -/
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

/-- `xor`'s witness computation: the inequality bit. Public only for the gadget laws in
`Snarky.Laws`. -/
def xorWit {F : Type} [Add F] [Mul F] [DecidableEq F] (a b : BoolVar F) :
    AsProver F (UnChecked Bool) := do
  let av ← AsProver.readCVar ↑a
  let bv ← AsProver.readCVar ↑b
  pure ⟨decide (av ≠ bv)⟩

/-- `xor`'s witnessing branch: witness the bit at `UnChecked Bool` (the typed
skip-the-check door, verbatim PS) and pin it with `2a · b = a + b − r`. Split out so the
gadget laws in `Snarky.Laws` quantify over it uniformly. -/
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

end Snarky
