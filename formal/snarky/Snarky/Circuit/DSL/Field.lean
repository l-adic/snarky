import Mathlib.Algebra.Field.Defs
import Snarky.Circuit.DSL.Monad
import Snarky.Backend.WP
import Snarky.Backend.Prover

/-!
# Field gadgets

Port of `Snarky.Circuit.DSL.Field` (packages/snarky/src/Snarky/Circuit/DSL/Field.purs):
the field comparison and arithmetic gadgets. The centrepiece is `equals` — an equality
*test* returning a `BoolVar` rather than an assertion, via the standard inverse-or-zero
trick — with `sum`, `pow`, and `square` alongside.

Name map (D7; underscores drop): `mul_` → `mul`, `inv_` → `inv`, `div_` → `div`,
`equals_` → `equals`, `neq_` → `neq`, `sum_` → `sum`, `pow_` → `pow`,
`square_` → `square`. PS parks `mul_`/`inv_`/`div_` in its Monad module to dodge orphan
instances (see `Circuit/DSL/Monad`); here they live with their laws. The PS
action-lifted `equals` variant rides the numeric-tower instances and is not ported
(D8); `pow`'s exponent is `Nat` (PS `Int`, never called negative). The targeted
`Mathlib.Algebra.Field.Defs` import is `inv`'s (D6: `[Field F]`, the weakest fitting
class for an inverse).

Deviations from the PS original (per `formal/docs/snarky-ps-alignment.md`):
- PS witnesses `equals_`'s `{r, zInv}` record through the generic deriving machinery
  (D8, not ported) and retags `r` with a bare `coerce`; here the witness is the pair
  `UnChecked Bool × F` — the typed skip-the-check discipline PS's own `xor_` uses, and
  the `Prod` instances' first Lean consumer. Same one `existsOp` of two variables, same
  order (PS's record rows sort alphabetically: `r`, `zInv`), same absence of `boolean`
  checks — the gadget's two `r1cs` constraints already force booleanity
  (`Snarky.equals_sound`).
- `neq` is `not` after `equals`, as in PS (whose `not` rides the HeytingAlgebra action
  instance, D8); `not` lives with its family in `DSL/Boolean`, above this module, so
  `neq` inlines its one-line retag.
- The `CircuitType F Bool` instance pins `F : Type 0` (`AsProver` payloads share `F`'s
  universe), so the `BoolVar`-returning gadgets are stated for `Type`-sized fields —
  every concrete field is one.

D9 survey (the `snarky-test-utils` Field spec), in the D12 statement form — gadget laws
are stated against the interpreters, never re-derived over the field alone, and live
BESIDE their gadgets (this module imports the backend for exactly that — a deliberate
deviation from the PS import graph, adjacency over layering): the `eq`
rows are `equals_sound`/`equals_complete` below, plus the fixed-input `decide`
examples in `Snarky.Example`; the `mul`/`inv`/`div` rows and `square`/`pow` likewise
(`div_sound`/`pow_sound` and their completeness twins are proved compositionally,
through the bind laws). The `sum` row is `sum_eval` below (`sum` is pure — its
evaluation IS its interpreter semantics). The `negate` row is `Circuit/CVar` algebra
under `reduce_eval`; `seal` is the
`DSL/Utils` follow-on (plan §6). The spec's end-to-end shape — compile, solve against
public inputs, compare with the model function — awaits `Backend/Compile` (walk
step 14).

Public results: the D12 gadget laws beside their gadgets — `mul_sound`/`_complete`,
`inv_sound`/`_complete`, `div_sound`/`_complete`, `equals_sound`/`_complete`,
`neq_sound`/`_complete`, `sum_eval`, `square_sound`/`_complete`, `pow_sound`/`_complete`
— all `roots.txt` entries; the `*Wit`/`*Core` defs are named internals for those laws,
not user API.
-/

namespace Snarky

variable {F c : Type u}

/-! ## The gadgets -/

/-- `mul`'s witness computation: the product of the operands' values. Public only for
the gadget laws. -/
def mulWit [Add F] [Mul F] (x y : FVar F) : AsProver F F := do
  let xv ← AsProver.readCVar x
  let yv ← AsProver.readCVar y
  pure (xv * yv)

/-- `mul`'s witnessing branch: witness the product, pin it with one `r1cs` constraint.
Split out so the gadget laws below quantify over it uniformly. -/
def mulCore [Add F] [Mul F] [BasicSystem F c] (x y : FVar F) : CircuitM F c (FVar F) := do
  let z ← witness (val := F) (mulWit x y)
  addConstraint (BasicSystem.r1cs x y z)
  pure z

/-- Multiply two field variables (PS `mul_`). Constants fold without constraining: two
constants multiply out, and a constant times an expression is `scale_`. Otherwise the
product is witnessed and pinned with one `r1cs` constraint. -/
def mul [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c] (x y : FVar F) :
    CircuitM F c (FVar F) :=
  match x, y with
  | .const a, .const b => pure (.const (a * b))
  | .const a, y => pure (CVar.scale_ a y)
  | x, .const b => pure (CVar.scale_ b x)
  | x, y => mulCore x y

/-- `inv`'s witness computation: the inverse, failing on zero (PS `DivisionByZero`).
Public only for the gadget laws. -/
def invWit [Field F] [DecidableEq F] (x : FVar F) : AsProver F F := do
  let xv ← AsProver.readCVar x
  if xv = 0 then AsProver.throw "inv: division by zero"
  else pure xv⁻¹

/-- `inv`'s witnessing branch: witness the inverse, pin it with `x · xInv = 1`. Split
out so the gadget laws below quantify over it uniformly. -/
def invCore [Field F] [DecidableEq F] [BasicSystem F c] (x : FVar F) :
    CircuitM F c (FVar F) := do
  let xInv ← witness (val := F) (invWit x)
  addConstraint (BasicSystem.r1cs x xInv (.const 1))
  pure xInv

/-- Invert a field variable: witness the inverse, pin it with `x · xInv = 1` (PS `inv_`).
A constant folds to its constant inverse — total where PS crashes on the constant zero
(Lean's `0⁻¹ = 0`); either way no constraint is emitted. During a prover run a zero
argument fails the witness computation, as in PS (`DivisionByZero`). -/
def inv [Field F] [DecidableEq F] [BasicSystem F c] (x : FVar F) : CircuitM F c (FVar F) :=
  match x with
  | .const a => pure (.const a⁻¹)
  | x => invCore x

/-- Divide field variables: `x · y⁻¹`, one `inv` then one `mul` (PS `div_`). A zero
divisor fails in `inv`'s witness computation. -/
def div [Field F] [DecidableEq F] [BasicSystem F c] (x y : FVar F) :
    CircuitM F c (FVar F) := do
  let yInv ← inv y
  mul x yInv

/-- `equals`'s witness computation: the claimed answer bit and the inverse-or-zero.
Public only for the gadget laws. -/
def equalsWit {F : Type} [Field F] [DecidableEq F] (z : CVar F) :
    AsProver F (UnChecked Bool × F) := do
  let zv ← AsProver.readCVar z
  pure (if zv = 0 then (⟨true⟩, 0) else (⟨false⟩, zv⁻¹))

/-- `equals`'s witnessing branch, over the precomputed difference `z` — split out so the
gadget laws below quantify over it uniformly. Public only for those laws. -/
def equalsCore {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (z : CVar F) :
    CircuitM F c (BoolVar F) := do
  let rz ← witness (val := UnChecked Bool × F) (equalsWit z)
  let r := rz.1.val
  addConstraint (BasicSystem.r1cs ↑r z (.const 0))
  addConstraint (BasicSystem.r1cs rz.2 z (CVar.sub_ (.const 1) ↑r))
  pure r

/-- Equality test returning a boolean variable (PS `equals_`). A constant difference
folds to the constant answer. Otherwise, with `z = a − b`: witness the pair `(r, zInv)`
— `r` the claimed answer at `UnChecked Bool`, `zInv` the inverse or zero — and constrain
`r · z = 0` and `zInv · z = 1 − r`. The pair forces `r = (a == b)` — in particular `r`
is boolean (`Snarky.equals_sound`), which is why the witness may skip the `boolean`
check. -/
def equals {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (a b : FVar F) :
    CircuitM F c (BoolVar F) :=
  match CVar.sub_ a b with
  | .const f => pure (.unchecked (.const (if f = 0 then 1 else 0)))
  | z => equalsCore z

/-- Negated equality test (PS `neq_ = not <<< equals_`): the negated `equals` bit. The
negation is `not`'s retag `1 − r` inlined: `not` lives with its family in
`DSL/Boolean`, which imports this module. -/
def neq {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (a b : FVar F) :
    CircuitM F c (BoolVar F) := do
  let r ← equals a b
  pure (.unchecked (CVar.sub_ (.const 1) ↑r))

/-- Sum a list of field variables — pure, no constraints (PS `sum_`, which folds an
`Array` the same way): `add_` over the list from `const 0`. -/
def sum [Add F] [Zero F] (xs : List (FVar F)) : FVar F :=
  xs.foldl CVar.add_ (.const 0)

/-- Fuel-indexed body of `pow`, structural on the fuel so the definition kernel-reduces
(`decide`-friendly; PS recurses on `n / 2` directly). The fuel-exhausted branch is
unreachable: `pow` seeds fuel `n`, and the exponent at least halves each step. Public
only for the gadget laws. -/
def powGo [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c] :
    Nat → FVar F → Nat → CircuitM F c (FVar F)
  | _, _, 0 => pure (.const 1)
  | _, x, 1 => pure x
  | 0, x, _ => pure x
  | fuel + 1, x, n => do
    let sq ← mul x x
    let y ← powGo fuel sq (n / 2)
    if n % 2 = 0 then pure y else mul x y

/-- `x ^ n` by repeated squaring, in PS `pow_`'s recursion and constraint order: square,
recurse on `n / 2`, and multiply by `x` once more when `n` is odd. On a constant every
step goes through `mul`'s folding, so no constraints are emitted. -/
def pow [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c]
    (x : FVar F) (n : Nat) : CircuitM F c (FVar F) :=
  powGo n x n

/-- `square`'s witness computation: the square of the operand's value. Public only for
the gadget laws. -/
def squareWit [Add F] [Mul F] (x : FVar F) : AsProver F F := do
  let xv ← AsProver.readCVar x
  pure (xv * xv)

/-- `square`'s witnessing branch: witness the square, pin it with one `square`
constraint. Split out so the gadget laws below quantify over it uniformly. -/
def squareCore [Add F] [Mul F] [BasicSystem F c] (x : FVar F) : CircuitM F c (FVar F) := do
  let z ← witness (val := F) (squareWit x)
  addConstraint (BasicSystem.square x z)
  pure z

/-- Square a field variable via the dedicated `square` constraint rather than `r1cs`
(PS `square_`, matching OCaml's `Checked.square`). A constant folds. -/
def square [Add F] [Mul F] [BasicSystem F c] (x : FVar F) : CircuitM F c (FVar F) :=
  match x with
  | .const f => pure (.const (f * f))
  | x => squareCore x

/-! ## The sum law (D9: the sum spec row) -/

private theorem sum_go [AddMonoid F] [Mul F] {env : Assignments F} :
    ∀ {xs : List (CVar F)} {vals : List F} {acc : CVar F} {a : F},
      xs.map (CVar.eval · env) = vals.map .ok → acc.eval env = .ok a →
      (xs.foldl CVar.add_ acc).eval env = .ok (a + vals.sum) := by
  intro xs
  induction xs with
  | nil =>
    intro vals acc a hmap hacc
    cases vals with
    | nil => simpa using hacc
    | cons v vs => cases hmap
  | cons x xs ih =>
    intro vals acc a hmap hacc
    cases vals with
    | nil => cases hmap
    | cons v vs =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hx, hrest⟩ := hmap
      have hstep : (CVar.add_ acc x).eval env = .ok (a + v) := by
        rw [CVar.eval_add_]
        simp only [CVar.eval, hacc, hx]
      simpa [add_assoc] using ih hrest hstep

/-- `sum` evaluates to the sum of its operands' values: if each `xᵢ` evaluates to `vᵢ`
under `env`, the folded expression evaluates to `Σ vᵢ`. -/
theorem sum_eval [AddMonoid F] [Mul F] {env : Assignments F} {xs : List (CVar F)}
    {vals : List F} (h : xs.map (CVar.eval · env) = vals.map .ok) :
    (sum xs).eval env = .ok vals.sum := by
  have h0 : (CVar.const (0 : F)).eval env = .ok 0 := rfl
  simpa [sum] using sum_go h h0

/-! ## The gadget laws (D12)

Stated against `build`/`prove` over the reference `Basic` backend — soundness quantifies
over EVERY satisfying assignment, completeness runs the honest prover, each direct gadget
anchored by a definitional shape lemma of its built circuit. The laws for `DSL/Monad`'s
gadgets (`mul`/`inv`/`div`) live here with their gadget family: the interpreters import
`DSL/Monad`, so its own file cannot state interpreter theorems (a cycle, not a style
choice). -/

/-! ### `equals` (Circuit/DSL/Field) -/

/-- The field engine of `equals` soundness: `r · z = 0` and `zInv · z = 1 − r` pin `r`
to the equality bit. -/
private theorem equals_pin {F : Type} [Field F] [DecidableEq F] {r zInv z : F}
    (h₁ : r * z = 0) (h₂ : zInv * z = 1 - r) : r = if z = 0 then 1 else 0 := by
  by_cases hz : z = 0
  · subst hz
    rw [mul_zero] at h₂
    rw [if_pos rfl, ← sub_eq_zero.mp h₂.symm]
  · rw [if_neg hz]
    rcases mul_eq_zero.mp h₁ with hr | h0
    · exact hr
    · exact absurd h0 hz

/-- The field engine of `equals` completeness: the honest witness values satisfy both
constraints. -/
private theorem equals_checks {F : Type} [Field F] [DecidableEq F] (zv : F) :
    (if zv = 0 then (1 : F) else 0) * zv = 0 ∧
    (if zv = 0 then (0 : F) else zv⁻¹) * zv = 1 - (if zv = 0 then (1 : F) else 0) := by
  by_cases hz : zv = 0
  · simp [hz]
  · simp [hz]

/-- What `equalsCore` builds, pinned definitionally: two fresh variables (`r` at `nv`,
`zInv` at `nv + 1`) and the two `r1cs` constraints, the answer bit as result — the
anti-drift anchor both `equals` laws read off. -/
private theorem build_equalsCore {F : Type} [Field F] [DecidableEq F] (z : CVar F)
    (nv : Nat) :
    build (equalsCore (c := Basic F) z) nv =
      ⟨.unchecked (.var nv), nv + 2,
        [.r1cs (.var nv) z (.const 0),
         .r1cs (.var (nv + 1)) z (CVar.sub_ (.const 1) (.var nv))]⟩ := rfl

/-- `equalsCore` soundness: any satisfying assignment pins the answer bit. -/
private theorem equalsCore_sound {F : Type} [Field F] [DecidableEq F] {z : CVar F}
    {nv : Nat} {env : Assignments F} {zv : F} (hz : z.eval env = .ok zv)
    (hsat : ∀ con ∈ (build (equalsCore (c := Basic F) z) nv).constraints,
      con.holds env = true) :
    (build (equalsCore (c := Basic F) z) nv).result.toCVar.eval env
      = .ok (if zv = 0 then 1 else 0) := by
  rw [build_equalsCore] at hsat ⊢
  rw [List.forall_mem_cons, List.forall_mem_cons] at hsat
  obtain ⟨h₁, h₂, -⟩ := hsat
  cases hnv : env nv with
  | none => simp [Basic.holds, CVar.eval, hnv] at h₁
  | some rv =>
    cases hnv1 : env (nv + 1) with
    | none => simp [Basic.holds, CVar.eval, hnv1] at h₂
    | some iv =>
      have hvnv : (CVar.var nv).eval env = .ok rv := by simp [CVar.eval, hnv]
      have hsub : (CVar.sub_ (.const 1) (.var nv)).eval env = .ok (1 - rv) :=
        CVar.eval_sub_ rfl hvnv
      simp only [Basic.holds, CVar.eval, hnv, hnv1, hz, hsub, decide_eq_true_eq] at h₁ h₂
      show (CVar.var nv).eval env = _
      rw [hvnv, equals_pin h₁ h₂]

/-- The honest `equalsCore` run, from any witness values satisfying the two constraint
identities: the prover succeeds, assigning `r` at `nv` and `zInv` at `nv + 1`. -/
private theorem equalsCore_run {F : Type} [Field F] [DecidableEq F] {z : CVar F}
    {nv : Nat} {env : Assignments F} {zv v₁ v₂ : F} (hz : z.eval env = .ok zv)
    (hfresh : env.FreshFrom nv)
    (hwit : (equalsWit z env).map
        (CircuitType.valueToFields (F := F) (val := UnChecked Bool × F))
      = .ok ⟨#[v₁, v₂], rfl⟩)
    (hc₁ : v₁ * zv = 0) (hc₂ : v₂ * zv = 1 - v₁) :
    prove Basic.holds (equalsCore (c := Basic F) z) nv env
      = .ok ⟨.unchecked (.var nv), nv + 2, (env.extend nv v₁).extend (nv + 1) v₂⟩ := by
  have hnv : env nv = none := hfresh nv (Nat.le_refl nv)
  have hnv1 : (env.extend nv v₁) (nv + 1) = none := by
    simp [Assignments.extend, hfresh (nv + 1) (Nat.le_succ nv)]
  set env₂ : Assignments F := (env.extend nv v₁).extend (nv + 1) v₂ with henv₂
  have henv₂nv : env₂ nv = some v₁ := by
    simp [henv₂, Assignments.extend]
  have henv₂nv1 : env₂ (nv + 1) = some v₂ := by
    simp [henv₂, Assignments.extend]
  have hle : env.Le env₂ := by
    intro v x hv
    simp only [henv₂, Assignments.extend]
    split
    · next h => rw [h, hfresh (nv + 1) (Nat.le_succ nv)] at hv; cases hv
    · split
      · next h => rw [h, hnv] at hv; cases hv
      · exact hv
  have hzeval₂ : z.eval env₂ = .ok zv := CVar.eval_le hle hz
  have hext : env.extendPairs
      ((allocRange nv 2).toList.zip (⟨#[v₁, v₂], rfl⟩ : Vector F 2).toList)
      = .ok env₂ := by
    show env.extendPairs [(nv, v₁), (nv + 1, v₂)] = .ok env₂
    simp [Assignments.extendPairs, hnv, hnv1, henv₂]
  have hch₁ : Basic.holds (.r1cs (.var nv) z (.const 0)) env₂ = true := by
    simp [Basic.holds, CVar.eval, henv₂nv, hzeval₂, hc₁]
  have hch₂ : Basic.holds
      (.r1cs (.var (nv + 1)) z (CVar.sub_ (.const 1) (.var nv))) env₂ = true := by
    have hsub : (CVar.sub_ (.const 1) (.var nv)).eval env₂ = .ok (1 - v₁) :=
      CVar.eval_sub_ rfl (by simp [CVar.eval, henv₂nv])
    simp [Basic.holds, CVar.eval, henv₂nv1, hzeval₂, hsub, hc₂]
  show prove Basic.holds (.existsOp 2 (fun e => (equalsWit z e).map _) _) nv env = _
  simp only [prove, hwit, hext]
  show prove Basic.holds
    (.addConstraintOp (.r1cs (.var nv) z (.const 0))
      (.addConstraintOp (.r1cs (.var (nv + 1)) z (CVar.sub_ (.const 1) (.var nv)))
        (.pure (BoolVar.unchecked (.var nv))))) (nv + 2) env₂ = _
  simp only [prove, hch₁, hch₂, if_true]

/-- `equalsCore` completeness: on a fresh-from-`nv` assignment that evaluates `z`, the
honest prover run succeeds and the answer bit is correct. -/
private theorem equalsCore_complete {F : Type} [Field F] [DecidableEq F] {z : CVar F}
    {nv : Nat} {env : Assignments F} {zv : F} (hz : z.eval env = .ok zv)
    (hfresh : env.FreshFrom nv) :
    ∃ out, prove Basic.holds (equalsCore (c := Basic F) z) nv env = .ok out ∧
      out.result.toCVar.eval out.assignments = .ok (if zv = 0 then 1 else 0) ∧
      out.assignments.FreshFrom out.nextVar := by
  obtain ⟨hc₁, hc₂⟩ := equals_checks (F := F) zv
  have hwit : (equalsWit z env).map
      (CircuitType.valueToFields (F := F) (val := UnChecked Bool × F))
      = .ok ⟨#[if zv = 0 then 1 else 0, if zv = 0 then 0 else zv⁻¹], rfl⟩ := by
    by_cases hzv : zv = 0 <;>
      simp [equalsWit, AsProver.readCVar, hz, hzv, Bind.bind, ReaderT.bind, Except.bind,
        Pure.pure, ReaderT.pure, Except.pure, Except.map, CircuitType.valueToFields, bit]
  refine ⟨_, equalsCore_run hz hfresh hwit hc₁ hc₂, ?_, ?_⟩
  · show (CVar.var nv).eval _ = _
    simp [CVar.eval, Assignments.extend]
  · intro v hv
    replace hv : nv + 2 ≤ v := hv
    have h1 : v ≠ nv + 1 := by omega
    have h0 : v ≠ nv := by omega
    show ((env.extend nv _).extend (nv + 1) _) v = none
    simp [Assignments.extend, h1, h0, hfresh v (by omega)]

/-- **`equals` soundness** (D12): for every assignment satisfying the constraints
`equals a b` emits — adversarial witnesses included — the result evaluates to the
equality bit of the inputs' values. In particular the result is boolean, which is what
lets the gadget skip the `boolean` check. -/
theorem equals_sound {F : Type} [Field F] [DecidableEq F] {a b : FVar F} {nv : Nat}
    {env : Assignments F} {av bv : F}
    (hsat : ∀ con ∈ (build (equals (c := Basic F) a b) nv).constraints,
      con.holds env = true)
    (ha : a.eval env = .ok av) (hb : b.eval env = .ok bv) :
    (build (equals (c := Basic F) a b) nv).result.toCVar.eval env
      = .ok (if av = bv then 1 else 0) := by
  have hz : (CVar.sub_ a b).eval env = .ok (av - bv) := CVar.eval_sub_ ha hb
  have hiff : ((av - bv = 0) : Prop) = (av = bv) := propext sub_eq_zero
  unfold equals at hsat ⊢
  cases hcase : CVar.sub_ a b with
  | const f =>
    rw [hcase] at hz
    have hf : f = av - bv := by simpa [CVar.eval] using hz
    subst hf
    show Except.ok _ = _
    simp [sub_eq_zero]
  | var v =>
    rw [hcase] at hz hsat
    simpa only [hiff] using equalsCore_sound hz hsat
  | add x y =>
    rw [hcase] at hz hsat
    simpa only [hiff] using equalsCore_sound hz hsat
  | scale k x =>
    rw [hcase] at hz hsat
    simpa only [hiff] using equalsCore_sound hz hsat

/-- **`equals` completeness** (D12): on any assignment that evaluates the inputs and is
unassigned from `nv` up, the honest prover run of `equals a b` succeeds and its result
evaluates, under the final assignment, to the equality bit. -/
theorem equals_complete {F : Type} [Field F] [DecidableEq F] {a b : FVar F} {nv : Nat}
    {env : Assignments F} {av bv : F}
    (hfresh : env.FreshFrom nv)
    (ha : a.eval env = .ok av) (hb : b.eval env = .ok bv) :
    ∃ out, prove Basic.holds (equals (c := Basic F) a b) nv env = .ok out ∧
      out.result.toCVar.eval out.assignments = .ok (if av = bv then 1 else 0) ∧
      out.assignments.FreshFrom out.nextVar := by
  have hz : (CVar.sub_ a b).eval env = .ok (av - bv) := CVar.eval_sub_ ha hb
  have hiff : ((av - bv = 0) : Prop) = (av = bv) := propext sub_eq_zero
  unfold equals
  cases hcase : CVar.sub_ a b with
  | const f =>
    rw [hcase] at hz
    have hf : f = av - bv := by simpa [CVar.eval] using hz
    subst hf
    refine ⟨_, rfl, ?_, hfresh⟩
    show Except.ok _ = _
    simp [sub_eq_zero]
  | var v =>
    rw [hcase] at hz
    simpa only [hiff] using equalsCore_complete hz hfresh
  | add x y =>
    rw [hcase] at hz
    simpa only [hiff] using equalsCore_complete hz hfresh
  | scale k x =>
    rw [hcase] at hz
    simpa only [hiff] using equalsCore_complete hz hfresh

/-! ### `neq` — composed from `equals` -/

/-- **`neq` soundness** (D12): the negated equality bit. -/
theorem neq_sound {F : Type} [Field F] [DecidableEq F] {a b : FVar F} {nv : Nat}
    {env : Assignments F} {av bv : F}
    (hsat : ∀ con ∈ (build (neq (c := Basic F) a b) nv).constraints,
      con.holds env = true)
    (ha : a.eval env = .ok av) (hb : b.eval env = .ok bv) :
    (build (neq (c := Basic F) a b) nv).result.toCVar.eval env
      = .ok (if av = bv then 0 else 1) := by
  unfold neq at hsat ⊢
  rw [build_bind] at hsat ⊢
  have h₁ := equals_sound (fun con h => hsat con (List.mem_append_left _ h)) ha hb
  show (CVar.sub_ (.const 1) _).eval env = _
  rw [CVar.eval_sub_ rfl h₁]
  by_cases h : av = bv <;> simp [h]

/-- **`neq` completeness** (D12). -/
theorem neq_complete {F : Type} [Field F] [DecidableEq F] {a b : FVar F} {nv : Nat}
    {env : Assignments F} {av bv : F}
    (hfresh : env.FreshFrom nv)
    (ha : a.eval env = .ok av) (hb : b.eval env = .ok bv) :
    ∃ out, prove Basic.holds (neq (c := Basic F) a b) nv env = .ok out ∧
      out.result.toCVar.eval out.assignments = .ok (if av = bv then 0 else 1) ∧
      out.assignments.FreshFrom out.nextVar := by
  unfold neq
  rw [prove_bind]
  obtain ⟨o₁, hr₁, he₁, hf₁⟩ := equals_complete hfresh ha hb
  rw [hr₁]
  refine ⟨⟨.unchecked (CVar.sub_ (.const 1) ↑o₁.result), o₁.nextVar, o₁.assignments⟩,
    rfl, ?_, hf₁⟩
  show (CVar.sub_ (.const 1) _).eval _ = _
  rw [CVar.eval_sub_ rfl he₁]
  by_cases h : av = bv <;> simp [h]

/-! ### `mul` -/

/-- What `mulCore` builds: one fresh variable, one `r1cs` constraint. -/
private theorem build_mulCore {F : Type u} [Add F] [Mul F] (x y : FVar F) (nv : Nat) :
    build (mulCore (c := Basic F) x y) nv = ⟨.var nv, nv + 1, [.r1cs x y (.var nv)]⟩ :=
  rfl

/-- `mulCore` soundness: the constraint pins the fresh variable to the product. -/
private theorem mulCore_sound {F : Type u} [Add F] [CommMonoidWithZero F] [DecidableEq F]
    {x y : FVar F} {nv : Nat} {env : Assignments F} {xv yv : F}
    (hsat : ∀ con ∈ (build (mulCore (c := Basic F) x y) nv).constraints,
      con.holds env = true)
    (hx : x.eval env = .ok xv) (hy : y.eval env = .ok yv) :
    (build (mulCore (c := Basic F) x y) nv).result.eval env = .ok (xv * yv) := by
  rw [build_mulCore] at hsat ⊢
  have h₁ := hsat _ (List.mem_cons_self ..)
  cases hnv : env nv with
  | none => simp [Basic.holds, CVar.eval, hnv] at h₁
  | some zv =>
    simp only [Basic.holds, CVar.eval, hx, hy, hnv, decide_eq_true_eq] at h₁
    show (CVar.var nv).eval env = _
    simp [CVar.eval, hnv, ← h₁]

/-- The honest `mulCore` run: the prover succeeds, assigning the product at `nv`. -/
private theorem mulCore_run {F : Type u} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {x y : FVar F} {nv : Nat} {env : Assignments F} {xv yv : F}
    (hx : x.eval env = .ok xv) (hy : y.eval env = .ok yv)
    (hfresh : env.FreshFrom nv) :
    prove Basic.holds (mulCore (c := Basic F) x y) nv env
      = .ok ⟨.var nv, nv + 1, env.extend nv (xv * yv)⟩ := by
  have hnv : env nv = none := hfresh nv (Nat.le_refl nv)
  have hle : env.Le (env.extend nv (xv * yv)) := by
    intro v w hv
    simp only [Assignments.extend]
    split
    · next h => rw [h, hnv] at hv; cases hv
    · exact hv
  have hw : mulWit x y env = .ok (xv * yv) := by
    simp [mulWit, AsProver.readCVar, hx, hy, Bind.bind, ReaderT.bind, Except.bind,
      Pure.pure, ReaderT.pure, Except.pure]
  have hch : Basic.holds (.r1cs x y (.var nv)) (env.extend nv (xv * yv)) = true := by
    simp [Basic.holds, CVar.eval, CVar.eval_le hle hx, CVar.eval_le hle hy,
      Assignments.extend]
  exact prove_witnessCore hw hfresh hch

/-- **`mul` soundness** (D12): any satisfying assignment pins the result to the product
— the constant-folding fast paths included, which is the fold-preservation content. -/
theorem mul_sound {F : Type u} [Add F] [CommMonoidWithZero F] [DecidableEq F]
    {x y : FVar F} {nv : Nat} {env : Assignments F} {xv yv : F}
    (hsat : ∀ con ∈ (build (mul (c := Basic F) x y) nv).constraints,
      con.holds env = true)
    (hx : x.eval env = .ok xv) (hy : y.eval env = .ok yv) :
    (build (mul (c := Basic F) x y) nv).result.eval env = .ok (xv * yv) := by
  unfold mul at hsat ⊢
  cases x <;> cases y <;>
    first
    | (simp only [CVar.eval, Except.ok.injEq] at hx hy; subst hx; subst hy; rfl)
    | (simp only [CVar.eval, Except.ok.injEq] at hx; subst hx;
       exact CVar.eval_scale_ hy _)
    | (simp only [CVar.eval, Except.ok.injEq] at hy; subst hy;
       simpa [mul_comm] using CVar.eval_scale_ hx _)
    | exact mulCore_sound hsat hx hy

/-- **`mul` completeness** (D12): the honest prover run succeeds, computes the product,
and re-establishes freshness. -/
theorem mul_complete {F : Type u} [Add F] [CommMonoidWithZero F] [DecidableEq F]
    {x y : FVar F} {nv : Nat} {env : Assignments F} {xv yv : F}
    (hfresh : env.FreshFrom nv)
    (hx : x.eval env = .ok xv) (hy : y.eval env = .ok yv) :
    ∃ out, prove Basic.holds (mul (c := Basic F) x y) nv env = .ok out ∧
      out.result.eval out.assignments = .ok (xv * yv) ∧
      out.assignments.FreshFrom out.nextVar := by
  unfold mul
  cases x <;> cases y <;>
    first
    | (refine ⟨_, rfl, ?_, hfresh⟩
       simp only [CVar.eval, Except.ok.injEq] at hx hy
       subst hx; subst hy; rfl)
    | (refine ⟨_, rfl, ?_, hfresh⟩
       simp only [CVar.eval, Except.ok.injEq] at hx
       subst hx; exact CVar.eval_scale_ hy _)
    | (refine ⟨_, rfl, ?_, hfresh⟩
       simp only [CVar.eval, Except.ok.injEq] at hy
       subst hy; simpa [mul_comm] using CVar.eval_scale_ hx _)
    | (refine ⟨_, mulCore_run hx hy hfresh, ?_, ?_⟩
       · show (CVar.var nv).eval _ = _
         simp [CVar.eval, Assignments.extend]
       · intro v hv
         replace hv : nv + 1 ≤ v := hv
         have h0 : v ≠ nv := by omega
         show (env.extend nv _) v = none
         simp [Assignments.extend, h0, hfresh v (by omega)])

/-! ### `inv` -/

/-- What `invCore` builds: one fresh variable, the constraint `x · xInv = 1`. -/
private theorem build_invCore {F : Type u} [Field F] [DecidableEq F] (x : FVar F)
    (nv : Nat) :
    build (invCore (c := Basic F) x) nv =
      ⟨.var nv, nv + 1, [.r1cs x (.var nv) (.const 1)]⟩ := rfl

/-- `invCore` soundness: the constraint pins the fresh variable to the inverse (and, not
stated here, forces `xv ≠ 0`). -/
private theorem invCore_sound {F : Type u} [Field F] [DecidableEq F]
    {x : FVar F} {nv : Nat} {env : Assignments F} {xv : F}
    (hsat : ∀ con ∈ (build (invCore (c := Basic F) x) nv).constraints,
      con.holds env = true)
    (hx : x.eval env = .ok xv) :
    (build (invCore (c := Basic F) x) nv).result.eval env = .ok xv⁻¹ := by
  rw [build_invCore] at hsat ⊢
  have h₁ := hsat _ (List.mem_cons_self ..)
  cases hnv : env nv with
  | none => simp [Basic.holds, CVar.eval, hnv] at h₁
  | some iv =>
    simp only [Basic.holds, CVar.eval, hx, hnv, decide_eq_true_eq] at h₁
    show (CVar.var nv).eval env = _
    simp [CVar.eval, hnv, inv_eq_of_mul_eq_one_right h₁]

/-- The honest `invCore` run on a nonzero operand. -/
private theorem invCore_run {F : Type u} [Field F] [DecidableEq F]
    {x : FVar F} {nv : Nat} {env : Assignments F} {xv : F}
    (hx : x.eval env = .ok xv) (hxv : xv ≠ 0) (hfresh : env.FreshFrom nv) :
    prove Basic.holds (invCore (c := Basic F) x) nv env
      = .ok ⟨.var nv, nv + 1, env.extend nv xv⁻¹⟩ := by
  have hnv : env nv = none := hfresh nv (Nat.le_refl nv)
  have hle : env.Le (env.extend nv xv⁻¹) := by
    intro v w hv
    simp only [Assignments.extend]
    split
    · next h => rw [h, hnv] at hv; cases hv
    · exact hv
  have hw : invWit x env = .ok xv⁻¹ := by
    simp [invWit, AsProver.readCVar, hx, hxv, Bind.bind, ReaderT.bind, Except.bind,
      Pure.pure, ReaderT.pure, Except.pure]
  have hch : Basic.holds (.r1cs x (.var nv) (.const 1)) (env.extend nv xv⁻¹) = true := by
    simp [Basic.holds, CVar.eval, CVar.eval_le hle hx, Assignments.extend,
      mul_inv_cancel₀ hxv]
  exact prove_witnessCore hw hfresh hch

/-- **`inv` soundness** (D12): any satisfying assignment pins the result to the field
inverse. On the witnessing branch the constraint additionally forces the operand
nonzero; the constant branch is total via `0⁻¹ = 0`, so the law states the evaluation
alone. -/
theorem inv_sound {F : Type u} [Field F] [DecidableEq F]
    {x : FVar F} {nv : Nat} {env : Assignments F} {xv : F}
    (hsat : ∀ con ∈ (build (inv (c := Basic F) x) nv).constraints, con.holds env = true)
    (hx : x.eval env = .ok xv) :
    (build (inv (c := Basic F) x) nv).result.eval env = .ok xv⁻¹ := by
  unfold inv at hsat ⊢
  cases x <;>
    first
    | (simp only [CVar.eval, Except.ok.injEq] at hx; subst hx; rfl)
    | exact invCore_sound hsat hx

/-- **`inv` completeness** (D12): on a nonzero operand the honest prover run succeeds,
computes the inverse, and re-establishes freshness. -/
theorem inv_complete {F : Type u} [Field F] [DecidableEq F]
    {x : FVar F} {nv : Nat} {env : Assignments F} {xv : F}
    (hfresh : env.FreshFrom nv) (hx : x.eval env = .ok xv) (hxv : xv ≠ 0) :
    ∃ out, prove Basic.holds (inv (c := Basic F) x) nv env = .ok out ∧
      out.result.eval out.assignments = .ok xv⁻¹ ∧
      out.assignments.FreshFrom out.nextVar := by
  unfold inv
  cases x <;>
    first
    | (refine ⟨_, rfl, ?_, hfresh⟩
       simp only [CVar.eval, Except.ok.injEq] at hx
       subst hx; rfl)
    | (refine ⟨_, invCore_run hx hxv hfresh, ?_, ?_⟩
       · show (CVar.var nv).eval _ = _
         simp [CVar.eval, Assignments.extend]
       · intro v hv
         replace hv : nv + 1 ≤ v := hv
         have h0 : v ≠ nv := by omega
         show (env.extend nv _) v = none
         simp [Assignments.extend, h0, hfresh v (by omega)])

open Std.Do in
/-- **`inv` soundness triple**: `inv x` computes the operand's field inverse — the
witnessing row forces it; the constant branch is total via `0⁻¹ = 0`. Generic over
any lawful backend. -/
@[spec] theorem inv_spec {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x : FVar F) (Q : PostCond (FVar F) (.arg (Valuation F) (.arg Nat .pure))) :
    ⦃Computes (fun V rv => rv = (x.val V)⁻¹) Q⦄
    inv (c := c) x
    ⦃Q⦄ := by
  intro V nv hpre
  cases x <;> simp only [inv]
  case const a =>
    intro _
    exact hpre (.const a⁻¹) nv rfl
  all_goals
    (intro hsat
     have h := LawfulBasicSystem.holds_r1cs V _ _ _ (hsat _ (List.mem_cons_self ..))
     exact hpre (.var nv) (nv + 1) (inv_eq_of_mul_eq_one_right (by simpa using h)).symm)

open Std.Do in
/-- **`inv` completeness triple** (prover reading): on a nonzero operand the run
succeeds and the result reads as the inverse in the final table. -/
@[spec] theorem inv_complete_spec {F : Type} [Field F] [DecidableEq F]
    (x : FVar F) (xv : F)
    (Q : PostCond (FVar F) (.arg Nat (.arg (Assignments F) (.except EvalError .pure)))) :
    Triple (m := ProverM F) (inv (c := Basic F) x)
      (ProverComputes (fun env => x.eval env = .ok xv ∧ xv ≠ 0) (fun _ => xv⁻¹) Q)
      Q := by
  intro nv env hpre
  obtain ⟨hfresh, ⟨hx, hxv⟩, hk⟩ := hpre
  obtain ⟨⟨r, nv', env'⟩, hrun, heval, hfresh'⟩ := inv_complete hfresh hx hxv
  simp only [wp, PredTrans.apply, hrun]
  exact hk r nv' env' heval hfresh' (prove_assignments_le hrun)

/-! ### `div` — the first composed law -/

/-- **`div` soundness** (D12), proved compositionally: `build_bind` splits the
constraints, `inv_sound` pins the inverse, `mul_sound` pins the product. -/
theorem div_sound {F : Type u} [Field F] [DecidableEq F]
    {x y : FVar F} {nv : Nat} {env : Assignments F} {xv yv : F}
    (hsat : ∀ con ∈ (build (div (c := Basic F) x y) nv).constraints,
      con.holds env = true)
    (hx : x.eval env = .ok xv) (hy : y.eval env = .ok yv) :
    (build (div (c := Basic F) x y) nv).result.eval env = .ok (xv / yv) := by
  unfold div at hsat ⊢
  rw [build_bind] at hsat ⊢
  have h₁ := inv_sound (fun con h => hsat con (List.mem_append_left _ h)) hy
  have h₂ := mul_sound (fun con h => hsat con (List.mem_append_right _ h)) hx h₁
  simpa [div_eq_mul_inv] using h₂

/-- **`div` completeness** (D12), proved compositionally through `prove_bind`: a nonzero
divisor makes the honest run succeed with the quotient. -/
theorem div_complete {F : Type u} [Field F] [DecidableEq F]
    {x y : FVar F} {nv : Nat} {env : Assignments F} {xv yv : F}
    (hfresh : env.FreshFrom nv) (hx : x.eval env = .ok xv) (hy : y.eval env = .ok yv)
    (hyv : yv ≠ 0) :
    ∃ out, prove Basic.holds (div (c := Basic F) x y) nv env = .ok out ∧
      out.result.eval out.assignments = .ok (xv / yv) ∧
      out.assignments.FreshFrom out.nextVar := by
  unfold div
  rw [prove_bind]
  obtain ⟨o₁, hr₁, he₁, hf₁⟩ := inv_complete hfresh hy hyv
  rw [hr₁]
  have hx₁ : x.eval o₁.assignments = .ok xv :=
    CVar.eval_le (prove_assignments_le hr₁) hx
  obtain ⟨o₂, hr₂, he₂, hf₂⟩ := mul_complete hf₁ hx₁ he₁
  refine ⟨o₂, hr₂, ?_, hf₂⟩
  simpa [div_eq_mul_inv] using he₂

/-! ### `square` (Circuit/DSL/Field) -/

/-- What `squareCore` builds: one fresh variable, one `square` constraint. -/
private theorem build_squareCore {F : Type u} [Add F] [Mul F] (x : FVar F) (nv : Nat) :
    build (squareCore (c := Basic F) x) nv =
      ⟨.var nv, nv + 1, [.square x (.var nv)]⟩ := rfl

/-- `squareCore` soundness: the constraint pins the fresh variable to the square. -/
private theorem squareCore_sound {F : Type u} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] {x : FVar F} {nv : Nat} {env : Assignments F} {xv : F}
    (hsat : ∀ con ∈ (build (squareCore (c := Basic F) x) nv).constraints,
      con.holds env = true)
    (hx : x.eval env = .ok xv) :
    (build (squareCore (c := Basic F) x) nv).result.eval env = .ok (xv * xv) := by
  rw [build_squareCore] at hsat ⊢
  have h₁ := hsat _ (List.mem_cons_self ..)
  cases hnv : env nv with
  | none => simp [Basic.holds, CVar.eval, hnv] at h₁
  | some zv =>
    simp only [Basic.holds, CVar.eval, hx, hnv, decide_eq_true_eq] at h₁
    show (CVar.var nv).eval env = _
    simp [CVar.eval, hnv, ← h₁]

/-- The honest `squareCore` run. -/
private theorem squareCore_run {F : Type u} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] {x : FVar F} {nv : Nat} {env : Assignments F} {xv : F}
    (hx : x.eval env = .ok xv) (hfresh : env.FreshFrom nv) :
    prove Basic.holds (squareCore (c := Basic F) x) nv env
      = .ok ⟨.var nv, nv + 1, env.extend nv (xv * xv)⟩ := by
  have hnv : env nv = none := hfresh nv (Nat.le_refl nv)
  have hle : env.Le (env.extend nv (xv * xv)) := by
    intro v w hv
    simp only [Assignments.extend]
    split
    · next h => rw [h, hnv] at hv; cases hv
    · exact hv
  have hw : squareWit x env = .ok (xv * xv) := by
    simp [squareWit, AsProver.readCVar, hx, Bind.bind, ReaderT.bind, Except.bind,
      Pure.pure, ReaderT.pure, Except.pure]
  have hch : Basic.holds (.square x (.var nv)) (env.extend nv (xv * xv)) = true := by
    simp [Basic.holds, CVar.eval, CVar.eval_le hle hx, Assignments.extend]
  exact prove_witnessCore hw hfresh hch

/-- **`square` soundness** (D12): any satisfying assignment pins the result to the
square. -/
theorem square_sound {F : Type u} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {x : FVar F} {nv : Nat} {env : Assignments F} {xv : F}
    (hsat : ∀ con ∈ (build (square (c := Basic F) x) nv).constraints,
      con.holds env = true)
    (hx : x.eval env = .ok xv) :
    (build (square (c := Basic F) x) nv).result.eval env = .ok (xv * xv) := by
  unfold square at hsat ⊢
  cases x <;>
    first
    | (simp only [CVar.eval, Except.ok.injEq] at hx; subst hx; rfl)
    | exact squareCore_sound hsat hx

/-- **`square` completeness** (D12): the honest prover run succeeds, computes the
square, and re-establishes freshness. -/
theorem square_complete {F : Type u} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {x : FVar F} {nv : Nat} {env : Assignments F} {xv : F}
    (hfresh : env.FreshFrom nv) (hx : x.eval env = .ok xv) :
    ∃ out, prove Basic.holds (square (c := Basic F) x) nv env = .ok out ∧
      out.result.eval out.assignments = .ok (xv * xv) ∧
      out.assignments.FreshFrom out.nextVar := by
  unfold square
  cases x <;>
    first
    | (refine ⟨_, rfl, ?_, hfresh⟩
       simp only [CVar.eval, Except.ok.injEq] at hx
       subst hx; rfl)
    | (refine ⟨_, squareCore_run hx hfresh, ?_, ?_⟩
       · show (CVar.var nv).eval _ = _
         simp [CVar.eval, Assignments.extend]
       · intro v hv
         replace hv : nv + 1 ≤ v := hv
         have h0 : v ≠ nv := by omega
         show (env.extend nv _) v = none
         simp [Assignments.extend, h0, hfresh v (by omega)])

/-! ### `pow` (Circuit/DSL/Field) — composed through the fuel recursion -/

/-- `powGo` soundness, by induction on the fuel: with the fuel adequate for the
exponent, any satisfying assignment pins the result to the power. -/
private theorem powGo_sound {F : Type u} [Add F] [CommMonoidWithZero F] [DecidableEq F] :
    ∀ (fuel : Nat) {x : FVar F} (n : Nat) {nv : Nat} {env : Assignments F} {xv : F},
      n ≤ fuel + 1 →
      (∀ con ∈ (build (powGo (c := Basic F) fuel x n) nv).constraints,
        con.holds env = true) →
      x.eval env = .ok xv →
      (build (powGo (c := Basic F) fuel x n) nv).result.eval env = .ok (xv ^ n) := by
  intro fuel
  induction fuel with
  | zero =>
    intro x n nv env xv hfuel hsat hx
    match n, hfuel with
    | 0, _ => show Except.ok _ = _; rw [pow_zero]
    | 1, _ => rw [pow_one]; exact hx
  | succ fuel ih =>
    intro x n nv env xv hfuel hsat hx
    match n with
    | 0 => show Except.ok _ = _; rw [pow_zero]
    | 1 => rw [pow_one]; exact hx
    | m + 2 =>
      unfold powGo at hsat ⊢
      simp only [build_bind] at hsat ⊢
      have hsq := mul_sound
        (fun con h => hsat con (List.mem_append_left _ h)) hx hx
      have hrest := fun con h => hsat con (List.mem_append_right _ h)
      by_cases hpar : (m + 2) % 2 = 0
      · simp only [eq_true hpar, if_true] at hrest ⊢
        have hy := ih ((m + 2) / 2) (by omega)
          (fun con h => hrest con (List.mem_append_left _ h)) hsq
        have hpow : (xv * xv) ^ ((m + 2) / 2) = xv ^ (m + 2) := by
          rw [← pow_two, ← pow_mul]
          congr 1
          omega
        exact hpow ▸ hy
      · simp only [eq_false hpar, if_false] at hrest ⊢
        have hy := ih ((m + 2) / 2) (by omega)
          (fun con h => hrest con (List.mem_append_left _ h)) hsq
        have hfin := mul_sound
          (fun con h => hrest con (List.mem_append_right _ h)) hx hy
        have hpow : xv * (xv * xv) ^ ((m + 2) / 2) = xv ^ (m + 2) := by
          rw [← pow_two, ← pow_mul, mul_comm, ← pow_succ]
          congr 1
          omega
        exact hpow ▸ hfin

/-- **`pow` soundness** (D12), composed through the fuel recursion from `mul_sound` and
`build_bind`. -/
theorem pow_sound {F : Type u} [Add F] [CommMonoidWithZero F] [DecidableEq F]
    {x : FVar F} {n : Nat} {nv : Nat} {env : Assignments F} {xv : F}
    (hsat : ∀ con ∈ (build (pow (c := Basic F) x n) nv).constraints,
      con.holds env = true)
    (hx : x.eval env = .ok xv) :
    (build (pow (c := Basic F) x n) nv).result.eval env = .ok (xv ^ n) := by
  unfold pow at hsat ⊢
  exact powGo_sound n n (Nat.le_succ n) hsat hx

/-- `powGo` completeness, by induction on the fuel through `prove_bind` and
`mul_complete`. -/
private theorem powGo_complete {F : Type u} [Add F] [CommMonoidWithZero F]
    [DecidableEq F] :
    ∀ (fuel : Nat) {x : FVar F} (n : Nat) {nv : Nat} {env : Assignments F} {xv : F},
      n ≤ fuel + 1 →
      env.FreshFrom nv →
      x.eval env = .ok xv →
      ∃ out, prove Basic.holds (powGo (c := Basic F) fuel x n) nv env = .ok out ∧
        out.result.eval out.assignments = .ok (xv ^ n) ∧
        out.assignments.FreshFrom out.nextVar := by
  intro fuel
  induction fuel with
  | zero =>
    intro x n nv env xv hfuel hfresh hx
    match n, hfuel with
    | 0, _ => exact ⟨_, rfl, by rw [pow_zero]; rfl, hfresh⟩
    | 1, _ => exact ⟨_, rfl, by rw [pow_one]; exact hx, hfresh⟩
  | succ fuel ih =>
    intro x n nv env xv hfuel hfresh hx
    match n with
    | 0 => exact ⟨_, rfl, by rw [pow_zero]; rfl, hfresh⟩
    | 1 => exact ⟨_, rfl, by rw [pow_one]; exact hx, hfresh⟩
    | m + 2 =>
      have hdef : powGo (c := Basic F) (fuel + 1) x (m + 2)
          = (do let sq ← mul x x
                let y ← powGo (c := Basic F) fuel sq ((m + 2) / 2)
                if (m + 2) % 2 = 0 then pure y else mul x y) := rfl
      rw [hdef, prove_bind]
      obtain ⟨o₁, hr₁, he₁, hf₁⟩ := mul_complete hfresh hx hx
      rw [hr₁]
      simp only [Except.bind]
      obtain ⟨o₂, hr₂, he₂, hf₂⟩ := ih ((m + 2) / 2) (by omega) hf₁ he₁
      have hx₂ : x.eval o₂.assignments = .ok xv :=
        CVar.eval_le ((prove_assignments_le hr₁).trans (prove_assignments_le hr₂)) hx
      rw [prove_bind, hr₂]
      simp only [Except.bind]
      by_cases hpar : (m + 2) % 2 = 0
      · simp only [eq_true hpar, if_true]
        have hpow : (xv * xv) ^ ((m + 2) / 2) = xv ^ (m + 2) := by
          rw [← pow_two, ← pow_mul]
          congr 1
          omega
        exact ⟨o₂, rfl, hpow ▸ he₂, hf₂⟩
      · simp only [eq_false hpar, if_false]
        obtain ⟨o₃, hr₃, he₃, hf₃⟩ := mul_complete hf₂ hx₂ he₂
        have hpow : xv * (xv * xv) ^ ((m + 2) / 2) = xv ^ (m + 2) := by
          rw [← pow_two, ← pow_mul, mul_comm, ← pow_succ]
          congr 1
          omega
        exact ⟨o₃, hr₃, hpow ▸ he₃, hf₃⟩

/-- **`pow` completeness** (D12), composed through the fuel recursion from
`mul_complete` and `prove_bind`. -/
theorem pow_complete {F : Type u} [Add F] [CommMonoidWithZero F] [DecidableEq F]
    {x : FVar F} {n : Nat} {nv : Nat} {env : Assignments F} {xv : F}
    (hfresh : env.FreshFrom nv) (hx : x.eval env = .ok xv) :
    ∃ out, prove Basic.holds (pow (c := Basic F) x n) nv env = .ok out ∧
      out.result.eval out.assignments = .ok (xv ^ n) ∧
      out.assignments.FreshFrom out.nextVar := by
  unfold pow
  exact powGo_complete n n (Nat.le_succ n) hfresh hx

end Snarky
