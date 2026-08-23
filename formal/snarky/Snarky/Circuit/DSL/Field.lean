import Mathlib.Algebra.Field.Defs
import Snarky.Circuit.DSL.Monad
import Snarky.Backend.WP
import Snarky.Backend.Prover

-- `mvcgen` is experimental; this option is its acknowledged-use switch (see the
-- `Backend/WP` module docstring for the adoption rationale).
set_option mvcgen.warning false

/-!
# Field gadgets

Port of `Snarky.Circuit.DSL.Field` (packages/snarky/src/Snarky/Circuit/DSL/Field.purs):
the field arithmetic and comparison gadgets — `mul`, `inv`, `div`, `square`, `pow`, the
pure `sum`, and the equality tests `equals`/`neq` via the inverse-or-zero trick. Each
gadget carries its two laws (`*_spec`, `*_run`) beside it; laws are stated
against the interpreters, which is why this module imports the backend — a deliberate
deviation from the PS import graph, adjacency over layering.

Name map (underscores drop): `mul_` → `mul`, `inv_` → `inv`, `div_` → `div`,
`equals_` → `equals`, `neq_` → `neq`, `sum_` → `sum`, `pow_` → `pow`,
`square_` → `square`.

Deviations from the PS original (ledger: `formal/docs/snarky-ps-alignment.md`):
- `inv` is total: a constant zero folds via Lean's `0⁻¹ = 0` where PS crashes at
  construction; a prover run still fails on a zero operand, as in PS.
- `equals` witnesses the pair `(r, zInv)` at `UnChecked Bool × F` where PS derives a
  record; same rows, same order.
- `neq` inlines the one-line negation retag rather than depending on a negation gadget.
- `pow`'s exponent is `Nat` (PS `Int`, never called negative); the PS action-lifted
  `equals` variant is not ported.
- The `CircuitType F Bool` instance pins `F : Type 0`, so the `BoolVar`-returning
  gadgets are stated for `Type`-sized fields — every concrete field is one.
-/

namespace Snarky

variable {F c : Type u}

/-! ## The gadgets -/

/-- `mul`'s witness computation: the product of the operands' values. -/
private def mulWit [Add F] [Mul F] (x y : FVar F) : AsProver F F := do
  let xv ← AsProver.readCVar x
  let yv ← AsProver.readCVar y
  pure (xv * yv)

/-- `mul`'s witnessing branch: witness the product, pin it with one `r1cs` constraint.
Split out so the gadget laws below quantify over it uniformly. -/
private def mulCore [Add F] [Mul F] [BasicSystem F c] (x y : FVar F) : CircuitM F c (FVar F) := do
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

/-- `inv`'s witness computation: the inverse, failing on zero (PS `DivisionByZero`). -/
private def invWit [Field F] [DecidableEq F] (x : FVar F) : AsProver F F := do
  let xv ← AsProver.readCVar x
  if xv = 0 then AsProver.throw "inv: division by zero"
  else pure xv⁻¹

/-- `inv`'s witnessing branch: witness the inverse, pin it with `x · xInv = 1`. Split
out so the gadget laws below quantify over it uniformly. Public, unlike the other cores:
its product-row triple `invCore_spec` is rooted (`assertNonZero`'s soundness needs
`x · r = 1`, which `inv`'s `0⁻¹ = 0` reading erases), and a rooted statement needs a
public subject. Soundness-only — the completeness path runs through `inv_run`. -/
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

/-- `equals`'s witness computation: the claimed answer bit and the inverse-or-zero. -/
private def equalsWit {F : Type} [Field F] [DecidableEq F] (z : CVar F) :
    AsProver F (UnChecked Bool × F) := do
  let zv ← AsProver.readCVar z
  pure (if zv = 0 then (⟨true⟩, 0) else (⟨false⟩, zv⁻¹))

/-- `equals`'s witnessing branch, over the precomputed difference `z` — split out so the
gadget laws below quantify over it uniformly. -/
private def equalsCore {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (z : CVar F) :
    CircuitM F c (BoolVar F) := do
  let rz ← witness (val := UnChecked Bool × F) (equalsWit z)
  let r := rz.1.val
  addConstraint (BasicSystem.r1cs ↑r z (.const 0))
  addConstraint (BasicSystem.r1cs rz.2 z (CVar.sub_ (.const 1) ↑r))
  pure r

/-- The value-level answer of `equals`: the pure mirror both readings' laws state
their answer through. -/
def equalsPure [Zero F] [One F] [DecidableEq F] (a b : F) : F := if a = b then 1 else 0

/-- The value-level answer of `neq` — `equalsPure` negated. -/
def neqPure [Zero F] [One F] [DecidableEq F] (a b : F) : F := if a = b then 0 else 1

attribute [circuitVal] equalsPure neqPure

/-- Equality test returning a boolean variable (PS `equals_`). A constant difference
folds to the constant answer. Otherwise, with `z = a − b`: witness the pair `(r, zInv)`
— `r` the claimed answer at `UnChecked Bool`, `zInv` the inverse or zero — and constrain
`r · z = 0` and `zInv · z = 1 − r`. The pair forces `r = (a == b)` — in particular `r`
is boolean (`Snarky.equals_spec`), which is why the witness may skip the `boolean`
check. -/
def equals {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (a b : FVar F) :
    CircuitM F c (BoolVar F) :=
  match CVar.sub_ a b with
  | .const f => pure (.unchecked (.const (if f = 0 then 1 else 0)))
  | z => equalsCore z

/-- Negated equality test (PS `neq_ = not <<< equals_`): the negated `equals` bit, the
negation inlined as the retag `1 − r` (`not` itself lives with the Boolean family). -/
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
unreachable: `pow` seeds fuel `n`, and the exponent at least halves each step. -/
private def powGo [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c] :
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

/-- `square`'s witness computation: the square of the operand's value. -/
private def squareWit [Add F] [Mul F] (x : FVar F) : AsProver F F := do
  let xv ← AsProver.readCVar x
  pure (xv * xv)

/-- `square`'s witnessing branch: witness the square, pin it with one `square`
constraint. Split out so the gadget laws below quantify over it uniformly. -/
private def squareCore [Add F] [Mul F] [BasicSystem F c] (x : FVar F) : CircuitM F c (FVar F) := do
  let z ← witness (val := F) (squareWit x)
  addConstraint (BasicSystem.square x z)
  pure z

/-- Square a field variable via the dedicated `square` constraint rather than `r1cs`
(PS `square_`, matching OCaml's `Checked.square`). A constant folds. -/
def square [Add F] [Mul F] [BasicSystem F c] (x : FVar F) : CircuitM F c (FVar F) :=
  match x with
  | .const f => pure (.const (f * f))
  | x => squareCore x

/-! ## The sum law -/

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
      have hstep : (CVar.add_ acc x).eval env = .ok (a + v) :=
        CVar.eval_add_ hacc hx
      simpa [add_assoc] using ih hrest hstep

/-- `sum` evaluates to the sum of its operands' values: if each `xᵢ` evaluates to `vᵢ`
under `env`, the folded expression evaluates to `Σ vᵢ`. -/
theorem sum_eval [AddMonoid F] [Mul F] {env : Assignments F} {xs : List (CVar F)}
    {vals : List F} (h : xs.map (CVar.eval · env) = vals.map .ok) :
    (sum xs).eval env = .ok vals.sum := by
  have h0 : (CVar.const (0 : F)).eval env = .ok 0 := rfl
  simpa [sum] using sum_go h h0

/-- A sum of in-scope expressions is in scope. -/
theorem CVar.Scoped.sum {F : Type} [Add F] [Zero F] {st : ProverState F} {xs : List (CVar F)}
    (h : ∀ x ∈ xs, x.Scoped st) : (Snarky.sum xs).Scoped st := by
  unfold Snarky.sum
  suffices hf : ∀ (l : List (CVar F)) (acc : CVar F), acc.Scoped st → (∀ x ∈ l, x.Scoped st) →
      (l.foldl CVar.add_ acc).Scoped st from hf xs _ trivial h
  intro l
  induction l with
  | nil => exact fun _ hacc _ => hacc
  | cons x t ih =>
    intro acc hacc hl
    exact ih _ (hacc.add_ (hl x (List.mem_cons_self ..)))
      (fun y hy => hl y (List.mem_cons_of_mem _ hy))

/-! ## The gadget laws

Soundness quantifies over every satisfying assignment; completeness runs the honest
prover. The laws for the gadgets PS parks in its Monad module (`mul`/`inv`/`div`) live
here with their family: the interpreters import `DSL/Monad`, so that module cannot
state laws about them. -/

/-! ### `equals` -/

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

/-- What `equalsCore` builds at any backend: two fresh variables, two `r1cs` rows. -/
private theorem build_equalsCore' {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] (z : CVar F) (nv : Nat) :
    build (equalsCore (c := c) z) nv =
      ⟨.unchecked (.var nv), nv + 2,
        [BasicSystem.r1cs (.var nv) z (.const 0),
         BasicSystem.r1cs (.var (nv + 1)) z (CVar.sub_ (.const 1) (.var nv))]⟩ := rfl

open Std.Do in
/-- `equals a b` returns a bit reading `1` exactly when the operands read equal — the
constant difference folds, the witnessing pair is pinned by its two rows (which also
force the bit boolean, so the witness may skip the `boolean` check). -/
@[spec] theorem equals_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (a b : FVar F) :
    ⦃⌜True⌝⦄
    equals (c := Builder V c) a b
    ⦃⇓ r _ => ⌜(↑r : CVar F).val V = equalsPure (a.val V) (b.val V)⌝⦄ := by
  intro nv _
  have hz : (CVar.sub_ a b).val V = a.val V - b.val V := CVar.val_sub_ a b V
  cases hZ : CVar.sub_ a b <;> simp only [equals, hZ]
  case const f =>
    intro _
    rw [hZ] at hz
    simp only [circuitVal, show (f : F) = a.val V - b.val V from hz, sub_eq_zero]
  all_goals
    (intro hsat
     rw [build_equalsCore'] at hsat ⊢
     rw [List.forall_mem_cons, List.forall_mem_cons] at hsat
     obtain ⟨h₁, h₂, -⟩ := hsat
     have e₁ := LawfulBasicSystem.holds_r1cs V _ _ _ h₁
     have e₂ := LawfulBasicSystem.holds_r1cs V _ _ _ h₂
     rw [← hZ, hz] at e₁ e₂
     rw [CVar.val_sub_] at e₂
     show V nv = _
     have hpin : V nv = if a.val V - b.val V = 0 then 1 else 0 := equals_pin e₁ e₂
     rw [hpin]
     simp only [equalsPure]
     by_cases h : a.val V = b.val V
     · rw [if_pos (sub_eq_zero.mpr h), if_pos h]
     · rw [if_neg (sub_ne_zero.mpr h), if_neg h])

/-- The state and result of `equals`'s honest run — its `match` on the difference,
read at the table: a constant difference folds to the constant bit; otherwise the bit
and the inverse-or-zero (`zv⁻¹`, total via `0⁻¹ = 0`) are allocated. -/
def equalsRun {F : Type} [Field F] [DecidableEq F] (st : ProverState F) (a b : FVar F) :
    ProverState F × BoolVar F :=
  match CVar.sub_ a b with
  | .const f => (st, .unchecked (.const (if f = 0 then 1 else 0)))
  | z => (st.extendMany [if z.val st.env.toValuation = 0 then 1 else 0,
      (z.val st.env.toValuation)⁻¹], .unchecked (.var st.nv))

/-- The field engine of `equals` completeness: the honest values satisfy both rows. -/
private theorem equals_checks {F : Type} [Field F] [DecidableEq F] (zv : F) :
    (if zv = 0 then (1 : F) else 0) * zv = 0 ∧
    zv⁻¹ * zv = 1 - (if zv = 0 then (1 : F) else 0) := by
  by_cases hz : zv = 0 <;> simp [hz]

/-- `equalsCore`'s honest run: the bit at the counter, the inverse-or-zero after it,
both rows accepted. -/
private theorem equalsCore_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {z : CVar F}
    (st : ProverState F) (hz : z.Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (equalsCore (c := c) z) st.nv st.env
      = .ok ((st.extendMany [if z.val st.env.toValuation = 0 then 1 else 0,
          (z.val st.env.toValuation)⁻¹]).out (.unchecked (.var st.nv))) := by
  have hvz := CVar.val_of_le (st.le_extendMany [if z.val st.env.toValuation = 0 then 1 else 0,
    (z.val st.env.toValuation)⁻¹]) hz
  have hle := st.le_extendMany [if z.val st.env.toValuation = 0 then 1 else 0,
    (z.val st.env.toValuation)⁻¹]
  generalize hzv : z.val st.env.toValuation = zv at hvz hle ⊢
  obtain ⟨hc₁, hc₂⟩ := equals_checks zv
  simp only [equalsCore, prove_bind]
  rw [prove_witness_run (w := equalsWit z) st (.bind (.readCVar hz) fun _ => trivial)
    (v := (⟨decide (zv = 0)⟩, zv⁻¹)) (by
      simp [equalsWit, Except.bind, hzv]
      by_cases h : zv = 0 <;> simp [h])]
  have hvals : (CircuitType.valueToFields (F := F) (var := UnChecked (BoolVar F) × FVar F)
      ((⟨decide (zv = 0)⟩, zv⁻¹) : UnChecked Bool × F)).toList
      = [if zv = 0 then 1 else 0, zv⁻¹] := by
    show [bit (decide (zv = 0)), zv⁻¹] = _
    by_cases h : zv = 0 <;> simp [h, bit]
  have hvars : CircuitType.fieldsToVar (F := F) (val := UnChecked Bool × F)
      (mapVec CVar.var (allocRange st.nv (CircuitType.size F (UnChecked Bool × F))))
      = (⟨.unchecked (.var st.nv)⟩, .var (st.nv + 1)) := rfl
  simp only [hvals, hvars, Except.bind, BoolVar.toCVar_unchecked]
  rw [prove_addConstraint _ (LawfulChecker.holds_r1cs (by simp) (hz.of_le hle)
    (CVar.scoped_const _ _) (by simp [CVar.val, hvz, hc₁]))]
  simp only []
  rw [prove_addConstraint _ (LawfulChecker.holds_r1cs
    (by exact st.new_mem_extendMany (i := 1) (by simp))
    (hz.of_le hle) (CVar.Scoped.sub_ (CVar.scoped_const _ _) (by simp))
    (by simp [CVar.val, CVar.val_sub_, hvz, hc₂]))]
  rfl

/-- `equals`'s honest run lands at `equalsRun`. -/
theorem equals_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {a b : FVar F}
    (st : ProverState F) (ha : a.Scoped st) (hb : b.Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (equals (c := c) a b) st.nv st.env
      = .ok ((equalsRun st a b).1.out (equalsRun st a b).2) := by
  have hz : (CVar.sub_ a b).Scoped st := ha.sub_ hb
  unfold equals equalsRun
  cases h : CVar.sub_ a b
  case const => rfl
  all_goals exact equalsCore_run st (h ▸ hz)

/-- `equalsRun` reads, through the bit's expression, as the equality bit. -/
theorem equalsRun_grants {F : Type} [Field F] [DecidableEq F] {st : ProverState F}
    {a b : FVar F} (ha : a.Scoped st) (hb : b.Scoped st) :
    Grants F st ((equalsRun st a b).1, ↑(equalsRun st a b).2)
      (equalsPure (a.val st.env.toValuation) (b.val st.env.toValuation)) := by
  have hz : (CVar.sub_ a b).Scoped st := ha.sub_ hb
  have hv : (CVar.sub_ a b).val st.env.toValuation
      = a.val st.env.toValuation - b.val st.env.toValuation := CVar.val_sub_ ..
  unfold equalsRun
  cases h : CVar.sub_ a b <;> dsimp only <;> rw [h] at hv hz
  case const =>
    simp only [CVar.val] at hv
    exact Grants.fvar (Assignments.Le.refl _) trivial
      (by simp [CVar.val, BoolVar.toCVar_unchecked, equalsPure, hv, sub_eq_zero])
  all_goals
    rw [hv]
    refine Grants.fvar (st.le_extendMany _) (by simp [BoolVar.toCVar_unchecked]) ?_
    rw [BoolVar.toCVar_unchecked]
    simp [CVar.val, equalsPure, sub_eq_zero]

/-! ### `neq` — composed from `equals` -/

open Std.Do in
/-- The result bit is the negated equality answer. -/
@[spec] theorem neq_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (a b : FVar F) :
    ⦃⌜True⌝⦄
    neq (c := Builder V c) a b
    ⦃⇓ r _ => ⌜(↑r : CVar F).val V = neqPure (a.val V) (b.val V)⌝⦄ := by
  simp only [neq]
  mvcgen
  rename_i r _ hr
  simp only [circuitVal, hr]
  split_ifs <;> ring

/-- The state and result of `neq`'s honest run: `equals`, the bit negated. -/
def neqRun {F : Type} [Field F] [DecidableEq F] (st : ProverState F) (a b : FVar F) :
    ProverState F × BoolVar F :=
  let r := equalsRun st a b
  (r.1, .unchecked (CVar.sub_ (.const 1) ↑r.2))

/-- `neq`'s honest run lands at `neqRun`. -/
theorem neq_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {a b : FVar F}
    (st : ProverState F) (ha : a.Scoped st) (hb : b.Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (neq (c := c) a b) st.nv st.env
      = .ok ((neqRun st a b).1.out (neqRun st a b).2) := by
  simp only [neq, prove_bind, equals_run st ha hb, Except.bind, neqRun]
  rfl

/-- `neqRun` reads, through the bit's expression, as the negated equality bit. -/
theorem neqRun_grants {F : Type} [Field F] [DecidableEq F] {st : ProverState F}
    {a b : FVar F} (ha : a.Scoped st) (hb : b.Scoped st) :
    Grants F st ((neqRun st a b).1, ↑(neqRun st a b).2)
      (neqPure (a.val st.env.toValuation) (b.val st.env.toValuation)) := by
  have h := equalsRun_grants ha hb
  refine Grants.fvar h.le (CVar.Scoped.sub_ trivial h.fvar_scoped) ?_
  simp only [neqRun]
  rw [BoolVar.toCVar_unchecked, CVar.val_sub_, h.fvar_val]
  simp only [CVar.val, equalsPure, neqPure]
  split_ifs <;> norm_num

/-! ### `inv` -/

open Std.Do in
/-- The witnessing row pins the product `x · r = 1` — more than `inv`'s inverse
reading, whose `0⁻¹ = 0` erases the nonzero fact. -/
@[spec] theorem invCore_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x : FVar F) :
    ⦃⌜True⌝⦄
    invCore (c := Builder V c) x
    ⦃⇓ r _ => ⌜x.val V * r.val V = 1⌝⦄ := by
  intro nv _ hsat
  exact LawfulBasicSystem.holds_r1cs V _ _ _ (hsat _ (List.mem_cons_self ..))

open Std.Do in
/-- `inv x` computes the operand's field inverse — the witnessing row forces it; the
constant branch is total via `0⁻¹ = 0`. -/
@[spec] theorem inv_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x : FVar F) :
    ⦃⌜True⌝⦄
    inv (c := Builder V c) x
    ⦃⇓ r _ => ⌜r.val V = (x.val V)⁻¹⌝⦄ := by
  intro nv _
  cases x <;> simp only [inv]
  case const a =>
    intro _
    exact rfl
  all_goals
    (intro hsat
     have h := LawfulBasicSystem.holds_r1cs V _ _ _ (hsat _ (List.mem_cons_self ..))
     exact (inv_eq_of_mul_eq_one_right (by simpa using h)).symm)

/-- The state and result of `inv`'s honest run: a constant folds; otherwise the
inverse is allocated. -/
def invRun [Field F] [DecidableEq F] (st : ProverState F) (x : FVar F) :
    ProverState F × FVar F :=
  match x with
  | .const a => (st, .const a⁻¹)
  | x => (st.extendMany [(x.val st.env.toValuation)⁻¹], .var st.nv)

/-- `invCore`'s honest run on a nonzero operand: one slot, the inverse, its `r1cs` row
accepted. -/
private theorem invCore_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {x : FVar F}
    (st : ProverState F) (hx : x.Scoped st) (hne : x.val st.env.toValuation ≠ 0) :
    prove (Checker.holds (F := F) (c := c)) (invCore (c := c) x) st.nv st.env
      = .ok ((st.extendMany [(x.val st.env.toValuation)⁻¹]).out (.var st.nv)) := by
  have hle := st.le_extendMany [(x.val st.env.toValuation)⁻¹]
  simp only [invCore, prove_bind]
  rw [prove_witness_run (w := invWit x) st
    (.bind (.readCVar hx) fun _ => by split <;> trivial)
    (v := (x.val st.env.toValuation)⁻¹) (by simp [invWit, hne, AsProver.throw, Except.bind])]
  simp only [valueToFields_fvar_toList, fieldsToVar_fvar_alloc, Except.bind]
  rw [prove_addConstraint _ (LawfulChecker.holds_r1cs (hx.of_le hle) (by simp)
    (CVar.scoped_const _ _) (by simp [CVar.val, CVar.val_of_le hle hx, hne]))]
  rfl

/-- `inv`'s honest run on a nonzero operand lands at `invRun`. -/
theorem inv_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {x : FVar F}
    (st : ProverState F) (hx : x.Scoped st) (hne : x.val st.env.toValuation ≠ 0) :
    prove (Checker.holds (F := F) (c := c)) (inv (c := c) x) st.nv st.env
      = .ok ((invRun st x).1.out (invRun st x).2) := by
  cases x <;> simp only [inv, invRun, prove_pure] <;> exact invCore_run st hx hne

/-- `invRun` reads as the inverse. -/
theorem invRun_grants {F : Type} [Field F] [DecidableEq F] {st : ProverState F} {x : FVar F}
    (hx : x.Scoped st) : Grants F st (invRun st x) (x.val st.env.toValuation)⁻¹ := by
  cases x <;> simp only [invRun] <;>
    first
    | exact Grants.fvar (st.le_extendMany _) (by simp) (by simp [CVar.val])
    | exact Grants.fvar (Assignments.Le.refl _) trivial (by simp [CVar.val])

/-! ### `mul` -/

open Std.Do in
/-- `mul x y` computes the product — constants fold, otherwise the `r1cs` row forces
it. -/
@[spec] theorem mul_spec {F c : Type} {V : Valuation F} [Add F] [CommMonoidWithZero F]
    [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x y : FVar F) :
    ⦃⌜True⌝⦄
    mul (c := Builder V c) x y
    ⦃⇓ r _ => ⌜r.val V = x.val V * y.val V⌝⦄ := by
  intro nv _
  cases x <;> cases y <;> simp only [mul]
  case const.const a b =>
    intro _
    exact rfl
  all_goals
    first
    | (intro _
       exact CVar.val_scale_ _ _ _)
    | (intro _
       exact (CVar.val_scale_ _ _ _).trans (mul_comm _ _))
    | (intro hsat
       have h := LawfulBasicSystem.holds_r1cs V _ _ _ (hsat _ (List.mem_cons_self ..))
       exact h.symm)

/-- The state and result of `mul`'s honest run — its `match` on constants, read at the
table: the folded shapes allocate nothing, the witnessed one allocates the product. -/
def mulRun [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] (st : ProverState F)
    (x y : FVar F) : ProverState F × FVar F :=
  match x, y with
  | .const a, .const b => (st, .const (a * b))
  | .const a, y => (st, CVar.scale_ a y)
  | x, .const b => (st, CVar.scale_ b x)
  | x, y => (st.extendMany [x.val st.env.toValuation * y.val st.env.toValuation], .var st.nv)

/-- `mulCore`'s honest run: one slot, the product, its `r1cs` row accepted. -/
private theorem mulCore_run {F c : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {x y : FVar F}
    (st : ProverState F) (hx : x.Scoped st) (hy : y.Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (mulCore (c := c) x y) st.nv st.env
      = .ok ((st.extendMany [x.val st.env.toValuation * y.val st.env.toValuation]).out
          (.var st.nv)) := by
  have hle := st.le_extendMany [x.val st.env.toValuation * y.val st.env.toValuation]
  simp only [mulCore, prove_bind]
  rw [prove_witness_run (w := mulWit x y) st
    (.bind (.readCVar hx) fun _ => .bind (.readCVar hy) fun _ => trivial)
    (v := x.val st.env.toValuation * y.val st.env.toValuation) (by simp [mulWit, Except.bind])]
  simp only [valueToFields_fvar_toList, fieldsToVar_fvar_alloc, Except.bind]
  rw [prove_addConstraint _ (LawfulChecker.holds_r1cs (hx.of_le hle) (hy.of_le hle) (by simp)
    (by simp [CVar.val, CVar.val_of_le hle hx, CVar.val_of_le hle hy]))]
  rfl

/-- `mul`'s honest run lands at `mulRun`. -/
theorem mul_run {F c : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {x y : FVar F}
    (st : ProverState F) (hx : x.Scoped st) (hy : y.Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (mul (c := c) x y) st.nv st.env
      = .ok ((mulRun st x y).1.out (mulRun st x y).2) := by
  cases x <;> cases y <;> simp only [mul, mulRun, prove_pure] <;> exact mulCore_run st hx hy

/-- `mulRun` reads as the product. -/
theorem mulRun_grants {F : Type} [Add F] [CommMonoidWithZero F] [DecidableEq F] {st : ProverState F}
    {x y : FVar F} (hx : x.Scoped st) (hy : y.Scoped st) :
    Grants F st (mulRun st x y) (x.val st.env.toValuation * y.val st.env.toValuation) := by
  cases x <;> cases y <;> simp only [mulRun] <;>
    first
    | exact Grants.fvar (st.le_extendMany _) (by simp) (by simp [CVar.val])
    | exact Grants.fvar (Assignments.Le.refl _) (hy.scale_ _) (by simp [CVar.val, CVar.val_scale_])
    | exact Grants.fvar (Assignments.Le.refl _) (hx.scale_ _)
        (by simp [CVar.val, CVar.val_scale_, mul_comm])
    | exact Grants.fvar (Assignments.Le.refl _) trivial (by simp [CVar.val])

/-! ### `div` -/

open Std.Do in
/-- `div x y` computes the quotient — `x · y⁻¹`, total via `0⁻¹ = 0`. -/
@[spec] theorem div_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x y : FVar F) :
    ⦃⌜True⌝⦄
    div (c := Builder V c) x y
    ⦃⇓ r _ => ⌜r.val V = x.val V / y.val V⌝⦄ := by
  simp only [div]
  mvcgen
  rename_i r _ hr r' _
  intro hr'
  rw [hr', hr, div_eq_mul_inv]

/-- The state and result of `div`'s honest run: `inv`, then `mul`. -/
def divRun [Field F] [DecidableEq F] (st : ProverState F) (x y : FVar F) :
    ProverState F × FVar F :=
  let r := invRun st y
  mulRun r.1 x r.2

/-- `div`'s honest run on a nonzero divisor lands at `divRun`. -/
theorem div_run {F c : Type} [Field F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {x y : FVar F}
    (st : ProverState F) (hx : x.Scoped st) (hy : y.Scoped st)
    (hne : y.val st.env.toValuation ≠ 0) :
    prove (Checker.holds (F := F) (c := c)) (div (c := c) x y) st.nv st.env
      = .ok ((divRun st x y).1.out (divRun st x y).2) := by
  simp only [div, prove_bind, inv_run st hy hne, Except.bind, divRun]
  exact mul_run _ (hx.of_le (invRun_grants hy).le) (invRun_grants hy).fvar_scoped

/-- `divRun` reads as the quotient. -/
theorem divRun_grants {F : Type} [Field F] [DecidableEq F] {st : ProverState F} {x y : FVar F}
    (hx : x.Scoped st) (hy : y.Scoped st) :
    Grants F st (divRun st x y) (x.val st.env.toValuation / y.val st.env.toValuation) := by
  have hi := invRun_grants (st := st) hy
  have hm := mulRun_grants (hx.of_le hi.le) hi.fvar_scoped
  refine ⟨hi.le.trans hm.le, hm.scope, ?_⟩
  simp only [divRun]
  rw [hm.read, CVar.val_of_le hi.le hx, hi.fvar_val, div_eq_mul_inv]

/-! ### `square` -/

open Std.Do in
/-- `square x` computes `x · x` through the dedicated `square` row; a constant
folds. -/
@[spec] theorem square_spec {F c : Type} {V : Valuation F} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x : FVar F) :
    ⦃⌜True⌝⦄
    square (c := Builder V c) x
    ⦃⇓ r _ => ⌜r.val V = x.val V * x.val V⌝⦄ := by
  intro nv _
  cases x <;> simp only [square]
  case const f =>
    intro _
    exact rfl
  all_goals
    (intro hsat
     have h := LawfulBasicSystem.holds_square V _ _ (hsat _ (List.mem_cons_self ..))
     exact h.symm)

/-- The state and result of `square`'s honest run: a constant folds; otherwise the
square is allocated. -/
def squareRun [Add F] [Mul F] [Zero F] (st : ProverState F) (x : FVar F) :
    ProverState F × FVar F :=
  match x with
  | .const f => (st, .const (f * f))
  | x => (st.extendMany [x.val st.env.toValuation * x.val st.env.toValuation], .var st.nv)

/-- `squareCore`'s honest run: one slot, the square, its `square` row accepted. -/
private theorem squareCore_run {F c : Type} [Add F] [Mul F] [Zero F] [One F]
    [DecidableEq F] [BasicSystem F c] [Checker F c] [LawfulChecker F c] {x : FVar F}
    (st : ProverState F) (hx : x.Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (squareCore (c := c) x) st.nv st.env
      = .ok ((st.extendMany [x.val st.env.toValuation * x.val st.env.toValuation]).out
          (.var st.nv)) := by
  have hle := st.le_extendMany [x.val st.env.toValuation * x.val st.env.toValuation]
  simp only [squareCore, prove_bind]
  rw [prove_witness_run (w := squareWit x) st (.bind (.readCVar hx) fun _ => trivial)
    (v := x.val st.env.toValuation * x.val st.env.toValuation) (by simp [squareWit, Except.bind])]
  simp only [valueToFields_fvar_toList, fieldsToVar_fvar_alloc, Except.bind]
  rw [prove_addConstraint _ (LawfulChecker.holds_square (hx.of_le hle) (by simp)
    (by simp [CVar.val, CVar.val_of_le hle hx]))]
  rfl

/-- `square`'s honest run lands at `squareRun`. -/
theorem square_run {F c : Type} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {x : FVar F}
    (st : ProverState F) (hx : x.Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (square (c := c) x) st.nv st.env
      = .ok ((squareRun st x).1.out (squareRun st x).2) := by
  cases x <;> simp only [square, squareRun, prove_pure] <;> exact squareCore_run st hx

/-- `squareRun` reads as the square. -/
theorem squareRun_grants {F : Type} [Add F] [Mul F] [Zero F] {st : ProverState F} {x : FVar F}
    (hx : x.Scoped st) :
    Grants F st (squareRun st x) (x.val st.env.toValuation * x.val st.env.toValuation) := by
  cases x <;> simp only [squareRun] <;>
    first
    | exact Grants.fvar (st.le_extendMany _) (by simp) (by simp [CVar.val])
    | exact Grants.fvar (Assignments.Le.refl _) trivial (by simp [CVar.val])

/-! ### `pow` -/

open Std.Do in
/-- `powGo` soundness as a triple, by induction on the fuel: with the fuel adequate
for the exponent, the result reads as the power. -/
@[spec] private theorem powGo_spec {F c : Type} {V : Valuation F} [Add F] [CommMonoidWithZero F]
    [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] :
    ∀ (fuel : Nat) (x : FVar F) (n : Nat), n ≤ fuel + 1 →
        ⦃⌜True⌝⦄
        powGo (c := Builder V c) fuel x n
        ⦃⇓ r _ => ⌜r.val V = x.val V ^ n⌝⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro x n hfuel
    match n, hfuel with
    | 0, _ => exact fun nv _ _ => by simp [powGo, circuitVal]
    | 1, _ => exact fun nv _ _ => by simp [powGo, circuitVal]
  | succ fuel ih =>
    intro x n hfuel
    match n with
    | 0 => exact fun nv _ _ => by simp [powGo, circuitVal]
    | 1 => exact fun nv _ _ => by simp [powGo, circuitVal]
    | m + 2 =>
      simp only [powGo]
      mvcgen [ih]
      · omega
      · rename_i sq _ hsq y hpar _ hy
        rw [hy, hsq, ← pow_two, ← pow_mul]
        congr 1
        omega
      · rename_i sq _ hsq y hpar _ hy r _
        intro hr
        rw [hr, hy, hsq, ← pow_two, ← pow_mul, mul_comm, ← pow_succ]
        congr 1
        omega

open Std.Do in
/-- `pow x n`'s result reads as the operand's `n`-th power. -/
@[spec] theorem pow_spec {F c : Type} {V : Valuation F} [Add F] [CommMonoidWithZero F]
    [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (x : FVar F) (n : Nat) :
    ⦃⌜True⌝⦄
    pow (c := Builder V c) x n
    ⦃⇓ r _ => ⌜r.val V = x.val V ^ n⌝⦄ :=
  powGo_spec n x n (Nat.le_succ n)

/-- The state and result of `powGo`'s honest run: its recursion, over `mulRun`. -/
private def powGoRun [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] :
    Nat → ProverState F → FVar F → Nat → ProverState F × FVar F
  | _, st, _, 0 => (st, .const 1)
  | _, st, x, 1 => (st, x)
  | 0, st, x, _ => (st, x)
  | fuel + 1, st, x, n =>
    let sq := mulRun st x x
    let y := powGoRun fuel sq.1 sq.2 (n / 2)
    if n % 2 = 0 then y else mulRun y.1 x y.2

/-- The state and result of `pow`'s honest run. -/
def powRun [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] (st : ProverState F) (x : FVar F)
    (n : Nat) : ProverState F × FVar F :=
  powGoRun n st x n

/-- `powGoRun` reads as the power, with the fuel adequate for the exponent. -/
private theorem powGoRun_grants {F : Type} [Add F] [CommMonoidWithZero F] [DecidableEq F] :
    ∀ (fuel : Nat) {st : ProverState F} {x : FVar F} (n : Nat), n ≤ fuel + 1 →
      x.Scoped st → Grants F st (powGoRun fuel st x n) (x.val st.env.toValuation ^ n) := by
  intro fuel
  induction fuel with
  | zero =>
    intro st x n hfuel hx
    match n, hfuel with
    | 0, _ => exact Grants.fvar (Assignments.Le.refl _) trivial (by simp [CVar.val])
    | 1, _ => exact Grants.fvar (Assignments.Le.refl _) hx (by simp)
  | succ fuel ih =>
    intro st x n hfuel hx
    match n with
    | 0 => exact Grants.fvar (Assignments.Le.refl _) trivial (by simp [CVar.val])
    | 1 => exact Grants.fvar (Assignments.Le.refl _) hx (by simp)
    | m + 2 =>
      have hsq := mulRun_grants hx hx
      have hy := ih ((m + 2) / 2) (by omega) hsq.fvar_scoped
      simp only [powGoRun]
      by_cases hpar : (m + 2) % 2 = 0
      · rw [if_pos hpar]
        refine ⟨hsq.le.trans hy.le, hy.scope, ?_⟩
        rw [hy.read, hsq.fvar_val, ← pow_two, ← pow_mul]
        congr 1
        omega
      · rw [if_neg hpar]
        have hm := mulRun_grants (hx.of_le (hsq.le.trans hy.le)) hy.fvar_scoped
        refine ⟨(hsq.le.trans hy.le).trans hm.le, hm.scope, ?_⟩
        rw [hm.read, CVar.val_of_le (hsq.le.trans hy.le) hx, hy.fvar_val, hsq.fvar_val,
          ← pow_two, ← pow_mul, mul_comm, ← pow_succ]
        congr 1
        omega

/-- `powGo`'s honest run lands at `powGoRun`, with the fuel adequate for the exponent. -/
private theorem powGo_run {F c : Type} [Add F] [CommMonoidWithZero F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] :
    ∀ (fuel : Nat) {st : ProverState F} {x : FVar F} (n : Nat), n ≤ fuel + 1 → x.Scoped st →
      prove (Checker.holds (F := F) (c := c)) (powGo (c := c) fuel x n) st.nv st.env
        = .ok ((powGoRun fuel st x n).1.out (powGoRun fuel st x n).2) := by
  intro fuel
  induction fuel with
  | zero =>
    intro st x n hfuel hx
    match n, hfuel with
    | 0, _ => rfl
    | 1, _ => rfl
  | succ fuel ih =>
    intro st x n hfuel hx
    match n with
    | 0 => rfl
    | 1 => rfl
    | m + 2 =>
      have hsq := mulRun_grants hx hx
      have hy := powGoRun_grants fuel ((m + 2) / 2) (by omega) hsq.fvar_scoped
      simp only [powGo, powGoRun, prove_bind, mul_run st hx hx, Except.bind,
        ih ((m + 2) / 2) (by omega) hsq.fvar_scoped]
      by_cases hpar : (m + 2) % 2 = 0
      · rw [if_pos hpar, if_pos hpar]
        rfl
      · rw [if_neg hpar, if_neg hpar]
        exact mul_run _ (hx.of_le (hsq.le.trans hy.le)) hy.fvar_scoped

/-- `pow`'s honest run lands at `powRun`. -/
theorem pow_run {F c : Type} [Add F] [CommMonoidWithZero F] [DecidableEq F]
    [BasicSystem F c] [Checker F c] [LawfulChecker F c] {x : FVar F}
    (st : ProverState F) (hx : x.Scoped st) (n : Nat) :
    prove (Checker.holds (F := F) (c := c)) (pow (c := c) x n) st.nv st.env
      = .ok ((powRun st x n).1.out (powRun st x n).2) :=
  powGo_run n n (Nat.le_succ n) hx

/-- `powRun` reads as the power. -/
theorem powRun_grants {F : Type} [Add F] [CommMonoidWithZero F] [DecidableEq F] {st : ProverState F}
    {x : FVar F} (hx : x.Scoped st) (n : Nat) :
    Grants F st (powRun st x n) (x.val st.env.toValuation ^ n) :=
  powGoRun_grants n n (Nat.le_succ n) hx

end Snarky
