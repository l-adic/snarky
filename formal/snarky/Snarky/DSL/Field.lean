import Mathlib.Algebra.Field.Basic
import Snarky.BasicSystem
import Snarky.Witness
import Snarky.WP
import Snarky.Prover
import Snarky.Prover.VCGen

namespace Snarky

variable {F c : Type}

/-- Invert a field variable: witness the inverse, pin it with `x · xInv = 1`. A nonzero
constant folds to its constant inverse with no constraint; a constant zero takes the
witnessed path, where the witness fails and the row `0 · xInv = 1` is unsatisfiable. -/
def inv [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (x : FVar F) : CircuitM F c (FVar F) :=
  let witnessed : CircuitM F c (FVar F) := do
    let xInv ← witness (val := F) (advice x)
    addConstraint (BasicSystem.r1cs x xInv (.const 1))
    pure xInv
  match x with
  | .const a => if a = 0 then witnessed else pure (.const a⁻¹)
  | _ => witnessed
where
  /-- The advice: the operand's inverse; a zero reading throws. -/
  advice (x : FVar F) : AsProver F F := do
    let xv ← readVar (val := F) x
    if xv = 0 then AsProver.throw "inv: division by zero" else pure xv⁻¹

open Std.WP in
@[spec] theorem inv_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) :
    ⦃fun _ => True⦄
    inv (c := Builder V c) x
    ⦃fun r _ => x.val V * r.val V = 1⦄ := by
  simp only [inv]
  vcgen
  all_goals try subst_vars
  all_goals first
    | exact (LawfulBasicSystem.holds_r1cs V _ _ _).mp ‹_›
    | exact mul_inv_cancel₀ ‹_›

attribute [irreducible] inv

/-- Multiply two field variables: constants fold — two constants multiply out, a
constant times an expression folds to `scale_` — otherwise the product is witnessed and
pinned with one `r1cs` row. -/
def mul [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (x y : FVar F) : CircuitM F c (FVar F) :=
  match x, y with
  | .const a, .const b => pure (.const (a * b))
  | .const a, y => pure (CVar.scale_ a y)
  | x, .const b => pure (CVar.scale_ b x)
  | x, y => do
    let z ← witness (val := F) (advice x y)
    addConstraint (BasicSystem.r1cs x y z)
    pure z
where
  /-- The advice: read the operands, return the product. -/
  advice (x y : FVar F) : AsProver F F := do
    let xv ← AsProver.readCVar x
    let yv ← AsProver.readCVar y
    pure (xv * yv)

open Std.WP in
/-- `mul x y` reads as the product. -/
@[spec] theorem mul_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :
    ⦃fun _ => True⦄
    mul (c := Builder V c) x y
    ⦃fun a _ => a.val V = x.val V * y.val V⦄ := by
  simp only [mul]
  vcgen
  all_goals try subst_vars
  all_goals
    first
      | simp [mul_comm]
      | (rename_i h
         exact ((LawfulBasicSystem.holds_r1cs V _ _ _).mp h).symm)

attribute [irreducible] mul

/-- Square a field variable: a constant folds to its square, otherwise the square is
witnessed and pinned with one `square` row. -/
def square [Field F] [BasicSystem F c] [ConstraintHolds F c] (x : FVar F) : CircuitM F c (FVar F) :=
  match x with
  | .const a => pure (.const (a * a))
  | x => do
    let z ← witness (val := F) (advice x)
    addConstraint (BasicSystem.square x z)
    pure z
where
  /-- The advice: read the operand, return its square. -/
  advice (x : FVar F) : AsProver F F := do
    let xv ← AsProver.readCVar x
    pure (xv * xv)

open Std.WP in
/-- `square x` reads as the square. -/
@[spec] theorem square_spec {V : Valuation F} [Field F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) :
    ⦃fun _ => True⦄
    square (c := Builder V c) x
    ⦃fun a _ => a.val V = x.val V * x.val V⦄ := by
  simp only [square]
  vcgen
  all_goals try subst_vars
  all_goals
    first
      | simp
      | (rename_i h
         exact ((LawfulBasicSystem.holds_square V _ _).mp h).symm)

attribute [irreducible] square

/-- Divide field variables — `x · y⁻¹`: the inverse witnessed and pinned by `inv`, the
product by `mul`. -/
def div [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (x y : FVar F) :
    CircuitM F c (FVar F) := do
  let yInv ← inv y
  mul x yInv

open Std.WP in
/-- `div`'s soundness: the result reads as the quotient. `inv`'s row forces a nonzero
divisor, so the field's total division is the honest reading with no side condition. -/
@[spec] theorem div_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :
    ⦃fun _ => True⦄
    div (c := Builder V c) x y
    ⦃fun r _ => r.val V = x.val V / y.val V⦄ := by
  simp only [div]
  vcgen
  rename_i yInv _ hinv _ _ hmul
  rw [hmul, div_eq_mul_inv, inv_eq_of_mul_eq_one_right hinv]

attribute [irreducible] div

/-- Test a field variable for zero, returning the answer bit: witness the claimed bit and
the inverse-or-zero, and pin them with `r · x = 0` and `xInv · x = 1 − r` — the first row
kills `r` where `x` is nonzero, the second forces `r = 1` where `x` is zero, so `r` reads
`1` exactly where `x` reads `0` (and in particular reads a bit). A constant folds to the
constant answer with no constraint. -/
def isZero [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (x : FVar F) :
    CircuitM F c (BoolVar F) :=
  match x with
  | .const xv => pure (.unchecked (.const (if xv = 0 then 1 else 0)))
  | x => do
    let r ← witness (val := F) (bitAdvice x)
    let xInv ← witness (val := F) (invAdvice x)
    addConstraint (BasicSystem.r1cs r x (.const 0))
    addConstraint (BasicSystem.r1cs xInv x (CVar.sub_ (.const 1) r))
    pure (.unchecked r)
where
  /-- The advice: `1` where the operand reads `0`, else `0`. -/
  bitAdvice (x : FVar F) : AsProver F F := do
    let xv ← AsProver.readCVar x
    pure (if xv = 0 then 1 else 0)
  /-- The advice: the operand's inverse where it reads nonzero, else `0`. -/
  invAdvice (x : FVar F) : AsProver F F := do
    let xv ← AsProver.readCVar x
    pure (if xv = 0 then 0 else xv⁻¹)

open Std.WP in
/-- `isZero x` reads `1` where `x` reads `0`, and `0` elsewhere. -/
@[spec] theorem isZero_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) :
    ⦃fun _ => True⦄
    isZero (c := Builder V c) x
    ⦃fun (r : BoolVar F) _ => (↑r : CVar F).val V = if x.val V = 0 then 1 else 0⦄ := by
  simp only [isZero]
  vcgen
  · subst_vars
    rfl
  rename_i h1 h2
  subst_vars
  have hr1 := (LawfulBasicSystem.holds_r1cs V _ _ _).mp h1
  have hr2 := (LawfulBasicSystem.holds_r1cs V _ _ _).mp h2
  simp only [CVar.val_sub_, CVar.val, BoolVar.coe_unchecked] at hr1 hr2 ⊢
  split
  · next h =>
    rw [h, mul_zero] at hr2
    exact (sub_eq_zero.mp hr2.symm).symm
  · next h =>
    rcases mul_eq_zero.mp hr1 with h0 | h0
    · exact h0
    · exact absurd h0 h

attribute [irreducible] isZero

/-- Equality test, returning the answer bit: `isZero` on the difference — a constant
difference folds, otherwise two rows. -/
def equals [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (a b : FVar F) :
    CircuitM F c (BoolVar F) :=
  isZero (CVar.sub_ a b)

open Std.WP in
/-- `equals a b` reads `1` where `a` and `b` read equal, and `0` elsewhere. -/
@[spec] theorem equals_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : FVar F) :
    ⦃fun _ => True⦄
    equals (c := Builder V c) a b
    ⦃fun (r : BoolVar F) _ => (↑r : CVar F).val V = if a.val V = b.val V then 1 else 0⦄ := by
  simp only [equals]
  vcgen
  rename_i h
  simpa [sub_eq_zero] using h

attribute [irreducible] equals

/-- The rows `equals` emits, in order — `r · z = 0` then `zInv · z = 1 − r` over the
difference `z` — when the difference is not constant. -/
example [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (a b : FVar F) (nv : Nat)
    (h : ∀ f, CVar.sub_ a b ≠ CVar.const f) :
    (build (equals (c := c) a b) nv).constraints =
      [BasicSystem.r1cs (CVar.var nv) (CVar.sub_ a b) (.const 0),
       BasicSystem.r1cs (CVar.var (nv + 1)) (CVar.sub_ a b)
         (CVar.sub_ (.const 1) (CVar.var nv))] := by
  unfold equals isZero
  split
  · exact absurd ‹_› (h _)
  · rfl

/-- Negated equality test: `equals`'s bit, negated by the retag `1 − r` — no rows of its
own. -/
def neq [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (a b : FVar F) :
    CircuitM F c (BoolVar F) := do
  let r ← equals a b
  pure (.unchecked (CVar.sub_ (.const 1) ↑r))

open Std.WP in
/-- `neq a b` reads `0` where `a` and `b` read equal, and `1` elsewhere. -/
@[spec] theorem neq_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : FVar F) :
    ⦃fun _ => True⦄
    neq (c := Builder V c) a b
    ⦃fun (r : BoolVar F) _ => (↑r : CVar F).val V = if a.val V = b.val V then 0 else 1⦄ := by
  simp only [neq]
  vcgen
  rename_i h
  simp only [BoolVar.coe_unchecked, CVar.val_sub_, CVar.val, h]
  split <;> simp

attribute [irreducible] neq

/-- `neq` emits exactly `equals`'s rows. -/
example [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (a b : FVar F) (nv : Nat) :
    (build (neq (c := c) a b) nv).constraints = (build (equals (c := c) a b) nv).constraints := by
  unfold neq
  rw [build_bind]
  simp [build]

/-- Sum a list of field variables — pure, no rows: `add_` folded over the list from
`const 0`. -/
def sum [Add F] [Zero F] (xs : List (FVar F)) : FVar F :=
  xs.foldl CVar.add_ (.const 0)

/-- `sum xs` reads as the sum of its operands' readings. -/
theorem sum_eval [AddMonoid F] [Mul F] (V : Valuation F) (xs : List (FVar F)) :
    (sum xs).val V = (xs.map (·.val V)).sum := by
  suffices h : ∀ (l : List (FVar F)) (acc : FVar F),
      (l.foldl CVar.add_ acc).val V = acc.val V + (l.map (·.val V)).sum by
    simpa [sum] using h xs (.const 0)
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x t ih => intro acc; simp [ih, add_assoc]

/-- A sum of scoped operands is scoped. -/
theorem CVar.Scoped.sum [Add F] [Zero F] {st : ProverState F} {xs : List (FVar F)}
    (h : ∀ x ∈ xs, x.Scoped st) : (Snarky.sum xs).Scoped st := by
  unfold Snarky.sum
  suffices hf : ∀ (l : List (FVar F)) (acc : FVar F), acc.Scoped st → (∀ x ∈ l, x.Scoped st) →
      (l.foldl CVar.add_ acc).Scoped st from hf xs _ trivial h
  intro l
  induction l with
  | nil => exact fun _ hacc _ => hacc
  | cons x t ih =>
    intro acc hacc hl
    exact ih _ (hacc.add_ (hl x (List.mem_cons_self ..)))
      (fun y hy => hl y (List.mem_cons_of_mem _ hy))

attribute [irreducible] sum

/-- Fuel-indexed body of `pow`, structural on the fuel: square, recurse on `n / 2`, and
multiply by `x` once more when `n` is odd. The fuel-exhausted branch is unreachable —
`pow` seeds fuel `n`, and the exponent at least halves each step. -/
private def powGo [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] :
    Nat → FVar F → Nat → CircuitM F c (FVar F)
  | _, _, 0 => pure (.const 1)
  | _, x, 1 => pure x
  | 0, x, _ => pure x
  | fuel + 1, x, n => do
    let sq ← mul x x
    let y ← powGo fuel sq (n / 2)
    if n % 2 = 0 then pure y else mul x y

/-- `x ^ n` by repeated squaring — `mul`'s rows, in the recursion's order. On a constant
every step folds, so no rows are emitted. -/
def pow [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (x : FVar F) (n : Nat) :
    CircuitM F c (FVar F) :=
  powGo n x n

open Std.WP in
private theorem powGo_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] :
    ∀ (fuel : Nat) (x : FVar F) (n : Nat), n ≤ fuel + 1 →
      ⦃fun _ => True⦄
      powGo (c := Builder V c) fuel x n
      ⦃fun r _ => r.val V = x.val V ^ n⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro x n hfuel
    match n, hfuel with
    | 0, _ => exact ⟨fun nv _ _ => by simp [powGo, build]⟩
    | 1, _ => exact ⟨fun nv _ _ => by simp [powGo, build]⟩
  | succ fuel ih =>
    intro x n hfuel
    match n with
    | 0 => exact ⟨fun nv _ _ => by simp [powGo, build]⟩
    | 1 => exact ⟨fun nv _ _ => by simp [powGo, build]⟩
    | m + 2 =>
      simp only [powGo]
      vcgen [ih]
      · rename_i hsq _ hy _
        rw [hy, hsq, ← pow_two, ← pow_mul]
        congr 1
        omega
      · rename_i hsq _ hy _ r _ hr
        rw [hr, hy, hsq, ← pow_two, ← pow_mul, mul_comm, ← pow_succ]
        congr 1
        omega
      · omega

open Std.WP in
/-- `pow x n` reads as the operand's `n`-th power. -/
@[spec] theorem pow_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) (n : Nat) :
    ⦃fun _ => True⦄
    pow (c := Builder V c) x n
    ⦃fun r _ => r.val V = x.val V ^ n⦄ :=
  powGo_spec n x n (Nat.le_succ n)

attribute [irreducible] pow

/-! ## The completeness laws

Each gadget's law at the prover's reading (`Snarky.Prover.VCGen`): the operands' readings in, the
result's reading out, the values as parameters. `div`, `equals`, `neq` and `pow` are proved by
composition through the laws of the gadgets they call. -/

section ProverReading

open Snarky.Prover Std.WP

/-! The advices' runs: each returns its value wherever its operands are in scope. -/

/-- `inv.advice` at a nonzero reading returns the inverse. -/
private theorem Prover.inv_advice_run [Field F] [DecidableEq F] {x : FVar F} {s : ProverState F}
    (hx : x.Scoped s) (hne : x.val s.env.get ≠ 0) :
    (inv.advice x).run s.env = .ok (x.val s.env.get)⁻¹ := by
  simp [inv.advice, readVar_run (CircuitType.scoped_fvar.mpr hx), hne]

/-- `mul.advice` returns the product. -/
private theorem Prover.mul_advice_run [Field F] {x y : FVar F} {s : ProverState F}
    (hx : x.Scoped s) (hy : y.Scoped s) :
    (mul.advice x y).run s.env = .ok (x.val s.env.get * y.val s.env.get) := by
  simp [mul.advice, AsProver.readCVar_run hx, AsProver.readCVar_run hy]

/-- `square.advice` returns the square. -/
private theorem Prover.square_advice_run [Field F] {x : FVar F} {s : ProverState F}
    (hx : x.Scoped s) :
    (square.advice x).run s.env = .ok (x.val s.env.get * x.val s.env.get) := by
  simp [square.advice, AsProver.readCVar_run hx]

/-- `isZero.bitAdvice` returns the zero bit. -/
private theorem Prover.isZero_bitAdvice_run [Field F] [DecidableEq F] {x : FVar F}
    {s : ProverState F} (hx : x.Scoped s) :
    (isZero.bitAdvice x).run s.env = .ok (if x.val s.env.get = 0 then 1 else 0) := by
  simp [isZero.bitAdvice, AsProver.readCVar_run hx]

/-- `isZero.invAdvice` returns the inverse, or `0` at a zero reading. -/
private theorem Prover.isZero_invAdvice_run [Field F] [DecidableEq F] {x : FVar F}
    {s : ProverState F} (hx : x.Scoped s) :
    (isZero.invAdvice x).run s.env =
      .ok (if x.val s.env.get = 0 then 0 else (x.val s.env.get)⁻¹) := by
  simp [isZero.invAdvice, AsProver.readCVar_run hx]

/-- `inv`'s completeness: at a nonzero reading, the result reads the inverse. -/
theorem Prover.inv_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x : FVar F) (a : F) (ha : a ≠ 0) :
    ⦃Reads x a⦄ inv (c := Prover c) x ⦃fun r ↦ Reads r a⁻¹⦄ := by
  have hw := fun x' : FVar F ↦ Spec.witness (c := c) (inv.advice x') a⁻¹ valid_fvar
  unfold inv
  vcgen [hw]
  all_goals prover_assert with
    (intros; simp_all [Reads.fvar_apply, Prover.inv_advice_run, Checked.apply,
      LawfulBasicSystem.holds_r1cs, LawfulBasicSystem.cells_r1cs, CVar.val])

/-- `mul`'s completeness: the result reads the product of the operands' readings. -/
theorem Prover.mul_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x y : FVar F) (a b : F) :
    ⦃Reads x a ⊓ Reads y b⦄ mul (c := Prover c) x y ⦃fun r ↦ Reads r (a * b)⦄ := by
  have hw := fun x' y' : FVar F ↦ Spec.witness (c := c) (mul.advice x' y') (a * b) valid_fvar
  unfold mul
  vcgen [hw]
  all_goals prover_assert with
    (intros; simp_all [Reads.fvar_apply, Prover.mul_advice_run, Checked.apply,
      LawfulBasicSystem.holds_r1cs, LawfulBasicSystem.cells_r1cs, CVar.val, CVar.val_scale_,
      CVar.Scoped.scale_, mul_comm])

/-- `square`'s completeness: the result reads the square of the operand's reading. -/
theorem Prover.square_spec [Field F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x : FVar F) (a : F) :
    ⦃Reads x a⦄ square (c := Prover c) x ⦃fun r ↦ Reads r (a * a)⦄ := by
  have hw := fun x' : FVar F ↦ Spec.witness (c := c) (square.advice x') (a * a) valid_fvar
  unfold square
  vcgen [hw]
  all_goals prover_assert with
    (intros; simp_all [Reads.fvar_apply, Prover.square_advice_run, Checked.apply,
      LawfulBasicSystem.holds_square, LawfulBasicSystem.cells_square, CVar.val])

/-- `div`'s completeness, by composition of `inv` and `mul`: at a nonzero divisor, the result
reads the quotient. -/
theorem Prover.div_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x y : FVar F) (a b : F) (hb : b ≠ 0) :
    ⦃Reads x a ⊓ Reads y b⦄ div (c := Prover c) x y ⦃fun r ↦ Reads r (a / b)⦄ := by
  have hi := Prover.inv_spec (c := c) y b hb
  have hm := fun yInv : FVar F ↦ Prover.mul_spec (c := c) x yInv a b⁻¹
  unfold div
  vcgen [hi, hm]
  all_goals prover_assert with
    (intros; simp_all [Reads.fvar_apply, div_eq_mul_inv])

/-- `isZero`'s completeness: the bit reads whether the operand reads `0`. -/
theorem Prover.isZero_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x : FVar F) (a : F) :
    ⦃Reads x a⦄ isZero (c := Prover c) x ⦃fun r ↦ Reads r (decide (a = 0))⦄ := by
  have hb := fun x' : FVar F ↦
    Spec.witness (c := c) (isZero.bitAdvice x') (if a = 0 then (1 : F) else 0) valid_fvar
  have hi := fun x' : FVar F ↦
    Spec.witness (c := c) (isZero.invAdvice x') (if a = 0 then (0 : F) else a⁻¹) valid_fvar
  unfold isZero
  vcgen [hb, hi]
  all_goals prover_assert with
    (intros; (try simp_all [Reads.fvar_apply, Reads.boolVar_apply, Prover.isZero_bitAdvice_run,
      Prover.isZero_invAdvice_run, Checked.apply, LawfulBasicSystem.holds_r1cs,
      LawfulBasicSystem.cells_r1cs, CVar.val, CVar.val_sub_, CVar.Scoped.sub_, bit]);
      (try (split_ifs <;> simp_all)))

/-- `equals`'s completeness: the bit reads whether the operands read equal. -/
theorem Prover.equals_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x y : FVar F) (a b : F) :
    ⦃Reads x a ⊓ Reads y b⦄ equals (c := Prover c) x y ⦃fun r ↦ Reads r (decide (a = b))⦄ := by
  have hz := Prover.isZero_spec (c := c) (CVar.sub_ x y) (a - b)
  unfold equals
  vcgen [hz]
  all_goals prover_assert with
    (intros; simp_all [Reads.fvar_apply, Reads.boolVar_apply, CVar.val_sub_, CVar.Scoped.sub_,
      sub_eq_zero])

/-- `neq`'s completeness: the bit reads whether the operands read unequal. -/
theorem Prover.neq_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x y : FVar F) (a b : F) :
    ⦃Reads x a ⊓ Reads y b⦄ neq (c := Prover c) x y ⦃fun r ↦ Reads r (!decide (a = b))⦄ := by
  have he := Prover.equals_spec (c := c) x y a b
  unfold neq
  vcgen [he]
  all_goals prover_assert with
    (intros; (try simp_all [Reads.boolVar_apply, CVar.val_sub_, CVar.val, CVar.Scoped.sub_,
      bit]); (try (split_ifs <;> simp_all)))

/-- `powGo`'s completeness, along the recursion: within its fuel the result reads the operand's
reading to the `n`-th power. -/
private theorem Prover.powGo_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] :
    ∀ (fuel : Nat) (x : FVar F) (n : Nat) (a : F), n ≤ fuel + 1 →
      ⦃Reads x a⦄ powGo (c := Prover c) fuel x n ⦃fun r ↦ Reads r (a ^ n)⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro x n a hn
    match n, hn with
    | 0, _ =>
      simp only [powGo]
      vcgen
      all_goals prover_assert with (intros; simp_all [Reads.fvar_apply, CVar.val])
    | 1, _ =>
      simp only [powGo]
      vcgen
      simp
  | succ fuel ih =>
    intro x n a hn
    match n with
    | 0 =>
      simp only [powGo]
      vcgen
      all_goals prover_assert with (intros; simp_all [Reads.fvar_apply, CVar.val])
    | 1 =>
      simp only [powGo]
      vcgen
      simp
    | m + 2 =>
      -- the halving step's exponent arithmetic
      have heven : (m + 2) % 2 = 0 → (a * a) ^ ((m + 2) / 2) = a ^ (m + 2) :=
        fun h => by rw [← pow_two, ← pow_mul]; congr 1; omega
      have hodd : ¬(m + 2) % 2 = 0 → a * (a * a) ^ ((m + 2) / 2) = a ^ (m + 2) :=
        fun h => by rw [← pow_two, ← pow_mul, ← pow_succ']; congr 1; omega
      have hsq := Prover.mul_spec (c := c) x x a a
      have hy := fun sq : FVar F ↦ ih sq ((m + 2) / 2) (a * a) (by omega)
      -- the final product's law is left in the context: listed, it would also be taken for the
      -- square
      have hm := fun y : FVar F ↦ Prover.mul_spec (c := c) x y a ((a * a) ^ ((m + 2) / 2))
      simp only [powGo]
      vcgen [hsq, hy]
      all_goals prover_assert with (intros; simp_all [Reads.fvar_apply])

/-- `pow`'s completeness: the result reads the operand's reading to the `n`-th power. -/
theorem Prover.pow_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x : FVar F) (n : Nat) (a : F) :
    ⦃Reads x a⦄ pow (c := Prover c) x n ⦃fun r ↦ Reads r (a ^ n)⦄ := by
  unfold pow
  exact Prover.powGo_spec n x n a (Nat.le_succ n)

end ProverReading

end Snarky
