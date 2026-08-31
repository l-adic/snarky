import Mathlib.Algebra.Field.Basic
import Snarky.BasicSystem
import Snarky.Witness
import Snarky.WP
import Snarky.Prover

set_option mvcgen.warning false

namespace Snarky

variable {F c : Type}

/-- Invert a field variable: witness the inverse, pin it with `x · xInv = 1` (PS `inv_`).
A nonzero constant folds to its constant inverse with no constraint. PS throws at
construction on a constant zero; here it takes the witnessed path, where the witness
fails and the row `0 · xInv = 1` is unsatisfiable. -/
def inv [Field F] [DecidableEq F] [BasicSystem F c] (x : FVar F) : CircuitM F c (FVar F) :=
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

open Std.Do in
@[spec] theorem inv_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) :
    ⦃⌜True⌝⦄
    inv (c := Builder V c) x
    ⦃⇓ r _ => ⌜x.val V * r.val V = 1⌝⦄ := by
  simp only [inv]
  mvcgen
  all_goals first
    | exact (LawfulBasicSystem.holds_r1cs V _ _ _).mp ‹_›
    | exact mul_inv_cancel₀ ‹_›

/-- `inv`'s completeness law: where the operand reads nonzero the run succeeds — the
advice's throw is exactly the zero reading — the row it built is satisfied at every
extension of the final table, and the result is scoped. -/
theorem inv_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) (xv : F) (hne : xv ≠ 0) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st x xv) (inv (c := c) x)
      (fun a st' => CircuitType.ReadsAs (val := F) st' a xv⁻¹) := by
  -- the witnessed arm: advise the inverse, then pin it by the product row. The operand's
  -- reading is framed across the allocation — the row needs it, and the witness rule does
  -- not carry it.
  have hwit : Complete (F := F) (c := c)
      (fun st => CircuitType.ReadsAs (val := F) st x xv)
      (do let r ← witness (val := F) (inv.advice x)
          addConstraint (BasicSystem.r1cs x r (.const 1))
          pure r)
      (fun a st' => CircuitType.ReadsAs (val := F) st' a xv⁻¹) := by
    refine Complete.bind
      (Complete.imp (fun st h => ⟨?_, h⟩) (fun _ _ h => h)
        (Complete.frame Mono.readsAs (Complete.witness (inv.advice x) xv⁻¹ (by simp))))
      (fun r => Complete.bind (Complete.addConstraint ?_)
        fun _ => Complete.pure_of fun _ h => h.1)
    · rintro st ⟨hr, hxr⟩ stf hle
      refine (LawfulBasicSystem.holds_r1cs ..).mpr ?_
      rw [CVar.val_of_le hle (CircuitType.scoped_fvar.mp hxr.1),
        CVar.val_of_le hle (CircuitType.scoped_fvar.mp hr.1),
        CircuitType.reads_fvar.mp hxr.2, CircuitType.reads_fvar.mp hr.2]
      simp [hne]
    · simp [inv.advice, readVar_run h.1, CircuitType.readVal_fvar,
        CircuitType.reads_fvar.mp h.2, hne]
  simp only [inv]
  split
  · rename_i a
    split
    · exact hwit
    · exact Complete.pure_of fun st h =>
        ⟨CircuitType.scoped_fvar.mpr (CVar.scoped_const _ _),
          CircuitType.reads_fvar.mpr (by
            rw [show (CVar.const a⁻¹ : CVar F).val st.env.get = a⁻¹ from rfl,
              ← CircuitType.reads_fvar.mp h.2]
            rfl)⟩
  · exact hwit

attribute [irreducible] inv

/-- Multiply two field variables: constants fold — two constants multiply out, a
constant times an expression folds to `scale_` — otherwise the product is witnessed and
pinned with one `r1cs` row. -/
def mul [Field F] [DecidableEq F] [BasicSystem F c] (x y : FVar F) : CircuitM F c (FVar F) :=
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

open Std.Do in
/-- `mul x y` reads as the product. -/
@[spec] theorem mul_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :
    ⦃⌜True⌝⦄
    mul (c := Builder V c) x y
    ⦃⇓ a _ => ⌜a.val V = x.val V * y.val V⌝⦄ := by
  simp only [mul]
  mvcgen
  all_goals try subst_vars
  all_goals
    first
      | simp [mul_comm]
      | (rename_i h
         exact ((LawfulBasicSystem.holds_r1cs V _ _ _).mp h).symm)

/-- `mul`'s completeness law: from operands that read `xv` and `yv` the run succeeds, the
row it built is satisfied at every extension of the final table, and the result reads
their product — scope and reading together, as `CircuitType.ReadsAs` carries them. -/
theorem mul_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (xv yv : F) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st x xv ∧
        CircuitType.ReadsAs (val := F) st y yv)
      (mul (c := c) x y)
      (fun a st' => CircuitType.ReadsAs (val := F) st' a (xv * yv)) := by
  have hrd : ∀ {st : ProverState F} {v : FVar F} {a : F},
      CircuitType.ReadsAs (val := F) st v a → v.val st.env.get = a :=
    fun h => CircuitType.reads_fvar.mp h.2
  simp only [mul]
  split
  · exact Complete.pure_of fun st h => ⟨CircuitType.scoped_fvar.mpr (CVar.scoped_const _ _),
      CircuitType.reads_fvar.mpr (by rw [← hrd h.1, ← hrd h.2]; rfl)⟩
  · exact Complete.pure_of fun st h =>
      ⟨CircuitType.scoped_fvar.mpr (CVar.Scoped.scale_ (CircuitType.scoped_fvar.mp h.2.1)),
        CircuitType.reads_fvar.mpr (by
          rw [← hrd h.1, ← hrd h.2, CVar.val_scale_]; rfl)⟩
  · exact Complete.pure_of fun st h =>
      ⟨CircuitType.scoped_fvar.mpr (CVar.Scoped.scale_ (CircuitType.scoped_fvar.mp h.1.1)),
        CircuitType.reads_fvar.mpr (by
          rw [← hrd h.1, ← hrd h.2, CVar.val_scale_]
          simp [CVar.val, mul_comm])⟩
  · refine Complete.bind
      (Complete.imp (fun st h => ⟨?_, h⟩) (fun _ _ h => h)
        (Complete.frame (Mono.and Mono.readsAs Mono.readsAs)
          (Complete.witness (mul.advice x y) (xv * yv) (by simp))))
      (fun r => Complete.bind (Complete.addConstraint ?_)
        fun _ => Complete.pure_of fun _ h => h.1)
    · simp [mul.advice, AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.1.1),
        AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.1), hrd h.1, hrd h.2]
    · rintro st ⟨hr, hx, hy⟩ stf hle
      refine (LawfulBasicSystem.holds_r1cs ..).mpr ?_
      rw [CVar.val_of_le hle (CircuitType.scoped_fvar.mp hx.1),
        CVar.val_of_le hle (CircuitType.scoped_fvar.mp hy.1),
        CVar.val_of_le hle (CircuitType.scoped_fvar.mp hr.1), hrd hx, hrd hy, hrd hr]

attribute [irreducible] mul

/-- Square a field variable: a constant folds to its square, otherwise the square is
witnessed and pinned with one `square` row. -/
def square [Field F] [BasicSystem F c] (x : FVar F) : CircuitM F c (FVar F) :=
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

open Std.Do in
/-- `square x` reads as the square. -/
@[spec] theorem square_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) :
    ⦃⌜True⌝⦄
    square (c := Builder V c) x
    ⦃⇓ a _ => ⌜a.val V = x.val V * x.val V⌝⦄ := by
  simp only [square]
  mvcgen
  all_goals try subst_vars
  all_goals
    first
      | simp
      | (rename_i h
         exact ((LawfulBasicSystem.holds_square V _ _).mp h).symm)

/-- `square`'s completeness law: from a state with a scoped operand the run succeeds, the
row it built is satisfied at every extension of the final table, and the result is
scoped. -/
theorem square_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) (xv : F) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st x xv) (square (c := c) x)
      (fun a st' => CircuitType.ReadsAs (val := F) st' a (xv * xv)) := by
  have hrd : ∀ {st : ProverState F} {v : FVar F} {a : F},
      CircuitType.ReadsAs (val := F) st v a → v.val st.env.get = a :=
    fun h => CircuitType.reads_fvar.mp h.2
  simp only [square]
  split
  · exact Complete.pure_of fun st h => ⟨CircuitType.scoped_fvar.mpr (CVar.scoped_const _ _),
      CircuitType.reads_fvar.mpr (by rw [← hrd h]; rfl)⟩
  · refine Complete.bind
      (Complete.imp (fun st h => ⟨?_, h⟩) (fun _ _ h => h)
        (Complete.frame Mono.readsAs (Complete.witness (square.advice x) (xv * xv) (by simp))))
      (fun r => Complete.bind (Complete.addConstraint ?_)
        fun _ => Complete.pure_of fun _ h => h.1)
    · simp [square.advice, AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.1), hrd h]
    · rintro st ⟨hr, hx⟩ stf hle
      refine (LawfulBasicSystem.holds_square ..).mpr ?_
      rw [CVar.val_of_le hle (CircuitType.scoped_fvar.mp hx.1),
        CVar.val_of_le hle (CircuitType.scoped_fvar.mp hr.1), hrd hx, hrd hr]

attribute [irreducible] square

/-- Divide field variables — `x · y⁻¹`: the inverse witnessed and pinned by `inv`, the
product by `mul`. -/
def div [Field F] [DecidableEq F] [BasicSystem F c] (x y : FVar F) :
    CircuitM F c (FVar F) := do
  let yInv ← inv y
  mul x yInv

open Std.Do in
/-- `div`'s soundness: the result reads as the quotient. `inv`'s row forces a nonzero
divisor, so the field's total division is the honest reading with no side condition. -/
@[spec] theorem div_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) :
    ⦃⌜True⌝⦄
    div (c := Builder V c) x y
    ⦃⇓ r _ => ⌜r.val V = x.val V / y.val V⌝⦄ := by
  simp only [div]
  mvcgen
  rename_i _ yInv _ hinv _ _
  intro hmul
  rw [hmul, div_eq_mul_inv, inv_eq_of_mul_eq_one_right hinv]

/-- `div`'s completeness law: where the divisor reads nonzero the run succeeds, the rows
its calls built are satisfied at every extension of the final table, and the result is
scoped — `inv`'s and `mul`'s laws composed, neither reopened. -/
theorem div_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x y : FVar F) (xv yv : F)
    (hne : yv ≠ 0) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st x xv ∧
      CircuitType.ReadsAs (val := F) st y yv)
      (div (c := c) x y) (fun a st' => CircuitType.ReadsAs (val := F) st' a (xv / yv)) := by
  simp only [div]
  exact Complete.bind
    (Complete.imp (fun _ h => ⟨h.2, h.1⟩) (fun _ _ h => h)
      (Complete.frame Mono.readsAs (inv_complete (c := c) y yv hne)))
    fun r => Complete.imp (fun _ h => ⟨h.2, h.1⟩)
      (fun _ _ h => by rwa [div_eq_mul_inv]) (mul_complete (c := c) x r xv yv⁻¹)

attribute [irreducible] div

/-- Test a field variable for zero, returning the answer bit: witness the claimed bit and
the inverse-or-zero, and pin them with `r · x = 0` and `xInv · x = 1 − r` — the first row
kills `r` where `x` is nonzero, the second forces `r = 1` where `x` is zero, so `r` reads
`1` exactly where `x` reads `0` (and in particular reads a bit). A constant folds to the
constant answer with no constraint. -/
def isZero [Field F] [DecidableEq F] [BasicSystem F c] (x : FVar F) :
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

open Std.Do in
/-- `isZero x` reads `1` where `x` reads `0`, and `0` elsewhere. -/
@[spec] theorem isZero_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) :
    ⦃⌜True⌝⦄
    isZero (c := Builder V c) x
    ⦃⇓ r _ => ⌜(↑r : CVar F).val V = if x.val V = 0 then 1 else 0⌝⦄ := by
  simp only [isZero]
  mvcgen
  rename_i h1 _ _ h2
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

/-- `isZero`'s completeness law: from a state with a scoped operand the run succeeds, the
rows it built are satisfied at every extension of the final table, and the result is a
scoped bundle that reads as a bit — the bit taken straight off the witnessed value. -/
theorem isZero_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) (xv : F) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st x xv) (isZero (c := c) x)
      (fun a st' => CircuitType.ReadsAs (val := Bool) st' a (decide (xv = 0))) := by
  have hrd : ∀ {st : ProverState F} {v : FVar F} {a : F},
      CircuitType.ReadsAs (val := F) st v a → v.val st.env.get = a :=
    fun h => CircuitType.reads_fvar.mp h.2
  simp only [isZero]
  split
  · rename_i a
    refine Complete.pure_of fun st h => ⟨CircuitType.scoped_boolVar.mpr trivial,
      CircuitType.reads_boolVar.mpr ?_⟩
    show (CVar.const (if a = 0 then 1 else 0)).val st.env.get = _
    rw [← hrd h]
    by_cases hz : a = 0 <;> simp [hz, bit]
  · refine Complete.bind
      (Complete.imp (fun st h => ⟨?_, h⟩) (fun _ _ h => h)
        (Complete.frame Mono.readsAs
          (Complete.witness (isZero.bitAdvice x) (if xv = 0 then 1 else 0) (by simp))))
      (fun r => Complete.bind
        (Complete.imp (fun st h => ⟨?_, h⟩) (fun _ _ h => h)
          (Complete.frame (Mono.and Mono.readsAs Mono.readsAs)
            (Complete.witness (isZero.invAdvice x) (if xv = 0 then 0 else xv⁻¹) (by simp))))
        (fun rInv => Complete.bind (Complete.addConstraint ?_)
          fun _ => Complete.bind (Complete.addConstraint ?_)
            fun _ => Complete.pure_of fun _ h => ⟨CircuitType.scoped_boolVar.mpr
              (CircuitType.scoped_fvar.mp h.2.1.1), CircuitType.reads_boolVar.mpr ?_⟩))
    · rintro st ⟨hr, hb, hx⟩ stf hle
      rw [BoolVar.coe_unchecked] at hb
      refine (LawfulBasicSystem.holds_r1cs ..).mpr ?_
      rw [CVar.val_of_le hle (CircuitType.scoped_fvar.mp hb.1),
        CVar.val_of_le hle (CircuitType.scoped_fvar.mp hx.1), hrd hb, hrd hx]
      by_cases hz : xv = 0 <;> simp [hz]
    · rintro st ⟨hr, hb, hx⟩ stf hle
      rw [BoolVar.coe_unchecked] at hb
      refine (LawfulBasicSystem.holds_r1cs ..).mpr ?_
      simp only [CVar.val_sub_]
      rw [CVar.val_of_le hle (CircuitType.scoped_fvar.mp hr.1),
        CVar.val_of_le hle (CircuitType.scoped_fvar.mp hx.1),
        CVar.val_of_le hle (CircuitType.scoped_fvar.mp hb.1), hrd hr, hrd hx, hrd hb]
      by_cases hz : xv = 0 <;> simp [hz]
    · rw [hrd h.2.1]
      by_cases hz : xv = 0 <;> simp [hz, bit]
    · simp [isZero.bitAdvice, AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.1), hrd h]
    · simp [isZero.invAdvice, AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.1),
        hrd h.2]

attribute [irreducible] isZero

/-- Equality test, returning the answer bit: `isZero` on the difference — a constant
difference folds, otherwise two rows. -/
def equals [Field F] [DecidableEq F] [BasicSystem F c] (a b : FVar F) :
    CircuitM F c (BoolVar F) :=
  isZero (CVar.sub_ a b)

open Std.Do in
/-- `equals a b` reads `1` where `a` and `b` read equal, and `0` elsewhere. -/
@[spec] theorem equals_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : FVar F) :
    ⦃⌜True⌝⦄
    equals (c := Builder V c) a b
    ⦃⇓ r _ => ⌜(↑r : CVar F).val V = if a.val V = b.val V then 1 else 0⌝⦄ := by
  simp only [equals]
  mvcgen
  simp [sub_eq_zero]

/-- `equals`'s completeness law: `isZero`'s, at the difference. -/
theorem equals_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : FVar F) (av bv : F) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st a av ∧
      CircuitType.ReadsAs (val := F) st b bv)
      (equals (c := c) a b)
      (fun r st' => CircuitType.ReadsAs (val := Bool) st' r (decide (av = bv))) := by
  rintro st ⟨ha, hb⟩
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar]
    at ha hb
  obtain ⟨ha, hva⟩ := ha
  obtain ⟨hb, hvb⟩ := hb
  have h := isZero_complete (c := c) (CVar.sub_ a b) (av - bv) st
    (by
      simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar]
      exact ⟨CVar.Scoped.sub_ ha hb, by rw [CVar.val_sub_, hva, hvb]⟩)
  simpa [sub_eq_zero] using h

attribute [irreducible] equals

/-- The rows `equals` emits, in order — `r · z = 0` then `zInv · z = 1 − r` over the
difference `z` — when the difference is not constant. -/
example [Field F] [DecidableEq F] [BasicSystem F c] (a b : FVar F) (nv : Nat)
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
def neq [Field F] [DecidableEq F] [BasicSystem F c] (a b : FVar F) :
    CircuitM F c (BoolVar F) := do
  let r ← equals a b
  pure (.unchecked (CVar.sub_ (.const 1) ↑r))

open Std.Do in
/-- `neq a b` reads `0` where `a` and `b` read equal, and `1` elsewhere. -/
@[spec] theorem neq_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : FVar F) :
    ⦃⌜True⌝⦄
    neq (c := Builder V c) a b
    ⦃⇓ r _ => ⌜(↑r : CVar F).val V = if a.val V = b.val V then 0 else 1⌝⦄ := by
  simp only [neq]
  mvcgen
  rename_i h
  simp only [BoolVar.coe_unchecked, CVar.val_sub_, CVar.val, h]
  split <;> simp

/-- `neq`'s completeness law: `equals`'s run, its bit negated. -/
theorem neq_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : FVar F) (av bv : F) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st a av ∧
      CircuitType.ReadsAs (val := F) st b bv)
      (neq (c := c) a b)
      (fun r st' => CircuitType.ReadsAs (val := Bool) st' r (!decide (av = bv))) := by
  simp only [neq]
  refine Complete.bind (equals_complete (c := c) a b av bv)
    fun r => Complete.pure_of fun st hbb => ?_
  refine ⟨CircuitType.scoped_boolVar.mpr (CVar.Scoped.sub_ trivial
      (CircuitType.scoped_boolVar.mp hbb.1)), CircuitType.reads_boolVar.mpr ?_⟩
  rw [BoolVar.coe_unchecked, CVar.val_sub_, CircuitType.reads_boolVar.mp hbb.2]
  cases h : decide (av = bv) <;> simp [bit]

attribute [irreducible] neq

/-- `neq` emits exactly `equals`'s rows. -/
example [Field F] [DecidableEq F] [BasicSystem F c] (a b : FVar F) (nv : Nat) :
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
private def powGo [Field F] [DecidableEq F] [BasicSystem F c] :
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
def pow [Field F] [DecidableEq F] [BasicSystem F c] (x : FVar F) (n : Nat) :
    CircuitM F c (FVar F) :=
  powGo n x n

open Std.Do in
private theorem powGo_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] :
    ∀ (fuel : Nat) (x : FVar F) (n : Nat), n ≤ fuel + 1 →
      ⦃⌜True⌝⦄
      powGo (c := Builder V c) fuel x n
      ⦃⇓ r _ => ⌜r.val V = x.val V ^ n⌝⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro x n hfuel
    match n, hfuel with
    | 0, _ => exact fun nv _ _ => by simp [powGo, build]
    | 1, _ => exact fun nv _ _ => by simp [powGo, build]
  | succ fuel ih =>
    intro x n hfuel
    match n with
    | 0 => exact fun nv _ _ => by simp [powGo, build]
    | 1 => exact fun nv _ _ => by simp [powGo, build]
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
/-- `pow x n` reads as the operand's `n`-th power. -/
@[spec] theorem pow_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) (n : Nat) :
    ⦃⌜True⌝⦄
    pow (c := Builder V c) x n
    ⦃⇓ r _ => ⌜r.val V = x.val V ^ n⌝⦄ :=
  powGo_spec n x n (Nat.le_succ n)

private theorem powGo_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] :
    ∀ (fuel : Nat) (x : FVar F) (n : Nat),
      Complete (fun st => x.Scoped st) (powGo (c := c) fuel x n) (fun a st' => a.Scoped st') := by
  have hval : ∀ (v : CVar F) (st : ProverState F), v.Scoped st →
      ∃ a : F, CircuitType.ReadsAs (val := F) st v a :=
    fun v st h => ⟨v.val st.env.get, CircuitType.scoped_fvar.mpr h, rfl⟩
  -- `mul`, at whatever the operands happen to read: the law is indexed by values, the
  -- recursion carries only scope, and `instantiate` is the bridge.
  have hmul : ∀ x y : FVar F, Complete (F := F) (c := c)
      (fun st => x.Scoped st ∧ y.Scoped st) (mul (c := c) x y)
      (fun a st' => a.Scoped st' ∧ x.Scoped st') := by
    intro x y
    refine Complete.instantiate
      (P := fun p : F × F => fun st => (CircuitType.ReadsAs (val := F) st x p.1 ∧
        CircuitType.ReadsAs (val := F) st y p.2) ∧ x.Scoped st)
      (fun st h => ⟨⟨_, _⟩, ⟨(hval x st h.1).choose_spec, (hval y st h.2).choose_spec⟩, h.1⟩)
      fun p => Complete.imp (fun _ h => h) (fun _ _ h => ⟨CircuitType.scoped_fvar.mp h.1.1, h.2⟩)
        (Complete.frame Mono.scoped (mul_complete (c := c) x y p.1 p.2))
  intro fuel
  induction fuel with
  | zero =>
    intro x n
    match n with
    | 0 => exact Complete.pure_of fun _ _ => trivial
    | 1 => exact Complete.pure_of fun _ h => h
    | _ + 2 => exact Complete.pure_of fun _ h => h
  | succ fuel ih =>
    intro x n
    match n with
    | 0 => exact Complete.pure_of fun _ _ => trivial
    | 1 => exact Complete.pure_of fun _ h => h
    | m + 2 =>
      simp only [powGo]
      refine Complete.bind
        (Complete.imp (fun _ h => ⟨h, h⟩) (fun _ _ h => h) (hmul x x))
        fun sq => Complete.bind
          (Complete.imp (fun _ h => h) (fun _ _ h => h)
            (Complete.frame Mono.scoped (ih sq ((m + 2) / 2))))
          fun y => ?_
      by_cases hpar : (m + 2) % 2 = 0
      · rw [if_pos hpar]
        exact Complete.pure_of fun _ h => h.1
      · rw [if_neg hpar]
        exact Complete.imp (fun _ h => ⟨h.2, h.1⟩) (fun _ _ h => h.1) (hmul x y)

/-- `pow`'s completeness law: `mul`'s, along the recursion. -/
theorem pow_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (x : FVar F) (xv : F) (n : Nat) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st x xv) (pow (c := c) x n)
      (fun a st' => CircuitType.ReadsAs (val := F) st' a (xv ^ n)) := by
  intro st hx
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar] at hx ⊢
  obtain ⟨hx, hvx⟩ := hx
  subst hvx
  obtain ⟨r, st₁, hrun, hsat, hsc⟩ := powGo_complete (c := c) n x n st hx
  refine ⟨r, st₁, hrun, hsat, hsc, ?_⟩
  have hval := runs_post (fun V => pow_spec (c := c) (V := V) x n) hrun
    (hsat (Nat.le_refl _) (Assignments.Le.refl _))
  rw [hval, CVar.val_of_le (run_le hrun).2 hx]

attribute [irreducible] pow


end Snarky
