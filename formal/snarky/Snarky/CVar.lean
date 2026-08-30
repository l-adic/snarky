import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Snarky.Circuit

namespace Snarky

universe u

/-- An affine expression over variables (PS `CVar f`). -/
inductive CVar (F : Type u) where
  | var (v : Variable)
  | const (c : F)
  | add (a b : CVar F)
  | scale (k : F) (x : CVar F)
  deriving Repr, DecidableEq

/-- A single field element as a circuit value (PS `FVar f` is a wrapped `CVar`). -/
abbrev FVar (F : Type u) := CVar F

variable {F : Type u}

/-- Addition, folding `const + const`. No other folding. -/
def CVar.add_ [Add F] : CVar F → CVar F → CVar F
  | .const a, .const b => .const (a + b)
  | a, b => .add a b

/-- Scalar multiple, folding scaling by `0` (to `const 0`) and by `1` (to the operand).
Scaling a constant is deliberately not folded. -/
def CVar.scale_ [Zero F] [One F] [DecidableEq F] (k : F) (x : CVar F) : CVar F :=
  if k = 0 then .const 0
  else if k = 1 then x
  else .scale k x

/-- Negation (PS `negate_`): scaling by `-1`. -/
def CVar.negate_ [Zero F] [One F] [Neg F] [DecidableEq F] (x : CVar F) : CVar F :=
  scale_ (-1) x

/-- Subtraction, folding `const - const`; otherwise `a + (-1)·b`. -/
def CVar.sub_ [Add F] [Sub F] [Zero F] [One F] [Neg F] [DecidableEq F] :
    CVar F → CVar F → CVar F
  | .const a, .const b => .const (a - b)
  | a, b => add_ a (scale_ (-1) b)

/-- Read the value of an affine expression from the current assignments (PS
`readCVar`): read its variables and combine. -/
def AsProver.readCVar [Add F] [Mul F] : CVar F → AsProver F F
  | .var v => .read v .pure
  | .const k => .pure k
  | .add a b => do
    let x ← readCVar a
    let y ← readCVar b
    pure (x + y)
  | .scale k y => do
    let x ← readCVar y
    pure (k * x)

/-- The total evaluation of an affine expression under a valuation. -/
def CVar.val [Add F] [Mul F] : CVar F → (Variable → F) → F
  | .var v, V => V v
  | .const k, _ => k
  | .add a b, V => a.val V + b.val V
  | .scale k x, V => k * x.val V

attribute [simp] CVar.val

/-! The folds are reading-preserving. -/

@[simp] theorem CVar.val_add_ [Add F] [Mul F] (a b : CVar F) (V : Variable → F) :
    (CVar.add_ a b).val V = a.val V + b.val V := by
  cases a <;> cases b <;> simp [CVar.add_, CVar.val]

@[simp] theorem CVar.val_scale_ [Add F] [MulZeroOneClass F] [DecidableEq F] (k : F) (x : CVar F)
    (V : Variable → F) : (CVar.scale_ k x).val V = k * x.val V := by
  unfold CVar.scale_
  split
  · next h => simp [CVar.val, h]
  · split
    · next h => simp [h]
    · rfl

@[simp] theorem CVar.val_negate_ [Ring F] [DecidableEq F] (x : CVar F) (V : Variable → F) :
    (CVar.negate_ x).val V = -x.val V := by
  rw [CVar.negate_, CVar.val_scale_, neg_one_mul]

@[simp] theorem CVar.val_sub_ [Ring F] [DecidableEq F] (a b : CVar F) (V : Variable → F) :
    (CVar.sub_ a b).val V = a.val V - b.val V := by
  cases a <;> cases b <;>
    simp [CVar.sub_, CVar.val_add_, CVar.val_scale_, CVar.val, sub_eq_add_neg]

/-! ## Scope, relative to a variable predicate -/

/-- `x.ScopedBy P`: every variable of the expression satisfies `P`. -/
def CVar.ScopedBy (P : Variable → Prop) : CVar F → Prop
  | .var v => P v
  | .const _ => True
  | .add a b => a.ScopedBy P ∧ b.ScopedBy P
  | .scale _ y => y.ScopedBy P

/-! The folds are scope-preserving. -/

theorem CVar.ScopedBy.add_ {P : Variable → Prop} [Add F] {a b : CVar F} (ha : a.ScopedBy P)
    (hb : b.ScopedBy P) : (CVar.add_ a b).ScopedBy P := by
  cases a <;> cases b <;> first | exact ⟨ha, hb⟩ | trivial

theorem CVar.ScopedBy.scale_ {P : Variable → Prop} [Zero F] [One F] [DecidableEq F] {k : F}
    {x : CVar F} (hx : x.ScopedBy P) : (CVar.scale_ k x).ScopedBy P := by
  unfold CVar.scale_
  split
  · trivial
  · split
    · exact hx
    · exact hx

theorem CVar.ScopedBy.sub_ {P : Variable → Prop} [Add F] [Sub F] [Zero F] [One F] [Neg F]
    [DecidableEq F] {a b : CVar F} (ha : a.ScopedBy P) (hb : b.ScopedBy P) :
    (CVar.sub_ a b).ScopedBy P := by
  cases a <;> cases b <;> first | trivial | exact CVar.ScopedBy.add_ ha hb.scale_

attribute [irreducible] CVar.add_ CVar.scale_ CVar.sub_

/-! ## The canonical affine form -/

/-- The canonical affine form `c + Σ aᵢ·xᵢ` of a `CVar`: an optional constant plus
coefficient terms keyed by variable. -/
structure AffineExpression (F : Type u) where
  /-- The constant summand; `none` contributes `0`. -/
  constant : Option F
  /-- The coefficient terms `(xᵢ, aᵢ)`, in strictly ascending variable order with at most
  one term per variable. -/
  terms : List (Variable × F)
  deriving Repr, DecidableEq

namespace AffineExpression

/-- Insert one coefficient term into an ascending term list, adding coefficients on an
already-present variable. -/
private def insertTerm [Add F] (v : Variable) (a : F) :
    List (Variable × F) → List (Variable × F)
  | [] => [(v, a)]
  | (w, b) :: rest =>
    if v < w then (v, a) :: (w, b) :: rest
    else if v = w then (v, a + b) :: rest
    else (w, b) :: insertTerm v a rest

/-- Union of two ascending term lists, adding coefficients on shared variables. -/
private def unionTerms [Add F] (t₁ t₂ : List (Variable × F)) : List (Variable × F) :=
  t₂.foldl (fun acc vc => insertTerm vc.1 vc.2 acc) t₁

/-- Merge two optional constants, adding when both are present. -/
private def mergeConst [Add F] : Option F → Option F → Option F
  | none, c => c
  | c, none => c
  | some a, some b => some (a + b)

/-- The reading of an affine form: the constant (`0` if absent) plus its terms. -/
def val [Add F] [Mul F] [Zero F] (e : AffineExpression F) (V : Variable → F) : F :=
  e.constant.getD 0 + (e.terms.map fun t => t.2 * V t.1).sum

end AffineExpression

/-- Reduce a `CVar` to its canonical affine form. Constants merge via `mergeConst`, terms
via `unionTerms`; zero coefficients produced by cancellation are filtered at each `add`
node. -/
def CVar.reduceToAffineExpression [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] :
    CVar F → AffineExpression F
  | .var v => ⟨none, [(v, 1)]⟩
  | .const k => ⟨some k, []⟩
  | .add l r =>
    let l' := reduceToAffineExpression l
    let r' := reduceToAffineExpression r
    ⟨AffineExpression.mergeConst l'.constant r'.constant,
      (AffineExpression.unionTerms l'.terms r'.terms).filter (fun t => t.2 != 0)⟩
  | .scale k x =>
    let x' := reduceToAffineExpression x
    ⟨x'.constant.map (k * ·), x'.terms.map (fun t => (t.1, k * t.2))⟩

/-! ## Reduction preserves the reading -/

namespace AffineExpression

variable [CommSemiring F] {V : Variable → F}

private theorem sum_insertTerm (v : Variable) (a : F) (ts : List (Variable × F)) :
    ((insertTerm v a ts).map fun t => t.2 * V t.1).sum =
      a * V v + (ts.map fun t => t.2 * V t.1).sum := by
  induction ts with
  | nil => simp [insertTerm]
  | cons t rest ih =>
    obtain ⟨w, b⟩ := t
    simp only [insertTerm]
    split_ifs with h₁ h₂
    · simp
    · subst h₂; simp [add_mul, add_assoc]
    · simp only [List.map_cons, List.sum_cons]
      rw [ih, add_left_comm]

private theorem sum_unionTerms (t₁ t₂ : List (Variable × F)) :
    ((unionTerms t₁ t₂).map fun t => t.2 * V t.1).sum =
      (t₁.map fun t => t.2 * V t.1).sum + (t₂.map fun t => t.2 * V t.1).sum := by
  induction t₂ generalizing t₁ with
  | nil => simp [unionTerms]
  | cons t rest ih =>
    simp only [unionTerms, List.foldl_cons] at ih ⊢
    rw [ih, sum_insertTerm]
    simp only [List.map_cons, List.sum_cons]
    rw [add_assoc, add_left_comm]

private theorem sum_filter [DecidableEq F] (ts : List (Variable × F)) :
    ((ts.filter fun t => t.2 != 0).map fun t => t.2 * V t.1).sum =
      (ts.map fun t => t.2 * V t.1).sum := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
    by_cases h : t.2 = 0
    · simp [ih, h]
    · simp [bne_iff_ne.mpr h, ih]

private theorem sum_scale (k : F) (ts : List (Variable × F)) :
    ((ts.map fun t => (t.1, k * t.2)).map fun t => t.2 * V t.1).sum =
      k * (ts.map fun t => t.2 * V t.1).sum := by
  induction ts with
  | nil => simp
  | cons t rest ih => simp only [List.map_cons, List.sum_cons, ih, mul_add, mul_assoc]

private theorem getD_mergeConst (a b : Option F) :
    (mergeConst a b).getD 0 = a.getD 0 + b.getD 0 := by
  cases a <;> cases b <;> simp [mergeConst]

end AffineExpression

/-- Reduction preserves the reading. -/
theorem CVar.reduce_val [CommSemiring F] [DecidableEq F] (x : CVar F) (V : Variable → F) :
    x.reduceToAffineExpression.val V = x.val V := by
  induction x with
  | var v => simp [reduceToAffineExpression, AffineExpression.val, CVar.val]
  | const k => simp [reduceToAffineExpression, AffineExpression.val, CVar.val]
  | add l r ihl ihr =>
    simp only [reduceToAffineExpression, AffineExpression.val, CVar.val] at ihl ihr ⊢
    rw [AffineExpression.getD_mergeConst, AffineExpression.sum_filter,
      AffineExpression.sum_unionTerms, ← ihl, ← ihr]
    exact add_add_add_comm ..
  | scale k x ih =>
    simp only [reduceToAffineExpression, AffineExpression.val, CVar.val] at ih ⊢
    rw [AffineExpression.sum_scale, ← ih]
    rcases hc : x.reduceToAffineExpression.constant with _ | a
    · simp
    · simp [mul_add]

/-! ## Reduction stays within the expression's variables -/

namespace AffineExpression

private theorem insertTerm_forall [Add F] {P : Variable → Prop} {v : Variable} {a : F}
    {ts : List (Variable × F)} (hv : P v) (hts : ∀ t ∈ ts, P t.1) :
    ∀ t ∈ insertTerm v a ts, P t.1 := by
  induction ts with
  | nil => simpa [insertTerm] using hv
  | cons s rest ih =>
    obtain ⟨w, b⟩ := s
    have hw : P w := hts _ (List.mem_cons_self ..)
    have hrest : ∀ t ∈ rest, P t.1 := fun t ht => hts t (List.mem_cons_of_mem _ ht)
    simp only [insertTerm]
    split_ifs
    · exact List.forall_mem_cons.mpr ⟨hv, List.forall_mem_cons.mpr ⟨hw, hrest⟩⟩
    · exact List.forall_mem_cons.mpr ⟨hv, hrest⟩
    · exact List.forall_mem_cons.mpr ⟨hw, ih hrest⟩

private theorem unionTerms_forall [Add F] {P : Variable → Prop} {t₁ t₂ : List (Variable × F)}
    (h₁ : ∀ t ∈ t₁, P t.1) (h₂ : ∀ t ∈ t₂, P t.1) : ∀ t ∈ unionTerms t₁ t₂, P t.1 := by
  induction t₂ generalizing t₁ with
  | nil => simpa [unionTerms] using h₁
  | cons s rest ih =>
    simp only [unionTerms, List.foldl_cons] at ih ⊢
    exact ih (insertTerm_forall (h₂ _ (List.mem_cons_self ..)) h₁)
      fun t ht => h₂ t (List.mem_cons_of_mem _ ht)

end AffineExpression

/-- Reduction stays within the expression's variables. -/
theorem CVar.ScopedBy.reduce [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {P : Variable → Prop} {x : CVar F} (hx : x.ScopedBy P) :
    ∀ t ∈ x.reduceToAffineExpression.terms, P t.1 := by
  induction x with
  | var v => simpa [reduceToAffineExpression] using hx
  | const k => simp [reduceToAffineExpression]
  | add l r ihl ihr =>
    intro t ht
    simp only [reduceToAffineExpression, List.mem_filter] at ht
    exact AffineExpression.unionTerms_forall (ihl hx.1) (ihr hx.2) t ht.1
  | scale k x ih =>
    intro t ht
    simp only [reduceToAffineExpression, List.mem_map] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact ih hx s hs

end Snarky
