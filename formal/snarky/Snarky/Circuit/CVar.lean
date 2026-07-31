import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

/-!
# Circuit variables and affine expressions

Port of `Snarky.Circuit.CVar` (packages/snarky/src/Snarky/Circuit/CVar.purs): the `CVar`
type of affine expressions over allocated circuit variables, its folding smart
constructors, evaluation against a partial assignment, and the reduction to the canonical
affine form `c + Σ aᵢ·xᵢ` (`AffineExpression`) together with the evaluation-agreement
theorem `reduce_eval` — the property the PS package checks by QuickCheck, proved here.

The public surface is the PS export list, def for def; the public theorems are
`CVar.reduce_eval`, the fold-evaluation lemmas `CVar.eval_add_`/`eval_scale_`/`eval_sub_`,
and their inversions `eval_scale_inv`/`eval_sub_inv` (a successful evaluation evaluates
the operands — how the gadget laws read fresh variables out of
fold-wrapped constraint slots); `DSL/Field.sum_eval` consumes the fold lemmas too.
The affine-form helpers (`insertTerm`, `unionTerms`, `mergeConst`, `evalTerms`) and every
supporting lemma are `private` — PS likewise keeps its `reduce'` internal.

`EvalError` also lives in this module because its PS original does: `EvaluationError` is
defined in `Circuit/CVar.purs`, while the separate `Circuit/EvalError.purs` is only the
JS-exception transport, which `Except` replaces structurally and which is therefore not
ported.

Deviations from the PS original (per `formal/docs/snarky-ps-alignment.md`):
- `Variable` is `Nat` (PS: a newtype over `Int` with `v0`/`incrementVariable`).
- `CVar` is monomorphic in the variable type. PS `CVar f i` is a bifunctor instantiated
  at `i = Variable` (`FVar`) and at `i = Bool Variable` (`BoolVar`'s phantom tag); the
  Lean rendering keeps one index type and makes `BoolVar` a nominal wrapper with a
  private constructor instead (see `Circuit/Types`).
- `const_` is not ported (`CVar.const` is already first-class); the QuickCheck machinery
  (`Arbitrary`, `genWithAssignments`) is not ported — the property it tested is
  `reduce_eval`; the `Semigroup`/`Monoid` instances (zero-folding append) are not ported:
  their would-be consumer `DSL/Field.sum` mirrors PS `sum_`, which folds `add_` directly.
- `EvalError` variants: `unassigned` ↔ PS `MissingVariable`; `custom` subsumes PS
  `FailedAssertion`/`DivisionByZero`; `conflict` and `unsatisfiedConstraint` are
  prover-side additions (our prover may never overwrite an assignment — see
  `Backend/Prover`); PS `WithContext` awaits `labelOp` error attribution.

Definitions keep the weakest classes their bodies need (`Add`, `Mul`, `Zero`, `One`,
`Neg`, `Sub`, `DecidableEq`); the reduction lemmas assume `CommSemiring` via the targeted
Mathlib imports above. Everything is structural recursion, so downstream `decide` works.

The prover's assignment store lives in `Snarky/Backend/Assignments.lean` (its PS home);
`eval` takes a bare lookup `Variable → Option F`, mirroring the PS `eval`'s
`(Variable -> m f)` argument.
-/

namespace Snarky

/-- A circuit variable: an index into the wire assignment, allocated sequentially by the
interpreters (PS `Variable`). -/
abbrev Variable := Nat

/-- Errors arising while running witness code or checking constraints during a prover run
(PS `EvaluationError`, extended with the prover-side failure modes). -/
inductive EvalError where
  /-- A variable was read before being assigned. -/
  | unassigned (v : Variable)
  /-- A variable was assigned twice (assignments may only grow). -/
  | conflict (v : Variable)
  /-- A constraint added via `addConstraint` does not hold on the current assignment. -/
  | unsatisfiedConstraint
  /-- A witness computation failed with a message (PS `throwAsProver`). -/
  | custom (msg : String)
  deriving Repr, DecidableEq

/-! ## Affine expressions -/

/-- Affine expressions over circuit variables (PS `CVar`): variables, constants, sums and
scalings. `sub x y` is expressible as `add x (scale (-1) y)` when `F` has negation, so it is
not a separate constructor. -/
inductive CVar (F : Type u) where
  | var (v : Variable)
  | const (c : F)
  | add (a b : CVar F)
  | scale (k : F) (x : CVar F)
  deriving Repr, DecidableEq

namespace CVar

/-! ## Smart constructors

The PS constructors that fold constants eagerly (`add_`, `sub_`, `scale_`, `negate_`).
The names keep the PS trailing underscore: it does the same disambiguation work here as in
PS, where the plain names are the raw constructors. -/

/-- Addition, folding `const + const` (PS `add_`). No other folding: PS folds exactly this
case. -/
def add_ [Add F] : CVar F → CVar F → CVar F
  | .const a, .const b => .const (a + b)
  | a, b => .add a b

/-- Scalar multiple, folding scaling by `0` (to `const 0`) and by `1` (to the operand)
(PS `scale_`). Scaling a constant is deliberately NOT folded, as in PS. -/
def scale_ [Zero F] [One F] [DecidableEq F] (k : F) (x : CVar F) : CVar F :=
  if k = 0 then .const 0
  else if k = 1 then x
  else .scale k x

/-- Negation as scaling by `-1` (PS `negate_ = scale_ (negate one)`). -/
def negate_ [Zero F] [One F] [Neg F] [DecidableEq F] (x : CVar F) : CVar F :=
  scale_ (-1) x

/-- Subtraction, folding `const - const`; otherwise `a + (-1)·b` (PS `sub_`). -/
def sub_ [Add F] [Sub F] [Zero F] [One F] [Neg F] [DecidableEq F] :
    CVar F → CVar F → CVar F
  | .const a, .const b => .const (a - b)
  | a, b => add_ a (scale_ (-1) b)

/-! ## Evaluation -/

/-- Evaluate an affine expression against a partial assignment, failing on the first
unassigned variable (PS `eval`, monomorphized: PS abstracts the lookup's `Applicative`;
here it is `Except` over the `Variable → Option F` lookup). Written with explicit `match`
(not `do`) so proofs can `split` on the intermediate results. -/
def eval [Add F] [Mul F] : CVar F → (Variable → Option F) → Except EvalError F
  | .var v, env =>
    match env v with
    | some x => .ok x
    | none => .error (.unassigned v)
  | .const k, _ => .ok k
  | .add a b, env =>
    match a.eval env with
    | .error e => .error e
    | .ok x =>
      match b.eval env with
      | .error e => .error e
      | .ok y => .ok (x + y)
  | .scale k x, env =>
    match x.eval env with
    | .error e => .error e
    | .ok y => .ok (k * y)

/-! ## The folds are evaluation-preserving

The smart constructors pre-fold constants; these lemmas say the folds cannot change a
successful evaluation — what connects gadget fast paths to the gadget laws. -/

/-- `add_` evaluates like the raw constructor. -/
theorem eval_add_ [Add F] [Mul F] (a b : CVar F) (env : Variable → Option F) :
    (add_ a b).eval env = (CVar.add a b).eval env := by
  cases a <;> cases b <;> rfl

/-- `scale_` evaluates to the scalar product. -/
theorem eval_scale_ [Add F] [MulZeroOneClass F] [DecidableEq F] {x : CVar F}
    {env : Variable → Option F} {xv : F} (hx : x.eval env = .ok xv) (k : F) :
    (scale_ k x).eval env = .ok (k * xv) := by
  unfold scale_
  split_ifs with h0 h1
  · subst h0; simp [eval]
  · subst h1; simpa using hx
  · simp [eval, hx]

/-- `sub_` evaluates to the difference. -/
theorem eval_sub_ [CommRing F] [DecidableEq F] {a b : CVar F}
    {env : Variable → Option F} {av bv : F}
    (ha : a.eval env = .ok av) (hb : b.eval env = .ok bv) :
    (sub_ a b).eval env = .ok (av - bv) := by
  unfold sub_
  split
  · next c₁ c₂ =>
    simp only [eval, Except.ok.injEq] at ha hb
    subst ha; subst hb; rfl
  · rw [eval_add_]
    have hs := eval_scale_ hb (-1)
    simp only [eval, ha, hs]
    congr 1
    ring

/-- Inversion for `scale_`: a successful evaluation of a NONZERO scaling evaluates its
operand (a zero scaling folds to `const 0` and forgets it — hence the hypothesis). -/
theorem eval_scale_inv [Add F] [MulZeroOneClass F] [DecidableEq F] {k : F} (hk : k ≠ 0)
    {x : CVar F} {env : Variable → Option F} {w : F}
    (h : (scale_ k x).eval env = .ok w) : ∃ xv, x.eval env = .ok xv ∧ w = k * xv := by
  unfold scale_ at h
  rw [if_neg hk] at h
  split_ifs at h with h1
  · exact ⟨w, h, by rw [h1, one_mul]⟩
  · revert h
    show (CVar.scale k x).eval env = _ → _
    simp only [eval]
    split
    · intro h; cases h
    · next xv hxv => intro h; exact ⟨xv, hxv, by simpa using h.symm⟩

/-- Inversion for `sub_`: a successful evaluation evaluates both operands. -/
theorem eval_sub_inv [Field F] [DecidableEq F] {a b : CVar F}
    {env : Variable → Option F} {w : F}
    (h : (sub_ a b).eval env = .ok w) :
    ∃ av bv, a.eval env = .ok av ∧ b.eval env = .ok bv ∧ w = av - bv := by
  unfold sub_ at h
  split at h
  · next c₁ c₂ =>
    exact ⟨c₁, c₂, rfl, rfl, by simpa [eval] using h.symm⟩
  · rw [eval_add_] at h
    revert h
    show (CVar.add a _).eval env = _ → _
    simp only [eval]
    split
    · intro h; cases h
    · next av hav =>
      split
      · intro h; cases h
      · next w' hw' =>
        intro h
        obtain ⟨bv, hbv, rfl⟩ :=
          eval_scale_inv (neg_ne_zero.mpr one_ne_zero) hw'
        exact ⟨av, bv, hav, hbv, by
          simp only [Except.ok.injEq] at h
          rw [← h]; ring⟩

end CVar

/-! ## The canonical affine form -/

/-- The canonical affine form `c + Σ aᵢ·xᵢ` of a `CVar` (PS `AffineExpression`): an
optional constant plus coefficient terms keyed by variable. -/
structure AffineExpression (F : Type u) where
  /-- The constant summand; `none` means no constant contributes (it evaluates as `0`). -/
  constant : Option F
  /-- The coefficient terms `(xᵢ, aᵢ)`, in strictly ascending variable order with at most
  one term per variable — the image of the PS `Map.toUnfoldable`. -/
  terms : List (Variable × F)
  deriving Repr, DecidableEq

namespace AffineExpression

/-- Insert one coefficient term into an ascending term list, adding coefficients on an
already-present variable (PS `Map.insertWith add`). Structural recursion, so it stays
kernel-reducible. -/
private def insertTerm [Add F] (v : Variable) (a : F) : List (Variable × F) → List (Variable × F)
  | [] => [(v, a)]
  | (w, b) :: rest =>
    if v < w then (v, a) :: (w, b) :: rest
    else if v = w then (v, a + b) :: rest
    else (w, b) :: insertTerm v a rest

/-- Union of two ascending term lists, adding coefficients on shared variables
(PS `Map.unionWith (+)`). -/
private def unionTerms [Add F] (t₁ t₂ : List (Variable × F)) : List (Variable × F) :=
  t₂.foldl (fun acc vc => insertTerm vc.1 vc.2 acc) t₁

/-- Merge two optional constants, adding when both are present; `none` acts as "no
contribution" (the PS `Maybe` addition used by `reduceToAffineExpression`). -/
private def mergeConst [Add F] : Option F → Option F → Option F
  | none, c => c
  | c, none => c
  | some a, some b => some (a + b)

/-- The running-sum evaluator underlying `AffineExpression.eval`: accumulate
`acc + Σ aᵢ·xᵢ` over the term list, failing on the first unassigned variable. -/
private def evalTerms [Add F] [Mul F] (env : Variable → Option F) (acc : F) :
    List (Variable × F) → Except EvalError F
  | [] => .ok acc
  | (v, k) :: rest =>
    match env v with
    | none => .error (.unassigned v)
    | some x => evalTerms env (acc + k * x) rest

/-- Evaluate the affine form against a partial assignment (PS `evalAffineExpression`):
start from the constant (`0` if `none`) and accumulate the terms left to right. -/
def eval [Add F] [Mul F] [Zero F] (e : AffineExpression F) (env : Variable → Option F) :
    Except EvalError F :=
  evalTerms env (e.constant.getD 0) e.terms

end AffineExpression

namespace CVar

/-- Reduce a `CVar` to its canonical affine form (PS `reduceToAffineExpression`).
Constants merge via `mergeConst`, terms via `unionTerms`; zero coefficients produced by
cancellation are filtered at each `add` node, exactly as in PS. -/
def reduceToAffineExpression [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] :
    CVar F → AffineExpression F
  | .var v => ⟨none, [(v, 1)]⟩
  | .const k => ⟨some k, []⟩
  | .add l r =>
    ⟨AffineExpression.mergeConst
        (reduceToAffineExpression l).constant (reduceToAffineExpression r).constant,
      (AffineExpression.unionTerms
        (reduceToAffineExpression l).terms (reduceToAffineExpression r).terms).filter
        (fun t => t.2 != 0)⟩
  | .scale k x =>
    ⟨(reduceToAffineExpression x).constant.map (k * ·),
      (reduceToAffineExpression x).terms.map (fun t => (t.1, k * t.2))⟩

end CVar

/-! ## Reduction agrees with evaluation

The PS test suite checks by QuickCheck that `eval` agrees with
`evalAffineExpression ∘ reduceToAffineExpression`; here the agreement is the theorem
`CVar.reduce_eval`. The direction is "AST success is preserved": a successful `CVar.eval`
forces every variable of the expression to be assigned, so the canonical form evaluates to
the same value. (The converse fails by design: an `add` node filters terms whose
coefficients cancel to zero, so the affine form can succeed where the AST evaluation reads
an unassigned variable with net coefficient zero.) All lemmas here are private
machinery; the public result is `CVar.reduce_eval` at the end of the section. -/

namespace AffineExpression

/-- Shifting the accumulator shifts a successful running sum. -/
private theorem evalTerms_shift [CommSemiring F] {env : Variable → Option F} (a : F) :
    ∀ {t : List (Variable × F)} {b w : F}, evalTerms env b t = .ok w →
      evalTerms env (a + b) t = .ok (a + w) := by
  intro t
  induction t with
  | nil =>
    intro b w h
    simp only [evalTerms, Except.ok.injEq] at h ⊢
    rw [h]
  | cons vk rest ih =>
    obtain ⟨v, k⟩ := vk
    intro b w h
    simp only [evalTerms] at h ⊢
    cases henv : env v with
    | none => simp only [henv] at h; cases h
    | some x =>
      simp only [henv] at h ⊢
      rw [add_assoc]
      exact ih h

/-- A successful running sum at any accumulator restarts from `0`: the total splits into
the accumulator plus the terms' own contribution. -/
private theorem evalTerms_unshift [CommSemiring F] {env : Variable → Option F} :
    ∀ {t : List (Variable × F)} {b w : F}, evalTerms env b t = .ok w →
      ∃ w', evalTerms env 0 t = .ok w' ∧ w = b + w' := by
  intro t
  induction t with
  | nil =>
    intro b w h
    simp only [evalTerms, Except.ok.injEq] at h
    exact ⟨0, rfl, by rw [← h, add_zero]⟩
  | cons vk rest ih =>
    obtain ⟨v, k⟩ := vk
    intro b w h
    simp only [evalTerms] at h ⊢
    cases henv : env v with
    | none => simp only [henv] at h; cases h
    | some x =>
      simp only [henv] at h ⊢
      obtain ⟨w', hw', rfl⟩ := ih h
      simp only [zero_add]
      refine ⟨k * x + w', ?_, by rw [add_assoc]⟩
      have hshift := evalTerms_shift (env := env) (k * x) hw'
      rwa [add_zero] at hshift

/-- A successful running sum forces every listed variable to be assigned. -/
private theorem evalTerms_assigned [Add F] [Mul F] {env : Variable → Option F} :
    ∀ {t : List (Variable × F)} {b w : F}, evalTerms env b t = .ok w →
      ∀ p ∈ t, ∃ x, env p.1 = some x := by
  intro t
  induction t with
  | nil => intro _ _ _ p hp; cases hp
  | cons vk rest ih =>
    obtain ⟨v, k⟩ := vk
    intro b w h p hp
    simp only [evalTerms] at h
    cases henv : env v with
    | none => simp only [henv] at h; cases h
    | some x =>
      simp only [henv] at h
      rcases List.mem_cons.mp hp with rfl | hmem
      · exact ⟨x, henv⟩
      · exact ih h p hmem

/-- Inserting a term for an assigned variable folds its contribution into the
accumulator. -/
private theorem evalTerms_insertTerm [CommSemiring F] {env : Variable → Option F}
    {v : Variable} {x : F} (hv : env v = some x) (k : F) :
    ∀ (t : List (Variable × F)) (acc : F),
      evalTerms env acc (insertTerm v k t) = evalTerms env (acc + k * x) t := by
  intro t
  induction t with
  | nil => intro acc; simp [insertTerm, evalTerms, hv]
  | cons wb rest ih =>
    obtain ⟨w, b⟩ := wb
    intro acc
    by_cases hlt : v < w
    · simp only [insertTerm]
      rw [if_pos hlt]
      simp only [evalTerms, hv]
    · by_cases heq : v = w
      · subst heq
        simp only [insertTerm]
        rw [if_neg hlt]
        simp only [if_true, evalTerms, hv]
        have hacc : acc + (k + b) * x = acc + k * x + b * x := by ring
        rw [hacc]
      · simp only [insertTerm]
        rw [if_neg hlt, if_neg heq]
        cases henv : env w with
        | none => simp only [evalTerms, henv]
        | some y =>
          simp only [evalTerms, henv]
          rw [ih]
          have hacc : acc + b * y + k * x = acc + k * x + b * y := by ring
          rw [hacc]

/-- Union with a successfully-evaluating term list folds its total into the
accumulator. -/
private theorem evalTerms_unionTerms [CommSemiring F] {env : Variable → Option F} :
    ∀ {t₂ : List (Variable × F)} {s₂ : F}, evalTerms env 0 t₂ = .ok s₂ →
      ∀ (t₁ : List (Variable × F)) (acc : F),
        evalTerms env acc (unionTerms t₁ t₂) = evalTerms env (acc + s₂) t₁ := by
  intro t₂
  induction t₂ with
  | nil =>
    intro s₂ h t₁ acc
    simp only [evalTerms, Except.ok.injEq] at h
    have h0 : unionTerms t₁ ([] : List (Variable × F)) = t₁ := rfl
    rw [h0, ← h, add_zero]
  | cons vk rest ih =>
    obtain ⟨v, k⟩ := vk
    intro s₂ h t₁ acc
    simp only [evalTerms] at h
    cases henv : env v with
    | none => simp only [henv] at h; cases h
    | some x =>
      simp only [henv] at h
      obtain ⟨s', hs', rfl⟩ := evalTerms_unshift h
      have hfold : unionTerms t₁ ((v, k) :: rest) = unionTerms (insertTerm v k t₁) rest :=
        rfl
      rw [hfold, ih hs', evalTerms_insertTerm henv]
      have hacc : acc + s' + k * x = acc + (0 + k * x + s') := by ring
      rw [hacc]

/-- Filtering zero-coefficient terms preserves the running sum when every listed variable
is assigned (the PS `Map.filter (_ /= zero)` at `add` nodes). -/
private theorem evalTerms_filter [CommSemiring F] [DecidableEq F] {env : Variable → Option F} :
    ∀ t : List (Variable × F), (∀ p ∈ t, ∃ x, env p.1 = some x) →
      ∀ acc : F,
        evalTerms env acc (t.filter (fun p => p.2 != 0)) = evalTerms env acc t := by
  intro t
  induction t with
  | nil => intro _ _; rfl
  | cons vk rest ih =>
    obtain ⟨v, k⟩ := vk
    intro hassigned acc
    obtain ⟨x, hx⟩ := hassigned (v, k) (List.mem_cons_self ..)
    have hrest := fun p hp => hassigned p (List.mem_cons_of_mem _ hp)
    by_cases hk : k = 0
    · subst hk
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, if_false,
        evalTerms, hx, zero_mul, add_zero, ih hrest]
    · simp only [List.filter_cons, bne_iff_ne, ne_eq, hk, not_false_eq_true, if_true,
        evalTerms, hx, ih hrest]

/-- Scaling every coefficient scales a successful running sum (with the accumulator
scaled alongside). -/
private theorem evalTerms_scale [CommSemiring F] {env : Variable → Option F} (k : F) :
    ∀ {t : List (Variable × F)} {acc w : F}, evalTerms env acc t = .ok w →
      evalTerms env (k * acc) (t.map (fun p => (p.1, k * p.2))) = .ok (k * w) := by
  intro t
  induction t with
  | nil =>
    intro acc w h
    simp only [evalTerms, List.map_nil, Except.ok.injEq] at h ⊢
    rw [h]
  | cons vb rest ih =>
    obtain ⟨v, b⟩ := vb
    intro acc w h
    simp only [evalTerms, List.map_cons] at h ⊢
    cases henv : env v with
    | none => simp only [henv] at h; cases h
    | some x =>
      simp only [henv] at h ⊢
      have hacc : k * acc + k * b * x = k * (acc + b * x) := by ring
      rw [hacc]
      exact ih h

/-- `mergeConst` matches addition under the `getD 0` reading of the constants. -/
private theorem mergeConst_getD [CommSemiring F] (c₁ c₂ : Option F) :
    (mergeConst c₁ c₂).getD 0 = c₁.getD 0 + c₂.getD 0 := by
  cases c₁ <;> cases c₂ <;> simp [mergeConst]

end AffineExpression

namespace CVar

open AffineExpression in
/-- Reduction preserves successful evaluation: if a `CVar` evaluates, its canonical affine
form evaluates to the same value. This is the PS QuickCheck property "`eval` agrees with
`evalAffineExpression ∘ reduceToAffineExpression`" as a theorem. -/
theorem reduce_eval [CommSemiring F] [DecidableEq F] {x : CVar F} {env : Variable → Option F}
    {v : F} (h : x.eval env = .ok v) :
    x.reduceToAffineExpression.eval env = .ok v := by
  induction x generalizing v with
  | var w =>
    simp only [eval] at h
    cases henv : env w with
    | none => simp only [henv] at h; cases h
    | some y =>
      simp only [henv] at h
      cases h
      simp [reduceToAffineExpression, AffineExpression.eval, evalTerms, henv]
  | const k =>
    simp only [eval, Except.ok.injEq] at h
    subst h
    simp [reduceToAffineExpression, AffineExpression.eval, evalTerms]
  | add l r ihl ihr =>
    simp only [eval] at h
    split at h
    · cases h
    · next a ha =>
      split at h
      · cases h
      · next b hb =>
        cases h
        have hl := ihl ha
        have hr := ihr hb
        simp only [AffineExpression.eval] at hl hr ⊢
        obtain ⟨sl, hsl, rfl⟩ := evalTerms_unshift hl
        obtain ⟨sr, hsr, rfl⟩ := evalTerms_unshift hr
        simp only [reduceToAffineExpression, mergeConst_getD]
        have hunion :
            evalTerms env
                ((reduceToAffineExpression l).constant.getD 0 +
                  (reduceToAffineExpression r).constant.getD 0)
                (unionTerms (reduceToAffineExpression l).terms
                  (reduceToAffineExpression r).terms) =
              .ok ((reduceToAffineExpression l).constant.getD 0 + sl +
                ((reduceToAffineExpression r).constant.getD 0 + sr)) := by
          rw [evalTerms_unionTerms hsr]
          have hshift := evalTerms_shift (env := env)
            ((reduceToAffineExpression l).constant.getD 0 +
              (reduceToAffineExpression r).constant.getD 0 + sr) hsl
          rw [add_zero] at hshift
          rw [hshift]
          congr 1
          ring
        rw [evalTerms_filter _ (evalTerms_assigned hunion), hunion]
  | scale k x ih =>
    simp only [eval] at h
    split at h
    · cases h
    · next y hy =>
      cases h
      have hx := ih hy
      simp only [AffineExpression.eval] at hx ⊢
      simp only [reduceToAffineExpression]
      have hconst : ((reduceToAffineExpression x).constant.map (k * ·)).getD 0 =
          k * (reduceToAffineExpression x).constant.getD 0 := by
        cases (reduceToAffineExpression x).constant <;> simp
      rw [hconst]
      exact evalTerms_scale k hx

end CVar

end Snarky
