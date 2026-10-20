import Lean
import Snarky.Kimchi.Circuit.GroupMap
import Std.WP
import Std.Tactic.Do
import Mathlib.Util.CountHeartbeats

/-!
# Question 3: a frame procedure for `CircuitM F (Prover c)` (experiment sidecar)

The `Std.WP` instance and bridge are Q2's. New here: the frame `CellsAt s₀ vs` ("the cells `vs`,
in scope at the entry `s₀`, keep their scope and their entry readings"), the one lemma that
every program frames it, the leaves restated without `st₀ ≤ s'`, and the `@[frameproc]`.
-/

namespace Snarky

open Lean.Order Std.WP

variable {F c : Type}

/-- The transformer is monotone in both conditions. -/
theorem proverWP_mono₂ [Zero F] [ConstraintHolds F c] {α : Type} {x : CircuitM F c α}
    {Q₁ Q₂ : α → ProverState F → ULift Prop} {E₁ E₂ : EvalError → ProverState F → ULift Prop}
    (hQ : ∀ a s, (Q₁ a s).down → (Q₂ a s).down) (hE : ∀ e s, (E₁ e s).down → (E₂ e s).down)
    {st : ProverState F} (hx : (proverWP x Q₁ E₁ st).down) : (proverWP x Q₂ E₂ st).down := by
  induction x generalizing st with
  | pure a => exact hQ a st hx
  | addConstraintOp con k ih =>
    simp only [proverWP] at hx ⊢
    exact ⟨hx.1, hx.2.1, ih hx.2.2⟩
  | existsOp n wit k ih =>
    simp only [proverWP] at hx ⊢
    rcases hr : wit.run st.env with e | xs <;> rw [hr] at hx
    · exact hE e st hx
    · exact ih _ hx

/-- The prover's reading as a `Std.WP` interpretation. -/
instance Prover.instStdWP [Zero F] [ConstraintHolds F c] {α : Type} :
    Std.WP.WP (CircuitM F (Prover c) α) α (ProverState F → Prop)
      (EvalError → ProverState F → Prop) where
  wpTrans x := ⟨fun post epost st =>
    (proverWP.{0} (c := Prover c) x (fun a s => ULift.up.{0} (post a s))
      (fun e s => ULift.up.{0} (epost e s)) st).down⟩
  wp_trans_monotone _ := fun _ _ _ _ hE hQ _ h =>
    proverWP_mono₂ (fun a s => hQ a s) (fun e s => hE e s) h

/-- The reading is a monad morphism. -/
instance Prover.instStdWPMonad [Zero F] [ConstraintHolds F c] :
    Std.WP.WPMonad (CircuitM F (Prover c)) (ProverState F → Prop)
      (EvalError → ProverState F → Prop) where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := fun _ h => h
  bind_le_wp_bind x f post epost := fun st h => by
    show (proverWP.{0} (c := Prover c) (x >>= f) _ _ st).down
    rw [proverWP_bind]
    exact h

/-- The bridge: a law at the prover's reading, as the transformer it unfolds to, is a `Std.WP`
triple. -/
theorem Prover.std_of_wp [Zero F] [ConstraintHolds F c] {α : Type} {x : CircuitM F (Prover c) α}
    {P : ProverState F → Prop} {Q : α → ProverState F → Prop}
    (h : ∀ st, P st → (proverWP.{0} (c := Prover c) x (fun r s => ULift.up.{0} (Q r s))
      (fun _ _ => ULift.up.{0} False) st).down) :
    ⦃P⦄ x ⦃Q⦄ :=
  ⟨fun st hp => proverWP_mono₂ (fun _ _ h => h) (fun _ _ (h : False) => h.elim) (h st hp)⟩


/-! ## The frame -/

/-- A run carries any predicate that survives table growth: the one transport fact, by
induction on the program. -/
theorem proverWP_frame [Zero F] [ConstraintHolds F c] {α : Type} {x : CircuitM F c α}
    {Fr : ProverState F → Prop} (hmono : ∀ s s', s ≤ s' → Fr s → Fr s')
    {Q₁ Q₂ : α → ProverState F → ULift Prop} {E : EvalError → ProverState F → ULift Prop}
    (hQ : ∀ a s, Fr s → (Q₁ a s).down → (Q₂ a s).down) {st : ProverState F} (hF : Fr st)
    (hx : (proverWP x Q₁ E st).down) : (proverWP x Q₂ E st).down := by
  induction x generalizing st with
  | pure a => exact hQ a st hF hx
  | addConstraintOp con k ih =>
    simp only [proverWP] at hx ⊢
    exact ⟨hx.1, hx.2.1, ih hF hx.2.2⟩
  | existsOp n wit k ih =>
    simp only [proverWP] at hx ⊢
    rcases hr : wit.run st.env with e | xs <;> rw [hr] at hx
    · exact hx
    · exact ih _ (hmono st (st.alloc xs) (st.dom.le_extendList _) hF) hx

/-- The cells `vs`, in scope at the entry `s₀`, are in scope at `s` and read there what they
read at `s₀`. -/
def CellsAt [Add F] [Mul F] [Zero F] (s₀ : ProverState F) : List (CVar F) → ProverState F → Prop
  | [], _ => True
  | v :: vs, s => (v.Scoped s ∧ s.read v = s₀.read v) ∧ CellsAt s₀ vs s

/-- Table growth keeps the frame. -/
theorem CellsAt.mono [Add F] [Mul F] [Zero F] {s₀ : ProverState F} :
    ∀ {vs : List (CVar F)} {s s' : ProverState F}, s ≤ s' → CellsAt s₀ vs s → CellsAt s₀ vs s'
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, hle, ⟨⟨hv, hr⟩, h⟩ =>
    ⟨⟨hv.of_le hle, (ProverState.read_of_le hle hv).trans hr⟩, CellsAt.mono hle h⟩

/-- Every program at the prover's reading frames `CellsAt s₀ vs`. -/
theorem Prover.frames_cellsAt [Field F] [ConstraintHolds F c] {α : Type}
    (x : CircuitM F (Prover c) α) (s₀ : ProverState F) (vs : List (CVar F)) :
    WP.Frames (@Lean.Order.meet (ProverState F → Prop) _) x (CellsAt s₀ vs) := by
  constructor
  intro Q E st h
  rw [meet_apply, meet_prop_eq_and] at h
  exact proverWP_frame (fun _ _ => CellsAt.mono) (Q₁ := fun a s => ULift.up.{0} (Q a s))
    (fun a s hF hq => show Lean.Order.meet (CellsAt s₀ vs) (Q a) s by
      rw [meet_apply, meet_prop_eq_and]; exact ⟨hF, hq⟩) h.1 h.2

/-! The frame procedure's proof that the entry state satisfies the frame it infers. -/

theorem CellsAt.rebase [Add F] [Mul F] [Zero F] {s₀ s : ProverState F} :
    ∀ {vs : List (CVar F)}, CellsAt s₀ vs s → CellsAt s vs s
  | [], _ => trivial
  | _ :: _, ⟨⟨hv, _⟩, h⟩ => ⟨⟨hv, rfl⟩, CellsAt.rebase h⟩

theorem CellsAt.nil_self [Add F] [Mul F] [Zero F] (s : ProverState F) : CellsAt s [] s := trivial

theorem CellsAt.cons_self [Add F] [Mul F] [Zero F] {s : ProverState F} {v : CVar F}
    {vs : List (CVar F)} (hv : v.Scoped s) (h : CellsAt s vs s) : CellsAt s (v :: vs) s :=
  ⟨⟨hv, rfl⟩, h⟩

theorem CVar.scoped_of_eq {s b : ProverState F} {v : CVar F} (h : s = b) (hv : v.Scoped b) :
    v.Scoped s :=
  h ▸ hv

/-! ## The leaves, without `st₀ ≤ s'` -/

set_option experimental.vcgen true

/-- `mul` under a name of its own, so its restated law is the only one registered. -/
def mulQ [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (x y : FVar F) :
    CircuitM F c (FVar F) :=
  mul x y

/-- `div` under a name of its own. -/
def divQ [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (x y : FVar F) :
    CircuitM F c (FVar F) :=
  div x y

@[spec] theorem Prover.mulQ_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x y : FVar F) (st₀ : ProverState F) :
    ⦃fun st => st = st₀ ∧ x.Scoped st₀ ∧ y.Scoped st₀⦄
    mulQ (c := Prover c) x y
    ⦃fun r st' => r.Scoped st' ∧ st'.read r = st₀.read x * st₀.read y⦄ :=
  Prover.std_of_wp fun st h => by
    refine proverWP_mono₂ ?_ ?_ (Prover.mul_spec x y st₀ st h)
    · intro _ _ h; exact ⟨h.1, h.2.1⟩
    · intro _ _ h; exact h

@[spec] theorem Prover.divQ_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x y : FVar F) (st₀ : ProverState F) :
    ⦃fun st => st = st₀ ∧ x.Scoped st₀ ∧ y.Scoped st₀ ∧ st₀.read y ≠ 0⦄
    divQ (c := Prover c) x y
    ⦃fun r st' => r.Scoped st' ∧ st'.read r = st₀.read x / st₀.read y⦄ :=
  Prover.std_of_wp fun st h => by
    refine proverWP_mono₂ ?_ ?_ (Prover.div_spec x y st₀ st h)
    · intro _ _ h; exact ⟨h.1, h.2.1⟩
    · intro _ _ h; exact h

end Snarky

/-! ## The frame procedure -/

namespace Q3

open Lean Meta Lean.Meta.Sym Lean.Meta.Sym.Internal Lean.Elab.Tactic.VCGen

/-- A hypothesis's conjuncts, each with its proof. -/
partial def facts (prop proof : Expr) : MetaM (Array (Expr × Expr)) := do
  let prop ← instantiateMVars prop
  match_expr prop with
  | And a b =>
    return (← facts a (← mkAppM ``And.left #[proof])) ++ (← facts b (← mkAppM ``And.right #[proof]))
  | _ => return #[(prop, proof)]

/-- The frame at the state `s` with its proof at `s`: the cells in scope there, read off the
local context (the `Scoped` facts at `s` or at a state equated with it, and the frame already
carried to `s`), each at its reading at `s`. -/
def cellsFrame (s : Expr) : MetaM (Option (Expr × Expr)) := do
  let mut fs : Array (Expr × Expr) := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    unless ← isProp decl.type do continue
    fs := fs ++ (← facts decl.type decl.toExpr)
  let mut aliases : Array (Expr × Expr) := #[]
  for (p, h) in fs do
    match_expr p with
    | Eq _ a b =>
      if a == s && b.isFVar then aliases := aliases.push (b, h)
      else if b == s && a.isFVar then aliases := aliases.push (a, ← mkEqSymm h)
    | _ => pure ()
  let mut old : Option (List Expr × Expr) := none
  for (p, h) in fs do
    match_expr p with
    | Snarky.CellsAt _ _ _ _ _ vs st =>
      if st == s then
        if let some (_, vs) := vs.listLit? then old := some (vs, h)
    | _ => pure ()
  let oldVs := (old.map (·.1)).getD []
  let mut new : Array (Expr × Expr) := #[]
  for (p, h) in fs do
    match_expr p with
    | Snarky.CVar.Scoped _ st v =>
      if oldVs.contains v || new.any (·.1 == v) then continue
      if st == s then new := new.push (v, h)
      else if let some (_, he) := aliases.find? (·.1 == st) then
        new := new.push (v, ← mkAppM ``Snarky.CVar.scoped_of_eq #[he, h])
    | _ => pure ()
  if new.isEmpty && old.isNone then return none
  let mut proof ← match old with
    | some (_, h) => mkAppM ``Snarky.CellsAt.rebase #[h]
    | none => mkAppM ``Snarky.CellsAt.nil_self #[s]
  for (_, hv) in new.reverse do
    proof ← mkAppM ``Snarky.CellsAt.cons_self #[hv, proof]
  let F := (← whnfR (← inferType s)).appArg!
  let vs := new.toList.map (·.1) ++ oldVs
  let frame ← mkAppM ``Snarky.CellsAt #[s, ← mkListLit (← mkAppM ``Snarky.CVar #[F]) vs]
  return some (frame, proof)

/-- Frame the cells in scope at the call's entry state, with their entry readings, and prove
the entry state satisfies the frame: no frame obligation reaches the user. -/
def cellsFrameProc : FrameInferenceProc := fun i => do
  let #[s] := i.unframedApp.excessArgs | return .decline
  let s ← instantiateMVars s
  let some (frame, proof) ← cellsFrame s | return .decline
  trace[Elab.Tactic.Do.vcgen] "cells frame: {frame}"
  return .commit i.unframedApp.excessArgs fun goal => do
    let frame ← shareCommon frame
    goal.frame.assign frame
    goal.footprint.assign i.pre
    let rhs ← mkAppNS (← mkAppNS (← i.mkOpApp) #[frame, goal.framedApp.wp]) i.unframedApp.excessArgs
    let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppNS i.le #[i.pre, rhs])
    let some gs ← goal.splitLatticeOp? m.mvarId!
      | throwError "frameproc: no lattice split applies to{indentExpr (← m.mvarId!.getType)}"
    -- the split leaves `pre ⊑ W s`, which the spec proves, and `pre ⊑ frame s`, which the
    -- frame's own proof does
    for g in gs do
      if (isWPApp? (← g.getType).appArg!).isSome then g.assign goal.specProof
      else
        let hle ← mkAppM ``Lean.Order.le_of_right #[i.pre, mkApp frame s, proof]
        unless ← isDefEq (← g.getType) (← Meta.inferType hle) do
          throwError "frameproc: the frame proof does not fit{indentExpr (← g.getType)}"
        g.assign hle
    return { splitVCProof := m, subgoals := [] }

/-- `CircuitM`'s frame procedure: the meet frame, inferred as the cells in scope. -/
@[frameproc] def cellsFP : FrameProc where
  prog := ``Snarky.CircuitM
  mkOpAppM := fun info => Meta.mkAppOptM ``Lean.Order.meet #[info.Pred, none]
  mkResourceTy := fun info => pure info.Pred
  opHead := ``Lean.Order.meet
  proc := cellsFrameProc

end Q3

namespace Snarky

open Lean.Order Std.WP

variable {F c : Type}

/-! ## Smoke test: three steps, every operand made earlier -/

def threeMulQ [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] (x y : FVar F) :
    CircuitM F c (FVar F) := do
  let a ← mulQ x y
  let b ← mulQ a x
  mulQ b a

theorem Prover.threeMulQ_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] (x y : FVar F) (st₀ : ProverState F) :
    ⦃fun s => s = st₀ ∧ x.Scoped st₀ ∧ y.Scoped st₀⦄
    threeMulQ (c := Prover c) x y
    ⦃fun r s' => r.Scoped s' ∧
      s'.read r = st₀.read x * st₀.read y * st₀.read x * (st₀.read x * st₀.read y)⦄ := by
  unfold threeMulQ
  vcgen
  all_goals first
    | exact Prover.frames_cellsAt _ _ _
    | ((try simp only [CellsAt] at *); grind [CVar.scoped_of_eq])

/-! ## GroupMap's candidates stage under the frame -/

/-- `gmCandidates` (`Snarky/Kimchi/Circuit/GroupMap.lean`), over the restated leaves. -/
def gmCandidatesQ [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (params : Kimchi.GroupMapParams F) (t : FVar F) :
    CircuitM F c (FVar F × FVar F × FVar F) := do
  let t2 ← mulQ t t
  let t2PlusFu := CVar.add_ t2 (.const params.fu)
  let alphaInv ← mulQ t2PlusFu t2
  let alpha ← divQ (.const 1) alphaInv
  let t4 ← mulQ t2 t2
  let t4Alpha ← mulQ t4 alpha
  let temp1 ← mulQ t4Alpha (.const params.sqrtNeg3U2)
  let x1 := CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) temp1
  let x2 := CVar.sub_ (.const (-params.u)) x1
  let t2Inv ← mulQ alpha t2PlusFu
  let t2PlusFuSq ← mulQ t2PlusFu t2PlusFu
  let temp2a ← mulQ t2PlusFuSq t2Inv
  let temp2 ← mulQ temp2a (.const params.inv3U2)
  let x3 := CVar.sub_ (.const params.u) temp2
  pure (x1, x2, x3)

set_option Elab.async false in
#count_heartbeats in
/-- `Prover.gmCandidates_spec` without `st₀ ≤ s'`, by `vcgen` under the cells frame. -/
theorem Prover.gmCandidatesQ_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (params : Kimchi.GroupMapParams F) (t : FVar F)
    (st₀ : ProverState F) :
    ⦃fun s => s = st₀ ∧ t.Scoped st₀ ∧
      (st₀.read t * st₀.read t + params.fu) * (st₀.read t * st₀.read t) ≠ 0⦄
    gmCandidatesQ (c := Prover c) params t
    ⦃fun r s' => r.1.Scoped s' ∧ r.2.1.Scoped s' ∧ r.2.2.Scoped s' ∧
      s'.read r.1 = (Kimchi.potentialXs params (st₀.read t)).1 ∧
      s'.read r.2.1 = (Kimchi.potentialXs params (st₀.read t)).2.1 ∧
      s'.read r.2.2 = (Kimchi.potentialXs params (st₀.read t)).2.2⦄ := by
  unfold gmCandidatesQ
  vcgen
  all_goals first
    | exact Prover.frames_cellsAt _ _ _
    | ((try simp only [CellsAt] at *)
       grind only [CVar.val, CVar.val_add_, CVar.val_sub_, CVar.Scoped.add_, CVar.Scoped.sub_,
         CVar.scoped_const, Kimchi.potentialXs])

/-! ## Baseline: the in-tree proof (`le_chain`), on this toolchain -/

/-- `gmCandidates`, verbatim, over the library's leaves. -/
def gmCandidatesB [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (params : Kimchi.GroupMapParams F) (t : FVar F) :
    CircuitM F c (FVar F × FVar F × FVar F) := do
  let t2 ← mul t t
  let t2PlusFu := CVar.add_ t2 (.const params.fu)
  let alphaInv ← mul t2PlusFu t2
  let alpha ← div (.const 1) alphaInv
  let t4 ← mul t2 t2
  let t4Alpha ← mul t4 alpha
  let temp1 ← mul t4Alpha (.const params.sqrtNeg3U2)
  let x1 := CVar.sub_ (.const params.sqrtNeg3U2MinusUOver2) temp1
  let x2 := CVar.sub_ (.const (-params.u)) x1
  let t2Inv ← mul alpha t2PlusFu
  let t2PlusFuSq ← mul t2PlusFu t2PlusFu
  let temp2a ← mul t2PlusFuSq t2Inv
  let temp2 ← mul temp2a (.const params.inv3U2)
  let x3 := CVar.sub_ (.const params.u) temp2
  pure (x1, x2, x3)

open Std.Do in
set_option Elab.async false in
#count_heartbeats in
/-- `Prover.gmCandidates_spec`, statement and proof verbatim. -/
theorem Prover.gmCandidatesB_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (params : Kimchi.GroupMapParams F) (t : FVar F)
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ t.Scoped st₀ ∧
      (st₀.read t * st₀.read t + params.fu) * (st₀.read t * st₀.read t) ≠ 0⌝⦄
    gmCandidatesB (c := Prover c) params t
    ⦃⇓ r s' => ⌜r.1.Scoped s' ∧ r.2.1.Scoped s' ∧ r.2.2.Scoped s' ∧
      s'.read r.1 = (Kimchi.potentialXs params (st₀.read t)).1 ∧
      s'.read r.2.1 = (Kimchi.potentialXs params (st₀.read t)).2.1 ∧
      s'.read r.2.2 = (Kimchi.potentialXs params (st₀.read t)).2.2 ∧ st₀ ≤ s'⌝⦄ := by
  unfold gmCandidatesB
  dsimp only
  mvcgen
  -- the abscissae: every reading unwound to the cell's own table by conditional rewriting
  case vc11 =>
    rename_i s₀ h₀ r1 s1 h1 r2 s2 h2 r3 s3 h3 r4 s4 h4 r5 s5 h5 r6 s6 h6 r7 s7 h7 r8 s8 h8
      r9 s9 h9 r10 s10 h10
    simp only [Prover.Reg.iff] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    obtain ⟨rfl, -, -⟩ := h₀
    obtain ⟨c1, v1, l1⟩ := h1
    obtain ⟨c2, v2, l2⟩ := h2
    obtain ⟨c3, v3, l3⟩ := h3
    obtain ⟨c4, v4, l4⟩ := h4
    obtain ⟨c5, v5, l5⟩ := h5
    obtain ⟨c6, v6, l6⟩ := h6
    obtain ⟨c7, v7, l7⟩ := h7
    obtain ⟨c8, v8, l8⟩ := h8
    obtain ⟨c9, v9, l9⟩ := h9
    obtain ⟨c10, v10, l10⟩ := h10
    refine ⟨CVar.Scoped.sub_ trivial (c6.of_le (by le_chain)),
      CVar.Scoped.sub_ trivial (CVar.Scoped.sub_ trivial (c6.of_le (by le_chain))),
      CVar.Scoped.sub_ trivial c10, ?_, ?_, ?_, by le_chain⟩
    all_goals
      simp (disch := le_chain) only [ProverState.read_of_le _ c1, ProverState.read_of_le _ c3,
        ProverState.read_of_le _ c6, ProverState.read_of_le _ c7, ProverState.read_of_le _ c10,
        v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, CVar.val_add_, CVar.val_sub_, CVar.val]
      simp [Kimchi.potentialXs]
  all_goals (try simp only [Prover.Reg.iff] at *)
  all_goals (try grind (ematch := 40) (gen := 40) only [CVar.Scoped.of_le, CVar.Scoped.add_,
    CVar.Scoped.sub_, CVar.scoped_const])
  -- the divisor's reading, from the precondition
  all_goals grind (ematch := 40) (gen := 40) [ProverState.read_of_le, CVar.Scoped.of_le,
    CVar.Scoped.add_, CVar.scoped_const, CVar.val_add_, CVar.val]

end Snarky

#print axioms Snarky.Prover.frames_cellsAt
#print axioms Snarky.Prover.divQ_spec
#print axioms Snarky.Prover.threeMulQ_spec
#print axioms Snarky.Prover.gmCandidatesQ_spec
#print axioms Snarky.Prover.gmCandidatesB_spec
