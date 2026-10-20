import Lean
import Snarky.Prover.WP
import Snarky.Witness
import Snarky.Traverse
import Std.WP
import Std.Tactic.Do

/-!
# EXPERIMENT (toolchain 4.35, not for merge): the prover's reading under `vcgen`

The `Std.WP` interpretation of `CircuitM F (Prover c)` (question 2), the cells frame and its frame
procedure (question 3), and the generic pieces question 4 needs: a run's entry lies below its
exit (`std_le`), the bridge back to the `Std.Do` laws (`do_of_std`), the witness law without its
order conjunct, and the scan step without its order conjunct.
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

/-! ## Question 4: generic pieces -/

/-- Post-consequence for a `Std.WP` triple at the prover's reading. -/
theorem Prover.std_post_mono [Zero F] [ConstraintHolds F c] {α : Type}
    {x : CircuitM F (Prover c) α} {P : ProverState F → Prop} {Q₁ Q₂ : α → ProverState F → Prop}
    (h : ⦃P⦄ x ⦃Q₁⦄) (hQ : ∀ r s, Q₁ r s → Q₂ r s) : ⦃P⦄ x ⦃Q₂⦄ :=
  ⟨fun st hp => proverWP_mono₂ (fun a s h => hQ a s h) (fun _ _ h => h) (h.le_wp st hp)⟩

/-- A run's entry lies below its exit: a property of every run, added to any law whose
precondition names the entry. -/
theorem Prover.std_le [Zero F] [ConstraintHolds F c] {α : Type} {x : CircuitM F (Prover c) α}
    {st₀ : ProverState F} {P : ProverState F → Prop} {Q : α → ProverState F → Prop}
    (h : ⦃fun s => s = st₀ ∧ P s⦄ x ⦃Q⦄) :
    ⦃fun s => s = st₀ ∧ P s⦄ x ⦃fun r s' => Q r s' ∧ st₀ ≤ s'⦄ :=
  ⟨fun st hp => proverWP_frame (Fr := (st₀ ≤ ·)) (fun _ _ h1 h2 => le_trans h2 h1)
    (Q₁ := fun r s => ULift.up.{0} (Q r s))
    (Q₂ := fun r s => ULift.up.{0} (Q r s ∧ st₀ ≤ s)) (fun _ _ hF hq => ⟨hq, hF⟩)
    (le_of_eq hp.1.symm) (h.le_wp st hp)⟩

/-- The witness law, without its order conjunct. -/
theorem Prover.std_witness_of_run [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] {val var : Type}
    [CircuitType F val var] [CheckedType F (Prover c) val var]
    [WPCheckedType F (Prover c) val var] (compute : AsProver F val)
    (pre : ProverState F → Prop) (value : ProverState F → val)
    (hrun : ∀ st, pre st → compute.run st.env = .ok (value st))
    (hvalid : ∀ st, pre st → CheckedType.Valid (F := F) (c := Prover c) (var := var) (value st))
    (st₀ : ProverState F) :
    ⦃fun s => s = st₀ ∧ pre st₀⦄
    witness (c := Prover c) (val := val) compute
    ⦃fun r s' => CircuitType.ReadsAs (val := val) s' r (value st₀)⦄ :=
  Prover.std_of_wp fun st h => by
    refine proverWP_mono₂ ?_ ?_ (Prover.witness_of_run compute pre value hrun hvalid st₀ st h)
    · intro _ _ h; exact h.1
    · intro _ _ h; exact h

section Scan

variable {s α β A X Y : Type}
  (Ss : ProverState F → s → Prop) (Sy : ProverState F → β → Prop)
  (reads : ProverState F → s → A) (readx : ProverState F → α → X) (ready : ProverState F → β → Y)
  (g : A → X → A) (h : A → X → Y)

/-- `Prover.ScanStep` without its order conjunct: what a round proves under the frame. -/
abbrev Prover.ScanStep₀ (st : ProverState F) (acc : s) (x : α) (y : β) (acc' : s)
    (s' : ProverState F) : Prop :=
  Sy s' y ∧ Ss s' acc' ∧ ready s' y = h (reads st acc) (readx st x) ∧
    reads s' acc' = g (reads st acc) (readx st x)

/-- A round's law as written, from its law without the order conjunct. -/
theorem Prover.std_scanStep [ConstraintHolds F c] [Zero F] {f : CircuitM F (Prover c) (β × s)}
    {st : ProverState F} {acc : s} {x : α} {P : ProverState F → Prop}
    (hf : ⦃fun s => s = st ∧ P s⦄ f
      ⦃fun p s' => Prover.ScanStep₀ Ss Sy reads readx ready g h st acc x p.1 p.2 s'⦄) :
    ⦃fun s => s = st ∧ P s⦄ f
      ⦃fun p s' => Prover.ScanStep Ss Sy reads readx ready g h st acc x p.1 p.2 s'⦄ :=
  Prover.std_post_mono (Prover.std_le hf) fun _ _ ⟨⟨a, b, c, d⟩, e⟩ => ⟨a, b, c, d, e⟩

end Scan

open Std.Do in
/-- The bridge back: a `Std.WP` law is the library's `Std.Do` law. -/
theorem Prover.do_of_std [Zero F] [ConstraintHolds F c] {α : Type}
    {x : CircuitM F (Prover c) α} {P : ProverState F → Prop} {Q : α → ProverState F → Prop}
    (h : Std.WP.Triple x P Q Lean.Order.bot) :
    ⦃fun s => ⌜P s⌝⦄ x ⦃⇓ r s => ⌜Q r s⌝⦄ := by
  intro st hp
  exact proverWP_mono₂ (fun _ _ h => h) (fun _ _ h => absurd h (by simp)) (h.le_wp st hp)

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
