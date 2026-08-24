import Snarky.Pilot.Vocab

/-!
# Pilot: `xor`

Two bits, one row. What the deployed gadget adds is PS's constant folding: four branches,
three of them constraint-free. The folding is a decision (`xorFold`); the gadget is the
decision over its core (`folded`); the decision's facts are stated once.

A completeness law says only that the honest run accepts and what it returns is in scope
(`Runs`, course Ch9). What the result reads as is the soundness law's business: the
honest table satisfies every row the builder emits, so it is one of the valuations the
spec quantifies over (`complete_of_sound`, course §9.5). Growth of the table is a law of
the calculus (`prove_assignments_le`).
-/

namespace Snarky.Pilot

open Snarky Std.Do

variable {F c : Type}

/-! ## The run relation, and the simulation

Belongs in `Backend/WP.lean`: `SoundChecker` is the soundness direction `LawfulChecker`
lacks, and `complete_of_sound` is the bridge between the two readings. -/

/-- `g` at `st` accepts, returning `r` at `st'`. -/
def Runs [Add F] [Mul F] [Zero F] [Checker F c] {α : Type} (g : CircuitM F c α)
    (st : ProverState F) (r : α) (st' : ProverState F) : Prop :=
  prove (Checker.holds (F := F) (c := c)) g st.nv st.env = .ok (st'.out r)

/-- Every run grows the table — the calculus's law, never a gadget's. -/
theorem Runs.le [Add F] [Mul F] [Zero F] [Checker F c] {α : Type} {g : CircuitM F c α}
    {st st' : ProverState F} {r : α} (h : Runs g st r st') : st.env.Le st'.env :=
  prove_assignments_le h

/-- `pure` runs in place. -/
theorem Runs.pure [Add F] [Mul F] [Zero F] [Checker F c] {α : Type} {a : α}
    {st : ProverState F} : Runs (pure a : CircuitM F c α) st a st :=
  rfl

/-- A sequence runs through the intermediate state. -/
theorem Runs.bind [Add F] [Mul F] [Zero F] [Checker F c] {α β : Type} {x : CircuitM F c α}
    {f : α → CircuitM F c β} {st st' st'' : ProverState F} {a : α} {b : β}
    (h₁ : Runs x st a st') (h₂ : Runs (f a) st' b st'') : Runs (x >>= f) st b st'' := by
  simp only [Runs, prove_bind] at h₁ h₂ ⊢
  rw [h₁]
  exact h₂

/-- The checker's soundness: an accepted row holds at the table's total reading, and
stays accepted as the table grows. -/
class SoundChecker (F c : Type) [Add F] [Mul F] [Zero F] [Checker F c] [ConstraintHolds F c] :
    Prop where
  /-- An accepted row holds at the total reading. -/
  holds_of_check : ∀ (con : c) (env : Assignments F),
    Checker.holds con env = true → ConstraintHolds.Holds env.toValuation con
  /-- An accepted row stays accepted as the table grows. -/
  check_mono : ∀ (con : c) {a a' : Assignments F},
    a.Le a' → Checker.holds con a = true → Checker.holds con a' = true

/-- `Basic`'s reading is its checker at the total table. -/
instance Basic.instSoundChecker [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] :
    SoundChecker F (Basic F) where
  holds_of_check _ env h := Basic.holds_mono (Assignments.le_toValuation env) h
  check_mono _ _ _ hle h := Basic.holds_mono hle h

/-- A program, read at the soundness tag. -/
abbrev atBuilder (V : Valuation F) {α : Type} (g : CircuitM F c α) :
    CircuitM F (Builder V c) α := g

/-- **The simulation.** A run's result satisfies, at the table it lands on, every
soundness law of the program: the honest table passed every emitted row, so it is one
of the valuations the law quantifies over. -/
theorem complete_of_sound [Add F] [Mul F] [Zero F] [Checker F c] [ConstraintHolds F c]
    [SoundChecker F c] {α : Type} {g : CircuitM F c α} {post : Valuation F → α → Prop}
    (hspec : ∀ V : Valuation F, ⦃⌜True⌝⦄ atBuilder V g ⦃⇓ r _ => ⌜post V r⌝⦄)
    {st st' : ProverState F} {r : α} (h : Runs g st r st') : post st'.env.toValuation r := by
  have hb := (builder_spec_iff (V := st'.env.toValuation) (atBuilder _ g)
    (post st'.env.toValuation)).mp (hspec _) st.nv
  have hc := prove_complete (holds := Checker.holds (F := F) (c := c))
    (fun con _ _ hle hh => SoundChecker.check_mono con hle hh) h
  have hres : (build (atBuilder st'.env.toValuation g) st.nv).result = r :=
    (prove_build_agrees h).1
  rw [hres] at hb
  exact hb fun con hcon => SoundChecker.holds_of_check (c := c) con _ (hc con hcon)

/-! ## The folding combinator -/

/-- A gadget with a constant-folding decision: the fold's answer, else the core. -/
def folded {β : Type} (fold : Option β) (core : CircuitM F c β) : CircuitM F c β :=
  match fold with
  | some r => pure r
  | none => core

/-- A sound law lifts through the fold when the fold's answers satisfy it. -/
theorem folded_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    {β : Type} {V : Valuation F} {fold : Option β}
    {core : CircuitM F (Builder V c) β} {P : β → Prop} (hfold : ∀ r, fold = some r → P r)
    (hcore : ⦃⌜True⌝⦄ core ⦃⇓ r _ => ⌜P r⌝⦄) :
    ⦃⌜True⌝⦄ folded fold core ⦃⇓ r _ => ⌜P r⌝⦄ := by
  unfold folded
  cases h : fold
  · exact hcore
  · exact fun _ _ _ => hfold _ h

/-- A run lifts through the fold when the fold's answer is in scope. -/
theorem folded_complete [Add F] [Mul F] [Zero F] [Checker F c] {β : Type} {fold : Option β}
    {core : CircuitM F c β} {st : ProverState F} {Q : β → ProverState F → Prop}
    (hfold : ∀ r, fold = some r → Q r st) (hcore : ∃ r st', Runs core st r st' ∧ Q r st') :
    ∃ r st', Runs (folded fold core) st r st' ∧ Q r st' := by
  unfold folded
  cases h : fold
  · exact hcore
  · exact ⟨_, st, rfl, hfold _ h⟩

/-! ## The gadget -/

/-- PS's constant folding for `xor`: the answer when a constant operand decides it. -/
def xorFold [Field F] [DecidableEq F] (a b : BoolVar F) : Option (BoolVar F) :=
  match (↑a : CVar F), (↑b : CVar F) with
  | .const av, .const bv => some (.unchecked (.const (if av = bv then 0 else 1)))
  | .const av, _ => if av = 0 then some b else if av = 1 then some (Snarky.not b) else none
  | _, .const bv => if bv = 0 then some a else if bv = 1 then some (Snarky.not a) else none
  | _, _ => none

/-- The advice: the bit `a ≠ b`. -/
private def xorWit [Add F] [Mul F] [DecidableEq F] (a b : BoolVar F) :
    AsProver F (UnChecked Bool) := do
  let av ← AsProver.readCVar ↑a
  let bv ← AsProver.readCVar ↑b
  pure ⟨decide (av ≠ bv)⟩

/-- The row: witness the bit, pin it with `2a · b = a + b − r`. -/
private def xorCore [Field F] [DecidableEq F] [BasicSystem F c] (a b : BoolVar F) :
    CircuitM F c (BoolVar F) := do
  let res ← witness (val := UnChecked Bool) (xorWit a b)
  addConstraint (BasicSystem.r1cs (CVar.add_ (↑a : CVar F) ↑a) ↑b
    (CVar.sub_ (CVar.add_ ↑a ↑b) ↑res.val))
  pure res.val

/-- Exclusive or (PS `xor_`): the fold's answer, else the row. -/
def xor [Field F] [DecidableEq F] [BasicSystem F c] (a b : BoolVar F) :
    CircuitM F c (BoolVar F) :=
  folded (xorFold a b) (xorCore a b)

/-- The pilot gadget is the deployed one. -/
theorem xor_eq [Field F] [DecidableEq F] [BasicSystem F c] (a b : BoolVar F) :
    xor (c := c) a b = Snarky.xor a b := by
  unfold xor folded xorFold Snarky.xor
  cases (↑a : CVar F) <;> cases (↑b : CVar F) <;> (try simp only []) <;> (try split_ifs) <;> rfl

/-! ## The fold's two facts — the one place the cases are opened -/

/-- The fold's answer reads as the xor bit. -/
theorem xorFold_val [Field F] [DecidableEq F] {V : Valuation F} {a b r : BoolVar F}
    {ab bb : Bool} (h : xorFold a b = some r) (hav : (↑a : CVar F).val V = bit ab)
    (hbv : (↑b : CVar F).val V = bit bb) : (↑r : CVar F).val V = bit (ab ^^ bb) := by
  revert h hav hbv
  unfold xorFold
  cases hA : (↑a : CVar F) <;> cases hB : (↑b : CVar F) <;> (try simp only []) <;>
    intro h hav hbv <;> (try split_ifs at h) <;> cases h <;>
    cases ab <;> cases bb <;>
    simp_all [CVar.val, CVar.val_sub_, bit, BoolVar.toCVar_unchecked, Snarky.not]

/-- The fold's answer is in scope when the operands are. -/
theorem xorFold_scoped [Field F] [DecidableEq F] {st : ProverState F} {a b r : BoolVar F}
    (h : xorFold a b = some r) (ha : (↑a : CVar F).Scoped st) (hb : (↑b : CVar F).Scoped st) :
    (↑r : CVar F).Scoped st := by
  revert h
  unfold xorFold
  cases (↑a : CVar F) <;> cases (↑b : CVar F) <;> (try simp only []) <;>
    intro h <;> (try split_ifs at h) <;> cases h <;>
    first | trivial | exact ha | exact hb | exact not_scoped ha | exact not_scoped hb

/-! ## Soundness -/

/-- `2a · b = a + b − r` pins `r` to the xor bit. -/
private theorem xor_pin [CommRing F] {ab bb : Bool} {rv : F}
    (h : ((bit ab : F) + bit ab) * bit bb = bit ab + bit bb - rv) :
    rv = bit (ab ^^ bb) := by
  have h' : rv = (bit ab : F) + bit bb - (bit ab + bit ab) * bit bb := by
    rw [eq_sub_iff_add_eq] at h ⊢
    rw [← h]
    ring
  rw [h']
  cases ab <;> cases bb <;> simp [bit]

/-- The row pins the result. -/
private theorem xorCore_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :
    ⦃⌜True⌝⦄
    xorCore (c := Builder V c) a b
    ⦃⇓ r _ => ⌜∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab ^^ bb)⌝⦄ := by
  intro nv _ hsat ab bb ha hb
  have h := LawfulBasicSystem.holds_r1cs V _ _ _ (hsat _ (List.mem_cons_self ..))
  simp only [circuitVal] at h
  rw [ha, hb] at h
  exact xor_pin h

/-- `xor`: on bit operands the result reads as the xor bit. -/
@[spec] theorem xor_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :
    ⦃⌜True⌝⦄
    xor (c := Builder V c) a b
    ⦃⇓ r _ => ⌜∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (ab ^^ bb)⌝⦄ := by
  refine folded_spec ?_ (xorCore_spec (c := c) (V := V) a b)
  exact fun _ h _ _ hav hbv => xorFold_val h hav hbv

/-! ## Completeness -/

/-- The row's honest run on bit operands accepts, returning a fresh bit. -/
private theorem xorCore_complete [Field F] [DecidableEq F] [BasicSystem F c] [Checker F c]
    [LawfulChecker F c] {a b : BoolVar F} {ab bb : Bool} (st : ProverState F)
    (ha : (↑a : CVar F).Scoped st) (hb : (↑b : CVar F).Scoped st)
    (hav : (↑a : CVar F).val st.env.toValuation = bit ab)
    (hbv : (↑b : CVar F).val st.env.toValuation = bit bb) :
    ∃ r st', Runs (xorCore (c := c) a b) st r st' ∧ (↑r : CVar F).Scoped st' := by
  have hle := st.le_extendMany [bit (decide ((↑a : CVar F).val st.env.toValuation
    ≠ (↑b : CVar F).val st.env.toValuation))]
  refine ⟨.unchecked (.var st.nv), st.extendMany [bit (decide ((↑a : CVar F).val st.env.toValuation
    ≠ (↑b : CVar F).val st.env.toValuation))], ?_, ProverState.mem_extendMany_head ..⟩
  simp only [Runs, xorCore, prove_bind]
  rw [prove_witnessUB_run (w := xorWit a b) st (b := decide ((↑a : CVar F).val st.env.toValuation
      ≠ (↑b : CVar F).val st.env.toValuation))
    (.bind (.readCVar ha) fun _ => .bind (.readCVar hb) fun _ => trivial)
    (by simp [xorWit, Except.bind])]
  simp only [Except.bind, BoolVar.toCVar_unchecked]
  rw [prove_addConstraint _ (LawfulChecker.holds_r1cs ((ha.at hle).add_ (ha.at hle)) (hb.at hle)
    (((ha.at hle).add_ (hb.at hle)).sub_
      (show (CVar.var st.nv).Scoped _ from ProverState.mem_extendMany_head ..))
    (by simp only [CVar.val_add_, CVar.val_sub_, CVar.val, ProverState.get_extendMany_head,
          CVar.val_at hav hle ha, CVar.val_at hbv hle hb]
        simp only [hav, hbv]
        cases ab <;> cases bb <;> simp [bit]))]
  rfl

/-- `xor`'s honest run on bit operands accepts, returning a bit in scope. -/
theorem xor_complete [Field F] [DecidableEq F] [BasicSystem F c] [Checker F c]
    [LawfulChecker F c] {a b : BoolVar F} {ab bb : Bool} (st : ProverState F)
    (ha : (↑a : CVar F).Scoped st) (hb : (↑b : CVar F).Scoped st)
    (hav : (↑a : CVar F).val st.env.toValuation = bit ab)
    (hbv : (↑b : CVar F).val st.env.toValuation = bit bb) :
    ∃ r st', Runs (xor (c := c) a b) st r st' ∧ (↑r : CVar F).Scoped st' :=
  folded_complete (fun _ h => xorFold_scoped h ha hb) (xorCore_complete st ha hb hav hbv)

/-! ## `xnor`, composed

Two `xor` gates, the second against the constant bit. The reading is not restated: a
consumer takes it from `complete_of_sound xnor_spec`; and the composite's own completeness
takes the first gate's reading from `complete_of_sound xor_spec`. -/

/-- Exclusive nor: `a ⊕ b ⊕ 1`. -/
def xnor [Field F] [DecidableEq F] [BasicSystem F c] (a b : BoolVar F) :
    CircuitM F c (BoolVar F) := do
  let r ← xor a b
  xor r true_

/-- `xnor`: on bit operands the result reads as the negated xor bit. -/
@[spec] theorem xnor_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (a b : BoolVar F) :
    ⦃⌜True⌝⦄
    xnor (c := Builder V c) a b
    ⦃⇓ r _ => ⌜∀ ab bb : Bool,
        (↑a : CVar F).val V = bit ab → (↑b : CVar F).val V = bit bb →
          (↑r : CVar F).val V = bit (!(ab ^^ bb))⌝⦄ := by
  simp only [xnor]
  mvcgen
  rename_i h₁ _ _
  intro h₂ ab bb hav hbv
  rw [h₂ _ true (h₁ ab bb hav hbv) rfl, Bool.xor_true]

/-- `xnor`'s honest run on bit operands accepts, returning a bit in scope. -/
theorem xnor_complete [Field F] [DecidableEq F] [BasicSystem F c] [Checker F c]
    [LawfulChecker F c] [ConstraintHolds F c] [LawfulBasicSystem F c] [SoundChecker F c]
    {a b : BoolVar F} {ab bb : Bool} (st : ProverState F)
    (ha : (↑a : CVar F).Scoped st) (hb : (↑b : CVar F).Scoped st)
    (hav : (↑a : CVar F).val st.env.toValuation = bit ab)
    (hbv : (↑b : CVar F).val st.env.toValuation = bit bb) :
    ∃ r st', Runs (xnor (c := c) a b) st r st' ∧ (↑r : CVar F).Scoped st' :=
  let ⟨_, st₁, h₁, hs₁⟩ := xor_complete st ha hb hav hbv
  let ⟨r', st₂, h₂, hs₂⟩ := xor_complete (b := true_) (bb := true) st₁ hs₁ (CVar.scoped_const _ _)
    (complete_of_sound (fun V => xor_spec (c := c) (V := V) a b) h₁ ab bb
      (CVar.val_at hav h₁.le ha) (CVar.val_at hbv h₁.le hb)) rfl
  ⟨r', st₂, h₁.bind h₂, hs₂⟩

end Snarky.Pilot
