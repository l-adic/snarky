import Snarky.Circuit.DSL.Field
import Snarky.Backend.Prover

/-!
# The interpreter laws

The theorems the deep embedding exists to state — none of them is expressible against the
final-tagless PureScript original:

1. **Witness-independence** (`build_eraseWitness`): the constraint builder never
   inspects a witness payload — `build` factors through `eraseWitness`, the function
   stripping every `AsProver` computation from the tree. Two circuits differing only in
   their witness payloads have equal erasures, hence identical constraint systems
   (`build_eq_of_eraseWitness`). This is structural: continuations receive only fresh
   `Variable`s, never field values.
2. **Interpreter agreement** (`prove_build_agrees`): on a successful prover run, the
   builder and the prover compute the same result and allocate variables identically —
   the deep-embedding counterpart of PS's builder/prover running the *same* closure
   against two `CircuitOps` records.
3. **Completeness** (`prove_complete`): if the prover run succeeds, the final assignment
   satisfies *every* constraint the builder emits. The prover checks each constraint
   against the assignment current at emission time; the final assignment only extends it
   (`prove_assignments_le`), so a monotone `holds` stays true. Backends discharge the
   monotonicity hypothesis once via their `holds_mono` (`Snarky.Basic.holds_mono`;
   `Snarky.Kimchi.GateConstraint.holds_mono`).
4. **Gadget laws** (plan D12) — the `## The gadget laws` section: a gadget's law is
   stated against the interpreters, never re-derived over the field alone. Soundness
   quantifies over EVERY assignment satisfying the constraints `build` emits —
   adversarial witnesses included — and pins the result's evaluation to the gadget's
   semantics; completeness runs the honest prover from any fresh-enough assignment.
   Stated over the reference `Basic` backend (transport to other backends arrives with a
   lawful-`BasicSystem` consumer); each law reads off a definitional shape lemma for the
   built circuit, so a drifted gadget cannot keep its law. First instance:
   `equals_sound`/`equals_complete`. They live here, not beside their gadgets, because
   the gadget modules mirror the PS layering, below the backend (D3).

The interpreter laws (all but the corollary `build_eq_of_eraseWitness`), the gadget
laws, and `CVar.eval_le` are audited roots — `roots.txt` is the manifest,
`scripts/check_axioms.lean` the axiom gate (standard axioms only). Deliberately NOT
stated: the general converse of completeness — satisfiability of the built system
implying a successful honest-prover run — which would need totality hypotheses on the
witness computations (per-gadget completeness supplies exactly this, gadget by gadget);
and anything about the proof system itself (zero-knowledge, extraction), which lives
beyond the DSL layer.
-/

namespace Snarky

variable {F c : Type u}

/-! ## Witness-independence -/

/-- Strip every witness payload from the tree, leaving the circuit's shape: the
`AsProver` computations at `existsOp`/`assignOp` nodes are replaced by the trivially
failing one. Two circuits differ only in their witness code exactly when their erasures
are equal — for literal circuit terms that equality is `rfl`. -/
def eraseWitness : CircuitM F c α → CircuitM F c α
  | .pure a => .pure a
  | .freshOp k => .freshOp fun v => eraseWitness (k v)
  | .addConstraintOp con k => .addConstraintOp con (eraseWitness k)
  | .existsOp n _ k =>
    .existsOp n (fun _ => .error (.custom "erased")) fun vs => eraseWitness (k vs)
  | .assignOp vs _ k =>
    .assignOp vs (fun _ => .error (.custom "erased")) (eraseWitness k)
  | .labelOp s k => .labelOp s (eraseWitness k)

/-- **Witness-independence of the builder**: `build` factors through `eraseWitness` —
the constraint system (and the result, and the variable numbering) depends only on the
shape of the circuit, never on the witness computations stored at `existsOp`/`assignOp`
nodes. -/
theorem build_eraseWitness (m : CircuitM F c α) : ∀ n, build (eraseWitness m) n = build m n := by
  induction m with
  | pure a => intro n; rfl
  | freshOp k ih => intro n; simp only [eraseWitness, build]; exact ih n (n + 1)
  | addConstraintOp con k ih => intro n; simp only [eraseWitness, build, ih n]
  | existsOp k wit K ih => intro n; simp only [eraseWitness, build]; exact ih _ (n + k)
  | assignOp vs wit k ih => intro n; simp only [eraseWitness, build]; exact ih n
  | labelOp s k ih => intro n; simp only [eraseWitness, build]; exact ih n

/-- Circuits with equal erasures build identically — the two-circuit corollary. -/
theorem build_eq_of_eraseWitness {m m' : CircuitM F c α}
    (h : eraseWitness m = eraseWitness m') (n : Nat) : build m n = build m' n := by
  rw [← build_eraseWitness m, h, build_eraseWitness]

/-! ## Prover runs only extend the assignment -/

/-- A successful prover run never re-assigns a variable, so its final assignment extends
its initial one. -/
theorem prove_assignments_le {holds : c → Assignments F → Bool} {m : CircuitM F c α}
    {nv nv' : Nat} {env env' : Assignments F} {x : α}
    (h : prove holds m nv env = .ok ⟨x, nv', env'⟩) : env.Le env' := by
  induction m generalizing nv nv' env env' x with
  | pure a =>
    simp only [prove, Except.ok.injEq, Proved.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact Assignments.Le.refl _
  | freshOp k ih =>
    simp only [prove] at h
    exact ih _ h
  | addConstraintOp con k ih =>
    simp only [prove] at h
    split at h
    · exact ih h
    · cases h
  | existsOp n wit k ih =>
    simp only [prove] at h
    split at h
    · cases h
    · split at h
      · cases h
      · next hext => exact (Assignments.le_extendPairs hext).trans (ih _ h)
  | assignOp vs wit k ih =>
    simp only [prove] at h
    split at h
    · cases h
    · split at h
      · cases h
      · next hext => exact (Assignments.le_extendPairs hext).trans (ih h)
  | labelOp str k ih =>
    simp only [prove] at h
    exact ih h

/-! ## Interpreter agreement -/

/-- **Builder/prover agreement**: on a successful prover run the two interpreters compute
the same result and the same final variable counter — they allocate variables in lockstep
(the PS builder and prover run the same closure against two `CircuitOps` records; here
that is a theorem rather than an intention). -/
theorem prove_build_agrees {holds : c → Assignments F → Bool} {m : CircuitM F c α}
    {nv nv' : Nat} {env env' : Assignments F} {x : α}
    (h : prove holds m nv env = .ok ⟨x, nv', env'⟩) :
    (build m nv).result = x ∧ (build m nv).nextVar = nv' := by
  induction m generalizing nv nv' env env' x with
  | pure a =>
    simp only [prove, Except.ok.injEq, Proved.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨rfl, rfl⟩
  | freshOp k ih =>
    simp only [prove] at h
    simp only [build]
    exact ih _ h
  | addConstraintOp con k ih =>
    simp only [prove] at h
    simp only [build]
    split at h
    · exact ih h
    · cases h
  | existsOp n wit k ih =>
    simp only [prove] at h
    simp only [build]
    split at h
    · cases h
    · split at h
      · cases h
      · exact ih _ h
  | assignOp vs wit k ih =>
    simp only [prove] at h
    simp only [build]
    split at h
    · cases h
    · split at h
      · cases h
      · exact ih h
  | labelOp str k ih =>
    simp only [prove] at h
    simp only [build]
    exact ih h

/-! ## Completeness -/

/-- **Completeness**: if the prover run succeeds, the final assignment satisfies every
constraint the builder emits — provided `holds` is monotone in the assignment-extension
order (true of any constraint that evaluates its `CVar`s, by `CVar.eval_le`). The prover
checked each constraint when it was added; monotonicity carries the check to the end of
the run. -/
theorem prove_complete {holds : c → Assignments F → Bool}
    (hmono : ∀ (con : c) {a a' : Assignments F},
      a.Le a' → holds con a = true → holds con a' = true)
    {m : CircuitM F c α} {nv nv' : Nat} {env env' : Assignments F} {x : α}
    (h : prove holds m nv env = .ok ⟨x, nv', env'⟩) :
    ∀ con ∈ (build m nv).constraints, holds con env' = true := by
  induction m generalizing nv nv' env env' x with
  | pure a =>
    intro con hcon
    simp [build] at hcon
  | freshOp k ih =>
    simp only [prove] at h
    simp only [build]
    exact ih _ h
  | addConstraintOp con' k ih =>
    simp only [prove] at h
    split at h
    · next hh =>
      intro con hcon
      simp only [build, List.mem_cons] at hcon
      rcases hcon with rfl | hcon
      · exact hmono con (prove_assignments_le h) hh
      · exact ih h con hcon
    · cases h
  | existsOp n wit k ih =>
    simp only [prove] at h
    simp only [build]
    split at h
    · cases h
    · split at h
      · cases h
      · exact ih _ h
  | assignOp vs wit k ih =>
    simp only [prove] at h
    simp only [build]
    split at h
    · cases h
    · split at h
      · cases h
      · exact ih h
  | labelOp str k ih =>
    simp only [prove] at h
    simp only [build]
    exact ih h

/-! ## The gadget laws (D12)

Stated against `build`/`prove` over the reference `Basic` backend — see item 4 of the
module docstring. Each gadget's development: a definitional shape lemma for its built
circuit (the anti-drift anchor), private field-level engines, and the public
soundness/completeness pair. -/

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
    (hfresh : ∀ v, nv ≤ v → env v = none)
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
    (hfresh : ∀ v, nv ≤ v → env v = none) :
    ∃ out, prove Basic.holds (equalsCore (c := Basic F) z) nv env = .ok out ∧
      out.result.toCVar.eval out.assignments = .ok (if zv = 0 then 1 else 0) := by
  obtain ⟨hc₁, hc₂⟩ := equals_checks (F := F) zv
  have hwit : (equalsWit z env).map
      (CircuitType.valueToFields (F := F) (val := UnChecked Bool × F))
      = .ok ⟨#[if zv = 0 then 1 else 0, if zv = 0 then 0 else zv⁻¹], rfl⟩ := by
    by_cases hzv : zv = 0 <;>
      simp [equalsWit, AsProver.readCVar, hz, hzv, Bind.bind, ReaderT.bind, Except.bind,
        Pure.pure, ReaderT.pure, Except.pure, Except.map, CircuitType.valueToFields]
  refine ⟨_, equalsCore_run hz hfresh hwit hc₁ hc₂, ?_⟩
  show (CVar.var nv).eval _ = _
  simp [CVar.eval, Assignments.extend]

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
    (hfresh : ∀ v, nv ≤ v → env v = none)
    (ha : a.eval env = .ok av) (hb : b.eval env = .ok bv) :
    ∃ out, prove Basic.holds (equals (c := Basic F) a b) nv env = .ok out ∧
      out.result.toCVar.eval out.assignments = .ok (if av = bv then 1 else 0) := by
  have hz : (CVar.sub_ a b).eval env = .ok (av - bv) := CVar.eval_sub_ ha hb
  have hiff : ((av - bv = 0) : Prop) = (av = bv) := propext sub_eq_zero
  unfold equals
  cases hcase : CVar.sub_ a b with
  | const f =>
    rw [hcase] at hz
    have hf : f = av - bv := by simpa [CVar.eval] using hz
    subst hf
    refine ⟨_, rfl, ?_⟩
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

end Snarky
