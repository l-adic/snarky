import Snarky.Circuit.DSL.Boolean
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
   built circuit, so a drifted gadget cannot keep its law; composite gadgets compose
   their children's laws through `build_bind`/`prove_bind` (`div` chains `inv` into
   `mul`; `pow` inducts over its fuel) rather than re-reducing their trees. The roster:
   `equals`, `mul`, `inv`, `square` directly, `div` and `pow` compositionally. They live
   here, not beside their gadgets, because the gadget modules mirror the PS layering,
   below the backend (D3).

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

/-! ### `mul` (Circuit/DSL/Monad) -/

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
  have hwit : (mulWit x y env).map (CircuitType.valueToFields (F := F) (val := F))
      = .ok ⟨#[xv * yv], rfl⟩ := by
    simp [mulWit, AsProver.readCVar, hx, hy, Bind.bind, ReaderT.bind, Except.bind,
      Pure.pure, ReaderT.pure, Except.pure, Except.map, CircuitType.valueToFields]
  have hext : env.extendPairs
      ((allocRange nv 1).toList.zip (⟨#[xv * yv], rfl⟩ : Vector F 1).toList)
      = .ok (env.extend nv (xv * yv)) := by
    show env.extendPairs [(nv, xv * yv)] = .ok _
    simp [Assignments.extendPairs, hnv]
  have hch : Basic.holds (.r1cs x y (.var nv)) (env.extend nv (xv * yv)) = true := by
    simp [Basic.holds, CVar.eval, CVar.eval_le hle hx, CVar.eval_le hle hy,
      Assignments.extend]
  show prove Basic.holds (.existsOp 1 (fun e => (mulWit x y e).map _) _) nv env = _
  simp only [prove, hwit, hext]
  show prove Basic.holds
    (.addConstraintOp (.r1cs x y (.var nv)) (.pure (CVar.var nv))) (nv + 1)
    (env.extend nv (xv * yv)) = _
  simp only [prove, hch, if_true]

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

/-! ### `inv` (Circuit/DSL/Monad) -/

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
  have hwit : (invWit x env).map (CircuitType.valueToFields (F := F) (val := F))
      = .ok ⟨#[xv⁻¹], rfl⟩ := by
    simp [invWit, AsProver.readCVar, hx, hxv, Bind.bind, ReaderT.bind, Except.bind,
      Pure.pure, ReaderT.pure, Except.pure, Except.map, CircuitType.valueToFields]
  have hext : env.extendPairs
      ((allocRange nv 1).toList.zip (⟨#[xv⁻¹], rfl⟩ : Vector F 1).toList)
      = .ok (env.extend nv xv⁻¹) := by
    show env.extendPairs [(nv, xv⁻¹)] = .ok _
    simp [Assignments.extendPairs, hnv]
  have hch : Basic.holds (.r1cs x (.var nv) (.const 1)) (env.extend nv xv⁻¹) = true := by
    simp [Basic.holds, CVar.eval, CVar.eval_le hle hx, Assignments.extend,
      mul_inv_cancel₀ hxv]
  show prove Basic.holds (.existsOp 1 (fun e => (invWit x e).map _) _) nv env = _
  simp only [prove, hwit, hext]
  show prove Basic.holds
    (.addConstraintOp (.r1cs x (.var nv) (.const 1)) (.pure (CVar.var nv))) (nv + 1)
    (env.extend nv xv⁻¹) = _
  simp only [prove, hch, if_true]

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
  have hwit : (squareWit x env).map (CircuitType.valueToFields (F := F) (val := F))
      = .ok ⟨#[xv * xv], rfl⟩ := by
    simp [squareWit, AsProver.readCVar, hx, Bind.bind, ReaderT.bind, Except.bind,
      Pure.pure, ReaderT.pure, Except.pure, Except.map, CircuitType.valueToFields]
  have hext : env.extendPairs
      ((allocRange nv 1).toList.zip (⟨#[xv * xv], rfl⟩ : Vector F 1).toList)
      = .ok (env.extend nv (xv * xv)) := by
    show env.extendPairs [(nv, xv * xv)] = .ok _
    simp [Assignments.extendPairs, hnv]
  have hch : Basic.holds (.square x (.var nv)) (env.extend nv (xv * xv)) = true := by
    simp [Basic.holds, CVar.eval, CVar.eval_le hle hx, Assignments.extend]
  show prove Basic.holds (.existsOp 1 (fun e => (squareWit x e).map _) _) nv env = _
  simp only [prove, hwit, hext]
  show prove Basic.holds
    (.addConstraintOp (.square x (.var nv)) (.pure (CVar.var nv))) (nv + 1)
    (env.extend nv (xv * xv)) = _
  simp only [prove, hch, if_true]

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

/-! ### `div` (Circuit/DSL/Monad) — the first composed law -/

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

/-! ### `neq` (Circuit/DSL/Field) — composed from `equals` -/

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
  refine ⟨⟨Snarky.not o₁.result, o₁.nextVar, o₁.assignments⟩, rfl, ?_, hf₁⟩
  show (CVar.sub_ (.const 1) _).eval _ = _
  rw [CVar.eval_sub_ rfl he₁]
  by_cases h : av = bv <;> simp [h]

/-! ### `and`/`or` (Circuit/DSL/Monad) — composed from `mul`, `not`

The boolean laws speak through `Snarky.bit`, the `CircuitType Bool` encoding — the
relation form the faithfulness arc composes over. -/

private theorem bit_mul {F : Type u} [MulZeroOneClass F] (a b : Bool) :
    (bit a : F) * bit b = bit (a && b) := by
  cases a <;> cases b <;> simp [bit]

/-- **`and` soundness** (D12): the conjunction bit. -/
theorem and_sound {F : Type u} [Add F] [CommMonoidWithZero F] [DecidableEq F]
    {a b : BoolVar F} {nv : Nat} {env : Assignments F} {ab bb : Bool}
    (hsat : ∀ con ∈ (build (Snarky.and (c := Basic F) a b) nv).constraints,
      con.holds env = true)
    (ha : (↑a : CVar F).eval env = .ok (bit ab))
    (hb : (↑b : CVar F).eval env = .ok (bit bb)) :
    (build (Snarky.and (c := Basic F) a b) nv).result.toCVar.eval env
      = .ok (bit (ab && bb)) := by
  unfold Snarky.and at hsat ⊢
  rw [build_bind] at hsat ⊢
  have h₁ := mul_sound (fun con h => hsat con (List.mem_append_left _ h)) ha hb
  rw [bit_mul] at h₁
  exact h₁

/-- **`and` completeness** (D12). -/
theorem and_complete {F : Type u} [Add F] [CommMonoidWithZero F] [DecidableEq F]
    {a b : BoolVar F} {nv : Nat} {env : Assignments F} {ab bb : Bool}
    (hfresh : env.FreshFrom nv)
    (ha : (↑a : CVar F).eval env = .ok (bit ab))
    (hb : (↑b : CVar F).eval env = .ok (bit bb)) :
    ∃ out, prove Basic.holds (Snarky.and (c := Basic F) a b) nv env = .ok out ∧
      out.result.toCVar.eval out.assignments = .ok (bit (ab && bb)) ∧
      out.assignments.FreshFrom out.nextVar := by
  unfold Snarky.and
  rw [prove_bind]
  obtain ⟨o₁, hr₁, he₁, hf₁⟩ := mul_complete hfresh ha hb
  rw [hr₁]
  refine ⟨⟨.unchecked o₁.result, o₁.nextVar, o₁.assignments⟩, rfl, ?_, hf₁⟩
  show o₁.result.eval o₁.assignments = _
  rw [he₁, bit_mul]

/-- **`or` soundness** (D12): the disjunction bit, by De Morgan through `and` and
`not_eval`. -/
theorem or_sound {F : Type u} [CommRing F] [NoZeroDivisors F] [DecidableEq F]
    {a b : BoolVar F} {nv : Nat} {env : Assignments F} {ab bb : Bool}
    (hsat : ∀ con ∈ (build (Snarky.or (c := Basic F) a b) nv).constraints,
      con.holds env = true)
    (ha : (↑a : CVar F).eval env = .ok (bit ab))
    (hb : (↑b : CVar F).eval env = .ok (bit bb)) :
    (build (Snarky.or (c := Basic F) a b) nv).result.toCVar.eval env
      = .ok (bit (ab || bb)) := by
  unfold Snarky.or at hsat ⊢
  rw [build_bind] at hsat ⊢
  have h₁ := and_sound (fun con h => hsat con (List.mem_append_left _ h))
    (not_eval ha) (not_eval hb)
  show (CVar.sub_ (.const 1) _).eval env = _
  rw [CVar.eval_sub_ rfl h₁]
  cases ab <;> cases bb <;> simp [bit]

/-- **`or` completeness** (D12). -/
theorem or_complete {F : Type u} [CommRing F] [NoZeroDivisors F] [DecidableEq F]
    {a b : BoolVar F} {nv : Nat} {env : Assignments F} {ab bb : Bool}
    (hfresh : env.FreshFrom nv)
    (ha : (↑a : CVar F).eval env = .ok (bit ab))
    (hb : (↑b : CVar F).eval env = .ok (bit bb)) :
    ∃ out, prove Basic.holds (Snarky.or (c := Basic F) a b) nv env = .ok out ∧
      out.result.toCVar.eval out.assignments = .ok (bit (ab || bb)) ∧
      out.assignments.FreshFrom out.nextVar := by
  unfold Snarky.or
  rw [prove_bind]
  obtain ⟨o₁, hr₁, he₁, hf₁⟩ := and_complete hfresh (not_eval ha) (not_eval hb)
  rw [hr₁]
  refine ⟨⟨Snarky.not o₁.result, o₁.nextVar, o₁.assignments⟩, rfl, ?_, hf₁⟩
  show (CVar.sub_ (.const 1) _).eval _ = _
  rw [CVar.eval_sub_ rfl he₁]
  cases ab <;> cases bb <;> simp [bit]

/-! ### `xor` (Circuit/DSL/Boolean)

The `any`/`all` combinators' three-plus cases are the OPEN OBLIGATION of walk step 10:
a sum of `n` bits detects `n` only below the field characteristic, so their laws need a
cast-injectivity hypothesis and the bit-counting lemma — deferred to the step that first
consumes them. -/

/-- Inversion for a satisfied `r1cs` row: all three operands evaluate and the product
identity holds. -/
private theorem r1cs_inv {F : Type u} [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]
    {l r o : CVar F} {env : Assignments F}
    (h : (Basic.r1cs l r o).holds env = true) :
    ∃ x y z, l.eval env = .ok x ∧ r.eval env = .ok y ∧ o.eval env = .ok z ∧ x * y = z := by
  have h' : (match l.eval env, r.eval env, o.eval env with
      | .ok x, .ok y, .ok z => decide (x * y = z)
      | _, _, _ => false) = true := h
  split at h'
  · next x y z hx hy hz => exact ⟨x, y, z, hx, hy, hz, by simpa using h'⟩
  · cases h'

/-- The field engine of `xor` soundness: the constraint `2a · b = a + b − r` pins `r` to
the xor bit. -/
private theorem xor_pin {F : Type u} [CommRing F] {ab bb : Bool} {rv : F}
    (h : ((bit ab : F) + bit ab) * bit bb = bit ab + bit bb - rv) :
    rv = bit (ab ^^ bb) := by
  have h' : rv = (bit ab : F) + bit bb - (bit ab + bit ab) * bit bb := by
    rw [eq_sub_iff_add_eq] at h ⊢
    rw [← h]
    ring
  rw [h']
  cases ab <;> cases bb <;> simp [bit]

/-- What `xorCore` builds: one fresh variable at `UnChecked Bool`, one `r1cs` row
`2a · b = a + b − r`. -/
private theorem build_xorCore {F : Type} [Field F] [DecidableEq F] (a b : BoolVar F)
    (nv : Nat) :
    build (xorCore (c := Basic F) a b) nv =
      ⟨.unchecked (.var nv), nv + 1,
        [.r1cs (CVar.add_ a.toCVar a.toCVar) b.toCVar
          (CVar.sub_ (CVar.add_ a.toCVar b.toCVar) (.var nv))]⟩ := rfl

/-- `xorCore` soundness: any satisfying assignment pins the xor bit. -/
private theorem xorCore_sound {F : Type} [Field F] [DecidableEq F] {a b : BoolVar F}
    {nv : Nat} {env : Assignments F} {ab bb : Bool}
    (ha : (↑a : CVar F).eval env = .ok (bit ab))
    (hb : (↑b : CVar F).eval env = .ok (bit bb))
    (hsat : ∀ con ∈ (build (xorCore (c := Basic F) a b) nv).constraints,
      con.holds env = true) :
    (build (xorCore (c := Basic F) a b) nv).result.toCVar.eval env
      = .ok (bit (ab ^^ bb)) := by
  rw [build_xorCore] at hsat ⊢
  obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := r1cs_inv (hsat _ (List.mem_cons_self ..))
  have haa : (CVar.add_ (a.toCVar) (a.toCVar)).eval env = .ok (bit ab + bit ab) := by
    rw [CVar.eval_add_]; simp [CVar.eval, ha]
  have hab : (CVar.add_ (a.toCVar) (b.toCVar)).eval env = .ok (bit ab + bit bb) := by
    rw [CVar.eval_add_]; simp [CVar.eval, ha, hb]
  rw [haa, Except.ok.injEq] at hx
  rw [hb, Except.ok.injEq] at hy
  obtain ⟨s₁, s₂, hs₁, hs₂, rfl⟩ := CVar.eval_sub_inv hz
  rw [hab, Except.ok.injEq] at hs₁
  subst hx; subst hy; subst hs₁
  show (CVar.var nv).eval env = _
  rw [hs₂, xor_pin hxyz]

/-- The honest `xorCore` run. -/
private theorem xorCore_run {F : Type} [Field F] [DecidableEq F] {a b : BoolVar F}
    {nv : Nat} {env : Assignments F} {ab bb : Bool}
    (ha : (↑a : CVar F).eval env = .ok (bit ab))
    (hb : (↑b : CVar F).eval env = .ok (bit bb))
    (hfresh : env.FreshFrom nv) :
    prove Basic.holds (xorCore (c := Basic F) a b) nv env
      = .ok ⟨.unchecked (.var nv), nv + 1, env.extend nv (bit (ab ^^ bb))⟩ := by
  have hnv : env nv = none := hfresh nv (Nat.le_refl nv)
  have hle : env.Le (env.extend nv (bit (ab ^^ bb))) := by
    intro v w hv
    simp only [Assignments.extend]
    split
    · next h => rw [h, hnv] at hv; cases hv
    · exact hv
  have hwit : (xorWit a b env).map
      (CircuitType.valueToFields (F := F) (val := UnChecked Bool))
      = .ok ⟨#[bit (ab ^^ bb)], rfl⟩ := by
    cases hab : ab <;> cases hbb : bb <;>
      simp [xorWit, AsProver.readCVar, ha, hb, hab, hbb, Bind.bind, ReaderT.bind,
        Except.bind, Pure.pure, ReaderT.pure, Except.pure, Except.map,
        CircuitType.valueToFields, bit, one_ne_zero]
  have hext : env.extendPairs
      ((allocRange nv 1).toList.zip
        (⟨#[bit (ab ^^ bb)], rfl⟩ : Vector F 1).toList)
      = .ok (env.extend nv (bit (ab ^^ bb))) := by
    show env.extendPairs [(nv, bit (ab ^^ bb))] = .ok _
    simp [Assignments.extendPairs, hnv]
  have hch : Basic.holds
      (.r1cs (CVar.add_ a.toCVar a.toCVar) b.toCVar
        (CVar.sub_ (CVar.add_ a.toCVar b.toCVar) (.var nv)))
      (env.extend nv (bit (ab ^^ bb))) = true := by
    have ha' := CVar.eval_le hle ha
    have hb' := CVar.eval_le hle hb
    have haa : (CVar.add_ (a.toCVar) (a.toCVar)).eval (env.extend nv (bit (ab ^^ bb)))
        = .ok ((bit ab : F) + bit ab) := by
      rw [CVar.eval_add_]; simp [CVar.eval, ha']
    have hvnv : (CVar.var nv).eval (env.extend nv (bit (ab ^^ bb)))
        = .ok (bit (ab ^^ bb)) := by simp [CVar.eval, Assignments.extend]
    have hab : (CVar.add_ (a.toCVar) (b.toCVar)).eval (env.extend nv (bit (ab ^^ bb)))
        = .ok ((bit ab : F) + bit bb) := by
      rw [CVar.eval_add_]; simp [CVar.eval, ha', hb']
    have hsub := CVar.eval_sub_ hab hvnv
    simp only [Basic.holds, haa, hb', hsub, decide_eq_true_eq]
    cases ab <;> cases bb <;> simp [bit]
  show prove Basic.holds (.existsOp 1 (fun e => (xorWit a b e).map _) _) nv env = _
  simp only [prove, hwit, hext]
  show prove Basic.holds
    (.addConstraintOp (.r1cs (CVar.add_ a.toCVar a.toCVar) b.toCVar
        (CVar.sub_ (CVar.add_ a.toCVar b.toCVar) (.var nv)))
      (.pure (BoolVar.unchecked (.var nv)))) (nv + 1)
    (env.extend nv (bit (ab ^^ bb))) = _
  simp only [prove, hch, if_true]

/-- A constant that encodes a bit is `0` or `1` — the discharging fact for `xor`'s
guard-chain fall-through branches. -/
private theorem bit_cases {F : Type u} [Zero F] [One F] {av : F} {ab : Bool}
    (h : av = bit ab) : av = 0 ∨ av = 1 := by
  cases ab <;> simp [bit] at h <;> [exact Or.inl h; exact Or.inr h]

/-- The `a`-constant guard chain of `xor`, over syntactic `if`s. -/
private theorem xor_sound_constA {F : Type} [Field F] [DecidableEq F] {a b : BoolVar F}
    {nv : Nat} {env : Assignments F} {ab bb : Bool} {av : F}
    (hA : (↑a : CVar F) = .const av)
    (ha : (↑a : CVar F).eval env = .ok (bit ab))
    (hb : (↑b : CVar F).eval env = .ok (bit bb)) :
    (build (if av = 0 then pure b else if av = 1 then pure (Snarky.not b)
        else xorCore (c := Basic F) a b) nv).result.toCVar.eval env
      = .ok (bit (ab ^^ bb)) := by
  have hav : av = bit ab := by rw [hA] at ha; simpa [CVar.eval] using ha
  split_ifs with h0 h1
  · have : ab = false := by
      cases ab
      · rfl
      · exact absurd (hav.symm.trans h0) (by simp [bit])
    subst this
    simpa using hb
  · have : ab = true := by
      cases ab
      · exact absurd (hav ▸ h1) (by simp [bit])
      · rfl
    subst this
    show (CVar.sub_ (.const 1) _).eval env = _
    rw [CVar.eval_sub_ rfl hb]
    cases bb <;> simp [bit]
  · rcases bit_cases hav with h | h
    · exact absurd h h0
    · exact absurd h h1

/-- The `b`-constant guard chain of `xor`, over syntactic `if`s. -/
private theorem xor_sound_constB {F : Type} [Field F] [DecidableEq F] {a b : BoolVar F}
    {nv : Nat} {env : Assignments F} {ab bb : Bool} {bv : F}
    (hB : (↑b : CVar F) = .const bv)
    (ha : (↑a : CVar F).eval env = .ok (bit ab))
    (hb : (↑b : CVar F).eval env = .ok (bit bb)) :
    (build (if bv = 0 then pure a else if bv = 1 then pure (Snarky.not a)
        else xorCore (c := Basic F) a b) nv).result.toCVar.eval env
      = .ok (bit (ab ^^ bb)) := by
  have hbv : bv = bit bb := by rw [hB] at hb; simpa [CVar.eval] using hb
  split_ifs with h0 h1
  · have : bb = false := by
      cases bb
      · rfl
      · exact absurd (hbv.symm.trans h0) (by simp [bit])
    subst this
    simpa using ha
  · have : bb = true := by
      cases bb
      · exact absurd (hbv ▸ h1) (by simp [bit])
      · rfl
    subst this
    show (CVar.sub_ (.const 1) _).eval env = _
    rw [CVar.eval_sub_ rfl ha]
    cases ab <;> simp [bit]
  · rcases bit_cases hbv with h | h
    · exact absurd h h0
    · exact absurd h h1

/-- **`xor` soundness** (D12): any satisfying assignment pins the result to the xor bit,
through every branch of the PS guard chain. -/
theorem xor_sound {F : Type} [Field F] [DecidableEq F] {a b : BoolVar F} {nv : Nat}
    {env : Assignments F} {ab bb : Bool}
    (hsat : ∀ con ∈ (build (Snarky.xor (c := Basic F) a b) nv).constraints,
      con.holds env = true)
    (ha : (↑a : CVar F).eval env = .ok (bit ab))
    (hb : (↑b : CVar F).eval env = .ok (bit bb)) :
    (build (Snarky.xor (c := Basic F) a b) nv).result.toCVar.eval env
      = .ok (bit (ab ^^ bb)) := by
  unfold Snarky.xor at hsat ⊢
  cases hA : (↑a : CVar F) <;> cases hB : (↑b : CVar F) <;> rw [hA, hB] at hsat
  case const.const av bv =>
    have hav : av = bit ab := by rw [hA] at ha; simpa [CVar.eval] using ha
    have hbv : bv = bit bb := by rw [hB] at hb; simpa [CVar.eval] using hb
    subst hav; subst hbv
    show Except.ok _ = _
    cases ab <;> cases bb <;> simp [bit]
  case const.var av v => exact xor_sound_constA hA ha hb
  case const.add av x y => exact xor_sound_constA hA ha hb
  case const.scale av k x => exact xor_sound_constA hA ha hb
  case var.const v bv => exact xor_sound_constB hB ha hb
  case add.const x y bv => exact xor_sound_constB hB ha hb
  case scale.const k x bv => exact xor_sound_constB hB ha hb
  all_goals exact xorCore_sound ha hb hsat

/-- The `a`-constant guard chain of `xor`, completeness side. -/
private theorem xor_complete_constA {F : Type} [Field F] [DecidableEq F]
    {a b : BoolVar F} {nv : Nat} {env : Assignments F} {ab bb : Bool} {av : F}
    (hA : (↑a : CVar F) = .const av)
    (ha : (↑a : CVar F).eval env = .ok (bit ab))
    (hb : (↑b : CVar F).eval env = .ok (bit bb))
    (hfresh : env.FreshFrom nv) :
    ∃ out, prove Basic.holds (if av = 0 then pure b else if av = 1 then pure (Snarky.not b)
        else xorCore (c := Basic F) a b) nv env = .ok out ∧
      out.result.toCVar.eval out.assignments = .ok (bit (ab ^^ bb)) ∧
      out.assignments.FreshFrom out.nextVar := by
  have hav : av = bit ab := by rw [hA] at ha; simpa [CVar.eval] using ha
  split_ifs with h0 h1
  · have : ab = false := by
      cases ab
      · rfl
      · exact absurd (hav.symm.trans h0) (by simp [bit])
    subst this
    exact ⟨_, rfl, by simpa using hb, hfresh⟩
  · have : ab = true := by
      cases ab
      · exact absurd (hav ▸ h1) (by simp [bit])
      · rfl
    subst this
    refine ⟨_, rfl, ?_, hfresh⟩
    show (CVar.sub_ (.const 1) _).eval env = _
    rw [CVar.eval_sub_ rfl hb]
    cases bb <;> simp [bit]
  · rcases bit_cases hav with h | h
    · exact absurd h h0
    · exact absurd h h1

/-- The `b`-constant guard chain of `xor`, completeness side. -/
private theorem xor_complete_constB {F : Type} [Field F] [DecidableEq F]
    {a b : BoolVar F} {nv : Nat} {env : Assignments F} {ab bb : Bool} {bv : F}
    (hB : (↑b : CVar F) = .const bv)
    (ha : (↑a : CVar F).eval env = .ok (bit ab))
    (hb : (↑b : CVar F).eval env = .ok (bit bb))
    (hfresh : env.FreshFrom nv) :
    ∃ out, prove Basic.holds (if bv = 0 then pure a else if bv = 1 then pure (Snarky.not a)
        else xorCore (c := Basic F) a b) nv env = .ok out ∧
      out.result.toCVar.eval out.assignments = .ok (bit (ab ^^ bb)) ∧
      out.assignments.FreshFrom out.nextVar := by
  have hbv : bv = bit bb := by rw [hB] at hb; simpa [CVar.eval] using hb
  split_ifs with h0 h1
  · have : bb = false := by
      cases bb
      · rfl
      · exact absurd (hbv.symm.trans h0) (by simp [bit])
    subst this
    exact ⟨_, rfl, by simpa using ha, hfresh⟩
  · have : bb = true := by
      cases bb
      · exact absurd (hbv ▸ h1) (by simp [bit])
      · rfl
    subst this
    refine ⟨_, rfl, ?_, hfresh⟩
    show (CVar.sub_ (.const 1) _).eval env = _
    rw [CVar.eval_sub_ rfl ha]
    cases ab <;> simp [bit]
  · rcases bit_cases hbv with h | h
    · exact absurd h h0
    · exact absurd h h1

/-- **`xor` completeness** (D12): the honest prover run succeeds through every branch of
the guard chain and answers the xor bit. -/
theorem xor_complete {F : Type} [Field F] [DecidableEq F] {a b : BoolVar F} {nv : Nat}
    {env : Assignments F} {ab bb : Bool}
    (hfresh : env.FreshFrom nv)
    (ha : (↑a : CVar F).eval env = .ok (bit ab))
    (hb : (↑b : CVar F).eval env = .ok (bit bb)) :
    ∃ out, prove Basic.holds (Snarky.xor (c := Basic F) a b) nv env = .ok out ∧
      out.result.toCVar.eval out.assignments = .ok (bit (ab ^^ bb)) ∧
      out.assignments.FreshFrom out.nextVar := by
  unfold Snarky.xor
  cases hA : (↑a : CVar F) <;> cases hB : (↑b : CVar F)
  case const.const av bv =>
    have hav : av = bit ab := by rw [hA] at ha; simpa [CVar.eval] using ha
    have hbv : bv = bit bb := by rw [hB] at hb; simpa [CVar.eval] using hb
    subst hav; subst hbv
    refine ⟨_, rfl, ?_, hfresh⟩
    show Except.ok _ = _
    cases ab <;> cases bb <;> simp [bit]
  case const.var av v => exact xor_complete_constA hA ha hb hfresh
  case const.add av x y => exact xor_complete_constA hA ha hb hfresh
  case const.scale av k x => exact xor_complete_constA hA ha hb hfresh
  case var.const v bv => exact xor_complete_constB hB ha hb hfresh
  case add.const x y bv => exact xor_complete_constB hB ha hb hfresh
  case scale.const k x bv => exact xor_complete_constB hB ha hb hfresh
  all_goals
    refine ⟨_, xorCore_run ha hb hfresh, ?_, ?_⟩
    · show (CVar.var nv).eval _ = _
      simp [CVar.eval, Assignments.extend]
    · intro v hv
      replace hv : nv + 1 ≤ v := hv
      have h0 : v ≠ nv := by omega
      show (env.extend nv _) v = none
      simp [Assignments.extend, h0, hfresh v (by omega)]

/-! ### `select` (Circuit/DSL/Boolean, the `IfThenElse` field instance) -/

/-- What `selectCore` builds: one fresh variable, the mux constraint
`b · (t − e) = r − e`. -/
private theorem build_selectCore {F : Type} [Field F] [DecidableEq F]
    (b : BoolVar F) (t e : FVar F) (nv : Nat) :
    build (selectCore (c := Basic F) b t e) nv =
      ⟨.var nv, nv + 1,
        [.r1cs b.toCVar (CVar.sub_ t e) (CVar.sub_ (.var nv) e)]⟩ := rfl

/-- `selectCore` soundness: the constraint pins the mux value. -/
private theorem selectCore_sound {F : Type} [Field F] [DecidableEq F]
    {b : BoolVar F} {t e : FVar F} {nv : Nat} {env : Assignments F} {bb : Bool}
    {tv ev : F}
    (hb : (↑b : CVar F).eval env = .ok (bit bb))
    (ht : t.eval env = .ok tv) (he : e.eval env = .ok ev)
    (hsat : ∀ con ∈ (build (selectCore (c := Basic F) b t e) nv).constraints,
      con.holds env = true) :
    (build (selectCore (c := Basic F) b t e) nv).result.eval env
      = .ok (if bb then tv else ev) := by
  rw [build_selectCore] at hsat ⊢
  obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := r1cs_inv (hsat _ (List.mem_cons_self ..))
  rw [hb, Except.ok.injEq] at hx
  rw [CVar.eval_sub_ ht he, Except.ok.injEq] at hy
  obtain ⟨s₁, s₂, hs₁, hs₂, rfl⟩ := CVar.eval_sub_inv hz
  rw [he, Except.ok.injEq] at hs₂
  subst hx; subst hy; subst hs₂
  show (CVar.var nv).eval env = _
  rw [hs₁]
  congr 1
  rw [eq_sub_iff_add_eq] at hxyz
  rw [← hxyz]
  cases bb <;> simp [bit]

/-- The honest `selectCore` run. -/
private theorem selectCore_run {F : Type} [Field F] [DecidableEq F]
    {b : BoolVar F} {t e : FVar F} {nv : Nat} {env : Assignments F} {bb : Bool}
    {tv ev : F}
    (hb : (↑b : CVar F).eval env = .ok (bit bb))
    (ht : t.eval env = .ok tv) (he : e.eval env = .ok ev)
    (hfresh : env.FreshFrom nv) :
    prove Basic.holds (selectCore (c := Basic F) b t e) nv env
      = .ok ⟨.var nv, nv + 1, env.extend nv (if bb then tv else ev)⟩ := by
  have hnv : env nv = none := hfresh nv (Nat.le_refl nv)
  have hle : env.Le (env.extend nv (if bb then tv else ev)) := by
    intro v w hv
    simp only [Assignments.extend]
    split
    · next h => rw [h, hnv] at hv; cases hv
    · exact hv
  have hwit : (selectWit b t e env).map (CircuitType.valueToFields (F := F) (val := F))
      = .ok ⟨#[if bb then tv else ev], rfl⟩ := by
    cases bb <;>
      simp [selectWit, AsProver.readCVar, hb, ht, he, Bind.bind, ReaderT.bind,
        Except.bind, Except.map, CircuitType.valueToFields, bit]
  have hext : env.extendPairs
      ((allocRange nv 1).toList.zip
        (⟨#[if bb then tv else ev], rfl⟩ : Vector F 1).toList)
      = .ok (env.extend nv (if bb then tv else ev)) := by
    show env.extendPairs [(nv, if bb then tv else ev)] = .ok _
    simp [Assignments.extendPairs, hnv]
  have hch : Basic.holds
      (.r1cs b.toCVar (CVar.sub_ t e) (CVar.sub_ (.var nv) e))
      (env.extend nv (if bb then tv else ev)) = true := by
    have hb' := CVar.eval_le hle hb
    have ht' := CVar.eval_le hle ht
    have he' := CVar.eval_le hle he
    have hvnv : (CVar.var nv).eval (env.extend nv (if bb then tv else ev))
        = .ok (if bb then tv else ev) := by simp [CVar.eval, Assignments.extend]
    have hsub₁ := CVar.eval_sub_ ht' he'
    have hsub₂ := CVar.eval_sub_ hvnv he'
    simp only [Basic.holds, hb', hsub₁, hsub₂, decide_eq_true_eq]
    cases bb <;> simp [bit]
  show prove Basic.holds (.existsOp 1 (fun x => (selectWit b t e x).map _) _) nv env = _
  simp only [prove, hwit, hext]
  show prove Basic.holds
    (.addConstraintOp (.r1cs b.toCVar (CVar.sub_ t e) (CVar.sub_ (.var nv) e))
      (.pure (CVar.var nv))) (nv + 1)
    (env.extend nv (if bb then tv else ev)) = _
  simp only [prove, hch, if_true]

/-- The evaluation of the constant-branches affine mux, over an arbitrary selector
expression. -/
private theorem select_mux_eval {F : Type} [Field F] [DecidableEq F] {bc : CVar F}
    {bb : Bool} {env : Assignments F} {tv' ev' tv ev : F}
    (hb : bc.eval env = .ok (bit bb))
    (ht : (CVar.const tv').eval env = .ok tv) (he : (CVar.const ev').eval env = .ok ev) :
    (CVar.add_ (.scale tv' bc)
      (CVar.scale_ ev' (CVar.sub_ (.const 1) bc))).eval env
      = .ok (if bb then tv else ev) := by
  have htv : tv' = tv := by simpa [CVar.eval] using ht
  have hev : ev' = ev := by simpa [CVar.eval] using he
  rw [← htv, ← hev]
  rw [CVar.eval_add_]
  have h₁ : (CVar.scale tv' bc).eval env = .ok (tv' * bit bb) := by
    simp [CVar.eval, hb]
  have h₂ := CVar.eval_scale_
    (CVar.eval_sub_ (rfl : (CVar.const (1 : F)).eval env = .ok 1) hb) ev'
  set X := CVar.scale tv' bc with hX
  set Y := CVar.scale_ ev' (CVar.sub_ (.const 1) bc) with hY
  simp only [CVar.eval, h₁, h₂]
  cases bb <;> simp [bit]

/-- **`select` soundness** (D12, the `IfThenElse` field instance): any satisfying
assignment pins the result to the selected branch, through the constant-selector fold,
the constant-branches affine mux, and the witnessing branch. -/
theorem select_sound {F : Type} [Field F] [DecidableEq F] {b : BoolVar F} {t e : FVar F}
    {nv : Nat} {env : Assignments F} {bb : Bool} {tv ev : F}
    (hsat : ∀ con ∈ (build (select (c := Basic F) b t e) nv).constraints,
      con.holds env = true)
    (hb : (↑b : CVar F).eval env = .ok (bit bb))
    (ht : t.eval env = .ok tv) (he : e.eval env = .ok ev) :
    (build (select (c := Basic F) b t e) nv).result.eval env
      = .ok (if bb then tv else ev) := by
  show (build (match (↑b : CVar F) with
    | .const bv => pure (if bv = 1 then t else e)
    | _ => match t, e with
      | .const tv', .const ev' =>
        pure (CVar.add_ (.scale tv' ↑b) (CVar.scale_ ev' (CVar.sub_ (.const 1) ↑b)))
      | t, e => selectCore b t e) nv).result.eval env = _
  replace hsat : ∀ con ∈ (build (match (↑b : CVar F) with
    | .const bv => pure (if bv = 1 then t else e)
    | _ => match t, e with
      | .const tv', .const ev' =>
        pure (CVar.add_ (.scale tv' ↑b) (CVar.scale_ ev' (CVar.sub_ (.const 1) ↑b)))
      | t, e => selectCore b t e) nv).constraints, Basic.holds con env = true := hsat
  cases hB : (↑b : CVar F) <;> rw [hB] at hsat
  case const bv =>
    have hbv : bv = bit bb := by rw [hB] at hb; simpa [CVar.eval] using hb
    subst hbv
    show (build (pure (if (bit bb : F) = 1 then t else e) :
      CircuitM F (Basic F) (FVar F)) nv).result.eval env = _
    cases bb <;> simp [bit] <;> [exact he; exact ht]
  all_goals cases t <;> cases e <;>
    first
      | exact select_mux_eval (hB ▸ hb) ht he
      | exact selectCore_sound hb ht he hsat

/-- **`select` completeness** (D12): the honest prover run succeeds through every branch
and computes the selected value. -/
theorem select_complete {F : Type} [Field F] [DecidableEq F] {b : BoolVar F}
    {t e : FVar F} {nv : Nat} {env : Assignments F} {bb : Bool} {tv ev : F}
    (hfresh : env.FreshFrom nv)
    (hb : (↑b : CVar F).eval env = .ok (bit bb))
    (ht : t.eval env = .ok tv) (he : e.eval env = .ok ev) :
    ∃ out, prove Basic.holds (select (c := Basic F) b t e) nv env = .ok out ∧
      out.result.eval out.assignments = .ok (if bb then tv else ev) ∧
      out.assignments.FreshFrom out.nextVar := by
  show ∃ out, prove Basic.holds (match (↑b : CVar F) with
    | .const bv => pure (if bv = 1 then t else e)
    | _ => match t, e with
      | .const tv', .const ev' =>
        pure (CVar.add_ (.scale tv' ↑b) (CVar.scale_ ev' (CVar.sub_ (.const 1) ↑b)))
      | t, e => selectCore b t e) nv env = .ok out ∧ _ ∧ _
  cases hB : (↑b : CVar F)
  case const bv =>
    have hbv : bv = bit bb := by rw [hB] at hb; simpa [CVar.eval] using hb
    subst hbv
    refine ⟨_, rfl, ?_, hfresh⟩
    show (if (bit bb : F) = 1 then t else e).eval env = _
    cases bb <;> simp [bit] <;> [exact he; exact ht]
  all_goals cases t <;> cases e <;>
    first
      | exact ⟨⟨_, nv, env⟩, rfl, select_mux_eval (hB ▸ hb) ht he, hfresh⟩
      | (refine ⟨_, selectCore_run hb ht he hfresh, ?_, ?_⟩
         · show (CVar.var nv).eval _ = _
           simp [CVar.eval, Assignments.extend]
         · intro v hv
           replace hv : nv + 1 ≤ v := hv
           have h0 : v ≠ nv := by omega
           show (env.extend nv _) v = none
           simp [Assignments.extend, h0, hfresh v (by omega)])

end Snarky
