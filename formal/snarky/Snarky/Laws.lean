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

Four of the five theorems here — all but the corollary `build_eq_of_eraseWitness` — plus
`CVar.eval_le` are the package's audited roots (`scripts/check_axioms.lean`: standard
axioms only). Deliberately NOT stated: the
converse of completeness — that satisfiability of the built system implies a successful
honest-prover run — which would need totality hypotheses on the witness computations;
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

end Snarky
