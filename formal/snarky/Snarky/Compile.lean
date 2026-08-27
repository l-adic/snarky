import Snarky.DSL.Assert

/-!
# Compiling and solving whole circuits

A circuit `main : avar → CircuitM F c bvar` becomes a constraint system (`compile`) and a
witness solver (`solve`). The public interface is the input bundle at slots `0 …`,
seeded before the run, and an output bundle witnessed after the body and constrained
equal to what the body returned; `compile`'s result carries both bundles, so the public
slots are read off the encoding rather than spelled.

The outputs are witnessed rather than preallocated because the prover's table has no
holes — it is defined exactly below its counter, which is what makes a scoped reading
stable under later allocation. A slot allocated before the body and filled after it would
be such a hole.

`solve_complete` is the payoff: a circuit whose body is complete solves, and the table it
produces satisfies every compiled row and reads the input and the output at the public
bundles.
-/

namespace Snarky

variable {F c a b avar bvar : Type}

/-- The public input bundle: the encoding's slots, from `0`. -/
def inputVar [A : CircuitType F a avar] : avar :=
  A.fieldsToVar (mapVec CVar.var (allocRange 0 A.size))

/-- The whole-circuit program: bind the input bundle, pay its check, run the body,
witness the output's encoding into fresh public slots, and constrain the body's output to
them. The result is the body's output paired with the public bundle. -/
def compileBody [Field F] [DecidableEq F] [BasicSystem F c] [CircuitType F a avar]
    [CheckedType F c a avar] [CircuitType F b bvar] (main : avar → CircuitM F c bvar) :
    CircuitM F c (bvar × bvar) := do
  let av : avar := inputVar (F := F) (a := a)
  CheckedType.check (c := c) (val := a) av
  let out ← main av
  let pub ← witness (val := UnChecked b) (do
    let x ← readVar (val := b) out
    pure (UnChecked.mk x))
  assertEq (val := b) out pub.val
  pure (out, pub.val)

/-- A circuit's constraint system: the builder on the whole-circuit program, with the
counter past the input slots. -/
def compile [Field F] [DecidableEq F] [BasicSystem F c] [A : CircuitType F a avar]
    [CheckedType F c a avar] [CircuitType F b bvar] (main : avar → CircuitM F c bvar) :
    Built c (bvar × bvar) :=
  build (compileBody (a := a) (b := b) main) A.size

/-- The state a solve starts from: the input's encoding at the input slots. -/
def seed [A : CircuitType F a avar] (input : a) : ProverState F :=
  ⟨A.size, Assignments.empty.extendList 0 (A.valueToFields input).toList, by
    simpa using Assignments.empty_dom.extendList (A.valueToFields input).toList⟩

/-- Solve a circuit on a public input: run the prover on the whole-circuit program from
the seeded table and read the output bundle back. -/
def solve [Field F] [DecidableEq F] [BasicSystem F c] [CircuitType F a avar]
    [CheckedType F c a avar] [CircuitType F b bvar] (main : avar → CircuitM F c bvar)
    (input : a) : Except EvalError (b × Assignments F) :=
  match prove (compileBody (a := a) (b := b) main) (seed (F := F) (avar := avar) input).nv
      (seed (F := F) (avar := avar) input).env with
  | .error e => .error e
  | .ok p =>
    match (readVar (val := b) p.result.1).run p.assignments with
    | .error e => .error e
    | .ok outVal => .ok (outVal, p.assignments)

/-! ## The public input, at the seeded state -/

/-- The input bundle is in scope from the start: its slots are the first `A.size`. -/
theorem scoped_inputVar [Add F] [Mul F] [Zero F] [A : CircuitType F a avar] (input : a) :
    CircuitType.Scoped (val := a) (seed (F := F) (avar := avar) input)
      (inputVar (F := F) (a := a)) := by
  intro cv hcv
  rw [inputVar, A.var_roundTrip, toList_mapVec, List.mem_map] at hcv
  obtain ⟨v, hv, rfl⟩ := hcv
  exact show v < A.size by simpa [allocRange] using hv

/-- The seeded table reads the input at the input bundle. -/
theorem reads_inputVar [Add F] [Mul F] [Zero F] [A : CircuitType F a avar] (input : a) :
    CircuitType.Reads (seed (F := F) (avar := avar) input).env.get
      (inputVar (F := F) (a := a)) input := by
  unfold CircuitType.Reads inputVar
  rw [A.var_roundTrip]
  ext i hi
  simp only [getElem_mapVec, getElem_allocRange, CVar.val]
  show (Assignments.empty.extendList 0 (A.valueToFields input).toList).get (0 + i) = _
  rw [Assignments.get, Assignments.extendList_get (by simpa using hi)]
  simp

/-! ## The seam -/

open CircuitType in
/-- A circuit whose body is complete solves at an admissible public input: the run
succeeds, the table it produces satisfies every compiled row, and the compiled system's
two bundles — the body's output and the public one — both read as the value the solve
returned. Admissibility (`CheckedType.Valid`) is the input type's own rows read at the
value, so the statement covers exactly the inputs the compiled system accepts and
assumes nothing else about the prover. -/
theorem solve_complete [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] [A : CircuitType F a avar] [CheckedType F c a avar]
    [B : CircuitType F b bvar] {main : avar → CircuitM F c bvar} (input : a)
    (hinput : CheckedType.Valid (F := F) (c := c) (var := avar) input)
    (hmain : Complete (F := F) (c := c)
      (fun st => Scoped (val := a) st (inputVar (F := F) (a := a)) ∧
        Reads st.env.get (inputVar (F := F) (a := a)) input)
      (main (inputVar (F := F) (a := a)))
      (fun out st' => Scoped (val := b) st' out ∧ WellFormed (val := b) st'.env.get out)) :
    ∃ (outVal : b) (env : Assignments F),
      solve (a := a) (b := b) main input = .ok (outVal, env) ∧
      (∀ con ∈ (compile (a := a) (b := b) main).constraints,
        ConstraintHolds.Holds env.get con) ∧
      Reads env.get (compile (a := a) (b := b) main).result.1 outVal ∧
      Reads env.get (compile (a := a) (b := b) main).result.2 outVal := by
  have hav := scoped_inputVar (F := F) (avar := avar) input
  have hrv := reads_inputVar (F := F) (avar := avar) input
  -- the input bundle's check, which may allocate auxiliaries of its own
  obtain ⟨_, st₀, hcheck, hsat₀, _⟩ :=
    CheckedType.check_complete (c := c) (val := a) (inputVar (F := F) (a := a)) input hinput
      (seed (F := F) (avar := avar) input) ⟨hav, hrv⟩
  -- the body, from where the check left off
  obtain ⟨out, st₁, hrun₁, hsat₁, hscope₁, v, hreads₁⟩ :=
    hmain st₀ ⟨hav.mono hcheck.nv_le, hrv.of_le hav hcheck.le⟩
  -- the public bundle
  obtain ⟨pub, st₂, hrun₂, hsat₂, hnv₂, hle₂, hscopeP, hreadsP⟩ :=
    witness_complete (c := c) (val := UnChecked b)
      (do let x ← readVar (val := b) out; pure (UnChecked.mk x)) (st := st₁)
      (v := UnChecked.mk v) (by simp)
      (by
        simp only [AsProver.bind_eq, AsProver.run_bind, readVar_run hscope₁,
          (reads_iff.mp hreads₁).2]
        rfl)
  have hscopeP' : Scoped (val := b) st₂ pub.val := hscopeP
  have hreadsP' : Reads st₂.env.get pub.val v := hreadsP
  -- the binding rows
  obtain ⟨_, st₃, hrun₃, hsat₃, -⟩ :=
    assertEq_complete (c := c) (val := b) out pub.val v st₂
      ⟨Scoped.mono hnv₂ hscope₁, hscopeP', hreads₁.of_le hscope₁ hle₂, hreadsP'⟩
  -- the whole run
  have hrun : Runs (compileBody (a := a) (b := b) main)
      (seed (F := F) (avar := avar) input) (out, pub.val) st₃ :=
    hcheck.bind (hrun₁.bind (hrun₂.bind (hrun₃.bind rfl)))
  have hle₃ : st₂.env.Le st₃.env := hrun₃.le
  have hres : ((out, pub.val) : bvar × bvar) = (compile (a := a) (b := b) main).result :=
    (prove_build_agrees hrun).1
  refine ⟨v, st₃.env, ?_, ?_, ?_, ?_⟩
  · unfold solve
    rw [show prove (compileBody (a := a) (b := b) main) (seed (F := F) (avar := avar) input).nv
        (seed (F := F) (avar := avar) input).env = .ok (st₃.out (out, pub.val)) from hrun]
    have hout : Scoped (val := b) st₃ out :=
      Scoped.mono hrun₃.nv_le (Scoped.mono hnv₂ hscope₁)
    show (match (readVar (val := b) out).run st₃.env with
      | Except.error e => Except.error e
      | Except.ok outVal => Except.ok (outVal, st₃.env)) = Except.ok (v, st₃.env)
    rw [readVar_run hout,
      (reads_iff.mp ((hreads₁.of_le hscope₁ hle₂).of_le (Scoped.mono hnv₂ hscope₁) hle₃)).2]
  · exact Sat.bind hcheck
      (hsat₀ (hrun₁.nv_le.trans (hnv₂.trans hrun₃.nv_le))
        (hrun₁.le.trans (hle₂.trans hle₃)))
      (Sat.bind hrun₁ (hsat₁ (Nat.le_trans hnv₂ hrun₃.nv_le) (hle₂.trans hle₃))
        (Sat.bind hrun₂ (hsat₂ hrun₃.nv_le hle₃)
          (Sat.bind hrun₃ (hsat₃ (Nat.le_refl _) (Assignments.Le.refl _)) Sat.pure)))
  · rw [← hres]
    exact (hreads₁.of_le hscope₁ hle₂).of_le (Scoped.mono hnv₂ hscope₁) hle₃
  · rw [← hres]
    exact hreadsP'.of_le hscopeP' hle₃

attribute [irreducible] inputVar compileBody compile solve

end Snarky
