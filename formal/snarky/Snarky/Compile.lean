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
returned, with the input bundle still reading the value the solve was given.
Admissibility (`CheckedType.Valid`) is the input type's own rows read at the value, so the
statement covers exactly the inputs the compiled system accepts and assumes nothing else
about the prover. The input reading is what lets a soundness statement about satisfying
valuations be applied to the table this produces. -/
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
      Reads env.get (inputVar (F := F) (a := a)) input ∧
      Reads env.get (compile (a := a) (b := b) main).result.1 outVal ∧
      Reads env.get (compile (a := a) (b := b) main).result.2 outVal := by
  have hav := scoped_inputVar (F := F) (avar := avar) input
  have hrv := reads_inputVar (F := F) (avar := avar) input
  -- the whole-circuit program's law, on the completeness primitives: the input's check,
  -- the body, the public bundle's witness, and the binding rows, each framed across the
  -- next
  have hbody : Complete (F := F) (c := c)
      (fun st => Scoped (val := a) st (inputVar (F := F) (a := a)) ∧
        Reads st.env.get (inputVar (F := F) (a := a)) input)
      (compileBody (a := a) (b := b) main)
      (fun r st' => ∃ v : b, Scoped (val := b) st' r.1 ∧ Reads st'.env.get r.1 v ∧
        Scoped (val := b) st' r.2 ∧ Reads st'.env.get r.2 v ∧
        Reads st'.env.get (inputVar (F := F) (a := a)) input) := by
    simp only [compileBody]
    refine Complete.bind
      (Complete.imp (fun _ h => ⟨h, h⟩) (fun _ _ h => h)
        (Complete.frame Mono.readsAs
          (CheckedType.check_complete (c := c) (val := a)
            (inputVar (F := F) (a := a)) input hinput)))
      fun _ => ?_
    refine Complete.bind
      (Complete.imp (fun _ h => ⟨h.2, h.2⟩) (fun _ _ h => h)
        (Complete.frame Mono.readsAs hmain))
      fun out => ?_
    -- the body's output value, named off its well-formedness
    refine Complete.instantiate (ι := b)
      (P := fun v st => CircuitType.ReadsAs (val := b) st out v ∧
        CircuitType.ReadsAs (val := a) st (inputVar (F := F) (a := a)) input)
      (fun st h => ⟨h.1.2.choose, ⟨h.1.1, h.1.2.choose_spec⟩, h.2⟩)
      fun v => ?_
    refine Complete.bind
      (Complete.imp (fun st h => ⟨?wrun, h⟩) (fun _ _ h => h)
        (Complete.frame (Mono.and Mono.readsAs Mono.readsAs)
          (Complete.witness
            (do let x ← readVar (val := b) out; pure (UnChecked.mk x))
            (UnChecked.mk v) (by simp))))
      fun pub => ?_
    case wrun =>
      simp only [AsProver.bind_eq, AsProver.run_bind, readVar_run h.1.1,
        (reads_iff.mp h.1.2).2, Except.bind]
      rfl
    refine Complete.bind
      (Complete.imp
        (fun st h => ⟨⟨h.2.1.1, CircuitType.scoped_unchecked.mp h.1.1,
          h.2.1.2, CircuitType.reads_unchecked.mp h.1.2⟩, h⟩)
        (fun _ _ h => h)
        (Complete.frame
          (Mono.and Mono.readsAs (Mono.and Mono.readsAs Mono.readsAs))
          (assertEq_complete (c := c) (val := b) out pub.val v)))
      fun _ => Complete.pure_of fun st h =>
        ⟨v, h.2.2.1.1, h.2.2.1.2, CircuitType.scoped_unchecked.mp h.2.1.1,
          CircuitType.reads_unchecked.mp h.2.1.2, h.2.2.2.2⟩
  obtain ⟨r, st', hrun, hsat, v, hsc1, hrd1, hsc2, hrd2, hrin⟩ :=
    hbody (seed (F := F) (avar := avar) input) ⟨hav, hrv⟩
  have hres : r = (compile (a := a) (b := b) main).result := (prove_build_agrees hrun).1
  refine ⟨v, st'.env, ?_, ?_, hrin, ?_, ?_⟩
  · unfold solve
    rw [show prove (compileBody (a := a) (b := b) main)
        (seed (F := F) (avar := avar) input).nv (seed (F := F) (avar := avar) input).env
        = .ok (st'.out r) from hrun]
    show (match (readVar (val := b) r.1).run st'.env with
      | Except.error e => Except.error e
      | Except.ok outVal => Except.ok (outVal, st'.env)) = Except.ok (v, st'.env)
    rw [readVar_run hsc1, (reads_iff.mp hrd1).2]
  · exact hsat (Nat.le_refl _) (Assignments.Le.refl _)
  · rw [← hres]
    exact hrd1
  · rw [← hres]
    exact hrd2

/-- The counter the body starts from: past the input slots, and past whatever the input
bundle's own check allocated. -/
def bodyStart [Field F] [BasicSystem F c] [A : CircuitType F a avar]
    [CheckedType F c a avar] : Nat :=
  (build (CheckedType.check (F := F) (c := c) (val := a)
    (inputVar (F := F) (a := a))) A.size).nextVar

/-- The compiled system's rows contain the input check's, built at the input slots: the
whole-circuit program pays the check first. A valuation satisfying the compiled system
therefore satisfies the check's rows, and so — through `CheckedType.check_sound` — whatever
the input type's own rows force about the bundle. -/
theorem mem_compile_of_mem_check [Field F] [DecidableEq F] [BasicSystem F c]
    [A : CircuitType F a avar] [CheckedType F c a avar] [CircuitType F b bvar]
    {main : avar → CircuitM F c bvar} {con : c}
    (h : con ∈ (build (CheckedType.check (F := F) (c := c) (val := a)
      (inputVar (F := F) (a := a))) A.size).constraints) :
    con ∈ (compile (a := a) (b := b) main).constraints := by
  rw [compile, compileBody, build_bind, List.mem_append]
  exact Or.inl h

/-- The compiled system's rows contain the body's, built from `bodyStart`: the
whole-circuit program runs the input check, then the body, then the output binding, and
`build_bind` concatenates their rows in that order. A valuation satisfying the compiled
system therefore satisfies the body's own rows — the direction a soundness triple needs. -/
theorem mem_compile_of_mem_body [Field F] [DecidableEq F] [BasicSystem F c]
    [A : CircuitType F a avar] [CheckedType F c a avar] [CircuitType F b bvar]
    {main : avar → CircuitM F c bvar} {con : c}
    (h : con ∈ (build (main (inputVar (F := F) (a := a)))
      (bodyStart (F := F) (c := c) (a := a) (avar := avar))).constraints) :
    con ∈ (compile (a := a) (b := b) main).constraints := by
  rw [bodyStart] at h
  rw [compile, compileBody, build_bind, List.mem_append]
  exact Or.inr (by rw [build_bind, List.mem_append]; exact Or.inl h)

attribute [irreducible] inputVar compileBody compile solve

end Snarky
