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

`solve_spec` is the payoff: a circuit whose body has its law at the prover's reading solves,
and the table it produces satisfies every compiled row and reads the input and the output at
the public bundles; `solve_complete` is the same theorem under the seam's completeness name.
`compile_reads` and `compileWith_reads` are the reading side: wherever the compiled
rows hold, a public input given in the order of `compiledPublicVars` reads as the typed input
and the body's typed output.
-/

namespace Snarky

set_option mvcgen.warning false

variable {F c a b avar bvar : Type}

/-- The public input bundle: the encoding's slots, from `0`. -/
def inputVar [A : CircuitType F a avar] : avar :=
  A.fieldsToVar (mapVec CVar.var (allocRange 0 A.size))

/-- The whole-circuit program: bind the input bundle, pay its check, run the body,
witness the output's encoding into fresh public slots, and constrain the body's output to
them. The result is the body's output paired with the public bundle. -/
def compileBody [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F a avar]
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
def compile [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [A : CircuitType F a avar]
    [CheckedType F c a avar] [CircuitType F b bvar] (main : avar → CircuitM F c bvar) :
    Built c (bvar × bvar) :=
  build (compileBody (a := a) (b := b) main) A.size

/-- The state a solve starts from: the input's encoding at the input slots. -/
def seed [A : CircuitType F a avar] (input : a) : ProverState F :=
  ⟨A.size, Assignments.empty.extendList 0 (A.valueToFields input).toList, by
    simpa using Assignments.empty_dom.extendList (A.valueToFields input).toList⟩

/-- Solve a circuit on a public input: run the prover on the whole-circuit program from
the seeded table and read the output bundle back. -/
def solve [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [CircuitType F a avar]
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

open CircuitType Std.Do in
/-- A circuit whose body has its law at the prover's reading solves at an admissible public
input: the run succeeds, the table it produces satisfies every compiled row, and the compiled
system's two bundles — the body's output and the public one — both read as the value the solve
returned, with the input bundle still reading the value the solve was given. The circuit is
read at the completeness tag, `main (c := Prover c)` for a body generic in its constraint type,
where the checked types' laws live; the body's law starts from the input bundle reading the
input. The run is read off the whole-circuit program's law by `proverWP_prove`. -/
theorem solve_spec [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] [A : CircuitType F a avar] [CheckedType F (Prover c) a avar]
    [WPCheckedType F (Prover c) a avar] [B : CircuitType F b bvar]
    {main : avar → CircuitM F (Prover c) bvar} (input : a)
    (hinput : CheckedType.Valid (F := F) (c := Prover c) (var := avar) input)
    (hmain : ∀ st₀ : ProverState F,
      ⦃fun s => ⌜s = st₀ ∧ ReadsAs (val := a) st₀ (inputVar (F := F) (a := a)) input⌝⦄
      main (inputVar (F := F) (a := a))
      ⦃⇓ out s' => ⌜Scoped (val := b) s' out ∧ WellFormed (val := b) s'.env.get out ∧
        st₀ ≤ s'⌝⦄) :
    ∃ (outVal : b) (env : Assignments F),
      solve (c := Prover c) (a := a) (b := b) main input = .ok (outVal, env) ∧
      (∀ con ∈ (compile (c := Prover c) (a := a) (b := b) main).constraints,
        ConstraintHolds.Holds env.get con) ∧
      Reads env.get (inputVar (F := F) (a := a)) input ∧
      Reads env.get (compile (c := Prover c) (a := a) (b := b) main).result.1 outVal ∧
      Reads env.get (compile (c := Prover c) (a := a) (b := b) main).result.2 outVal := by
  have hm := Prover.register hmain
  have hw := fun out : bvar => Prover.register (Prover.witness_of_run (F := F) (c := c)
    (val := UnChecked b) (do let x ← readVar (val := b) out; pure (UnChecked.mk x))
    (fun st => Scoped (val := b) st out)
    (fun st => UnChecked.mk (readVal st.env.get out))
    (fun st (h : Scoped (val := b) st out) => by
      simp only [AsProver.bind_eq, AsProver.run_bind, readVar_run h, Except.bind]
      rfl)
    (fun _ _ _ _ _ => trivial))
  have hseed : ReadsAs (val := a) (seed (F := F) (avar := avar) input)
      (inputVar (F := F) (a := a)) input :=
    ⟨scoped_inputVar input, reads_inputVar input⟩
  -- the whole-circuit program's law: the public bundle reads the body's output value
  have hbody : ⦃fun s => ⌜s = seed (F := F) (avar := avar) input⌝⦄
      compileBody (c := Prover c) (a := a) (b := b) main
      ⦃⇓ r s' => ⌜∃ v : b, ReadsAs (val := b) s' r.1 v ∧ ReadsAs (val := b) s' r.2 v ∧
        ReadsAs (val := a) s' (inputVar (F := F) (a := a)) input⌝⦄ := by
    unfold compileBody
    mvcgen [hm, hw]
    -- the input's check: the seeded bundle reads the input, admissibly
    case vc2 =>
      rename_i s h
      subst h
      exact ⟨trivial, hseed, hinput⟩
    -- the body: the input still reads past the check
    case vc3 =>
      rename_i s₀ h₀ u s h
      subst h₀
      exact ⟨trivial, hseed.of_le h⟩
    -- the public bundle's witness: the body's output in scope
    case vc4 =>
      rename_i h
      exact ⟨trivial, (Prover.Reg.iff.mp h).1⟩
    -- the binding rows: the output and the public bundle read the same fields
    case vc5 =>
      rename_i out s₂ h₂ pub s h₃
      simp only [Prover.Reg.iff] at h₂ h₃
      obtain ⟨v, hv⟩ := h₂.2.1
      have hR : Reads s.env.get pub.val (readVal s₂.env.get out) := reads_unchecked'.mp h₃.1.2
      rw [(reads_iff.mp hv).2] at hR
      exact ⟨trivial, h₂.1.mono (ProverState.nv_le_of_le h₃.2), scoped_unchecked'.mp h₃.1.1,
        Eq.trans (hv.of_le h₂.1 h₃.2) (Eq.symm hR)⟩
    -- the result: both bundles read the output's value, the input its own
    case vc6 =>
      rename_i s₀ h₀ u₁ s₁ h₁ out s₂ h₂ pub s₃ h₃ u₂ s h₄
      simp only [Prover.Reg.iff] at h₂ h₃ h₄
      subst h₀
      refine ⟨readVal s₂.env.get out, ?_, ?_,
        hseed.of_le (h₁.trans (h₂.2.2.trans (h₃.2.trans h₄)))⟩
      · exact (show ReadsAs (val := b) s₂ out (readVal s₂.env.get out) from
          ⟨h₂.1, reads_iff.mpr ⟨h₂.2.1, rfl⟩⟩).of_le (h₃.2.trans h₄)
      · exact (show ReadsAs (val := b) s₃ pub.val (readVal s₂.env.get out) from
          ⟨scoped_unchecked'.mp h₃.1.1, reads_unchecked'.mp h₃.1.2⟩).of_le h₄
  obtain ⟨r, st', hrun, -, ⟨v, hrd1, hrd2, hrin⟩, hrows⟩ :=
    proverWP_prove (c := Prover c) (hbody (seed (F := F) (avar := avar) input) rfl)
  have hres : r = (compile (c := Prover c) (a := a) (b := b) main).result :=
    (prove_build_agrees hrun).1
  refine ⟨v, st'.env, ?_, hrows st' le_rfl, hrin.2, ?_, ?_⟩
  · unfold solve
    rw [show prove (compileBody (c := Prover c) (a := a) (b := b) main)
        (seed (F := F) (avar := avar) input).nv (seed (F := F) (avar := avar) input).env
        = .ok (st'.out r) from hrun]
    show (match (readVar (val := b) r.1).run st'.env with
      | Except.error e => Except.error e
      | Except.ok outVal => Except.ok (outVal, st'.env)) = Except.ok (v, st'.env)
    rw [readVar_run hrd1.1, (reads_iff.mp hrd1.2).2]
  · rw [← hres]
    exact hrd1.2
  · rw [← hres]
    exact hrd2.2

open CircuitType Std.Do in
/-- The solver's completeness under the seam's completeness name: `solve_spec`'s statement,
proved by `solve_spec`, which is the result. The axiom gate roots this name, so a search for
the solver's completeness law lands on a checked theorem. -/
theorem solve_complete [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [LawfulBasicSystem F c] [A : CircuitType F a avar] [CheckedType F (Prover c) a avar]
    [WPCheckedType F (Prover c) a avar] [B : CircuitType F b bvar]
    {main : avar → CircuitM F (Prover c) bvar} (input : a)
    (hinput : CheckedType.Valid (F := F) (c := Prover c) (var := avar) input)
    (hmain : ∀ st₀ : ProverState F,
      ⦃fun s => ⌜s = st₀ ∧ ReadsAs (val := a) st₀ (inputVar (F := F) (a := a)) input⌝⦄
      main (inputVar (F := F) (a := a))
      ⦃⇓ out s' => ⌜Scoped (val := b) s' out ∧ WellFormed (val := b) s'.env.get out ∧
        st₀ ≤ s'⌝⦄) :
    ∃ (outVal : b) (env : Assignments F),
      solve (c := Prover c) (a := a) (b := b) main input = .ok (outVal, env) ∧
      (∀ con ∈ (compile (c := Prover c) (a := a) (b := b) main).constraints,
        ConstraintHolds.Holds env.get con) ∧
      Reads env.get (inputVar (F := F) (a := a)) input ∧
      Reads env.get (compile (c := Prover c) (a := a) (b := b) main).result.1 outVal ∧
      Reads env.get (compile (c := Prover c) (a := a) (b := b) main).result.2 outVal :=
  solve_spec input hinput hmain

/-- The counter the body starts from: past the input slots, and past whatever the input
bundle's own check allocated. -/
def bodyStart [Field F] [BasicSystem F c] [ConstraintHolds F c] [A : CircuitType F a avar]
    [CheckedType F c a avar] : Nat :=
  (build (CheckedType.check (F := F) (c := c) (val := a)
    (inputVar (F := F) (a := a))) A.size).nextVar

/-! ## Circuits that keep cells

A statement about a circuit often needs cells the circuit computes but does not publish, such
as what a verifier gadget read. `compileWith` compiles a body that returns those cells beside
its output: the constraint system is `compile`'s, and the run's result carries the cells
(`compileWith_result`), so the rows and the cells come from one run. -/

/-- `compileBody` for a body that also returns cells it keeps internal: only the output is
bound to the public bundle, and the cells ride along in the result. -/
def compileWithBody {α : Type} [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [CircuitType F a avar] [CheckedType F c a avar] [CircuitType F b bvar]
    (main : avar → CircuitM F c (bvar × α)) : CircuitM F c ((bvar × α) × bvar) := do
  let av : avar := inputVar (F := F) (a := a)
  CheckedType.check (c := c) (val := a) av
  let out ← main av
  let pub ← witness (val := UnChecked b) (do
    let x ← readVar (val := b) out.1
    pure (UnChecked.mk x))
  assertEq (val := b) out.1 pub.val
  pure (out, pub.val)

/-- `compile` for a body that also returns cells it keeps internal (`compileWithBody`). -/
def compileWith {α : Type} [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    [A : CircuitType F a avar] [CheckedType F c a avar] [CircuitType F b bvar]
    (main : avar → CircuitM F c (bvar × α)) : Built c ((bvar × α) × bvar) :=
  build (compileWithBody (a := a) (b := b) main) A.size

/-- The run's result carries the body's: its output and its cells, as the body builds from
`bodyStart`. -/
theorem compileWith_result {α : Type} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [A : CircuitType F a avar] [CheckedType F c a avar]
    [CircuitType F b bvar] (main : avar → CircuitM F c (bvar × α)) :
    (compileWith (a := a) (b := b) main).result.1
      = (build (main (inputVar (F := F) (a := a)))
          (bodyStart (F := F) (c := c) (a := a) (avar := avar))).result := by
  simp only [compileWith, compileWithBody, bodyStart, build_bind]
  rfl

/-- The compiled rows contain the body's, built from `bodyStart`. -/
theorem mem_compileWith_of_mem_body {α : Type} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [A : CircuitType F a avar] [CheckedType F c a avar]
    [CircuitType F b bvar] {main : avar → CircuitM F c (bvar × α)} {con : c}
    (h : con ∈ (build (main (inputVar (F := F) (a := a)))
      (bodyStart (F := F) (c := c) (a := a) (avar := avar))).constraints) :
    con ∈ (compileWith (a := a) (b := b) main).constraints := by
  rw [bodyStart] at h
  rw [compileWith, compileWithBody, build_bind, List.mem_append]
  exact Or.inr (by rw [build_bind, List.mem_append]; exact Or.inl h)

/-! ## The public layout and its readings

`compiledPublicVars` lays out a compiled circuit's public variables: the input slots, then the
variables of the output's public copy. Both blocks are fresh variables, so the layout follows
from the build alone. `compile_reads` and `compileWith_reads` read a public input given in that
order: the input bundle reads as a value exactly when the value encodes the input fields, and
the body's output exactly when it encodes the output fields. The input reading is the layout;
the output reading also needs the rows binding the body's output to its public copy. -/

/-- The variables backing a bundle of plain variables — the witnessed public output
slots, whose ids the assembly needs but whose numbering it does not care about. -/
private def bundleVars [Add F] [Mul F] [Zero F] [CircuitType F b bvar] (v : bvar) :
    List Variable :=
  (CircuitType.varToFields (val := b) v).toList.filterMap fun (cv : CVar F) =>
    match cv with
    | CVar.var w => some w
    | _ => none

/-- The public variables of a compiled circuit: the input slots, then the variables of the
output bundle the compiled program witnessed. -/
def compiledPublicVars [Add F] [Mul F] [Zero F] [A : CircuitType F a avar]
    [CircuitType F b bvar] {β : Type} (built : Built c (β × bvar)) : List Variable :=
  (allocRange 0 A.size).toList ++ bundleVars (F := F) (b := b) built.result.2

/-- The fields of a bundle of fresh variables are those variables. -/
private theorem bundleVars_fresh [Add F] [Mul F] [Zero F] [B : CircuitType F b bvar] (k : Nat) :
    bundleVars (F := F) (b := b) (B.fieldsToVar (mapVec CVar.var (allocRange k B.size))) =
      (allocRange k B.size).toList := by
  simp [bundleVars, B.var_roundTrip, List.filterMap_map]

/-- The public variables of a built circuit whose public copy is fresh at `k`. -/
private theorem compiledPublicVars_fresh [Add F] [Mul F] [Zero F] [A : CircuitType F a avar]
    [B : CircuitType F b bvar] {β : Type} (built : Built c (β × bvar)) (k : Nat)
    (h : built.result.2 = B.fieldsToVar (mapVec CVar.var (allocRange k B.size))) :
    compiledPublicVars (F := F) (a := a) (b := b) built =
      (allocRange 0 A.size).toList ++ (allocRange k B.size).toList := by
  rw [compiledPublicVars, h, bundleVars_fresh]

variable [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
  [A : CircuitType F a avar] [CheckedType F c a avar] [B : CircuitType F b bvar]

/-- `compile`'s public copy of the output: the fresh slots past the body. -/
private theorem compile_result_public (main : avar → CircuitM F c bvar) :
    (compile (a := a) (b := b) main).result.2 =
      B.fieldsToVar (mapVec CVar.var (allocRange (build (main (inputVar (F := F) (a := a)))
        (bodyStart (F := F) (c := c) (a := a) (avar := avar))).nextVar B.size)) := by
  simp only [compile, compileBody, bodyStart, build_bind]
  rfl

/-- `compileWith`'s public copy of the output: the fresh slots past the body. -/
private theorem compileWith_result_public {α : Type} (main : avar → CircuitM F c (bvar × α)) :
    (compileWith (a := a) (b := b) main).result.2 =
      B.fieldsToVar (mapVec CVar.var (allocRange (build (main (inputVar (F := F) (a := a)))
        (bodyStart (F := F) (c := c) (a := a) (avar := avar))).nextVar B.size)) := by
  simp only [compileWith, compileWithBody, bodyStart, build_bind]
  rfl

/-- A compiled circuit has one public variable per input field and one per output field. -/
theorem length_compiledPublicVars_compile (main : avar → CircuitM F c bvar) :
    (compiledPublicVars (F := F) (a := a) (b := b) (compile (a := a) (b := b) main)).length =
      A.size + B.size := by
  rw [compiledPublicVars_fresh _ _ (compile_result_public main)]
  simp

/-- `length_compiledPublicVars_compile` for a circuit that keeps cells. -/
theorem length_compiledPublicVars_compileWith {α : Type}
    (main : avar → CircuitM F c (bvar × α)) :
    (compiledPublicVars (F := F) (a := a) (b := b) (compileWith (a := a) (b := b) main)).length =
      A.size + B.size := by
  rw [compiledPublicVars_fresh _ _ (compileWith_result_public main)]
  simp

/-- Where `compile`'s rows hold, the body's output and its public copy have equal fields. -/
private theorem compile_binds [LawfulBasicSystem F c] (main : avar → CircuitM F c bvar)
    (V : Valuation F)
    (hsat : ∀ con ∈ (compile (a := a) (b := b) main).constraints, ConstraintHolds.Holds V con) :
    mapVec (·.val V)
        (CircuitType.varToFields (val := b) (compile (a := a) (b := b) main).result.1) =
      mapVec (·.val V)
        (CircuitType.varToFields (val := b) (compile (a := a) (b := b) main).result.2) := by
  simp only [compile, compileBody, build_bind, List.mem_append] at hsat ⊢
  exact (builder_spec_iff (V := V) _ _).mp
    (assertEq_fields_spec (V := V) (c := c) (val := b) _ _) _
    (fun con hc => hsat con (Or.inr (Or.inr (Or.inr (Or.inl hc)))))

/-- Where `compileWith`'s rows hold, the body's output and its public copy have equal fields. -/
private theorem compileWith_binds [LawfulBasicSystem F c] {α : Type}
    (main : avar → CircuitM F c (bvar × α)) (V : Valuation F)
    (hsat : ∀ con ∈ (compileWith (a := a) (b := b) main).constraints,
      ConstraintHolds.Holds V con) :
    mapVec (·.val V)
        (CircuitType.varToFields (val := b) (compileWith (a := a) (b := b) main).result.1.1) =
      mapVec (·.val V)
        (CircuitType.varToFields (val := b) (compileWith (a := a) (b := b) main).result.2) := by
  simp only [compileWith, compileWithBody, build_bind, List.mem_append] at hsat ⊢
  exact (builder_spec_iff (V := V) _ _).mp
    (assertEq_fields_spec (V := V) (c := c) (val := b) _ _) _
    (fun con hc => hsat con (Or.inr (Or.inr (Or.inr (Or.inl hc)))))

omit [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c] [CheckedType F c a avar] in
/-- The readings from the layout: a public copy fresh at `k`, an output bound to it, and the
public input in the compiled order. -/
private theorem reads_of_layout {β : Type} (built : Built c (β × bvar)) (out : bvar) (k : Nat)
    (V : Valuation F)
    (hpubv : built.result.2 = B.fieldsToVar (mapVec CVar.var (allocRange k B.size)))
    (hbind : mapVec (·.val V) (CircuitType.varToFields (val := b) out) =
      mapVec (·.val V) (CircuitType.varToFields (val := b) built.result.2))
    (pubIn : Vector F A.size) (pubOut : Vector F B.size)
    (hpub : (compiledPublicVars (F := F) (a := a) (b := b) built).map V =
      pubIn.toList ++ pubOut.toList) :
    (∀ x : a, CircuitType.Reads V (inputVar (F := F) (a := a)) x ↔ A.valueToFields x = pubIn) ∧
      ∀ y : b, CircuitType.Reads V out y ↔ B.valueToFields y = pubOut := by
  rw [compiledPublicVars_fresh built k hpubv, List.map_append] at hpub
  obtain ⟨hin, hout⟩ := List.append_inj hpub (by simp)
  have hinF : mapVec (·.val V) (CircuitType.varToFields (val := a) (inputVar (F := F) (a := a))) =
      pubIn := by
    apply Vector.toList_inj.mp
    rw [inputVar, A.var_roundTrip, toList_mapVec, toList_mapVec, List.map_map, ← hin]
    rfl
  have houtF : mapVec (·.val V) (CircuitType.varToFields (val := b) out) = pubOut := by
    apply Vector.toList_inj.mp
    rw [hbind, hpubv, B.var_roundTrip, toList_mapVec, toList_mapVec, List.map_map, ← hout]
    rfl
  refine ⟨fun x => ?_, fun y => ?_⟩
  · rw [CircuitType.Reads, hinF, eq_comm]
  · rw [CircuitType.Reads, houtF, eq_comm]

/-- **The compiled circuit's typed reading.** Where `compile`'s rows hold at `V` and `V` takes
the public input `pubIn ++ pubOut` at the public variables, the input bundle reads as `x`
exactly when `x` encodes to `pubIn`, and the body's output as `y` exactly when `y` encodes to
`pubOut`. -/
theorem compile_reads [LawfulBasicSystem F c] {main : avar → CircuitM F c bvar}
    {V : Valuation F}
    (hsat : ∀ con ∈ (compile (a := a) (b := b) main).constraints, ConstraintHolds.Holds V con)
    (pubIn : Vector F A.size) (pubOut : Vector F B.size)
    (hpub : (compiledPublicVars (F := F) (a := a) (b := b) (compile (a := a) (b := b) main)).map V =
      pubIn.toList ++ pubOut.toList) :
    (∀ x : a, CircuitType.Reads V (inputVar (F := F) (a := a)) x ↔ A.valueToFields x = pubIn) ∧
      ∀ y : b, CircuitType.Reads V (compile (a := a) (b := b) main).result.1 y ↔
        B.valueToFields y = pubOut :=
  reads_of_layout _ _ _ V (compile_result_public main) (compile_binds main V hsat) pubIn pubOut hpub

/-- `compile_reads` for a circuit that keeps cells: the body's output is `result.1.1`, and the
cells stay in `result.1.2` under the same valuation. -/
theorem compileWith_reads [LawfulBasicSystem F c] {α : Type}
    {main : avar → CircuitM F c (bvar × α)} {V : Valuation F}
    (hsat : ∀ con ∈ (compileWith (a := a) (b := b) main).constraints,
      ConstraintHolds.Holds V con)
    (pubIn : Vector F A.size) (pubOut : Vector F B.size)
    (hpub : (compiledPublicVars (F := F) (a := a) (b := b)
      (compileWith (a := a) (b := b) main)).map V = pubIn.toList ++ pubOut.toList) :
    (∀ x : a, CircuitType.Reads V (inputVar (F := F) (a := a)) x ↔ A.valueToFields x = pubIn) ∧
      ∀ y : b, CircuitType.Reads V (compileWith (a := a) (b := b) main).result.1.1 y ↔
        B.valueToFields y = pubOut :=
  reads_of_layout _ _ _ V (compileWith_result_public main) (compileWith_binds main V hsat) pubIn
    pubOut hpub

attribute [irreducible] inputVar compileBody compile solve compileWithBody compileWith

end Snarky
