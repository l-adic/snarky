import Snarky.Circuit.DSL.Assert
import Snarky.Backend.Ops

/-!
# Compiling and solving whole circuits

Port of `Snarky.Backend.Compile` (packages/snarky/src/Snarky/Backend/Compile.purs), the
entry points that turn a circuit `main : avar → CircuitM F c bvar` into a constraint
system (`compile`, PS `compile`) and a witness solver (`solve`, PS
`makeSolver`/`runSolver` collapsed — no `Effect`, no advice handler, so the solver IS the
run). Both allocate the public interface deterministically from variable `0`: inputs at
`0..A.size-1`, outputs at `A.size..A.size+B.size-1` (PS records the same range in
`publicInputs`; here it is canonical, so no field carries it).

One deliberate deviation: PS spells two near-identical programs — `compile`'s omits the
output back-fill, the solver's includes it. Since the builder ignores `assignOp`, ONE
shared program (`compileBody`) serves both interpreters, and the laws below quantify over
literally the same op tree — no cross-program reasoning. Not ported: the
`debug`/label-birth machinery (`compile'`/`makeSolver'`), the advice row
(`AdviceHandler`, the open tail `r`), and the `Checker` type (the `holds` parameter of
`prove` plays that role).

The payoff theorem is `solve_complete`: a successful solve yields an assignment that
satisfies every compiled constraint and decodes at the public slots to the given input
and the returned output.
-/

namespace Snarky

universe u

variable {F c : Type u} {a b avar bvar : Type u}

/-! ## The shared program -/

/-- Constrain paired columns equal, head first — PS's
`for_ (zip (varToFields out) (map Var bvars)) (uncurry assertEqual_)` with the zip fused
into the recursion. Mismatched lengths cannot arise from `compileBody` (both lists have
`B.size` elements); the catch-all makes the function total. -/
private def assertEqPairs [DecidableEq F] [BasicSystem F c] :
    List (CVar F) → List Variable → CircuitM F c PUnit
  | v :: vs, w :: ws => do
    assertEqual v (.var w)
    assertEqPairs vs ws
  | _, _ => pure PUnit.unit

/-- The output back-fill witness: read the output bundle's value and re-encode it as
field elements — PS `map valueToFields (read out)`. -/
private def outputWit [Add F] [Mul F] [B : CircuitType F b bvar] (out : bvar) :
    AsProver F (Vector F B.size) :=
  fun env => (readVar (val := b) out env).map B.valueToFields

/-- The public-input bundle every compiled circuit binds: the declared input type's
variable bundle over the preallocated slots `0 … A.size−1`. A whole-circuit statement
reads the input off a valuation or table through this bundle (`readVal`/`Reads`),
never by spelling slots. -/
def inputVar [A : CircuitType F a avar] : avar :=
  A.fieldsToVar (mapVec CVar.var (allocRange 0 A.size))

/-- The whole-circuit program both interpreters run: bind the input bundle to the
preallocated input slots, pay its `check`, run `main`, back-fill the output slots from
the computed output (builder: no-op; prover: the `assignOp` that makes `solve`'s output
slots live), and constrain the output bundle to those slots. PS splits this into a
builder program and a solver program; see the module docstring for why Lean shares one. -/
def compileBody [Add F] [Mul F] [DecidableEq F] [BasicSystem F c]
    [A : CircuitType F a avar] [CheckedType F c avar] [B : CircuitType F b bvar]
    (main : avar → CircuitM F c bvar) : CircuitM F c bvar := do
  let av := inputVar (F := F) (a := a)
  let bvars := allocRange A.size B.size
  CheckedType.check (c := c) av
  let out ← main av
  assignVars bvars (outputWit out)
  assertEqPairs (B.varToFields out).toList bvars.toList
  pure out

/-! ## The entry points -/

/-- Extract a circuit's constraint system (PS `compile`): run the builder on
`compileBody` with the counter already past the `A.size + B.size` public slots. -/
def compile [Add F] [Mul F] [DecidableEq F] [BasicSystem F c]
    [A : CircuitType F a avar] [CheckedType F c avar] [B : CircuitType F b bvar]
    (main : avar → CircuitM F c bvar) : Built c bvar :=
  build (compileBody (a := a) (b := b) main) (A.size + B.size)

/-- Solve a circuit on a public input (PS `makeSolver` + `runSolver`): seed the input
slots with the input's encoding, run the prover on `compileBody`, and decode the output
bundle from the final assignment. Returns the output value and the full assignment — PS's
`Tuple b (Frozen f)`. -/
def solve [Add F] [Mul F] [DecidableEq F] [BasicSystem F c]
    [A : CircuitType F a avar] [CheckedType F c avar] [B : CircuitType F b bvar]
    (holds : c → Assignments F → Bool) (main : avar → CircuitM F c bvar) (input : a) :
    Except EvalError (b × Assignments F) :=
  match Assignments.empty.extendPairs
      ((allocRange 0 A.size).toList.zip (A.valueToFields input).toList) with
  | .error e => .error e
  | .ok env₀ =>
    match prove holds (compileBody (a := a) (b := b) main) (A.size + B.size) env₀ with
    | .error e => .error e
    | .ok p =>
      match readVar (val := b) p.result p.assignments with
      | .error e => .error e
      | .ok outVal => .ok (outVal, p.assignments)

/-- A circuit with no public output emits exactly its checked body's constraints: at
output `PUnit` the back-fill assigns nothing and the output binding asserts nothing,
so `compile`'s constraint list is the input check's followed by the body's. The
whole-circuit soundness statement of a pure knowledge circuit reads its `Sound`
triple through this identity. -/
theorem compile_punit_constraints [Add F] [Mul F] [DecidableEq F] [BasicSystem F c]
    [A : CircuitType F a avar] [CheckedType F c avar]
    (main : avar → CircuitM F c PUnit) :
    (compile (a := a) (b := PUnit) main).constraints
      = (build (do CheckedType.check (c := c) (inputVar (F := F) (a := a))
                   main (inputVar (F := F) (a := a))) A.size).constraints := by
  show (build (compileBody (a := a) (b := PUnit) main) A.size).constraints = _
  simp only [compileBody, build_bind]
  show (_ : List c) ++ ((_ : List c) ++ ([] : List c)) = _
  rw [List.append_nil]

/-! ## The payoff theorem -/

/-- `allocRange` is the vector form of `List.range'`. -/
private theorem allocRange_toList (s k : Nat) :
    (allocRange s k).toList = List.range' s k := by
  apply List.ext_getElem
  · simp [allocRange]
  · intro i h1 h2
    simp [allocRange, List.getElem_range']

/-- What a successful batch extension over a contiguous range establishes: every slot in
the range holds its paired value, and everything below the range is untouched. Serves
both `solve`'s input seeding and the output back-fill. -/
private theorem extendPairs_range'_lookup :
    ∀ (l : List F) (s : Nat) {env env' : Assignments F},
      env.extendPairs ((List.range' s l.length).zip l) = .ok env' →
      (∀ j (hj : j < l.length), env' (s + j) = some l[j]) ∧
        ∀ w, w < s → env' w = env w := by
  intro l
  induction l with
  | nil =>
    intro s env env' h
    simp only [List.range', List.zip_nil_right,
      Assignments.extendPairs, Except.ok.injEq] at h
    subst h
    exact ⟨fun j hj => absurd hj (Nat.not_lt_zero j), fun _ _ => rfl⟩
  | cons x l ih =>
    intro s env env' h
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons,
      Assignments.extendPairs] at h
    split at h
    · cases h
    · next hnone =>
      obtain ⟨ihlook, ihlow⟩ := ih (s + 1) h
      refine ⟨fun j hj => ?_, fun w hw => ?_⟩
      · cases j with
        | zero =>
          simp only [Nat.add_zero, List.getElem_cons_zero]
          rw [ihlow s (Nat.lt_succ_self s)]
          simp [Assignments.extend]
        | succ j =>
          simp only [List.length_cons] at hj
          rw [show s + (j + 1) = (s + 1) + j by omega]
          rw [ihlook j (by omega)]
          simp
      · rw [ihlow w (by omega)]
        simp [Assignments.extend, Nat.ne_of_lt hw]

/-- Batch extension over a contiguous range of fresh slots cannot fail, and leaves
everything at or above the range's end unassigned. -/
private theorem extendPairs_range'_ok :
    ∀ (l : List F) (s : Nat) {env : Assignments F}, env.FreshFrom s →
      ∃ env' : Assignments F,
        env.extendPairs ((List.range' s l.length).zip l) = .ok env' ∧
        env'.FreshFrom (s + l.length) := by
  intro l
  induction l with
  | nil =>
    intro s env hf
    exact ⟨env, rfl, by simpa using hf⟩
  | cons x l ih =>
    intro s env hf
    have hfree : env s = none := hf s (Nat.le_refl s)
    have hf' : (env.extend s x).FreshFrom (s + 1) := by
      intro v hv
      have hne : v ≠ s := by omega
      simp only [Assignments.extend, hne, if_false]
      exact hf v (by omega)
    obtain ⟨env', hrun, hfout⟩ := ih (s + 1) hf'
    refine ⟨env', ?_, fun v hv => hfout v ?_⟩
    · simp only [List.length_cons, List.range'_succ, List.zip_cons_cons,
        Assignments.extendPairs, hfree]
      exact hrun
    · simp only [List.length_cons] at hv
      omega

/-- The input seeding always succeeds — the public slots are fresh on the empty
table — and the seeded table holds the input's encoding at the input slots, with
nothing assigned at or above the input range. The entry facts a whole-circuit
completeness statement starts from. -/
theorem solve_seed [A : CircuitType F a avar] (input : a) :
    ∃ env₀ : Assignments F,
      Assignments.empty.extendPairs
          ((allocRange 0 A.size).toList.zip (A.valueToFields input).toList)
        = .ok env₀ ∧
      (∀ i (hi : i < A.size), env₀ i = some ((A.valueToFields input)[i])) ∧
      env₀.FreshFrom A.size := by
  set L := (A.valueToFields input).toList with hL
  have hlenL : L.length = A.size := by simp [hL]
  obtain ⟨env₀, hrun, hfout⟩ := extendPairs_range'_ok L 0
    (env := Assignments.empty) (fun _ _ => rfl)
  have hrun' : Assignments.empty.extendPairs
      ((allocRange 0 A.size).toList.zip L) = .ok env₀ := by
    rw [allocRange_toList, ← hlenL]
    exact hrun
  refine ⟨env₀, hrun', fun i hi => ?_, fun v hv => hfout v (by omega)⟩
  have h := (extendPairs_range'_lookup L 0 hrun).1 i (by omega)
  simpa [hL] using h

/-- A no-output circuit's solve succeeds as soon as its input check and its body run
honestly: at output `PUnit` the back-fill assigns nothing, the output binding asserts
nothing, and the size-0 output decode cannot fail. Staged as the check's run then the
body's, so a consumer never touches the wrapper's internals. -/
theorem solve_punit_ok [Add F] [Mul F] [DecidableEq F] [BasicSystem F c]
    [A : CircuitType F a avar] [CheckedType F c avar]
    {holds : c → Assignments F → Bool} {main : avar → CircuitM F c PUnit}
    {input : a} {env₀ : Assignments F}
    (hseed : Assignments.empty.extendPairs
        ((allocRange 0 A.size).toList.zip (A.valueToFields input).toList)
      = .ok env₀)
    {nvc : Nat} {envc : Assignments F}
    (hcheck : prove holds (CheckedType.check (c := c) (inputVar (F := F) (a := a)))
        A.size env₀ = .ok ⟨PUnit.unit, nvc, envc⟩)
    {p : Proved F PUnit}
    (hmain : prove holds (main (inputVar (F := F) (a := a))) nvc envc = .ok p) :
    solve (b := PUnit) holds main input = .ok (PUnit.unit, p.assignments) := by
  have hbody : prove holds (compileBody (a := a) (b := PUnit) main)
      (A.size + CircuitType.size F PUnit) env₀
      = .ok ⟨p.result, p.nextVar, p.assignments⟩ := by
    show prove holds
      (CheckedType.check (c := c) (inputVar (F := F) (a := a)) >>= fun _ =>
        main (inputVar (F := F) (a := a)) >>= fun out =>
          assignVars (allocRange A.size (CircuitType.size F PUnit))
              (outputWit (b := PUnit) out) >>= fun _ =>
            assertEqPairs (CircuitType.varToFields (val := PUnit) out).toList
                (allocRange A.size (CircuitType.size F PUnit)).toList >>= fun _ =>
              pure out)
      A.size env₀ = _
    rw [prove_bind, hcheck]
    dsimp only [Except.bind]
    rw [prove_bind, hmain]
    dsimp only [Except.bind]
    rfl
  unfold solve
  rw [hseed]
  dsimp only
  rw [hbody]
  rfl

/-! ## The slot decode -/

variable [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]

omit [Zero F] [One F] in
/-- The public slots decode at ANY extending backend: a successful `proveWith` run of
`compileBody` returns a table reading the input at the input slots (the seed
survives) and the decoded output at the output slots (the back-fill wrote them, and
the tail only extends). `solve_complete` states the base-`prove` instance alongside
its constraint clause; backends whose prover seams check nothing (kimchi) consume
this form. -/
theorem proveWith_compileBody_slots {g σ : Type u} {ops : BackendOps F g c σ}
    [BasicSystem F c] [A : CircuitType F a avar] [CheckedType F c avar] [B : CircuitType F b bvar]
    (hp : ops.ProveExtends)
    {main : avar → CircuitM F c bvar} {input : a} {outVal : b}
    {env₀ : Assignments F} {p : Proved F bvar}
    (hseed : Assignments.empty.extendPairs
        ((allocRange 0 A.size).toList.zip (A.valueToFields input).toList) = .ok env₀)
    (hrun : proveWith ops (compileBody (a := a) (b := b) main)
        (A.size + B.size) env₀ = .ok p)
    (hread : readVar (val := b) p.result p.assignments = .ok outVal) :
    (∀ i (hi : i < A.size), p.assignments i = some ((A.valueToFields input)[i])) ∧
      ∀ j (hj : j < B.size),
        p.assignments (A.size + j) = some ((B.valueToFields outVal)[j]) := by
  set L := (A.valueToFields input).toList with hL
  have hlenL : L.length = A.size := by simp [hL]
  rw [allocRange_toList, ← hlenL] at hseed
  have hseedlook := (extendPairs_range'_lookup L 0 hseed).1
  rw [show p = ⟨p.result, p.nextVar, p.assignments⟩ from rfl] at hrun
  have hle₀ := (proveWith_extends hp hrun).1
  simp only [compileBody] at hrun
  rw [proveWith_bind] at hrun
  obtain ⟨s₁, hrun₁, hrun⟩ := bind_ok hrun
  rw [proveWith_bind] at hrun
  obtain ⟨s₂, hrun₂, hrun⟩ := bind_ok hrun
  have hslots : (allocRange A.size B.size).toList.find?
      (s₂.nextVar ≤ ·) = none := by
    refine List.find?_eq_none.mpr fun v hv => ?_
    have hlt := (mem_allocRange hv).2
    have h₁ := (proveWith_extends hp hrun₁).2
    have h₂ := (proveWith_extends hp hrun₂).2
    simp only [decide_eq_true_eq]
    omega
  rw [proveWith_bind] at hrun
  obtain ⟨s₃, hassign, hrun⟩ := bind_ok hrun
  simp only [assignVars, proveWith, outputWit, hslots] at hassign
  split at hassign
  · cases hassign
  next xs hwit =>
    split at hassign
    · cases hassign
    next env₃ hext =>
      cases hwitread : readVar (val := b) s₂.result s₂.assignments with
      | error e => rw [hwitread] at hwit; cases hwit
      | ok ov =>
        rw [hwitread] at hwit
        simp only [Except.map, Except.ok.injEq] at hwit
        subst hwit
        set M := (B.valueToFields ov).toList with hM
        have hlenM : M.length = B.size := by simp [hM]
        rw [allocRange_toList, ← hlenM] at hext
        have hextlook := (extendPairs_range'_lookup M A.size hext).1
        simp only [Except.ok.injEq] at hassign
        subst hassign
        have hle₃ : env₃.Le p.assignments := (proveWith_extends hp hrun).1
        have hle₂ : s₂.assignments.Le p.assignments :=
          (Assignments.le_extendPairs hext).trans hle₃
        have hres : s₂.result = p.result := by
          rw [proveWith_bind] at hrun
          obtain ⟨s₄, -, hpure⟩ := bind_ok hrun
          simp only [proveWith, Except.ok.injEq, Proved.mk.injEq] at hpure
          exact hpure.1
        rw [hres] at hwitread
        rw [readVar_le hle₂ hwitread] at hread
        cases hread
        refine ⟨fun i hi => ?_, fun j hj => ?_⟩
        · have hlook := hseedlook i (by omega)
          rw [Nat.zero_add] at hlook
          have hfin := hle₀ i _ hlook
          rw [hfin]
          simp [hL]
        · have hfin := hle₃ (A.size + j) _ (hextlook j (by omega))
          rw [hfin]
          simp [hM]

/-- A successful `solve` produces an assignment that satisfies
every constraint `compile` emits, holds the input's encoding at the input slots, and
holds the returned output's encoding at the output slots. Stated over the reference
`Basic F` backend, whose `holds` is monotone (`Basic.holds_mono`).

Constraint satisfaction is `prove_complete` for the shared program — the checking
prover's own clause, with no backend-generic counterpart; the slot decodes are
`proveWith_compileBody_slots` at the base ops (`prove` is `proveWith` at
`checkedOps`, which extends). -/
theorem solve_complete [A : CircuitType F a avar] [CheckedType F (Basic F) avar]
    [B : CircuitType F b bvar] {main : avar → CircuitM F (Basic F) bvar} {input : a}
    {outVal : b} {env : Assignments F}
    (h : solve (b := b) Basic.holds main input = .ok (outVal, env)) :
    (∀ con ∈ (compile (a := a) (b := b) main).constraints, con.holds env = true) ∧
      ((∀ i (hi : i < A.size), env i = some ((A.valueToFields input)[i])) ∧
        ∀ j (hj : j < B.size), env (A.size + j) = some ((B.valueToFields outVal)[j])) := by
  unfold solve at h
  split at h
  · cases h
  next env₀ hseed =>
    split at h
    · cases h
    next p hrun =>
      split at h
      · cases h
      next out' hread =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hmono : ∀ (con : Basic F) {e e' : Assignments F},
            e.Le e' → con.holds e = true → con.holds e' = true :=
          fun _ => Basic.holds_mono
        rw [show p = ⟨p.result, p.nextVar, p.assignments⟩ from rfl] at hrun
        have hsat := prove_complete hmono hrun
        rw [← proveWith_checkedOps] at hrun
        exact ⟨hsat, proveWith_compileBody_slots (checkedOps_proveExtends _)
          hseed hrun hread⟩
