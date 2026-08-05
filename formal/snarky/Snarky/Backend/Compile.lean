import Snarky.Circuit.DSL.Assert

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
literally the same op tree — no cross-program reasoning. Non-ported (D8): the
`debug`/label-birth machinery (`compile'`/`makeSolver'`), the advice row
(`AdviceHandler`, the open tail `r`), and the `Checker` type (the `holds` parameter of
`prove` plays that role).

## The payoff (the fragment-interface seam)

`solve_complete`: a successful solve yields an assignment that satisfies every compiled
constraint AND decodes at the public slots to the given input and the returned output.
This is the statement a verifier fragment exports — downstream, per-fragment soundness
towers consume satisfying assignments through exactly this interface
(`formal/docs/circuit-verifier-faithfulness.md`).
-/

namespace Snarky

universe u

variable {F c : Type u} {a b avar bvar : Type u}

/-! ## The shared program -/

/-- Constrain paired columns equal, head first — PS's
`for_ (zip (varToFields out) (map Var bvars)) (uncurry assertEqual_)` with the zip fused
into the recursion. Mismatched lengths cannot arise from `compileBody` (both lists have
`B.size` elements); the catch-all makes the function total. -/
def assertEqPairs [DecidableEq F] [BasicSystem F c] :
    List (CVar F) → List Variable → CircuitM F c PUnit
  | v :: vs, w :: ws => do
    assertEqual v (.var w)
    assertEqPairs vs ws
  | _, _ => pure PUnit.unit

/-- The output back-fill witness: read the output bundle's value and re-encode it as
field elements — PS `map valueToFields (read out)`. -/
def outputWit [Add F] [Mul F] [B : CircuitType F b bvar] (out : bvar) :
    AsProver F (Vector F B.size) :=
  fun env => (readVar (val := b) out env).map B.valueToFields

/-- The whole-circuit program both interpreters run: bind the input bundle to the
preallocated input slots, pay its `check`, run `main`, back-fill the output slots from
the computed output (builder: no-op; prover: the `assignOp` that makes `solve`'s output
slots live), and constrain the output bundle to those slots. PS splits this into a
builder program and a solver program; see the module docstring for why Lean shares one. -/
def compileBody [Add F] [Mul F] [DecidableEq F] [BasicSystem F c]
    [A : CircuitType F a avar] [CheckedType F c avar] [B : CircuitType F b bvar]
    (main : avar → CircuitM F c bvar) : CircuitM F c bvar := do
  let av := A.fieldsToVar (mapVec CVar.var (allocRange 0 A.size))
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

/-! ## The payoff theorem -/

/-- Splitter for successful `Except.bind`s: recover the intermediate value. -/
private theorem bind_ok {α β : Type u} {x : Except EvalError α}
    {f : α → Except EvalError β} {r : β} (h : x.bind f = .ok r) :
    ∃ m, x = .ok m ∧ f m = .ok r := by
  cases x with
  | error e => simp only [Except.bind] at h; cases h
  | ok m => exact ⟨m, rfl, h⟩

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

variable [Add F] [Mul F] [Zero F] [One F] [DecidableEq F]

/-- **The fragment seam**: a successful `solve` produces an assignment that satisfies
every constraint `compile` emits, holds the input's encoding at the input slots, and
holds the returned output's encoding at the output slots. Stated over the reference
`Basic F` backend, whose `holds` is monotone (`Basic.holds_mono`).

Constraint satisfaction is `prove_complete` for the shared program; the slot decodes
chase the run: the seed fills the input slots and prover runs only extend
(`prove_assignments_le`), and the back-fill's `extendPairs` fills the output slots with
the encoding of the value `readVar` sees mid-run — carried to the returned output by
`readVar_le`. Stepped through in the body. -/
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
        -- The seed's slot facts, behind an opaque list so the range' lemma applies.
        set L := (A.valueToFields input).toList with hL
        have hlenL : L.length = A.size := by simp [hL]
        rw [allocRange_toList, ← hlenL] at hseed
        have hseedlook := (extendPairs_range'_lookup L 0 hseed).1
        -- The whole-run facts, before the equation is decomposed.
        have hmono : ∀ (con : Basic F) {e e' : Assignments F},
            e.Le e' → con.holds e = true → con.holds e' = true :=
          fun _ => Basic.holds_mono
        rw [show p = ⟨p.result, p.nextVar, p.assignments⟩ from rfl] at hrun
        have hsat := prove_complete hmono hrun
        have hle₀ := prove_assignments_le hrun
        -- Decompose the run at the program's binds.
        simp only [compileBody] at hrun
        rw [prove_bind] at hrun
        obtain ⟨s₁, hrun₁, hrun⟩ := bind_ok hrun
        rw [prove_bind] at hrun
        obtain ⟨s₂, hrun₂, hrun⟩ := bind_ok hrun
        -- The back-fill targets the preallocated output slots, and the counter has
        -- only advanced since they were reserved — so the assign guard is satisfied.
        have hslots : (allocRange A.size B.size).toList.find?
            (s₂.nextVar ≤ ·) = none := by
          refine List.find?_eq_none.mpr fun v hv => ?_
          have hlt := (mem_allocRange hv).2
          have h₁ := prove_nextVar_le hrun₁
          have h₂ := prove_nextVar_le hrun₂
          simp only [decide_eq_true_eq]
          omega
        rw [prove_bind] at hrun
        obtain ⟨s₃, hassign, hrun⟩ := bind_ok hrun
        -- The back-fill stage: recover the mid-run output read and the slot fills.
        simp only [assignVars, prove, outputWit, hslots] at hassign
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
              -- The tail stages only extend the assignment.
              simp only [Except.ok.injEq] at hassign
              subst hassign
              have hle₃ : env₃.Le p.assignments := prove_assignments_le hrun
              have hle₂ : s₂.assignments.Le p.assignments :=
                (Assignments.le_extendPairs hext).trans hle₃
              -- The mid-run read survives to the end, so `ov` IS the decoded output.
              have hres : s₂.result = p.result := by
                rw [prove_bind] at hrun
                obtain ⟨s₄, -, hpure⟩ := bind_ok hrun
                simp only [prove, Except.ok.injEq, Proved.mk.injEq] at hpure
                exact hpure.1
              rw [hres] at hwitread
              rw [readVar_le hle₂ hwitread] at hread
              cases hread
              refine ⟨hsat, fun i hi => ?_, fun j hj => ?_⟩
              · have := hseedlook i (by omega)
                rw [Nat.zero_add] at this
                have := hle₀ i _ this
                rw [this]
                simp [hL]
              · have := hle₃ (A.size + j) _ (hextlook j (by omega))
                rw [this]
                simp [hM]
