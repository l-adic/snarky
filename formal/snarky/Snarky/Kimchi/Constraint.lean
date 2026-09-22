import Snarky.Kimchi.Constraint.GenericPlonk
import Snarky.Kimchi.Constraint.AddComplete
import Snarky.Kimchi.Constraint.EndoScalar
import Snarky.Kimchi.Constraint.VarBaseMul
import Snarky.Kimchi.Constraint.EndoMul
import Snarky.Kimchi.Constraint.Poseidon

/-!
# The kimchi constraint type and its reduction

The backend's constraint sum `KimchiConstraint`, the emitted-gate sum `KimchiGate`
with its row dispatch, the `BasicSystem` instance carrying the DSL's constructors into
that sum, and the one reduction `KimchiConstraint.reduce` taking a constraint to its
gate. Transcribed from packages/snarky-kimchi/src/Snarky/Constraint/Kimchi.purs.

Each arm of the reduction calls its gate's own reducer and wraps the emitted rows in
the matching `KimchiGate` arm. Two arms break that pattern. A `.basic` constraint
emits through the batching queue and so wraps as `.noOp`, carrying no rows of its own;
`.pad` has no gate module behind it, so `reducePad` pins its seven operands here and
emits one degenerate generic row.

The reduction is polymorphic in the reduction monad (`PlonkReductionM`), so the
builder and the prover run it unchanged. It therefore borrows and returns the one
shared variable counter of `Constraint/Reduction.lean`: reduction-internal variables
are numbered between user variables in program order, and that interleaving is fixture
bytes. Run in the prover it tests nothing — a kimchi constraint emits rows, not a
checkable predicate — so nothing here validates a witness.

The Poseidon parameters ride in the constraint payload (see `Constraint/Poseidon.lean`),
so the reduction takes no parameter for them.
-/

namespace Snarky.Kimchi

open Snarky

/-- The kimchi backend's constraint type: the DSL's `Basic` vocabulary, one arm per
modelled gate, and the padding row. -/
inductive KimchiConstraint (F : Type u) where
  /-- A `Basic` constraint, reduced through the generic-gate fan-out. -/
  | basic (c : Basic F)
  /-- A complete-addition constraint. -/
  | addComplete (c : AddComplete F)
  /-- A Poseidon block constraint. -/
  | poseidon (c : PoseidonConstraint F)
  /-- A variable-base scalar-multiplication constraint. -/
  | varBaseMul (c : VarBaseMul F)
  /-- A challenge-decomposition constraint. -/
  | endoScalar (c : EndoScalar F)
  /-- An endomorphism-optimized scalar-multiplication constraint. -/
  | endoMul (c : EndoMul F)
  /-- Pad the circuit by one row: the degenerate generic row of `mkPadRow`, over the
  seven permutable cells. Its use is to push a row count past a domain boundary; no
  Lean circuit constructs it, and it reads vacuously. -/
  | pad (vs : Vector (FVar F) 7)

/-- What one constraint reduces to: the per-gate row carriers, or nothing (a `Basic`
constraint emits through the batching queue instead). -/
inductive KimchiGate (F : Type u) where
  /-- One packed generic row. -/
  | plonk (r : Rows F)
  /-- One complete-addition row. -/
  | addComplete (r : Rows F)
  /-- A Poseidon block's rows. -/
  | poseidon (rs : List (KimchiRow F))
  /-- A scalar multiplication's row pairs. -/
  | varBaseMul (rs : List (KimchiRow F × KimchiRow F))
  /-- A challenge decomposition's rows. -/
  | endoScalar (rs : List (KimchiRow F))
  /-- An endomorphism multiplication's rows. -/
  | endoMul (rs : List (KimchiRow F))
  /-- No direct rows (a reduced `Basic` constraint). -/
  | noOp

/-- Row dispatch: the rows an emitted gate contributes, none for `.noOp`. -/
instance : ToKimchiRows F (KimchiGate F) where
  toKimchiRows
    | .plonk r => toKimchiRows r
    | .addComplete r => toKimchiRows r
    | .poseidon rs => toKimchiRows rs
    | .varBaseMul rs => toKimchiRows rs
    | .endoScalar rs => toKimchiRows rs
    | .endoMul rs => toKimchiRows rs
    | .noOp => []

/-- The DSL's constraint constructors, into the kimchi sum: each lands in `.basic`. -/
instance : BasicSystem F (KimchiConstraint F) where
  r1cs l r o := .basic (.r1cs l r o)
  equal a b := .basic (.equal a b)
  square a c := .basic (.square a c)
  boolean x := .basic (.boolean x)

variable {F : Type} {m : Type → Type}

/-- Pin the padding row's seven operands to variables and wire them into one row. -/
private def reducePad [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] (vs : Vector (FVar F) 7) : m (Rows F) := do
  let v0 ← reduceToVariable vs[0]
  let v1 ← reduceToVariable vs[1]
  let v2 ← reduceToVariable vs[2]
  let v3 ← reduceToVariable vs[3]
  let v4 ← reduceToVariable vs[4]
  let v5 ← reduceToVariable vs[5]
  let v6 ← reduceToVariable vs[6]
  pure (mkPadRow ⟨⟨[v0, v1, v2, v3, v4, v5, v6]⟩, by simp⟩)

/-- Reduce a constraint through its gate's reducer and wrap the rows. A `.basic`
constraint emits into the batching queue instead and wraps as `.noOp`. -/
def KimchiConstraint.reduce [Add F] [Mul F] [Sub F] [Zero F] [One F] [Neg F]
    [DecidableEq F] [Monad m] [PlonkReductionM F m] :
    KimchiConstraint F → m (KimchiGate F)
  | .basic c => do
    Snarky.Kimchi.reduce c
    pure .noOp
  | .addComplete c => .addComplete <$> c.reduce
  | .poseidon c => .poseidon <$> c.reduce
  | .varBaseMul c => .varBaseMul <$> VarBaseMul.reduce c
  | .endoScalar c => .endoScalar <$> EndoScalar.reduce c
  | .endoMul c => .endoMul <$> c.reduce
  | .pad vs => .plonk <$> reducePad vs

/- PORT: the ops record and its seam laws are OFF.

There is no backend-ops indirection to plug into: `build` and `prove` are the two
interpreters directly, with no per-constraint hook a backend can supply, so
`BackendOps`, `Lockstep` and `ProveExtends` have nothing to instantiate against, and
the `Seam` vocabulary the proofs below consume has no definition.

/-! ## The backend ops (PS's two instances, as one record) -/

/-- The kimchi backend's ops (the PS `CompileCircuit`/`SolveCircuit` instances):
each constraint runs the one dispatch — in the builder for `appendConstraint`
(emitting first the batched generic rows the reduction flushed, then the wrapped
gate), in the prover for `proveConstraint` (extending the table, checking nothing —
the PS production semantics; see the module docstring) — and `finalize` flushes the
odd queued constraint into one more packed row. -/
def kimchiOps [Add F] [Mul F] [Sub F] [Zero F] [One F] [Neg F] [Div F]
    [DecidableEq F] :
    BackendOps F (KimchiGate F) (KimchiConstraint F) (AuxState F) where
  appendConstraint con n aux :=
    let red := reduceAsBuilder n aux (KimchiConstraint.reduce con)
    (red.2.1.map .plonk ++ [red.1], red.2.2.1, red.2.2.2)
  proveConstraint con nv env :=
    match reduceAsProver ⟨nv, env⟩ (KimchiConstraint.reduce con) with
    | .error e => .error e
    | .ok (_, s') => .ok (s'.nextVariable, s'.assignments)
  finalize aux :=
    ((finalizeGateQueue aux.queuedGenericGate).map .plonk,
     { aux with queuedGenericGate := none })

/-! ## Seam coherence: the dispatch and the ops-record discharge -/

/-- `reducePad` is a seam: seven pinned operands, one row. -/
private theorem reducePad_seam [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F]
    [Neg F] [DecidableEq F] (vs : Vector (FVar F) 7) :
    Seam (reducePad (m := PlonkBuilder F) vs) (reducePad (m := PlonkProver F) vs) := by
  unfold reducePad
  repeat first
    | exact Seam.pure _
    | refine Seam.bind (reduceToVariable_seam _) fun _ => ?_

/-- The one shared dispatch runs its two seams in lockstep: `KimchiConstraint.reduce`
is a seam, arm by arm from the per-gate walks. -/
theorem KimchiConstraint.reduce_seam [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F]
    [Neg F] [DecidableEq F] (con : KimchiConstraint F) :
    Seam (KimchiConstraint.reduce (m := PlonkBuilder F) con)
      (KimchiConstraint.reduce (m := PlonkProver F) con) := by
  rcases con with c | c | c | c | c | c | vs <;> simp only [KimchiConstraint.reduce]
  · refine Seam.bind (_root_.Snarky.Kimchi.reduce_seam c) fun _ => ?_
    exact Seam.pure _
  · exact Seam.map _ (AddComplete.reduce_seam c)
  · exact Seam.map _ (PoseidonConstraint.reduce_seam c)
  · exact Seam.map _ (VarBaseMul.reduce_seam c)
  · exact Seam.map _ (EndoScalar.reduce_seam c)
  · exact Seam.map _ (EndoMul.reduce_seam c)
  · exact Seam.map _ (reducePad_seam vs)

/-- The kimchi backend's per-constraint counter lockstep: a successful prover seam
pins the builder seam's counter, for every auxiliary state — the two instantiations
of the one dispatch advance the shared counter identically
(`KimchiConstraint.reduce_seam`). -/
theorem kimchiOps_lockstep [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F] [Neg F]
    [DecidableEq F] : (kimchiOps (F := F)).Lockstep := by
  intro con n env n' env' aux h
  simp only [kimchiOps] at h ⊢
  rcases hp : reduceAsProver ⟨n, env⟩ (KimchiConstraint.reduce con) with e | ⟨a, sP'⟩ <;>
    rw [hp] at h
  · cases h
  · obtain ⟨rfl, -⟩ : sP'.nextVariable = n' ∧ sP'.assignments = env' := by
      simpa using h
    obtain ⟨-, hn, -, -⟩ := KimchiConstraint.reduce_seam con hp ⟨[], n, aux⟩ rfl
    exact hn

/-- The kimchi backend's per-constraint prover extension: a successful prover seam
only extends the witness table — the guarded write — and never retreats the
counter. -/
theorem kimchiOps_proveExtends [Add F] [Mul F] [Sub F] [Div F] [Zero F] [One F]
    [Neg F] [DecidableEq F] : (kimchiOps (F := F)).ProveExtends := by
  intro con n env n' env' h
  simp only [kimchiOps] at h
  rcases hp : reduceAsProver ⟨n, env⟩ (KimchiConstraint.reduce con) with e | ⟨a, sP'⟩ <;>
    rw [hp] at h
  · cases h
  · obtain ⟨rfl, rfl⟩ : sP'.nextVariable = n' ∧ sP'.assignments = env' := by
      simpa using h
    obtain ⟨-, -, hle, hmono⟩ :=
      KimchiConstraint.reduce_seam con hp ⟨[], n, initialAuxState⟩ rfl
    exact ⟨hle, hmono⟩

end Snarky.Kimchi
-/
