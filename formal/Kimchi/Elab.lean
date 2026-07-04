import Kimchi.Circuits.PoseidonStep

/-!
# Shallow elaboration semantics: the emission monad

The PureScript circuit DSL builds a circuit by *emitting* gate rows from a state monad. This file
models that emission fragment in Lean — `ElabM` is a state monad over the gate array, `emit`
appends a row — and proves the first **generic seam-closure theorem**: elaborating the Poseidon
chain gadget produces `posCircuit m coeffs` *for every* `m`, replacing the per-fixture empirical
`CheckReconstruction` tie with a theorem about the elaborator itself.

Two structural lemmas make elaborations compose the way circuits do:

* `elab_gates_append` — an elaboration is *append-only*: its effect from any start state is
  `gs ++ (its own emission)`. Emission is context-free, the property that lets blocks be
  reasoned about independently;
* `elab_seq` — sequencing elaborations concatenates their emissions, which is exactly
  `Circuit.append` on the circuit side (`elabPoseidon_seq` instantiates this: two chained
  Poseidon blocks elaborate to the `append` of their circuits).

Honest scope: this is the *gate-emission* fragment (kinds, coefficients, row order). The wire /
union-find layer — where copy constraints come from — is the next semantic layer; the CoreFn
interpreter (`Kimchi/CoreFn.lean`) is the executable path to validating this model against the
real compiled elaborator, closing the remaining eyeball gap per combinator.
-/

namespace Kimchi.Circuit.Elab

open Kimchi.Circuit

/-! ## The emission monad -/

/-- The elaboration monad: state is the emitted gate array. -/
abbrev ElabM (F : Type) (α : Type) := StateM (Array (Gate F)) α

/-- Emit one gate row. -/
def emit {F : Type} (g : Gate F) : ElabM F Unit :=
  modify (·.push g)

/-- The gates an elaboration produces from a start state. -/
def gatesFrom {F : Type} (e : ElabM F Unit) (gs : Array (Gate F)) : Array (Gate F) :=
  (e.run gs).2

/-- Run an elaboration from the empty state as a circuit (no public rows — blocks are embedded
    by the host, as in `Satisfies.of_embed`). -/
def elabCircuit {F : Type} (e : ElabM F Unit) : Circuit F :=
  { publicInputSize := 0, gates := gatesFrom e #[] }

/-! ## The Poseidon chain gadget -/

variable {F : Type} [CommRing F] [DecidableEq F]

open Kimchi.Circuit.Poseidon

/-- `pure` emits nothing. -/
@[simp] theorem gatesFrom_pure (gs : Array (Gate F)) :
    gatesFrom (pure () : ElabM F Unit) gs = gs := rfl

/-- `bind` threads the emitted gates. -/
@[simp] theorem gatesFrom_bind (a b : ElabM F Unit) (gs : Array (Gate F)) :
    gatesFrom (do a; b) gs = gatesFrom b (gatesFrom a gs) := rfl

/-- `emit` appends one row. -/
@[simp] theorem gatesFrom_emit (g : Gate F) (gs : Array (Gate F)) :
    gatesFrom (emit g) gs = gs.push g := rfl

/-- The Poseidon chain gadget's emission: one `Poseidon` row per round, in round order —
    the Lean model of the PS gadget's fold over rounds. -/
def elabPoseidon (coeffs : ℕ → Array F) : ℕ → ElabM F Unit
  | 0 => pure ()
  | m + 1 => do
      elabPoseidon coeffs m
      emit (posGate (coeffs m))

/-! ## Append-only emission and sequencing -/

/-- Elaborations are **append-only**: from any start state, the result is the start state
    followed by the elaboration's own (context-free) emission. -/
theorem elab_gates_append (coeffs : ℕ → Array F) (m : ℕ) (gs : Array (Gate F)) :
    gatesFrom (elabPoseidon coeffs m) gs
      = gs ++ gatesFrom (elabPoseidon coeffs m) #[] := by
  induction m generalizing gs with
  | zero => simp [elabPoseidon]
  | succ n ih =>
      rw [show elabPoseidon coeffs (n + 1)
          = (do elabPoseidon coeffs n; emit (posGate (coeffs n))) from rfl]
      rw [gatesFrom_bind, gatesFrom_bind, gatesFrom_emit, gatesFrom_emit, ih gs, ih #[],
        Array.push_eq_append_singleton, Array.push_eq_append_singleton, Array.append_assoc]

/-- **Sequencing = concatenation**: running one elaboration after another emits the
    concatenation of their emissions — the monadic image of `Circuit.append`. -/
theorem elab_seq (coeffs coeffs' : ℕ → Array F) (m m' : ℕ) :
    gatesFrom (do elabPoseidon coeffs m; elabPoseidon coeffs' m') #[]
      = gatesFrom (elabPoseidon coeffs m) #[] ++ gatesFrom (elabPoseidon coeffs' m') #[] := by
  rw [gatesFrom_bind, elab_gates_append]

/-! ## The seam-closure theorem -/

/-- **Elaboration = reconstruction, for every `m`.** The Poseidon chain gadget's emission is
    exactly the reconstructed circuit `posCircuit m coeffs` — the generic replacement for the
    per-fixture empirical reconstruction check (which remains as the tie to the *real* compiled
    artifact; see `Kimchi/CoreFn.lean` for the path to closing that too). -/
theorem elabPoseidon_eq_posCircuit (coeffs : ℕ → Array F) (m : ℕ) :
    elabCircuit (elabPoseidon coeffs m) = Kimchi.Circuit.Poseidon.posCircuit m coeffs := by
  unfold elabCircuit Kimchi.Circuit.Poseidon.posCircuit
  congr 1
  induction m with
  | zero => rfl
  | succ n ih =>
      have step : gatesFrom (elabPoseidon coeffs (n + 1)) #[]
          = (gatesFrom (elabPoseidon coeffs n) #[]).push
              (Kimchi.Circuit.Poseidon.posGate (coeffs n)) := by
        show gatesFrom (do elabPoseidon coeffs n; emit (posGate (coeffs n))) #[] = _
        rw [gatesFrom_bind, gatesFrom_emit]
      rw [step, ih, Array.ofFn_succ]
      rfl

/-- Two chained Poseidon blocks elaborate to the `Circuit.append` of their circuits (with the
    block convention `publicInputSize = 0`): the DSL's sequencing *is* the append combinator. -/
theorem elabPoseidon_seq (coeffs coeffs' : ℕ → Array F) (m m' : ℕ) :
    elabCircuit (do elabPoseidon coeffs m; elabPoseidon coeffs' m')
      = (Kimchi.Circuit.Poseidon.posCircuit m coeffs).append
          (Kimchi.Circuit.Poseidon.posCircuit m' coeffs').gates := by
  unfold elabCircuit Circuit.append
  have h1 := elabPoseidon_eq_posCircuit (F := F) coeffs m
  have h2 := elabPoseidon_eq_posCircuit (F := F) coeffs' m'
  have g1 : gatesFrom (elabPoseidon coeffs m) #[]
      = (Kimchi.Circuit.Poseidon.posCircuit m coeffs).gates := congrArg Circuit.gates h1
  have g2 : gatesFrom (elabPoseidon coeffs' m') #[]
      = (Kimchi.Circuit.Poseidon.posCircuit m' coeffs').gates := congrArg Circuit.gates h2
  simp only [elab_seq, g1, g2]
  rfl

end Kimchi.Circuit.Elab
