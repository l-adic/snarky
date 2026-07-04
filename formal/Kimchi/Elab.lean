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

/-! ## The wire layer

The second emission effect: *wiring*. The DSL's `assertEqual_`-style operations record union
events between cells; keygen closes each resulting equivalence class into a **cycle** of wire
pointers (kimchi's sigma — every cell points at the next cell of its class). The kernel theorem
of that translation: pointer equalities around a cycle are extensionally *class-constancy* —
which is precisely the shape `copyHolds` consumes, and (via `Circuits/Permutation.lean`) the
shape Ironwood's grand-product kernel delivers. -/

/-- Elaboration state with wiring: emitted gates plus recorded union events. -/
structure ElabSt (F : Type) where
  gates : Array (Gate F)
  links : List (Cell × Cell)

/-- The wire-aware elaboration monad. -/
abbrev ElabWM (F : Type) (α : Type) := StateM (ElabSt F) α

/-- Emit one gate row. -/
def emitW {F : Type} (g : Gate F) : ElabWM F Unit :=
  modify fun st => { st with gates := st.gates.push g }

/-- Record a union event: the two cells must carry equal values (an `assertEqual_`). -/
def wireW {F : Type} (a b : Cell) : ElabWM F Unit :=
  modify fun st => { st with links := (a, b) :: st.links }

/-- A witness respects the recorded links. This is the *specification* the wiring means. -/
def LinksHold {F : Type} [Zero F] (links : List (Cell × Cell)) (w : Witness F) : Prop :=
  ∀ p ∈ links, w.cell p.1 = w.cell p.2

/-- A wire map realizes a class as a cycle: each listed cell points at the next, wrapping. -/
def CycleWires (wireOf : Cell → Cell) (l : List Cell) : Prop :=
  ∀ i (hi : i < l.length),
    wireOf l[i] = l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))

/-- **The cycle-wiring kernel.** If a witness satisfies the pointer equalities of a cycle
    (`w.cell c = w.cell (wireOf c)` along the class), then the class is *constant*: any two
    of its cells agree. The step from kimchi's sigma representation to the equalities
    `copyHolds` states — and the inverse direction is immediate, so cycles lose nothing. -/
theorem class_const_of_cycle {F : Type} [Zero F] (w : Witness F) (wireOf : Cell → Cell)
    (l : List Cell) (hcyc : CycleWires wireOf l)
    (hptr : ∀ c ∈ l, w.cell c = w.cell (wireOf c)) :
    ∀ a ∈ l, ∀ b ∈ l, w.cell a = w.cell b := by
  -- every cell equals the head, by walking the pointers forward
  have aux : ∀ i (hi : i < l.length), w.cell l[0] = w.cell l[i] := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ n ih =>
        intro hi
        have hn : n < l.length := by omega
        have hstep := hptr l[n] (l.getElem_mem hn)
        rw [hcyc n hn] at hstep
        simp only [Nat.mod_eq_of_lt hi] at hstep
        exact (ih hn).trans hstep
  intro a ha b hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  exact (aux i hi).symm.trans (aux j hj)

/-- The converse: class-constancy trivially satisfies the pointer equalities of *any* cycle
    through the class — so realizing links as cycles is a lossless encoding. -/
theorem cycle_of_class_const {F : Type} [Zero F] (w : Witness F) (wireOf : Cell → Cell)
    (l : List Cell) (hcyc : CycleWires wireOf l)
    (hconst : ∀ a ∈ l, ∀ b ∈ l, w.cell a = w.cell b) :
    ∀ c ∈ l, w.cell c = w.cell (wireOf c) := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  rw [hcyc i hi]
  exact hconst l[i] (l.getElem_mem hi)
    (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)))
    (l.getElem_mem (Nat.mod_lt _ (by omega)))

/-- **The wiring semantics, end to end.** For classes that cover the recorded links (each link's
    endpoints share a class) and are realized as cycles by the circuit's wire map, pointer
    satisfaction implies the links' specification `LinksHold` — the DSL-level meaning of the
    union events is recovered from the sigma encoding. -/
theorem linksHold_of_cycles {F : Type} [Zero F] (w : Witness F) (wireOf : Cell → Cell)
    (classes : List (List Cell)) (links : List (Cell × Cell))
    (hcycles : ∀ l ∈ classes, CycleWires wireOf l)
    (hcover : ∀ p ∈ links, ∃ l ∈ classes, p.1 ∈ l ∧ p.2 ∈ l)
    (hptr : ∀ l ∈ classes, ∀ c ∈ l, w.cell c = w.cell (wireOf c)) :
    LinksHold links w := by
  intro p hp
  obtain ⟨l, hl, h1, h2⟩ := hcover p hp
  exact class_const_of_cycle w wireOf l (hcycles l hl) (hptr l hl) p.1 h1 p.2 h2

end Kimchi.Circuit.Elab
