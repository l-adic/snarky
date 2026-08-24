import Snarky.Backend.Prover

/-!
# Kimchi circuit utilities

Port of `Snarky.Circuit.Kimchi.Utils`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/Utils.purs): `mapAccumM`, the
accumulating traversal the gate gadgets thread their per-row state through.

Name map: `mapAccumM` keeps its name. The module's `verifyCircuit`/`verifyCircuitM`
are solver smoke-test `Effect` machinery with no analogue in the pure embedding and
are not ported.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS defines it as a `StateT` traversal; here it is a `forIn` loop, so the `Std.Do`
  loop rules walk it directly and it owes no composition laws of its own. The
  spelling is bind-for-bind the same traversal: one `f` call per element, outputs
  collected in element order.
- PS's `Traversable t` renders at `List` (the constraint payloads are lists).
-/

namespace Snarky.Kimchi

/-- Thread an accumulator through a monadic map (PS `mapAccumM`): one `f` call per
element in order, returning the outputs in element order and the final
accumulator. -/
def mapAccumM {m : Type u → Type v} [Monad m] {s a b : Type u}
    (f : s → a → m (b × s)) (init : s) (xs : List a) : m (List b × s) := do
  let mut acc := init
  let mut out : List b := []
  for x in xs do
    let (y, acc') ← f acc x
    out := out ++ [y]
    acc := acc'
  pure (out, acc)

/-- The state function of a `mapAccumM` run: `step` folded over the elements, the
outputs collected in order, the final accumulator. -/
def mapAccumRun {F s a b : Type} (step : ProverState F → s → a → ProverState F × (b × s)) :
    ProverState F → s → List a → ProverState F × (List b × s)
  | st, acc, [] => (st, ([], acc))
  | st, acc, x :: xs =>
    let r := step st acc x
    let rest := mapAccumRun step r.1 r.2.2 xs
    (rest.1, (r.2.1 :: rest.2.1, rest.2.2))

/-- The fold collects one output per element. -/
theorem mapAccumRun_length {F s a b : Type} (step : ProverState F → s → a → ProverState F × (b × s))
    (st : ProverState F) (acc : s) :
    ∀ xs : List a, (mapAccumRun step st acc xs).2.1.length = xs.length
  | [] => rfl
  | _ :: xs => by
    simp only [mapAccumRun, List.length_cons]
    exact congrArg (· + 1) (mapAccumRun_length step _ _ xs)

/-- The loop behind `mapAccumM`, from any collected prefix: the fold of the steps. -/
private theorem prove_mapAccumM_loop {F c s a b : Type} {holds : c → Assignments F → Bool}
    (P : ProverState F → s → Prop) (f : s → a → CircuitM F c (b × s))
    (step : ProverState F → s → a → ProverState F × (b × s)) :
    ∀ (xs : List a),
      (∀ st acc x, x ∈ xs → P st acc →
        prove holds (f acc x) st.nv st.env = .ok ((step st acc x).1.out (step st acc x).2)) →
      (∀ st acc x, x ∈ xs → P st acc → P (step st acc x).1 (step st acc x).2.2) →
      ∀ (acc : s) (out : List b) (st : ProverState F), P st acc →
        prove holds (forIn xs (⟨acc, out⟩ : MProd s (List b)) fun x r => do
            let d ← f r.fst x
            pure PUnit.unit
            pure (ForInStep.yield ⟨d.snd, r.snd ++ [d.fst]⟩)) st.nv st.env
          = .ok ((mapAccumRun step st acc xs).1.out
              ⟨(mapAccumRun step st acc xs).2.2, out ++ (mapAccumRun step st acc xs).2.1⟩) := by
  intro xs
  induction xs with
  | nil =>
    intro _ _ acc out st _
    simp only [List.forIn_nil, prove_pure, mapAccumRun, List.append_nil]
  | cons x xs ih =>
    intro hstep hP acc out st hst
    rw [List.forIn_cons]
    simp only [prove_bind, hstep st acc x (List.mem_cons_self ..) hst, Except.bind, prove_pure]
    rw [ih (fun st acc y hy h => hstep st acc y (List.mem_cons_of_mem _ hy) h)
      (fun st acc y hy h => hP st acc y (List.mem_cons_of_mem _ hy) h) _ _ _
      (hP st acc x (List.mem_cons_self ..) hst)]
    simp [mapAccumRun]

/-- `mapAccumM`'s honest run, from a per-element run equation at every state and
accumulator a step-preserved property admits: the fold of the steps, outputs in order. -/
theorem prove_mapAccumM {F c s a b : Type} {holds : c → Assignments F → Bool}
    (P : ProverState F → s → Prop) (f : s → a → CircuitM F c (b × s))
    (step : ProverState F → s → a → ProverState F × (b × s)) (xs : List a)
    (hstep : ∀ st acc x, x ∈ xs → P st acc →
      prove holds (f acc x) st.nv st.env = .ok ((step st acc x).1.out (step st acc x).2))
    (hP : ∀ st acc x, x ∈ xs → P st acc → P (step st acc x).1 (step st acc x).2.2)
    (acc : s) (st : ProverState F) (hst : P st acc) :
    prove holds (mapAccumM f acc xs) st.nv st.env
      = .ok ((mapAccumRun step st acc xs).1.out (mapAccumRun step st acc xs).2) := by
  simp only [mapAccumM]
  rw [prove_bind, prove_mapAccumM_loop P f step xs hstep hP acc [] st hst]
  rfl

end Snarky.Kimchi
