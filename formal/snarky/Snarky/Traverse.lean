import Snarky.Prover

/-!
# Traversing a vector in the circuit monad

Two loops. `zipWithVecM` runs a circuit at every index of two equal-length vectors and
collects the results; `mapAccumM` walks a list threading an accumulator. Both visit their
entries in order, which is the order the rows are emitted in.

Each carries its laws, so a gadget that loops writes the step and inherits the loop: a
soundness spec carrying a per-step relation along the whole trace, and a completeness law
whose monotonicity hypotheses stand in for a loop invariant — and which delivers every
step's grant AT THE FINAL TABLE, where the row a ladder emits after its loop is judged.
That transport is the loop's, done once, rather than each ladder's.
-/

namespace Snarky

set_option mvcgen.warning false

variable {F c : Type}

/-- `zipWithVecM`'s recursion, over index functions. -/
private def zipGo {α β γ : Type} (f : α → β → CircuitM F c γ) :
    ∀ (n : Nat), (Fin n → α) → (Fin n → β) → CircuitM F c (Vector γ n)
  | 0, _, _ => pure #v[]
  | n + 1, xs, ys => do
    let init ← zipGo f n (fun i => xs i.castSucc) (fun i => ys i.castSucc)
    let last ← f (xs (Fin.last n)) (ys (Fin.last n))
    pure (init.push last)

/-- Run `f` at every index of two vectors, in index order, collecting the results. -/
def zipWithVecM {α β γ : Type} {n : Nat} (f : α → β → CircuitM F c γ) (xs : Vector α n)
    (ys : Vector β n) : CircuitM F c (Vector γ n) :=
  zipGo f n (fun i => xs[i]) (fun i => ys[i])

open Std.Do in
private theorem zipGo_spec {V : Valuation F} {α β γ : Type} [ConstraintHolds F c]
    (f : α → β → CircuitM F (Builder V c) γ) :
    ∀ (n : Nat) (xs : Fin n → α) (ys : Fin n → β) (post : Fin n → γ → Prop),
      (∀ i : Fin n, ⦃⌜True⌝⦄ f (xs i) (ys i) ⦃⇓ r _ => ⌜post i r⌝⦄) →
      ⦃⌜True⌝⦄ zipGo f n xs ys ⦃⇓ rs _ => ⌜∀ i : Fin n, post i rs[i]⌝⦄
  | 0, _, _, _, _ => by
    intro _ _ _ i
    exact i.elim0
  | n + 1, xs, ys, post, hf => by
    have hlast := hf (Fin.last n)
    have hinit := zipGo_spec f n (fun i => xs i.castSucc) (fun i => ys i.castSucc)
      (fun i => post i.castSucc) (fun i => hf i.castSucc)
    simp only [zipGo]
    mvcgen [hinit, hlast]
    rename_i init _ hinit' last _ hlast'
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hlast'
    · simpa using hinit' j

open Std.Do in
/-- Every entry's postcondition holds of the collected result. -/
theorem zipWithVecM_spec {V : Valuation F} {α β γ : Type} [ConstraintHolds F c] {n : Nat}
    (f : α → β → CircuitM F (Builder V c) γ) (xs : Vector α n) (ys : Vector β n)
    (post : Fin n → γ → Prop)
    (hf : ∀ i : Fin n, ⦃⌜True⌝⦄ f xs[i] ys[i] ⦃⇓ r _ => ⌜post i r⌝⦄) :
    ⦃⌜True⌝⦄ zipWithVecM f xs ys ⦃⇓ rs _ => ⌜∀ i : Fin n, post i rs[i]⌝⦄ :=
  zipGo_spec f n _ _ post hf

section Complete

variable [Zero F] [ConstraintHolds F c] {α β γ : Type}

private theorem zipGo_complete (f : α → β → CircuitM F c γ) (pre : ProverState F → Prop)
    (hpre : ∀ {st st' : ProverState F}, st.nv ≤ st'.nv → st.env.Le st'.env → pre st → pre st') :
    ∀ (n : Nat) (xs : Fin n → α) (ys : Fin n → β)
      (post : Fin n → γ → ProverState F → Prop),
      (∀ (i : Fin n) {a : γ} {st st' : ProverState F}, st.nv ≤ st'.nv → st.env.Le st'.env →
        post i a st → post i a st') →
      (∀ i : Fin n, Complete pre (f (xs i) (ys i)) (post i)) →
      Complete pre (zipGo f n xs ys) (fun rs st' => ∀ i : Fin n, post i rs[i] st')
  | 0, _, _, _, _, _ => fun st hst =>
    ⟨#v[], st, rfl, fun _ _ => by simp [Sat, build, zipGo], fun i => i.elim0⟩
  | n + 1, xs, ys, post, hmono, hf => by
    intro st hst
    obtain ⟨init, st₁, hrunI, hsatI, hpostI⟩ :=
      zipGo_complete f pre hpre n (fun i => xs i.castSucc) (fun i => ys i.castSucc)
        (fun i => post i.castSucc) (fun i => hmono i.castSucc) (fun i => hf i.castSucc)
        st hst
    obtain ⟨last, st₂, hrunL, hsatL, hpostL⟩ :=
      hf (Fin.last n) st₁ (hpre hrunI.nv_le hrunI.le hst)
    refine ⟨init.push last, st₂, hrunI.bind (hrunL.bind rfl), fun hnv hle =>
      Sat.bind hrunI (hsatI (Nat.le_trans hrunL.nv_le hnv) (hrunL.le.trans hle))
        (Sat.bind hrunL (hsatL hnv hle) Sat.pure), fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hpostL
    · simpa using hmono _ hrunL.nv_le hrunL.le (hpostI j)

/-- Every entry's completeness composes into the loop's, given that the precondition and
the entries' postconditions transport along the table's growth. -/
theorem zipWithVecM_complete {n : Nat} (f : α → β → CircuitM F c γ) (xs : Vector α n)
    (ys : Vector β n) (pre : ProverState F → Prop) (post : Fin n → γ → ProverState F → Prop)
    (hpre : ∀ {st st' : ProverState F}, st.nv ≤ st'.nv → st.env.Le st'.env → pre st → pre st')
    (hpost : ∀ (i : Fin n) {a : γ} {st st' : ProverState F}, st.nv ≤ st'.nv →
      st.env.Le st'.env → post i a st → post i a st')
    (hf : ∀ i : Fin n, Complete pre (f xs[i] ys[i]) (post i)) :
    Complete pre (zipWithVecM f xs ys) (fun rs st' => ∀ i : Fin n, post i rs[i] st') :=
  zipGo_complete f pre hpre n _ _ post hpost hf

end Complete

/-! ## Accumulating -/

/-- Map with an accumulator, in list order: each element is run against the state the
previous one left, and the outputs are collected in order. Generic in the monad —
the reduction's two carriers use it as well as the circuit monad. -/
def mapAccumM {m : Type u → Type v} [Monad m] {s α β : Type u} (f : s → α → m (β × s))
    (init : s) : List α → m (List β × s)
  | [] => pure ([], init)
  | x :: xs => do
    let (y, acc) ← f init x
    let (ys, acc') ← mapAccumM f acc xs
    pure (y :: ys, acc')

/-- The trace of an accumulating traversal: each output is related to the input it came
from and to the states either side of it, and the states thread from the initial one to
the final. This is what a loop's caller learns — the per-step relation, chained. -/
def Chain {s α β : Type} (R : s → α → β → s → Prop) : s → List α → List β → s → Prop
  | init, [], ys, fin => ys = [] ∧ init = fin
  | init, x :: xs, ys, fin =>
    ∃ (y : β) (ys' : List β) (mid : s),
      ys = y :: ys' ∧ R init x y mid ∧ Chain R mid xs ys' fin

/-- A trace with no outputs traversed no inputs: the loop ran zero steps. -/
theorem Chain.of_nil_out {s α β : Type} {R : s → α → β → s → Prop} :
    ∀ {init fin : s} {xs : List α}, Chain R init xs [] fin → xs = [] ∧ init = fin
  | _, _, [], h => ⟨rfl, h.2⟩
  | _, _, _ :: _, h => by
    obtain ⟨y, ys', -, heq, -, -⟩ := h
    exact nomatch heq

open Std.Do in
/-- `mapAccumM`'s soundness: a per-step relation, established by the step's own spec,
holds along the whole trace. The caller supplies `R` and gets the chain — no bespoke
loop invariant per gadget. -/
theorem mapAccumM_spec {V : Valuation F} {s α β : Type} [ConstraintHolds F c]
    (f : s → α → CircuitM F (Builder V c) (β × s)) (R : s → α → β → s → Prop)
    (hstep : ∀ (st : s) (x : α), ⦃⌜True⌝⦄ f st x ⦃⇓ p _ => ⌜R st x p.1 p.2⌝⦄) :
    ∀ (init : s) (xs : List α),
      ⦃⌜True⌝⦄ mapAccumM f init xs ⦃⇓ p _ => ⌜Chain R init xs p.1 p.2⌝⦄
  | init, [] => by
    intro nv _ _
    exact ⟨rfl, rfl⟩
  | init, x :: xs => by
    have hx := hstep init x
    have hrest := fun (acc : s) => mapAccumM_spec f R hstep acc xs
    simp only [mapAccumM]
    mvcgen [hx, hrest]
    rename_i p _ hp q _ hq
    exact ⟨p.1, q.1, p.2, rfl, hp, hq⟩

/-- The trace, read at one table: every step's grant evaluated at the same state,
rather than at the state that step ended in. This is what a ladder's caller needs —
the row it emits after the loop is judged at the end, so the loop's facts must arrive
there. `mapAccumM_complete` does that transport once. -/
def ChainAt {s α β : Type} (out : s → α → β → s → ProverState F → Prop)
    (stf : ProverState F) : s → List α → List β → s → Prop
  | init, [], ys, fin => ys = [] ∧ init = fin
  | init, x :: xs, ys, fin =>
    ∃ (y : β) (ys' : List β) (mid : s),
      ys = y :: ys' ∧ out init x y mid stf ∧ ChainAt out stf mid xs ys' fin

/-- `mapAccumM`'s completeness: a step's law, an accumulator invariant and a grant that
survives the table's growth compose into the whole ladder's. The caller writes the step
and gets the loop — including every step's grant at the final table, which is where the
emitted row is judged. -/
theorem mapAccumM_complete [Zero F] [ConstraintHolds F c] {s α β : Type}
    (f : s → α → CircuitM F c (β × s)) (P : α → Prop) (inv : s → ProverState F → Prop)
    (out : s → α → β → s → ProverState F → Prop)
    (hinv : ∀ (acc : s) {st st' : ProverState F}, st.nv ≤ st'.nv → st.env.Le st'.env →
      inv acc st → inv acc st')
    (hout : ∀ (acc : s) (x : α) (y : β) (acc' : s) {st st' : ProverState F},
      st.nv ≤ st'.nv → st.env.Le st'.env → out acc x y acc' st → out acc x y acc' st')
    (hstep : ∀ (acc : s) (x : α), P x →
      Complete (inv acc) (f acc x) (fun p st' => inv p.2 st' ∧ out acc x p.1 p.2 st')) :
    ∀ (init : s) (xs : List α), (∀ x ∈ xs, P x) →
      Complete (inv init) (mapAccumM f init xs)
        (fun p st' => inv p.2 st' ∧ ChainAt out st' init xs p.1 p.2)
  | init, [], _ => fun st hst =>
    ⟨([], init), st, rfl, fun _ _ => by simp [Sat, build, mapAccumM], hst, rfl, rfl⟩
  | init, x :: xs, hP => by
    intro st hst
    obtain ⟨p, st₁, hrun₁, hsat₁, hinv₁, hout₁⟩ := hstep init x (hP x (by simp)) st hst
    obtain ⟨q, st₂, hrun₂, hsat₂, hinv₂, hchain⟩ :=
      mapAccumM_complete f P inv out hinv hout hstep p.2 xs
        (fun y hy => hP y (by simp [hy])) st₁ hinv₁
    refine ⟨(p.1 :: q.1, q.2), st₂, ?_, ?_, hinv₂,
      ⟨p.1, q.1, p.2, rfl, hout _ _ _ _ hrun₂.nv_le hrun₂.le hout₁, hchain⟩⟩
    · exact hrun₁.bind (hrun₂.bind rfl)
    · intro stf hnv hle
      exact Sat.bind hrun₁ (hsat₁ (Nat.le_trans hrun₂.nv_le hnv) (hrun₂.le.trans hle))
        (Sat.bind hrun₂ (hsat₂ hnv hle) Sat.pure)

attribute [irreducible] zipWithVecM

end Snarky
