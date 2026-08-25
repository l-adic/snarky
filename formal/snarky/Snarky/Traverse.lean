import Snarky.Prover

/-!
# Traversing a vector in the circuit monad

`zipWithVecM` runs a circuit at every index of two equal-length vectors and collects the
results; `mapAccumM` walks a list threading an accumulator. Entries are visited in index order, which is the order their rows are emitted in.

The laws are the loop's: a per-index soundness spec, and a per-index completeness law
whose two monotonicity hypotheses stand in for a loop invariant, since the prover's table
grows under each entry.
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

attribute [irreducible] zipWithVecM

end Snarky
