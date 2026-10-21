import Snarky.Prover
import Snarky.Prover.WP
import Mathlib.Data.List.Chain

/-!
# Traversing a vector in the circuit monad

Two loops. `zipWithVecM` runs a circuit at every index of two equal-length vectors and
collects the results; `mapAccumM` walks a list threading an accumulator. Both visit their
entries in order, which is the order the rows are emitted in.

Each carries its soundness law, so a gadget that loops writes the step and inherits the loop: a
spec carrying a per-step relation along the whole trace. The completeness laws at the prover's
reading are the generic traversal contracts in `Snarky.Prover.VCGen`.
-/

namespace Snarky

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

open Std.WP in
private theorem zipGo_spec {V : Valuation F} {α β γ : Type} [ConstraintHolds F c]
    (f : α → β → CircuitM F (Builder V c) γ) :
    ∀ (n : Nat) (xs : Fin n → α) (ys : Fin n → β) (post : Fin n → γ → Prop),
      (∀ i : Fin n, ⦃fun _ => True⦄ f (xs i) (ys i) ⦃fun r _ => post i r⦄) →
      ⦃fun _ => True⦄ zipGo f n xs ys ⦃fun rs _ => ∀ i : Fin n, post i rs[i]⦄
  | 0, _, _, _, _ => ⟨fun _ _ _ i => i.elim0⟩
  | n + 1, xs, ys, post, hf => by
    have hlast := hf (Fin.last n)
    have hinit := zipGo_spec f n (fun i => xs i.castSucc) (fun i => ys i.castSucc)
      (fun i => post i.castSucc) (fun i => hf i.castSucc)
    simp only [zipGo]
    vcgen [hinit, hlast]
    rename_i hinit' _ hlast' i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hlast'
    · simpa using hinit' j

open Std.WP in
/-- Every entry's postcondition holds of the collected result. -/
theorem zipWithVecM_spec {V : Valuation F} {α β γ : Type} [ConstraintHolds F c] {n : Nat}
    (f : α → β → CircuitM F (Builder V c) γ) (xs : Vector α n) (ys : Vector β n)
    (post : Fin n → γ → Prop)
    (hf : ∀ i : Fin n, ⦃fun _ => True⦄ f xs[i] ys[i] ⦃fun r _ => post i r⦄) :
    ⦃fun _ => True⦄ zipWithVecM f xs ys ⦃fun rs _ => ∀ i : Fin n, post i rs[i]⦄ :=
  zipGo_spec f n _ _ post hf

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

/-- A trace whose steps record the states they read and wrote is its outputs' facts, their
links, and its ends. -/
theorem chain_iff {s α β : Type} {R : s → α → β → s → Prop} (inp out : β → s)
    (Q : α → β → Prop) (hR : ∀ a x y b, R a x y b ↔ inp y = a ∧ out y = b ∧ Q x y) :
    ∀ {init fin : s} {xs : List α} {ys : List β},
      Chain R init xs ys fin ↔
        List.Forall₂ Q xs ys ∧ ys.IsChain (fun y y' => inp y' = out y) ∧
          (∀ y ∈ ys.head?, inp y = init) ∧ (ys.getLast?.map out).getD init = fin
  | init, fin, [], ys => by
    cases ys with
    | nil => simp [Chain]
    | cons y ys => simp [Chain]
  | init, fin, x :: xs, ys => by
    cases ys with
    | nil => simp [Chain]
    | cons y ys =>
      have ih := @chain_iff s α β R inp out Q hR (out y) fin xs ys
      simp only [Chain, List.cons.injEq, hR]
      constructor
      · rintro ⟨y', ys', mid, ⟨rfl, rfl⟩, ⟨hin, rfl, hq⟩, hrest⟩
        obtain ⟨hF, hC, hH, hL⟩ := ih.mp hrest
        refine ⟨List.Forall₂.cons hq hF, List.isChain_cons.mpr ⟨hH, hC⟩, by simpa using hin, ?_⟩
        cases ys with
        | nil => simpa using hL
        | cons z zs => simpa [List.getLast?_cons] using hL
      · rintro ⟨hF, hC, hH, hL⟩
        obtain ⟨hq, hF'⟩ := List.forall₂_cons.mp hF
        obtain ⟨hH', hC'⟩ := List.isChain_cons.mp hC
        refine ⟨y, ys, out y, ⟨rfl, rfl⟩, ⟨by simpa using hH, rfl, hq⟩, ih.mpr ⟨hF', hC', hH', ?_⟩⟩
        cases ys with
        | nil => simpa using hL
        | cons z zs => simpa [List.getLast?_cons] using hL

open Std.WP in
/-- `mapAccumM`'s soundness: a per-step relation, established by the step's own spec,
holds along the whole trace. The caller supplies `R` and gets the chain — no bespoke
loop invariant per gadget. -/
theorem mapAccumM_spec {V : Valuation F} {s α β : Type} [ConstraintHolds F c]
    (f : s → α → CircuitM F (Builder V c) (β × s)) (R : s → α → β → s → Prop)
    (hstep : ∀ (st : s) (x : α), ⦃fun _ => True⦄ f st x ⦃fun p _ => R st x p.1 p.2⦄) :
    ∀ (init : s) (xs : List α),
      ⦃fun _ => True⦄ mapAccumM f init xs ⦃fun p _ => Chain R init xs p.1 p.2⦄
  | init, [] => ⟨fun _ _ _ => ⟨rfl, rfl⟩⟩
  | init, x :: xs => by
    have hx := hstep init x
    have hrest := fun (acc : s) => mapAccumM_spec f R hstep acc xs
    simp only [mapAccumM]
    vcgen [hx, hrest]
    rename_i b s₁ _ hp bs _ _ hq
    exact ⟨b, bs, s₁, rfl, hp, hq⟩

open Std.WP in
/-- `List.forM`'s soundness: a per-entry postcondition, established by the entry's own
spec, holds of every entry the loop visited. -/
theorem forM_spec {V : Valuation F} {α : Type} [ConstraintHolds F c]
    (f : α → CircuitM F (Builder V c) PUnit) (R : α → Prop)
    (hstep : ∀ x : α, ⦃fun _ => True⦄ f x ⦃fun _ _ => R x⦄) :
    ∀ l : List α, ⦃fun _ => True⦄ l.forM f ⦃fun _ _ => ∀ x ∈ l, R x⦄
  | [] => ⟨fun _ _ _ x hx => by simp at hx⟩
  | x :: l => by
    have hx := hstep x
    have hrest := forM_spec f R hstep l
    rw [show (x :: l).forM f = (do f x; l.forM f) from rfl]
    vcgen [hx, hrest]
    rename_i hR _ _ hrest' y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact hR
    · exact hrest' y hy'

/-- The empty paired traversal has no results. -/
theorem zipWithVecM_zero {α β γ : Type} (f : α → β → CircuitM F c γ)
    (xs : Vector α 0) (ys : Vector β 0) : zipWithVecM f xs ys = pure #v[] := rfl

/-- A paired traversal runs the prefix before appending the final entry's result. -/
theorem zipWithVecM_succ {α β γ : Type} {n : Nat} (f : α → β → CircuitM F c γ)
    (xs : Vector α (n + 1)) (ys : Vector β (n + 1)) :
    zipWithVecM f xs ys = (do
      let init ← zipWithVecM f (Vector.ofFn fun i : Fin n ↦ xs[i.castSucc])
        (Vector.ofFn fun i : Fin n ↦ ys[i.castSucc])
      let last ← f xs[Fin.last n] ys[Fin.last n]
      pure (init.push last)) := by
  simp only [zipWithVecM, zipGo, Fin.getElem_fin, Vector.getElem_ofFn]

attribute [irreducible] zipWithVecM

end Snarky
