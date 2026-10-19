import Snarky.Prover
import Snarky.Prover.WP
import Mathlib.Data.List.Chain

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
    (hpre : Monotone pre) :
    ∀ (n : Nat) (xs : Fin n → α) (ys : Fin n → β)
      (post : Fin n → γ → ProverState F → Prop),
      (∀ (i : Fin n) (a : γ), Monotone (post i a)) →
      (∀ i : Fin n, Complete pre (f (xs i) (ys i)) (post i)) →
      Complete pre (zipGo f n xs ys) (fun rs st' => ∀ i : Fin n, post i rs[i] st')
  | 0, _, _, _, _, _ => Complete.pure_of fun _ _ i => i.elim0
  | n + 1, xs, ys, post, hmono, hf => by
    refine Complete.bind
      (Complete.imp (fun _ h => ⟨h, h⟩) (fun _ _ h => h)
        (Complete.frame hpre (zipGo_complete f pre hpre n (fun i => xs i.castSucc)
          (fun i => ys i.castSucc) (fun i => post i.castSucc)
          (fun i => hmono i.castSucc) (fun i => hf i.castSucc))))
      fun init => Complete.bind
        (Complete.imp (fun _ h => ⟨h.2, h.1⟩) (fun _ _ h => h)
          (Complete.frame
            (Monotone.forall fun i : Fin n => hmono i.castSucc init[i])
            (hf (Fin.last n))))
        fun last => Complete.pure_of fun _ h i => by
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using h.1
          · simpa using h.2 j

/-- Every entry's completeness composes into the loop's, given that the precondition and
the entries' postconditions transport along the table's growth. -/
theorem zipWithVecM_complete {n : Nat} (f : α → β → CircuitM F c γ) (xs : Vector α n)
    (ys : Vector β n) (pre : ProverState F → Prop) (post : Fin n → γ → ProverState F → Prop)
    (hpre : Monotone pre) (hpost : ∀ (i : Fin n) (a : γ), Monotone (post i a))
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

/-- `mapAccumM`'s completeness: a step's law, an accumulator invariant indexed by what is
left to traverse, and a per-step fact compose into the loop's. The fact splits into its
wiring (`wire`, stateless) and a fact about the output at the table (`row`, monotone); the
loop returns the wiring as a `Chain` and every output's fact at the final table, where an
emitted row is judged. -/
theorem mapAccumM_complete [Zero F] [ConstraintHolds F c] {s α β : Type}
    (f : s → α → CircuitM F c (β × s)) (P : α → Prop)
    (inv : List α → s → ProverState F → Prop)
    (wire : s → α → β → s → Prop) (row : β → ProverState F → Prop)
    (hinv : ∀ (xs : List α) (acc : s), Monotone (inv xs acc))
    (hrow : ∀ y : β, Monotone (row y))
    (hstep : ∀ (acc : s) (x : α) (xs : List α), P x →
      Complete (inv (x :: xs) acc) (f acc x)
        (fun p st' => inv xs p.2 st' ∧ wire acc x p.1 p.2 ∧ row p.1 st')) :
    ∀ (init : s) (xs : List α), (∀ x ∈ xs, P x) →
      Complete (inv xs init) (mapAccumM f init xs)
        (fun p st' => inv [] p.2 st' ∧ Chain wire init xs p.1 p.2 ∧ ∀ y ∈ p.1, row y st')
  | init, [], _ => Complete.pure_of fun _ h => ⟨h, ⟨rfl, rfl⟩, by simp⟩
  | init, x :: xs, hP =>
    Complete.bind (hstep init x xs (hP x (by simp)))
      fun p => Complete.bind
        (Complete.frame (monotone_and monotone_const (hrow p.1))
          (mapAccumM_complete f P inv wire row hinv hrow hstep p.2 xs
            fun y hy => hP y (by simp [hy])))
        fun q => Complete.pure_of fun _ h =>
          ⟨h.1.1, ⟨p.1, q.1, p.2, rfl, h.2.1, h.1.2.1⟩, by
            rintro y (_ | ⟨_, hy⟩)
            · exact h.2.2
            · exact h.1.2.2 y hy⟩

open Std.Do in
/-- `List.forM`'s soundness: a per-entry postcondition, established by the entry's own
spec, holds of every entry the loop visited. -/
theorem forM_spec {V : Valuation F} {α : Type} [ConstraintHolds F c]
    (f : α → CircuitM F (Builder V c) PUnit) (R : α → Prop)
    (hstep : ∀ x : α, ⦃⌜True⌝⦄ f x ⦃⇓ _ _ => ⌜R x⌝⦄) :
    ∀ l : List α, ⦃⌜True⌝⦄ l.forM f ⦃⇓ _ _ => ⌜∀ x ∈ l, R x⌝⦄
  | [] => by
    intro nv _ _ x hx
    simp at hx
  | x :: l => by
    have hx := hstep x
    have hrest := forM_spec f R hstep l
    rw [show (x :: l).forM f = (do f x; l.forM f) from rfl]
    mvcgen [hx, hrest]
    rename_i _ _ _ hR _ _
    intro hrest' y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact hR
    · exact hrest' y hy'

/-! ## The prover reading

The state-relative completeness laws of the loops, generic in the per-element conditions as the
`Vector.mapM` law is: `P` at an element's entry state, `Q` of its entry, result and exit, the
transports as hypotheses, and every element's condition at the loop's entry and every result's
fact there, per index. -/

section ProverReading

open Std.Do

variable [Zero F] [ConstraintHolds F c] {α β γ : Type}

/-- `zipGo`'s law, by induction on the length. -/
private theorem Prover.zipGo_spec (f : α → β → CircuitM F (Prover c) γ)
    (P : ProverState F → α → β → Prop)
    (Q : ProverState F → α → β → γ → ProverState F → Prop)
    (hP : ∀ st st' x y, st ≤ st' → P st x y → P st' x y)
    (hQ : ∀ st st' x y r s', st ≤ st' → P st x y → Q st' x y r s' → Q st x y r s')
    (hQ' : ∀ st x y r s' s'', s' ≤ s'' → Q st x y r s' → Q st x y r s'')
    (hle : ∀ st x y r s', Q st x y r s' → st ≤ s')
    (hf : ∀ st x y, ⦃fun s => ⌜s = st ∧ P st x y⌝⦄ f x y ⦃⇓ r s' => ⌜Q st x y r s'⌝⦄) :
    ∀ (n : Nat) (xs : Fin n → α) (ys : Fin n → β) (st₀ : ProverState F),
      ⦃fun s => ⌜s = st₀ ∧ ∀ i, P st₀ (xs i) (ys i)⌝⦄
      zipGo f n xs ys
      ⦃⇓ rs s' => ⌜(∀ i, Q st₀ (xs i) (ys i) rs[i] s') ∧ st₀ ≤ s'⌝⦄
  | 0, _, _, st₀ => by
    simp only [zipGo]
    mvcgen
    rename_i s h
    exact ⟨fun i => i.elim0, le_of_eq h.1.symm⟩
  | n + 1, xs, ys, st₀ => by
    have hinit := Prover.zipGo_spec f P Q hP hQ hQ' hle hf n (fun i => xs i.castSucc)
      (fun i => ys i.castSucc)
    simp only [zipGo]
    mvcgen [hinit, hf]
    case pre =>
      rename_i s h
      obtain ⟨rfl, hall⟩ := h
      exact ⟨trivial, fun i => hall i.castSucc⟩
    case post.success.pre =>
      rename_i s h init s₁ hinit'
      obtain ⟨rfl, hall⟩ := h
      exact ⟨trivial, hP _ _ _ _ hinit'.2 (hall (Fin.last n))⟩
    case post.success.post.success =>
      rename_i s h init s₁ hinit' last s₂ hlast'
      obtain ⟨rfl, hall⟩ := h
      refine ⟨fun i => ?_, hinit'.2.trans (hle _ _ _ _ _ hlast')⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hQ _ _ _ _ _ _ hinit'.2 (hall (Fin.last n)) hlast'
      · simpa using hQ' _ _ _ _ _ _ (hle _ _ _ _ _ hlast') (hinit'.1 j)

/-- `zipWithVecM`'s state-relative completeness: every entry's condition at the loop's entry,
every result's fact there. -/
theorem Prover.zipWithVecM_spec {n : Nat} (f : α → β → CircuitM F (Prover c) γ)
    (P : ProverState F → α → β → Prop)
    (Q : ProverState F → α → β → γ → ProverState F → Prop)
    (hP : ∀ st st' x y, st ≤ st' → P st x y → P st' x y)
    (hQ : ∀ st st' x y r s', st ≤ st' → P st x y → Q st' x y r s' → Q st x y r s')
    (hQ' : ∀ st x y r s' s'', s' ≤ s'' → Q st x y r s' → Q st x y r s'')
    (hle : ∀ st x y r s', Q st x y r s' → st ≤ s')
    (hf : ∀ st x y, ⦃fun s => ⌜s = st ∧ P st x y⌝⦄ f x y ⦃⇓ r s' => ⌜Q st x y r s'⌝⦄)
    (xs : Vector α n) (ys : Vector β n) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ ∀ i : Fin n, P st₀ xs[i] ys[i]⌝⦄
    zipWithVecM f xs ys
    ⦃⇓ rs s' => ⌜(∀ i : Fin n, Q st₀ xs[i] ys[i] rs[i] s') ∧ st₀ ≤ s'⌝⦄ :=
  Prover.zipGo_spec f P Q hP hQ hQ' hle hf n _ _ st₀

/-- `List.forM`'s state-relative completeness: a unit result, so every entry's condition at the
loop's entry is the whole content; the induction hypothesis is passed registered. -/
theorem Prover.forM_spec (f : α → CircuitM F (Prover c) PUnit) (P : ProverState F → α → Prop)
    (hP : ∀ st st' x, st ≤ st' → P st x → P st' x)
    (hf : ∀ st x, ⦃fun s => ⌜s = st ∧ P st x⌝⦄ f x ⦃⇓ _ s' => ⌜st ≤ s'⌝⦄) :
    ∀ (l : List α) (st₀ : ProverState F),
      ⦃fun s => ⌜s = st₀ ∧ ∀ x ∈ l, P st₀ x⌝⦄ l.forM f ⦃⇓ _ s' => ⌜st₀ ≤ s'⌝⦄
  | [], st₀ => by
    rw [show ([] : List α).forM f = pure PUnit.unit from rfl]
    mvcgen
    rename_i s h
    exact le_of_eq h.1.symm
  | x :: l, st₀ => by
    have hf' := Prover.register (fun st => hf st x)
    have hrest := Prover.register (Prover.forM_spec f P hP hf l)
    rw [show (x :: l).forM f = (do f x; l.forM f) from rfl]
    mvcgen [hf', hrest]
    all_goals grind [Prover.Reg.iff, List.mem_cons_self, List.mem_cons_of_mem]

end ProverReading

/-! ## The prover reading of the accumulating loop

The generic law chains the step's fact with the state threaded beside the accumulator, so no
fact is re-read at the loop's entry inside the law. The reading form is its corollary: the
readings are parameters, the step fact is one named shape, and the loop's result is a scan. -/

section MapAccum

open Std.Do

/-- `mapAccumM`'s state-relative completeness: the element condition carries forward, the step
establishes the next accumulator's condition and advances the state, and the per-step facts
chain from the initial accumulator at the entry to the final one at the exit. -/
theorem Prover.mapAccumM_spec [Zero F] [ConstraintHolds F c] {s α β : Type}
    (f : s → α → CircuitM F (Prover c) (β × s))
    (A : ProverState F → s → Prop) (E : ProverState F → α → Prop)
    (Q : ProverState F → s → α → β → s → ProverState F → Prop)
    (hE : ∀ st st' x, st ≤ st' → E st x → E st' x)
    (hQA : ∀ st acc x y acc' s', Q st acc x y acc' s' → A s' acc')
    (hle : ∀ st acc x y acc' s', Q st acc x y acc' s' → st ≤ s')
    (hf : ∀ st acc x, ⦃fun s => ⌜s = st ∧ A st acc ∧ E st x⌝⦄ f acc x
      ⦃⇓ p s' => ⌜Q st acc x p.1 p.2 s'⌝⦄) :
    ∀ (init : s) (xs : List α) (st₀ : ProverState F),
      ⦃fun s => ⌜s = st₀ ∧ A st₀ init ∧ ∀ x ∈ xs, E st₀ x⌝⦄
      mapAccumM f init xs
      ⦃⇓ p s' => ⌜Chain (fun a x y b => Q a.2 a.1 x y b.1 b.2) (init, st₀) xs p.1 (p.2, s') ∧
        st₀ ≤ s'⌝⦄
  | init, [], st₀ => by
    simp only [mapAccumM]
    mvcgen
    rename_i s h
    obtain ⟨rfl, -⟩ := h
    exact ⟨⟨rfl, rfl⟩, le_rfl⟩
  | init, x :: xs, st₀ => by
    have ih := fun (acc : s) (st : ProverState F) =>
      Prover.mapAccumM_spec f A E Q hE hQA hle hf acc xs st
    simp only [mapAccumM]
    mvcgen [hf, ih]
    case pre =>
      rename_i s h
      obtain ⟨rfl, hA, hE'⟩ := h
      exact ⟨trivial, hA, hE' x (List.mem_cons_self ..)⟩
    case post.success.pre =>
      rename_i s h p s₁ hp
      obtain ⟨rfl, hA, hE'⟩ := h
      exact ⟨trivial, hQA _ _ _ _ _ _ hp,
        fun y hy => hE _ _ y (hle _ _ _ _ _ _ hp) (hE' y (List.mem_cons_of_mem _ hy))⟩
    case post.success.post.success =>
      rename_i s h p s₁ hp q s₂ hq
      obtain ⟨rfl, hA, hE'⟩ := h
      exact ⟨⟨p.1, q.1, (p.2, s₁), rfl, hp, hq.1⟩, (hle _ _ _ _ _ _ hp).trans hq.2⟩

section Scan

variable {s α β A X Y : Type}
  (Ss : ProverState F → s → Prop) (Sx : ProverState F → α → Prop) (Sy : ProverState F → β → Prop)
  (reads : ProverState F → s → A) (readx : ProverState F → α → X) (ready : ProverState F → β → Y)
  (g : A → X → A) (h : A → X → Y)

/-- The step fact of a reading-shaped step: the output and the next accumulator are in scope at
the exit and read the step functions of the entry readings, and the state advanced. One
definition, so the corollary, the chain lemma and every ladder's step spec share one shape;
reducible, so `grind` sees the conjuncts. -/
abbrev Prover.ScanStep (st : ProverState F) (acc : s) (x : α) (y : β) (acc' : s)
    (s' : ProverState F) : Prop :=
  Sy s' y ∧ Ss s' acc' ∧ ready s' y = h (reads st acc) (readx st x) ∧
    reads s' acc' = g (reads st acc) (readx st x) ∧ st ≤ s'

/-- In range, the default of `List.getD` is immaterial. -/
private theorem getD_congr_of_lt {l : List A} {i : ℕ} (hi : i < l.length) (d d' : A) :
    l.getD i d = l.getD i d' := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- The chain of reading-shaped steps, read at the loop's entry and the final state: the
accumulator folds, each output is the step function at the prefix fold before it. -/
private theorem Prover.chain_scan
    (hSx : ∀ st st' x, st ≤ st' → Sx st x → Sx st' x)
    (hSy : ∀ st st' y, st ≤ st' → Sy st y → Sy st' y)
    (hreadx : ∀ st st' x, st ≤ st' → Sx st x → readx st' x = readx st x)
    (hready : ∀ st st' y, st ≤ st' → Sy st y → ready st' y = ready st y) :
    ∀ {xs : List α} {init : s} {st₀ : ProverState F} {ys : List β} {fin : s}
      {s' : ProverState F},
      Chain (fun a x y b => Prover.ScanStep Ss Sy reads readx ready g h a.2 a.1 x y b.1 b.2)
        (init, st₀) xs ys (fin, s') →
      Ss st₀ init → (∀ x ∈ xs, Sx st₀ x) →
      Ss s' fin ∧ reads s' fin = (xs.map (readx st₀)).foldl g (reads st₀ init) ∧
        ys.length = xs.length ∧
        (∀ (i : ℕ) (hi : i < xs.length) (hi' : i < ys.length), Sy s' ys[i] ∧
          ready s' ys[i] =
            h (((xs.map (readx st₀)).scanl g (reads st₀ init)).getD i (reads st₀ init))
              (readx st₀ xs[i])) ∧
        st₀ ≤ s'
  | [], init, st₀, ys, fin, s', hch, hinit, _ => by
    obtain ⟨rfl, hend⟩ := hch
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hend
    exact ⟨hinit, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), le_rfl⟩
  | x :: xs, init, st₀, ys, fin, s', hch, hinit, hxs => by
    obtain ⟨y, ys', ⟨acc₁, s₁⟩, rfl, hq, hrest⟩ := hch
    dsimp only at hq
    obtain ⟨hy, hacc, hready₁, hreads₁, hle₁⟩ := hq
    have hxs' : ∀ z ∈ xs, Sx st₀ z := fun z hz => hxs z (List.mem_cons_of_mem _ hz)
    obtain ⟨hfin, hfold, hlen, hidx, hle₂⟩ :=
      Prover.chain_scan hSx hSy hreadx hready hrest hacc
        fun z hz => hSx _ _ z hle₁ (hxs' z hz)
    have hmap : xs.map (readx s₁) = xs.map (readx st₀) :=
      List.map_congr_left fun z hz => hreadx _ _ z hle₁ (hxs' z hz)
    refine ⟨hfin, ?_, by simp [hlen], ?_, hle₁.trans hle₂⟩
    · rw [hfold, hmap, hreads₁, List.map_cons, List.foldl_cons]
    · intro i hi hi'
      cases i with
      | zero =>
        refine ⟨hSy _ _ y hle₂ hy, ?_⟩
        simp only [List.getElem_cons_zero, List.map_cons, List.scanl_cons, List.getD_cons_zero]
        rw [hready _ _ y hle₂ hy, hready₁]
      | succ j =>
        have hj : j < xs.length := by simpa using hi
        have hj' : j < ys'.length := by simpa using hi'
        obtain ⟨hyj, hreadj⟩ := hidx j hj hj'
        refine ⟨by simpa using hyj, ?_⟩
        have hxj : readx st₀ xs[j] = readx s₁ xs[j] :=
          (hreadx _ _ _ hle₁ (hxs' _ (List.getElem_mem hj))).symm
        rw [hreads₁] at hreadj
        simp only [List.getElem_cons_succ, List.map_cons, List.scanl_cons, List.getD_cons_succ,
          ← hmap, hxj]
        rw [getD_congr_of_lt (by simp; omega) _ (g (reads st₀ init) (readx st₀ x))]
        exact hreadj

/-- `mapAccumM`'s reading form: the accumulator folds the elements' entry readings, each output
is the step function at the prefix fold before it, all in scope at the final state. The four
transports are grind lines at a ladder. -/
theorem Prover.mapAccumM_scan_spec [Zero F] [ConstraintHolds F c]
    (f : s → α → CircuitM F (Prover c) (β × s)) (px : X → Prop)
    (hSx : ∀ st st' x, st ≤ st' → Sx st x → Sx st' x)
    (hSy : ∀ st st' y, st ≤ st' → Sy st y → Sy st' y)
    (hreadx : ∀ st st' x, st ≤ st' → Sx st x → readx st' x = readx st x)
    (hready : ∀ st st' y, st ≤ st' → Sy st y → ready st' y = ready st y)
    (hf : ∀ st acc x, ⦃fun s => ⌜s = st ∧ Ss st acc ∧ Sx st x ∧ px (readx st x)⌝⦄ f acc x
      ⦃⇓ p s' => ⌜Prover.ScanStep Ss Sy reads readx ready g h st acc x p.1 p.2 s'⌝⦄)
    (init : s) (xs : List α) (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ Ss st₀ init ∧ ∀ x ∈ xs, Sx st₀ x ∧ px (readx st₀ x)⌝⦄
    mapAccumM f init xs
    ⦃⇓ p s' => ⌜Ss s' p.2 ∧ reads s' p.2 = (xs.map (readx st₀)).foldl g (reads st₀ init) ∧
      p.1.length = xs.length ∧
      (∀ (i : ℕ) (hi : i < xs.length) (hi' : i < p.1.length), Sy s' p.1[i] ∧
        ready s' p.1[i] =
          h (((xs.map (readx st₀)).scanl g (reads st₀ init)).getD i (reads st₀ init))
            (readx st₀ xs[i])) ∧
      st₀ ≤ s'⌝⦄ := by
  have hgen := Prover.mapAccumM_spec f Ss (fun st x => Sx st x ∧ px (readx st x))
    (Prover.ScanStep Ss Sy reads readx ready g h)
    (fun st st' x hle hx => ⟨hSx _ _ x hle hx.1, by rw [hreadx _ _ x hle hx.1]; exact hx.2⟩)
    (fun _ _ _ _ _ _ hq => hq.2.1) (fun _ _ _ _ _ _ hq => hq.2.2.2.2) hf init xs st₀
  intro s hs
  obtain ⟨rfl, hinit, hxs⟩ := hs
  have hrun := hgen s ⟨rfl, hinit, hxs⟩
  refine (wp (mapAccumM f init xs)).mono _ _ ?_ s hrun
  refine ⟨fun p s' hpost => ?_, .rfl⟩
  obtain ⟨hch, hle⟩ := hpost
  obtain ⟨hfin, hfold, hlen, hidx, -⟩ := Prover.chain_scan Ss Sx Sy reads readx ready g h hSx hSy
    hreadx hready hch hinit fun x hx => (hxs x hx).1
  exact ⟨hfin, hfold, hlen, hidx, hle⟩

end Scan

end MapAccum

attribute [irreducible] zipWithVecM

end Snarky
