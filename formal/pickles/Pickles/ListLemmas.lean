import Mathlib.Data.List.Forall2
import Mathlib.Data.Vector.Basic

/-!
# List and vector lemmas the pickles modules share

Facts about `List`, `List.Forall₂` and `Vector` that mention no pickles type: what a circuit
that walks two cell lists in step establishes about them as lists, and how one-entry and
flattened vectors read as lists.
-/

namespace Pickles

/-! ## Zips -/

/-- Pointwise ties along a zip give the mapped lists, at equal lengths: what a circuit that
compares two cell lists entry by entry establishes about them as lists. -/
theorem map_eq_map_of_zip {α β γ : Type} {f : α → γ} {g : β → γ} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      (∀ p ∈ l₁.zip l₂, f p.1 = g p.2) → l₁.map f = l₂.map g
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => absurd hlen (by simp)
  | _ :: _, [], hlen, _ => absurd hlen (by simp)
  | a :: as, b :: bs, hlen, h => by
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨h (a, b) (by simp), map_eq_map_of_zip (by simpa using hlen) fun p hp => h p ?_⟩
      rw [List.zip_cons_cons]
      exact List.mem_cons_of_mem _ hp

/-- Mapping a function of the second components over a zip, at equal lengths, maps the second
list. -/
theorem zip_map_snd {α β γ : Type} (g : β → γ) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
      (l₁.zip l₂).map (fun x => g x.2) = l₂.map g := fun l₁ l₂ h => by
  rw [show (fun x : α × β => g x.2) = g ∘ Prod.snd from rfl, ← List.map_map,
    List.map_snd_zip h.ge]

/-- Mapping a function of the first components over a zip of two vectors maps the first. -/
theorem toList_map_fst_zip {α β γ : Type} {n : ℕ} (as : Vector α n) (bs : Vector β n)
    (f : α → γ) : List.map (fun x => f x.1) (as.toList.zip bs.toList) = as.toList.map f := by
  show List.map (f ∘ (fun x : α × β => x.1)) _ = _
  rw [← List.map_map, ← Vector.toList_zip, ← Vector.toList_map, Vector.map_fst_zip]

/-! ## `Forall₂` along zips -/

/-- Pairing a list with another of the same length keeps a relation on the first. -/
theorem forall₂_zip_left {α β γ : Type} {R : α → γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List γ} (l : List β), List.Forall₂ R l₁ l₂ → l.length = l₁.length →
      List.Forall₂ (fun q v => R q.1 v) (l₁.zip l) l₂
  | [], [], _, .nil, _ => .nil
  | _ :: _, _ :: _, [], .cons _ _, h => absurd h (by simp)
  | _ :: _, _ :: _, _ :: l, .cons hq hs, h =>
    .cons hq (forall₂_zip_left l hs (by simpa using h))

/-- A relation on the second components of a zip, at equal lengths, is one on the list. -/
theorem forall₂_zip_right {α β γ : Type} {R : β → γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {ns : List γ}, l₂.length = l₁.length →
      List.Forall₂ (fun q m => R q.2 m) (l₁.zip l₂) ns → List.Forall₂ R l₂ ns
  | [], [], _, _, h => by cases h; exact .nil
  | _ :: _, _ :: l₂, _ :: _, hl, .cons hq hs => .cons hq (forall₂_zip_right (by simpa using hl) hs)
  | [], _ :: _, _, hl, _ => absurd hl (by simp)
  | _ :: _, [], _, hl, _ => absurd hl (by simp)

/-- Two `List.zipWith`s of the same lists are related where their entries are, pair by pair. -/
theorem forall₂_zipWith {α β γ δ : Type} (R : γ → δ → Prop) (f : α → β → γ) (g : α → β → δ) :
    ∀ (ks : List α) (lb : List β), (∀ p ∈ ks.zip lb, R (f p.1 p.2) (g p.1 p.2)) →
      List.Forall₂ R (List.zipWith f ks lb) (List.zipWith g ks lb)
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | k :: ks, P :: lb, h => by
      simp only [List.zipWith_cons_cons]
      exact List.Forall₂.cons (h (k, P) (by simp))
        (forall₂_zipWith R f g ks lb fun p hp => h p (by simp [hp]))

/-! ## Flattening -/

/-- A flattened vector of vectors, as a list, is the flattened list of their lists. -/
theorem toList_flatten' {α : Type} {m n : ℕ} (v : Vector (Vector α n) m) :
    v.flatten.toList = (v.toList.map Vector.toList).flatten := by
  simp [Vector.flatten, Vector.toList, Function.comp_def]
  rfl

/-- Keeping the entries a mask sets: the flattened singletons are the kept entries, in order. -/
theorem flatten_zipWith_keep {α : Type} :
    ∀ {w : ℕ} (m : Fin w → Bool) (f : Fin w → α),
      (List.zipWith (fun b x => if b = true then [x] else []) (List.ofFn m)
        (List.ofFn f)).flatten = ((List.finRange w).filter m).map f
  | 0, _, _ => by simp
  | _ + 1, m, f => by
    rw [List.ofFn_succ, List.ofFn_succ, List.zipWith_cons_cons, List.flatten_cons,
      flatten_zipWith_keep (fun j => m j.succ) (fun j => f j.succ), List.finRange_succ,
      List.filter_cons, List.filter_map]
    by_cases h : m 0 <;> simp [h, Function.comp_def, List.map_map]

/-! ## Vectors -/

/-- An entry of a mapped vector, at a `Fin` index. -/
theorem getElem_map_fin {α β : Type} {n : ℕ} (f : α → β) (Ps : Vector α n) (ci : Fin n) :
    (Ps.map f)[ci] = f Ps[ci] := by
  simp [Fin.getElem_fin]

end Pickles
