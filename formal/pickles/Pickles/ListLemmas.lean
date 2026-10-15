import Mathlib.Data.List.Forall2
import Mathlib.Data.Vector.Basic

/-!
# List and vector lemmas the pickles modules share

Facts about `List`, `List.Forall₂` and `Vector` that mention no pickles type: maps over zips,
entrywise relations between vectors and their lists, and how one-entry and flattened vectors
read as lists.
-/

namespace Pickles

/-! ## Zips -/

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

/-- Lists of chunks of one length with equal flattenings are equal. -/
theorem flatten_inj {α : Type} {m : ℕ} :
    ∀ {L1 L2 : List (List α)}, (∀ c ∈ L1, c.length = m) → (∀ c ∈ L2, c.length = m) →
      L1.length = L2.length → L1.flatten = L2.flatten → L1 = L2
  | [], [], _, _, _, _ => rfl
  | c1 :: L1, c2 :: L2, h1, h2, hl, hf => by
    simp only [List.flatten_cons] at hf
    obtain ⟨hc, ht⟩ := List.append_inj hf (by rw [h1 c1 (by simp), h2 c2 (by simp)])
    rw [hc, flatten_inj (fun c hc => h1 c (by simp [hc])) (fun c hc => h2 c (by simp [hc]))
      (by simpa using hl) ht]
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl

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

/-- A suffix mask emits empty lists for the prefix and maps the retained suffix. -/
theorem zipWith_suffix {α β : Type} {m n : ℕ} (ms : Vector Bool m) (xs : Vector α m)
    (f : α → List β) (hms : ∀ (j : ℕ) (hj : j < m), ms[j] = decide (m - n ≤ j)) :
    (Vector.zipWith (fun b x => if b then f x else []) ms xs).toList =
      List.replicate (m - n) [] ++ (xs.toList.drop (m - n)).map f := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [Vector.getElem_toList, Vector.getElem_zipWith, hms j (by simpa using h1)]
  by_cases hj : j < m - n
  · rw [List.getElem_append_left (by simpa using hj)]
    simp [show ¬(m - n ≤ j) by omega]
  · rw [List.getElem_append_right (by simpa using hj)]
    simp [show m - n ≤ j by omega, show m - n + (j - (m - n)) = j by omega]

/-- An entry of a mapped vector, at a `Fin` index. -/
theorem getElem_map_fin {α β : Type} {n : ℕ} (f : α → β) (Ps : Vector α n) (ci : Fin n) :
    (Ps.map f)[ci] = f Ps[ci] := by
  simp [Fin.getElem_fin]

/-- Two vectors' lists are related entrywise exactly when their entries are, index by index. -/
theorem forall₂_toList_iff {α β : Type} {R : α → β → Prop} {n : ℕ} {v : Vector α n}
    {w : Vector β n} : List.Forall₂ R v.toList w.toList ↔ ∀ i : Fin n, R v[i] w[i] := by
  rw [List.forall₂_iff_get]
  constructor
  · rintro ⟨-, h⟩ i
    simpa using h i (by simp) (by simp)
  · intro h
    exact ⟨by simp, fun i h₁ h₂ => by simpa using h ⟨i, by simpa using h₁⟩⟩

/-- A list related entrywise to a vector's list is the list of a vector of the same length,
related to it index by index. -/
theorem exists_vector_of_forall₂ {α β : Type} {R : α → β → Prop} {n : ℕ} {v : Vector α n}
    {l : List β} (h : List.Forall₂ R v.toList l) :
    ∃ w : Vector β n, w.toList = l ∧ ∀ i : Fin n, R v[i] w[i] := by
  have hl : l.length = n := by simpa using h.length_eq.symm
  refine ⟨⟨l.toArray, by simpa using hl⟩, by simp, forall₂_toList_iff.mp ?_⟩
  simpa using h

/-- A vector of singletons flattens to the vector's entries. -/
theorem toList_flatten_singletons {α β : Type} {n : ℕ} (v : Vector α n) (f : α → β) :
    (v.map fun c => #v[f c]).flatten.toList = v.toList.map f := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [Vector.getElem_toList, List.getElem_map]
  rw [Vector.getElem_flatten (by simpa using h₁)]
  simp

end Pickles
