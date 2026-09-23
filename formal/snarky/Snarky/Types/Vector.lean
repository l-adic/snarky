/-!
# Vector helpers

List-backed operations on `Vector` and their equations: a structural `map`, splitting
and appending, a prefix at a definite length, and chunking as the inverse of `flatten`.
Nothing here knows about circuits.
-/

namespace Snarky

universe u v

variable {α : Type u}

/-- A List-backed `Vector.map` (core's runs through `Array.mapM` — well-founded
recursion, opaque to the kernel; `List.map` is structural, so this version reduces
under `decide`). -/
def mapVec {β : Type v} {n : Nat} (f : α → β) (v : Vector α n) : Vector β n :=
  ⟨⟨v.toList.map f⟩, by simp⟩

@[simp] theorem toList_mapVec {β : Type v} {n : Nat}
    (f : α → β) (v : Vector α n) :
    (mapVec f v).toList = v.toList.map f := rfl

@[simp] theorem getElem_mapVec {β : Type v} {n : Nat} (f : α → β) (v : Vector α n)
    (i : Nat) (hi : i < n) : (mapVec f v)[i] = f v[i] := by
  simp [mapVec]

/-- `mapVec` is `Vector.map`. -/
theorem mapVec_eq_map {β : Type v} {n : Nat} (f : α → β) (v : Vector α n) :
    mapVec f v = v.map f := by
  ext i hi
  simp

/-- A one-entry vector is its own entry's singleton. -/
theorem vector_singleton_eta (v : Vector α 1) : #v[v[0]] = v := by
  ext i hi
  have : i = 0 := by omega
  subst this
  simp

/-- Split an `n + m` vector at `n`. -/
def splitVec {n m : Nat} (v : Vector α (n + m)) : Vector α n × Vector α m :=
  (⟨⟨v.toList.take n⟩, by simp⟩, ⟨⟨v.toList.drop n⟩, by simp⟩)

@[simp] theorem splitVec_append {n m : Nat} (v : Vector α n) (w : Vector α m) :
    splitVec (v ++ w) = (v, w) := by
  refine Prod.ext ?_ ?_ <;> ext i hi <;> simp [splitVec]

@[simp] theorem append_splitVec {n m : Nat} (v : Vector α (n + m)) :
    (splitVec v).1 ++ (splitVec v).2 = v := by
  ext i hi
  simp [splitVec]

/-- Two appends agree exactly when their halves do. -/
theorem append_inj_iff {n m : Nat} {v v' : Vector α n} {w w' : Vector α m} :
    v ++ w = v' ++ w' ↔ v = v' ∧ w = w' :=
  ⟨fun h => by simpa using congrArg splitVec h, fun ⟨h₁, h₂⟩ => by rw [h₁, h₂]⟩

theorem mapVec_append {β : Type v} {n m : Nat} (f : α → β) (v : Vector α n) (w : Vector α m) :
    mapVec f (v ++ w) = mapVec f v ++ mapVec f w := by
  ext i hi
  rcases Nat.lt_or_ge i n with h | h
  · simp [h]
  · simp [Vector.getElem_append_right hi h]

/-- The first `k` entries, at a definite length — `Vector.take` lands at `min k n`, which
would need a cast wherever the bound is a hypothesis rather than a literal. -/
def takeVec {n : Nat} (k : Nat) (hk : k ≤ n) (v : Vector α n) : Vector α k :=
  Vector.ofFn fun i : Fin k => v[i.val]'(Nat.lt_of_lt_of_le i.isLt hk)

@[simp] theorem getElem_takeVec {n k : Nat} (hk : k ≤ n) (v : Vector α n) (i : Nat)
    (hi : i < k) : (takeVec k hk v)[i] = v[i]'(Nat.lt_of_lt_of_le hi hk) := by
  simp [takeVec]

/-- The inverse of `Vector.flatten`: cut an `n * s` vector into `n` pieces of `s`. -/
def chunkVec {s n : Nat} (v : Vector α (n * s)) : Vector (Vector α s) n :=
  Vector.ofFn fun i => Vector.ofFn fun j => v[j.1 + s * i.1]'(by
    have h := Nat.mul_le_mul_left s i.2
    rw [Nat.mul_succ] at h
    have hj := j.2
    rw [Nat.mul_comm n s]
    omega)

@[simp] theorem chunkVec_flatten {s n : Nat} (vs : Vector (Vector α s) n) :
    chunkVec vs.flatten = vs := by
  ext i hi j hj
  have hs : 0 < s := Nat.lt_of_le_of_lt (Nat.zero_le j) hj
  simp [chunkVec, Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]

/-- A chunk's entry is the flat vector's, at the flattened index. -/
@[simp] theorem getElem_chunkVec {s n : Nat} (v : Vector α (n * s)) (r j : Nat)
    (hr : r < n) (hj : j < s) :
    ((chunkVec v)[r]'hr)[j]'hj = v[j + s * r]'(by
      have h := Nat.mul_le_mul_left s hr
      rw [Nat.mul_succ] at h
      rw [Nat.mul_comm n s]
      omega) := by
  simp [chunkVec]

@[simp] theorem flatten_chunkVec {s n : Nat} (v : Vector α (n * s)) :
    (chunkVec v).flatten = v := by
  ext k hk
  simp [chunkVec, Nat.mod_add_div]

/-- A vector's flattening, as a list: the pieces' lists concatenated. -/
theorem toList_flatten {s n : Nat} (vs : Vector (Vector α s) n) :
    vs.flatten.toList = (vs.toList.map Vector.toList).flatten := by
  simp [Vector.flatten, Array.toList_flatten, List.map_map, Function.comp_def]
  rfl

/-- The pieces' entrywise images, concatenated, are the flat vector's: chunking is a
regrouping, so anything read off it entrywise reads off the flat vector. -/
theorem flatten_map_chunkVec {β : Type v} {s n : Nat} (v : Vector α (n * s)) (g : α → β) :
    ((chunkVec v).toList.map fun row => row.toList.map g).flatten = v.toList.map g := by
  rw [show (fun row : Vector α s => row.toList.map g)
      = (fun l : List α => l.map g) ∘ Vector.toList from rfl,
    ← List.map_map, ← List.map_flatten, ← toList_flatten, flatten_chunkVec]

end Snarky
