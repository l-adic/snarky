/-!
# Vector utilities

Kernel-reduction-friendly `Vector` operations: replacements for kernel-opaque core
functions, and the `Data.Vector` ports the DSL needs (PS `sized-vector`). Everything in
this library is validated by `decide`, which reduces terms in the kernel — and several
core `Vector` functions go through `Array.mapM`, whose loop is compiled by *well-founded
recursion* and is therefore opaque to kernel reduction: a single such call anywhere in an
executable path silently wedges every downstream `decide`. Replacements take the `List`
route instead (structural recursion, reduces by iota), converting through
`Vector.toList` with a `simp` length witness; ports are structural on the length.
-/

namespace Snarky

/-- A List-backed `Vector.map` (core's runs through `Array.mapM` — well-founded recursion,
opaque to the kernel; `List.map` is structural, so this version reduces under `decide`). -/
def mapVec (f : α → β) (v : Vector α n) : Vector β n :=
  ⟨⟨v.toList.map f⟩, by simp⟩

@[simp] theorem toList_mapVec (f : α → β) (v : Vector α n) :
    (mapVec f v).toList = v.toList.map f := rfl

@[simp] theorem getElem_mapVec (f : α → β) (v : Vector α n) (i : Nat) (hi : i < n) :
    (mapVec f v)[i] = f v[i] := by
  simp [mapVec]

/-- A flattening reads as the flattening of the element lists (the `toList` bridge core
provides for `map` but not `flatten`). -/
theorem toList_flatten {α : Type u} {m n : Nat} (xss : Vector (Vector α m) n) :
    xss.flatten.toList = (xss.toList.map Vector.toList).flatten := by
  rcases xss with ⟨⟨l⟩, h⟩
  simp [Vector.flatten_mk, List.map_map]
  rfl

/-- Collect `n` indexed effectful computations into a sized vector, in index order —
PS `Vector.generateA`, monad-generic. Structural on `n`, so it kernel-reduces at any
concrete monad. -/
def generateVec {m : Type u → Type v} [Monad m] :
    (n : Nat) → (Fin n → m α) → m (Vector α n)
  | 0, _ => pure #v[]
  | n + 1, f => do
    let init ← generateVec n fun i => f i.castSucc
    let last ← f (Fin.last n)
    pure (init.push last)

end Snarky
