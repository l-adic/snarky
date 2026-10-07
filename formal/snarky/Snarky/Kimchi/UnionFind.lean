import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Find

/-!
# Pure union-find

Transcribes packages/union-find/src/Data/UnionFind/Mutable.purs: the int-keyed parent/rank
union-find threaded through the kimchi backend's wire state. The upstream structure is
mutable with path halving; this one is pure and drops the halving. That changes nothing
observable: halving only re-points non-root elements at ancestors, so every root, rank,
union decision and `find` result is the same.

The union-by-rank rule is mirrored exactly, tie-break included, because the representative
is observable through `rootOf`, and the wiring built from it is compared by the CS-equality
check (`formal/scripts/check_cs.lean`).

## Main results

The class view, under which nothing outside this module reads `parent` or `rank`:

- `Inv`: parents in range, rank strictly increasing along a non-root's parent pointer;
  `empty_inv`, `find_inv`, `union_inv`.
- `Same`: two elements share a class; `same_union_self`, `same_union_mono`, `same_find_mono`:
  a union joins its arguments, and neither a union nor a `find` splits a class.
- `rootOf_getD_eq`: the dense view agrees with `find`.
-/

namespace Snarky.Kimchi

/-- Int-keyed union-find: dense parent and rank arrays, elements `0 .. parent.size - 1`.
An element outside the arrays is its own singleton class until `ensure` adds it. -/
structure UnionFind where
  /-- Parent pointers, dense by element: a root points at itself. -/
  parent : Array Nat
  /-- Union-by-rank ranks, in lockstep with `parent`. -/
  rank : Array Nat

namespace UnionFind

/-- The empty structure: no elements seen. -/
def empty : UnionFind := ⟨#[], #[]⟩

/-- Grow the arrays so element `i` exists; new elements are singletons of rank `0`. -/
private def ensure (i : Nat) (uf : UnionFind) : UnionFind :=
  if i < uf.parent.size then uf
  else
    let grow := List.range (i + 1 - uf.parent.size) |>.map (· + uf.parent.size)
    ⟨uf.parent ++ grow.toArray, uf.rank ++ (grow.map fun _ => 0).toArray⟩

/-- Chase parent pointers to the root. The fuel is the element count: parent chains are
acyclic and shorter than the array. -/
private def rootLoop (fuel x : Nat) (parent : Array Nat) : Nat :=
  match fuel with
  | 0 => x
  | fuel + 1 =>
    let p := parent.getD x x
    if p = x then x else rootLoop fuel p parent

/-- The representative of `x`, adding `x` as a singleton if unseen; returns the
possibly-grown structure alongside. -/
def find (x : Nat) (uf : UnionFind) : Nat × UnionFind :=
  let uf := uf.ensure x
  (rootLoop uf.parent.size x uf.parent, uf)

/-- Merge the classes of `x` and `y` by rank: the smaller-rank root is pointed at the
larger; on a tie, `y`'s root is pointed at `x`'s, whose rank bumps. -/
def union (x y : Nat) (uf : UnionFind) : UnionFind :=
  let uf := (uf.ensure x).ensure y
  let rx := rootLoop uf.parent.size x uf.parent
  let ry := rootLoop uf.parent.size y uf.parent
  if rx = ry then uf
  else
    let cx := uf.rank.getD rx 0
    let cy := uf.rank.getD ry 0
    if cx < cy then { uf with parent := uf.parent.set! rx ry }
    else if cy < cx then { uf with parent := uf.parent.set! ry rx }
    else { uf with parent := uf.parent.set! ry rx, rank := uf.rank.set! rx (cx + 1) }

/-- The root of every seen element, dense by element index; the view `assembleGates`
consumes. -/
def rootOf (uf : UnionFind) : Array Nat :=
  (List.range uf.parent.size).map (fun i => rootLoop uf.parent.size i uf.parent)
    |>.toArray

/-! ## The class view -/

/-- Parents stay in range, and rank strictly increases along a non-root's parent pointer. -/
def Inv (uf : UnionFind) : Prop :=
  uf.rank.size = uf.parent.size ∧
    ∀ i (h : i < uf.parent.size), uf.parent[i] < uf.parent.size ∧
      (uf.parent[i] = i ∨ uf.rank[i]! < uf.rank[uf.parent[i]]!)

/-- Two elements share a class. -/
def Same (uf : UnionFind) (v w : Nat) : Prop := (uf.find v).1 = (uf.find w).1

/-- A root: its own parent, an unseen element included. -/
private def IsRoot (parent : Array Nat) (r : Nat) : Prop := parent.getD r r = r

private instance (parent : Array Nat) (r : Nat) : Decidable (IsRoot parent r) :=
  inferInstanceAs (Decidable (parent.getD r r = r))

/-- The `k`-th ancestor. -/
private def chain (parent : Array Nat) (x : Nat) : Nat → Nat
  | 0 => x
  | k + 1 => parent.getD (chain parent x k) (chain parent x k)

private theorem chain_succ' (parent : Array Nat) (x k : Nat) :
    chain parent x (k + 1) = chain parent (parent.getD x x) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show parent.getD (chain parent x (k + 1)) (chain parent x (k + 1)) = _
    rw [ih]
    rfl

private theorem chain_of_isRoot {parent : Array Nat} {x : Nat} (h : IsRoot parent x) (k : Nat) :
    chain parent x k = x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [chain, ih]
    exact h

/-- The loop returns a root of the chain in reach of its fuel. -/
private theorem rootLoop_eq_chain {parent : Array Nat} :
    ∀ (fuel k x : Nat), k ≤ fuel → IsRoot parent (chain parent x k) →
      rootLoop fuel x parent = chain parent x k
  | fuel, 0, x, _, hr => by
    cases fuel with
    | zero => rfl
    | succ fuel =>
      have hr' : parent.getD x x = x := hr
      simp only [rootLoop]
      rw [if_pos hr']
      rfl
  | 0, k + 1, _, hk, _ => absurd hk (Nat.not_succ_le_zero _)
  | fuel + 1, k + 1, x, hk, hr => by
    simp only [rootLoop]
    by_cases hx : parent.getD x x = x
    · rw [if_pos hx, chain_of_isRoot hx]
    · rw [if_neg hx]
      rw [chain_succ'] at hr ⊢
      exact rootLoop_eq_chain fuel k _ (Nat.le_of_succ_le_succ hk) hr

private theorem chain_lt {uf : UnionFind} (h : Inv uf) {x : Nat} (hx : x < uf.parent.size) :
    ∀ k, chain uf.parent x k < uf.parent.size
  | 0 => hx
  | k + 1 => by
    have := chain_lt h hx k
    simp only [chain, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem this,
      Option.getD_some]
    exact (h.2 _ this).1

private theorem rank_lt_of_not_isRoot {uf : UnionFind} (h : Inv uf) {z : Nat}
    (hz : z < uf.parent.size) (hr : ¬ IsRoot uf.parent z) :
    uf.rank[z]! < uf.rank[uf.parent.getD z z]! := by
  simp only [IsRoot, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hz,
    Option.getD_some] at hr ⊢
  exact (h.2 z hz).2.resolve_left hr

/-- Under the invariant, a seen element's chain reaches a root within the element count:
the ranks strictly increase along it, so it cannot revisit an element. -/
private theorem exists_root_chain {uf : UnionFind} (h : Inv uf) {x : Nat}
    (hx : x < uf.parent.size) :
    ∃ k, k < uf.parent.size ∧ IsRoot uf.parent (chain uf.parent x k) := by
  by_contra hno
  push Not at hno
  have hmono : ∀ j, j < uf.parent.size →
      uf.rank[chain uf.parent x j]! < uf.rank[chain uf.parent x (j + 1)]! := fun j hj =>
    rank_lt_of_not_isRoot h (chain_lt h hx j) (hno j hj)
  have hlt : ∀ i j, i < j → j ≤ uf.parent.size →
      uf.rank[chain uf.parent x i]! < uf.rank[chain uf.parent x j]! := by
    intro i j hij hj
    induction j with
    | zero => exact absurd hij (Nat.not_lt_zero _)
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hij | rfl
      · exact lt_trans (ih hij (Nat.le_of_succ_le hj)) (hmono j (Nat.lt_of_succ_le hj))
      · exact hmono i (Nat.lt_of_succ_le hj)
  let f : Fin (uf.parent.size + 1) → Fin uf.parent.size :=
    fun k => ⟨chain uf.parent x k, chain_lt h hx k⟩
  have hf : Function.Injective f := by
    intro i j hij
    simp only [f, Fin.mk.injEq] at hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt' | hlt'
    · have := hlt i j hlt' (Nat.le_of_lt_succ j.isLt)
      rw [hij] at this
      exact lt_irrefl _ this
    · have := hlt j i hlt' (Nat.le_of_lt_succ i.isLt)
      rw [hij] at this
      exact lt_irrefl _ this
  have := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at this
  omega

/-- The root of a seen element is a root of the chain, hence a fixed point in range. -/
private theorem root_spec {uf : UnionFind} (h : Inv uf) {x : Nat} (hx : x < uf.parent.size) :
    IsRoot uf.parent (rootLoop uf.parent.size x uf.parent) ∧
      rootLoop uf.parent.size x uf.parent < uf.parent.size := by
  obtain ⟨k, hk, hr⟩ := exists_root_chain h hx
  rw [rootLoop_eq_chain _ k x (Nat.le_of_lt hk) hr]
  exact ⟨hr, chain_lt h hx k⟩

private theorem rootLoop_of_ge {parent : Array Nat} {x : Nat} (hx : parent.size ≤ x) (fuel : Nat) :
    rootLoop fuel x parent = x :=
  rootLoop_eq_chain fuel 0 x (Nat.zero_le _) (by
    simp only [IsRoot, chain, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hx,
      Option.getD_none])

/-- Pointing a root at another root: the elements of its class move to the other root, and
every other element keeps its root. -/
private theorem root_set {uf : UnionFind} (h : Inv uf) {rx ry : Nat} (hrx : IsRoot uf.parent rx)
    (hry : IsRoot uf.parent ry) (hy : ry < uf.parent.size) (hne : rx ≠ ry) (x : Nat) :
    rootLoop uf.parent.size x (uf.parent.set! ry rx) =
      if rootLoop uf.parent.size x uf.parent = ry then rx
      else rootLoop uf.parent.size x uf.parent := by
  have hset : ∀ z, (uf.parent.set! ry rx).getD z z =
      if z = ry then rx else uf.parent.getD z z := by
    intro z
    by_cases hz : z = ry
    · subst hz
      simp [Array.set!, hy]
    · simp [Array.set!, hz, Ne.symm hz]
  have hsize : (uf.parent.set! ry rx).size = uf.parent.size := by simp [Array.set!]
  by_cases hx : x < uf.parent.size
  · obtain ⟨k₀, hk₀, hr₀⟩ := exists_root_chain h hx
    have hex : ∃ k, IsRoot uf.parent (chain uf.parent x k) := ⟨k₀, hr₀⟩
    have hklt : Nat.find hex < uf.parent.size := lt_of_le_of_lt (Nat.find_min' hex hr₀) hk₀
    have hkroot : IsRoot uf.parent (chain uf.parent x (Nat.find hex)) := Nat.find_spec hex
    have hroot : rootLoop uf.parent.size x uf.parent = chain uf.parent x (Nat.find hex) :=
      rootLoop_eq_chain _ _ x (Nat.le_of_lt hklt) hkroot
    have hagree : ∀ j, j ≤ Nat.find hex →
        chain (uf.parent.set! ry rx) x j = chain uf.parent x j := by
      intro j hj
      induction j with
      | zero => rfl
      | succ j ih =>
        have hnot : ¬ IsRoot uf.parent (chain uf.parent x j) :=
          Nat.find_min hex (Nat.lt_of_succ_le hj)
        have hnry : chain uf.parent x j ≠ ry := fun e => hnot (e ▸ hry)
        show (uf.parent.set! ry rx).getD (chain (uf.parent.set! ry rx) x j)
          (chain (uf.parent.set! ry rx) x j) = uf.parent.getD (chain uf.parent x j)
            (chain uf.parent x j)
        rw [ih (Nat.le_of_succ_le hj), hset, if_neg hnry]
    rw [hroot]
    by_cases hr : chain uf.parent x (Nat.find hex) = ry
    · rw [if_pos hr]
      have hnext : chain (uf.parent.set! ry rx) x (Nat.find hex + 1) = rx := by
        simp only [chain, hagree _ (Nat.le_refl _), hr, hset, ite_true]
      have hrx' : IsRoot (uf.parent.set! ry rx) rx := by
        simp only [IsRoot, hset, if_neg hne]
        exact hrx
      rw [rootLoop_eq_chain _ (Nat.find hex + 1) x hklt (by rw [hnext]; exact hrx'), hnext]
    · rw [if_neg hr]
      have hr' : IsRoot (uf.parent.set! ry rx) (chain (uf.parent.set! ry rx) x (Nat.find hex)) := by
        rw [hagree _ (Nat.le_refl _)]
        show (uf.parent.set! ry rx).getD _ _ = _
        rw [hset, if_neg hr]
        exact hkroot
      rw [rootLoop_eq_chain _ (Nat.find hex) x (Nat.le_of_lt hklt) hr', hagree _ (Nat.le_refl _)]
  · have hx' : uf.parent.size ≤ x := Nat.le_of_not_lt hx
    rw [rootLoop_of_ge hx', rootLoop_of_ge (by rw [hsize]; exact hx')]
    rw [if_neg (by omega)]

/-! ### Growing -/

private theorem getD_ensure (uf : UnionFind) (i z : Nat) :
    (uf.ensure i).parent.getD z z = uf.parent.getD z z := by
  unfold ensure
  split
  · rfl
  · simp only [Array.getD_eq_getD_getElem?]
    by_cases hz : z < uf.parent.size
    · rw [Array.getElem?_append_left hz]
    · rw [Array.getElem?_append_right (Nat.le_of_not_lt hz),
        Array.getElem?_eq_none (xs := uf.parent) (Nat.le_of_not_lt hz), Option.getD_none,
        List.getElem?_toArray, List.getElem?_map]
      by_cases hz2 : z - uf.parent.size < i + 1 - uf.parent.size
      · rw [List.getElem?_range hz2]
        simp only [Option.map_some, Option.getD_some]
        omega
      · rw [List.getElem?_eq_none (by simpa using hz2)]
        rfl

private theorem size_ensure (uf : UnionFind) (i : Nat) :
    (uf.ensure i).parent.size = if i < uf.parent.size then uf.parent.size else i + 1 := by
  unfold ensure
  split
  · rfl
  · simp
    omega

private theorem lt_size_ensure (uf : UnionFind) (i : Nat) : i < (uf.ensure i).parent.size := by
  rw [size_ensure]
  split <;> omega

private theorem size_le_size_ensure (uf : UnionFind) (i : Nat) :
    uf.parent.size ≤ (uf.ensure i).parent.size := by
  rw [size_ensure]
  split <;> omega

private theorem chain_ensure (uf : UnionFind) (i z : Nat) (k : Nat) :
    chain (uf.ensure i).parent z k = chain uf.parent z k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [chain, ih, getD_ensure]

private theorem isRoot_ensure (uf : UnionFind) (i z : Nat) :
    IsRoot (uf.ensure i).parent z ↔ IsRoot uf.parent z := by
  simp only [IsRoot, getD_ensure]

private theorem ensure_inv {uf : UnionFind} (h : Inv uf) (i : Nat) : Inv (uf.ensure i) := by
  have hs := h.1
  unfold ensure
  split
  · exact h
  · refine ⟨by simp [hs], fun j hj => ?_⟩
    simp only [Array.size_append, List.size_toArray, List.length_map, List.length_range] at hj ⊢
    by_cases hjold : j < uf.parent.size
    · have hp := h.2 j hjold
      rw [Array.getElem_append_left hjold]
      refine ⟨by omega, ?_⟩
      rcases hp.2 with hp2 | hp2
      · exact Or.inl hp2
      · right
        have hj1 : j < uf.rank.size := by omega
        have hj2 : uf.parent[j] < uf.rank.size := by omega
        rw [getElem!_pos (uf.rank ++ _) j (by simp only [Array.size_append]; omega),
          getElem!_pos (uf.rank ++ _) uf.parent[j] (by simp only [Array.size_append]; omega),
          Array.getElem_append_left hj1, Array.getElem_append_left hj2]
        rwa [getElem!_pos uf.rank j hj1, getElem!_pos uf.rank uf.parent[j] hj2] at hp2
    · rw [Array.getElem_append_right (Nat.le_of_not_lt hjold)]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      refine ⟨by omega, Or.inl (by omega)⟩

private theorem rootLoop_ensure {uf : UnionFind} (h : Inv uf) (i z : Nat) :
    rootLoop (uf.ensure i).parent.size z (uf.ensure i).parent =
      rootLoop uf.parent.size z uf.parent := by
  by_cases hz : z < uf.parent.size
  · obtain ⟨k, hk, hr⟩ := exists_root_chain h hz
    have hr' : IsRoot (uf.ensure i).parent (chain (uf.ensure i).parent z k) := by
      rw [chain_ensure, isRoot_ensure]
      exact hr
    rw [rootLoop_eq_chain _ k z (Nat.le_of_lt (lt_of_lt_of_le hk (size_le_size_ensure uf i))) hr',
      rootLoop_eq_chain _ k z (Nat.le_of_lt hk) hr, chain_ensure]
  · have hz' : uf.parent.size ≤ z := Nat.le_of_not_lt hz
    have hroot : IsRoot uf.parent z := by
      simp only [IsRoot, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hz', Option.getD_none]
    rw [rootLoop_of_ge hz',
      rootLoop_eq_chain _ 0 z (Nat.zero_le _) ((isRoot_ensure uf i z).mpr hroot)]
    rfl

/-- The root `find` returns is the loop's on the ungrown structure. -/
private theorem find_fst {uf : UnionFind} (h : Inv uf) (x : Nat) :
    (uf.find x).1 = rootLoop uf.parent.size x uf.parent :=
  rootLoop_ensure h x x

/-! ### The public view -/

/-- The empty structure keeps the invariant. -/
theorem empty_inv : Inv empty :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- A `find` keeps the invariant: it only grows the structure by singletons. -/
theorem find_inv {uf : UnionFind} (h : Inv uf) (x : Nat) : Inv (uf.find x).2 :=
  ensure_inv h x

/-- A `find` never splits a class. -/
theorem same_find_mono {uf : UnionFind} (h : Inv uf) {v w : Nat} (hvw : uf.Same v w) (x : Nat) :
    (uf.find x).2.Same v w := by
  unfold Same at hvw ⊢
  rw [find_fst h, find_fst h] at hvw
  rw [find_fst (find_inv h x), find_fst (find_inv h x)]
  show rootLoop (uf.ensure x).parent.size v (uf.ensure x).parent =
    rootLoop (uf.ensure x).parent.size w (uf.ensure x).parent
  rw [rootLoop_ensure h x v, rootLoop_ensure h x w, hvw]

private theorem size_set! (xs : Array Nat) (i a : Nat) : (xs.set! i a).size = xs.size := by
  simp [Array.set!]

private theorem getElem!_set! (xs : Array Nat) {i : Nat} (hi : i < xs.size) (a k : Nat) :
    (xs.set! i a)[k]! = if i = k then a else xs[k]! := by
  by_cases hk : k < xs.size
  · rw [getElem!_pos (xs.set! i a) k (by rw [size_set!]; exact hk), getElem!_pos xs k hk]
    simp only [Array.set!, Array.getElem_setIfInBounds hk]
  · have hk' : ¬ k < (xs.set! i a).size := by
      rw [size_set!]
      exact hk
    rw [getElem!_neg (xs.set! i a) k hk', getElem!_neg xs k hk, if_neg (by omega)]

private theorem rank_getD_eq {uf : UnionFind} (h : Inv uf) {r : Nat} (hr : r < uf.parent.size) :
    uf.rank.getD r 0 = uf.rank[r]! := by
  rw [getElem!_pos _ _ (by rw [h.1]; exact hr), Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by rw [h.1]; exact hr), Option.getD_some]

/-- The union's structure before linking: both arguments seen, the invariant kept. -/
private theorem union_setup {uf : UnionFind} (h : Inv uf) (x y : Nat) :
    Inv ((uf.ensure x).ensure y) ∧ x < ((uf.ensure x).ensure y).parent.size ∧
      y < ((uf.ensure x).ensure y).parent.size :=
  ⟨ensure_inv (ensure_inv h x) y,
    lt_of_lt_of_le (lt_size_ensure uf x) (size_le_size_ensure _ y), lt_size_ensure _ y⟩

/-- Pointing a root at a root of larger rank keeps the invariant. -/
private theorem inv_set {uf : UnionFind} (h : Inv uf) {a b : Nat} (hblt : b < uf.parent.size)
    (hrank : uf.rank[a]! < uf.rank[b]!) : Inv { uf with parent := uf.parent.set! a b } := by
  refine ⟨by simp [Array.set!, h.1], fun j hj => ?_⟩
  simp only [Array.set!, Array.size_setIfInBounds] at hj ⊢
  simp only [Array.getElem_setIfInBounds hj]
  by_cases hja : a = j
  · subst hja
    simp only [ite_true]
    exact ⟨hblt, Or.inr hrank⟩
  · simp only [hja, ite_false]
    exact h.2 j hj

/-- Pointing a root at a root of equal rank and bumping that rank keeps the invariant. -/
private theorem inv_set_tie {uf : UnionFind} (h : Inv uf) {a b : Nat} (hb : IsRoot uf.parent b)
    (hblt : b < uf.parent.size) (hne : b ≠ a)
    (hrank : uf.rank[a]! = uf.rank[b]!) :
    Inv { uf with parent := uf.parent.set! a b, rank := uf.rank.set! b (uf.rank[b]! + 1) } := by
  have hs := h.1
  refine ⟨by simp [Array.set!, hs], fun j hj => ?_⟩
  simp only [size_set!] at hj ⊢
  have hbr : b < uf.rank.size := by omega
  simp only [getElem!_set! uf.rank hbr]
  have hpar : (uf.parent.set! a b)[j] = if a = j then b else uf.parent[j] := by
    simp only [Array.set!, Array.getElem_setIfInBounds hj]
  rw [hpar]
  by_cases hja : a = j
  · subst hja
    simp only [ite_true]
    refine ⟨hblt, Or.inr ?_⟩
    simp only [hne, ite_false]
    omega
  · simp only [hja, ite_false]
    have hp := h.2 j hj
    refine ⟨hp.1, ?_⟩
    rcases hp.2 with hp2 | hp2
    · exact Or.inl hp2
    · right
      have hroot : uf.parent[b] = b := by
        simpa only [IsRoot, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hblt,
          Option.getD_some] using hb
      have hjb : ¬ b = j := fun e => by
        subst e
        rw [hroot] at hp2
        exact lt_irrefl _ hp2
      rw [if_neg hjb]
      by_cases hpb : b = uf.parent[j]
      · rw [if_pos hpb]
        rw [← hpb] at hp2
        omega
      · rw [if_neg hpb]
        exact hp2

/-- A union keeps the invariant: by rank, tie included. -/
theorem union_inv {uf : UnionFind} (h : Inv uf) (x y : Nat) : Inv (uf.union x y) := by
  obtain ⟨h', hx, hy⟩ := union_setup h x y
  obtain ⟨hrootx, hxlt⟩ := root_spec h' hx
  obtain ⟨hrooty, hylt⟩ := root_spec h' hy
  unfold union
  dsimp only
  split_ifs with h1 h2 h3
  · exact h'
  · exact inv_set h' hylt (by rwa [rank_getD_eq h' hxlt, rank_getD_eq h' hylt] at h2)
  · exact inv_set h' hxlt (by rwa [rank_getD_eq h' hxlt, rank_getD_eq h' hylt] at h3)
  · rw [rank_getD_eq h' hxlt] at h2 h3 ⊢
    rw [rank_getD_eq h' hylt] at h2 h3
    exact inv_set_tie h' hrootx hxlt h1 (by omega)

/-- The root of any element after a union: the moved root's class takes the other root. -/
private theorem root_union {uf : UnionFind} (h : Inv uf) (x y z : Nat) :
    rootLoop (uf.union x y).parent.size z (uf.union x y).parent =
      let uf' := (uf.ensure x).ensure y
      let rx := rootLoop uf'.parent.size x uf'.parent
      let ry := rootLoop uf'.parent.size y uf'.parent
      let r := rootLoop uf'.parent.size z uf'.parent
      if rx = ry then r
      else if uf'.rank.getD rx 0 < uf'.rank.getD ry 0 then (if r = rx then ry else r)
      else (if r = ry then rx else r) := by
  obtain ⟨h', hx, hy⟩ := union_setup h x y
  obtain ⟨hrootx, hxlt⟩ := root_spec h' hx
  obtain ⟨hrooty, hylt⟩ := root_spec h' hy
  unfold union
  dsimp only
  obtain ⟨uf', huf'⟩ : ∃ u, u = (uf.ensure x).ensure y := ⟨_, rfl⟩
  rw [← huf'] at hrootx hxlt hrooty hylt h' ⊢
  obtain ⟨rx, hrx⟩ : ∃ r, r = rootLoop uf'.parent.size x uf'.parent := ⟨_, rfl⟩
  obtain ⟨ry, hry⟩ : ∃ r, r = rootLoop uf'.parent.size y uf'.parent := ⟨_, rfl⟩
  rw [← hrx] at hrootx hxlt ⊢
  rw [← hry] at hrooty hylt ⊢
  by_cases h1 : rx = ry
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : uf'.rank.getD rx 0 < uf'.rank.getD ry 0
    · rw [if_pos h2, if_pos h2]
      dsimp only
      rw [size_set!]
      exact root_set h' hrooty hrootx hxlt (Ne.symm h1) z
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : uf'.rank.getD ry 0 < uf'.rank.getD rx 0
      · rw [if_pos h3]
        dsimp only
        rw [size_set!]
        exact root_set h' hrootx hrooty hylt h1 z
      · rw [if_neg h3]
        dsimp only
        rw [size_set!]
        exact root_set h' hrootx hrooty hylt h1 z

theorem same_union_self {uf : UnionFind} (h : Inv uf) (x y : Nat) : (uf.union x y).Same x y := by
  unfold Same
  rw [find_fst (union_inv h x y), find_fst (union_inv h x y), root_union h, root_union h]
  dsimp only
  split_ifs <;> first | rfl | simp_all

theorem same_union_mono {uf : UnionFind} (h : Inv uf) {v w : Nat} (hvw : uf.Same v w)
    (x y : Nat) : (uf.union x y).Same v w := by
  unfold Same at hvw ⊢
  rw [find_fst h, find_fst h] at hvw
  rw [find_fst (union_inv h x y), find_fst (union_inv h x y), root_union h, root_union h]
  dsimp only
  rw [rootLoop_ensure (ensure_inv h x) y v, rootLoop_ensure h x v,
    rootLoop_ensure (ensure_inv h x) y w, rootLoop_ensure h x w, hvw]

/-- The dense view is `find`; an unseen element is its own key. -/
theorem rootOf_getD_eq {uf : UnionFind} (h : Inv uf) (v : Nat) :
    uf.rootOf.getD v v = (uf.find v).1 := by
  rw [find_fst h]
  simp only [rootOf, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
  by_cases hv : v < uf.parent.size
  · rw [List.getElem?_range hv]
    rfl
  · rw [List.getElem?_eq_none (by simpa using hv)]
    exact (rootLoop_of_ge (Nat.le_of_not_lt hv) _).symm

end UnionFind

end Snarky.Kimchi
