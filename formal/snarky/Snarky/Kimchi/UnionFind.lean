/-!
# Pure union-find

Port of `Data.UnionFind.Mutable` (packages/union-find/src/Data/UnionFind/Mutable.purs),
the int-keyed parent/rank union-find the kimchi backend's wire state threads. The PS
structure is mutable (`STArray` parent/rank, path halving, union by rank); this rendering
is pure and drops the halving. That drop is semantics-preserving, not an approximation:
path halving only re-points non-root elements at ancestors — every root, every rank, and
therefore every subsequent union decision and every `find` result is identical with or
without it. What must be mirrored exactly is the union-by-rank rule itself (smaller rank
under larger; on a tie the SECOND root is pointed at the first, whose rank bumps),
because the representative choice is observable through `rootOf` until the wiring pass is
shown to consume only the partition (recorded hypothesis, validated at the CS-equality
step of `formal/docs/snarky-kimchi-alignment.md`).

Name map: `fresh` → `empty` (pure value, no allocation), `find`/`union`/`rootOf`/
`equivalenceClasses` keep their names; `ensure` stays the internal growth step. The
`Effect`/`ST` wrappers disappear; `find` and `union` return the grown structure instead.

Everything is structural (`Array` get/set, fuel-bounded root chase), so the module is
`decide`-friendly throughout.
-/

namespace Snarky.Kimchi

/-- Int-keyed union-find: dense parent and rank arrays, elements `0 .. parent.size - 1`.
An element outside the arrays is implicitly its own singleton class until `ensure`d in
(PS grows the backing `STArray`s the same way). -/
structure UnionFind where
  /-- Parent pointers, dense by element: a root points at itself. -/
  parent : Array Nat
  /-- Union-by-rank ranks, in lockstep with `parent`. -/
  rank : Array Nat
  deriving Repr, DecidableEq

namespace UnionFind

/-- The empty structure — no elements seen (PS `fresh`, minus the allocation). -/
def empty : UnionFind := ⟨#[], #[]⟩

/-- Grow the arrays so element `i` exists; new elements are their own parent with rank
`0` — singleton classes (PS `ensure`). -/
private def ensure (i : Nat) (uf : UnionFind) : UnionFind :=
  if i < uf.parent.size then uf
  else
    let grow := List.range (i + 1 - uf.parent.size) |>.map (· + uf.parent.size)
    ⟨uf.parent ++ grow.toArray, uf.rank ++ (grow.map fun _ => 0).toArray⟩

/-- Chase parent pointers to the root, fuel-bounded (PS `rootLoop`, minus the halving
writes — see the module docstring for why dropping them changes nothing). The fuel is
the element count: parent chains are acyclic and shorter than the array. -/
private def rootLoop (fuel x : Nat) (parent : Array Nat) : Nat :=
  match fuel with
  | 0 => x
  | fuel + 1 =>
    let p := parent.getD x x
    if p = x then x else rootLoop fuel p parent

/-- The representative of `x`, creating it as a singleton if unseen (PS `find`). Returns
the possibly-grown structure alongside. -/
def find (x : Nat) (uf : UnionFind) : Nat × UnionFind :=
  let uf := uf.ensure x
  (rootLoop uf.parent.size x uf.parent, uf)

/-- Merge the classes of `x` and `y` by rank (PS `union`, rule mirrored exactly): the
smaller-rank root is pointed at the larger; on a tie, `y`'s root is pointed at `x`'s,
whose rank bumps. -/
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

/-- The root of every seen element, dense by element index (PS `rootOf`) — the frozen
view the wiring pass consumes. -/
def rootOf (uf : UnionFind) : Array Nat :=
  (List.range uf.parent.size).map (fun i => rootLoop uf.parent.size i uf.parent)
    |>.toArray

/-- Insert `i` into the class list of `root` inside an assoc list sorted by root — the
structural stand-in for PS's `Map.insertWith append` (ascending-key iteration falls out
of keeping the list sorted; `List.mergeSort` would be kernel-opaque). -/
private def insertGrouped (root i : Nat) :
    List (Nat × List Nat) → List (Nat × List Nat)
  | [] => [(root, [i])]
  | (r, ms) :: rest =>
    if root = r then (r, ms ++ [i]) :: rest
    else if root < r then (root, [i]) :: (r, ms) :: rest
    else (r, ms) :: insertGrouped root i rest

/-- Equivalence classes, each ascending, ordered by root (PS `equivalenceClasses`, whose
`Map.values` iterates keys ascending). Test-path only in PS; here it also feeds the
`decide` examples below. -/
def equivalenceClasses (uf : UnionFind) : List (List Nat) :=
  let grouped := (uf.rootOf.toList.zipIdx).foldl
    (fun acc (ri : Nat × Nat) => insertGrouped ri.1 ri.2 acc) []
  grouped.map (·.2)

end UnionFind

/-! ## Examples (the union-find package's own spec rows, as `decide` checks) -/

/-- Two unions chaining three elements into one class, with a bystander — the exhibit
the `decide` examples below run on. -/
def egUF : UnionFind :=
  UnionFind.empty.union 0 1 |>.union 1 2 |>.ensure 3

/-- All three chained elements share one representative; the bystander keeps its own. -/
example : (egUF.find 0).1 = (egUF.find 2).1 ∧ (egUF.find 3).1 = 3 := by decide

/-- The classes come out grouped, each ascending, ordered by root. -/
example : egUF.equivalenceClasses = [[0, 1, 2], [3]] := by decide

/-- The tie rule: on equal ranks the second root joins the first (`0 ∪ 1` roots at `0`). -/
example : ((UnionFind.empty.union 0 1).find 1).1 = 0 := by decide

end Snarky.Kimchi
