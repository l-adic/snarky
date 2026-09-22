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

end UnionFind

end Snarky.Kimchi
