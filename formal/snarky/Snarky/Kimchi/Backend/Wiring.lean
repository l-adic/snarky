import Snarky.Kimchi.Backend.Assemble
import Std.Data.HashMap.Lemmas
import Mathlib.Data.List.Nodup

/-!
# The wire map's cycles

The assembly wires each class of permutation cells in a cycle: the cells carrying one
root, in row-major order, each pointing at the next and the last at the first. The wire
map builds the classes in one pass over the rows and the cycles in a second; the two
passes are read here as folds, and the map is characterised at every cell of a class.
Along a cycle, any assignment of values that agrees across each wire agrees across the
class, which is what a satisfying table's copy constraints give.

## Main definitions

- `keyedCells`: the wired cells with their roots, in row-major order.
- `classCells`: one root's cells, in row-major order.

## Main results

- `wireMap_getElem?`: the wire map sends each cell of a class to the next, the last to
  the first.
- `length_assembleGates`, `getElem_assembleGates`: an assembled row's tag, coefficients
  and wiring targets.
- `classCells_bounds`, `mem_classCells_of_label`: a class's cells are labelled cells of the
  wired columns, and every such cell is in its root's class.
- `classCells_values_eq`: values agreeing across every wire of a class agree across it.
-/

namespace Snarky.Kimchi

variable {F : Type}

/-! ## The classes -/

/-- The class table: each root's wired cells so far, in row-major order. -/
private abbrev Classes := Std.HashMap Variable (Array (Nat × Nat))

/-- Append a cell to its root's class. -/
private def pushCell (c : Nat × Nat) : Option (Array (Nat × Nat)) → Option (Array (Nat × Nat))
  | none => some #[c]
  | some cs => some (cs.push c)

private theorem pushCell_eq (c : Nat × Nat) (o : Option (Array (Nat × Nat))) :
    pushCell c o = some ((o.getD #[]).push c) := by
  cases o <;> rfl

/-- The first pass's inner body: one cell of row `i` into its class, the column advanced. -/
private def classInner (roots : Array Variable) (i : Nat) (mv : Option Variable)
    (r : MProd Classes Nat) : Id (ForInStep (MProd Classes Nat)) := do
  let mut classes := r.fst
  let mut j := r.snd
  if let some v := mv then
    classes := classes.alter (roots.getD v v) fun
      | none => some #[(i, j)]
      | some cs => some (cs.push (i, j))
  j := j + 1
  pure (ForInStep.yield ⟨classes, j⟩)

/-- The first pass's outer body: one row's wired cells into their classes, the row
advanced. -/
private def classOuter (roots : Array Variable) (row : KimchiRow F) (r : MProd Classes Nat) :
    Id (ForInStep (MProd Classes Nat)) := do
  let r' ← forIn (row.vars.toList.take 7) (⟨r.fst, 0⟩ : MProd Classes Nat)
    (classInner roots r.snd)
  pure (ForInStep.yield ⟨r'.fst, r.snd + 1⟩)

/-- The second pass's body: one class's cells wired in a cycle. -/
private def cycleOuter (x : Variable × Array (Nat × Nat)) (m : Std.HashMap (Nat × Nat) Wire) :
    Id (ForInStep (Std.HashMap (Nat × Nat) Wire)) := do
  let cells := x.2
  let mut m := m
  for k in [0:cells.size] do
    let t := cells[(k + 1) % cells.size]!
    m := m.insert cells[k]! ⟨t.1, t.2⟩
  pure (ForInStep.yield m)

/-- The wire map as its two passes over named bodies. -/
private theorem wireMap_eq (roots : Array Variable) (rows : List (KimchiRow F)) :
    wireMap roots rows = Id.run (do
      let r ← forIn rows (⟨∅, 0⟩ : MProd Classes Nat) (classOuter roots)
      forIn r.fst (∅ : Std.HashMap (Nat × Nat) Wire) cycleOuter) := by
  rfl

/-- A row's wired cells from column `j`, keyed by root. -/
private def rowKeyed (roots : Array Variable) (i : Nat) (cells : List (Option Variable))
    (j : Nat) : List (Variable × (Nat × Nat)) :=
  (cells.zipIdx j).filterMap fun (mv, jj) => mv.map fun v => (roots.getD v v, (i, jj))

/-- The rows' wired cells from row `i`, keyed by root, in row-major order. -/
private def keyedFrom (roots : Array Variable) (rows : List (KimchiRow F)) (i : Nat) :
    List (Variable × (Nat × Nat)) :=
  (rows.zipIdx i).flatMap fun (row, ii) => rowKeyed roots ii (row.vars.toList.take 7) 0

/-- The wired cells of the rows with their roots, in row-major order. -/
def keyedCells (roots : Array Variable) (rows : List (KimchiRow F)) :
    List (Variable × (Nat × Nat)) :=
  keyedFrom roots rows 0

/-- The cells of one root among keyed cells, in order. -/
private def cellsOf (k : Variable) (kcs : List (Variable × (Nat × Nat))) : List (Nat × Nat) :=
  kcs.filterMap fun kc => if kc.1 = k then some kc.2 else none

/-- The cells of one root, in row-major order. -/
def classCells (roots : Array Variable) (rows : List (KimchiRow F)) (k : Variable) :
    List (Nat × Nat) :=
  cellsOf k (keyedCells roots rows)

/-- The class table extended by keyed cells in order. -/
private def classFold (init : Classes) (kcs : List (Variable × (Nat × Nat))) : Classes :=
  kcs.foldl (fun m kc => m.alter kc.1 (pushCell kc.2)) init

private theorem classFold_append (init : Classes) (a b : List (Variable × (Nat × Nat))) :
    classFold init (a ++ b) = classFold (classFold init a) b :=
  List.foldl_append

private theorem forIn_classInner (roots : Array Variable) (i : Nat)
    (cells : List (Option Variable)) (classes : Classes) (j : Nat) :
    forIn (m := Id) cells (⟨classes, j⟩ : MProd Classes Nat) (classInner roots i) =
      ⟨classFold classes (rowKeyed roots i cells j), j + cells.length⟩ := by
  induction cells generalizing classes j with
  | nil => rfl
  | cons mv rest ih =>
    cases mv with
    | none =>
      simp only [List.forIn_cons]
      show forIn rest (⟨classes, j + 1⟩ : MProd Classes Nat) (classInner roots i) = _
      rw [ih]
      simp [rowKeyed, List.zipIdx_cons, classFold, Nat.add_assoc, Nat.add_comm 1]
    | some v =>
      simp only [List.forIn_cons]
      show forIn rest (⟨classes.alter (roots.getD v v) (pushCell (i, j)), j + 1⟩ :
        MProd Classes Nat) (classInner roots i) = _
      rw [ih]
      simp [rowKeyed, List.zipIdx_cons, classFold, Nat.add_assoc, Nat.add_comm 1]

private theorem forIn_classOuter (roots : Array Variable) (rows : List (KimchiRow F))
    (classes : Classes) (i : Nat) :
    forIn (m := Id) rows (⟨classes, i⟩ : MProd Classes Nat) (classOuter roots) =
      ⟨classFold classes (keyedFrom roots rows i), i + rows.length⟩ := by
  induction rows generalizing classes i with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.forIn_cons]
    show forIn rest (⟨(forIn (m := Id) (row.vars.toList.take 7)
      (⟨classes, 0⟩ : MProd Classes Nat) (classInner roots i)).fst, i + 1⟩ :
        MProd Classes Nat) (classOuter roots) = _
    rw [forIn_classInner, ih]
    simp [keyedFrom, List.zipIdx_cons, classFold_append, Nat.add_assoc, Nat.add_comm 1]

private theorem getElem?_classFold (init : Classes) (kcs : List (Variable × (Nat × Nat)))
    (k : Variable) :
    (classFold init kcs)[k]? =
      if cellsOf k kcs = [] then init[k]?
      else some ((init[k]?.getD #[]) ++ (cellsOf k kcs).toArray) := by
  induction kcs generalizing init with
  | nil => simp [classFold, cellsOf]
  | cons kc rest ih =>
    have h : classFold init (kc :: rest) = classFold (init.alter kc.1 (pushCell kc.2)) rest :=
      rfl
    rw [h, ih]
    by_cases hk : kc.1 = k
    · subst hk
      have hc : cellsOf kc.1 (kc :: rest) = kc.2 :: cellsOf kc.1 rest := by simp [cellsOf]
      rw [hc, Std.HashMap.getElem?_alter_self, pushCell_eq, List.toArray_cons,
        Array.push_eq_append]
      by_cases hrest : cellsOf kc.1 rest = [] <;> simp [hrest]
    · have hc : cellsOf k (kc :: rest) = cellsOf k rest := by simp [cellsOf, hk]
      rw [hc]
      simp [Std.HashMap.getElem?_alter, hk]

/-! ## The cycles -/

/-- The wire at a cycle position: the next cell, the last wrapping to the first. -/
private def cycleWire (cells : Array (Nat × Nat)) (k : Nat) : Wire :=
  ⟨(cells[(k + 1) % cells.size]!).1, (cells[(k + 1) % cells.size]!).2⟩

/-- The second pass's inner body: one cell wired to the next. -/
private def cycleInner (cells : Array (Nat × Nat)) (k : Nat) (m : Std.HashMap (Nat × Nat) Wire) :
    Id (ForInStep (Std.HashMap (Nat × Nat) Wire)) := do
  let t := cells[(k + 1) % cells.size]!
  pure (ForInStep.yield (m.insert cells[k]! ⟨t.1, t.2⟩))

/-- The wires of a cycle over the listed positions, inserted in order. -/
private def cycleFold (cells : Array (Nat × Nat)) (ks : List Nat)
    (m : Std.HashMap (Nat × Nat) Wire) : Std.HashMap (Nat × Nat) Wire :=
  ks.foldl (fun m k => m.insert cells[k]! (cycleWire cells k)) m

private theorem forIn_cycleInner (cells : Array (Nat × Nat)) (a n step : Nat)
    (m : Std.HashMap (Nat × Nat) Wire) :
    forIn (m := Id) (List.range' a n step) m (cycleInner cells) =
      cycleFold cells (List.range' a n step) m := by
  induction n generalizing a m with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons]
    show forIn (List.range' (a + step) n step) (m.insert cells[a]! (cycleWire cells a))
      (cycleInner cells) = _
    rw [ih]
    rfl

private theorem cycleOuter_eq (x : Variable × Array (Nat × Nat))
    (m : Std.HashMap (Nat × Nat) Wire) :
    cycleOuter x m = ForInStep.yield (cycleFold x.2 (List.range' 0 x.2.size) m) := by
  show (do
      let m' ← forIn (m := Id) [0:x.2.size] m (cycleInner x.2)
      pure (ForInStep.yield m')) = _
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_cycleInner]
  show ForInStep.yield (cycleFold x.2 (List.range' _ _ _) m) = _
  simp [Std.Legacy.Range.size]

/-- The cycles of the listed classes, in order. -/
private def cyclesFold (xs : List (Variable × Array (Nat × Nat)))
    (m : Std.HashMap (Nat × Nat) Wire) : Std.HashMap (Nat × Nat) Wire :=
  xs.foldl (fun m x => cycleFold x.2 (List.range' 0 x.2.size) m) m

private theorem forIn_cycleOuter (xs : List (Variable × Array (Nat × Nat)))
    (m : Std.HashMap (Nat × Nat) Wire) :
    forIn (m := Id) xs m cycleOuter = cyclesFold xs m := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, cycleOuter_eq]
    show forIn xs (cycleFold x.2 (List.range' 0 x.2.size) m) cycleOuter = _
    rw [ih]
    rfl

private theorem getElem?_cycleFold_of_notMem (cells : Array (Nat × Nat)) (ks : List Nat)
    (m : Std.HashMap (Nat × Nat) Wire) (c : Nat × Nat) (hks : ∀ k ∈ ks, k < cells.size)
    (hc : c ∉ cells.toList) : (cycleFold cells ks m)[c]? = m[c]? := by
  induction ks generalizing m with
  | nil => rfl
  | cons k ks ih =>
    have hk := hks k (List.mem_cons_self ..)
    rw [cycleFold, List.foldl_cons, ← cycleFold,
      ih _ (fun k hk => hks k (List.mem_cons_of_mem _ hk)), Std.HashMap.getElem?_insert]
    have : cells[k]! ≠ c := by
      rw [getElem!_pos cells k hk]
      intro h
      exact hc (h ▸ Array.getElem_mem_toList hk)
    simp [this]

private theorem getElem?_cycleFold_of_notMem_index (cells : Array (Nat × Nat))
    (hnd : cells.toList.Nodup) (ks : List Nat) (hks : ∀ k ∈ ks, k < cells.size) (q : Nat)
    (hq : q < cells.size) (hqks : q ∉ ks) (m : Std.HashMap (Nat × Nat) Wire) :
    (cycleFold cells ks m)[cells[q]]? = m[cells[q]]? := by
  induction ks generalizing m with
  | nil => rfl
  | cons k ks ih =>
    have hk := hks k (List.mem_cons_self ..)
    rw [cycleFold, List.foldl_cons, ← cycleFold,
      ih (fun k hk => hks k (List.mem_cons_of_mem _ hk)) (fun h => hqks (List.mem_cons_of_mem _ h)),
      Std.HashMap.getElem?_insert]
    have hne : cells[k]! ≠ cells[q] := by
      rw [getElem!_pos cells k hk]
      intro h
      have := (List.getElem_inj (xs := cells.toList) (h₀ := by simpa using hk)
        (h₁ := by simpa using hq) hnd).mp (by simpa using h)
      exact hqks (this ▸ List.mem_cons_self ..)
    simp [hne]

private theorem getElem?_cycleFold (cells : Array (Nat × Nat)) (hnd : cells.toList.Nodup)
    (ks : List Nat) (hks : ∀ k ∈ ks, k < cells.size) (hnd' : ks.Nodup)
    (m : Std.HashMap (Nat × Nat) Wire) (q : Nat) (hq : q ∈ ks) :
    (cycleFold cells ks m)[cells[q]!]? = some (cycleWire cells q) := by
  induction ks generalizing m with
  | nil => exact (List.not_mem_nil hq).elim
  | cons k ks ih =>
    have hk := hks k (List.mem_cons_self ..)
    have hks' := fun k hk => hks k (List.mem_cons_of_mem _ hk)
    rw [cycleFold, List.foldl_cons, ← cycleFold]
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [getElem!_pos cells q hk,
        getElem?_cycleFold_of_notMem_index cells hnd ks hks' q hk (List.nodup_cons.mp hnd').1,
        Std.HashMap.getElem?_insert]
      simp
    · exact ih hks' (List.nodup_cons.mp hnd').2 _ hq

private theorem getElem?_cyclesFold_of_notMem (xs : List (Variable × Array (Nat × Nat)))
    (m : Std.HashMap (Nat × Nat) Wire) (c : Nat × Nat) (hc : ∀ x ∈ xs, c ∉ x.2.toList) :
    (cyclesFold xs m)[c]? = m[c]? := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih =>
    rw [cyclesFold, List.foldl_cons, ← cyclesFold,
      ih _ (fun x hx => hc x (List.mem_cons_of_mem _ hx)),
      getElem?_cycleFold_of_notMem _ _ _ _
        (fun k hk => by simpa using (List.mem_range'_1.mp hk).2) (hc x (List.mem_cons_self ..))]

private theorem getElem?_cyclesFold (xs : List (Variable × Array (Nat × Nat)))
    (hnd : ∀ x ∈ xs, x.2.toList.Nodup)
    (hdisj : xs.Pairwise fun x y => ∀ c ∈ x.2.toList, c ∉ y.2.toList)
    (m : Std.HashMap (Nat × Nat) Wire) (x : Variable × Array (Nat × Nat)) (hx : x ∈ xs) (q : Nat)
    (hq : q < x.2.size) : (cyclesFold xs m)[x.2[q]]? = some (cycleWire x.2 q) := by
  induction xs generalizing m with
  | nil => exact (List.not_mem_nil hx).elim
  | cons y ys ih =>
    rw [cyclesFold, List.foldl_cons, ← cyclesFold]
    obtain ⟨hy, hdisj'⟩ := List.pairwise_cons.mp hdisj
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [getElem?_cyclesFold_of_notMem _ _ _
        (fun y' hy' => hy y' hy' _ (Array.getElem_mem_toList hq)), ← getElem!_pos x.2 q hq]
      exact getElem?_cycleFold x.2 (hnd x (List.mem_cons_self ..)) _
        (fun k hk => by simpa using (List.mem_range'_1.mp hk).2) (List.nodup_range' ..) m q
        (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
    · exact ih (fun x hx => hnd x (List.mem_cons_of_mem _ hx)) hdisj' _ hx

/-! ## Row-major order -/

/-- Row-major order on cells. -/
private def Before (a b : Nat × Nat) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

private theorem Before.ne {a b : Nat × Nat} (h : Before a b) : a ≠ b := by
  rintro rfl
  rcases h with h | ⟨-, h⟩ <;> exact Nat.lt_irrefl _ h

private theorem mem_rowKeyed (roots : Array Variable) (i : Nat) (cells : List (Option Variable))
    (j : Nat) {kc : Variable × (Nat × Nat)} (h : kc ∈ rowKeyed roots i cells j) :
    kc.2.1 = i ∧ j ≤ kc.2.2 := by
  simp only [rowKeyed, List.mem_filterMap] at h
  obtain ⟨⟨mv, jj⟩, hmem, hmap⟩ := h
  cases mv with
  | none => simp at hmap
  | some v =>
    simp only [Option.map_some, Option.some.injEq] at hmap
    subst hmap
    exact ⟨rfl, (List.mem_zipIdx hmem).1⟩

private theorem mem_rowKeyed_iff (roots : Array Variable) (i : Nat)
    (cells : List (Option Variable)) (j : Nat) (k : Variable) (c : Nat × Nat) :
    (k, c) ∈ rowKeyed roots i cells j ↔
      c.1 = i ∧ j ≤ c.2 ∧ ∃ (h : c.2 - j < cells.length) (v : Variable),
        cells[c.2 - j] = some v ∧ roots.getD v v = k := by
  simp only [rowKeyed, List.mem_filterMap]
  constructor
  · rintro ⟨⟨mv, jj⟩, hmem, hmap⟩
    cases mv with
    | none => simp at hmap
    | some v =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmap
      obtain ⟨rfl, rfl⟩ := hmap
      obtain ⟨h1, h2, h3⟩ := List.mem_zipIdx hmem
      exact ⟨rfl, h1, by omega, v, h3.symm, rfl⟩
  · rintro ⟨h1, h2, h3, v, hv, hk⟩
    refine ⟨(some v, c.2), ?_, by show some (roots.getD v v, (i, c.2)) = some (k, c); rw [hk, ← h1]⟩
    rw [List.mem_iff_getElem]
    exact ⟨c.2 - j, by simpa using h3, by rw [List.getElem_zipIdx, hv]; congr 2; omega⟩

private theorem pairwise_rowKeyed (roots : Array Variable) (i : Nat)
    (cells : List (Option Variable)) (j : Nat) :
    (rowKeyed roots i cells j).Pairwise fun a b => Before a.2 b.2 := by
  induction cells generalizing j with
  | nil => simp [rowKeyed]
  | cons mv rest ih =>
    cases mv with
    | none =>
      have e : rowKeyed roots i (none :: rest) j = rowKeyed roots i rest (j + 1) := rfl
      rw [e]
      exact ih (j + 1)
    | some v =>
      have e : rowKeyed roots i (some v :: rest) j =
        (roots.getD v v, (i, j)) :: rowKeyed roots i rest (j + 1) := rfl
      rw [e]
      refine List.Pairwise.cons (fun b hb => ?_) (ih (j + 1))
      have := mem_rowKeyed roots i rest (j + 1) hb
      exact Or.inr ⟨this.1.symm, by show j < b.2.2; omega⟩

private theorem keyedFrom_cons (roots : Array Variable) (row : KimchiRow F)
    (rest : List (KimchiRow F)) (i : Nat) :
    keyedFrom roots (row :: rest) i =
      rowKeyed roots i (row.vars.toList.take 7) 0 ++ keyedFrom roots rest (i + 1) := rfl

private theorem mem_keyedFrom (roots : Array Variable) (rows : List (KimchiRow F)) (i : Nat)
    {kc : Variable × (Nat × Nat)} (h : kc ∈ keyedFrom roots rows i) : i ≤ kc.2.1 := by
  induction rows generalizing i with
  | nil => exact (List.not_mem_nil h).elim
  | cons row rest ih =>
    rw [keyedFrom_cons, List.mem_append] at h
    rcases h with h | h
    · exact (mem_rowKeyed roots i _ 0 h).1.symm.le
    · exact Nat.le_of_succ_le (ih (i + 1) h)

private theorem mem_keyedFrom_iff (roots : Array Variable) (rows : List (KimchiRow F)) (i : Nat)
    (k : Variable) (c : Nat × Nat) :
    (k, c) ∈ keyedFrom roots rows i ↔
      i ≤ c.1 ∧ ∃ (hr : c.1 - i < rows.length) (hj : c.2 < 7) (v : Variable),
        rows[c.1 - i].vars[c.2]'(by omega) = some v ∧ roots.getD v v = k := by
  induction rows generalizing i with
  | nil =>
    simp only [keyedFrom, List.zipIdx_nil, List.flatMap_nil, List.not_mem_nil, false_iff,
      List.length_nil, not_and]
    rintro - ⟨hr, -⟩
    exact absurd hr (Nat.not_lt_zero _)
  | cons row rest ih =>
    rw [keyedFrom_cons, List.mem_append, mem_rowKeyed_iff, ih]
    constructor
    · rintro (⟨h1, -, h3, v, hv, hk⟩ | ⟨h1, h2, h3, v, hv, hk⟩)
      · refine ⟨h1.symm.le, by simp; omega, by simpa using h3, v, ?_, hk⟩
        rw [List.getElem_take, Vector.getElem_toList] at hv
        simpa [h1] using hv
      · refine ⟨by omega, by simp; omega, h3, v, ?_, hk⟩
        have e : c.1 - i = (c.1 - (i + 1)) + 1 := by omega
        simpa [e] using hv
    · rintro ⟨h1, h2, h3, v, hv, hk⟩
      by_cases hc : c.1 = i
      · left
        refine ⟨hc, Nat.zero_le _, by simp; omega, v, ?_, hk⟩
        rw [List.getElem_take, Vector.getElem_toList]
        simpa [hc] using hv
      · right
        refine ⟨by omega, by simp at h2; omega, h3, v, ?_, hk⟩
        have e : c.1 - i = (c.1 - (i + 1)) + 1 := by omega
        simpa [e] using hv

private theorem pairwise_keyedFrom (roots : Array Variable) (rows : List (KimchiRow F)) (i : Nat) :
    (keyedFrom roots rows i).Pairwise fun a b => Before a.2 b.2 := by
  induction rows generalizing i with
  | nil => exact List.Pairwise.nil
  | cons row rest ih =>
    rw [keyedFrom_cons, List.pairwise_append]
    refine ⟨pairwise_rowKeyed roots i _ 0, ih (i + 1), fun a ha b hb => ?_⟩
    have h1 := (mem_rowKeyed roots i _ 0 ha).1
    have h2 := mem_keyedFrom roots rest (i + 1) hb
    exact Or.inl (by omega)

private theorem nodup_cells (roots : Array Variable) (rows : List (KimchiRow F)) :
    ((keyedCells roots rows).map (·.2)).Nodup :=
  List.pairwise_map.mpr ((pairwise_keyedFrom roots rows 0).imp Before.ne)

private theorem nodup_classCells (roots : Array Variable) (rows : List (KimchiRow F))
    (k : Variable) : (classCells roots rows k).Nodup :=
  (pairwise_keyedFrom roots rows 0).filterMap _ fun _ _ h b hb b' hb' => by
    split at hb <;> split at hb' <;> simp at hb hb'
    subst hb hb'
    exact h.ne

private theorem mem_classCells {roots : Array Variable} {rows : List (KimchiRow F)} {k : Variable}
    {c : Nat × Nat} : c ∈ classCells roots rows k ↔ (k, c) ∈ keyedCells roots rows := by
  simp only [classCells, cellsOf, List.mem_filterMap]
  constructor
  · rintro ⟨⟨k', c'⟩, hmem, h⟩
    simp only at h
    split at h
    · simp only [Option.some.injEq] at h
      subst_vars
      exact hmem
    · exact absurd h (by simp)
  · intro h
    exact ⟨(k, c), h, by simp⟩

private theorem key_eq_of_mem_classCells {roots : Array Variable} {rows : List (KimchiRow F)}
    {k k' : Variable} {c : Nat × Nat} (h : c ∈ classCells roots rows k)
    (h' : c ∈ classCells roots rows k') : k = k' := by
  rw [mem_classCells] at h h'
  have := (List.nodup_map_iff_inj_on (List.Nodup.of_map _ (nodup_cells roots rows))).mp
    (nodup_cells roots rows) _ h _ h' rfl
  exact (Prod.mk.injEq ..).mp this |>.1

/-- A class's cells lie in the rows' first seven columns. -/
theorem classCells_bounds {roots : Array Variable} {rows : List (KimchiRow F)} {k : Variable}
    {c : Nat × Nat} (h : c ∈ classCells roots rows k) : c.1 < rows.length ∧ c.2 < 7 := by
  obtain ⟨-, hr, hj, -⟩ := (mem_keyedFrom_iff roots rows 0 k c).mp (mem_classCells.mp h)
  exact ⟨by simpa using hr, hj⟩

/-- A labelled cell in the first seven columns is in its root's class. -/
theorem mem_classCells_of_label {roots : Array Variable} {rows : List (KimchiRow F)} {r j : Nat}
    (hr : r < rows.length) (hj : j < 7) {v : Variable}
    (hv : rows[r].vars[j]'(by omega) = some v) :
    (r, j) ∈ classCells roots rows (roots.getD v v) := by
  rw [mem_classCells, keyedCells, mem_keyedFrom_iff]
  exact ⟨Nat.zero_le _, by simpa using hr, hj, v, by simpa using hv, rfl⟩

/-! ## The wire map at a class -/

private theorem classFold_eq_classCells (roots : Array Variable) (rows : List (KimchiRow F))
    {x : Variable × Array (Nat × Nat)}
    (hx : x ∈ (classFold ∅ (keyedFrom roots rows 0)).toList) :
    x.2 = (classCells roots rows x.1).toArray := by
  obtain ⟨k, cells⟩ := x
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, getElem?_classFold] at hx
  split at hx
  · simp at hx
  · simp only [Std.HashMap.getElem?_empty, Option.getD_none, Array.empty_append,
      Option.some.injEq] at hx
    exact hx.symm

/-- The wire map sends each cell of a class to the next, the last to the first. -/
theorem wireMap_getElem? (roots : Array Variable) (rows : List (KimchiRow F)) (k : Variable)
    (q : Nat) (hq : q < (classCells roots rows k).length) :
    (wireMap roots rows)[(classCells roots rows k)[q]]? =
      some ⟨((classCells roots rows k)[(q + 1) % (classCells roots rows k).length]'
          (Nat.mod_lt _ (by omega))).1,
        ((classCells roots rows k)[(q + 1) % (classCells roots rows k).length]'
          (Nat.mod_lt _ (by omega))).2⟩ := by
  rw [wireMap_eq]
  show (Id.run (forIn (m := Id) (forIn (m := Id) rows (⟨∅, 0⟩ : MProd Classes Nat)
    (classOuter roots)).fst ∅ cycleOuter))[_]? = _
  rw [forIn_classOuter, Std.HashMap.forIn_eq_forIn_toList, forIn_cycleOuter]
  show (cyclesFold (classFold ∅ (keyedFrom roots rows 0)).toList ∅)[_]? = _
  have hne : cellsOf k (keyedFrom roots rows 0) ≠ [] := by
    intro h
    have : (classCells roots rows k).length = 0 := by
      show (cellsOf k (keyedFrom roots rows 0)).length = 0
      rw [h]
      rfl
    omega
  have hmem : (k, (classCells roots rows k).toArray) ∈
      (classFold ∅ (keyedFrom roots rows 0)).toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, getElem?_classFold, if_neg hne]
    simp [classCells, keyedCells]
  have hnd : ∀ x ∈ (classFold ∅ (keyedFrom roots rows 0)).toList, x.2.toList.Nodup := by
    intro x hx
    rw [classFold_eq_classCells roots rows hx]
    simpa using nodup_classCells roots rows x.1
  have hdisj : (classFold ∅ (keyedFrom roots rows 0)).toList.Pairwise
      fun x y => ∀ c ∈ x.2.toList, c ∉ y.2.toList := by
    refine Std.HashMap.distinct_keys_toList.imp_of_mem fun {x y} hx hy hxy c hcx hcy => ?_
    rw [classFold_eq_classCells roots rows hx] at hcx
    rw [classFold_eq_classCells roots rows hy] at hcy
    rw [List.toList_toArray] at hcx hcy
    exact (beq_eq_false_iff_ne.mp hxy) (key_eq_of_mem_classCells hcx hcy)
  have h := getElem?_cyclesFold _ hnd hdisj ∅ _ hmem q (by simpa using hq)
  simp only [List.getElem_toArray] at h
  rw [h]
  simp only [cycleWire, List.size_toArray]
  rw [getElem!_pos _ _ (by simpa using Nat.mod_lt (q + 1) (Nat.lt_of_le_of_lt (Nat.zero_le q) hq))]
  simp

/-- The gate table has one row per row. -/
theorem length_assembleGates (roots : Array Variable) (rows : List (KimchiRow F)) :
    (assembleGates roots rows).length = rows.length := by
  simp [assembleGates]

/-- An assembled row's tag and coefficients are its row's, and its wiring targets are the
wire map's at the row's permutation cells. -/
theorem getElem_assembleGates (roots : Array Variable) (rows : List (KimchiRow F)) (i : Nat)
    (hi : i < rows.length) :
    (assembleGates roots rows)[i]'(by simpa [assembleGates] using hi) =
      { kind := rows[i].kind,
        wires := ⟨⟨[wireTarget (wireMap roots rows) i 0, wireTarget (wireMap roots rows) i 1,
          wireTarget (wireMap roots rows) i 2, wireTarget (wireMap roots rows) i 3,
          wireTarget (wireMap roots rows) i 4, wireTarget (wireMap roots rows) i 5,
          wireTarget (wireMap roots rows) i 6]⟩, by simp⟩,
        coeffs := rows[i].coeffs } := by
  simp [assembleGates, List.getElem_zipIdx]

/-- Values agreeing across every wire of a class agree across the class. -/
theorem classCells_values_eq (roots : Array Variable) (rows : List (KimchiRow F))
    (k : Variable) (val : Nat × Nat → F)
    (hcopy : ∀ c ∈ classCells roots rows k,
      val ((wireTarget (wireMap roots rows) c.1 c.2).row,
        (wireTarget (wireMap roots rows) c.1 c.2).col) = val c)
    {c c' : Nat × Nat} (hc : c ∈ classCells roots rows k) (hc' : c' ∈ classCells roots rows k) :
    val c = val c' := by
  have step : ∀ q (hq : q < (classCells roots rows k).length),
      val ((classCells roots rows k)[(q + 1) % (classCells roots rows k).length]'
        (Nat.mod_lt _ (by omega))) = val (classCells roots rows k)[q] := by
    intro q hq
    have := hcopy _ (List.getElem_mem hq)
    rw [wireTarget, Prod.mk.eta, Std.HashMap.getD_eq_getD_getElem?,
      wireMap_getElem? roots rows k q hq] at this
    simpa using this
  have all : ∀ q (hq : q < (classCells roots rows k).length),
      val (classCells roots rows k)[q] = val ((classCells roots rows k)[0]'(by omega)) := by
    intro q
    induction q with
    | zero => intro; rfl
    | succ q ih =>
      intro hq
      have h := step q (by omega)
      simp only [Nat.mod_eq_of_lt hq] at h
      rw [h]
      exact ih (by omega)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc'
  rw [all i hi, all j hj]

end Snarky.Kimchi
