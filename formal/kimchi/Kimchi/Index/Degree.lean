import Kimchi.Index.Aggregate

/-!
# Degree bounds for the kimchi aggregate family

This file proves the two degree bounds behind the ζ-axis counting of the one quotient
check: `card_badZetas_le` (`Kimchi/SchwartzZippel.lean`) bounds the bad-ζ set of an
eval-check by a degree bound `D` covering both sides,
`(aggregate α (idx.fullFamily …)).natDegree ≤ D` and `(t * zH F n).natDegree ≤ D`.
Both are satisfied by taking the single crude, uniform degree bound

  `degreeBound n = 9 * n`,

which every member of the `21 + 3` aggregate family — and every `t · Z_H` with
`t.natDegree < 7·n` — provably fits under; `Kimchi.Protocol.Equation.sound` consumes
the two headline bounds to cap its bad-ζ set at `degreeBound n`. The bound is
deliberately loose: the design goal is *one* `D` that works for all `24` members at once
(so a single `degreeBound n` covers both sides of the check), not a tight per-member
count. Arithmetic confirms `9n` suffices with only `≤`-crude reasoning, so we do not chase
a smaller constant.

The development is bottom-up:

* **Cell interpolants** (`columnPoly ω v`) have `natDegree < n` — they are Lagrange
  interpolants through the `n` domain nodes (`degree_columnPoly_lt`). Shifts
  (`shift`/`shiftRow`, both `.comp (C ω * X)`) do not raise degree.
* **Per-gate entries** — each constraint polynomial in `idx.gateConstraints wTab g`, read
  by `getD`, has `natDegree ≤ 8·n` (worst case: Poseidon's degree-7 s-box over cell
  interpolants of degree `< n`; slots past a gate's length are `0`).
* **Members** — a gate member `∑_g selectorPoly g · Eₖ` is `≤ (n−1) + 8n ≤ 9n`; the three
  permutation members are `≤ 9n` as well (member `0`: `zkpm` of degree `≤ n` times a
  degree-`≤ 8n` product difference; members `1,2`: `(z−1)·lagNumer` of degree `< 2n`).
* **Headlines** — `fullFamily_natDegree_le` case-splits the `dif` in `fullFamily`;
  `aggregate_natDegree_le` folds the members under `natDegree_sum_le`/`natDegree_smul_le`;
  `t_zH_natDegree_le` uses `natDegree (zH F n) = n` (`zH = Xⁿ − 1`) and `(7n−1)+n < 9n`.

All bounds are proved: the per-gate entries are discharged uniformly by `compute_degree`
over the cell bound (`columnPoly_natDegree_lt`), split into one theorem per gate (with the
reused `singleBit_entry_le` / `poseidon_round_comp_le` per-block helpers) so each stays
within the heartbeat budget. The headline family/aggregate/`t·Z_H` bounds reduce to exactly
`{propext, Classical.choice, Quot.sound}`.
-/

namespace Kimchi.Index

open Polynomial Kimchi.Lift
open Kimchi.Lift.Gate

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

/-! ## The uniform degree bound -/

/-- **The uniform degree bound** `D = 9·n` covering both sides of the aggregated
eval-check — the cardinality cap of its bad-ζ set (`card_badZetas_le`). Crude by
design: one `D` for all `21 + 3` members and for
every honest quotient `t · Z_H`, not a tight per-member count. -/
def degreeBound (n : ℕ) : ℕ := 9 * n

/-! ## Cell-level bounds

The column interpolants that every constraint polynomial is built from have degree `< n`,
and the domain shift `X ↦ ω·X` does not raise degree. These are the leaves of every
member bound below. -/

/-- **A column interpolant has degree `< n`.** `columnPoly ω v` is the Lagrange interpolant
through the `n` domain nodes, so `degree < n` (`degree_columnPoly_lt`); with `NeZero n` the
`WithBot` degree bound transfers to `natDegree`. -/
theorem columnPoly_natDegree_lt [NeZero n] {ω : F} (hω : IsPrimitiveRoot ω n)
    (v : Fin n → F) : (columnPoly ω v).natDegree < n := by
  have hd := degree_columnPoly_lt hω v
  by_cases hp : columnPoly ω v = 0
  · rw [hp, natDegree_zero]; exact Nat.pos_of_neZero n
  · exact (natDegree_lt_iff_degree_lt hp).mpr hd

omit [DecidableEq F] in
/-- **The shift does not raise degree.** `shift ω p = p.comp (C ω * X)`, and post-composing
with the degree-`≤ 1` linear rotation only lowers degree (`natDegree_comp_le`). -/
private theorem shift_natDegree_le {ω : F} (p : Polynomial F) :
    (shift ω p).natDegree ≤ p.natDegree := by
  unfold shift
  have h1 : (C ω * X).natDegree ≤ 1 :=
    le_trans (natDegree_C_mul_le ω X) (le_of_eq natDegree_X)
  calc (p.comp (C ω * X)).natDegree
      ≤ p.natDegree * (C ω * X).natDegree := natDegree_comp_le
    _ ≤ p.natDegree * 1 := by gcongr
    _ = p.natDegree := mul_one _

omit [DecidableEq F] in
/-- **The permutation next-row shift does not raise degree.** Same `.comp (C ω * X)` shape
as `shift`, so degree is preserved (`natDegree_comp_le`). -/
private theorem shiftRow_natDegree_le {ω : F} (z : Polynomial F) :
    (Kimchi.Permutation.shiftRow ω z).natDegree ≤ z.natDegree := by
  unfold Kimchi.Permutation.shiftRow
  have h1 : (C ω * X).natDegree ≤ 1 :=
    le_trans (natDegree_C_mul_le ω X) (le_of_eq natDegree_X)
  calc (z.comp (C ω * X)).natDegree
      ≤ z.natDegree * (C ω * X).natDegree := natDegree_comp_le
    _ ≤ z.natDegree * 1 := by gcongr
    _ = z.natDegree := mul_one _

/-! ## A fold-degree helper

The EndoScalar crumb accumulation folds a list into a running polynomial via
`acc ↦ mul · acc + f x`, where the multiplier `mul` is a *constant* (`natDegree 0` — the
numerals `4`/`2` of the recoding). Rather than hand-unfold the eight levels, bound the whole
fold by induction on the list: a uniform per-entry bound `d` on both the seed and every
`f x` survives the fold. -/

omit [DecidableEq F] in
/-- **A `mul · acc + f x` fold stays under a uniform degree bound** when `mul` is constant.
If the seed and every `f x` have `natDegree ≤ d`, so does the fold — `mul · acc` preserves the
bound (`natDegree_mul_le`, `mul.natDegree = 0`) and `+ f x` preserves it (`natDegree_add_le`).
Proof by induction on `l`. -/
private theorem foldl_linComb_natDegree_le {α : Type*} (mul : Polynomial F)
    (hmul : mul.natDegree = 0)
    (f : α → Polynomial F) (l : List α) (init : Polynomial F) (d : ℕ)
    (hinit : init.natDegree ≤ d) (hf : ∀ x ∈ l, (f x).natDegree ≤ d) :
    (l.foldl (fun acc x => mul * acc + f x) init).natDegree ≤ d := by
  induction l generalizing init with
  | nil => simpa using hinit
  | cons x l' ih =>
    rw [List.foldl_cons]
    apply ih
    · have hfx : (f x).natDegree ≤ d := hf x (by simp)
      calc (mul * init + f x).natDegree
          ≤ max (mul * init).natDegree (f x).natDegree := natDegree_add_le _ _
        _ ≤ d := max_le (le_trans natDegree_mul_le (by rw [hmul]; simpa using hinit)) hfx
    · intro y hy; exact hf y (by simp [hy])

omit [DecidableEq F] in
/-- **A `getD` slot of a degree-bounded list stays bounded.** In range it is a list member
(discharged by the hypothesis); past the end it is the zero default (`natDegree 0 = 0`). -/
private theorem getD_natDegree_le {L : List (Polynomial F)} {d : ℕ}
    (h : ∀ E ∈ L, E.natDegree ≤ d) (k : ℕ) : (L.getD k 0).natDegree ≤ d := by
  rcases Nat.lt_or_ge k L.length with hk | hk
  · rw [List.getD_eq_getElem _ _ hk]; exact h _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ hk, natDegree_zero]; exact Nat.zero_le d

omit [DecidableEq F] in
/-- **One VarBaseMul bit-block's four entries stay under `8·n`.** Every cell fed to
`singleBitCons` has degree `≤ d`; the deepest entry (`xo`, cleared with `t`, `u`) reaches
degree `6·d`, so `6·d ≤ 8·n` covers the block. Reused for all five chained blocks. -/
private theorem singleBit_entry_le {d : ℕ} {b xb yb s1 xi yi xo yo : Polynomial F}
    (hb : b.natDegree ≤ d) (hxb : xb.natDegree ≤ d) (hyb : yb.natDegree ≤ d)
    (hs1 : s1.natDegree ≤ d) (hxi : xi.natDegree ≤ d) (hyi : yi.natDegree ≤ d)
    (hxo : xo.natDegree ≤ d) (hyo : yo.natDegree ≤ d) (hd : 6 * d ≤ 8 * n) :
    ∀ e ∈ Gate.VarBaseMul.singleBitCons b xb yb s1 xi yi xo yo, e.natDegree ≤ 8 * n := by
  intro e he
  simp only [Gate.VarBaseMul.singleBitCons, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> (compute_degree; omega)

/-! ## Per-gate entry bound

Every constraint polynomial produced by a gate transcription, read positionally with
`getD` (default `0` past the gate's constraint count), has degree `≤ 8·n`. The worst case
is Poseidon's degree-7 s-box applied to cell interpolants of degree `< n`; the other gates
are lower (generic/completeAdd/varBaseMul/endoMul ≤ 3n, endoScalar ≤ 4n). Slots past a
gate's length are the zero polynomial (`natDegree 0 = 0`). -/

/-- Shared cell bound: a column interpolant of the index has `natDegree ≤ n - 1`. -/
private theorem cell_le [NeZero n] (idx : Index F n) (v : Fin n → F) :
    (columnPoly idx.omega v).natDegree ≤ n - 1 := by
  have := columnPoly_natDegree_lt idx.omega_prim v; omega

/-- Shared shifted-cell bound: the next-row shift of a cell has `natDegree ≤ n - 1`. -/
private theorem shift_cell_le [NeZero n] (idx : Index F n) (v : Fin n → F) :
    (shift idx.omega (columnPoly idx.omega v)).natDegree ≤ n - 1 :=
  le_trans (shift_natDegree_le _) (cell_le idx v)

/-- **CompleteAdd entries ≤ 8n.** Every entry is degree `≤ 3(n−1)` over cells `< n`. -/
private theorem addComplete_entry_le [NeZero n] (idx : Index F n)
    (wTab : Fin n → Fin wCols → F) :
    ∀ E ∈ idx.gateConstraints wTab .completeAdd, E.natDegree ≤ 8 * n := by
  intro E hE
  have b0 : (AddComplete.polyWitness idx.omega wTab).x1.natDegree ≤ n - 1 := cell_le idx _
  have b1 : (AddComplete.polyWitness idx.omega wTab).y1.natDegree ≤ n - 1 := cell_le idx _
  have b2 : (AddComplete.polyWitness idx.omega wTab).x2.natDegree ≤ n - 1 := cell_le idx _
  have b3 : (AddComplete.polyWitness idx.omega wTab).y2.natDegree ≤ n - 1 := cell_le idx _
  have b4 : (AddComplete.polyWitness idx.omega wTab).x3.natDegree ≤ n - 1 := cell_le idx _
  have b5 : (AddComplete.polyWitness idx.omega wTab).y3.natDegree ≤ n - 1 := cell_le idx _
  have b6 : (AddComplete.polyWitness idx.omega wTab).inf.natDegree ≤ n - 1 := cell_le idx _
  have b7 : (AddComplete.polyWitness idx.omega wTab).sameX.natDegree ≤ n - 1 := cell_le idx _
  have b8 : (AddComplete.polyWitness idx.omega wTab).s.natDegree ≤ n - 1 := cell_le idx _
  have b9 : (AddComplete.polyWitness idx.omega wTab).infZ.natDegree ≤ n - 1 := cell_le idx _
  have b10 : (AddComplete.polyWitness idx.omega wTab).x21Inv.natDegree ≤ n - 1 := cell_le idx _
  simp only [Index.gateConstraints, Gate.AddComplete.constraints, List.mem_cons,
    List.not_mem_nil, or_false] at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (compute_degree; omega)

/-- **VarBaseMul entries ≤ 8n.** The decomposition is linear; each of the five bit-blocks is
bounded by `singleBit_entry_le` (its deepest entry reaches degree `6(n−1)`). -/
private theorem varBaseMul_entry_le [NeZero n] (idx : Index F n)
    (wTab : Fin n → Fin wCols → F) :
    ∀ E ∈ idx.gateConstraints wTab .varBaseMul, E.natDegree ≤ 8 * n := by
  intro E hE
  have hd : 6 * (n - 1) ≤ 8 * n := by omega
  have hxT : (VarBaseMul.polyWitness idx.omega wTab).xT.natDegree ≤ n - 1 := cell_le idx _
  have hyT : (VarBaseMul.polyWitness idx.omega wTab).yT.natDegree ≤ n - 1 := cell_le idx _
  have hx0 : (VarBaseMul.polyWitness idx.omega wTab).x0.natDegree ≤ n - 1 := cell_le idx _
  have hy0 : (VarBaseMul.polyWitness idx.omega wTab).y0.natDegree ≤ n - 1 := cell_le idx _
  have hx1 : (VarBaseMul.polyWitness idx.omega wTab).x1.natDegree ≤ n - 1 := cell_le idx _
  have hy1 : (VarBaseMul.polyWitness idx.omega wTab).y1.natDegree ≤ n - 1 := cell_le idx _
  have hx2 : (VarBaseMul.polyWitness idx.omega wTab).x2.natDegree ≤ n - 1 := cell_le idx _
  have hy2 : (VarBaseMul.polyWitness idx.omega wTab).y2.natDegree ≤ n - 1 := cell_le idx _
  have hx3 : (VarBaseMul.polyWitness idx.omega wTab).x3.natDegree ≤ n - 1 := cell_le idx _
  have hy3 : (VarBaseMul.polyWitness idx.omega wTab).y3.natDegree ≤ n - 1 := cell_le idx _
  have hx4 : (VarBaseMul.polyWitness idx.omega wTab).x4.natDegree ≤ n - 1 := cell_le idx _
  have hy4 : (VarBaseMul.polyWitness idx.omega wTab).y4.natDegree ≤ n - 1 := cell_le idx _
  have hnP : (VarBaseMul.polyWitness idx.omega wTab).nPrime.natDegree ≤ n - 1 := cell_le idx _
  have hnn : (VarBaseMul.polyWitness idx.omega wTab).n.natDegree ≤ n - 1 := cell_le idx _
  have hx5 : (VarBaseMul.polyWitness idx.omega wTab).x5.natDegree ≤ n - 1 := shift_cell_le idx _
  have hy5 : (VarBaseMul.polyWitness idx.omega wTab).y5.natDegree ≤ n - 1 := shift_cell_le idx _
  have hb0 : (VarBaseMul.polyWitness idx.omega wTab).b0.natDegree ≤ n - 1 := shift_cell_le idx _
  have hb1 : (VarBaseMul.polyWitness idx.omega wTab).b1.natDegree ≤ n - 1 := shift_cell_le idx _
  have hb2 : (VarBaseMul.polyWitness idx.omega wTab).b2.natDegree ≤ n - 1 := shift_cell_le idx _
  have hb3 : (VarBaseMul.polyWitness idx.omega wTab).b3.natDegree ≤ n - 1 := shift_cell_le idx _
  have hb4 : (VarBaseMul.polyWitness idx.omega wTab).b4.natDegree ≤ n - 1 := shift_cell_le idx _
  have hss0 : (VarBaseMul.polyWitness idx.omega wTab).s0.natDegree ≤ n - 1 := shift_cell_le idx _
  have hss1 : (VarBaseMul.polyWitness idx.omega wTab).s1.natDegree ≤ n - 1 := shift_cell_le idx _
  have hss2 : (VarBaseMul.polyWitness idx.omega wTab).s2.natDegree ≤ n - 1 := shift_cell_le idx _
  have hss3 : (VarBaseMul.polyWitness idx.omega wTab).s3.natDegree ≤ n - 1 := shift_cell_le idx _
  have hss4 : (VarBaseMul.polyWitness idx.omega wTab).s4.natDegree ≤ n - 1 := shift_cell_le idx _
  rw [Index.gateConstraints, Gate.VarBaseMul.constraints, List.mem_cons] at hE
  rcases hE with rfl | hE
  · rw [Gate.VarBaseMul.decompCons]; compute_degree; omega
  · rcases List.mem_append.mp hE with hE | hE4
    · rcases List.mem_append.mp hE with hE | hE3
      · rcases List.mem_append.mp hE with hE | hE2
        · rcases List.mem_append.mp hE with hE0 | hE1
          · exact singleBit_entry_le hb0 hxT hyT hss0 hx0 hy0 hx1 hy1 hd _ hE0
          · exact singleBit_entry_le hb1 hxT hyT hss1 hx1 hy1 hx2 hy2 hd _ hE1
        · exact singleBit_entry_le hb2 hxT hyT hss2 hx2 hy2 hx3 hy3 hd _ hE2
      · exact singleBit_entry_le hb3 hxT hyT hss3 hx3 hy3 hx4 hy4 hd _ hE3
    · exact singleBit_entry_le hb4 hxT hyT hss4 hx4 hy4 hx5 hy5 hd _ hE4

/-- **EndoMul entries ≤ 8n.** Every entry is degree `≤ 4(n−1)` over cells `< n` and the
constant `endo = C endoBase`. -/
private theorem endoMul_entry_le [NeZero n] (idx : Index F n)
    (wTab : Fin n → Fin wCols → F) :
    ∀ E ∈ idx.gateConstraints wTab .endoMul, E.natDegree ≤ 8 * n := by
  intro E hE
  have hxT : (EndoMul.polyWitness idx.omega wTab).xT.natDegree ≤ n - 1 := cell_le idx _
  have hyT : (EndoMul.polyWitness idx.omega wTab).yT.natDegree ≤ n - 1 := cell_le idx _
  have hxP : (EndoMul.polyWitness idx.omega wTab).xP.natDegree ≤ n - 1 := cell_le idx _
  have hyP : (EndoMul.polyWitness idx.omega wTab).yP.natDegree ≤ n - 1 := cell_le idx _
  have hnn : (EndoMul.polyWitness idx.omega wTab).n.natDegree ≤ n - 1 := cell_le idx _
  have hb1 : (EndoMul.polyWitness idx.omega wTab).b1.natDegree ≤ n - 1 := cell_le idx _
  have hb2 : (EndoMul.polyWitness idx.omega wTab).b2.natDegree ≤ n - 1 := cell_le idx _
  have hb3 : (EndoMul.polyWitness idx.omega wTab).b3.natDegree ≤ n - 1 := cell_le idx _
  have hb4 : (EndoMul.polyWitness idx.omega wTab).b4.natDegree ≤ n - 1 := cell_le idx _
  have hs1 : (EndoMul.polyWitness idx.omega wTab).s1.natDegree ≤ n - 1 := cell_le idx _
  have hxR : (EndoMul.polyWitness idx.omega wTab).xR.natDegree ≤ n - 1 := cell_le idx _
  have hyR : (EndoMul.polyWitness idx.omega wTab).yR.natDegree ≤ n - 1 := cell_le idx _
  have hs3 : (EndoMul.polyWitness idx.omega wTab).s3.natDegree ≤ n - 1 := cell_le idx _
  have hinv : (EndoMul.polyWitness idx.omega wTab).inv.natDegree ≤ n - 1 := cell_le idx _
  have hnP : (EndoMul.polyWitness idx.omega wTab).nPrime.natDegree ≤ n - 1 := shift_cell_le idx _
  have hxS : (EndoMul.polyWitness idx.omega wTab).xS.natDegree ≤ n - 1 := shift_cell_le idx _
  have hyS : (EndoMul.polyWitness idx.omega wTab).yS.natDegree ≤ n - 1 := shift_cell_le idx _
  simp only [Index.gateConstraints, Gate.EndoMul.constraints, List.mem_cons,
    List.not_mem_nil, or_false] at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (compute_degree; omega)

/-- **Generic entries ≤ 8n.** Two entries, each degree `≤ 3(n−1)` (a bilinear `q₃·(w₀·w₁)`
term) over cell interpolants `< n`. -/
private theorem generic_entry_le [NeZero n] (idx : Index F n)
    (wTab : Fin n → Fin wCols → F) :
    ∀ E ∈ idx.gateConstraints wTab .generic, E.natDegree ≤ 8 * n := by
  intro E hE
  have hw0 : (columnPoly idx.omega (fun j => wTab j 0)).natDegree ≤ n - 1 := cell_le idx _
  have hw1 : (columnPoly idx.omega (fun j => wTab j 1)).natDegree ≤ n - 1 := cell_le idx _
  have hw2 : (columnPoly idx.omega (fun j => wTab j 2)).natDegree ≤ n - 1 := cell_le idx _
  have hw3 : (columnPoly idx.omega (fun j => wTab j 3)).natDegree ≤ n - 1 := cell_le idx _
  have hw4 : (columnPoly idx.omega (fun j => wTab j 4)).natDegree ≤ n - 1 := cell_le idx _
  have hw5 : (columnPoly idx.omega (fun j => wTab j 5)).natDegree ≤ n - 1 := cell_le idx _
  have hq0 : (columnPoly idx.omega (fun j => idx.coeffTable j 0)).natDegree ≤ n - 1 :=
    cell_le idx _
  have hq1 : (columnPoly idx.omega (fun j => idx.coeffTable j 1)).natDegree ≤ n - 1 :=
    cell_le idx _
  have hq2 : (columnPoly idx.omega (fun j => idx.coeffTable j 2)).natDegree ≤ n - 1 :=
    cell_le idx _
  have hq3 : (columnPoly idx.omega (fun j => idx.coeffTable j 3)).natDegree ≤ n - 1 :=
    cell_le idx _
  have hq4 : (columnPoly idx.omega (fun j => idx.coeffTable j 4)).natDegree ≤ n - 1 :=
    cell_le idx _
  have hq5 : (columnPoly idx.omega (fun j => idx.coeffTable j 5)).natDegree ≤ n - 1 :=
    cell_le idx _
  have hq6 : (columnPoly idx.omega (fun j => idx.coeffTable j 6)).natDegree ≤ n - 1 :=
    cell_le idx _
  have hq7 : (columnPoly idx.omega (fun j => idx.coeffTable j 7)).natDegree ≤ n - 1 :=
    cell_le idx _
  have hq8 : (columnPoly idx.omega (fun j => idx.coeffTable j 8)).natDegree ≤ n - 1 :=
    cell_le idx _
  have hq9 : (columnPoly idx.omega (fun j => idx.coeffTable j 9)).natDegree ≤ n - 1 :=
    cell_le idx _
  simp only [Index.gateConstraints, Generic.argument, Generic.cellMap, polyEnv,
    Gate.Generic.constraints, List.mem_cons, List.not_mem_nil, or_false] at hE
  rcases hE with rfl | rfl <;> (compute_degree; omega)

/-- **EndoScalar entries ≤ 8n.** The three recoding folds are bounded by
`foldl_linComb_natDegree_le` (with per-crumb bound `n−1` for the `n`-fold, `3(n−1)` for the
`a`/`b`-folds through the cubic `cPoly`/`dPoly`); the eight `crumbPoly` entries are degree
`4(n−1)`. -/
private theorem endoScalar_entry_le [NeZero n] (idx : Index F n)
    (wTab : Fin n → Fin wCols → F) :
    ∀ E ∈ idx.gateConstraints wTab .endoScalar, E.natDegree ≤ 8 * n := by
  intro E hE
  set w := EndoScalar.polyWitness idx.omega wTab with hwdef
  have hn0 : w.n0.natDegree ≤ n - 1 := cell_le idx _
  have hn8 : w.n8.natDegree ≤ n - 1 := cell_le idx _
  have ha0 : w.a0.natDegree ≤ n - 1 := cell_le idx _
  have ha8 : w.a8.natDegree ≤ n - 1 := cell_le idx _
  have hb0 : w.b0.natDegree ≤ n - 1 := cell_le idx _
  have hb8 : w.b8.natDegree ≤ n - 1 := cell_le idx _
  have hcr : ∀ x ∈ w.crumbs, x.natDegree ≤ n - 1 := by
    intro x hx
    rw [hwdef] at hx
    simp only [EndoScalar.polyWitness, EndoScalar.cellMap, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact cell_le idx _
  have h4 : (4 : Polynomial F).natDegree = 0 := by simp
  have h2 : (2 : Polynomial F).natDegree = 0 := by simp
  -- the cubic recoding polynomials on a crumb `< n` have degree `≤ 3(n − 1)`
  have hcp : ∀ x ∈ w.crumbs, (Gate.EndoScalar.cPoly x (F := F)).natDegree ≤ 3 * (n - 1) := by
    intro x hx
    have hxd := hcr x hx
    unfold Gate.EndoScalar.cPoly
    simp only [Polynomial.algebraMap_eq]
    compute_degree; omega
  have hdp : ∀ x ∈ w.crumbs, (Gate.EndoScalar.dPoly x (F := F)).natDegree ≤ 3 * (n - 1) := by
    intro x hx
    have hxd := hcr x hx
    unfold Gate.EndoScalar.dPoly Gate.EndoScalar.cPoly
    simp only [Polynomial.algebraMap_eq]
    compute_degree; omega
  simp only [Index.gateConstraints, Gate.EndoScalar.constraints, ← hwdef, List.mem_append,
    List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hE
  rcases hE with (rfl | rfl | rfl) | ⟨x, hx, rfl⟩
  · -- `n`-fold: mul = 4, seed and crumbs are cells `< n`
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ (le_trans hn8 (by omega)))
    exact le_trans
      (foldl_linComb_natDegree_le (4 : Polynomial F) h4 id w.crumbs w.n0 (n - 1) hn0 hcr)
      (by omega)
  · -- `a`-fold: mul = 2, per-crumb bound `3(n − 1)` via `cPoly`
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ (le_trans ha8 (by omega)))
    exact le_trans
      (foldl_linComb_natDegree_le (2 : Polynomial F) h2
        (fun x => Gate.EndoScalar.cPoly x (F := F)) w.crumbs w.a0 (3 * (n - 1))
        (le_trans ha0 (by omega)) hcp) (by omega)
  · -- `b`-fold: mul = 2, per-crumb bound `3(n − 1)` via `dPoly`
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ (le_trans hb8 (by omega)))
    exact le_trans
      (foldl_linComb_natDegree_le (2 : Polynomial F) h2
        (fun x => Gate.EndoScalar.dPoly x (F := F)) w.crumbs w.b0 (3 * (n - 1))
        (le_trans hb0 (by omega)) hdp) (by omega)
  · -- a `crumbPoly` entry: degree `4(n − 1)`
    have hxd := hcr x hx
    unfold Gate.EndoScalar.crumbPoly
    compute_degree; omega

omit [DecidableEq F] in
/-- **One Poseidon round-output component stays under `8·n`.** An MDS row `r + m₀·a⁷ +
m₁·b⁷ + m₂·c⁷` over cells `≤ d` (constant MDS coefficients) reaches degree `7·d`, so the
`state − round` entry is `≤ 8·n` once `7·d ≤ 8·n`. Reused for all 15 Poseidon entries. -/
private theorem poseidon_round_comp_le {d : ℕ} {lhs r a b c m0 m1 m2 : Polynomial F}
    (hm0 : m0.natDegree = 0) (hm1 : m1.natDegree = 0) (hm2 : m2.natDegree = 0)
    (hlhs : lhs.natDegree ≤ d) (hr : r.natDegree ≤ d) (ha : a.natDegree ≤ d)
    (hb : b.natDegree ≤ d) (hc : c.natDegree ≤ d) (hd : 7 * d ≤ 8 * n) :
    (lhs - (r + m0 * a ^ 7 + m1 * b ^ 7 + m2 * c ^ 7)).natDegree ≤ 8 * n := by
  compute_degree; omega

/-- **Poseidon entries ≤ 8n.** The deepest gate: each of the 15 entries is a state cell minus
a round output, whose degree-7 s-box over cells `< n` reaches `7(n−1) < 8n`. Each entry is
discharged by `poseidon_round_comp_le`. -/
private theorem poseidon_entry_le [NeZero n] (idx : Index F n)
    (wTab : Fin n → Fin wCols → F) :
    ∀ E ∈ idx.gateConstraints wTab .poseidon, E.natDegree ≤ 8 * n := by
  intro E hE
  have s01 : (Poseidon.polyWitness idx.omega wTab).s0.1.natDegree ≤ n - 1 := cell_le idx _
  have s02 : (Poseidon.polyWitness idx.omega wTab).s0.2.1.natDegree ≤ n - 1 := cell_le idx _
  have s03 : (Poseidon.polyWitness idx.omega wTab).s0.2.2.natDegree ≤ n - 1 := cell_le idx _
  have s11 : (Poseidon.polyWitness idx.omega wTab).s1.1.natDegree ≤ n - 1 := cell_le idx _
  have s12 : (Poseidon.polyWitness idx.omega wTab).s1.2.1.natDegree ≤ n - 1 := cell_le idx _
  have s13 : (Poseidon.polyWitness idx.omega wTab).s1.2.2.natDegree ≤ n - 1 := cell_le idx _
  have s21 : (Poseidon.polyWitness idx.omega wTab).s2.1.natDegree ≤ n - 1 := cell_le idx _
  have s22 : (Poseidon.polyWitness idx.omega wTab).s2.2.1.natDegree ≤ n - 1 := cell_le idx _
  have s23 : (Poseidon.polyWitness idx.omega wTab).s2.2.2.natDegree ≤ n - 1 := cell_le idx _
  have s31 : (Poseidon.polyWitness idx.omega wTab).s3.1.natDegree ≤ n - 1 := cell_le idx _
  have s32 : (Poseidon.polyWitness idx.omega wTab).s3.2.1.natDegree ≤ n - 1 := cell_le idx _
  have s33 : (Poseidon.polyWitness idx.omega wTab).s3.2.2.natDegree ≤ n - 1 := cell_le idx _
  have s41 : (Poseidon.polyWitness idx.omega wTab).s4.1.natDegree ≤ n - 1 := cell_le idx _
  have s42 : (Poseidon.polyWitness idx.omega wTab).s4.2.1.natDegree ≤ n - 1 := cell_le idx _
  have s43 : (Poseidon.polyWitness idx.omega wTab).s4.2.2.natDegree ≤ n - 1 := cell_le idx _
  have s51 : (Poseidon.polyWitness idx.omega wTab).s5.1.natDegree ≤ n - 1 := shift_cell_le idx _
  have s52 : (Poseidon.polyWitness idx.omega wTab).s5.2.1.natDegree ≤ n - 1 :=
    shift_cell_le idx _
  have s53 : (Poseidon.polyWitness idx.omega wTab).s5.2.2.natDegree ≤ n - 1 :=
    shift_cell_le idx _
  have r01 : (Poseidon.rcPoly idx.omega idx.coeffTable 0).1.natDegree ≤ n - 1 := cell_le idx _
  have r02 : (Poseidon.rcPoly idx.omega idx.coeffTable 0).2.1.natDegree ≤ n - 1 := cell_le idx _
  have r03 : (Poseidon.rcPoly idx.omega idx.coeffTable 0).2.2.natDegree ≤ n - 1 := cell_le idx _
  have r11 : (Poseidon.rcPoly idx.omega idx.coeffTable 1).1.natDegree ≤ n - 1 := cell_le idx _
  have r12 : (Poseidon.rcPoly idx.omega idx.coeffTable 1).2.1.natDegree ≤ n - 1 := cell_le idx _
  have r13 : (Poseidon.rcPoly idx.omega idx.coeffTable 1).2.2.natDegree ≤ n - 1 := cell_le idx _
  have r21 : (Poseidon.rcPoly idx.omega idx.coeffTable 2).1.natDegree ≤ n - 1 := cell_le idx _
  have r22 : (Poseidon.rcPoly idx.omega idx.coeffTable 2).2.1.natDegree ≤ n - 1 := cell_le idx _
  have r23 : (Poseidon.rcPoly idx.omega idx.coeffTable 2).2.2.natDegree ≤ n - 1 := cell_le idx _
  have r31 : (Poseidon.rcPoly idx.omega idx.coeffTable 3).1.natDegree ≤ n - 1 := cell_le idx _
  have r32 : (Poseidon.rcPoly idx.omega idx.coeffTable 3).2.1.natDegree ≤ n - 1 := cell_le idx _
  have r33 : (Poseidon.rcPoly idx.omega idx.coeffTable 3).2.2.natDegree ≤ n - 1 := cell_le idx _
  have r41 : (Poseidon.rcPoly idx.omega idx.coeffTable 4).1.natDegree ≤ n - 1 := cell_le idx _
  have r42 : (Poseidon.rcPoly idx.omega idx.coeffTable 4).2.1.natDegree ≤ n - 1 := cell_le idx _
  have r43 : (Poseidon.rcPoly idx.omega idx.coeffTable 4).2.2.natDegree ≤ n - 1 := cell_le idx _
  have hm00 : ((idx.mds.map C).m00 : Polynomial F).natDegree = 0 := natDegree_C _
  have hm01 : ((idx.mds.map C).m01 : Polynomial F).natDegree = 0 := natDegree_C _
  have hm02 : ((idx.mds.map C).m02 : Polynomial F).natDegree = 0 := natDegree_C _
  have hm10 : ((idx.mds.map C).m10 : Polynomial F).natDegree = 0 := natDegree_C _
  have hm11 : ((idx.mds.map C).m11 : Polynomial F).natDegree = 0 := natDegree_C _
  have hm12 : ((idx.mds.map C).m12 : Polynomial F).natDegree = 0 := natDegree_C _
  have hm20 : ((idx.mds.map C).m20 : Polynomial F).natDegree = 0 := natDegree_C _
  have hm21 : ((idx.mds.map C).m21 : Polynomial F).natDegree = 0 := natDegree_C _
  have hm22 : ((idx.mds.map C).m22 : Polynomial F).natDegree = 0 := natDegree_C _
  have hd : 7 * (n - 1) ≤ 8 * n := by omega
  simp only [Index.gateConstraints, Gate.Poseidon.constraints, Gate.Poseidon.round,
    Gate.Poseidon.sbox, List.mem_cons, List.not_mem_nil, or_false] at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact poseidon_round_comp_le hm00 hm01 hm02 s11 r01 s01 s02 s03 hd
  · exact poseidon_round_comp_le hm10 hm11 hm12 s12 r02 s01 s02 s03 hd
  · exact poseidon_round_comp_le hm20 hm21 hm22 s13 r03 s01 s02 s03 hd
  · exact poseidon_round_comp_le hm00 hm01 hm02 s21 r11 s11 s12 s13 hd
  · exact poseidon_round_comp_le hm10 hm11 hm12 s22 r12 s11 s12 s13 hd
  · exact poseidon_round_comp_le hm20 hm21 hm22 s23 r13 s11 s12 s13 hd
  · exact poseidon_round_comp_le hm00 hm01 hm02 s31 r21 s21 s22 s23 hd
  · exact poseidon_round_comp_le hm10 hm11 hm12 s32 r22 s21 s22 s23 hd
  · exact poseidon_round_comp_le hm20 hm21 hm22 s33 r23 s21 s22 s23 hd
  · exact poseidon_round_comp_le hm00 hm01 hm02 s41 r31 s31 s32 s33 hd
  · exact poseidon_round_comp_le hm10 hm11 hm12 s42 r32 s31 s32 s33 hd
  · exact poseidon_round_comp_le hm20 hm21 hm22 s43 r33 s31 s32 s33 hd
  · exact poseidon_round_comp_le hm00 hm01 hm02 s51 r41 s41 s42 s43 hd
  · exact poseidon_round_comp_le hm10 hm11 hm12 s52 r42 s41 s42 s43 hd
  · exact poseidon_round_comp_le hm20 hm21 hm22 s53 r43 s41 s42 s43 hd

/-- **Per-gate entry bound.** The `k`-th constraint of any gate type `g` (default `0` past
its length) has `natDegree ≤ 8·n`, dispatched to the six per-gate entry bounds through
`getD_natDegree_le` (slots past a gate's length are the zero polynomial). `8·n` covers the
deepest gate (Poseidon's s-box). -/
private theorem gateConstraints_getD_natDegree_le [NeZero n] (idx : Index F n)
    (wTab : Fin n → Fin wCols → F) (g : GateType) (k : ℕ) :
    ((idx.gateConstraints wTab g).getD k 0).natDegree ≤ 8 * n := by
  cases g with
  | zero => simp [Index.gateConstraints]
  | generic => exact getD_natDegree_le (generic_entry_le idx wTab) k
  | poseidon => exact getD_natDegree_le (poseidon_entry_le idx wTab) k
  | completeAdd => exact getD_natDegree_le (addComplete_entry_le idx wTab) k
  | varBaseMul => exact getD_natDegree_le (varBaseMul_entry_le idx wTab) k
  | endoMul => exact getD_natDegree_le (endoMul_entry_le idx wTab) k
  | endoScalar => exact getD_natDegree_le (endoScalar_entry_le idx wTab) k

/-! ## Member bounds

Each of the `21 + 3` aggregate members lands under `degreeBound n = 9n`: a gate member is
a selector interpolant (`< n`) times a gate entry (`≤ 8n`), summed and with the public
interpolant (`< n`) subtracted; the three permutation members are `zkpm`·(product
difference) and `(z−1)·lagNumer`, each `≤ 9n`. -/

/-- **Gate-member bound.** `idx.gateMember pub wTab k` — the cross-gate sum
`∑_g selectorPoly g · Eₖ` minus the public interpolant in slot `0` — has `natDegree ≤ 9n`.
Each summand is `< n` (selector) times `≤ 8n` (entry, `gateConstraints_getD_natDegree_le`),
so `≤ (n−1) + 8n < 9n`; the subtracted public interpolant is `< n`. -/
private theorem gateMember_natDegree_le [NeZero n] (idx : Index F n)
    (pub : Fin idx.publicCount → F) (wTab : Fin n → Fin wCols → F) (k : ℕ) :
    (idx.gateMember pub wTab k).natDegree ≤ degreeBound n := by
  unfold Index.gateMember
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
  · -- the cross-gate sum: (selector < n) · (entry ≤ 8n) ≤ 9n
    apply natDegree_sum_le_of_forall_le
    intro g _
    refine le_trans (natDegree_mul_le) ?_
    have hc : (columnPoly idx.omega (idx.selectorRow g)).natDegree < n :=
      columnPoly_natDegree_lt idx.omega_prim _
    have he : ((idx.gateConstraints wTab g).getD k 0).natDegree ≤ 8 * n :=
      gateConstraints_getD_natDegree_le idx wTab g k
    unfold degreeBound
    omega
  · -- the subtracted public interpolant (< n) or zero
    split_ifs with hk
    · unfold Index.pubPoly
      have hp : (columnPoly idx.omega (pubAt idx pub)).natDegree < n :=
        columnPoly_natDegree_lt idx.omega_prim _
      unfold degreeBound
      omega
    · rw [natDegree_zero]
      unfold degreeBound
      omega

open Kimchi.Permutation in
/-- **Permutation-member bound.** Each of the three permutation constraints at the index's
wiring data has `natDegree ≤ 9n` when the accumulator `z` has degree `< n`. Member `0` is
`zkpm` (the three-factor mask, degree `≤ 3 ≤ n` via `idx.zk_three`) times a
`z·shiftSide − shiftRow z·sigmaSide` product difference (degree `≤ 8n`), so `≤ 9n`; members
`1,2` are `(z − 1)·lagNumer` of degree `< 2n ≤ 9n`. -/
private theorem permConstraints_natDegree_le [NeZero n] (idx : Index F n)
    (wTab : Fin n → Fin wCols → F) (z : Polynomial F) (hz : z.natDegree < n) (β γ : F)
    (s : Fin 3) :
    (Permutation.constraints idx.omega idx.zkRows z (idx.permWitnessPoly wTab)
        (Permutation.sigmaPoly idx.omega idx.zkRows idx.shifts idx.wiringPerm) idx.shifts β γ
        (⟨0, Nat.pos_of_neZero n⟩ : Fin n) idx.unmaskedEnd s).natDegree
      ≤ degreeBound n := by
  set w := idx.permWitnessPoly wTab with hw
  set σ := Permutation.sigmaPoly idx.omega idx.zkRows idx.shifts idx.wiringPerm with hσ
  -- The cell interpolants underneath both row products have `natDegree < n`.
  have hwdeg : ∀ i : Fin permCols, (w i).natDegree < n := fun i => by
    rw [hw]; exact columnPoly_natDegree_lt idx.omega_prim _
  have hσdeg : ∀ i : Fin permCols, (σ i).natDegree < n := fun i => by
    rw [hσ]; exact columnPoly_natDegree_lt idx.omega_prim _
  -- The three-factor zk mask has degree ≤ 3, and `3 ≤ n` via `zk_three` + `zk_le`.
  have hzkbound : (zkpm idx.omega n idx.zkRows).natDegree ≤ n := by
    have h3n : 3 ≤ n := le_trans idx.zk_three idx.zk_le
    have h1 : ∀ e : ℕ, ((X : Polynomial F) - C (idx.omega ^ e)).natDegree ≤ 1 := fun e =>
      le_trans (natDegree_sub_le _ _) (by simp [natDegree_X, natDegree_C])
    unfold zkpm
    refine le_trans natDegree_mul_le ?_
    have h2 : ((X - C (idx.omega ^ (n - idx.zkRows)))
        * (X - C (idx.omega ^ (n - idx.zkRows + 1)))).natDegree ≤ 2 := by
      have := h1 (n - idx.zkRows)
      have := h1 (n - idx.zkRows + 1)
      exact le_trans natDegree_mul_le (by omega)
    have := h1 (n - 1)
    omega
  -- Each row-product factor has degree ≤ n (a cell `< n`, plus a constant, plus a
  -- degree-≤1 shift term), so the 7-fold product is ≤ 7n.
  have hshift : (shiftSide w idx.shifts β γ).natDegree ≤ 7 * n := by
    unfold shiftSide
    refine le_trans (natDegree_prod_le _ _) ?_
    have hfac : ∀ i ∈ (Finset.univ : Finset (Fin permCols)),
        (w i + C γ + C β * C (idx.shifts i) * X).natDegree ≤ n := by
      intro i _
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans (natDegree_add_le _ _) (max_le (le_of_lt (hwdeg i)) ?_)
        rw [natDegree_C]; omega
      · refine le_trans natDegree_mul_le ?_
        rw [natDegree_X, ← C_mul, natDegree_C]; omega
    refine le_trans (Finset.sum_le_sum hfac) ?_
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hsigma : (sigmaSide w σ β γ).natDegree ≤ 7 * n := by
    unfold sigmaSide
    refine le_trans (natDegree_prod_le _ _) ?_
    have hfac : ∀ i ∈ (Finset.univ : Finset (Fin permCols)),
        (w i + C γ + C β * σ i).natDegree ≤ n := by
      intro i _
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans (natDegree_add_le _ _) (max_le (le_of_lt (hwdeg i)) ?_)
        rw [natDegree_C]; omega
      · exact le_trans natDegree_mul_le (by rw [natDegree_C]; simpa using le_of_lt (hσdeg i))
    refine le_trans (Finset.sum_le_sum hfac) ?_
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- The two boundary numerators have degree < n.
  have hlag : ∀ r : Fin n, (lagNumer idx.omega r).natDegree < n := by
    intro r
    unfold lagNumer
    exact lt_of_le_of_lt (natDegree_C_mul_le _ _) (columnPoly_natDegree_lt idx.omega_prim _)
  have hz1 : (z - 1).natDegree < n := by
    refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
    rw [natDegree_one]; omega
  fin_cases s <;> simp only [Permutation.constraints]
  · -- Member 0: zkpm · (z·shiftSide − shiftRow z·sigmaSide), degree ≤ n + 8n = 9n.
    have hA : (z * shiftSide w idx.shifts β γ).natDegree ≤ 8 * n :=
      le_trans natDegree_mul_le (by omega)
    have hB : (shiftRow idx.omega z * sigmaSide w σ β γ).natDegree ≤ 8 * n := by
      have hsr := shiftRow_natDegree_le (ω := idx.omega) z
      exact le_trans natDegree_mul_le (by omega)
    refine le_trans natDegree_mul_le ?_
    have hdiff : (z * shiftSide w idx.shifts β γ
        - shiftRow idx.omega z * sigmaSide w σ β γ).natDegree ≤ 8 * n :=
      le_trans (natDegree_sub_le _ _) (max_le hA hB)
    unfold degreeBound; omega
  · -- Member 1: (z − 1) · lagNumer r₀, degree < 2n.
    have := hlag (⟨0, Nat.pos_of_neZero n⟩ : Fin n)
    refine le_trans natDegree_mul_le ?_
    unfold degreeBound; omega
  · -- Member 2: (z − 1) · lagNumer r₁, degree < 2n.
    have := hlag idx.unmaskedEnd
    refine le_trans natDegree_mul_le ?_
    unfold degreeBound; omega

/-! ## The headlines

The three bounds the caller passes to `Index.satisfies_of_evalCheck`. -/


variable [NeZero n]

/-- **Every family member fits under `degreeBound n`.** Case-split the `dif` in
`fullFamily`: below `gateAlphaCount` it is a gate member (`gateMember_natDegree_le`);
above, a permutation member (`permConstraints_natDegree_le`). This is the per-member input
to the aggregate bound. -/
private theorem fullFamily_natDegree_le (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (z : Polynomial F) (hz : z.natDegree < n) (β γ : F)
    (k : Fin (gateAlphaCount + permAlphaCount)) :
    (idx.fullFamily pub wTab z β γ k).natDegree ≤ degreeBound n := by
  unfold Index.fullFamily
  by_cases h : (k : ℕ) < gateAlphaCount
  · rw [dif_pos h]
    exact gateMember_natDegree_le idx pub wTab k
  · rw [dif_neg h]
    exact permConstraints_natDegree_le idx wTab z hz β γ _

/-- **The aggregate-side bound.** The α-aggregate `∑_c α^c • (member c)` fits under
`degreeBound n`: `natDegree_sum_le` reduces to a per-summand bound, `natDegree_smul_le`
drops the scalar `α^c`, and each member is bounded by `fullFamily_natDegree_le`. -/
theorem aggregate_natDegree_le (idx : Index F n) (pub : Fin idx.publicCount → F)
    (wTab : Fin n → Fin wCols → F) (z : Polynomial F) (hz : z.natDegree < n) (β γ : F)
    (α : F) :
    (aggregate α (idx.fullFamily pub wTab z β γ)).natDegree ≤ degreeBound n := by
  unfold aggregate
  apply natDegree_sum_le_of_forall_le
  intro c _
  rw [Polynomial.smul_eq_C_mul]
  exact le_trans (natDegree_C_mul_le _ _)
    (fullFamily_natDegree_le idx pub wTab z hz β γ c)

omit [DecidableEq F] [NeZero n] in
/-- **The quotient-side bound.** With `t.natDegree < 7·n`, the exact quotient product
`t · Z_H` fits under `degreeBound n`: `natDegree_mul_le` and `natDegree (zH F n) = n`
(`zH = Xⁿ − 1`) give `(7n − 1) + n < 9n`. Independent of the index. -/
theorem t_zH_natDegree_le (t : Polynomial F) (ht : t.natDegree < 7 * n) :
    (t * zH F n).natDegree ≤ degreeBound n := by
  have hzH : (zH F n).natDegree = n := by
    rw [zH, ← C_1, natDegree_X_pow_sub_C]
  unfold degreeBound
  calc (t * zH F n).natDegree ≤ t.natDegree + (zH F n).natDegree := natDegree_mul_le
    _ = t.natDegree + n := by rw [hzH]
    _ ≤ 9 * n := by omega


end Kimchi.Index
