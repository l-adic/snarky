import Snarky.Circuit.DSL.Field
import Kimchi.Gate.Semantics.EndoScalar
import Snarky.Circuit.DSL.Assert
import Snarky.Circuit.DSL.Bits
import Snarky.Kimchi.Semantics
import Snarky.Kimchi.Circuit.Utils

/-!
# The EndoScalar gadget

Port of `Snarky.Circuit.Kimchi.EndoScalar`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/EndoScalar.purs): the GLV challenge
decomposition. `toFieldChecked'` witnesses the scalar's 2-bit crumbs in ONE bulk
`exists` — eight per row, MSB-first — then threads the three accumulators through
`mapAccumM`, one `(a8, b8, n8)` witness per row, and emits the `endoScalar` round
list; `toField` pins the reconstruction `n` to the scalar and returns the affine
`a·endo + b`. `toFieldPure` is the constant-space model of the same fold.

Name map: `toField`, `toFieldChecked'`, `toFieldPure` keep their names, namespaced
`EndoScalar` after the PS module's qualified use. `expandToEndoScalar` is
pickles-layer (cross-field transport) and is not ported.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS's type-level `SizedF nBits` sizing renders as the explicit `rows` parameter
  with `16 · rows` bits, and the bit reads go through `[ToNat F]`.
- PS's record `exists` allocates its fields alphabetically; the per-row witness is
  the ordered triple `(a8, b8, n8)`, the same allocation spelled explicitly.
- PS's `aF`/`bF` are the gate's own `cFunc`/`dFunc` tables (their throwing branches
  rendered as the tables' `0`), so the witness folds are stated with them directly.
- `toFieldPure` is generalized from PS's pinned 128 bits to `16 · rows`.
-/

namespace Snarky.Kimchi.EndoScalar

open Snarky

variable {F c : Type}

/-- Crumb `j` (MSB-first) of a `2·count`-bit natural: bits `2(count−j)−1` (high) and
`2(count−j)−2` (low) — the PS `toBits` reversed and paired. -/
private def crumbOfNat (count j k : ℕ) : ℕ :=
  2 * (if k.testBit (2 * (count - j) - 1) then 1 else 0)
    + (if k.testBit (2 * (count - j) - 2) then 1 else 0)

/-- The scalar's crumbs, MSB-first (PS `chunks @2` of the reversed bits) — the honest
crumb list the completeness laws read the gate model at. -/
def crumbsOfNat [NatCast F] (count k : ℕ) : List F :=
  (List.range count).map fun j => (crumbOfNat count j k : F)

/-- The crumb table the bulk witness writes: row `r`'s entry `j` is crumb `8r + j`. -/
private def crumbVals [NatCast F] (rows k : ℕ) : Vector (Vector F 8) rows :=
  Vector.ofFn fun r => Vector.ofFn fun j =>
    (crumbOfNat (8 * rows) (8 * r.1 + j.1) k : F)

/-- The scalar's MSB-first 2-bit crumbs, eight per row. -/
private def crumbsWit [Field F] [ToNat F] (rows : ℕ) (scalar : FVar F) :
    AsProver F (Vector (Vector F 8) rows) := do
  let v ← AsProver.readCVar scalar
  pure (crumbVals rows (ToNat.toNat v))

/-- One row's accumulator witness: fold the row's eight crumbs into the three
accumulators over the gate's bare tables, returned in the allocation order
`(a8, b8, n8)`. -/
private def rowWit [Field F] [DecidableEq F] (xs : Vector (FVar F) 8)
    (st : FVar F × FVar F × FVar F) : AsProver F (F × F × F) := do
  let a0 ← AsProver.readCVar st.1
  let b0 ← AsProver.readCVar st.2.1
  let n0 ← AsProver.readCVar st.2.2
  let vals ← xs.toList.mapM AsProver.readCVar
  pure (vals.foldl (fun acc x => 2 * acc + Kimchi.Gate.EndoScalar.cFunc x) a0,
        vals.foldl (fun acc x => 2 * acc + Kimchi.Gate.EndoScalar.dFunc x) b0,
        vals.foldl (fun acc x => 4 * acc + x) n0)

/-- The gate emitter (PS `toFieldChecked'`; OCaml
`Pickles.Scalar_challenge.to_field_checked'`): the bulk crumb witness, the
accumulator rounds, one `endoScalar` constraint — returning the raw `(a, b, n)`
accumulators with no wrapper constraints. -/
def toFieldChecked' [Field F] [DecidableEq F] [ToNat F] [KimchiSystem F c]
    (rows : ℕ) (scalar : FVar F) :
    CircuitM F c (FVar F × FVar F × FVar F) := do
  let crumbs ← witness (val := Vector (Vector F 8) rows) (crumbsWit rows scalar)
  let (rounds, fin) ← mapAccumM
    (fun (st : FVar F × FVar F × FVar F) (xs : Vector (FVar F) 8) => do
      let w ← witness (val := F × F × F) (rowWit xs st)
      pure (({ n0 := st.2.2, n8 := w.2.2, a0 := st.1, a8 := w.1,
               b0 := st.2.1, b8 := w.2.1, xs } : EndoScalarRound F),
            (w.1, w.2.1, w.2.2)))
    (.const 2, .const 2, .const 0) crumbs.toList
  addConstraint (KimchiSystem.endoScalar rounds)
  pure fin

/-- The checked decomposition (PS `toField`; OCaml `to_field_checked`): the gate,
the pin `n = scalar`, and the affine reconstruction `a·endo + b` — folded
constraint-free when the endo coefficient is a constant. -/
def toField [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]
    (rows : ℕ) (scalar endo : FVar F) : CircuitM F c (FVar F) := do
  let (a, b, n) ← toFieldChecked' (c := c) rows scalar
  assertEqual n scalar
  match endo with
  | .const e => pure (CVar.add_ (CVar.scale_ e a) b)
  | _ => do
    let p ← mul a endo
    pure (CVar.add_ b p)

/-- The pure model (PS `toFieldPure`): the same MSB-first bit-pair fold on values,
from the accumulator seeds `(2, 2)`. -/
def toFieldPure [Field F] [ToNat F] (rows : ℕ) (scalar endo : F) : F :=
  let n := ToNat.toNat scalar
  let acc := (List.range (8 * rows)).foldl
    (fun (st : F × F) i =>
      let s : F := if n.testBit (16 * rows - 2 - 2 * i) then 1 else -1
      if n.testBit (16 * rows - 1 - 2 * i) then (2 * st.1 + s, 2 * st.2)
      else (2 * st.1, 2 * st.2 + s))
    (2, 2)
  acc.1 * endo + acc.2

/-! ## Soundness

`toFieldChecked'_spec`: any satisfying valuation exhibits a valid crumb list whose
gate-model decompositions (`Kimchi.Gate.EndoScalar.decomposeA`/`decomposeB`/
`nReconstruct` — the emitter's seeds `(2, 2, 0)` are theirs) carry the three
returned accumulators. The loop's invariant is structural only — the witnesses
promise nothing; the content arrives at the constraint after the loop. -/

/-- The loop's structural view: the collected rounds are the chain-threaded records
over the traversed chunks — each round's inputs are the previous round's output
variables, from `st` to `fin`. Valuation-free: the soundness invariant carries shape
only; the values arrive with the constraint after the loop. -/
private def Threaded : (FVar F × FVar F × FVar F) → List (Vector (FVar F) 8) →
    List (EndoScalarRound F) → (FVar F × FVar F × FVar F) → Prop
  | st, [], rounds, fin => rounds = [] ∧ fin = st
  | st, xs :: rest, rounds, fin =>
    ∃ w tail,
      rounds = ({ n0 := st.2.2, n8 := w.2.2, a0 := st.1, a8 := w.1,
                  b0 := st.2.1, b8 := w.2.1, xs } : EndoScalarRound F) :: tail ∧
      Threaded w rest tail fin

/-- One more chunk extends a threading at the tail. -/
private theorem Threaded.snoc :
    ∀ {st fin : FVar F × FVar F × FVar F} {pref : List (Vector (FVar F) 8)}
      {rounds : List (EndoScalarRound F)},
      Threaded st pref rounds fin →
      ∀ (xs : Vector (FVar F) 8) (w : FVar F × FVar F × FVar F),
      Threaded st (pref ++ [xs])
        (rounds ++ [{ n0 := fin.2.2, n8 := w.2.2, a0 := fin.1, a8 := w.1,
                      b0 := fin.2.1, b8 := w.2.1, xs }]) w
  | st, fin, [], rounds, h, xs, w => by
    obtain ⟨hr, hfin⟩ := h
    subst hr hfin
    exact ⟨w, [], rfl, rfl, rfl⟩
  | st, fin, chunk :: rest, rounds, h, xs, w => by
    obtain ⟨w', tail, hr, hrest⟩ := h
    subst hr
    exact ⟨w', tail ++ [_], rfl, hrest.snoc xs w⟩

/-- A satisfied threading folds: every round's gate law chains through the shared
accumulator variables, so `fin` reads as the bare-table folds of the concatenated
crumb values from `st`'s values. -/
private theorem threaded_sound [Field F] [DecidableEq F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (V : Valuation F) :
    ∀ (pref : List (Vector (FVar F) 8)) (st fin : FVar F × FVar F × FVar F)
      (rounds : List (EndoScalarRound F)),
      Threaded st pref rounds fin →
      (∀ r ∈ rounds, Kimchi.Gate.EndoScalar.Holds (EndoScalarRound.read V r)) →
      ∃ crumbs : List F,
        (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
        crumbs.length = 8 * pref.length ∧
        fin.1.val V = crumbs.foldl
          (fun a x => 2 * a + Kimchi.Gate.EndoScalar.cFunc x) (st.1.val V) ∧
        fin.2.1.val V = crumbs.foldl
          (fun b x => 2 * b + Kimchi.Gate.EndoScalar.dFunc x) (st.2.1.val V) ∧
        fin.2.2.val V = crumbs.foldl (fun n x => 4 * n + x) (st.2.2.val V)
  | [], st, fin, rounds, h, _ => by
    obtain ⟨hr, hfin⟩ := h
    subst hr hfin
    exact ⟨[], by simp, by simp, rfl, rfl, rfl⟩
  | chunk :: rest, st, fin, rounds, h, hHolds => by
    obtain ⟨w, tail, hr, hrest⟩ := h
    subst hr
    have hs := Kimchi.Gate.EndoScalar.sound h2 h3 _ (hHolds _ (List.mem_cons_self ..))
    obtain ⟨hvalid, hn, ha, hb⟩ := hs
    simp only [EndoScalarRound.read] at hvalid hn ha hb
    obtain ⟨crumbs', hvalid', hlen', ha', hb', hn'⟩ :=
      threaded_sound h2 h3 V rest w fin tail hrest
        (fun r hr => hHolds r (List.mem_cons_of_mem _ hr))
    refine ⟨chunk.toList.map (·.val V) ++ crumbs', ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hvalid x hx
      · exact hvalid' x hx
    · simp only [List.length_append, List.length_map, Vector.length_toList,
        List.length_cons, hlen']
      omega
    · rw [List.foldl_append, ← ha, ha']
    · rw [List.foldl_append, ← hb, hb']
    · rw [List.foldl_append, ← hn, hn']

open Std.Do in
/-- The gate emitter is sound: some valid crumb list of length `8·rows` carries the
returned `(a, b, n)` as its gate-model decompositions — the emitter's seeds
`(2, 2, 0)` are theirs. The characteristic hypotheses are the gate's own (`sound`
interpolates the tables from the cubics). -/
theorem toFieldChecked'_spec [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (rows : ℕ) (scalar : FVar F)
    (Q : PostCond (FVar F × FVar F × FVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : FVar F × FVar F × FVar F) =>
        ∃ crumbs : List F,
          (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
          crumbs.length = 8 * rows ∧
          r.1.val V = Kimchi.Gate.EndoScalar.decomposeA crumbs ∧
          r.2.1.val V = Kimchi.Gate.EndoScalar.decomposeB crumbs ∧
          r.2.2.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs) Q⦄
    (toFieldChecked' (c := KimchiConstraint F) rows scalar)
    ⦃Q⦄ := by
  simp only [toFieldChecked', mapAccumM]
  mvcgen
  rename_i s hpre
  intro crumbVars _
  mvcgen
  case inv1 =>
    exact ⇓ p s' => ⌜s'.V = s.V ∧
      Threaded (.const 2, .const 2, .const 0) p.1.prefix p.2.snd p.2.fst⌝
  case vc2.vc1.pre =>
    exact ⟨rfl, rfl, rfl⟩
  case vc1.step =>
    rename_i pref cur suff hsplit b st' hinv
    intro r nv'
    mvcgen
    obtain ⟨hV, hthr⟩ := hinv
    exact ⟨hV, hthr.snoc cur r⟩
  case vc3.vc1.post.success =>
    rename_i fin st' hinv
    obtain ⟨hV, hthr⟩ := hinv
    intro _ nv' hpay _
    rw [hV]
    refine hpre fin.fst nv' ?_
    have hHolds : ∀ r ∈ fin.snd,
        Kimchi.Gate.EndoScalar.Holds (EndoScalarRound.read s.V r) := by
      have h := hpay
      rw [hV] at h
      exact h
    obtain ⟨crumbs, hvalid, hlen, ha, hb, hn⟩ :=
      threaded_sound h2 h3 s.V crumbVars.toList _ fin.fst fin.snd hthr hHolds
    refine ⟨crumbs, hvalid, by simpa using hlen, ?_, ?_, ?_⟩
    · rw [Kimchi.Gate.EndoScalar.decomposeA_eq_table h2 h3 hvalid]
      simpa [CVar.val] using ha
    · rw [Kimchi.Gate.EndoScalar.decomposeB_eq_table h2 h3 hvalid]
      simpa [CVar.val] using hb
    · simpa [Kimchi.Gate.EndoScalar.nReconstruct, CVar.val] using hn

open Std.Do in
/-- The checked decomposition is sound: the result reads as the gate model's
`toField` — `a·endo + b` — over some valid crumb list of length `8·rows` whose
`nReconstruct` is the scalar. -/
theorem toField_spec [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (rows : ℕ) (scalar endo : FVar F)
    (Q : PostCond (FVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : FVar F) =>
        ∃ crumbs : List F,
          (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
          crumbs.length = 8 * rows ∧
          r.val V = Kimchi.Gate.EndoScalar.toField crumbs (endo.val V) ∧
          scalar.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs) Q⦄
    (toField (c := KimchiConstraint F) rows scalar endo)
    ⦃Q⦄ := by
  simp only [toField]
  mvcgen
  rename_i s hpre
  refine toFieldChecked'_spec h2 h3 rows scalar _ _ ?_
  intro abn nv1 ⟨crumbs, hvalid, hlen, ha, hb, hn⟩
  mvcgen
  intro _ nv2 heq
  split
  · rename_i e
    mvcgen
    refine hpre _ _ ?_
    refine ⟨crumbs, hvalid, hlen, ?_, by rw [← heq, hn]⟩
    simp only [Kimchi.Gate.EndoScalar.toField, CVar.val_add_, CVar.val_scale_,
      ha, hb, CVar.val]
    ring
  · mvcgen
    intro p nv3 hp
    mvcgen
    refine hpre _ _ ?_
    refine ⟨crumbs, hvalid, hlen, ?_, by rw [← heq, hn]⟩
    simp only [Kimchi.Gate.EndoScalar.toField]
    rw [CVar.val_add_, hp, ha, hb]
    ring

/-! ## Completeness

The honest prover run accepts, and the results read as the gate model at the
scalar's own crumbs (`crumbsOfNat`). The emitter needs only a readable scalar; the
checked decomposition's `n = scalar` pin adds the boundary conditions of the
representative — faithfulness and the `4 ^ (8·rows)` range. The crumb lemmas below
are ℕ-side positional arithmetic; the loop's invariant carries the accumulator
reads and the collected rounds' checks across table growth. -/

/-- Every crumb is a valid 2-bit value. -/
private theorem crumbOfNat_cast_valid [Field F] (count j k : ℕ) :
    ((crumbOfNat count j k : ℕ) : F) = 0 ∨ ((crumbOfNat count j k : ℕ) : F) = 1
      ∨ ((crumbOfNat count j k : ℕ) : F) = 2 ∨ ((crumbOfNat count j k : ℕ) : F) = 3 := by
  unfold crumbOfNat
  by_cases h1 : k.testBit (2 * (count - j) - 1) <;>
    by_cases h0 : k.testBit (2 * (count - j) - 2) <;> simp [h1, h0]

/-- Every extracted crumb is a valid 2-bit value — what the gate's completeness
consumes. -/
private theorem crumbsOfNat_valid [Field F] (count k : ℕ) :
    ∀ x ∈ crumbsOfNat (F := F) count k, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  intro x hx
  simp only [crumbsOfNat, List.mem_map, List.mem_range] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact crumbOfNat_cast_valid count j k

/-- A crumb is a base-4 digit read from the top: crumb `j` of a `count`-crumb
challenge is digit `count−1−j` of its value. -/
private theorem crumbOfNat_eq_digit (count j k : ℕ) (hj : j < count) :
    crumbOfNat count j k = k / 4 ^ (count - 1 - j) % 4 := by
  have hm1 : 2 * (count - j) - 1 = 1 + 2 * (count - 1 - j) := by omega
  have hm2 : 2 * (count - j) - 2 = 0 + 2 * (count - 1 - j) := by omega
  rw [crumbOfNat, hm1, hm2]
  set m := count - 1 - j
  have h4 : (4 : ℕ) ^ m = 2 ^ (2 * m) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [h4, ← Nat.testBit_div_two_pow, ← Nat.testBit_div_two_pow,
    Nat.testBit_add_one, Nat.testBit_zero, Nat.testBit_zero]
  set q := k / 2 ^ (2 * m)
  rcases Nat.mod_two_eq_zero_or_one (q / 2) with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one q with h0 | h0 <;>
      simp [h1, h0] <;> omega

/-- Casting a base-4 Horner fold out of `ℕ`. -/
private theorem foldl_horner_cast [Semiring F] :
    ∀ (l : List ℕ) (a : ℕ),
      (l.map (Nat.cast (R := F))).foldl (fun n x => 4 * n + x) (a : F)
        = ((l.foldl (fun n x => 4 * n + x) a : ℕ) : F)
  | [], _ => rfl
  | x :: xs, a => by
    simp only [List.map_cons, List.foldl_cons]
    rw [show ((4 : F) * a + x) = ((4 * a + x : ℕ) : F) by push_cast; ring_nf]
    exact foldl_horner_cast xs (4 * a + x)

/-- The Horner reconstruction at `ℕ`: the MSB-first crumbs fold back to the value
modulo `4^count`. -/
private theorem crumbsOfNat_foldl_nat (count k : ℕ) :
    ((List.range count).map fun j => crumbOfNat count j k).foldl
      (fun n x => 4 * n + x) 0 = k % 4 ^ count := by
  induction count generalizing k with
  | zero => simp [Nat.mod_one]
  | succ c ih =>
    rw [List.range_succ, List.map_append, List.foldl_append]
    have hmap : (List.range c).map (fun j => crumbOfNat (c + 1) j k)
        = (List.range c).map (fun j => crumbOfNat c j (k / 4)) := by
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      rw [crumbOfNat_eq_digit (c + 1) j k (by omega),
        crumbOfNat_eq_digit c j (k / 4) hj,
        show c + 1 - 1 - j = (c - 1 - j) + 1 by omega, pow_succ,
        mul_comm ((4 : ℕ) ^ (c - 1 - j)) 4, ← Nat.div_div_eq_div_mul]
    have hlast : crumbOfNat (c + 1) c k = k % 4 := by
      rw [crumbOfNat_eq_digit (c + 1) c k (by omega)]
      simp
    rw [hmap, ih]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [hlast]
    have hM : (0 : ℕ) < 4 ^ c := pow_pos (by norm_num) c
    have hkdecomp : k = 4 * (k / 4 % 4 ^ c) + k % 4 + 4 ^ (c + 1) * (k / 4 / 4 ^ c) := by
      have h1 := Nat.div_add_mod k 4
      have h2 := Nat.div_add_mod (k / 4) (4 ^ c)
      calc k = 4 * (k / 4) + k % 4 := h1.symm
        _ = 4 * (4 ^ c * (k / 4 / 4 ^ c) + k / 4 % 4 ^ c) + k % 4 := by rw [h2]
        _ = 4 * (k / 4 % 4 ^ c) + k % 4 + 4 ^ (c + 1) * (k / 4 / 4 ^ c) := by ring
    have hlt : 4 * (k / 4 % 4 ^ c) + k % 4 < 4 ^ (c + 1) := by
      have hr := Nat.mod_lt (k / 4) hM
      have hs := Nat.mod_lt k (show 0 < 4 by norm_num)
      have h41 : (4 : ℕ) ^ (c + 1) = 4 * 4 ^ c := by ring
      omega
    conv_rhs => rw [hkdecomp]
    rw [Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt hlt).symm

/-- The register reconstruction recovers the challenge: the gate's `n` fold over the
extracted crumbs is the value itself, for values in range — what `toField`'s
`n = scalar` pin consumes. -/
private theorem crumbsOfNat_reconstruct [Field F] (count k : ℕ) (hk : k < 4 ^ count) :
    Kimchi.Gate.EndoScalar.nReconstruct (crumbsOfNat (F := F) count k) = (k : F) := by
  unfold Kimchi.Gate.EndoScalar.nReconstruct crumbsOfNat
  rw [show ((List.range count).map fun j => ((crumbOfNat count j k : ℕ) : F))
      = ((List.range count).map fun j => crumbOfNat count j k).map Nat.cast by
    rw [List.map_map]; rfl]
  rw [show (0 : F) = ((0 : ℕ) : F) by norm_num, foldl_horner_cast,
    crumbsOfNat_foldl_nat, Nat.mod_eq_of_lt hk]

/-- Flattening the row-chunked table recovers the flat MSB-first stream. -/
private theorem flatten_ofFn_rows {F : Type} (g : ℕ → F) :
    ∀ m : ℕ,
      (List.ofFn fun r : Fin m => List.ofFn fun j : Fin 8 => g (8 * r.1 + j.1)).flatten
        = (List.range (8 * m)).map g
  | 0 => by simp
  | m + 1 => by
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simp only [Fin.val_castSucc]
    rw [flatten_ofFn_rows g m, show 8 * (m + 1) = 8 * m + 8 by ring, List.range_add,
      List.map_append, List.map_map]
    congr 1

/-- The bulk witness's table, flattened, is the crumb stream. -/
private theorem crumbVals_flatten [NatCast F] (rows k : ℕ) :
    ((crumbVals (F := F) rows k).toList.map Vector.toList).flatten
      = crumbsOfNat (8 * rows) k := by
  show ((Vector.ofFn _).toList.map Vector.toList).flatten = _
  rw [Vector.toList_ofFn, List.map_ofFn]
  exact flatten_ofFn_rows (fun i => (crumbOfNat (8 * rows) i k : F)) rows

/-- The value-level row step: the three accumulator folds of one row. -/
private def accStep [Field F] [DecidableEq F] (st : F × F × F) (xs : List F) :
    F × F × F :=
  (xs.foldl (fun a x => 2 * a + Kimchi.Gate.EndoScalar.cFunc x) st.1,
   xs.foldl (fun b x => 2 * b + Kimchi.Gate.EndoScalar.dFunc x) st.2.1,
   xs.foldl (fun n x => 4 * n + x) st.2.2)

/-- Row-stepping is folding the concatenated crumbs. -/
private theorem accStep_foldl [Field F] [DecidableEq F] :
    ∀ (rs : List (List F)) (st : F × F × F),
      rs.foldl accStep st
        = (rs.flatten.foldl (fun a x => 2 * a + Kimchi.Gate.EndoScalar.cFunc x) st.1,
           rs.flatten.foldl (fun b x => 2 * b + Kimchi.Gate.EndoScalar.dFunc x) st.2.1,
           rs.flatten.foldl (fun n x => 4 * n + x) st.2.2)
  | [], st => rfl
  | r :: rs, st => by
    simp only [List.foldl_cons, List.flatten_cons, List.foldl_append]
    exact accStep_foldl rs _

/-- Element reads assemble into the list read. -/
private theorem mapM_eval_ok [Add F] [Mul F] {env : Assignments F} :
    ∀ {xs : List (FVar F)} {vs : List F}, xs.length = vs.length →
      (∀ j (hj : j < xs.length) (hj' : j < vs.length), xs[j].eval env = .ok vs[j]) →
      xs.mapM (CVar.eval · env) = .ok vs
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | x :: xs, v :: vs, hlen, hj => by
    have h0 := hj 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    have ih := mapM_eval_ok (env := env) (xs := xs) (vs := vs) (by simpa using hlen)
      (fun j hj1 hj2 => by
        have := hj (j + 1) (by simpa using hj1) (by simpa using hj2)
        simpa only [List.getElem_cons_succ] using this)
    simp [List.mapM_cons, h0, ih, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- List reads survive table extension. -/
private theorem mapM_eval_le [Add F] [Mul F] {env env' : Assignments F}
    (hle : env.Le env') :
    ∀ {xs : List (FVar F)} {vs : List F},
      xs.mapM (CVar.eval · env) = .ok vs → xs.mapM (CVar.eval · env') = .ok vs
  | [], _, h => h
  | x :: xs, vs, h => by
    cases he : x.eval env with
    | error e => simp [List.mapM_cons, he, Bind.bind, Except.bind] at h
    | ok y =>
      cases hr : xs.mapM (CVar.eval · env) with
      | error e => simp [List.mapM_cons, he, hr, Bind.bind, Except.bind] at h
      | ok ys =>
        simp only [List.mapM_cons, he, hr, Bind.bind, Except.bind, Pure.pure,
          Except.pure] at h
        simp [List.mapM_cons, CVar.eval_le hle he, mapM_eval_le hle hr, Bind.bind,
          Except.bind, Pure.pure, Except.pure, h]

/-- The prover-side list read is the elementwise read. -/
private theorem readAll_ok [Add F] [Mul F] {env : Assignments F} :
    ∀ {xs : List (FVar F)} {vs : List F},
      xs.mapM (CVar.eval · env) = .ok vs →
      (xs.mapM AsProver.readCVar) env = .ok vs
  | [], vs, h => h
  | x :: xs, vs, h => by
    cases he : x.eval env with
    | error e => simp [List.mapM_cons, he, Bind.bind, Except.bind] at h
    | ok y =>
      cases hr : xs.mapM (CVar.eval · env) with
      | error e => simp [List.mapM_cons, he, hr, Bind.bind, Except.bind] at h
      | ok ys =>
        simp only [List.mapM_cons, he, hr, Bind.bind, Except.bind, Pure.pure,
          Except.pure] at h
        simp [List.mapM_cons, AsProver.readCVar, he, readAll_ok hr, Bind.bind,
          ReaderT.bind, Except.bind, Pure.pure, ReaderT.pure, Except.pure, h]

/-- Invert one `Except` bind of a successful run. -/
private theorem bind_ok {α β : Type} {x : Except EvalError α}
    {f : α → Except EvalError β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, by simpa [Bind.bind, Except.bind] using h⟩

/-- A round evaluates to a witness exactly when each register and the crumb list
read as its fields. -/
private theorem round_eval_ok_iff [Field F] [DecidableEq F] {env : Assignments F}
    {r : EndoScalarRound F} {w : Kimchi.Gate.EndoScalar.Witness F} :
    EndoScalarRound.eval env r = .ok w ↔
      r.a0.eval env = .ok w.a0 ∧ r.b0.eval env = .ok w.b0 ∧
      r.n0.eval env = .ok w.n0 ∧ r.a8.eval env = .ok w.a8 ∧
      r.b8.eval env = .ok w.b8 ∧ r.n8.eval env = .ok w.n8 ∧
      r.xs.toList.mapM (CVar.eval · env) = .ok w.crumbs := by
  constructor
  · intro h
    unfold EndoScalarRound.eval at h
    obtain ⟨a0, ha0, h⟩ := bind_ok h
    obtain ⟨b0, hb0, h⟩ := bind_ok h
    obtain ⟨n0, hn0, h⟩ := bind_ok h
    obtain ⟨a8, ha8, h⟩ := bind_ok h
    obtain ⟨b8, hb8, h⟩ := bind_ok h
    obtain ⟨n8, hn8, h⟩ := bind_ok h
    obtain ⟨vs, hxs, h⟩ := bind_ok h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨ha0, hb0, hn0, ha8, hb8, hn8, hxs⟩
  · intro ⟨ha0, hb0, hn0, ha8, hb8, hn8, hxs⟩
    unfold EndoScalarRound.eval
    rw [ha0, hb0, hn0, ha8, hb8, hn8, hxs]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A round's read survives table extension. -/
private theorem round_eval_le [Field F] [DecidableEq F] {env env' : Assignments F}
    (hle : env.Le env') {r : EndoScalarRound F} {w : Kimchi.Gate.EndoScalar.Witness F}
    (h : EndoScalarRound.eval env r = .ok w) :
    EndoScalarRound.eval env' r = .ok w := by
  obtain ⟨ha0, hb0, hn0, ha8, hb8, hn8, hxs⟩ := round_eval_ok_iff.mp h
  exact round_eval_ok_iff.mpr ⟨CVar.eval_le hle ha0, CVar.eval_le hle hb0,
    CVar.eval_le hle hn0, CVar.eval_le hle ha8, CVar.eval_le hle hb8,
    CVar.eval_le hle hn8, mapM_eval_le hle hxs⟩

/-- The collected rounds' check survives table extension. -/
private theorem check_rounds_le [Field F] [DecidableEq F] {env env' : Assignments F}
    (hle : env.Le env') {rounds : List (EndoScalarRound F)}
    (h : KimchiConstraint.check (.endoScalar rounds) env = true) :
    KimchiConstraint.check (.endoScalar rounds) env' = true := by
  simp only [KimchiConstraint.check, List.all_eq_true] at h ⊢
  intro r hr
  have hh := h r hr
  cases he : EndoScalarRound.eval env r with
  | error e => rw [he] at hh; simp at hh
  | ok w =>
    rw [he] at hh
    rw [round_eval_le hle he]
    exact hh

/-- One more element folds onto the prefix. -/
private theorem take_succ_foldl {α β : Type} (f : β → α → β) {l : List α} {k : ℕ}
    (hk : k < l.length) (init : β) :
    (l.take (k + 1)).foldl f init = f ((l.take k).foldl f init) l[k] := by
  rw [List.take_add, List.take_one_drop_eq_of_lt_length hk]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.get_eq_getElem]

/-- Every entry of one witness row is a valid crumb. -/
private theorem crumbVals_row_valid [Field F] (rows n k : ℕ) (hk : k < rows) :
    ∀ x ∈ ((crumbVals (F := F) rows n)[k]'hk).toList,
      x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  intro x hx
  simp only [crumbVals, Vector.getElem_ofFn, Vector.toList_ofFn, List.mem_ofFn] at hx
  obtain ⟨j, rfl⟩ := hx
  exact crumbOfNat_cast_valid _ _ _

/-- One row's accumulator witness computes the row step. -/
private theorem rowWit_ok [Field F] [DecidableEq F] {env : Assignments F}
    {xs : Vector (FVar F) 8} {st : FVar F × FVar F × FVar F} {a b n : F} {vs : List F}
    (ha : st.1.eval env = .ok a) (hb : st.2.1.eval env = .ok b)
    (hn : st.2.2.eval env = .ok n)
    (hxs : xs.toList.mapM (CVar.eval · env) = .ok vs) :
    rowWit xs st env
      = .ok (vs.foldl (fun acc x => 2 * acc + Kimchi.Gate.EndoScalar.cFunc x) a,
             vs.foldl (fun acc x => 2 * acc + Kimchi.Gate.EndoScalar.dFunc x) b,
             vs.foldl (fun acc x => 4 * acc + x) n) := by
  simp [rowWit, AsProver.readCVar, ha, hb, hn, readAll_ok hxs, Bind.bind, ReaderT.bind,
    Except.bind, Pure.pure, ReaderT.pure, Except.pure]

open Std.Do in
/-- The gate emitter is complete: the honest prover run accepts on any readable
scalar — no range condition — and the returned accumulators read as the gate model's
decompositions of the scalar's crumbs. -/
theorem toFieldChecked'_complete_spec [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (rows : ℕ) (scalar : FVar F)
    (Q : PostCond (FVar F × FVar F × FVar F)
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (scalar.eval env).isOk)
        (fun env r env' => ∀ vv, scalar.eval env = .ok vv →
          r.1.eval env' = .ok (Kimchi.Gate.EndoScalar.decomposeA
            (crumbsOfNat (8 * rows) (ToNat.toNat vv))) ∧
          r.2.1.eval env' = .ok (Kimchi.Gate.EndoScalar.decomposeB
            (crumbsOfNat (8 * rows) (ToNat.toNat vv))) ∧
          r.2.2.eval env' = .ok (Kimchi.Gate.EndoScalar.nReconstruct
            (crumbsOfNat (8 * rows) (ToNat.toNat vv)))) Q⦄
    (toFieldChecked' (c := KimchiProverC F) rows scalar)
    ⦃Q⦄ := by
  simp only [toFieldChecked', mapAccumM]
  mvcgen
  rename_i st₀ hpre
  obtain ⟨hoks, hk⟩ := hpre
  obtain ⟨vv, hv⟩ := CVar.evalOk hoks
  have hwit : crumbsWit rows scalar st₀.env
      = .ok (crumbVals rows (ToNat.toNat vv)) := by
    simp [crumbsWit, AsProver.readCVar, hv, Bind.bind, ReaderT.bind, Except.bind,
      Pure.pure, ReaderT.pure, Except.pure]
  refine ⟨by rw [hwit]; rfl, fun crumbVars st₁ hgrant hle₁ => ?_⟩
  have hread := hgrant _ hwit
  mvcgen
  case inv1 =>
    exact ⇓ p s' => ⌜st₁.env.Le s'.env ∧
      (let stv := (((crumbVals (F := F) rows (ToNat.toNat vv)).toList.map
          Vector.toList).take p.1.prefix.length).foldl accStep (2, 2, 0)
       p.2.fst.1.eval s'.env = .ok stv.1 ∧
       p.2.fst.2.1.eval s'.env = .ok stv.2.1 ∧
       p.2.fst.2.2.eval s'.env = .ok stv.2.2) ∧
      KimchiConstraint.check (.endoScalar p.2.snd) s'.env = true⌝
  case vc1.step =>
    rename_i pref cur suff hsplit b s' hinv
    obtain ⟨hLe, hacc, hcheck⟩ := hinv
    obtain ⟨hA, hB, hN⟩ := hacc
    have hkrows : pref.length < rows := by
      have hlen := congrArg List.length hsplit
      simp only [Vector.length_toList, List.length_append, List.length_cons] at hlen
      omega
    have hcur : cur = crumbVars[pref.length]'hkrows := by
      have h1 : crumbVars.toList[pref.length]'(by
          simp only [Vector.length_toList]; omega) = cur := by
        simp only [hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      rw [← h1, Vector.getElem_toList]
    subst hcur
    have hxs : (crumbVars[pref.length]'hkrows).toList.mapM (CVar.eval · s'.env)
        = .ok ((crumbVals (F := F) rows (ToNat.toNat vv))[pref.length]'hkrows).toList := by
      refine mapM_eval_ok (by simp) ?_
      intro j hj hj'
      simp only [Vector.length_toList] at hj
      simp only [Vector.getElem_toList]
      exact CVar.eval_le hLe (hread pref.length hkrows j hj)
    have hrow := rowWit_ok (env := s'.env) hA hB hN hxs
    refine ⟨by rw [hrow]; rfl, fun r st' hgrant' hle' => ?_⟩
    have hw := hgrant' _ hrow
    have heval : EndoScalarRound.eval st'.env
        { n0 := b.fst.2.2, n8 := r.2.2, a0 := b.fst.1, a8 := r.1,
          b0 := b.fst.2.1, b8 := r.2.1, xs := crumbVars[pref.length]'hkrows }
        = .ok (Kimchi.Gate.EndoScalar.buildTable _ _ _
            ((crumbVals (F := F) rows (ToNat.toNat vv))[pref.length]'hkrows).toList) :=
      round_eval_ok_iff.mpr ⟨CVar.eval_le hle' hA, CVar.eval_le hle' hB,
        CVar.eval_le hle' hN, hw.1, hw.2.1, hw.2.2, mapM_eval_le hle' hxs⟩
    mvcgen
    refine ⟨hLe.trans hle', ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [take_succ_foldl accStep (by simp [hkrows]) (2, 2, 0)]
      simp only [List.getElem_map, Vector.getElem_toList]
      exact ⟨hw.1, hw.2.1, hw.2.2⟩
    · simp only [KimchiConstraint.check, List.all_append, List.all_cons, List.all_nil,
        Bool.and_eq_true, and_true]
      refine ⟨?_, ?_⟩
      · simpa only [KimchiConstraint.check] using check_rounds_le hle' hcheck
      · simp only [heval]
        exact (Kimchi.Gate.EndoScalar.ok_iff _).mpr
          (Kimchi.Gate.EndoScalar.complete_table h2 h3 _ _ _ _
            (crumbVals_row_valid rows (ToNat.toNat vv) pref.length hkrows))
  case vc2.vc1.pre =>
    refine ⟨Assignments.Le.refl st₁.env, ⟨?_, ?_, ?_⟩,
        by simp [KimchiConstraint.check]⟩ <;>
      simp [CVar.eval]
  case vc3.vc1.post.success =>
    rename_i fin s' hinv
    obtain ⟨hLe, hacc, hcheck⟩ := hinv
    obtain ⟨hA, hB, hN⟩ := hacc
    rw [List.take_of_length_le (by simp)] at hA hB hN
    rw [accStep_foldl, crumbVals_flatten] at hA hB hN
    refine addConstraint_complete_spec (c := KimchiConstraint F)
      (KimchiSystem.endoScalar fin.snd) (fun a => wp⟦pure fin.fst⟧ Q, Q.2) s'
      ⟨hcheck, fun u st₂ _ hle₂ => ?_⟩
    simp only [wp, PredTrans.apply, prove]
    intro hf
    refine hk fin.fst ⟨st₂.nv, st₂.env, hf⟩ (fun vv' hv' => ?_)
      (hle₁.trans (hLe.trans hle₂))
    rw [hv] at hv'
    injection hv' with hv'
    subst hv'
    have hvalid := crumbsOfNat_valid (F := F) (8 * rows) (ToNat.toNat vv)
    refine ⟨?_, ?_, ?_⟩
    · rw [Kimchi.Gate.EndoScalar.decomposeA_eq_table h2 h3 hvalid]
      exact CVar.eval_le hle₂ hA
    · rw [Kimchi.Gate.EndoScalar.decomposeB_eq_table h2 h3 hvalid]
      exact CVar.eval_le hle₂ hB
    · exact CVar.eval_le hle₂ hN
  case vc4.vc1.post.except =>
    exact ExceptConds.entails_false

open Std.Do in
/-- The checked decomposition is complete: the honest prover run accepts on a
readable scalar whose representative is faithful and fits the crumb budget, and the
result reads as the gate model's `toField` at the scalar's crumbs. -/
theorem toField_complete_spec [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (rows : ℕ) (scalar endo : FVar F)
    (Q : PostCond (FVar F) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (scalar.eval env).isOk ∧ (endo.eval env).isOk ∧
          ∀ vv, scalar.eval env = .ok vv →
            ((ToNat.toNat vv : ℕ) : F) = vv ∧ ToNat.toNat vv < 4 ^ (8 * rows))
        (fun env r env' => ∀ vv ev, scalar.eval env = .ok vv →
          endo.eval env = .ok ev →
          r.eval env' = .ok (Kimchi.Gate.EndoScalar.toField
            (crumbsOfNat (8 * rows) (ToNat.toNat vv)) ev)) Q⦄
    (toField (c := KimchiProverC F) rows scalar endo)
    ⦃Q⦄ := by
  simp only [toField]
  mvcgen
  rename_i st₀ hpre
  obtain ⟨⟨hoks, hoke, hbound⟩, hk⟩ := hpre
  obtain ⟨vv, hv⟩ := CVar.evalOk hoks
  obtain ⟨ev, he⟩ := CVar.evalOk hoke
  obtain ⟨hfaith, hlt⟩ := hbound vv hv
  refine toFieldChecked'_complete_spec h2 h3 rows scalar _ _
    ⟨hoks, fun abn st₁ hpost₁ hle₁ => ?_⟩
  obtain ⟨hA, hB, hN⟩ := hpost₁ vv hv
  mvcgen
  refine ⟨⟨by rw [hN]; rfl, by rw [CVar.eval_le hle₁ hv]; rfl,
      fun nv sv hnv hsv => ?_⟩, fun u st₂ hle₂ => ?_⟩
  · rw [hN] at hnv
    injection hnv with hnv
    rw [CVar.eval_le hle₁ hv] at hsv
    injection hsv with hsv
    subst hnv hsv
    rw [crumbsOfNat_reconstruct (8 * rows) (ToNat.toNat vv) hlt, hfaith]
  · split
    · rename_i e
      simp only [wp, PredTrans.apply, prove]
      intro hf
      refine hk _ ⟨st₂.nv, st₂.env, hf⟩ (fun vv' ev' hv' he' => ?_)
        (hle₁.trans hle₂)
      rw [hv] at hv'
      injection hv' with hv'
      subst hv'
      rw [he] at he'
      injection he' with he'
      subst he'
      have hA2 := CVar.eval_le hle₂ hA
      have hB2 := CVar.eval_le hle₂ hB
      have hev : ev = e := by
        simp only [CVar.eval] at he
        exact (Except.ok.inj he).symm
      rw [CVar.eval_add_]
      simp only [CVar.eval, CVar.eval_scale_ hA2 e, hB2, Except.ok.injEq,
        Kimchi.Gate.EndoScalar.toField, hev]
      ring
    · mvcgen
      refine ⟨⟨by rw [CVar.eval_le hle₂ hA]; rfl,
          by rw [CVar.eval_le (hle₁.trans hle₂) he]; rfl⟩,
        fun p st₃ hp hle₃ => ?_⟩
      have hpv := hp _ _ (CVar.eval_le hle₂ hA) (CVar.eval_le (hle₁.trans hle₂) he)
      simp only [wp, PredTrans.apply, prove]
      intro hf
      refine hk _ ⟨st₃.nv, st₃.env, hf⟩ (fun vv' ev' hv' he' => ?_)
        (hle₁.trans (hle₂.trans hle₃))
      rw [hv] at hv'
      injection hv' with hv'
      subst hv'
      rw [he] at he'
      injection he' with he'
      subst he'
      have hB3 := CVar.eval_le (hle₂.trans hle₃) hB
      rw [CVar.eval_add_]
      simp only [CVar.eval, hB3, hpv, Except.ok.injEq,
        Kimchi.Gate.EndoScalar.toField]
      ring
