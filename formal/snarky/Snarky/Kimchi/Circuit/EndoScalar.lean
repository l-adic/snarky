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
- PS's `aF`/`bF` throw on impossible crumbs; `aDigit`/`bDigit` render the dead
  branches as `0`.
- `toFieldPure` is generalized from PS's pinned 128 bits to `16 · rows`.
-/

namespace Snarky.Kimchi.EndoScalar

open Snarky

variable {F c : Type}

/-- The crumb-to-`a`-digit map (PS `aF`). -/
private def aDigit [Field F] [DecidableEq F] (x : F) : F :=
  if x = 2 then -1 else if x = 3 then 1 else 0

/-- The crumb-to-`b`-digit map (PS `bF`). -/
private def bDigit [Field F] [DecidableEq F] (x : F) : F :=
  if x = 0 then -1 else if x = 1 then 1 else 0

/-- The scalar's MSB-first 2-bit crumbs, eight per row (PS `toBits` reversed and
paired): crumb `i` is `2·bit(16·rows − 1 − 2i) + bit(16·rows − 2 − 2i)`. -/
private def crumbsWit [Field F] [ToNat F] (rows : ℕ) (scalar : FVar F) :
    AsProver F (Vector (Vector F 8) rows) := do
  let v ← AsProver.readCVar scalar
  let n := ToNat.toNat v
  pure (Vector.ofFn fun r => Vector.ofFn fun j =>
    let i := 8 * r.1 + j.1
    ((2 * (if n.testBit (16 * rows - 1 - 2 * i) then 1 else 0)
      + (if n.testBit (16 * rows - 2 - 2 * i) then 1 else 0) : F)))

/-- One row's accumulator witness: fold the row's eight crumbs into the three
accumulators, returned in the allocation order `(a8, b8, n8)`. -/
private def rowWit [Field F] [DecidableEq F] (xs : Vector (FVar F) 8)
    (st : FVar F × FVar F × FVar F) : AsProver F (F × F × F) := do
  let a0 ← AsProver.readCVar st.1
  let b0 ← AsProver.readCVar st.2.1
  let n0 ← AsProver.readCVar st.2.2
  let vals ← xs.toList.mapM AsProver.readCVar
  pure (vals.foldl (fun acc x => 2 * acc + aDigit x) a0,
        vals.foldl (fun acc x => 2 * acc + bDigit x) b0,
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

end Snarky.Kimchi.EndoScalar
