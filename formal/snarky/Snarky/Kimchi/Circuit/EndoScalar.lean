import Snarky.DSL.Field
import Kimchi.Gate.Semantics.EndoScalar
import Snarky.DSL.Assert
import Snarky.DSL.Bits
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
- PS's `aF`/`bF` fold the bare tables; the row witness computes the gate's canonical
  `Kimchi.Gate.EndoScalar.build` instead — the same field values on the honest (valid)
  crumbs, and the form the gate's completeness certifies.
-/

namespace Snarky.Kimchi.EndoScalar

open Snarky

variable {F c : Type}

/-- Crumb `j` (MSB-first) of a `2·count`-bit natural: bits `2(count−j)−1` (high) and
`2(count−j)−2` (low) — the PS `toBits` reversed and paired. -/
private def crumbOfNat (count j k : ℕ) : ℕ :=
  2 * (if k.testBit (2 * (count - j) - 1) then 1 else 0)
    + (if k.testBit (2 * (count - j) - 2) then 1 else 0)

/-- The crumb table the bulk witness writes: row `r`'s entry `j` is crumb `8r + j`. -/
private def crumbVals [NatCast F] (rows k : ℕ) : Vector (Vector F 8) rows :=
  Vector.ofFn fun r => Vector.ofFn fun j =>
    (crumbOfNat (8 * rows) (8 * r.1 + j.1) k : F)

/-- The scalar's MSB-first 2-bit crumbs, eight per row. -/
private def crumbsWit [Field F] [ToNat F] (rows : ℕ) (scalar : FVar F) :
    AsProver F (Vector (Vector F 8) rows) := do
  let v ← AsProver.readCVar scalar
  pure (crumbVals rows (ToNat.toNat v))

/-- One row's accumulator witness: read the threaded registers and the row's eight
crumbs, and take the gate's canonical row's outputs
(`Kimchi.Gate.EndoScalar.build`), in the allocation order `(a8, b8, n8)`. -/
private def rowWit [Field F] [DecidableEq F] (xs : Vector (FVar F) 8)
    (st : FVar F × FVar F × FVar F) : AsProver F (F × F × F) := do
  let a0 ← AsProver.readCVar st.1
  let b0 ← AsProver.readCVar st.2.1
  let n0 ← AsProver.readCVar st.2.2
  let vals ← xs.toList.mapM AsProver.readCVar
  let w := Kimchi.Gate.EndoScalar.build a0 b0 n0 vals
  pure (w.a8, w.b8, w.n8)

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

/-- An empty threading traversed no chunks: the final triple is the start. -/
private theorem Threaded.nil :
    ∀ {st fin : FVar F × FVar F × FVar F} {pref : List (Vector (FVar F) 8)},
      Threaded st pref [] fin → pref = [] ∧ fin = st
  | _, _, [], h => ⟨rfl, h.2⟩
  | _, _, _ :: _, h => by
    obtain ⟨w, tail, heq, -⟩ := h
    exact nomatch heq

/-- The structural facts of a nonempty threading: the round count, round `0`'s seed
wiring, the shared accumulator variables between adjacent rounds, and the final
triple's wiring — everything the gate's `chain_decompose` consumes, extracted
without touching a valuation. -/
private theorem threaded_chain :
    ∀ {pref : List (Vector (FVar F) 8)} {st fin : FVar F × FVar F × FVar F}
      {r₀ : EndoScalarRound F} {rs : List (EndoScalarRound F)},
      Threaded st pref (r₀ :: rs) fin →
      (r₀ :: rs).length = pref.length ∧
      (r₀.a0 = st.1 ∧ r₀.b0 = st.2.1 ∧ r₀.n0 = st.2.2) ∧
      (∀ i (hi : i + 1 < (r₀ :: rs).length),
        (r₀ :: rs)[i + 1].a0 = (r₀ :: rs)[i].a8 ∧
        (r₀ :: rs)[i + 1].b0 = (r₀ :: rs)[i].b8 ∧
        (r₀ :: rs)[i + 1].n0 = (r₀ :: rs)[i].n8) ∧
      (fin.1 = (r₀ :: rs)[rs.length].a8 ∧
       fin.2.1 = (r₀ :: rs)[rs.length].b8 ∧
       fin.2.2 = (r₀ :: rs)[rs.length].n8)
  | x :: rest, st, fin, r₀, rs, h => by
    obtain ⟨w, tail, heq, hrest⟩ := h
    injection heq with h1 h2
    subst h1 h2
    cases rs with
    | nil =>
      obtain ⟨rfl, rfl⟩ := Threaded.nil hrest
      exact ⟨rfl, ⟨rfl, rfl, rfl⟩, fun i hi => by simp at hi, ⟨rfl, rfl, rfl⟩⟩
    | cons r₁ ts =>
      obtain ⟨ihlen, ⟨e1, e2, e3⟩, ihstep, ihlast⟩ := threaded_chain hrest
      refine ⟨by simpa using ihlen, ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero =>
          simpa only [List.getElem_cons_succ, List.getElem_cons_zero]
            using ⟨e1, e2, e3⟩
        | succ j =>
          have hj : j + 1 < (r₁ :: ts).length := by simpa using hi
          simpa only [List.getElem_cons_succ] using ihstep j hj
      · obtain ⟨f1, f2, f3⟩ := ihlast
        simpa only [List.length_cons, List.getElem_cons_succ] using ⟨f1, f2, f3⟩

/-- A satisfied threading from the seeds computes the gate tower's chain: the
structural wiring (`threaded_chain`) instantiates `chain_decompose`'s indexed run
at the payload reads, so `fin` reads as the decompositions of the concatenated
crumb stream. The gadget layer contributes wiring only; the fold arithmetic is the
tower's. -/
private theorem threaded_sound [Field F] [DecidableEq F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (V : Valuation F)
    {pref : List (Vector (FVar F) 8)} {fin : FVar F × FVar F × FVar F}
    {rounds : List (EndoScalarRound F)}
    (hthr : Threaded (.const 2, .const 2, .const 0) pref rounds fin)
    (hHolds : ∀ r ∈ rounds, Kimchi.Gate.EndoScalar.Holds (EndoScalarRound.read V r)) :
    ∃ crumbs : List F,
      (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
      crumbs.length = 8 * pref.length ∧
      fin.1.val V = Kimchi.Gate.EndoScalar.decomposeA crumbs ∧
      fin.2.1.val V = Kimchi.Gate.EndoScalar.decomposeB crumbs ∧
      fin.2.2.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs := by
  match hround : rounds, hthr with
  | [], hthr' =>
    obtain ⟨rfl, rfl⟩ := Threaded.nil hthr'
    refine ⟨[], by simp, by simp, ?_, ?_, ?_⟩ <;>
      simp [Kimchi.Gate.EndoScalar.decomposeA, Kimchi.Gate.EndoScalar.decomposeB,
        Kimchi.Gate.EndoScalar.decomposeFold,
        Kimchi.Gate.EndoScalar.nReconstruct, CVar.val]
  | r₀ :: rs, hthr' =>
    subst hround
    obtain ⟨hlen, ⟨h01, h02, h03⟩, hstep, hf1, hf2, hf3⟩ := threaded_chain hthr'
    set w : ℕ → Kimchi.Gate.EndoScalar.Witness F :=
      fun i => EndoScalarRound.read V ((r₀ :: rs).getD i r₀) with hw
    have hwi : ∀ i (hi : i ≤ rs.length),
        w i = EndoScalarRound.read V ((r₀ :: rs)[i]'(by simp; omega)) := by
      intro i hi
      simp only [hw]
      congr 1
      exact List.getD_eq_getElem _ _ (by simp; omega)
    have hHolds' : ∀ i, i ≤ rs.length → Kimchi.Gate.EndoScalar.Holds (w i) := by
      intro i hi
      rw [hwi i hi]
      exact hHolds _ (List.getElem_mem _)
    obtain ⟨hA, hB, hN⟩ := Kimchi.Gate.EndoScalar.chain_decompose rs.length w hHolds'
      (by rw [hwi 0 (by omega)]; simp [EndoScalarRound.read, h01, CVar.val])
      (by rw [hwi 0 (by omega)]; simp [EndoScalarRound.read, h02, CVar.val])
      (by rw [hwi 0 (by omega)]; simp [EndoScalarRound.read, h03, CVar.val])
      (fun i hi => by
        obtain ⟨e, -, -⟩ := hstep i (by simp; omega)
        simp only [List.getElem_cons_succ] at e
        rw [hwi (i + 1) (by omega), hwi i (by omega)]
        simp [EndoScalarRound.read, e])
      (fun i hi => by
        obtain ⟨-, e, -⟩ := hstep i (by simp; omega)
        simp only [List.getElem_cons_succ] at e
        rw [hwi (i + 1) (by omega), hwi i (by omega)]
        simp [EndoScalarRound.read, e])
      (fun i hi => by
        obtain ⟨-, -, e⟩ := hstep i (by simp; omega)
        simp only [List.getElem_cons_succ] at e
        rw [hwi (i + 1) (by omega), hwi i (by omega)]
        simp [EndoScalarRound.read, e])
    refine ⟨Kimchi.Gate.EndoScalar.chainCrumbs w (rs.length + 1), ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Kimchi.Gate.EndoScalar.chainCrumbs, List.mem_flatMap,
        List.mem_range] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      exact (Kimchi.Gate.EndoScalar.sound h2 h3 _ (hHolds' i (by omega))).1 x hxi
    · rw [Kimchi.Gate.EndoScalar.chainCrumbs_length 8 w (rs.length + 1)
        (fun i _ => by simp [hw, EndoScalarRound.read]), ← hlen]
      simp
    · rw [← hA, hwi rs.length (by omega)]
      simp [EndoScalarRound.read, hf1]
    · rw [← hB, hwi rs.length (by omega)]
      simp [EndoScalarRound.read, hf2]
    · rw [← hN, hwi rs.length (by omega)]
      simp [EndoScalarRound.read, hf3]

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
    obtain ⟨crumbs, hvalid, hlen, ha, hb, hn⟩ := threaded_sound h2 h3 s.V hthr hHolds
    exact ⟨crumbs, hvalid, by simpa using hlen, ha, hb, hn⟩

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
scalar's own crumbs (`Kimchi.Gate.EndoScalar.crumbsOf`). The emitter needs only a
readable scalar; the checked decomposition's `n = scalar` pin adds the boundary
conditions of the representative — faithfulness and the `4 ^ (8·rows)` range. The
witness's testBit crumbs meet the gate model's expansion at
`map_crumbOfNat_eq_crumbsOf`; the loop's invariant identifies the run with the
gate's canonical chain (`chainBuild`), whose acceptance and reading are the gate's
own `chain_complete` and `chain_decompose`. -/

/-- Every crumb is a valid 2-bit value. -/
private theorem crumbOfNat_cast_valid [Field F] (count j k : ℕ) :
    ((crumbOfNat count j k : ℕ) : F) = 0 ∨ ((crumbOfNat count j k : ℕ) : F) = 1
      ∨ ((crumbOfNat count j k : ℕ) : F) = 2 ∨ ((crumbOfNat count j k : ℕ) : F) = 3 := by
  unfold crumbOfNat
  by_cases h1 : k.testBit (2 * (count - j) - 1) <;>
    by_cases h0 : k.testBit (2 * (count - j) - 2) <;> simp [h1, h0]

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

/-- The witness's testBit crumbs are the gate model's expansion: mapping `crumbOfNat`
over the index range is `crumbsOf`. -/
private theorem map_crumbOfNat_eq_crumbsOf [Field F] (count k : ℕ) :
    ((List.range count).map fun j => ((crumbOfNat count j k : ℕ) : F))
      = Kimchi.Gate.EndoScalar.crumbsOf count k := by
  induction count generalizing k with
  | zero => rfl
  | succ c ih =>
    rw [show Kimchi.Gate.EndoScalar.crumbsOf (F := F) (c + 1) k
        = Kimchi.Gate.EndoScalar.crumbsOf c (k / 4) ++ [((k % 4 : ℕ) : F)] from rfl,
      List.range_succ, List.map_append]
    congr 1
    · rw [← ih (k / 4)]
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      rw [crumbOfNat_eq_digit (c + 1) j k (by omega),
        crumbOfNat_eq_digit c j (k / 4) hj,
        show c + 1 - 1 - j = (c - 1 - j) + 1 by omega, pow_succ,
        mul_comm ((4 : ℕ) ^ (c - 1 - j)) 4, ← Nat.div_div_eq_div_mul]
    · simp only [List.map_cons, List.map_nil]
      rw [crumbOfNat_eq_digit (c + 1) c k (by omega)]
      simp

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
private theorem crumbVals_flatten [Field F] (rows k : ℕ) :
    ((crumbVals (F := F) rows k).toList.map Vector.toList).flatten
      = Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) k := by
  show ((Vector.ofFn _).toList.map Vector.toList).flatten = _
  rw [Vector.toList_ofFn, List.map_ofFn, ← map_crumbOfNat_eq_crumbsOf]
  exact flatten_ofFn_rows (fun i => (crumbOfNat (8 * rows) i k : F)) rows

/-- Every entry of one witness row is a valid crumb. -/
private theorem crumbVals_row_valid [Field F] (rows n k : ℕ) (hk : k < rows) :
    ∀ x ∈ ((crumbVals (F := F) rows n)[k]'hk).toList,
      x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  intro x hx
  simp only [crumbVals, Vector.getElem_ofFn, Vector.toList_ofFn, List.mem_ofFn] at hx
  obtain ⟨j, rfl⟩ := hx
  exact crumbOfNat_cast_valid _ _ _

/-- The scalar's crumb rows as a total chain index (empty rows off the end) — the
`rows` argument the gate's `chainBuild` threads. -/
private def crumbRows [NatCast F] (rows k : ℕ) : ℕ → List F := fun i =>
  ((crumbVals (F := F) rows k).toList.map Vector.toList).getD i []

/-- In range, a chain row is the witness table's row. -/
private theorem crumbRows_getElem [NatCast F] (rows k i : ℕ) (hi : i < rows) :
    crumbRows (F := F) rows k i = ((crumbVals (F := F) rows k)[i]'hi).toList := by
  simp only [crumbRows]
  rw [List.getD_eq_getElem _ _ (by simp [hi])]
  simp

/-- Every chain row is valid crumbs (vacuously off the end). -/
private theorem crumbRows_valid [Field F] (rows k : ℕ) :
    ∀ i, ∀ x ∈ crumbRows (F := F) rows k i, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  intro i x hx
  by_cases hi : i < rows
  · rw [crumbRows_getElem rows k i hi] at hx
    exact crumbVals_row_valid rows k i hi x hx
  · rw [show crumbRows (F := F) rows k i = [] from by
      simp only [crumbRows]
      exact List.getD_eq_default _ _ (by simp; omega)] at hx
    cases hx

/-- Flattening over a row list's range through its total index is the flatten. -/
private theorem flatMap_range_getD {α : Type} :
    ∀ l : List (List α),
      (List.range l.length).flatMap (fun i => l.getD i []) = l.flatten
  | [] => rfl
  | r :: rs => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.getD_cons_zero]
    rw [show (fun i => (r :: rs).getD (i + 1) []) = (fun i => rs.getD i []) from
        funext fun i => List.getD_cons_succ ..,
      flatMap_range_getD rs, List.flatten_cons]

/-- Rebuilding a chain row from its own registers is the row: `build` stores its
arguments, so the chain step reads off the previous row's fields. -/
private theorem build_fields [Field F] (rows' : ℕ → List F) (i : ℕ) :
    Kimchi.Gate.EndoScalar.build
        (Kimchi.Gate.EndoScalar.chainBuild rows' i).a0
        (Kimchi.Gate.EndoScalar.chainBuild rows' i).b0
        (Kimchi.Gate.EndoScalar.chainBuild rows' i).n0 (rows' i)
      = Kimchi.Gate.EndoScalar.chainBuild rows' i := by
  cases i <;> rfl

/-- A chain row carries its own crumbs. -/
private theorem chainBuild_crumbs [Field F] (rows' : ℕ → List F) (i : ℕ) :
    (Kimchi.Gate.EndoScalar.chainBuild rows' i).crumbs = rows' i := by
  cases i <;> rfl

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

/-- One row's accumulator witness computes the gate's canonical row's outputs. -/
private theorem rowWit_ok [Field F] [DecidableEq F] {env : Assignments F}
    {xs : Vector (FVar F) 8} {st : FVar F × FVar F × FVar F} {a b n : F} {vs : List F}
    (ha : st.1.eval env = .ok a) (hb : st.2.1.eval env = .ok b)
    (hn : st.2.2.eval env = .ok n)
    (hxs : xs.toList.mapM (CVar.eval · env) = .ok vs) :
    rowWit xs st env
      = .ok ((Kimchi.Gate.EndoScalar.build a b n vs).a8,
             (Kimchi.Gate.EndoScalar.build a b n vs).b8,
             (Kimchi.Gate.EndoScalar.build a b n vs).n8) := by
  simp [rowWit, AsProver.readCVar, ha, hb, hn, AsProver.readAll_ok hxs, Bind.bind, ReaderT.bind,
    Except.bind, Pure.pure, ReaderT.pure, Except.pure]

open Std.Do in
/-- The gate emitter is complete: the honest prover run accepts on any readable
scalar — no range condition — and the returned accumulators read as the gate model's
decompositions of the scalar's crumbs. -/
theorem toFieldChecked'_complete_spec [Field F] [DecidableEq F] [ToNat F]
    (rows : ℕ) (scalar : FVar F)
    (Q : PostCond (FVar F × FVar F × FVar F)
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete (fun env => (scalar.eval env).isOk)
        (fun env r env' => ∀ vv, scalar.eval env = .ok vv →
          r.1.eval env' = .ok (Kimchi.Gate.EndoScalar.decomposeA
            (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) (ToNat.toNat vv))) ∧
          r.2.1.eval env' = .ok (Kimchi.Gate.EndoScalar.decomposeB
            (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) (ToNat.toNat vv))) ∧
          r.2.2.eval env' = .ok (Kimchi.Gate.EndoScalar.nReconstruct
            (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) (ToNat.toNat vv)))) Q⦄
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
      (let w := Kimchi.Gate.EndoScalar.chainBuild
          (crumbRows (F := F) rows (ToNat.toNat vv)) p.1.prefix.length
       p.2.fst.1.eval s'.env = .ok w.a0 ∧
       p.2.fst.2.1.eval s'.env = .ok w.b0 ∧
       p.2.fst.2.2.eval s'.env = .ok w.n0) ∧
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
        = .ok (crumbRows (F := F) rows (ToNat.toNat vv) pref.length) := by
      rw [crumbRows_getElem rows (ToNat.toNat vv) pref.length hkrows]
      refine mapM_eval_ok (by simp) ?_
      intro j hj hj'
      simp only [Vector.length_toList] at hj
      simp only [Vector.getElem_toList]
      exact CVar.eval_le hLe (hread pref.length hkrows j hj)
    have hrow := rowWit_ok (env := s'.env) hA hB hN hxs
    rw [build_fields] at hrow
    refine ⟨by rw [hrow]; rfl, fun r st' hgrant' hle' => ?_⟩
    have hw := hgrant' _ hrow
    have heval : EndoScalarRound.eval st'.env
        { n0 := b.fst.2.2, n8 := r.2.2, a0 := b.fst.1, a8 := r.1,
          b0 := b.fst.2.1, b8 := r.2.1, xs := crumbVars[pref.length]'hkrows }
        = .ok (Kimchi.Gate.EndoScalar.chainBuild
            (crumbRows (F := F) rows (ToNat.toNat vv)) pref.length) :=
      round_eval_ok_iff.mpr ⟨CVar.eval_le hle' hA, CVar.eval_le hle' hB,
        CVar.eval_le hle' hN, hw.1, hw.2.1, hw.2.2, by
          rw [chainBuild_crumbs]
          exact mapM_eval_le hle' hxs⟩
    mvcgen
    refine ⟨hLe.trans hle', ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      exact ⟨hw.1, hw.2.1, hw.2.2⟩
    · simp only [KimchiConstraint.check, List.all_append, List.all_cons, List.all_nil,
        Bool.and_eq_true, and_true]
      refine ⟨?_, ?_⟩
      · simpa only [KimchiConstraint.check] using check_rounds_le hle' hcheck
      · simp only [heval]
        exact (Kimchi.Gate.EndoScalar.ok_iff _).mpr
          ((Kimchi.Gate.EndoScalar.chain_complete pref.length _
            (fun i _ => crumbRows_valid rows (ToNat.toNat vv) i)).1 pref.length
            (Nat.le_refl _))
  case vc2.vc1.pre =>
    refine ⟨Assignments.Le.refl st₁.env, ⟨?_, ?_, ?_⟩,
        by simp [KimchiConstraint.check]⟩ <;>
      simp [CVar.eval, Kimchi.Gate.EndoScalar.chainBuild,
        Kimchi.Gate.EndoScalar.build]
  case vc3.vc1.post.success =>
    rename_i fin s' hinv
    obtain ⟨hLe, hacc, hcheck⟩ := hinv
    obtain ⟨hA, hB, hN⟩ := hacc
    simp only [Vector.length_toList] at hA hB hN
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
    cases rows with
    | zero =>
      exact ⟨CVar.eval_le hle₂ (by simpa using hA),
        CVar.eval_le hle₂ (by simpa using hB), CVar.eval_le hle₂ (by simpa using hN)⟩
    | succ m =>
      obtain ⟨hH, c1, c2, c3, s1, s2, s3, -⟩ :=
        Kimchi.Gate.EndoScalar.chain_complete m
          (crumbRows (F := F) (m + 1) (ToNat.toNat vv))
          (fun i _ => crumbRows_valid (m + 1) (ToNat.toNat vv) i)
      obtain ⟨dA, dB, dN⟩ := Kimchi.Gate.EndoScalar.chain_decompose m
        (Kimchi.Gate.EndoScalar.chainBuild
          (crumbRows (F := F) (m + 1) (ToNat.toNat vv)))
        hH c1 c2 c3 s1 s2 s3
      have hstream := flatMap_range_getD
        (((crumbVals (F := F) (m + 1) (ToNat.toNat vv)).toList.map Vector.toList))
      rw [show (((crumbVals (F := F) (m + 1) (ToNat.toNat vv)).toList.map
          Vector.toList)).length = m + 1 from by simp,
        crumbVals_flatten] at hstream
      have hstream' : (List.range (m + 1)).flatMap
            (crumbRows (F := F) (m + 1) (ToNat.toNat vv))
          = Kimchi.Gate.EndoScalar.crumbsOf (8 * (m + 1)) (ToNat.toNat vv) := hstream
      rw [Kimchi.Gate.EndoScalar.chainCrumbs_chainBuild, hstream'] at dA dB dN
      refine ⟨?_, ?_, ?_⟩
      · exact CVar.eval_le hle₂ (by rw [← dA]; exact hA)
      · exact CVar.eval_le hle₂ (by rw [← dB]; exact hB)
      · exact CVar.eval_le hle₂ (by rw [← dN]; exact hN)
  case vc4.vc1.post.except =>
    exact ExceptConds.entails_false

open Std.Do in
/-- The checked decomposition is complete: the honest prover run accepts on a
readable scalar whose representative is faithful and fits the crumb budget, and the
result reads as the gate model's `toField` at the scalar's crumbs. -/
theorem toField_complete_spec [Field F] [DecidableEq F] [ToNat F]
    (rows : ℕ) (scalar endo : FVar F)
    (Q : PostCond (FVar F) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (scalar.eval env).isOk ∧ (endo.eval env).isOk ∧
          ∀ vv, scalar.eval env = .ok vv →
            ((ToNat.toNat vv : ℕ) : F) = vv ∧ ToNat.toNat vv < 4 ^ (8 * rows))
        (fun env r env' => ∀ vv ev, scalar.eval env = .ok vv →
          endo.eval env = .ok ev →
          r.eval env' = .ok (Kimchi.Gate.EndoScalar.toField
            (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) (ToNat.toNat vv)) ev)) Q⦄
    (toField (c := KimchiProverC F) rows scalar endo)
    ⦃Q⦄ := by
  simp only [toField]
  mvcgen
  rename_i st₀ hpre
  obtain ⟨⟨hoks, hoke, hbound⟩, hk⟩ := hpre
  obtain ⟨vv, hv⟩ := CVar.evalOk hoks
  obtain ⟨ev, he⟩ := CVar.evalOk hoke
  obtain ⟨hfaith, hlt⟩ := hbound vv hv
  refine toFieldChecked'_complete_spec rows scalar _ _
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
    rw [Kimchi.Gate.EndoScalar.nReconstruct_crumbsOf, Nat.mod_eq_of_lt hlt, hfaith]
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
      rw [CVar.eval_add_fold]
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
      rw [CVar.eval_add_fold]
      simp only [CVar.eval, hB3, hpv, Except.ok.injEq,
        Kimchi.Gate.EndoScalar.toField]
      ring

end Snarky.Kimchi.EndoScalar
