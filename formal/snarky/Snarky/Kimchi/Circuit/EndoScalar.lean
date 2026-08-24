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
theorem toFieldChecked'_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (rows : ℕ) (scalar : FVar F) :
    ⦃⌜True⌝⦄
    (toFieldChecked' (c := Builder V (KimchiConstraint F)) rows scalar)
    ⦃⇓ r _ => ⌜∃ crumbs : List F,
          (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
          crumbs.length = 8 * rows ∧
          r.1.val V = Kimchi.Gate.EndoScalar.decomposeA crumbs ∧
          r.2.1.val V = Kimchi.Gate.EndoScalar.decomposeB crumbs ∧
          r.2.2.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs⌝⦄ := by
  simp only [toFieldChecked', mapAccumM]
  mvcgen
  case inv1 =>
    exact ⇓ p _ => ⌜Threaded (.const 2, .const 2, .const 0) p.1.prefix p.2.snd p.2.fst⌝
  case vc2.post.success.pre =>
    exact ⟨rfl, rfl⟩
  case vc1.step.post.success =>
    rename_i pref cur suff _ b _ hinv r _ _
    simp at hinv ⊢
    exact hinv.snoc cur r
  case vc3.post.success.post.success.post.success =>
    rename_i fin _ hinv _ _ hpay
    simp at hinv
    have hHolds : ∀ r ∈ fin.snd,
        Kimchi.Gate.EndoScalar.Holds (EndoScalarRound.read V r) := hpay
    obtain ⟨crumbs, hvalid, hlen, ha, hb, hn⟩ := threaded_sound h2 h3 V hinv hHolds
    exact ⟨crumbs, hvalid, by simpa using hlen, ha, hb, hn⟩

open Std.Do in
/-- The checked decomposition is sound: the result reads as the gate model's
`toField` — `a·endo + b` — over some valid crumb list of length `8·rows` whose
`nReconstruct` is the scalar. -/
theorem toField_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (rows : ℕ) (scalar endo : FVar F) :
    ⦃⌜True⌝⦄
    (toField (c := Builder V (KimchiConstraint F)) rows scalar endo)
    ⦃⇓ r _ => ⌜∃ crumbs : List F,
          (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
          crumbs.length = 8 * rows ∧
          r.val V = Kimchi.Gate.EndoScalar.toField crumbs (endo.val V) ∧
          scalar.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs⌝⦄ := by
  simp only [toField]
  have hc := toFieldChecked'_spec (V := V) h2 h3 rows scalar
  mvcgen [hc]
  · rename_i abn _ habn _ e _ _ heq
    obtain ⟨crumbs, hvalid, hlen, ha, hb, hn⟩ := habn
    refine ⟨crumbs, hvalid, hlen, ?_, by rw [← heq, hn]⟩
    simp only [Kimchi.Gate.EndoScalar.toField, CVar.val_add_, CVar.val_scale_,
      ha, hb, CVar.val]
    ring
  · rename_i abn _ habn _ _ _ _ _ heq p _ hp
    obtain ⟨crumbs, hvalid, hlen, ha, hb, hn⟩ := habn
    refine ⟨crumbs, hvalid, hlen, ?_, by rw [← heq, hn]⟩
    simp only [Kimchi.Gate.EndoScalar.toField]
    rw [CVar.val_add_, hp, ha, hb]
    ring

/-! ## Completeness

The honest prover run accepts, and the results read as the gate model at the
scalar's own crumbs (`Kimchi.Gate.EndoScalar.crumbsOf`). The emitter needs only a
readable scalar; the checked decomposition's `n = scalar` pin adds the boundary
condition of the representative — the `4 ^ (8·rows)` range. The
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

/-- One accumulator round's step of the honest run: the three register outputs
allocated, the round record and the new registers returned. -/
private def roundStep [Field F] [DecidableEq F] (st : ProverState F)
    (acc : FVar F × FVar F × FVar F) (xs : Vector (FVar F) 8) :
    ProverState F × (EndoScalarRound F × (FVar F × FVar F × FVar F)) :=
  let w := Kimchi.Gate.EndoScalar.build (acc.1.val st.env.toValuation)
    (acc.2.1.val st.env.toValuation) (acc.2.2.val st.env.toValuation)
    (xs.toList.map (·.val st.env.toValuation))
  (st.extendMany [w.a8, w.b8, w.n8],
    ({ n0 := acc.2.2, n8 := .var (st.nv + 2), a0 := acc.1, a8 := .var st.nv,
       b0 := acc.2.1, b8 := .var (st.nv + 1), xs },
     (.var st.nv, .var (st.nv + 1), .var (st.nv + 2))))

/-- The crumb table's variables: the bulk allocation at the counter. -/
private def crumbVarsOf (st : ProverState F) (rows : ℕ) : Vector (Vector (FVar F) 8) rows :=
  CircuitType.fieldsToVar (F := F) (val := Vector (Vector F 8) rows)
    (mapVec CVar.var (allocRange st.nv (CircuitType.size F (Vector (Vector F 8) rows))))

/-- The state after the bulk witness: the scalar's crumb table written. -/
private def crumbState [Field F] [ToNat F] (st : ProverState F) (rows : ℕ) (scalar : FVar F) :
    ProverState F :=
  st.extendMany (CircuitType.valueToFields (F := F) (var := Vector (Vector (FVar F) 8) rows)
    (crumbVals (F := F) rows (ToNat.toNat (scalar.val st.env.toValuation)))).toList

/-- The state and result of `toFieldChecked'`'s honest run: the crumb table, then the
accumulator rounds. -/
def toFieldChecked'Run [Field F] [DecidableEq F] [ToNat F] (st : ProverState F) (rows : ℕ)
    (scalar : FVar F) : ProverState F × (FVar F × FVar F × FVar F) :=
  let r := mapAccumRun roundStep (crumbState st rows scalar) (.const 2, .const 2, .const 0)
    (crumbVarsOf st rows).toList
  (r.1, r.2.2)

/-- Every crumb variable is in scope at the crumb state. -/
private theorem crumbVarsOf_scoped [Field F] [ToNat F] (st : ProverState F) (rows : ℕ)
    (scalar : FVar F) :
    ∀ xs ∈ (crumbVarsOf st rows).toList, ∀ x ∈ xs.toList, x.Scoped (crumbState st rows scalar) := by
  intro xs hxs x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hxs
  obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.mp hx
  simp only [Vector.getElem_toList]
  have h := scoped_vector_iff.mp (scoped_extendMany_new (var := Vector (Vector (FVar F) 8) rows)
    st (crumbVals (F := F) rows (ToNat.toNat (scalar.val st.env.toValuation)))) j
    (by simpa using hj)
  exact scoped_fvar_iff.mp (scoped_vector_iff.mp h l (by simpa using hl))

/-- A crumb row reads, at the crumb state, as the scalar's chain row. -/
private theorem crumbVarsOf_val [Field F] [ToNat F] (st : ProverState F) (rows : ℕ)
    (scalar : FVar F) (j : ℕ) (hj : j < rows) :
    ((crumbVarsOf st rows)[j]).toList.map (·.val (crumbState st rows scalar).env.toValuation)
      = crumbRows (F := F) rows (ToNat.toNat (scalar.val st.env.toValuation)) j := by
  rw [crumbRows_getElem _ _ j hj]
  have h := encodes_vector_iff.mp (encodes_extendMany_new (var := Vector (Vector (FVar F) 8) rows)
    st (crumbVals (F := F) rows (ToNat.toNat (scalar.val st.env.toValuation)))) j hj
  apply List.ext_getElem (by simp)
  intro l hl1 hl2
  simp only [List.getElem_map, Vector.getElem_toList]
  exact encodes_fvar_iff.mp (encodes_vector_iff.mp h l (by simpa using hl2))

/-- One accumulator round's honest run, at any state where the registers and the row's
crumbs are in scope. -/
private theorem round_run [Field F] [DecidableEq F] {st : ProverState F}
    {acc : FVar F × FVar F × FVar F} {xs : Vector (FVar F) 8}
    (ha : acc.1.Scoped st) (hb : acc.2.1.Scoped st) (hn : acc.2.2.Scoped st)
    (hxs : ∀ x ∈ xs.toList, x.Scoped st) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (do
        let w ← witness (val := F × F × F) (rowWit xs acc)
        pure (({ n0 := acc.2.2, n8 := w.2.2, a0 := acc.1, a8 := w.1,
                 b0 := acc.2.1, b8 := w.2.1, xs } : EndoScalarRound F),
              (w.1, w.2.1, w.2.2)) : CircuitM F (KimchiConstraint F) _) st.nv st.env
      = .ok ((roundStep st acc xs).1.out (roundStep st acc xs).2) := by
  simp only [prove_bind]
  rw [prove_witness_run (w := rowWit xs acc) st
    (.bind (.readCVar ha) fun _ => .bind (.readCVar hb) fun _ => .bind (.readCVar hn) fun _ =>
      .bind (.mapM_readCVar hxs) fun _ => trivial)
    (v := ((Kimchi.Gate.EndoScalar.build (acc.1.val st.env.toValuation)
        (acc.2.1.val st.env.toValuation) (acc.2.2.val st.env.toValuation)
        (xs.toList.map (·.val st.env.toValuation))).a8,
      (Kimchi.Gate.EndoScalar.build (acc.1.val st.env.toValuation)
        (acc.2.1.val st.env.toValuation) (acc.2.2.val st.env.toValuation)
        (xs.toList.map (·.val st.env.toValuation))).b8,
      (Kimchi.Gate.EndoScalar.build (acc.1.val st.env.toValuation)
        (acc.2.1.val st.env.toValuation) (acc.2.2.val st.env.toValuation)
        (xs.toList.map (·.val st.env.toValuation))).n8))
    (by simp [rowWit, Except.bind])]
  simp only [valueToFields_triple_toList, fieldsToVar_triple_alloc, Except.bind, roundStep]
  rfl

/-- The accumulator fold, read: from registers reading the chain's row-`i` inputs, over
rows reading the chain's crumbs, the fold grows the table, its registers read the
chain's row-`(i + l.length)` inputs, and every collected round evaluates at the final
table to its chain row. -/
private theorem roundsRun_inv [Field F] [DecidableEq F] (rows' : ℕ → List F) :
    ∀ (l : List (Vector (FVar F) 8)) (i : ℕ) (st : ProverState F)
      (acc : FVar F × FVar F × FVar F),
      (∀ j (hj : j < l.length), (∀ x ∈ l[j].toList, x.Scoped st) ∧
        l[j].toList.map (·.val st.env.toValuation) = rows' (i + j)) →
      acc.1.Scoped st → acc.2.1.Scoped st → acc.2.2.Scoped st →
      acc.1.val st.env.toValuation = (Kimchi.Gate.EndoScalar.chainBuild rows' i).a0 →
      acc.2.1.val st.env.toValuation = (Kimchi.Gate.EndoScalar.chainBuild rows' i).b0 →
      acc.2.2.val st.env.toValuation = (Kimchi.Gate.EndoScalar.chainBuild rows' i).n0 →
      st.env.Le (mapAccumRun roundStep st acc l).1.env ∧
      ((mapAccumRun roundStep st acc l).2.2.1.Scoped (mapAccumRun roundStep st acc l).1 ∧
        (mapAccumRun roundStep st acc l).2.2.2.1.Scoped (mapAccumRun roundStep st acc l).1 ∧
        (mapAccumRun roundStep st acc l).2.2.2.2.Scoped (mapAccumRun roundStep st acc l).1) ∧
      ((mapAccumRun roundStep st acc l).2.2.1.val
          (mapAccumRun roundStep st acc l).1.env.toValuation
          = (Kimchi.Gate.EndoScalar.chainBuild rows' (i + l.length)).a0 ∧
        (mapAccumRun roundStep st acc l).2.2.2.1.val
          (mapAccumRun roundStep st acc l).1.env.toValuation
          = (Kimchi.Gate.EndoScalar.chainBuild rows' (i + l.length)).b0 ∧
        (mapAccumRun roundStep st acc l).2.2.2.2.val
          (mapAccumRun roundStep st acc l).1.env.toValuation
          = (Kimchi.Gate.EndoScalar.chainBuild rows' (i + l.length)).n0) ∧
      ∀ j (hj : j < (mapAccumRun roundStep st acc l).2.1.length),
        EndoScalarRound.eval (mapAccumRun roundStep st acc l).1.env
          (mapAccumRun roundStep st acc l).2.1[j]
          = .ok (Kimchi.Gate.EndoScalar.chainBuild rows' (i + j))
  | [], i, st, acc, _, ha, hb, hn, hva, hvb, hvn => by
    refine ⟨Assignments.Le.refl _, ⟨ha, hb, hn⟩, ?_, fun j hj => by simp [mapAccumRun] at hj⟩
    simp only [mapAccumRun, List.length_nil, Nat.add_zero]
    exact ⟨hva, hvb, hvn⟩
  | x :: l, i, st, acc, hl, ha, hb, hn, hva, hvb, hvn => by
    obtain ⟨hxs, hxv⟩ := hl 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hxs hxv
    have hw : Kimchi.Gate.EndoScalar.build (acc.1.val st.env.toValuation)
        (acc.2.1.val st.env.toValuation) (acc.2.2.val st.env.toValuation)
        (x.toList.map (·.val st.env.toValuation)) = Kimchi.Gate.EndoScalar.chainBuild rows' i := by
      rw [hva, hvb, hvn, hxv, build_fields]
    have hle₁ : st.env.Le (roundStep st acc x).1.env := st.le_extendMany _
    have hs₁ : (roundStep st acc x).2.2.1.Scoped (roundStep st acc x).1 :=
      ProverState.mem_extendMany_head ..
    have hs₂ : (roundStep st acc x).2.2.2.1.Scoped (roundStep st acc x).1 :=
      st.new_mem_extendMany (i := 1) (by simp)
    have hs₃ : (roundStep st acc x).2.2.2.2.Scoped (roundStep st acc x).1 :=
      st.new_mem_extendMany (i := 2) (by simp)
    have hv₁ : (roundStep st acc x).2.2.1.val (roundStep st acc x).1.env.toValuation
        = (Kimchi.Gate.EndoScalar.chainBuild rows' i).a8 := by
      show (roundStep st acc x).1.env.toValuation st.nv = _
      simp only [roundStep, ProverState.get_extendMany_head, hw]
    have hv₂ : (roundStep st acc x).2.2.2.1.val (roundStep st acc x).1.env.toValuation
        = (Kimchi.Gate.EndoScalar.chainBuild rows' i).b8 := by
      show (roundStep st acc x).1.env.toValuation (st.nv + 1) = _
      simp only [roundStep]
      rw [ProverState.get_extendMany_new st (by simp), hw]
      rfl
    have hv₃ : (roundStep st acc x).2.2.2.2.val (roundStep st acc x).1.env.toValuation
        = (Kimchi.Gate.EndoScalar.chainBuild rows' i).n8 := by
      show (roundStep st acc x).1.env.toValuation (st.nv + 2) = _
      simp only [roundStep]
      rw [ProverState.get_extendMany_new st (by simp), hw]
      rfl
    have ih := roundsRun_inv rows' l (i + 1) (roundStep st acc x).1 (roundStep st acc x).2.2
      (fun j hj => by
        obtain ⟨hsj, hvj⟩ := hl (j + 1) (by simpa using hj)
        simp only [List.getElem_cons_succ] at hsj hvj
        refine ⟨fun y hy => (hsj y hy).of_le hle₁, ?_⟩
        rw [show i + 1 + j = i + (j + 1) by omega, ← hvj]
        exact List.map_congr_left fun y hy => CVar.val_of_le hle₁ (hsj y hy))
      hs₁ hs₂ hs₃ hv₁ hv₂ hv₃
    simp only [mapAccumRun]
    refine ⟨hle₁.trans ih.1, ih.2.1, ?_, ?_⟩
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using ih.2.2.1
    · intro j hj
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        have hle := hle₁.trans ih.1
        refine round_eval_ok_iff.mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show acc.1.eval _ = _
          rw [CVar.eval_eq_val (ha.of_le hle), CVar.val_of_le hle ha, hva]
        · show acc.2.1.eval _ = _
          rw [CVar.eval_eq_val (hb.of_le hle), CVar.val_of_le hle hb, hvb]
        · show acc.2.2.eval _ = _
          rw [CVar.eval_eq_val (hn.of_le hle), CVar.val_of_le hle hn, hvn]
        · show (roundStep st acc x).2.2.1.eval _ = _
          rw [CVar.eval_eq_val (hs₁.of_le ih.1), CVar.val_of_le ih.1 hs₁, hv₁]
        · show (roundStep st acc x).2.2.2.1.eval _ = _
          rw [CVar.eval_eq_val (hs₂.of_le ih.1), CVar.val_of_le ih.1 hs₂, hv₂]
        · show (roundStep st acc x).2.2.2.2.eval _ = _
          rw [CVar.eval_eq_val (hs₃.of_le ih.1), CVar.val_of_le ih.1 hs₃, hv₃]
        · show x.toList.mapM (CVar.eval · _) = _
          rw [CVar.mapM_eval_eq_val (fun y hy => (hxs y hy).of_le hle), chainBuild_crumbs, ← hxv]
          exact congrArg Except.ok
            (List.map_congr_left fun y hy => CVar.val_of_le hle (hxs y hy))
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [show i + (j + 1) = i + 1 + j by omega]
        exact ih.2.2.2 j (by simpa using hj)

/-- The emitter's honest run on an in-scope scalar lands at `toFieldChecked'Run`: the
crumb table, the accumulator rounds, and the chain constraint accepted on the gate's
canonical chain. -/
theorem toFieldChecked'_run [Field F] [DecidableEq F] [ToNat F] (rows : ℕ) {scalar : FVar F}
    (st : ProverState F) (hs : scalar.Scoped st) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (toFieldChecked' (c := KimchiConstraint F) rows scalar) st.nv st.env
      = .ok ((toFieldChecked'Run st rows scalar).1.out (toFieldChecked'Run st rows scalar).2) := by
  simp only [toFieldChecked', prove_bind]
  rw [prove_witness_run (w := crumbsWit rows scalar) st (.bind (.readCVar hs) fun _ => trivial)
    (v := crumbVals (F := F) rows (ToNat.toNat (scalar.val st.env.toValuation)))
    (by simp [crumbsWit, Except.bind])]
  rw [show CircuitType.fieldsToVar (F := F) (val := Vector (Vector F 8) rows)
      (mapVec CVar.var (allocRange st.nv (CircuitType.size F (Vector (Vector F 8) rows))))
      = crumbVarsOf st rows from rfl,
    show st.extendMany (CircuitType.valueToFields (F := F)
      (var := Vector (Vector (FVar F) 8) rows)
      (crumbVals (F := F) rows (ToNat.toNat (scalar.val st.env.toValuation)))).toList
      = crumbState st rows scalar from rfl]
  simp only [Except.bind]
  have hinv := roundsRun_inv (crumbRows rows (ToNat.toNat (scalar.val st.env.toValuation)))
    (crumbVarsOf st rows).toList 0 (crumbState st rows scalar) (.const 2, .const 2, .const 0)
    (fun j hj => ⟨fun x hx => crumbVarsOf_scoped st rows scalar _ (List.getElem_mem hj) x hx, by
      rw [Vector.getElem_toList, crumbVarsOf_val st rows scalar j (by simpa using hj),
        Nat.zero_add]⟩)
    trivial trivial trivial
    (by simp [CVar.val, Kimchi.Gate.EndoScalar.chainBuild, Kimchi.Gate.EndoScalar.build])
    (by simp [CVar.val, Kimchi.Gate.EndoScalar.chainBuild, Kimchi.Gate.EndoScalar.build])
    (by simp [CVar.val, Kimchi.Gate.EndoScalar.chainBuild, Kimchi.Gate.EndoScalar.build])
  rw [prove_mapAccumM (fun st' acc => (crumbState st rows scalar).env.Le st'.env ∧
      acc.1.Scoped st' ∧ acc.2.1.Scoped st' ∧ acc.2.2.Scoped st') _ roundStep _
    (fun st' acc xs hx ⟨hle, ha, hb, hn⟩ =>
      round_run ha hb hn fun x hxx => (crumbVarsOf_scoped st rows scalar xs hx x hxx).of_le hle)
    (fun st' acc xs _ ⟨hle, _, _, _⟩ => ⟨hle.trans (st'.le_extendMany _),
      ProverState.mem_extendMany_head .., st'.new_mem_extendMany (i := 1) (by simp),
      st'.new_mem_extendMany (i := 2) (by simp)⟩)
    (.const 2, .const 2, .const 0) (crumbState st rows scalar)
    ⟨Assignments.Le.refl _, trivial, trivial, trivial⟩]
  simp only []
  rw [prove_addConstraint _ (by
    show KimchiConstraint.check (.endoScalar _) _ = true
    simp only [KimchiConstraint.check, List.all_eq_true]
    intro r hr
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
    rw [hinv.2.2.2 j hj, Nat.zero_add]
    exact (Kimchi.Gate.EndoScalar.ok_iff _).mpr
      ((Kimchi.Gate.EndoScalar.chain_complete j _
        (fun i _ => crumbRows_valid rows (ToNat.toNat (scalar.val st.env.toValuation)) i)).1
        j (Nat.le_refl _)))]
  rfl

/-- `toFieldChecked'Run` reads as the gate model's decompositions of the scalar's
crumbs. -/
theorem toFieldChecked'Run_grants [Field F] [DecidableEq F] [ToNat F] (rows : ℕ)
    {scalar : FVar F} (st : ProverState F) (hs : scalar.Scoped st) :
    Grants (F × F × F) st (toFieldChecked'Run st rows scalar)
      (Kimchi.Gate.EndoScalar.decomposeA
          (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) (ToNat.toNat (scalar.val st.env.toValuation))),
        Kimchi.Gate.EndoScalar.decomposeB
          (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) (ToNat.toNat (scalar.val st.env.toValuation))),
        Kimchi.Gate.EndoScalar.nReconstruct
          (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows)
            (ToNat.toNat (scalar.val st.env.toValuation)))) := by
  have _ := hs
  have hinv := roundsRun_inv (crumbRows rows (ToNat.toNat (scalar.val st.env.toValuation)))
    (crumbVarsOf st rows).toList 0 (crumbState st rows scalar) (.const 2, .const 2, .const 0)
    (fun j hj => ⟨fun x hx => crumbVarsOf_scoped st rows scalar _ (List.getElem_mem hj) x hx, by
      rw [Vector.getElem_toList, crumbVarsOf_val st rows scalar j (by simpa using hj),
        Nat.zero_add]⟩)
    trivial trivial trivial
    (by simp [CVar.val, Kimchi.Gate.EndoScalar.chainBuild, Kimchi.Gate.EndoScalar.build])
    (by simp [CVar.val, Kimchi.Gate.EndoScalar.chainBuild, Kimchi.Gate.EndoScalar.build])
    (by simp [CVar.val, Kimchi.Gate.EndoScalar.chainBuild, Kimchi.Gate.EndoScalar.build])
  obtain ⟨hle, ⟨hsa, hsb, hsn⟩, ⟨hva, hvb, hvn⟩, -⟩ := hinv
  simp only [Vector.length_toList, Nat.zero_add] at hva hvb hvn
  have hle0 : st.env.Le (crumbState st rows scalar).env := st.le_extendMany _
  refine ⟨hle0.trans hle,
    scoped_prod_iff.mpr ⟨scoped_fvar_iff.mpr hsa,
      scoped_prod_iff.mpr ⟨scoped_fvar_iff.mpr hsb, scoped_fvar_iff.mpr hsn⟩⟩, ?_⟩
  simp only [readVal_prod, readVal_fvar, toFieldChecked'Run]
  rw [hva, hvb, hvn]
  cases rows with
  | zero =>
    simp [Kimchi.Gate.EndoScalar.chainBuild, Kimchi.Gate.EndoScalar.build,
      Kimchi.Gate.EndoScalar.nReconstruct]
  | succ m =>
    obtain ⟨hH, c1, c2, c3, s1, s2, s3, -⟩ :=
      Kimchi.Gate.EndoScalar.chain_complete m
        (crumbRows (F := F) (m + 1) (ToNat.toNat (scalar.val st.env.toValuation)))
        (fun i _ => crumbRows_valid (m + 1) (ToNat.toNat (scalar.val st.env.toValuation)) i)
    obtain ⟨dA, dB, dN⟩ := Kimchi.Gate.EndoScalar.chain_decompose m
      (Kimchi.Gate.EndoScalar.chainBuild
        (crumbRows (F := F) (m + 1) (ToNat.toNat (scalar.val st.env.toValuation))))
      hH c1 c2 c3 s1 s2 s3
    have hstream := flatMap_range_getD
      (((crumbVals (F := F) (m + 1) (ToNat.toNat (scalar.val st.env.toValuation))).toList.map
        Vector.toList))
    rw [show (((crumbVals (F := F) (m + 1) (ToNat.toNat (scalar.val st.env.toValuation))).toList.map
        Vector.toList)).length = m + 1 from by simp,
      crumbVals_flatten] at hstream
    have hstream' : (List.range (m + 1)).flatMap
          (crumbRows (F := F) (m + 1) (ToNat.toNat (scalar.val st.env.toValuation)))
        = Kimchi.Gate.EndoScalar.crumbsOf (8 * (m + 1))
            (ToNat.toNat (scalar.val st.env.toValuation)) := hstream
    rw [Kimchi.Gate.EndoScalar.chainCrumbs_chainBuild, hstream'] at dA dB dN
    show ((Kimchi.Gate.EndoScalar.chainBuild _ m).a8, (Kimchi.Gate.EndoScalar.chainBuild _ m).b8,
      (Kimchi.Gate.EndoScalar.chainBuild _ m).n8) = _
    rw [dA, dB, dN]

/-- The state and result of `toField`'s honest run: the emitter, the pin (nothing
allocated), the affine reconstruction — `mul`'s run unless the endo coefficient is a
constant. -/
def toFieldRun [Field F] [DecidableEq F] [ToNat F] (st : ProverState F) (rows : ℕ)
    (scalar endo : FVar F) : ProverState F × FVar F :=
  let r := toFieldChecked'Run st rows scalar
  match endo with
  | .const e => (r.1, CVar.add_ (CVar.scale_ e r.2.1) r.2.2.1)
  | _ =>
    let m := mulRun r.1 r.2.1 endo
    (m.1, CVar.add_ r.2.2.1 m.2)

/-- The checked decomposition's honest run, on an in-scope scalar whose representative
fits the crumb budget and an in-scope endo coefficient, lands at `toFieldRun`. -/
theorem toField_run [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F] (rows : ℕ)
    {scalar endo : FVar F} (st : ProverState F) (hs : scalar.Scoped st) (he : endo.Scoped st)
    (hlt : ToNat.toNat (scalar.val st.env.toValuation) < 4 ^ (8 * rows)) :
    prove (Checker.holds (F := F) (c := KimchiConstraint F))
      (toField (c := KimchiConstraint F) rows scalar endo) st.nv st.env
      = .ok ((toFieldRun st rows scalar endo).1.out (toFieldRun st rows scalar endo).2) := by
  have hg := toFieldChecked'Run_grants rows st hs
  have hsc := scoped_prod_iff.mp hg.scope
  have hsc2 := scoped_prod_iff.mp hsc.2
  have hrd := hg.read
  simp only [readVal_prod, readVal_fvar, Prod.ext_iff] at hrd
  simp only [toField, prove_bind, toFieldChecked'_run rows st hs, Except.bind]
  rw [assertEqual_run _ (scoped_fvar_iff.mp hsc2.2) (hs.of_le hg.le) (by
    rw [hrd.2.2, CVar.val_of_le hg.le hs, Kimchi.Gate.EndoScalar.nReconstruct_crumbsOf,
      Nat.mod_eq_of_lt hlt, LawfulToNat.cast_toNat])]
  cases endo with
  | const e => rfl
  | var v =>
    simp only [toFieldRun, prove_bind, mul_run _ (scoped_fvar_iff.mp hsc.1) (he.of_le hg.le),
      Except.bind]
    rfl
  | add a b =>
    simp only [toFieldRun, prove_bind, mul_run _ (scoped_fvar_iff.mp hsc.1) (he.of_le hg.le),
      Except.bind]
    rfl
  | scale k y =>
    simp only [toFieldRun, prove_bind, mul_run _ (scoped_fvar_iff.mp hsc.1) (he.of_le hg.le),
      Except.bind]
    rfl

/-- `toFieldRun` reads as the gate model's `toField` at the scalar's crumbs and the
endo coefficient's reading. -/
theorem toFieldRun_grants [Field F] [DecidableEq F] [ToNat F] (rows : ℕ) {scalar endo : FVar F}
    (st : ProverState F) (hs : scalar.Scoped st) (he : endo.Scoped st) :
    Grants F st (toFieldRun st rows scalar endo)
      (Kimchi.Gate.EndoScalar.toField
        (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) (ToNat.toNat (scalar.val st.env.toValuation)))
        (endo.val st.env.toValuation)) := by
  have hg := toFieldChecked'Run_grants rows st hs
  have hsc := scoped_prod_iff.mp hg.scope
  have hsc2 := scoped_prod_iff.mp hsc.2
  have hrd := hg.read
  simp only [readVal_prod, readVal_fvar, Prod.ext_iff] at hrd
  have hA := scoped_fvar_iff.mp hsc.1
  have hB := scoped_fvar_iff.mp hsc2.1
  cases endo
  case const e =>
    refine Grants.fvar hg.le (CVar.Scoped.add_ (CVar.Scoped.scale_ _ hA) hB) ?_
    simp only [CVar.val_add_, CVar.val_scale_, hrd.1, hrd.2.1, CVar.val,
      Kimchi.Gate.EndoScalar.toField]
    ring
  all_goals
    have hm := mulRun_grants hA (he.of_le hg.le)
    refine Grants.fvar (hg.le.trans hm.le) (CVar.Scoped.add_ (hB.of_le hm.le) hm.fvar_scoped) ?_
    simp only [CVar.val_add_, hm.fvar_val, CVar.val_of_le hm.le hB, hrd.1, hrd.2.1,
      CVar.val_of_le hg.le he, Kimchi.Gate.EndoScalar.toField]
    ring

end Snarky.Kimchi.EndoScalar
