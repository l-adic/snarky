import Snarky.DSL.Field
import Kimchi.Gate.Semantics.EndoScalar
import Snarky.DSL.Assert
import Snarky.DSL.Bits
import Snarky.Kimchi.Semantics
import Snarky.Traverse

/-!
# The EndoScalar gadget

Transcribes `packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/EndoScalar.purs`: the GLV
challenge decomposition. `toFieldChecked'` witnesses the scalar's 2-bit crumbs in one bulk
witness, eight per row, MSB-first, as the gate model's base-4 expansion
`Kimchi.Gate.EndoScalar.crumbsOf`. It then threads the three accumulators through
`mapAccumM`, witnessing each row's `(a8, b8, n8)` as the gate's canonical
`Kimchi.Gate.EndoScalar.build`, and emits one `endoScalar` constraint over the rounds.
`toField` pins the reconstruction `n` to the scalar and returns `a·endo + b`.

The bit width is the explicit `rows` parameter, `16 · rows` bits; the deployed width is
eight rows, a 128-bit challenge.
-/

namespace Snarky.Kimchi.EndoScalar

open Snarky

variable {F c : Type}

/-- The gate model's MSB-first base-4 expansion, as a vector — the crumb stream the
bulk witness writes. -/
private def crumbsVec [Field F] (c k : ℕ) : Vector F c :=
  Vector.ofFn fun i => (Kimchi.Gate.EndoScalar.crumbsOf (F := F) c k).getD i.1 0

/-- The scalar's MSB-first 2-bit crumbs, eight to a row. -/
private def crumbsWit [Field F] [ToNat F] (rows : ℕ) (scalar : FVar F) :
    AsProver F (Vector F (rows * 8)) := do
  let v ← AsProver.readCVar scalar
  pure (crumbsVec (rows * 8) (ToNat.toNat v))

/-- One row's accumulator witness: the outputs `(a8, b8, n8)` of the gate's canonical row
`Kimchi.Gate.EndoScalar.build` on the threaded registers and the row's eight crumbs. -/
private def rowWit [Field F] [DecidableEq F] (xs : Vector (FVar F) 8)
    (st : FVar F × FVar F × FVar F) : AsProver F (F × F × F) := do
  let a0 ← AsProver.readCVar st.1
  let b0 ← AsProver.readCVar st.2.1
  let n0 ← AsProver.readCVar st.2.2
  let vals ← xs.toList.mapM AsProver.readCVar
  let w := Kimchi.Gate.EndoScalar.build a0 b0 n0 vals
  pure (w.a8, w.b8, w.n8)

/-- The gate emitter: the bulk crumb witness, the accumulator rounds and one `endoScalar`
constraint, returning the raw `(a, b, n)` accumulators. -/
def toFieldChecked' [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [ConstraintHolds F c] [KimchiSystem F c]
    (rows : ℕ) (scalar : FVar F) :
    CircuitM F c (FVar F × FVar F × FVar F) := do
  let crumbs ← witness (val := Vector F (rows * 8)) (crumbsWit rows scalar)
  let (rounds, fin) ← mapAccumM row (.const 2, .const 2, .const 0) (chunkVec crumbs).toList
  addConstraint (KimchiSystem.endoScalar rounds)
  pure fin
where
  /-- One row: witness the outgoing accumulators, and pair the round they close with
  the accumulators the next row opens on. -/
  row (st : FVar F × FVar F × FVar F) (xs : Vector (FVar F) 8) :
      CircuitM F c (EndoScalarRound F × (FVar F × FVar F × FVar F)) := do
    let w ← witness (val := F × F × F) (rowWit xs st)
    pure ({ n0 := st.2.2, n8 := w.2.2, a0 := st.1, a8 := w.1,
            b0 := st.2.1, b8 := w.2.1, xs }, (w.1, w.2.1, w.2.2))

/-- The checked decomposition: the gate, the pin `n = scalar`, and `a·endo + b`, which
costs no constraint when `endo` is a constant. -/
def toField [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [ConstraintHolds F c]
    [KimchiSystem F c]
    (rows : ℕ) (scalar endo : FVar F) : CircuitM F c (FVar F) := do
  let (a, b, n) ← toFieldChecked' (c := c) rows scalar
  assertEqual n scalar
  match endo with
  | .const e => pure (CVar.add_ (CVar.scale_ e a) b)
  | _ => do
    let p ← mul a endo
    pure (CVar.add_ b p)

/-! ## Soundness

`mapAccumM_spec` chains the step's grant. The gadget only reads that chain off as the
indexed run `Kimchi.Gate.EndoScalar.chain_decompose` consumes; the fold arithmetic is
the gate model's. -/

/-- The step's grant: the round is built from the accumulators either side of it, over
the row it was handed. -/
private def Threads (st : FVar F × FVar F × FVar F) (xs : Vector (FVar F) 8)
    (r : EndoScalarRound F) (st' : FVar F × FVar F × FVar F) : Prop :=
  (r.a0, r.b0, r.n0) = st ∧ (r.a8, r.b8, r.n8) = st' ∧ r.xs = xs

/-- The crumb stream a round list carries, MSB-first: the rounds' rows concatenated. -/
private def roundCrumbs [Field F] (V : Valuation F) (rounds : List (EndoScalarRound F)) : List F :=
  rounds.flatMap fun r => r.xs.toList.map (·.val V)

/-- A trace's rounds carry the rows it was handed. -/
private theorem chain_rows {st fin : FVar F × FVar F × FVar F} {xs : List (Vector (FVar F) 8)}
    {rounds : List (EndoScalarRound F)} (h : Chain Threads st xs rounds fin) :
    rounds.map (·.xs) = xs := by
  have hF := ((chain_iff _ _ (fun (x : Vector (FVar F) 8) (r : EndoScalarRound F) => r.xs = x)
    fun _ _ _ _ => Iff.rfl).mp h).1
  clear h
  induction hF with
  | nil => rfl
  | cons hq _ ih => simp [hq, ih]

/-- A threaded trace's wiring: adjacent rounds share their accumulator variables, the
first opens at the seeds, and the last closes at the final ones — the three conditions
`Kimchi.Gate.EndoScalar.isChain_getD` asks for. -/
private theorem threads_wiring :
    ∀ {pref : List (Vector (FVar F) 8)} {st fin : FVar F × FVar F × FVar F}
      {r₀ : EndoScalarRound F} {rs : List (EndoScalarRound F)},
      Chain Threads st pref (r₀ :: rs) fin →
      (r₀ :: rs).IsChain (fun a b => b.a0 = a.a8 ∧ b.b0 = a.b8 ∧ b.n0 = a.n8) ∧
        (r₀.a0 = st.1 ∧ r₀.b0 = st.2.1 ∧ r₀.n0 = st.2.2) ∧
        ((r₀ :: rs).getLast (by simp)).a8 = fin.1 ∧
        ((r₀ :: rs).getLast (by simp)).b8 = fin.2.1 ∧
        ((r₀ :: rs).getLast (by simp)).n8 = fin.2.2
  | _, st, fin, r₀, rs, h => by
    obtain ⟨-, hC, hH, hL⟩ := (chain_iff _ _
      (fun (x : Vector (FVar F) 8) (r : EndoScalarRound F) => r.xs = x) fun _ _ _ _ => Iff.rfl).mp h
    simp only [Prod.ext_iff] at hC hH hL
    refine ⟨hC.imp fun _ _ e => ⟨e.1, e.2.1, e.2.2⟩, hH r₀ (by simp), ?_⟩
    simpa [List.getLast?_eq_some_getLast (l := r₀ :: rs) (by simp)] using hL

/-- A satisfied trace from the canonical seeds: its crumbs are valid, eight per row, and
the final accumulators read as the Algorithm-2 decompositions of the concatenated crumb
stream. -/
private theorem chain_sound [Field F] [DecidableEq F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (V : Valuation F)
    {pref : List (Vector (FVar F) 8)} {fin : FVar F × FVar F × FVar F}
    {rounds : List (EndoScalarRound F)}
    (hthr : Chain Threads (.const 2, .const 2, .const 0) pref rounds fin)
    (hHolds : ∀ r ∈ rounds, Kimchi.Gate.EndoScalar.Holds (EndoScalarRound.read V r)) :
      (∀ x ∈ roundCrumbs V rounds, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
      (roundCrumbs V rounds).length = 8 * pref.length ∧
      fin.1.val V = Kimchi.Gate.EndoScalar.decomposeA (roundCrumbs V rounds) ∧
      fin.2.1.val V = Kimchi.Gate.EndoScalar.decomposeB (roundCrumbs V rounds) ∧
      fin.2.2.val V = Kimchi.Gate.EndoScalar.nReconstruct (roundCrumbs V rounds) := by
  match hround : rounds, hthr with
  | [], hthr' =>
    obtain ⟨rfl, rfl⟩ := Chain.of_nil_out hthr'
    refine ⟨by simp [roundCrumbs], by simp [roundCrumbs], ?_, ?_, ?_⟩ <;>
      simp [roundCrumbs, Kimchi.Gate.EndoScalar.decomposeA,
        Kimchi.Gate.EndoScalar.decomposeB, Kimchi.Gate.EndoScalar.decomposeFold,
        Kimchi.Gate.EndoScalar.nReconstruct, CVar.val]
  | r₀ :: rs, hthr' =>
    subst hround
    obtain ⟨hlink, ⟨h01, h02, h03⟩, hf1, hf2, hf3⟩ := threads_wiring hthr'
    have hne : (r₀ :: rs).map (EndoScalarRound.read V) ≠ [] := by simp
    have hholds : ∀ w ∈ (r₀ :: rs).map (EndoScalarRound.read V),
        Kimchi.Gate.EndoScalar.Holds w := by
      intro w hw
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
      exact hHolds r hr
    obtain ⟨hrows, hopen, hlink'⟩ := Kimchi.Gate.EndoScalar.isChain_getD _ hne hholds
        ((List.isChain_map _).mpr
          (hlink.imp fun a b hab =>
            ⟨congrArg (·.val V) hab.1, congrArg (·.val V) hab.2.1,
              congrArg (·.val V) hab.2.2⟩))
        (by simp [EndoScalarRound.read, h01, CVar.val])
        (by simp [EndoScalarRound.read, h02, CVar.val])
        (by simp [EndoScalarRound.read, h03, CVar.val])
    obtain ⟨hA, hB, hN⟩ := Kimchi.Gate.EndoScalar.chain_decompose _ _ hrows hopen hlink'
    rw [Nat.sub_add_cancel (by simp), Kimchi.Gate.EndoScalar.chainCrumbs_getD,
      Kimchi.Gate.EndoScalar.getD_length_sub_one _ hne, List.getLast_map] at hA hB hN
    have hstream : ((r₀ :: rs).map (EndoScalarRound.read V)).flatMap (·.crumbs)
        = roundCrumbs V (r₀ :: rs) := by
      rw [roundCrumbs, List.flatMap_map]
      rfl
    rw [hstream] at hA hB hN
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp only [roundCrumbs, List.mem_flatMap] at hx
      obtain ⟨r, hr, hxr⟩ := hx
      obtain ⟨cv, -, rfl⟩ := List.mem_map.mp hxr
      exact (Kimchi.Gate.EndoScalar.sound h2 h3 _ (hHolds r hr)).1 _ hxr
    · have hrows := chain_rows hthr'
      have hlen : (r₀ :: rs).length = pref.length := by
        rw [← hrows, List.length_map]
      simp only [roundCrumbs, List.length_flatMap, ← hlen]
      simp
      omega
    · exact (congrArg (fun cv : CVar F => cv.val V) hf1).symm.trans hA
    · exact (congrArg (fun cv : CVar F => cv.val V) hf2).symm.trans hB
    · exact (congrArg (fun cv : CVar F => cv.val V) hf3).symm.trans hN

open Std.WP in
/-- The step's spec: the round it emits is wired to the accumulators either side. -/
@[spec] private theorem row_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (st : FVar F × FVar F × FVar F) (xs : Vector (FVar F) 8) :
    ⦃fun _ => True⦄
    toFieldChecked'.row (F := F) (c := Builder V (KimchiConstraint F)) st xs
    ⦃fun p _ => Threads st xs p.1 p.2⦄ := by
  simp only [toFieldChecked'.row, Threads]
  vcgen
  exact ⟨rfl, rfl⟩

open Std.WP in
/-- **Soundness.** Any satisfying valuation exhibits valid crumbs, eight per row, whose
Algorithm-2 decompositions are the three accumulators returned. -/
@[spec] private theorem toFieldChecked'_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (rows : ℕ) (scalar : FVar F) :
    ⦃fun _ => True⦄
    toFieldChecked' (c := Builder V (KimchiConstraint F)) rows scalar
    ⦃fun r _ => ∃ crumbs : List F,
      (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
      crumbs.length = 8 * rows ∧
      r.1.val V = Kimchi.Gate.EndoScalar.decomposeA crumbs ∧
      r.2.1.val V = Kimchi.Gate.EndoScalar.decomposeB crumbs ∧
      r.2.2.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs⦄ := by
  have hloop := mapAccumM_spec (V := V) (c := KimchiConstraint F)
    (toFieldChecked'.row (F := F)) Threads row_spec
  simp only [toFieldChecked']
  vcgen [hloop]
  rename_i _ rs _ _ _ _ hchain hpay
  have hHolds : ∀ r ∈ rs, Kimchi.Gate.EndoScalar.Holds (EndoScalarRound.read V r) := hpay
  obtain ⟨hv, hlen, hA, hB, hN⟩ := chain_sound h2 h3 V hchain hHolds
  exact ⟨_, hv, by simpa using hlen, hA, hB, hN⟩

open Std.WP in
/-- **Soundness of the wrapper** at `rows` rows: any satisfying valuation reads the scalar as
some `n < 2 ^ (16 · rows)`, and the result as `Kimchi.Gate.EndoScalar.toField` of `n`'s
`8 · rows` crumbs. -/
theorem toField_spec_rows {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (rows : ℕ) (scalar endo : FVar F) :
    ⦃fun _ => True⦄
    toField (c := Builder V (KimchiConstraint F)) rows scalar endo
    ⦃fun r _ => ∃ n : ℕ, n < 2 ^ (16 * rows) ∧ scalar.val V = ((n : ℕ) : F) ∧
      r.val V = Kimchi.Gate.EndoScalar.toField
        (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) n) (endo.val V)⦄ := by
  have hpack : ∀ (crumbs : List F) (rv sv ev : F),
      (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) → crumbs.length = 8 * rows →
      rv = Kimchi.Gate.EndoScalar.toField crumbs ev →
      sv = Kimchi.Gate.EndoScalar.nReconstruct crumbs →
      ∃ n : ℕ, n < 2 ^ (16 * rows) ∧ sv = ((n : ℕ) : F) ∧
        rv = Kimchi.Gate.EndoScalar.toField
          (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) n) ev := by
    intro crumbs rv sv ev hv hlen hr hs
    obtain ⟨n, hnlt, hcr⟩ := Kimchi.Gate.EndoScalar.eq_crumbsOf h2 h3 crumbs hv
    rw [hlen] at hnlt hcr
    have h4 : (4 : ℕ) ^ (8 * rows) = 2 ^ (16 * rows) := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]; ring_nf
    refine ⟨n, h4 ▸ hnlt, ?_, ?_⟩
    · rw [hs, hcr, Kimchi.Gate.EndoScalar.nReconstruct_crumbsOf, Nat.mod_eq_of_lt hnlt]
    · rw [hr, hcr]
  have hchk := toFieldChecked'_spec (V := V) h2 h3 rows scalar
  simp only [toField]
  vcgen [hchk]
  case vc1 =>
    rename_i hdec _ _ heq e hendo
    subst hendo
    obtain ⟨crumbs, hv, hlen, ha, hb, hn⟩ := hdec
    refine hpack crumbs _ _ _ hv hlen ?_ (by rw [← heq, hn])
    simp only [Kimchi.Gate.EndoScalar.toField, CVar.val_add_, CVar.val_scale_,
      ha, hb, CVar.val]
    ring
  rename_i hdec _ _ heq _ _ _ _ hmul
  obtain ⟨crumbs, hv, hlen, ha, hb, hn⟩ := hdec
  refine hpack crumbs _ _ _ hv hlen ?_ (by rw [← heq, hn])
  simp only [Kimchi.Gate.EndoScalar.toField, CVar.val_add_, hmul, ha, hb]
  ring

open Std.WP in
/-- **Soundness of the wrapper**, at the deployed eight rows: any satisfying valuation
reads the scalar as some `n < 2 ^ 128`, and the result as `Poseidon.FqSponge.endoExpand`
of `n`. -/
@[spec] theorem toField_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (scalar endo : FVar F) :
    ⦃fun _ => True⦄
    toField (c := Builder V (KimchiConstraint F)) 8 scalar endo
    ⦃fun r _ => ∃ n : ℕ, n < 2 ^ 128 ∧ scalar.val V = ((n : ℕ) : F) ∧
      r.val V = Poseidon.FqSponge.endoExpand (endo.val V) n⦄ := by
  have h := toField_spec_rows (V := V) h2 h3 8 scalar endo
  refine builder_spec_imp _ _ _ h fun r ⟨n, hn, hs, hr⟩ => ⟨n, by simpa using hn, hs, ?_⟩
  rw [hr, ← Kimchi.Gate.EndoScalar.endoExpand_eq_toField h2 h3]

/-! ## The completeness laws

The laws at the prover's reading (`Snarky.Prover.VCGen`): the operands' readings in, the
result's reading out, the values as parameters. A round reads as `Row`: its opening
accumulators, its crumbs, and its closing accumulators at the canonical row's outputs `next`.
`Spec.mapAccumM` collects the rounds' readings along `scan` and the accumulators' along the fold.
Each round holds by the gate's `Kimchi.Gate.EndoScalar.complete` on its own valid crumbs,
whatever accumulators it threads, and `values_fold` reads the fold as the decomposition of the
scalar's crumbs. -/

section ProverReading

open Snarky.Prover Std.WP

/-! ### The round -/

/-- The round's advice from the readings: `Kimchi.Gate.EndoScalar.build`'s outputs, in the
witness's allocation order `(a8, b8, n8)`. -/
private def rowVal [Field F] (a0 b0 n0 : F) (crumbs : List F) : F × F × F :=
  let w := Kimchi.Gate.EndoScalar.build a0 b0 n0 crumbs
  (w.a8, w.b8, w.n8)

/-- The accumulators a round closes at, from those it opens at and its crumbs. -/
private def next [Field F] (a : F × F × F) (v : Vector F 8) : F × F × F :=
  rowVal a.1 a.2.1 a.2.2 v.toList

/-- A round's reading: it opens at accumulators reading `av.1`, its crumbs read `av.2`, and it
closes at accumulators reading their `next`. -/
private noncomputable def Row [Field F] (r : EndoScalarRound F)
    (av : (F × F × F) × Vector F 8) : Pred F :=
  Reads (r.a0, r.b0, r.n0) av.1 ⊓
    (Reads (r.a8, r.b8, r.n8) (next av.1 av.2) ⊓ Reads r.xs av.2)

/-- `rowWit` returns the canonical row's outputs at its operands' readings. -/
private theorem rowWit_run [Field F] [DecidableEq F] {s : ProverState F}
    {xs : Vector (FVar F) 8} {acc : FVar F × FVar F × FVar F} (h1 : acc.1.Scoped s)
    (h2 : acc.2.1.Scoped s) (h3 : acc.2.2.Scoped s) (hxs : ∀ cv ∈ xs.toList, cv.Scoped s) :
    (rowWit xs acc).run s.env = .ok (rowVal (acc.1.val s.env.get) (acc.2.1.val s.env.get)
      (acc.2.2.val s.env.get) (xs.toList.map (·.val s.env.get))) := by
  simp only [rowWit, rowVal, AsProver.bind_eq, AsProver.run_bind, AsProver.readCVar_run h1,
    AsProver.readCVar_run h2, AsProver.readCVar_run h3, run_mapM_readCVar hxs, Except.bind]
  rfl

/-- `rowWit`'s advice: at accumulators reading `a` and crumbs reading `v`, it returns
`next a v`. -/
private theorem Prover.row_advice [Field F] [DecidableEq F] (acc : FVar F × FVar F × FVar F)
    (a : F × F × F) (xs : Vector (FVar F) 8) (v : Vector F 8) :
    Reads acc a ⊓ Reads xs v ≤ Advice (rowWit xs acc) (next a v) := by
  prover_assert with
    simp only [Reads.vector_apply, Reads.prod_apply, Reads.fvar_apply] at *
    grind [rowWit_run, next]

/-- The round's completeness: from accumulators reading `a` and crumbs reading `v`, the round
reads as `Row` and the next accumulators read `next a v`. -/
private theorem Prover.endoScalarRound_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (acc : FVar F × FVar F × FVar F) (a : F × F × F)
    (xs : Vector (FVar F) 8) (v : Vector F 8) :
    ⦃Reads acc a ⊓ Reads xs v⦄ toFieldChecked'.row (c := Prover c) acc xs
    ⦃fun p ↦ Row p.1 (a, v) ⊓ Reads p.2 (next a v)⦄ := by
  have hw := Spec.witness (c := c) (rowWit xs acc) (next a v) (by simp)
  unfold toFieldChecked'.row
  vcgen [hw]
  all_goals first | exact Prover.row_advice acc a xs v | prover_assert with simp_all [Row]

/-- The loop's completeness: the rounds read as `Row` along `scan next`, and the final
accumulators read the fold of `next` over the rows' crumbs. -/
private theorem Prover.endoScalarLoop_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (init : FVar F × FVar F × FVar F) (a : F × F × F)
    (xs : List (Vector (FVar F) 8)) (vs : List (Vector F 8)) :
    ⦃Reads init a ⊓ All₂ Reads xs vs⦄
      mapAccumM (toFieldChecked'.row (c := Prover c)) init xs
    ⦃fun p ↦ All₂ Row p.1 (scan next Prod.mk a vs) ⊓ Reads p.2 (vs.foldl next a)⦄ :=
  Spec.mapAccumM _ Reads Reads Row next Prod.mk Prover.endoScalarRound_spec init a xs vs

/-! ### The `endoScalar` row -/

/-- A round reading as `Row` on valid crumbs satisfies its `endoScalar` row, cells in scope. -/
private theorem Prover.row_checked [Field F] [DecidableEq F] (r : EndoScalarRound F)
    (a : F × F × F) (v : Vector F 8) (hv : ∀ x ∈ v.toList, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) :
    Row r (a, v) ≤ Checked (F := F) (KimchiConstraint.endoScalar [r]) := by
  have hc := Kimchi.Gate.EndoScalar.complete a.1 a.2.1 a.2.2 v.toList hv
  prover_assert with
    intros
    simp only [Row, Pred.inf_apply, Reads.prod_apply, Reads.fvar_apply,
      Reads.vector_apply] at *
    simp only [Checked.apply] at *
    simp_all [ConstraintHolds.Holds, ConstraintHolds.cells, KimchiConstraint.Holds,
      KimchiConstraint.cells, next, rowVal, EndoScalarRound.read,
      Kimchi.Gate.EndoScalar.build]

/-- An `endoScalar` row over a list of rounds is checked exactly when its head's and its tail's
are. -/
private theorem Prover.checked_cons [Field F] [DecidableEq F] (r : EndoScalarRound F)
    (rs : List (EndoScalarRound F)) :
    Checked (F := F) (KimchiConstraint.endoScalar (r :: rs)) =
      Checked (F := F) (KimchiConstraint.endoScalar [r]) ⊓
        Checked (F := F) (KimchiConstraint.endoScalar rs) := by
  apply Pred.ext
  intro s
  simp only [Pred.inf_apply, Checked.apply, ConstraintHolds.Holds, ConstraintHolds.cells,
    KimchiConstraint.Holds, KimchiConstraint.cells, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.forall_mem_cons, List.forall_mem_append]
  tauto

/-- Rounds reading as `Row` on valid crumbs satisfy their `endoScalar` row, cells in scope. -/
private theorem Prover.rows_checked [Field F] [DecidableEq F] (rs : List (EndoScalarRound F))
    (avs : List ((F × F × F) × Vector F 8))
    (hv : ∀ av ∈ avs, ∀ x ∈ av.2.toList, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) :
    All₂ Row rs avs ≤ Checked (F := F) (KimchiConstraint.endoScalar rs) := by
  induction rs generalizing avs with
  | nil =>
    cases avs <;> simp only [All₂]
    · apply top_le_iff.mpr
      apply Pred.ext
      simp [Checked.apply, ConstraintHolds.Holds, ConstraintHolds.cells,
        KimchiConstraint.Holds, KimchiConstraint.cells]
    · exact bot_le
  | cons r rs ih =>
    cases avs with
    | nil => simp only [All₂]; exact bot_le
    | cons av avs =>
      have hhead := Prover.row_checked r av.1 av.2 (hv av (by simp))
      have htail := ih avs (fun av ha ↦ hv av (by simp [ha]))
      rw [All₂, Prover.checked_cons]
      exact inf_le_inf hhead htail

/-! ### The crumbs -/

/-- The rows' crumb values: the scalar's base-4 expansion, eight crumbs to a row. -/
private def values [Field F] (rows k : ℕ) : List (Vector F 8) :=
  (chunkVec (crumbsVec (rows * 8) k)).toList

/-- The rows' crumbs concatenated are the scalar's expansion. -/
private theorem values_flat [Field F] (rows k : ℕ) :
    ((values (F := F) rows k).map Vector.toList).flatten =
      Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) k := by
  have hf := flatten_map_chunkVec (crumbsVec (F := F) (rows * 8) k) id
  simp only [List.map_id] at hf
  rw [values, hf, Nat.mul_comm 8 rows]
  apply List.ext_getElem (by simp [Kimchi.Gate.EndoScalar.crumbsOf_length])
  intro i hi hi'
  simp only [crumbsVec, Vector.getElem_toList, Vector.getElem_ofFn]
  exact List.getD_eq_getElem _ _ hi'

/-- Every row's crumbs are valid. -/
private theorem values_valid [Field F] (rows k : ℕ) :
    ∀ v ∈ values (F := F) rows k, ∀ x ∈ v.toList, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  intro v hv x hx
  apply Kimchi.Gate.EndoScalar.crumbsOf_valid (8 * rows) k x
  rw [← values_flat]
  exact List.mem_flatten.mpr ⟨v.toList, List.mem_map_of_mem hv, hx⟩

/-- The rounds' values along `scan` carry the rows' crumbs, so they are valid when those are. -/
private theorem scan_valid [Field F] (a : F × F × F) (vs : List (Vector F 8))
    (hv : ∀ v ∈ vs, ∀ x ∈ v.toList, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) :
    ∀ av ∈ scan next Prod.mk a vs, ∀ x ∈ av.2.toList, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  induction vs generalizing a with
  | nil => simp [scan]
  | cons v vs ih =>
    simpa only [scan, List.forall_mem_cons] using
      And.intro (hv v (by simp)) (ih (next a v) (fun v h ↦ hv v (by simp [h])))

/-- The rows' steps fold to the folds over their concatenated crumbs. -/
private theorem scan_fold [Field F] :
    ∀ (vs : List (Vector F 8)) (a b n : F),
      vs.foldl next (a, b, n) =
        ((vs.map Vector.toList).flatten.foldl
            (fun acc x => 2 * acc + Kimchi.Gate.EndoScalar.cPoly x) a,
          (vs.map Vector.toList).flatten.foldl
            (fun acc x => 2 * acc + Kimchi.Gate.EndoScalar.dPoly x) b,
          (vs.map Vector.toList).flatten.foldl (fun acc x => 4 * acc + x) n)
  | [], _, _, _ => rfl
  | v :: vs, a, b, n => by
    rw [List.foldl_cons, List.map_cons, List.flatten_cons, List.foldl_append, List.foldl_append,
      List.foldl_append]
    exact scan_fold vs _ _ _

/-- From the canonical seeds, the rows' fold is the decomposition of the scalar's crumbs. -/
private theorem values_fold [Field F] (rows k : ℕ) :
    (values (F := F) rows k).foldl next (2, 2, 0) =
      (Kimchi.Gate.EndoScalar.decomposeA (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) k),
        Kimchi.Gate.EndoScalar.decomposeB (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) k),
        Kimchi.Gate.EndoScalar.nReconstruct (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) k)) := by
  rw [scan_fold, values_flat]
  rfl

/-- `crumbsWit` returns the expansion of the scalar's reading. -/
private theorem crumbsWit_run [Field F] [ToNat F] {s : ProverState F} {rows : ℕ}
    {scalar : FVar F} (h : scalar.Scoped s) :
    (crumbsWit rows scalar).run s.env
      = .ok (crumbsVec (rows * 8) (ToNat.toNat (scalar.val s.env.get))) := by
  simp [crumbsWit, AsProver.readCVar_run h]

/-- `crumbsWit`'s advice: at a scalar reading `v`, it returns the expansion of `v`. -/
private theorem Prover.crumbs_advice [Field F] [ToNat F] (rows : ℕ) (scalar : FVar F) (v : F) :
    Reads scalar v ≤ Advice (crumbsWit rows scalar) (crumbsVec (rows * 8) (ToNat.toNat v)) := by
  prover_assert with
    simp only [Reads.fvar_apply] at *
    grind [crumbsWit_run]

/-! ### The decomposition -/

/-- `toFieldChecked'`'s completeness: at a scalar reading `v`, the three accumulators read as
the decompositions of `v`'s `8 · rows` crumbs. -/
theorem Prover.endoScalar_spec [Field F] [DecidableEq F] [ToNat F] (rows : ℕ) (scalar : FVar F)
    (v : F) :
    ⦃Reads scalar v⦄ toFieldChecked' (c := Prover (KimchiConstraint F)) rows scalar
    ⦃fun r ↦ Reads r
      (Kimchi.Gate.EndoScalar.decomposeA
          (Kimchi.Gate.EndoScalar.crumbsOf (F := F) (8 * rows) (ToNat.toNat v)),
        Kimchi.Gate.EndoScalar.decomposeB
          (Kimchi.Gate.EndoScalar.crumbsOf (F := F) (8 * rows) (ToNat.toNat v)),
        Kimchi.Gate.EndoScalar.nReconstruct
          (Kimchi.Gate.EndoScalar.crumbsOf (F := F) (8 * rows) (ToNat.toNat v)))⦄ := by
  have hw := Spec.witness (c := KimchiConstraint F) (crumbsWit rows scalar)
    (crumbsVec (rows * 8) (ToNat.toNat v)) (by simp)
  have hl := fun xs ↦ Prover.endoScalarLoop_spec (F := F) (c := KimchiConstraint F)
    (CVar.const 2, CVar.const 2, CVar.const 0) (2, 2, 0) xs (values rows (ToNat.toNat v))
  have he := Spec.emit (F := F) (c := KimchiConstraint F)
  have hcheck := fun rs ↦ Prover.rows_checked (F := F) rs (scan next Prod.mk (2, 2, 0)
    (values rows (ToNat.toNat v))) (scan_valid _ _ (values_valid rows (ToNat.toNat v)))
  have hchunk := fun xs ↦ Reads.chunk xs (crumbsVec (F := F) (rows * 8) (ToNat.toNat v))
  unfold toFieldChecked'
  vcgen [hw, hl, he]
  all_goals first
    | exact Prover.crumbs_advice rows scalar v
    | prover_assert with
        (try simp only [values_fold, Checked.prover_eq, KimchiSystem.endoScalar] at *)
        simp_all [Reads.prod_apply, Reads.fvar_apply, CVar.scoped_const, CVar.val, values]

/-! ### The wrapper -/

/-- The crumbs of a scalar whose representative fits their width reconstruct it. -/
private theorem nReconstruct_crumbsOf_of_lt [Field F] [ToNat F] [LawfulToNat F] {rows : ℕ}
    {v : F} (hlt : ToNat.toNat v < 2 ^ (16 * rows)) :
    Kimchi.Gate.EndoScalar.nReconstruct
      (Kimchi.Gate.EndoScalar.crumbsOf (F := F) (8 * rows) (ToNat.toNat v)) = v := by
  have h4 : (4 : ℕ) ^ (8 * rows) = 2 ^ (16 * rows) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]; ring_nf
  rw [Kimchi.Gate.EndoScalar.nReconstruct_crumbsOf, Nat.mod_eq_of_lt (h4 ▸ hlt),
    LawfulToNat.cast_toNat]

/-- `toField`'s completeness at `rows` rows: at a scalar reading `v` whose representative fits
`16 · rows` bits and a coefficient reading `e`, the result reads as the gate's effective scalar
of `v`'s crumbs at `e`. -/
theorem Prover.toField_spec_rows [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (rows : ℕ) (scalar endo : FVar F) (v e : F) (hlt : ToNat.toNat v < 2 ^ (16 * rows)) :
    ⦃Reads scalar v ⊓ Reads endo e⦄ toField (c := Prover (KimchiConstraint F)) rows scalar endo
    ⦃fun r ↦ Reads r (Kimchi.Gate.EndoScalar.toField
      (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) (ToNat.toNat v)) e)⦄ := by
  have hd := Prover.endoScalar_spec (F := F) rows scalar v
  have ha := fun n : FVar F ↦ Prover.assertEqual_spec (c := KimchiConstraint F) n scalar v
  have hm := fun a : FVar F ↦ Prover.mul_spec (c := KimchiConstraint F) a endo
    (Kimchi.Gate.EndoScalar.decomposeA
      (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) (ToNat.toNat v))) e
  have hnv := nReconstruct_crumbsOf_of_lt (rows := rows) hlt
  unfold toField
  vcgen [hd, ha, hm]
  all_goals prover_assert with
    (intros; simp_all [Reads.prod_apply, Reads.fvar_apply, Kimchi.Gate.EndoScalar.toField,
      CVar.val_add_, CVar.val_scale_, CVar.Scoped.add_, CVar.Scoped.scale_, CVar.val, mul_comm,
      add_comm])

/-- `toField`'s completeness at the deployed eight rows: at a scalar reading `v` below
`2 ^ 128` and a coefficient reading `e`, the result reads as `Poseidon.FqSponge.endoExpand`
of `v` at `e`. -/
theorem Prover.toField_spec [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (scalar endo : FVar F) (v e : F)
    (hlt : ToNat.toNat v < 2 ^ 128) :
    ⦃Reads scalar v ⊓ Reads endo e⦄ toField (c := Prover (KimchiConstraint F)) 8 scalar endo
    ⦃fun r ↦ Reads r (Poseidon.FqSponge.endoExpand e (ToNat.toNat v))⦄ := by
  rw [Kimchi.Gate.EndoScalar.endoExpand_eq_toField h2 h3]
  exact Prover.toField_spec_rows 8 scalar endo v e hlt

end ProverReading

attribute [irreducible] EndoScalar.toFieldChecked' EndoScalar.toFieldChecked'.row
  EndoScalar.toField

end Snarky.Kimchi.EndoScalar
