import Snarky.DSL.Field
import Kimchi.Gate.Semantics.EndoScalar
import Snarky.DSL.Assert
import Snarky.DSL.Bits
import Snarky.Kimchi.Semantics
import Snarky.Traverse
import Snarky.Prover.StdWP
import Mathlib.Util.CountHeartbeats

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

open Std.Do in
/-- The step's spec: the round it emits is wired to the accumulators either side. -/
@[spec] private theorem row_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (st : FVar F × FVar F × FVar F) (xs : Vector (FVar F) 8) :
    ⦃⌜True⌝⦄
    toFieldChecked'.row (F := F) (c := Builder V (KimchiConstraint F)) st xs
    ⦃⇓ p _ => ⌜Threads st xs p.1 p.2⌝⦄ := by
  simp only [toFieldChecked'.row, Threads]
  mvcgen

open Std.Do in
/-- **Soundness.** Any satisfying valuation exhibits valid crumbs, eight per row, whose
Algorithm-2 decompositions are the three accumulators returned. -/
@[spec] private theorem toFieldChecked'_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (rows : ℕ) (scalar : FVar F) :
    ⦃⌜True⌝⦄
    toFieldChecked' (c := Builder V (KimchiConstraint F)) rows scalar
    ⦃⇓ r _ => ⌜∃ crumbs : List F,
      (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) ∧
      crumbs.length = 8 * rows ∧
      r.1.val V = Kimchi.Gate.EndoScalar.decomposeA crumbs ∧
      r.2.1.val V = Kimchi.Gate.EndoScalar.decomposeB crumbs ∧
      r.2.2.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs⌝⦄ := by
  have hloop := mapAccumM_spec (V := V) (c := KimchiConstraint F)
    (toFieldChecked'.row (F := F)) Threads row_spec
  simp only [toFieldChecked']
  mvcgen [hloop]
  rename_i _ crumbs _ _ p _ hchain _ _ hpay
  have hHolds : ∀ r ∈ p.1, Kimchi.Gate.EndoScalar.Holds (EndoScalarRound.read V r) := hpay
  obtain ⟨hv, hlen, hA, hB, hN⟩ := chain_sound h2 h3 V hchain hHolds
  exact ⟨_, hv, by simpa using hlen, hA, hB, hN⟩

open Std.Do in
/-- **Soundness of the wrapper** at `rows` rows: any satisfying valuation reads the scalar as
some `n < 2 ^ (16 · rows)`, and the result as `Kimchi.Gate.EndoScalar.toField` of `n`'s
`8 · rows` crumbs. -/
theorem toField_spec_rows {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (rows : ℕ) (scalar endo : FVar F) :
    ⦃⌜True⌝⦄
    toField (c := Builder V (KimchiConstraint F)) rows scalar endo
    ⦃⇓ r _ => ⌜∃ n : ℕ, n < 2 ^ (16 * rows) ∧ scalar.val V = ((n : ℕ) : F) ∧
      r.val V = Kimchi.Gate.EndoScalar.toField
        (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) n) (endo.val V)⌝⦄ := by
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
  mvcgen [hchk]
  case h_1 =>
    rename_i _ hdec _ e _ _ heq
    obtain ⟨crumbs, hv, hlen, ha, hb, hn⟩ := hdec
    refine hpack crumbs _ _ _ hv hlen ?_ (by rw [← heq, hn])
    simp only [Kimchi.Gate.EndoScalar.toField, CVar.val_add_, CVar.val_scale_,
      ha, hb, CVar.val]
    ring
  rename_i _ hdec _ _ _ _ _ heq _ _ hmul
  obtain ⟨crumbs, hv, hlen, ha, hb, hn⟩ := hdec
  refine hpack crumbs _ _ _ hv hlen ?_ (by rw [← heq, hn])
  simp only [Kimchi.Gate.EndoScalar.toField, CVar.val_add_, hmul, ha, hb]
  ring

open Std.Do in
/-- **Soundness of the wrapper**, at the deployed eight rows: any satisfying valuation
reads the scalar as some `n < 2 ^ 128`, and the result as `Poseidon.FqSponge.endoExpand`
of `n`. -/
@[spec] theorem toField_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (scalar endo : FVar F) :
    ⦃⌜True⌝⦄
    toField (c := Builder V (KimchiConstraint F)) 8 scalar endo
    ⦃⇓ r _ => ⌜∃ n : ℕ, n < 2 ^ 128 ∧ scalar.val V = ((n : ℕ) : F) ∧
      r.val V = Poseidon.FqSponge.endoExpand (endo.val V) n⌝⦄ := by
  have h := toField_spec_rows (V := V) h2 h3 8 scalar endo
  refine builder_spec_imp _ _ _ h fun r ⟨n, hn, hs, hr⟩ => ⟨n, by simpa using hn, hs, ?_⟩
  rw [hr, ← Kimchi.Gate.EndoScalar.endoExpand_eq_toField h2 h3]

/-! ## The state-relative completeness laws

`toFieldChecked'`'s law at the prover's reading (`Snarky.Prover.WP`), on the template of the
scalar-multiplication ladders: the round's step fact in `Prover.ScanStep` shape at readings
named once, the loop's instance of `Prover.mapAccumM_scan_spec` registered, and the law closing
with the loop as a spec-table hit. The model side needs no walk: a row holds by the gate's
`complete` on its own valid crumbs, whatever the accumulators it threads, and the loop's fold is
the decomposition of the concatenated crumbs. -/

section ProverReading

open Std.Do

/-! ### The round at the prover's reading -/

/-- The round's advice from the readings: `Kimchi.Gate.EndoScalar.build`'s outputs, in the
witness's allocation order `(a8, b8, n8)`. -/
private def rowVal [Field F] (a0 b0 n0 : F) (crumbs : List F) : F × F × F :=
  let w := Kimchi.Gate.EndoScalar.build a0 b0 n0 crumbs
  (w.a8, w.b8, w.n8)

/-- The round's canonical row from its advice: what `Kimchi.Gate.EndoScalar.build` computes, in
the witness's own vocabulary, so a round's reading is this record by unfolding alone. -/
private def roundVal [Field F] (a0 b0 n0 : F) (crumbs : List F) :
    Kimchi.Gate.EndoScalar.Witness F :=
  let v := rowVal a0 b0 n0 crumbs
  { a0 := a0, b0 := b0, n0 := n0, a8 := v.1, b8 := v.2.1, n8 := v.2.2, crumbs := crumbs }

/-- The advice's record is the gate's canonical row. -/
private theorem roundVal_eq_build [Field F] (a0 b0 n0 : F) (crumbs : List F) :
    roundVal a0 b0 n0 crumbs = Kimchi.Gate.EndoScalar.build a0 b0 n0 crumbs := rfl

/-- The threaded registers' condition: all three in scope. -/
private def accScoped (st : ProverState F) (a : FVar F × FVar F × FVar F) : Prop :=
  a.1.Scoped st ∧ a.2.1.Scoped st ∧ a.2.2.Scoped st

/-- A row's crumbs in scope. -/
private def crumbsScoped (st : ProverState F) (xs : Vector (FVar F) 8) : Prop :=
  ∀ cv ∈ xs.toList, cv.Scoped st

private theorem rowWit_run [Field F] [DecidableEq F] {s : ProverState F}
    {xs : Vector (FVar F) 8} {acc : FVar F × FVar F × FVar F} (hacc : accScoped s acc)
    (hxs : crumbsScoped s xs) :
    (rowWit xs acc).run s.env = .ok (rowVal (acc.1.val s.env.get) (acc.2.1.val s.env.get)
      (acc.2.2.val s.env.get) (xs.toList.map (·.val s.env.get))) := by
  simp only [rowWit, rowVal, AsProver.bind_eq, AsProver.run_bind, AsProver.readCVar_run hacc.1,
    AsProver.readCVar_run hacc.2.1, AsProver.readCVar_run hacc.2.2, run_mapM_readCVar hxs,
    Except.bind]
  rfl

/-- A round's cells in scope: the six registers and the crumbs. -/
private def rowScoped (st : ProverState F) (r : EndoScalarRound F) : Prop :=
  ∀ cv ∈ r.a8 :: r.b8 :: r.n8 :: r.a0 :: r.b0 :: r.n0 :: r.xs.toList, cv.Scoped st

/-- The threaded registers' reading, flat. -/
private def accRead [Field F] (st : ProverState F) (a : FVar F × FVar F × FVar F) : F × F × F :=
  (st.read a.1, st.read a.2.1, st.read a.2.2)

/-- A row's crumbs' readings. -/
private def crumbsRead [Field F] (st : ProverState F) (xs : Vector (FVar F) 8) : List F :=
  xs.toList.map (·.val st.env.get)

/-- A round's reading: the gate's row at its own cells. -/
private def roundRead [Field F] [DecidableEq F] (st : ProverState F) (r : EndoScalarRound F) :
    Kimchi.Gate.EndoScalar.Witness F :=
  EndoScalarRound.read st.env.get r

/-- The row a round produces, from the registers' and the crumbs' readings. -/
private def rowStep [Field F] (a : F × F × F) (x : List F) : Kimchi.Gate.EndoScalar.Witness F :=
  roundVal a.1 a.2.1 a.2.2 x

/-- The registers' reading after a round: the row's outputs. -/
private def accStep [Field F] (a : F × F × F) (x : List F) : F × F × F :=
  ((rowStep a x).a8, (rowStep a x).b8, (rowStep a x).n8)

set_option Elab.async false in
#count_heartbeats in
/-- The round's chain of states and every entry cell's reading along it, the one place the
chain is known: the witness's state lies past the entry, and an entry cell in scope reads, at
every state past the entry, what it read at the entry. -/
private theorem round_readings [Field F] {s₁ s : ProverState F}
    {acc : FVar F × FVar F × FVar F} {xs : Vector (FVar F) 8} (hl : s₁ ≤ s)
    (hacc : accScoped s₁ acc) (hxs : crumbsScoped s₁ xs) :
    s₁ ≤ s ∧
      ∀ u, s₁ ≤ u →
        acc.1.val u.env.get = acc.1.val s₁.env.get ∧
        acc.2.1.val u.env.get = acc.2.1.val s₁.env.get ∧
        acc.2.2.val u.env.get = acc.2.2.val s₁.env.get ∧
        xs.toList.map (·.val u.env.get) = xs.toList.map (·.val s₁.env.get) :=
  ⟨hl, fun _ hle => ⟨CVar.val_of_le hle hacc.1, CVar.val_of_le hle hacc.2.1,
    CVar.val_of_le hle hacc.2.2, List.map_congr_left fun cv hcv => CVar.val_of_le hle (hxs cv hcv)⟩⟩

set_option Elab.async false in
#count_heartbeats in
/-- A round's reading survives the state's growth when its cells are in scope. -/
private theorem roundRead_of_le [Field F] [DecidableEq F] {st st' : ProverState F}
    (hle : st ≤ st') {r : EndoScalarRound F}
    (h : ∀ cv ∈ r.a8 :: r.b8 :: r.n8 :: r.a0 :: r.b0 :: r.n0 :: r.xs.toList, cv.Scoped st) :
    roundRead st' r = roundRead st r := by
  simp (disch := (apply h; simp)) only [roundRead, EndoScalarRound.read, CVar.val_of_le hle]
  congr 1
  exact List.map_congr_left fun cv hcv => CVar.val_of_le hle (h cv (by simp [hcv]))

/-- `rowWit` returns the round's advice. -/
@[spec] private def Prover.rowWit_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (xs : Vector (FVar F) 8) (acc : FVar F × FVar F × FVar F) :=
  Prover.register (Prover.witness_of_run (c := c) (rowWit xs acc)
    (fun st => accScoped st acc ∧ crumbsScoped st xs)
    (fun st => rowVal (st.read acc.1) (st.read acc.2.1) (st.read acc.2.2)
      (xs.toList.map (·.val st.env.get)))
    (fun _ h => rowWit_run h.1 h.2) fun _ _ => by simp)

set_option Elab.async false in
#count_heartbeats in
/-- The round's step fact: its cells in scope, the next registers in scope, the round reading
as the gate's canonical row at the entry readings, and the registers reading as that row's
outputs. -/
private theorem Prover.endoScalarRound_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (st : ProverState F) (acc : FVar F × FVar F × FVar F)
    (xs : Vector (FVar F) 8) :
    ⦃fun s => ⌜s = st ∧ accScoped st acc ∧ crumbsScoped st xs ∧ True⌝⦄
    toFieldChecked'.row (F := F) (c := Prover c) acc xs
    ⦃⇓ p s' => ⌜Prover.ScanStep accScoped rowScoped accRead crumbsRead roundRead accStep
      rowStep st acc xs p.1 p.2 s'⌝⦄ := by
  unfold toFieldChecked'.row
  mvcgen
  all_goals (try grind [Prover.Reg.iff, CircuitType.ReadsAs, CircuitType.scoped_fvar,
    CircuitType.scoped_prod', CVar.Scoped.of_le, accScoped, crumbsScoped])
  -- the step fact
  rename_i s₁ w s h hpre
  simp only [Prover.Reg.iff] at h
  obtain ⟨rfl, hacc, hxs⟩ := hpre
  obtain ⟨hw, hl⟩ := h
  -- the chain and the entry cells' readings along it, from the one lemma that knows it
  obtain ⟨hl, hrd⟩ := round_readings hl hacc hxs
  simp only [CircuitType.ReadsAs, CircuitType.scoped_prod', CircuitType.scoped_fvar,
    CircuitType.reads_prod', CircuitType.reads_fvar] at hw
  refine ⟨?_, ?_, ?_, ?_, hl⟩
  · simp only [rowScoped, List.forall_mem_cons]
    grind [CVar.Scoped.of_le, accScoped, crumbsScoped]
  · exact ⟨hw.1.1, hw.1.2.1, hw.1.2.2⟩
  -- the two equations: the vocabulary, the advice's readings, and (for the row) the entry
  -- cells' readings, the chain's link found in the context
  · simp (disch := assumption) only [roundRead, EndoScalarRound.read, ProverState.read,
      accRead, crumbsRead, rowStep, hw.2, hrd]
    exact rfl
  · simp only [ProverState.read, accRead, crumbsRead, accStep, rowStep, hw.2]
    exact rfl

set_option Elab.async false in
#count_heartbeats in
/-- The decomposition's loop, registered: the scan corollary at the round, its transports
discharged. -/
@[spec] private def Prover.endoScalarLoop_reg [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (init : FVar F × FVar F × FVar F) (xs : List (Vector (FVar F) 8)) :=
  Prover.register (Prover.mapAccumM_scan_spec accScoped crumbsScoped rowScoped accRead
    crumbsRead roundRead accStep rowStep (toFieldChecked'.row (F := F) (c := Prover c))
    (fun _ => True)
    (fun _ _ _ hle h cv hcv => (h cv hcv).of_le hle)
    (fun _ _ _ hle h cv hcv => (h cv hcv).of_le hle)
    (fun _ _ _ hle h => List.map_congr_left fun cv hcv => CVar.val_of_le hle (h cv hcv))
    (fun _ _ _ hle h => roundRead_of_le hle h)
    (fun st acc x => Prover.endoScalarRound_spec st acc x) init xs)

end ProverReading

/-! ## EXPERIMENT (Q4): the round under `vcgen` and the cells frame -/

section Experiment

open Lean.Order Std.WP

set_option experimental.vcgen true

theorem tuple_fst {α β : Type} (a : α) (b : β) : (a, b).1 = a := rfl

theorem tuple_snd {α β : Type} (a : α) (b : β) : (a, b).2 = b := rfl

/-- An eight-entry vector's list, entry by entry. -/
theorem vec8_toList {α : Type} (xs : Vector α 8) :
    xs.toList = [xs[0], xs[1], xs[2], xs[3], xs[4], xs[5], xs[6], xs[7]] := by
  obtain ⟨⟨l⟩, h⟩ := xs
  match l, h with
  | [_, _, _, _, _, _, _, _], _ => rfl

/-- `crumbsScoped` as its eight cells. -/
theorem crumbsScoped_iff' {st : ProverState F} {xs : Vector (FVar F) 8} :
    crumbsScoped st xs ↔ xs[0].Scoped st ∧ xs[1].Scoped st ∧ xs[2].Scoped st ∧
      xs[3].Scoped st ∧ xs[4].Scoped st ∧ xs[5].Scoped st ∧ xs[6].Scoped st ∧
      xs[7].Scoped st := by
  simp [crumbsScoped, vec8_toList]

/-- `witness (rowWit …)` under a name of its own. -/
def rowWitQ [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (xs : Vector (FVar F) 8) (st : FVar F × FVar F × FVar F) :
    CircuitM F c (FVar F × FVar F × FVar F) :=
  witness (val := F × F × F) (rowWit xs st)

/-- The advice's law, without `st₀ ≤ s'`. -/
@[spec] theorem Prover.rowWitQ_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (xs : Vector (FVar F) 8) (acc : FVar F × FVar F × FVar F)
    (st₀ : ProverState F) :
    ⦃fun s => s = st₀ ∧ (accScoped st₀ acc ∧ crumbsScoped st₀ xs)⦄
    rowWitQ (c := Prover c) xs acc
    ⦃fun r s' => CircuitType.ReadsAs (val := F × F × F) s' r
      (rowVal (st₀.read acc.1) (st₀.read acc.2.1) (st₀.read acc.2.2)
        (xs.toList.map (·.val st₀.env.get)))⦄ := by
  have h := Prover.std_witness_of_run (c := c) (rowWit xs acc)
    (fun st => accScoped st acc ∧ crumbsScoped st xs)
    (fun st => rowVal (st.read acc.1) (st.read acc.2.1) (st.read acc.2.2)
      (xs.toList.map (·.val st.env.get)))
    (fun _ h => rowWit_run h.1 h.2) (fun _ _ => by simp) st₀
  exact h

/-- `toFieldChecked'.row`, verbatim, over the restated leaf. -/
def rowQ [Field F] [DecidableEq F] [BasicSystem F c] [ConstraintHolds F c]
    (st : FVar F × FVar F × FVar F) (xs : Vector (FVar F) 8) :
    CircuitM F c (EndoScalarRound F × (FVar F × FVar F × FVar F)) := do
  let w ← rowWitQ xs st
  pure ({ n0 := st.2.2, n8 := w.2.2, a0 := st.1, a8 := w.1,
          b0 := st.2.1, b8 := w.2.1, xs }, (w.1, w.2.1, w.2.2))

set_option Elab.async false in
#count_heartbeats in
/-- The round's law without its order conjunct, by `vcgen` under the cells frame. -/
theorem Prover.rowQ_spec₀ [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (st : ProverState F) (acc : FVar F × FVar F × FVar F)
    (xs : Vector (FVar F) 8) :
    ⦃fun s => s = st ∧ (accScoped st acc ∧ crumbsScoped st xs ∧ True)⦄
    rowQ (F := F) (c := Prover c) acc xs
    ⦃fun p s' => Prover.ScanStep₀ accScoped rowScoped accRead crumbsRead roundRead accStep
      rowStep st acc xs p.1 p.2 s'⦄ := by
  refine ⟨fun s hs => ?_⟩
  obtain ⟨rfl, hacc, hxs, -⟩ := hs
  simp only [accScoped, crumbsScoped_iff'] at hacc hxs
  unfold rowQ
  vcgen simplifying_assumptions [CircuitType.ReadsAs.eq_1, CircuitType.scoped_prod',
    CircuitType.reads_prod', CircuitType.scoped_fvar, CircuitType.reads_fvar, tuple_fst,
    tuple_snd]
  all_goals first
    | exact Prover.frames_cellsAt _ _ _
    | ((try simp only [CellsAt, rowScoped, vec8_toList, List.forall_mem_cons,
          List.forall_mem_nil, accScoped, crumbsScoped_iff', roundRead, EndoScalarRound.read,
          accRead, crumbsRead, rowStep, accStep, roundVal, List.map_cons, List.map_nil,
          Kimchi.Gate.EndoScalar.Witness.mk.injEq, Prod.mk.injEq, List.cons.injEq,
          and_true] at *)
       grind)

/-- The round's law as written. -/
@[spec] theorem Prover.rowQ_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (st : ProverState F) (acc : FVar F × FVar F × FVar F)
    (xs : Vector (FVar F) 8) :
    ⦃fun s => s = st ∧ (accScoped st acc ∧ crumbsScoped st xs ∧ True)⦄
    rowQ (F := F) (c := Prover c) acc xs
    ⦃fun p s' => Prover.ScanStep accScoped rowScoped accRead crumbsRead roundRead accStep
      rowStep st acc xs p.1 p.2 s'⦄ :=
  Prover.std_scanStep _ _ _ _ _ _ _ (Prover.rowQ_spec₀ st acc xs)

open Std.Do in
set_option Elab.async false in
#count_heartbeats in
/-- The loop's instance, as written, over the `vcgen` round. -/
def Prover.endoScalarLoopQ [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] (init : FVar F × FVar F × FVar F) (xs : List (Vector (FVar F) 8))
    (st₀ : ProverState F) :=
  Prover.mapAccumM_scan_spec accScoped crumbsScoped rowScoped accRead
    crumbsRead roundRead accStep rowStep (rowQ (F := F) (c := Prover c))
    (fun _ => True)
    (fun _ _ _ hle h cv hcv => (h cv hcv).of_le hle)
    (fun _ _ _ hle h cv hcv => (h cv hcv).of_le hle)
    (fun _ _ _ hle h => List.map_congr_left fun cv hcv => CVar.val_of_le hle (h cv hcv))
    (fun _ _ _ hle h => roundRead_of_le hle h)
    (fun st acc x => Prover.do_of_std (Prover.rowQ_spec st acc x)) init xs st₀

end Experiment

end Snarky.Kimchi.EndoScalar

#print axioms Snarky.Kimchi.EndoScalar.Prover.rowQ_spec
#print axioms Snarky.Kimchi.EndoScalar.Prover.endoScalarLoopQ
