import Snarky.Tactic
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
def toFieldChecked' [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]
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

/-! ## Completeness

Each accumulator witness is `Kimchi.Gate.EndoScalar.build`'s outputs, so every row holds by
`Kimchi.Gate.EndoScalar.complete` on valid crumbs; `mapAccumM_complete` chains the rows. -/

/-- The rows the loop is handed: crumb variables in scope, reading as valid 2-bit
values. -/
private def CrumbRow [Field F] (st₁ : ProverState F) (xs : Vector (FVar F) 8) : Prop :=
  ∀ cv ∈ xs.toList, cv.Scoped st₁ ∧
    (cv.val st₁.env.get = 0 ∨ cv.val st₁.env.get = 1 ∨
      cv.val st₁.env.get = 2 ∨ cv.val st₁.env.get = 3)

/-- A round at a table: its cells are in scope, and its row holds. -/
private def RowOk [Field F] [DecidableEq F] (r : EndoScalarRound F) (st : ProverState F) :
    Prop :=
  (∀ cv ∈ r.a8 :: r.b8 :: r.n8 :: r.a0 :: r.b0 :: r.n0 :: r.xs.toList, cv.Scoped st) ∧
    Kimchi.Gate.EndoScalar.Holds (EndoScalarRound.read st.env.get r)

/-- A grant's row still holds at any extension of its table: its cells are in scope, so
their readings do not move. The emitted constraint's obligation needs exactly this. -/
private theorem RowOk.holds_of_le [Field F] [DecidableEq F] {r : EndoScalarRound F}
    {st st' : ProverState F} (hle : st ≤ st') (h : RowOk r st) :
    Kimchi.Gate.EndoScalar.Holds (EndoScalarRound.read st'.env.get r) := by
  obtain ⟨hsc, hholds⟩ := h
  have hread : EndoScalarRound.read st'.env.get r = EndoScalarRound.read st.env.get r := by
    simp (disch := (apply hsc; simp)) only [EndoScalarRound.read, CVar.val_of_le hle]
    congr 1
    exact List.map_congr_left fun cv hcv => CVar.val_of_le hle (hsc cv (by simp [hcv]))
  rw [hread]
  exact hholds

/-- A round's fact survives the table's growth. -/
private theorem monotone_rowOk [Field F] [DecidableEq F] (r : EndoScalarRound F) :
    Monotone (RowOk r) :=
  fun _ _ hle h =>
    ⟨fun cv hcv => (h.1 cv hcv).mono (ProverState.nv_le_of_le hle), RowOk.holds_of_le hle h⟩

/-- The step's completeness: the accumulator witness is the gate's canonical row's
outputs, so the row it closes holds by the gate's own `complete`. -/
private theorem row_complete [Field F] [DecidableEq F] [ToNat F] (st₁ : ProverState F)
    (acc : FVar F × FVar F × FVar F) (xs : Vector (FVar F) 8) (hx : CrumbRow st₁ xs) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => st₁ ≤ st ∧ acc.1.Scoped st ∧ acc.2.1.Scoped st ∧ acc.2.2.Scoped st)
      (toFieldChecked'.row (c := KimchiConstraint F) acc xs)
      (fun p st' => (st₁ ≤ st' ∧ p.2.1.Scoped st' ∧ p.2.2.1.Scoped st' ∧ p.2.2.2.Scoped st') ∧
        Threads acc xs p.1 p.2 ∧ RowOk p.1 st') := by
  have hvalid : ∀ x ∈ xs.toList.map (·.val st₁.env.get),
      x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
    intro x hxm
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp hxm
    exact (hx cv hcv).2
  simp only [toFieldChecked'.row]
  -- the accumulators' entry readings index the law
  refine Complete.instantiate (ι := F × F × F)
    (P := fun v st => st₁ ≤ st ∧
      CircuitType.ReadsAs (val := F) st acc.1 v.1 ∧
      CircuitType.ReadsAs (val := F) st acc.2.1 v.2.1 ∧
      CircuitType.ReadsAs (val := F) st acc.2.2 v.2.2)
    (fun st h =>
      ⟨(acc.1.val st.env.get, acc.2.1.val st.env.get, acc.2.2.val st.env.get), h.1,
        ⟨CircuitType.scoped_fvar.mpr h.2.1, CircuitType.reads_fvar.mpr rfl⟩,
        ⟨CircuitType.scoped_fvar.mpr h.2.2.1, CircuitType.reads_fvar.mpr rfl⟩,
        ⟨CircuitType.scoped_fvar.mpr h.2.2.2, CircuitType.reads_fvar.mpr rfl⟩⟩)
    fun v => ?_
  obtain ⟨a0, b0, n0⟩ := v
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?run, h⟩) (fun _ _ h => h)
      (Complete.frame
        (monotone_and monotone_le
          (monotone_and CircuitType.monotone_readsAs (monotone_and CircuitType.monotone_readsAs
            CircuitType.monotone_readsAs)))
        (Complete.witness (rowWit xs acc)
          ((Kimchi.Gate.EndoScalar.build a0 b0 n0
              (xs.toList.map (·.val st₁.env.get))).a8,
            (Kimchi.Gate.EndoScalar.build a0 b0 n0
              (xs.toList.map (·.val st₁.env.get))).b8,
            (Kimchi.Gate.EndoScalar.build a0 b0 n0
              (xs.toList.map (·.val st₁.env.get))).n8)
          (by simp))))
    fun w => Complete.pure_of fun st h => ?post
  case run =>
    have hxsc : ∀ cv ∈ xs.toList, cv.Scoped st := fun cv hcv => ((hx cv hcv).1).mono
      (ProverState.nv_le_of_le h.1)
    have hcr : xs.toList.map (·.val st.env.get) = xs.toList.map (·.val st₁.env.get) :=
      List.map_congr_left fun cv hcv => CVar.val_of_le h.1 (hx cv hcv).1
    simp only [rowWit, AsProver.bind_eq, AsProver.run_bind,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.1.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.2.1.1),
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.2.2.2.1),
      CircuitType.reads_fvar.mp h.2.1.2, CircuitType.reads_fvar.mp h.2.2.1.2,
      CircuitType.reads_fvar.mp h.2.2.2.2, run_mapM_readCVar hxsc, Except.bind, hcr]
    rfl
  case post =>
    obtain ⟨wa, wb, wn⟩ := w
    obtain ⟨⟨hscW, hrdW⟩, hP⟩ := h
    simp only [CircuitType.scoped_prod, CircuitType.scoped_fvar] at hscW
    simp only [CircuitType.reads_prod, CircuitType.reads_fvar] at hrdW
    have hcr : xs.toList.map (·.val st.env.get) = xs.toList.map (·.val st₁.env.get) :=
      List.map_congr_left fun cv hcv => CVar.val_of_le hP.1 (hx cv hcv).1
    refine ⟨⟨hP.1, hscW.1, hscW.2.1, hscW.2.2⟩,
      ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
    · intro cv hcv
      simp only [List.mem_cons] at hcv
      rcases hcv with rfl | rfl | rfl | rfl | rfl | rfl | hcv
      · exact hscW.1
      · exact hscW.2.1
      · exact hscW.2.2
      · exact CircuitType.scoped_fvar.mp hP.2.1.1
      · exact CircuitType.scoped_fvar.mp hP.2.2.1.1
      · exact CircuitType.scoped_fvar.mp hP.2.2.2.1
      · exact ((hx cv hcv).1).mono (ProverState.nv_le_of_le hP.1)
    · have hread : EndoScalarRound.read st.env.get
          { n0 := acc.2.2, n8 := wn, a0 := acc.1, a8 := wa, b0 := acc.2.1, b8 := wb, xs }
          = Kimchi.Gate.EndoScalar.build a0 b0 n0
              (xs.toList.map (·.val st₁.env.get)) := by
        simp only [EndoScalarRound.read, hrdW.1, hrdW.2.1, hrdW.2.2,
          CircuitType.reads_fvar.mp hP.2.1.2, CircuitType.reads_fvar.mp hP.2.2.1.2,
          CircuitType.reads_fvar.mp hP.2.2.2.2, hcr]
        rfl
      rw [hread]
      exact Kimchi.Gate.EndoScalar.complete a0 b0 n0 _ hvalid

/-- **Completeness.** From a readable scalar the honest run succeeds and the three
accumulators read as the Algorithm-2 decompositions of the scalar's own crumbs. -/
@[complete_law]
private theorem toFieldChecked'_complete [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (rows : ℕ) (scalar : FVar F) (sv : F) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => CircuitType.ReadsAs (val := F) st scalar sv)
      (toFieldChecked' (c := KimchiConstraint F) rows scalar)
      (fun r st' =>
        CircuitType.ReadsAs (val := F) st' r.1 (Kimchi.Gate.EndoScalar.decomposeA
          (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) (ToNat.toNat sv))) ∧
        CircuitType.ReadsAs (val := F) st' r.2.1 (Kimchi.Gate.EndoScalar.decomposeB
          (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) (ToNat.toNat sv))) ∧
        CircuitType.ReadsAs (val := F) st' r.2.2 (Kimchi.Gate.EndoScalar.nReconstruct
          (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) (ToNat.toNat sv)))) := by
  simp only [toFieldChecked']
  refine Complete.bind
    (Complete.imp (fun st h => ?crun) (fun _ _ h => h)
      (Complete.witness (crumbsWit rows scalar)
        (crumbsVec (rows * 8) (ToNat.toNat sv)) (by simp)))
    fun cvars => ?_
  case crun =>
    simp only [crumbsWit, AsProver.bind_eq, AsProver.run_bind,
      AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.1),
      CircuitType.reads_fvar.mp h.2, Except.bind]
    rfl
  -- the crumbs' landing table indexes the rest of the run: `instantiate` names it, and
  -- the index carries the crumb cells' scope and canonical readings
  refine Complete.instantiate
    (ι := {st₁ : ProverState F // ∀ (i : ℕ) (hi : i < rows * 8),
      (cvars[i]'hi).Scoped st₁ ∧
        (cvars[i]'hi).val st₁.env.get
          = (Kimchi.Gate.EndoScalar.crumbsOf (F := F) (rows * 8)
              (ToNat.toNat sv)).getD i 0})
    (P := fun i st => i.1 ≤ st)
    (fun st h =>
      ⟨⟨st, fun i hi =>
        ⟨CircuitType.scoped_fvar.mp (CircuitType.scoped_vector.mp h.1 i hi),
          by simpa [crumbsVec] using
            CircuitType.reads_fvar.mp (CircuitType.reads_vector.mp h.2 i hi)⟩⟩,
        le_rfl⟩)
    fun i => ?_
  obtain ⟨st₁, hentry⟩ := i
  have hP : ∀ x ∈ (chunkVec cvars).toList, CrumbRow st₁ x := by
    intro x hx cv hcv
    obtain ⟨r, hr, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
    obtain ⟨j, hj, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hcv)
    rw [getElem_chunkVec]
    refine ⟨(hentry _ _).1, ?_⟩
    rw [(hentry _ _).2,
      List.getD_eq_getElem _ _ (by rw [Kimchi.Gate.EndoScalar.crumbsOf_length]; omega)]
    exact Kimchi.Gate.EndoScalar.crumbsOf_valid _ _ _ (List.getElem_mem _)
  refine Complete.bind
    (Complete.imp (fun st h => ⟨h, trivial, trivial, trivial⟩) (fun _ _ h => h)
      (mapAccumM_complete (F := F) (c := KimchiConstraint F) toFieldChecked'.row
        (CrumbRow st₁)
        (fun _ acc st => st₁ ≤ st ∧ acc.1.Scoped st ∧ acc.2.1.Scoped st ∧ acc.2.2.Scoped st)
        Threads RowOk
        (fun _ _ => monotone_and monotone_le (monotone_and CVar.monotone_scoped
          (monotone_and CVar.monotone_scoped CVar.monotone_scoped)))
        monotone_rowOk
        (fun acc x _ hx => row_complete st₁ acc x hx)
        (.const 2, .const 2, .const 0) (chunkVec cvars).toList hP))
    fun p => ?_
  obtain ⟨rounds, fin⟩ := p
  refine Complete.bind (Complete.addConstraint ?row)
    fun _ => Complete.pure_of fun st h => ?post
  case row =>
    rintro st ⟨-, -, hrows⟩ stf hle
    exact fun r hr => RowOk.holds_of_le hle (hrows r hr)
  case post =>
    obtain ⟨hinv₂, hchain, hrows⟩ := h
    have hholds := fun r hr => (hrows r hr).2
    obtain ⟨-, -, hA, hB, hN⟩ := chain_sound h2 h3 st.env.get hchain hholds
    have hcrumbs : roundCrumbs st.env.get rounds
        = Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) (ToNat.toNat sv) := by
      have hrows := chain_rows hchain
      have hflat : roundCrumbs st.env.get rounds
          = cvars.toList.map (·.val st.env.get) := by
        rw [roundCrumbs, List.flatMap_def,
          show (fun r : EndoScalarRound F => r.xs.toList.map (·.val st.env.get))
            = (fun row : Vector (FVar F) 8 => row.toList.map (·.val st.env.get)) ∘ (·.xs)
            from rfl,
          ← List.map_map, hrows]
        exact flatten_map_chunkVec cvars _
      rw [hflat, Nat.mul_comm 8 rows]
      refine List.ext_getElem (by simp [Kimchi.Gate.EndoScalar.crumbsOf_length])
        fun i _ h2 => ?_
      have hi : i < rows * 8 := by
        simpa [Kimchi.Gate.EndoScalar.crumbsOf_length] using h2
      simp only [List.getElem_map, Vector.getElem_toList]
      rw [CVar.val_of_le hinv₂.1 (hentry i hi).1, (hentry i hi).2]
      exact List.getD_eq_getElem _ _ h2
    rw [← hcrumbs]
    exact ⟨⟨CircuitType.scoped_fvar.mpr hinv₂.2.1, CircuitType.reads_fvar.mpr hA⟩,
      ⟨CircuitType.scoped_fvar.mpr hinv₂.2.2.1, CircuitType.reads_fvar.mpr hB⟩,
      ⟨CircuitType.scoped_fvar.mpr hinv₂.2.2.2, CircuitType.reads_fvar.mpr hN⟩⟩

/-- **Completeness of the wrapper** at `rows` rows: on a scalar whose `ToNat` reading is
below `2 ^ (16 · rows)`, the honest run succeeds and the result reads as
`Kimchi.Gate.EndoScalar.toField` of its `8 · rows` crumbs. -/
theorem toField_complete_rows [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (rows : ℕ) (scalar endo : FVar F) (sv ev : F)
    (hlt : ToNat.toNat sv < 2 ^ (16 * rows)) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => CircuitType.ReadsAs (val := F) st scalar sv ∧
        CircuitType.ReadsAs (val := F) st endo ev)
      (toField (c := KimchiConstraint F) rows scalar endo)
      (fun r st' => CircuitType.ReadsAs (val := F) st' r
        (Kimchi.Gate.EndoScalar.toField
          (Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) (ToNat.toNat sv)) ev)) := by
  replace hlt : ToNat.toNat sv < 4 ^ (8 * rows) := by
    have h4 : (4 : ℕ) ^ (8 * rows) = 2 ^ (16 * rows) := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]; ring_nf
    rw [h4]; exact hlt
  have hnv : Kimchi.Gate.EndoScalar.nReconstruct
      (Kimchi.Gate.EndoScalar.crumbsOf (F := F) (8 * rows) (ToNat.toNat sv)) = sv := by
    rw [Kimchi.Gate.EndoScalar.nReconstruct_crumbsOf, Nat.mod_eq_of_lt hlt,
      LawfulToNat.cast_toNat]
  simp only [toField]
  complete_walk
  refine Complete.seq (by complete_mono_tac)
    (Complete.imp (fun st h => ⟨hnv ▸ h.2.2.2, h.1.1⟩) (fun _ _ h => h)
      (assertEqual_complete (c := KimchiConstraint F) _ scalar sv))
    fun _ => ?_
  split
  · rename_i e
    refine Complete.pure_of fun st h => ?_
    have he : e = ev := CircuitType.reads_fvar.mp h.1.1.2.2
    refine ⟨CircuitType.scoped_fvar.mpr
      (CVar.Scoped.add_ (CVar.Scoped.scale_ (CircuitType.scoped_fvar.mp h.1.2.1.1))
        (CircuitType.scoped_fvar.mp h.1.2.2.1.1)), CircuitType.reads_fvar.mpr ?_⟩
    simp only [CVar.val_add_, CVar.val_scale_, CircuitType.reads_fvar.mp h.1.2.1.2,
      CircuitType.reads_fvar.mp h.1.2.2.1.2, he, Kimchi.Gate.EndoScalar.toField]
    ring
  · complete_walk
    refine Complete.pure_of fun st h => ?_
    refine ⟨CircuitType.scoped_fvar.mpr
      (CVar.Scoped.add_ (CircuitType.scoped_fvar.mp h.1.1.2.2.1.1)
        (CircuitType.scoped_fvar.mp h.2.1)), CircuitType.reads_fvar.mpr ?_⟩
    rw [CVar.val_add_, CircuitType.reads_fvar.mp h.2.2,
      CircuitType.reads_fvar.mp h.1.1.2.2.1.2, Kimchi.Gate.EndoScalar.toField]
    ring

/-- **Completeness of the wrapper**, at the deployed eight rows: on a scalar whose
`ToNat` reading is below `2 ^ 128`, the honest run succeeds and the result reads as
`Poseidon.FqSponge.endoExpand` of it. -/
@[complete_law]
theorem toField_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (scalar endo : FVar F) (sv ev : F)
    (hlt : ToNat.toNat sv < 2 ^ 128) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => CircuitType.ReadsAs (val := F) st scalar sv ∧
        CircuitType.ReadsAs (val := F) st endo ev)
      (toField (c := KimchiConstraint F) 8 scalar endo)
      (fun r st' => CircuitType.ReadsAs (val := F) st' r
        (Poseidon.FqSponge.endoExpand ev (ToNat.toNat sv))) := by
  rw [show Poseidon.FqSponge.endoExpand ev (ToNat.toNat sv)
      = Kimchi.Gate.EndoScalar.toField
          (Kimchi.Gate.EndoScalar.crumbsOf (8 * 8) (ToNat.toNat sv)) ev from
    Kimchi.Gate.EndoScalar.endoExpand_eq_toField h2 h3 ev _]
  exact toField_complete_rows h2 h3 8 scalar endo sv ev (by simpa using hlt)

attribute [irreducible] EndoScalar.toFieldChecked' EndoScalar.toFieldChecked'.row
  EndoScalar.toField

end Snarky.Kimchi.EndoScalar
