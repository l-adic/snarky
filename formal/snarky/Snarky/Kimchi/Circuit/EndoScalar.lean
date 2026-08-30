import Snarky.DSL.Field
import Kimchi.Gate.Semantics.EndoScalar
import Snarky.DSL.Assert
import Snarky.DSL.Bits
import Snarky.Kimchi.Semantics
import Snarky.Traverse

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
- PS spells a crumb as a pair of `toBits` bits; the witness writes the gate model's own
  base-4 expansion (`Kimchi.Gate.EndoScalar.crumbsOf`) — the same values, in the form
  the gate's completeness and reconstruction laws are stated over.
- PS's `aF`/`bF` fold the bare tables; the row witness computes the gate's canonical
  `Kimchi.Gate.EndoScalar.build` instead — the same field values on the honest (valid)
  crumbs, and the form the gate's completeness certifies.
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

The loop's content is `mapAccumM_spec`'s: the step's grant, chained. What is left to
the gadget is wiring — reading the chain off as the indexed run the gate model's
`chain_decompose` consumes, which owns the fold arithmetic. -/

/-- The step's grant: the round is built from the accumulators either side of it, over
the row it was handed. Structural — no valuation appears. -/
private def Threads (st : FVar F × FVar F × FVar F) (xs : Vector (FVar F) 8)
    (r : EndoScalarRound F) (st' : FVar F × FVar F × FVar F) : Prop :=
  (r.a0 = st.1 ∧ r.b0 = st.2.1 ∧ r.n0 = st.2.2) ∧
    (r.a8 = st'.1 ∧ r.b8 = st'.2.1 ∧ r.n8 = st'.2.2) ∧ r.xs = xs

/-- The crumb stream a round list carries, MSB-first: the rounds' rows concatenated. -/
private def roundCrumbs [Field F] (V : Valuation F) (rounds : List (EndoScalarRound F)) : List F :=
  rounds.flatMap fun r => r.xs.toList.map (·.val V)

/-- A trace's rounds carry the rows it was handed. -/
private theorem chain_rows :
    ∀ {st fin : FVar F × FVar F × FVar F} {xs : List (Vector (FVar F) 8)}
      {rounds : List (EndoScalarRound F)},
      Chain Threads st xs rounds fin → rounds.map (·.xs) = xs
  | _, _, [], _, h => by rw [h.1]; rfl
  | _, _, _ :: _, _, h => by
    obtain ⟨r, tail, _, rfl, ⟨-, -, rfl⟩, hrest⟩ := h
    rw [List.map_cons, chain_rows hrest]

/-- A threaded trace, as a list: adjacent rounds share their accumulator variables, the
first opens at the seed accumulators, and the last closes at the final ones — the three
conditions `Kimchi.Gate.EndoScalar.Chain.ofList` asks for, extracted without touching a
valuation. -/
private theorem threads_wiring :
    ∀ {pref : List (Vector (FVar F) 8)} {st fin : FVar F × FVar F × FVar F}
      {r₀ : EndoScalarRound F} {rs : List (EndoScalarRound F)},
      Chain Threads st pref (r₀ :: rs) fin →
      (r₀ :: rs).IsChain (fun a b => b.a0 = a.a8 ∧ b.b0 = a.b8 ∧ b.n0 = a.n8) ∧
        (r₀.a0 = st.1 ∧ r₀.b0 = st.2.1 ∧ r₀.n0 = st.2.2) ∧
        ((r₀ :: rs).getLast (by simp)).a8 = fin.1 ∧
        ((r₀ :: rs).getLast (by simp)).b8 = fin.2.1 ∧
        ((r₀ :: rs).getLast (by simp)).n8 = fin.2.2
  | [], _, _, _, _, h => absurd h.1 (by simp)
  | _ :: rest, st, fin, r₀, rs, h => by
    obtain ⟨r, tail, mid, heq, ⟨⟨e1, e2, e3⟩, ⟨d1, d2, d3⟩, -⟩, hrest⟩ := h
    injection heq with hr ht
    subst hr ht
    cases rs with
    | nil =>
      obtain ⟨rfl, rfl⟩ := Chain.of_nil_out hrest
      exact ⟨List.isChain_singleton _, ⟨e1, e2, e3⟩, d1, d2, d3⟩
    | cons r₁ ts =>
      obtain ⟨ihlink, ⟨f1, f2, f3⟩, ihlast⟩ := threads_wiring hrest
      refine ⟨ihlink.cons (by simp [f1, f2, f3, d1, d2, d3]), ⟨e1, e2, e3⟩, ?_⟩
      rw [List.getLast_cons (by simp)]
      exact ihlast

/-- A satisfied trace from the canonical seeds computes the gate tower's chain: the
wiring instantiates `chain_decompose`'s indexed run at the rounds' readings, so the
final accumulators read as the decompositions of the concatenated crumb stream. The
gadget contributes wiring; the fold arithmetic is the tower's. -/
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
    obtain ⟨hA, hB, hN⟩ := Kimchi.Gate.EndoScalar.chain_decompose _ _
      (Kimchi.Gate.EndoScalar.Chain.ofList _ hne hholds
        ((List.isChain_map _).mpr
          (hlink.imp fun a b hab =>
            ⟨congrArg (·.val V) hab.1, congrArg (·.val V) hab.2.1,
              congrArg (·.val V) hab.2.2⟩))
        (by simp [EndoScalarRound.read, h01, CVar.val])
        (by simp [EndoScalarRound.read, h02, CVar.val])
        (by simp [EndoScalarRound.read, h03, CVar.val]))
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
/-- **Soundness.** Any satisfying valuation exhibits a valid crumb list of the row
width whose Algorithm-2 decompositions are the three accumulators returned. -/
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
/-- **Soundness of the wrapper**, at the deployed eight rows — the sixty-four crumbs of a
128-bit challenge, the width PS's `toFieldPure` fixes in its `SizedF 128` operand. Any
satisfying valuation reads the scalar as a prechallenge of that width, and the result as
the sponge's endo-expansion of it. -/
@[spec] theorem toField_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (scalar endo : FVar F) :
    ⦃⌜True⌝⦄
    toField (c := Builder V (KimchiConstraint F)) 8 scalar endo
    ⦃⇓ r _ => ⌜∃ n : ℕ, n < 2 ^ 128 ∧ scalar.val V = ((n : ℕ) : F) ∧
      r.val V = Poseidon.FqSponge.endoExpand (endo.val V) n⌝⦄ := by
  -- the crumbs a satisfying run exposes are the canonical expansion of the value they spell
  have hpack : ∀ (crumbs : List F) (rv sv ev : F),
      (∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) → crumbs.length = 8 * 8 →
      rv = Kimchi.Gate.EndoScalar.toField crumbs ev →
      sv = Kimchi.Gate.EndoScalar.nReconstruct crumbs →
      ∃ n : ℕ, n < 2 ^ 128 ∧ sv = ((n : ℕ) : F) ∧
        rv = Poseidon.FqSponge.endoExpand ev n := by
    intro crumbs rv sv ev hv hlen hr hs
    obtain ⟨n, hnlt, hcr⟩ := Kimchi.Gate.EndoScalar.eq_crumbsOf h2 h3 crumbs hv
    rw [hlen] at hnlt hcr
    refine ⟨n, by rw [show (2 : ℕ) ^ 128 = 4 ^ (8 * 8) from by norm_num]; exact hnlt, ?_, ?_⟩
    · rw [hs, hcr, Kimchi.Gate.EndoScalar.nReconstruct_crumbsOf, Nat.mod_eq_of_lt hnlt]
    · rw [hr, hcr, show (8 * 8 : ℕ) = 64 from rfl,
        ← Kimchi.Gate.EndoScalar.endoExpand_eq_toField h2 h3]
  have hchk := toFieldChecked'_spec (V := V) h2 h3 8 scalar
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

/-! ## Completeness

The honest run's rows are the gate's canonical ones — each accumulator witness is
`Kimchi.Gate.EndoScalar.build`'s outputs — so every row holds by the gate's own
`complete` on valid crumbs, and the trace reads as the decomposition of the scalar's
crumb stream. The loop is `mapAccumM_complete`'s. -/

/-- The rows the loop is handed: crumb variables in scope, reading as valid 2-bit
values. -/
private def CrumbRow [Field F] (st₁ : ProverState F) (xs : Vector (FVar F) 8) : Prop :=
  ∀ cv ∈ xs.toList, cv.Scoped st₁ ∧
    (cv.val st₁.env.get = 0 ∨ cv.val st₁.env.get = 1 ∨
      cv.val st₁.env.get = 2 ∨ cv.val st₁.env.get = 3)

/-- The loop's accumulator invariant: the table has only grown since the crumbs were
witnessed, and the three accumulators are in scope. -/
private def AccInv [Field F] (st₁ : ProverState F) (acc : FVar F × FVar F × FVar F)
    (st : ProverState F) : Prop :=
  (st₁.nv ≤ st.nv ∧ st₁.env.Le st.env) ∧
    acc.1.Scoped st ∧ acc.2.1.Scoped st ∧ acc.2.2.Scoped st

/-- The step's grant at a table: the round is wired to the accumulators either side,
its cells are in scope, and its row holds. -/
private def RowGrant [Field F] [DecidableEq F] (acc : FVar F × FVar F × FVar F)
    (xs : Vector (FVar F) 8) (r : EndoScalarRound F)
    (acc' : FVar F × FVar F × FVar F) (st : ProverState F) : Prop :=
  Threads acc xs r acc' ∧
    (∀ cv ∈ r.a8 :: r.b8 :: r.n8 :: r.a0 :: r.b0 :: r.n0 :: r.xs.toList, cv.Scoped st) ∧
    Kimchi.Gate.EndoScalar.Holds (EndoScalarRound.read st.env.get r)

/-- Scope and the table's growth survive further growth. -/
private theorem AccInv.mono [Field F] {st₁ : ProverState F} (acc : FVar F × FVar F × FVar F)
    {st st' : ProverState F} (hnv : st.nv ≤ st'.nv) (hle : st.env.Le st'.env)
    (h : AccInv st₁ acc st) : AccInv st₁ acc st' :=
  ⟨⟨Nat.le_trans h.1.1 hnv, h.1.2.trans hle⟩,
    h.2.1.mono hnv, h.2.2.1.mono hnv, h.2.2.2.mono hnv⟩

/-- A row's grant survives the table's growth: its cells are in scope, so their
readings — and with them the row — do not move. -/
private theorem RowGrant.mono [Field F] [DecidableEq F] (acc : FVar F × FVar F × FVar F)
    (xs : Vector (FVar F) 8) (r : EndoScalarRound F) (acc' : FVar F × FVar F × FVar F)
    {st st' : ProverState F} (hnv : st.nv ≤ st'.nv) (hle : st.env.Le st'.env)
    (h : RowGrant acc xs r acc' st) : RowGrant acc xs r acc' st' := by
  obtain ⟨hthr, hsc, hholds⟩ := h
  refine ⟨hthr, fun cv hcv => (hsc cv hcv).mono hnv, ?_⟩
  have hread : EndoScalarRound.read st'.env.get r = EndoScalarRound.read st.env.get r := by
    simp only [EndoScalarRound.read,
      CVar.val_of_le hle (hsc r.a8 (by simp)), CVar.val_of_le hle (hsc r.b8 (by simp)),
      CVar.val_of_le hle (hsc r.n8 (by simp)), CVar.val_of_le hle (hsc r.a0 (by simp)),
      CVar.val_of_le hle (hsc r.b0 (by simp)), CVar.val_of_le hle (hsc r.n0 (by simp))]
    congr 1
    exact List.map_congr_left fun cv hcv => CVar.val_of_le hle (hsc cv (by simp [hcv]))
  rw [hread]
  exact hholds

/-- The step's completeness: the accumulator witness is the gate's canonical row's
outputs, so the row it closes holds by the gate's own `complete`. -/
private theorem row_complete [Field F] [DecidableEq F] [ToNat F] (st₁ : ProverState F)
    (acc : FVar F × FVar F × FVar F) (xs : Vector (FVar F) 8) (hx : CrumbRow st₁ xs) :
    Complete (F := F) (c := KimchiConstraint F) (AccInv st₁ acc)
      (toFieldChecked'.row (c := KimchiConstraint F) acc xs)
      (fun p st' => AccInv st₁ p.2 st' ∧ RowGrant acc xs p.1 p.2 st') := by
  rintro st ⟨⟨hnv, hle⟩, ha, hb, hn⟩
  have hxsc : ∀ cv ∈ xs.toList, cv.Scoped st := fun cv hcv => ((hx cv hcv).1).mono hnv
  set a0 := acc.1.val st.env.get with ha0
  set b0 := acc.2.1.val st.env.get with hb0
  set n0 := acc.2.2.val st.env.get with hn0
  set crumbs := xs.toList.map (·.val st.env.get) with hcr
  have hvalid : ∀ x ∈ crumbs, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
    intro x hxm
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp hxm
    rw [CVar.val_of_le hle (hx cv hcv).1]
    exact (hx cv hcv).2
  obtain ⟨v, st', hrun, hsat, hnv', hle', hscW, hrdW⟩ :=
    witness_complete (c := KimchiConstraint F) (val := F × F × F) (rowWit xs acc)
      (st := st) (v := ((Kimchi.Gate.EndoScalar.build a0 b0 n0 crumbs).a8,
        (Kimchi.Gate.EndoScalar.build a0 b0 n0 crumbs).b8,
        (Kimchi.Gate.EndoScalar.build a0 b0 n0 crumbs).n8))
      (by simp)
      (by
        simp only [rowWit, AsProver.bind_eq, AsProver.run_bind, AsProver.readCVar_run ha,
          AsProver.readCVar_run hb, AsProver.readCVar_run hn, run_mapM_readCVar hxsc,
          Except.bind]
        rfl)
  obtain ⟨va, vb, vn⟩ := v
  simp only [CircuitType.scoped_prod, CircuitType.scoped_fvar] at hscW
  simp only [CircuitType.reads_prod, CircuitType.reads_fvar] at hrdW
  refine ⟨({ n0 := acc.2.2, n8 := vn, a0 := acc.1, a8 := va, b0 := acc.2.1, b8 := vb, xs },
      (va, vb, vn)), st', hrun.bind rfl,
    fun hnvF hleF => Sat.bind hrun (hsat hnvF hleF) Sat.pure,
    ⟨⟨Nat.le_trans hnv hnv', hle.trans hle'⟩, hscW.1, hscW.2.1, hscW.2.2⟩,
    ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩, ?_, ?_⟩
  · intro cv hcv
    simp only [List.mem_cons] at hcv
    rcases hcv with rfl | rfl | rfl | rfl | rfl | rfl | hcv
    · exact hscW.1
    · exact hscW.2.1
    · exact hscW.2.2
    · exact ha.mono hnv'
    · exact hb.mono hnv'
    · exact hn.mono hnv'
    · exact (hxsc cv hcv).mono hnv'
  · have hread : EndoScalarRound.read st'.env.get
        { n0 := acc.2.2, n8 := vn, a0 := acc.1, a8 := va, b0 := acc.2.1, b8 := vb, xs }
        = Kimchi.Gate.EndoScalar.build a0 b0 n0 crumbs := by
      have hcr' : xs.toList.map (·.val st'.env.get) = crumbs :=
        List.map_congr_left fun cv hcv => CVar.val_of_le hle' (hxsc cv hcv)
      simp only [EndoScalarRound.read, CVar.val_of_le hle' ha, CVar.val_of_le hle' hb,
        CVar.val_of_le hle' hn, hrdW.1, hrdW.2.1, hrdW.2.2, hcr', ← ha0, ← hb0, ← hn0]
      rfl
    rw [hread]
    exact Kimchi.Gate.EndoScalar.complete a0 b0 n0 crumbs hvalid

/-- The loop's grants, read off: the wiring, and every row holding at a later table. -/
private theorem chainAt_facts [Field F] [DecidableEq F] {st₂ stf : ProverState F}
    (hnv : st₂.nv ≤ stf.nv) (hle : st₂.env.Le stf.env) :
    ∀ {init fin : FVar F × FVar F × FVar F} {xs : List (Vector (FVar F) 8)}
      {rounds : List (EndoScalarRound F)},
      ChainAt RowGrant st₂ init xs rounds fin →
      Chain Threads init xs rounds fin ∧
        ∀ r ∈ rounds, Kimchi.Gate.EndoScalar.Holds (EndoScalarRound.read stf.env.get r)
  | _, _, [], _, h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨rfl, rfl⟩, by simp⟩
  | _, _, _ :: _, _, h => by
    obtain ⟨r, tail, mid, rfl, hgrant, hrest⟩ := h
    obtain ⟨hchain, hholds⟩ := chainAt_facts hnv hle hrest
    refine ⟨⟨r, tail, mid, rfl, hgrant.1, hchain⟩, fun r' hr' => ?_⟩
    rcases List.mem_cons.mp hr' with rfl | hr'
    · exact (RowGrant.mono _ _ _ _ hnv hle hgrant).2.2
    · exact hholds r' hr'

/-- **Completeness.** From a readable scalar the honest run succeeds, its rows hold at
every extension, and the three accumulators read as the Algorithm-2 decompositions of
the scalar's own crumb stream. -/
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
  rintro st hR
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar] at hR
  obtain ⟨hsc, hrd⟩ := hR
  obtain ⟨cvars, st₁, hrun₁, hsat₁, hnv₁, hle₁, hscC, hrdC⟩ :=
    witness_complete (c := KimchiConstraint F) (val := Vector F (rows * 8))
      (crumbsWit rows scalar) (st := st) (v := crumbsVec (rows * 8) (ToNat.toNat sv))
      (by simp)
      (by
        simp only [crumbsWit, AsProver.bind_eq, AsProver.run_bind,
          AsProver.readCVar_run hsc, hrd, Except.bind]
        rfl)
  rw [CircuitType.scoped_vector] at hscC
  rw [CircuitType.reads_vector] at hrdC
  have hentry : ∀ (i : ℕ) (hi : i < rows * 8),
      (cvars[i]'hi).Scoped st₁ ∧
        (cvars[i]'hi).val st₁.env.get
          = (Kimchi.Gate.EndoScalar.crumbsOf (F := F) (rows * 8)
              (ToNat.toNat sv)).getD i 0 :=
    fun i hi =>
      ⟨CircuitType.scoped_fvar.mp (hscC i hi),
        by simpa [crumbsVec] using CircuitType.reads_fvar.mp (hrdC i hi)⟩
  have hP : ∀ x ∈ (chunkVec cvars).toList, CrumbRow st₁ x := by
    intro x hx cv hcv
    obtain ⟨r, hr, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
    obtain ⟨j, hj, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hcv)
    rw [getElem_chunkVec]
    refine ⟨(hentry _ _).1, ?_⟩
    rw [(hentry _ _).2,
      List.getD_eq_getElem _ _ (by rw [Kimchi.Gate.EndoScalar.crumbsOf_length]; omega)]
    exact Kimchi.Gate.EndoScalar.crumbsOf_valid _ _ _ (List.getElem_mem _)
  obtain ⟨p, st₂, hrun₂, hsat₂, hinv₂, hchainAt⟩ :=
    mapAccumM_complete (F := F) (c := KimchiConstraint F) toFieldChecked'.row
      (CrumbRow st₁) (fun _ => AccInv st₁) RowGrant
      (fun _ => AccInv.mono (st₁ := st₁)) RowGrant.mono
      (fun acc x _ hx => row_complete st₁ acc x hx)
      (.const 2, .const 2, .const 0) (chunkVec cvars).toList hP st₁
      ⟨⟨Nat.le_refl _, Assignments.Le.refl _⟩, trivial, trivial, trivial⟩
  refine ⟨p.2, st₂, hrun₁.bind (hrun₂.bind (Runs.addConstraint.bind rfl)), ?_, ?_⟩
  · intro stf hnvF hleF
    refine Sat.bind hrun₁ (hsat₁ (Nat.le_trans hinv₂.1.1 hnvF) (hinv₂.1.2.trans hleF)) ?_
    refine Sat.bind hrun₂ (hsat₂ hnvF hleF) ?_
    exact Sat.bind Runs.addConstraint
      (Sat.addConstraint (chainAt_facts hnvF hleF hchainAt).2) Sat.pure
  · obtain ⟨hchain, hholds⟩ :=
      chainAt_facts (Nat.le_refl _) (Assignments.Le.refl _) hchainAt
    obtain ⟨-, -, hA, hB, hN⟩ := chain_sound h2 h3 st₂.env.get hchain hholds
    have hcrumbs : roundCrumbs st₂.env.get p.1
        = Kimchi.Gate.EndoScalar.crumbsOf (8 * rows) (ToNat.toNat sv) := by
      have hrows := chain_rows hchain
      have hflat : roundCrumbs st₂.env.get p.1
          = cvars.toList.map (·.val st₂.env.get) := by
        rw [roundCrumbs, List.flatMap_def,
          show (fun r : EndoScalarRound F => r.xs.toList.map (·.val st₂.env.get))
            = (fun row : Vector (FVar F) 8 => row.toList.map (·.val st₂.env.get)) ∘ (·.xs)
            from rfl,
          ← List.map_map, hrows]
        exact flatten_map_chunkVec cvars _
      rw [hflat, Nat.mul_comm 8 rows]
      refine List.ext_getElem (by simp [Kimchi.Gate.EndoScalar.crumbsOf_length])
        fun i _ h2 => ?_
      have hi : i < rows * 8 := by
        simpa [Kimchi.Gate.EndoScalar.crumbsOf_length] using h2
      simp only [List.getElem_map, Vector.getElem_toList]
      rw [CVar.val_of_le hinv₂.1.2 (hentry i hi).1, (hentry i hi).2]
      exact List.getD_eq_getElem _ _ h2
    rw [← hcrumbs]
    exact ⟨⟨CircuitType.scoped_fvar.mpr hinv₂.2.1, CircuitType.reads_fvar.mpr hA⟩,
      ⟨CircuitType.scoped_fvar.mpr hinv₂.2.2.1, CircuitType.reads_fvar.mpr hB⟩,
      ⟨CircuitType.scoped_fvar.mpr hinv₂.2.2.2, CircuitType.reads_fvar.mpr hN⟩⟩

/-- **Completeness of the wrapper**, at the deployed eight rows — the sixty-four crumbs
of a 128-bit challenge, the width PS's `toFieldPure` fixes in its `SizedF 128` operand.
On a scalar faithful to a representative of that width the honest run succeeds and the
result reads as the sponge's endo-expansion of it. -/
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
  replace hlt : ToNat.toNat sv < 4 ^ (8 * 8) := by norm_num; omega
  rintro st ⟨hRs, hRe⟩
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar]
    at hRs hRe
  obtain ⟨hsc', hrd⟩ := hRs
  obtain ⟨hsce, hrde⟩ := hRe
  have hsc : CircuitType.ReadsAs (val := F) st scalar sv :=
    ⟨CircuitType.scoped_fvar.mpr hsc', CircuitType.reads_fvar.mpr hrd⟩
  simp only [toField]
  obtain ⟨abn, st₁, hrun₁, hsat₁, hRA, hRB, hRN⟩ :=
    toFieldChecked'_complete h2 h3 8 scalar sv st hsc
  have hscA : abn.1.Scoped st₁ := CircuitType.scoped_fvar.mp hRA.1
  have hscB : abn.2.1.Scoped st₁ := CircuitType.scoped_fvar.mp hRB.1
  have hscN : abn.2.2.Scoped st₁ := CircuitType.scoped_fvar.mp hRN.1
  have hA := CircuitType.reads_fvar.mp hRA.2
  have hB := CircuitType.reads_fvar.mp hRB.2
  have hN := CircuitType.reads_fvar.mp hRN.2
  have hpin : abn.2.2.val st₁.env.get = scalar.val st₁.env.get := by
    rw [hN, CVar.val_of_le hrun₁.le hsc', hrd,
      Kimchi.Gate.EndoScalar.nReconstruct_crumbsOf, Nat.mod_eq_of_lt hlt,
      LawfulToNat.cast_toNat]
  obtain ⟨u, st₂, hrun₂, hsat₂, -⟩ :=
    assertEqual_complete (c := KimchiConstraint F) abn.2.2 scalar
      (scalar.val st₁.env.get) st₁
      ⟨⟨CircuitType.scoped_fvar.mpr hscN, CircuitType.reads_fvar.mpr hpin⟩,
        ⟨CircuitType.scoped_fvar.mpr (hsc'.mono hrun₁.nv_le),
          CircuitType.reads_fvar.mpr rfl⟩⟩
  have hA₂ : abn.1.val st₂.env.get
      = Kimchi.Gate.EndoScalar.decomposeA
        (Kimchi.Gate.EndoScalar.crumbsOf (8 * 8) (ToNat.toNat sv)) := by
    rw [CVar.val_of_le hrun₂.le hscA, hA]
  have hB₂ : abn.2.1.val st₂.env.get
      = Kimchi.Gate.EndoScalar.decomposeB
        (Kimchi.Gate.EndoScalar.crumbsOf (8 * 8) (ToNat.toNat sv)) := by
    rw [CVar.val_of_le hrun₂.le hscB, hB]
  split
  · rename_i _ e
    refine ⟨_, st₂, hrun₁.bind (hrun₂.bind rfl),
      fun hnv hle => Sat.bind hrun₁ (hsat₁ (hrun₂.nv_le.trans hnv) (hrun₂.le.trans hle))
        (Sat.bind hrun₂ (hsat₂ hnv hle) Sat.pure),
      CircuitType.scoped_fvar.mpr (CVar.Scoped.add_
        (CVar.Scoped.scale_ (hscA.mono hrun₂.nv_le)) (hscB.mono hrun₂.nv_le)),
      CircuitType.reads_fvar.mpr ?_⟩
    have hev : e = ev := hrde
    simp only [CVar.val_add_, CVar.val_scale_, hA₂, hB₂, hev,
      Kimchi.Gate.EndoScalar.toField]
    ring
  · obtain ⟨pr, st₃, hrun₃, hsat₃, hpr⟩ :=
      mul_complete (c := KimchiConstraint F) abn.1 endo
        (Kimchi.Gate.EndoScalar.decomposeA
          (Kimchi.Gate.EndoScalar.crumbsOf (8 * 8) (ToNat.toNat sv))) ev st₂
        ⟨⟨CircuitType.scoped_fvar.mpr (hscA.mono hrun₂.nv_le),
            CircuitType.reads_fvar.mpr hA₂⟩,
          ⟨CircuitType.scoped_fvar.mpr (hsce.mono (hrun₁.nv_le.trans hrun₂.nv_le)),
            CircuitType.reads_fvar.mpr (by
              rw [CVar.val_of_le (hrun₁.le.trans hrun₂.le) hsce, hrde])⟩⟩
    have hscP : pr.Scoped st₃ := CircuitType.scoped_fvar.mp hpr.1
    have hvalP := CircuitType.reads_fvar.mp hpr.2
    refine ⟨_, st₃, hrun₁.bind (hrun₂.bind (hrun₃.bind rfl)),
      fun hnv hle => Sat.bind hrun₁
        (hsat₁ ((hrun₂.nv_le.trans hrun₃.nv_le).trans hnv)
          ((hrun₂.le.trans hrun₃.le).trans hle))
        (Sat.bind hrun₂ (hsat₂ (hrun₃.nv_le.trans hnv) (hrun₃.le.trans hle))
          (Sat.bind hrun₃ (hsat₃ hnv hle) Sat.pure)),
      CircuitType.scoped_fvar.mpr
        (CVar.Scoped.add_ (hscB.mono (hrun₂.nv_le.trans hrun₃.nv_le)) hscP),
      CircuitType.reads_fvar.mpr ?_⟩
    rw [CVar.val_add_, hvalP, CVar.val_of_le hrun₃.le (hscB.mono hrun₂.nv_le), hB₂,
      Kimchi.Gate.EndoScalar.toField]
    ring

attribute [irreducible] EndoScalar.toFieldChecked' EndoScalar.toFieldChecked'.row
  EndoScalar.toField

end Snarky.Kimchi.EndoScalar
