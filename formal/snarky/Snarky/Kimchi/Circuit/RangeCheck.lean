import Snarky.Tactic
import Snarky.Kimchi.Circuit.EndoScalar
import Snarky.DSL.SizedF

/-!
# Range checks built on the EndoScalar gate

Port of `Snarky.Circuit.Kimchi.RangeCheck`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/RangeCheck.purs): `toField` at 8
rows decomposes a 128-bit value across 16-bit rows, which doubles as a 128-bit range
check — cheaper than bit unpacking. `rangeCheck128` asserts the fit and discards the
decomposition; `lowest128Bits'` splits a field element into 128-bit halves,
range-checks the high half and — under `constrainLowBits` — the low one (OCaml
`squeeze_challenge` vs `squeeze_scalar`), pins the recombination, and returns the
low half.

One section per gadget: the definition, its soundness spec, its completeness law, and
then the definition is sealed `irreducible`. The pure split stays transparent — the
statements speak about it.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS's type-level `FieldSizeInBits f 255` constraint renders as no hypothesis: the
  gadget emits the same ops at any field, and the laws carry the width facts they
  need (`toField_spec`'s `4^64 = 2^128` budget, the split's faithfulness).
- PS's `SizedF.fromField` advice partiality (`unsafePartial fromJust`) is total
  here: the split representatives are casts of reduced naturals, in range by
  construction.
-/

namespace Snarky.Kimchi

open Snarky Std.Do

variable {F c : Type}

/-! ## The 128-bit range check -/

/-- 128-bit range assert (PS `rangeCheck128`): the `toField` decomposition at 8 rows
IS the check; the reconstruction result is discarded. -/
def rangeCheck128 [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (endo : FVar F) (v : SizedF 128 (FVar F)) :
    CircuitM F c PUnit := do
  let _ ← EndoScalar.toField (c := c) 8 v.val endo
  pure ⟨⟩

/-- **Soundness** (`rangeCheck128`): any satisfying valuation reads the operand as a
natural below `2^128` — the value-level `SizedF` contract. -/
theorem rangeCheck128_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (endo : FVar F) (v : SizedF 128 (FVar F)) :
    ⦃⌜True⌝⦄
    rangeCheck128 (c := Builder V (KimchiConstraint F)) endo v
    ⦃⇓ _ _ => ⌜∃ n : ℕ, n < 2 ^ 128 ∧ v.val.val V = (n : F)⌝⦄ := by
  have htf := EndoScalar.toField_spec (V := V) h2 h3 v.val endo
  simp only [rangeCheck128]
  mvcgen [htf]
  rename_i _ _ hr
  obtain ⟨n, hlt, hval, -⟩ := hr
  exact ⟨n, hlt, hval⟩

/-- **Completeness** (`rangeCheck128`): the honest run accepts on an operand that reads a
value inside the tagged width. -/
theorem rangeCheck128_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (endo : FVar F) (v : SizedF 128 (FVar F))
    (vv ev : F) (hfits : ToNat.toNat vv < 2 ^ 128) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => CircuitType.ReadsAs (val := F) st v.val vv ∧
        CircuitType.ReadsAs (val := F) st endo ev)
      (rangeCheck128 (c := KimchiConstraint F) endo v)
      (fun _ _ => True) := by
  simp only [rangeCheck128]
  complete_walk
  exact Complete.pure_of fun _ _ => trivial

attribute [irreducible] rangeCheck128

/-! ## The split

The low half of a field element, with the high half range-checked and — under
`constrainLowBits` — the low one too. `lowest128BitsPure` is the value the honest run
lands on, so it stays transparent. -/

/-- The pure split (PS `lowest128BitsPure`): the low half of the canonical
representative. -/
def lowest128BitsPure [Field F] [ToNat F] (x : F) : SizedF 128 F :=
  ⟨((ToNat.toNat x % 2 ^ 128 : ℕ) : F)⟩

/-- The split advice (PS's `exists` body): the value's canonical representative,
split at `2^128` — low half first, matching OCaml's `Typ.(field * field)`. -/
private def lowestWit [Field F] [ToNat F] (x : FVar F) : AsProver F (F × F) := do
  let xv ← AsProver.readCVar x
  pure (((ToNat.toNat xv % 2 ^ 128 : ℕ) : F), ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F))

/-- Extract the lowest 128 bits (PS `lowest128Bits'`; OCaml `lowest_128_bits`):
witness the split `x = lohi.val.1 + hi·2^128`, range-check `hi` and — under
`constrainLowBits` — `lo` via the `EndoScalar` decomposition, pin the
recombination, and return the low half. -/
def lowest128Bits' [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (constrainLowBits : Bool) (endo x : FVar F) :
    CircuitM F c (SizedF 128 (FVar F)) := do
  let lohi ← witness (val := UnChecked (F × F)) (.mk <$> lowestWit x)
  let _ ← EndoScalar.toField (c := c) 8 lohi.val.2 endo
  if constrainLowBits then
    let _ ← EndoScalar.toField (c := c) 8 lohi.val.1 endo
    pure ⟨⟩
  assertEqual x (CVar.add_ lohi.val.1 (CVar.scale_ ((2 : F) ^ 128) lohi.val.2))
  pure ⟨lohi.val.1⟩

/-- **Soundness** (`lowest128Bits'`): the operand reads as `lo + 2^128·hi` for the
returned low half and SOME high half below `2^128`; the low half is below `2^128` exactly
when `constrainLowBits` asked for it — OCaml's `squeeze_challenge` / `squeeze_scalar`
split. -/
theorem lowest128Bits'_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (constrainLowBits : Bool) (endo x : FVar F) :
    ⦃⌜True⌝⦄
    lowest128Bits' (c := Builder V (KimchiConstraint F)) constrainLowBits endo x
    ⦃⇓ r _ => ⌜∃ hiv : F,
      x.val V = r.val.val V + 2 ^ 128 * hiv ∧
      (∃ n : ℕ, n < 2 ^ 128 ∧ hiv = (n : F)) ∧
      (constrainLowBits = true →
        ∃ n : ℕ, n < 2 ^ 128 ∧ r.val.val V = (n : F))⌝⦄ := by
  have htf := fun (y : FVar F) => EndoScalar.toField_spec (V := V) h2 h3 y endo
  simp only [lowest128Bits']
  mvcgen [htf]
  · -- the low half is checked too
    rename_i _ lohi _ _ _ _ _ hhi _ _ hlo _ _ heq
    obtain ⟨nh, hnhlt, hnh, -⟩ := hhi
    obtain ⟨nl, hnllt, hnl, -⟩ := hlo
    exact ⟨lohi.val.2.val V, by rw [heq, CVar.val_add_, CVar.val_scale_],
      ⟨nh, hnhlt, hnh⟩, fun _ => ⟨nl, hnllt, hnl⟩⟩
  · -- only the high half is checked
    rename_i _ lohi _ _ _ hfalse _ hhi _ _ heq
    obtain ⟨nh, hnhlt, hnh, -⟩ := hhi
    exact ⟨lohi.val.2.val V, by rw [heq, CVar.val_add_, CVar.val_scale_],
      ⟨nh, hnhlt, hnh⟩, fun hc => absurd hc hfalse⟩

/-- **Completeness** (`lowest128Bits'`): the honest run accepts and the result reads the
pure split's low half. The high half fits by hypothesis, and both halves' representatives
must survive the cast — the round-trip the split's advice relies on. -/
theorem lowest128Bits'_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (constrainLowBits : Bool) (endo x : FVar F)
    (xv ev : F) (hhi : ToNat.toNat xv / 2 ^ 128 < 2 ^ 128)
    (hlo' : ToNat.toNat ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) = ToNat.toNat xv % 2 ^ 128)
    (hhi' : ToNat.toNat ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) = ToNat.toNat xv / 2 ^ 128) :
    Complete (F := F) (c := KimchiConstraint F)
      (fun st => CircuitType.ReadsAs (val := F) st x xv ∧ CircuitType.ReadsAs (val := F) st endo ev)
      (lowest128Bits' (c := KimchiConstraint F) constrainLowBits endo x)
      (fun r st' => CircuitType.ReadsAs (val := F) st' r.val (lowest128BitsPure xv).val) := by
  have hsplit : xv =
      ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) + 2 ^ 128 * ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) := by
    have hmd := Nat.mod_add_div (ToNat.toNat xv) (2 ^ 128)
    calc xv = ((ToNat.toNat xv : ℕ) : F) := (LawfulToNat.cast_toNat xv).symm
      _ = ((ToNat.toNat xv % 2 ^ 128 + 2 ^ 128 * (ToNat.toNat xv / 2 ^ 128) : ℕ) : F) := by
            rw [hmd]
      _ = _ := by push_cast; ring
  have hlolt : ToNat.toNat ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) < 2 ^ 128 := by
    rw [hlo']
    exact Nat.mod_lt _ (by positivity)
  have hhilt : ToNat.toNat ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) < 2 ^ 128 := by
    rw [hhi']
    exact hhi
  simp only [lowest128Bits']
  -- the split, in one witness
  refine Complete.seq (by complete_mono_tac)
    (Complete.imp
      (fun st h => by
        simp only [lowestWit, AsProver.map_eq, AsProver.bind_eq, AsProver.run_bind,
          AsProver.readCVar_run (CircuitType.scoped_fvar.mp h.1.1),
          CircuitType.reads_fvar.mp h.1.2, Except.bind]
        rfl)
      (fun _ _ h => h)
      (Complete.witness (UnChecked.mk <$> lowestWit x)
        (⟨(((ToNat.toNat xv % 2 ^ 128 : ℕ) : F),
          ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F))⟩ : UnChecked (F × F))
        (by simp)))
    fun lohi => ?_
  obtain ⟨⟨lo, hi⟩⟩ := lohi
  -- the split's halves, componentwise
  have hw : ∀ {st : ProverState F},
      CircuitType.ReadsAs (val := UnChecked (F × F)) st ⟨(lo, hi)⟩
          ⟨(((ToNat.toNat xv % 2 ^ 128 : ℕ) : F),
            ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F))⟩ →
        CircuitType.ReadsAs (val := F) st lo ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) ∧
        CircuitType.ReadsAs (val := F) st hi ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) := by
    intro st h
    have hsc := h.1
    have hrd := h.2
    simp only [CircuitType.scoped_unchecked, CircuitType.scoped_prod,
      CircuitType.scoped_fvar] at hsc
    simp only [CircuitType.reads_unchecked, CircuitType.reads_prod,
      CircuitType.reads_fvar] at hrd
    exact ⟨⟨CircuitType.scoped_fvar.mpr hsc.1, CircuitType.reads_fvar.mpr hrd.1⟩,
      ⟨CircuitType.scoped_fvar.mpr hsc.2, CircuitType.reads_fvar.mpr hrd.2⟩⟩
  -- the halves and the recombination, as search rules for the walk
  have hloR := fun {st : ProverState F} h => (hw (st := st) h).1
  have hhiR := fun {st : ProverState F} h => (hw (st := st) h).2
  have hxread : ∀ {st : ProverState F},
      CircuitType.ReadsAs (val := F) st lo ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) →
      CircuitType.ReadsAs (val := F) st hi ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) →
      CircuitType.ReadsAs (val := F) st
        (CVar.add_ lo (CVar.scale_ ((2 : F) ^ 128) hi)) xv :=
    fun hl hh => ⟨CircuitType.scoped_fvar.mpr
        (CVar.Scoped.add_ (CircuitType.scoped_fvar.mp hl.1)
          (CVar.Scoped.scale_ (CircuitType.scoped_fvar.mp hh.1))),
      CircuitType.reads_fvar.mpr (by
        rw [CVar.val_add_, CVar.val_scale_, CircuitType.reads_fvar.mp hl.2,
          CircuitType.reads_fvar.mp hh.2]
        exact hsplit.symm)⟩
  -- range-check the high half; the walk then stops at the statement-position `if`
  complete_walk
  by_cases hc : constrainLowBits = true
  · simp only [hc, if_true]
    complete_walk
    exact Complete.pure_of fun _ h => hloR h.1.1.1.1.2
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, if_false]
    complete_walk
    exact Complete.pure_of fun _ h => hloR h.1.1.1.2

attribute [irreducible] lowestWit lowest128Bits'

/-! ## `lowest128Bits`

OCaml's `squeeze_challenge` flavour: `lowest128Bits'` with the low half checked, so its
laws are the section above's at `constrainLowBits := true`. -/

/-- OCaml `squeeze_challenge`'s flavor: both halves checked (PS `lowest128Bits`). -/
def lowest128Bits [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [KimchiSystem F c] (endo x : FVar F) : CircuitM F c (SizedF 128 (FVar F)) :=
  lowest128Bits' true endo x

attribute [irreducible] lowest128Bits

end Snarky.Kimchi
