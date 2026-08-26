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
  need (`nReconstruct_lt`'s `4^64 = 2^128` budget, the split's faithfulness).
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

open Kimchi.Gate.EndoScalar (nReconstruct_lt) in
/-- **Soundness** (`rangeCheck128`): any satisfying valuation reads the operand as a
natural below `2^128` — the value-level `SizedF` contract. -/
theorem rangeCheck128_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (endo : FVar F) (v : SizedF 128 (FVar F)) :
    ⦃⌜True⌝⦄
    rangeCheck128 (c := Builder V (KimchiConstraint F)) endo v
    ⦃⇓ _ _ => ⌜∃ n : ℕ, n < 2 ^ 128 ∧ v.val.val V = (n : F)⌝⦄ := by
  have htf := EndoScalar.toField_spec (V := V) h2 h3 8 v.val endo
  simp only [rangeCheck128]
  mvcgen [htf]
  rename_i _ _ hr
  obtain ⟨crumbs, hvalid, hlen, -, hval⟩ := hr
  obtain ⟨n, hlt, hcast⟩ := nReconstruct_lt h2 h3 crumbs hvalid
  refine ⟨n, ?_, by rw [hval, hcast]⟩
  calc n < 4 ^ crumbs.length := hlt
    _ = 2 ^ 128 := by rw [hlen]; norm_num

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
  intro st hpre
  obtain ⟨r, st₁, hrun, hsat, -⟩ :=
    EndoScalar.toField_complete h2 h3 8 v.val endo vv ev (by norm_num at hfits ⊢; exact hfits)
      st hpre
  exact ⟨⟨⟩, st₁, hrun.bind rfl, fun hnv hle =>
    Sat.bind hrun (hsat hnv hle) Sat.pure, trivial⟩

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

open Kimchi.Gate.EndoScalar (nReconstruct_lt) in
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
  have htf := fun (y : FVar F) => EndoScalar.toField_spec (V := V) h2 h3 8 y endo
  have hrange : ∀ (y : FVar F) (crumbs : List F),
      (∀ z ∈ crumbs, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3) → crumbs.length = 8 * 8 →
      y.val V = Kimchi.Gate.EndoScalar.nReconstruct crumbs →
      ∃ n : ℕ, n < 2 ^ 128 ∧ y.val V = (n : F) := by
    intro y crumbs hvalid hlen hval
    obtain ⟨n, hlt, hcast⟩ := nReconstruct_lt h2 h3 crumbs hvalid
    exact ⟨n, by calc n < 4 ^ crumbs.length := hlt
                   _ = 2 ^ 128 := by rw [hlen]; norm_num, by rw [hval, hcast]⟩
  simp only [lowest128Bits']
  mvcgen [htf]
  · -- the low half is checked too
    rename_i _ lohi _ _ _ _ _ hhi _ _ hlo _ _ heq
    obtain ⟨ch, hvh, hlh, -, hnh⟩ := hhi
    obtain ⟨cl, hvl, hll, -, hnl⟩ := hlo
    exact ⟨lohi.val.2.val V, by rw [heq, CVar.val_add_, CVar.val_scale_],
      hrange _ ch hvh hlh hnh, fun _ => hrange _ cl hvl hll hnl⟩
  · -- only the high half is checked
    rename_i _ lohi _ _ _ hfalse _ hhi _ _ heq
    obtain ⟨ch, hvh, hlh, -, hnh⟩ := hhi
    exact ⟨lohi.val.2.val V, by rw [heq, CVar.val_add_, CVar.val_scale_],
      hrange _ ch hvh hlh hnh, fun hc => absurd hc hfalse⟩

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
  rintro st ⟨hRx, hRe⟩
  have hRx' := hRx
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar] at hRx'
  obtain ⟨hscx, hvx⟩ := hRx'
  have hsplit : xv =
      ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) + 2 ^ 128 * ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) := by
    have hmd := Nat.mod_add_div (ToNat.toNat xv) (2 ^ 128)
    calc xv = ((ToNat.toNat xv : ℕ) : F) := (LawfulToNat.cast_toNat xv).symm
      _ = ((ToNat.toNat xv % 2 ^ 128 + 2 ^ 128 * (ToNat.toNat xv / 2 ^ 128) : ℕ) : F) := by
            rw [hmd]
      _ = _ := by push_cast; ring
  have hlolt : ToNat.toNat ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) < 4 ^ (8 * 8) := by
    rw [hlo']
    have hm : ToNat.toNat xv % 2 ^ 128 < 2 ^ 128 := Nat.mod_lt _ (by positivity)
    norm_num at hm ⊢
    exact hm
  have hhilt : ToNat.toNat ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) < 4 ^ (8 * 8) := by
    rw [hhi']
    norm_num at hhi ⊢
    exact hhi
  simp only [lowest128Bits']
  obtain ⟨lohi, st₁, hrun₁, hsat₁, hnv₁, hle₁, hsc₁, hrd₁⟩ :=
    witness_complete (c := KimchiConstraint F) (val := UnChecked (F × F))
      (UnChecked.mk <$> lowestWit x) (st := st)
      (v := ⟨(((ToNat.toNat xv % 2 ^ 128 : ℕ) : F), ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F))⟩)
      (by
        simp only [lowestWit, AsProver.map_eq, AsProver.bind_eq, AsProver.run_bind,
          AsProver.readCVar_run hscx, hvx, Except.bind]
        rfl)
  obtain ⟨⟨lo, hi⟩⟩ := lohi
  simp only [CircuitType.scoped_unchecked, CircuitType.scoped_prod,
    CircuitType.scoped_fvar] at hsc₁
  simp only [CircuitType.reads_unchecked, CircuitType.reads_prod,
    CircuitType.reads_fvar] at hrd₁
  have hRlo : CircuitType.ReadsAs (val := F) st₁ lo ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) :=
    ⟨CircuitType.scoped_fvar.mpr hsc₁.1, CircuitType.reads_fvar.mpr hrd₁.1⟩
  have hRhi : CircuitType.ReadsAs (val := F) st₁ hi ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) :=
    ⟨CircuitType.scoped_fvar.mpr hsc₁.2, CircuitType.reads_fvar.mpr hrd₁.2⟩
  obtain ⟨rhi, st₂, hrun₂, hsat₂, -⟩ :=
    EndoScalar.toField_complete h2 h3 8 hi endo ((ToNat.toNat xv / 2 ^ 128 : ℕ) : F) ev hhilt st₁
      ⟨hRhi, hRe.mono hnv₁ hle₁⟩
  have hle₂ := hrun₂.le
  have hnv₂ := hrun₂.nv_le
  -- the pin, at any table past the split
  have hpin : ∀ stk : ProverState F, st₁.env.Le stk.env →
      x.val stk.env.get = (CVar.add_ lo (CVar.scale_ ((2 : F) ^ 128) hi)).val stk.env.get := by
    intro stk hlek
    rw [CVar.val_add_, CVar.val_scale_,
      CVar.val_of_le hlek (CircuitType.scoped_fvar.mp hRlo.1),
      CVar.val_of_le hlek (CircuitType.scoped_fvar.mp hRhi.1),
      CircuitType.reads_fvar.mp hRlo.2, CircuitType.reads_fvar.mp hRhi.2,
      CVar.val_of_le (hle₁.trans hlek) hscx, hvx]
    exact hsplit
  by_cases hc : constrainLowBits = true
  · simp only [hc, if_true]
    obtain ⟨rlo, st₃, hrun₃, hsat₃, -⟩ :=
      EndoScalar.toField_complete h2 h3 8 lo endo ((ToNat.toNat xv % 2 ^ 128 : ℕ) : F) ev hlolt st₂
        ⟨hRlo.mono hnv₂ hle₂, hRe.mono (Nat.le_trans hnv₁ hnv₂) (hle₁.trans hle₂)⟩
    have hle₃ := hrun₃.le
    have hnv₃ := hrun₃.nv_le
    obtain ⟨u, st₄, hrun₄, hsat₄, -⟩ :=
      assertEqual_complete (c := KimchiConstraint F) x
        (CVar.add_ lo (CVar.scale_ ((2 : F) ^ 128) hi))
        (x.val st₃.env.get) st₃
        ⟨⟨CircuitType.scoped_fvar.mpr (hscx.mono (Nat.le_trans hnv₁
            (Nat.le_trans hnv₂ hnv₃))), CircuitType.reads_fvar.mpr rfl⟩,
          ⟨CircuitType.scoped_fvar.mpr (CVar.Scoped.add_
              ((CircuitType.scoped_fvar.mp hRlo.1).mono (Nat.le_trans hnv₂ hnv₃))
              (CVar.Scoped.scale_
                ((CircuitType.scoped_fvar.mp hRhi.1).mono (Nat.le_trans hnv₂ hnv₃)))),
            CircuitType.reads_fvar.mpr (hpin st₃ (hle₂.trans hle₃)).symm⟩⟩
    have hunit₃ : Runs (pure ⟨⟩ : CircuitM F (KimchiConstraint F) PUnit) st₃ ⟨⟩ st₃ := rfl
    refine ⟨⟨lo⟩, st₄, hrun₁.bind (hrun₂.bind (hrun₃.bind
        (Runs.bind hunit₃ (hrun₄.bind rfl)))),
      fun hnv hle => Sat.bind hrun₁ (hsat₁ ?_ ?_) (Sat.bind hrun₂ (hsat₂ ?_ ?_)
        (Sat.bind hrun₃ (hsat₃ ?_ ?_)
          (Sat.bind hunit₃ (by simp [Sat, build])
            (Sat.bind hrun₄ (hsat₄ hnv hle) Sat.pure)))), ?_⟩
    · exact Nat.le_trans (Nat.le_trans hnv₂ (Nat.le_trans hnv₃ hrun₄.nv_le)) hnv
    · exact ((hle₂.trans hle₃).trans hrun₄.le).trans hle
    · exact Nat.le_trans (Nat.le_trans hnv₃ hrun₄.nv_le) hnv
    · exact (hle₃.trans hrun₄.le).trans hle
    · exact Nat.le_trans hrun₄.nv_le hnv
    · exact hrun₄.le.trans hle
    · exact hRlo.mono (Nat.le_trans hnv₂ (Nat.le_trans hnv₃ hrun₄.nv_le))
        ((hle₂.trans hle₃).trans hrun₄.le)
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, if_false]
    obtain ⟨u, st₃, hrun₃, hsat₃, -⟩ :=
      assertEqual_complete (c := KimchiConstraint F) x
        (CVar.add_ lo (CVar.scale_ ((2 : F) ^ 128) hi))
        (x.val st₂.env.get) st₂
        ⟨⟨CircuitType.scoped_fvar.mpr (hscx.mono (Nat.le_trans hnv₁ hnv₂)),
            CircuitType.reads_fvar.mpr rfl⟩,
          ⟨CircuitType.scoped_fvar.mpr (CVar.Scoped.add_
              ((CircuitType.scoped_fvar.mp hRlo.1).mono hnv₂)
              (CVar.Scoped.scale_ ((CircuitType.scoped_fvar.mp hRhi.1).mono hnv₂))),
            CircuitType.reads_fvar.mpr (hpin st₂ hle₂).symm⟩⟩
    have hunit₂ : Runs (pure ⟨⟩ : CircuitM F (KimchiConstraint F) PUnit) st₂ ⟨⟩ st₂ := rfl
    refine ⟨⟨lo⟩, st₃,
      hrun₁.bind (hrun₂.bind (Runs.bind hunit₂ (hrun₃.bind rfl))),
      fun hnv hle => Sat.bind hrun₁ (hsat₁ ?_ ?_) (Sat.bind hrun₂ (hsat₂ ?_ ?_)
        (Sat.bind hunit₂ (by simp [Sat, build])
          (Sat.bind hrun₃ (hsat₃ hnv hle) Sat.pure))), ?_⟩
    · exact Nat.le_trans (Nat.le_trans hnv₂ hrun₃.nv_le) hnv
    · exact (hle₂.trans hrun₃.le).trans hle
    · exact Nat.le_trans hrun₃.nv_le hnv
    · exact hrun₃.le.trans hle
    · exact hRlo.mono (Nat.le_trans hnv₂ hrun₃.nv_le) (hle₂.trans hrun₃.le)

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
