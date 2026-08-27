import Mathlib.Data.List.Forall2
import Snarky.DSL.Assert
import Snarky.DSL.Bits
import Snarky.DSL.Boolean

/-!
# The canonical bit decomposition

Port of OCaml `Field.Checked.unpack_full` / `lt_bitstring_value` (snark0.ml, the base-DSL
checked runtime). Plain `unpack` (snarky's `Snarky/DSL/Bits.lean`) pins the bits' weighted
sum to the operand only modulo the field, so any representative's decomposition satisfies
its rows; locking the decomposition to the canonical representative takes a further
comparison against the modulus.

`modBitsMsb` is the modulus as an MSB-first bit pattern; `ltBitstringValue` compares an
MSB-first bit vector against it, descending to the least significant bit and combining on
the way back out: at a `1` bit of the pattern the operand may drop below (`or`), at a `0`
bit it must stay equal (`and`). `ltPure` is the comparison's value-level mirror, and
`ltPure_iff_lt` is where the comparison becomes an inequality on `natVal`.
`assertBitsBelow` packages the comparison with its assertion — the lock itself, payable
on fresh bits or on bits a consumer already holds.

Deviation from the PS original (`packages/schnorr/src/Snarky/Circuit/Schnorr/
UnpackFull.purs`): PS builds the comparison as a `Binary` tree, regroups runs into N-ary
nodes evaluated with the sum-based `allBools`/`anyBools` constraint-savers, and
short-circuits the last one and two bits. This is the uniform binary recursion — the same
value, more rows.
-/

namespace Schnorr

open Snarky

variable {F c : Type}

/-! ## The value layer -/

/-- MSB-first bit decomposition of `m` at width `n` (PS `modulusBitsMsb`) — the reversal
of `unpackPure`'s digits, at a natural rather than a field element. -/
def modBitsMsb (m n : ℕ) : List Bool :=
  (List.ofFn fun i : Fin n => m.testBit i.val).reverse

/-- The pattern has the requested width. -/
theorem modBitsMsb_length (m n : ℕ) : (modBitsMsb m n).length = n := by
  simp [modBitsMsb]

/-- The pattern's value is the modulus it was cut from. -/
theorem natVal_reverse_modBitsMsb {m n : ℕ} (h : m < 2 ^ n) :
    natVal (modBitsMsb m n).reverse = m := by
  rw [modBitsMsb, List.reverse_reverse]
  exact natVal_testBit n m h

/-- The comparison's value-level mirror: MSB-first `xs < ys`, `false` on any length
mismatch. -/
def ltPure : List Bool → List Bool → Bool
  | x :: xs, true :: ys => !x || ltPure xs ys
  | x :: xs, false :: ys => !x && ltPure xs ys
  | _, _ => false

/-- `ltPure` decides the value comparison on equal lengths. -/
theorem ltPure_iff_lt : ∀ {xs ys : List Bool}, xs.length = ys.length →
    (ltPure xs ys = true ↔ natVal xs.reverse < natVal ys.reverse) := by
  intro xs
  induction xs with
  | nil =>
    intro ys hlen
    rw [List.length_nil] at hlen
    rw [List.length_eq_zero_iff.mp hlen.symm]
    simp [ltPure, natVal]
  | cons x xs ih =>
    intro ys hlen
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hx := natVal_lt xs.reverse
      have hy := natVal_lt ys.reverse
      rw [List.length_reverse] at hx hy
      rw [hlen] at hx
      have hih := ih hlen
      cases x <;> cases y <;>
        simp only [ltPure, List.reverse_cons, natVal_append_singleton,
          List.length_reverse, hlen, Bool.toNat_false, Bool.toNat_true,
          Bool.not_false, Bool.not_true, Bool.true_or, Bool.false_or, Bool.true_and,
          Bool.false_and, hih, false_iff, true_iff, Bool.false_eq_true] <;>
        omega

/-! ## The comparison -/

/-- `xs < ys` for an MSB-first bit vector against a constant pattern (OCaml
`lt_bitstring_value`). -/
def ltBitstringValue [Field F] [DecidableEq F] [BasicSystem F c] :
    List (BoolVar F) → List Bool → CircuitM F c (BoolVar F)
  | x :: xs, true :: ys => do
    let r ← ltBitstringValue xs ys
    Snarky.or (Snarky.not x) r
  | x :: xs, false :: ys => do
    let r ← ltBitstringValue xs ys
    Snarky.and (Snarky.not x) r
  | _, _ => pure false_

/-- Outside the two matching shapes the comparison is `false`: the pattern is exhausted,
or the operands are and with them the bits they read as. -/
private theorem ltPure_eq_false {α : Type} {R : α → Bool → Prop} {xs : List α}
    {ys bs : List Bool}
    (h1 : ∀ (x : α) (xs' : List α) (ys' : List Bool), xs = x :: xs' → ys = true :: ys' → False)
    (h2 : ∀ (x : α) (xs' : List α) (ys' : List Bool), xs = x :: xs' → ys = false :: ys' → False)
    (hfa : List.Forall₂ R xs bs) : ltPure bs ys = false := by
  cases hfa with
  | nil => cases ys <;> rfl
  | cons _ _ =>
    rename_i x _ xs' _ _ _
    cases ys with
    | nil => rfl
    | cons y ys' =>
      cases y
      · exact (h2 x xs' ys' rfl rfl).elim
      · exact (h1 x xs' ys' rfl rfl).elim

open Std.Do in
/-- The comparison reads as `ltPure` of the operands' bits against the pattern. -/
@[spec] theorem ltBitstringValue_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (xs : List (BoolVar F)) (ys : List Bool) :
    ⦃⌜True⌝⦄
    ltBitstringValue (c := Builder V c) xs ys
    ⦃⇓ r _ => ⌜∀ bs : List Bool,
        List.Forall₂ (fun (x : BoolVar F) (b : Bool) => (↑x : CVar F).val V = bit b) xs bs →
        (↑r : CVar F).val V = bit (ltPure bs ys)⌝⦄ := by
  induction xs, ys using ltBitstringValue.induct with
  | case1 x xs ys ih =>
    simp only [ltBitstringValue]
    mvcgen [ih]
    rename_i _ _ _ hr _ _
    intro hor bs hbs
    cases hbs with
    | cons hx htl =>
      rename_i b bs'
      rw [hor (!b) (ltPure bs' ys) (not_val hx) (hr bs' htl)]
      simp [ltPure]
  | case2 x xs ys ih =>
    simp only [ltBitstringValue]
    mvcgen [ih]
    rename_i _ _ _ hr _ _
    intro hand bs hbs
    cases hbs with
    | cons hx htl =>
      rename_i b bs'
      rw [hand (!b) (ltPure bs' ys) (not_val hx) (hr bs' htl)]
      simp [ltPure]
  | case3 xs ys h1 h2 =>
    simp only [ltBitstringValue]
    mvcgen
    intro bs hbs
    rw [ltPure_eq_false h1 h2 hbs]
    simp [bit]

/-- The comparison's completeness law: on operands reading as `bs`, the run succeeds and
the result reads as `ltPure bs ys`. -/
theorem ltBitstringValue_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c]
    (xs : List (BoolVar F)) (ys bs : List Bool) :
    Complete (F := F) (c := c)
      (fun st => List.Forall₂ (fun (x : BoolVar F) (b : Bool) =>
        CircuitType.ReadsAs (val := Bool) st x b) xs bs)
      (ltBitstringValue (c := c) xs ys)
      (fun r st' => CircuitType.ReadsAs (val := Bool) st' r (ltPure bs ys)) := by
  induction xs, ys using ltBitstringValue.induct generalizing bs with
  | case1 x xs ys ih =>
    intro st hfa
    simp only [ltBitstringValue]
    cases hfa with
    | cons hx htl =>
      rename_i b bs'
      obtain ⟨r, st₁, hrun₁, hsat₁, hr⟩ := ih bs' st htl
      have hx₁ := hx.mono hrun₁.nv_le hrun₁.le
      obtain ⟨out, st₂, hrun₂, hsat₂, hout⟩ :=
        Snarky.or_complete (c := c) (Snarky.not x) r (!b) (ltPure bs' ys) st₁
          ⟨⟨CircuitType.scoped_boolVar.mpr
              (not_scoped (CircuitType.scoped_boolVar.mp hx₁.1)),
            CircuitType.reads_boolVar.mpr
              (not_val (CircuitType.reads_boolVar.mp hx₁.2))⟩, hr⟩
      refine ⟨out, st₂, hrun₁.bind hrun₂, ?_, ?_⟩
      · intro stf hnv hle
        exact Sat.bind hrun₁ (hsat₁ (Nat.le_trans hrun₂.nv_le hnv) (hrun₂.le.trans hle))
          (hsat₂ hnv hle)
      · simpa [ltPure] using hout
  | case2 x xs ys ih =>
    intro st hfa
    simp only [ltBitstringValue]
    cases hfa with
    | cons hx htl =>
      rename_i b bs'
      obtain ⟨r, st₁, hrun₁, hsat₁, hr⟩ := ih bs' st htl
      have hx₁ := hx.mono hrun₁.nv_le hrun₁.le
      obtain ⟨out, st₂, hrun₂, hsat₂, hout⟩ :=
        Snarky.and_complete (c := c) (Snarky.not x) r (!b) (ltPure bs' ys) st₁
          ⟨⟨CircuitType.scoped_boolVar.mpr
              (not_scoped (CircuitType.scoped_boolVar.mp hx₁.1)),
            CircuitType.reads_boolVar.mpr
              (not_val (CircuitType.reads_boolVar.mp hx₁.2))⟩, hr⟩
      refine ⟨out, st₂, hrun₁.bind hrun₂, ?_, ?_⟩
      · intro stf hnv hle
        exact Sat.bind hrun₁ (hsat₁ (Nat.le_trans hrun₂.nv_le hnv) (hrun₂.le.trans hle))
          (hsat₂ hnv hle)
      · simpa [ltPure] using hout
  | case3 xs ys h1 h2 =>
    intro st hfa
    simp only [ltBitstringValue]
    refine ⟨false_, st, rfl, fun _ _ => Sat.pure, ?_⟩
    rw [ltPure_eq_false h1 h2 hfa]
    exact ⟨CircuitType.scoped_boolVar.mpr (false_scoped st),
      CircuitType.reads_boolVar.mpr (by simp [bit])⟩

attribute [irreducible] ltBitstringValue

/-! ## The lock -/

/-- Assert an LSB-first bit list's ℕ value lies strictly below `m` at width `n` — the
canonicity lock as one gadget (the `lt_bitstring_value …; assert` composition).
`unpackFull` pays it on fresh bits; a consumer holding bits already pays it on those. -/
def assertBitsBelow [Field F] [DecidableEq F] [BasicSystem F c]
    (m n : ℕ) (bits : List (BoolVar F)) : CircuitM F c PUnit := do
  let lt ← ltBitstringValue bits.reverse (modBitsMsb m n)
  Snarky.assert lt

open Std.Do in
/-- The lock's rows force the operands' bits to a value strictly below `m`. -/
@[spec] theorem assertBitsBelow_spec {V : Valuation F} [Field F] [DecidableEq F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (m n : ℕ) (hm : m < 2 ^ n) (bits : List (BoolVar F)) (hlen : bits.length = n) :
    ⦃⌜True⌝⦄
    assertBitsBelow (c := Builder V c) m n bits
    ⦃⇓ _ _ => ⌜∀ bs : List Bool,
        List.Forall₂ (fun (x : BoolVar F) (b : Bool) => (↑x : CVar F).val V = bit b) bits bs →
        natVal bs < m⌝⦄ := by
  simp only [assertBitsBelow]
  mvcgen
  rename_i _ hlt _ _
  intro hassert bs hfa
  have hltv := hlt bs.reverse (List.forall₂_reverse_iff.mpr hfa)
  rw [hassert] at hltv
  have hltrue : ltPure bs.reverse (modBitsMsb m n) = true := by
    by_contra h
    rw [Bool.not_eq_true] at h
    rw [h] at hltv
    simp [bit] at hltv
  have hcmp := (ltPure_iff_lt (by
    rw [List.length_reverse, modBitsMsb_length, ← hfa.length_eq, hlen])).mp hltrue
  rwa [natVal_reverse_modBitsMsb hm, List.reverse_reverse] at hcmp

/-- The lock's completeness law: bits reading as a value below `m` satisfy its rows. -/
theorem assertBitsBelow_complete [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c]
    (m n : ℕ) (hm : m < 2 ^ n) (bits : List (BoolVar F))
    (bs : List Bool) (hbs : bs.length = n) (hval : natVal bs < m) :
    Complete (F := F) (c := c)
      (fun st => List.Forall₂ (fun (x : BoolVar F) (b : Bool) =>
        CircuitType.ReadsAs (val := Bool) st x b) bits bs)
      (assertBitsBelow (c := c) m n bits) (fun _ _ => True) := by
  intro st hfa
  simp only [assertBitsBelow]
  obtain ⟨lt, st₁, hrun₁, hsat₁, hlt⟩ :=
    ltBitstringValue_complete (c := c) bits.reverse (modBitsMsb m n) bs.reverse st
      (List.forall₂_reverse_iff.mpr hfa)
  have hltrue : ltPure bs.reverse (modBitsMsb m n) = true :=
    (ltPure_iff_lt (by rw [List.length_reverse, modBitsMsb_length, hbs])).mpr
      (by rwa [natVal_reverse_modBitsMsb hm, List.reverse_reverse])
  rw [hltrue] at hlt
  obtain ⟨_, st₂, hrun₂, hsat₂, -⟩ := Snarky.assert_complete (c := c) lt st₁ hlt
  refine ⟨PUnit.unit, st₂, hrun₁.bind hrun₂, ?_, trivial⟩
  intro stf hnv hle
  exact Sat.bind hrun₁ (hsat₁ (Nat.le_trans hrun₂.nv_le hnv) (hrun₂.le.trans hle))
    (hsat₂ hnv hle)

attribute [irreducible] assertBitsBelow

/-! ## The canonical unpack -/

/-- `unpack_full` (OCaml `Field.Checked.unpack_full`): decompose into `n` LSB-first bits
with the canonical `< m` lock. -/
def unpackFull [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    (m n : ℕ) (v : FVar F) : CircuitM F c (Vector (BoolVar F) n) := do
  let bits ← unpack v n
  assertBitsBelow m n bits.toList
  pure bits

open Std.Do in
/-- `unpackFull`'s rows force bits whose ℕ value casts to the operand's reading AND lies
below `m` — the canonicity plain `unpack` lacks: at `m` the reader's `card`, the value IS
the reading's representative. -/
@[spec] theorem unpackFull_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (m n : ℕ) (hm : m < 2 ^ n) (v : FVar F) :
    ⦃⌜True⌝⦄
    unpackFull (c := Builder V c) m n v
    ⦃⇓ r _ => ⌜∃ bs : Vector Bool n,
        (∀ i (hi : i < n), (↑r[i] : CVar F).val V = bit bs[i]) ∧
        ((natVal bs.toList : ℕ) : F) = v.val V ∧ natVal bs.toList < m⌝⦄ := by
  simp only [unpackFull]
  mvcgen
  case vc2.hlen => simp
  rename_i _ _ _ hbits _ _ hlock
  obtain ⟨bs, hread, hsum⟩ := hbits
  refine ⟨bs, hread, by rw [← packPure_natVal]; exact hsum, hlock bs.toList ?_⟩
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h1 h2 => ?_⟩
  simp only [List.get_eq_getElem, Vector.getElem_toList]
  exact hread i (by simpa using h1)

/-- `unpackFull`'s completeness law: on a representative that fits the width and lies
below `m` the run succeeds, and the bits are the operand's binary digits. -/
theorem unpackFull_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (m n : ℕ) (hm : m < 2 ^ n) (v : FVar F) (vv : F)
    (hfit : ToNat.toNat vv < 2 ^ n) (hbound : ToNat.toNat vv < m) :
    Complete (F := F) (c := c) (fun st => CircuitType.ReadsAs (val := F) st v vv)
      (unpackFull (c := c) m n v)
      (fun r st' => CircuitType.ReadsAs (val := Vector Bool n) st' r (unpackPure vv n)) := by
  intro st hv
  simp only [unpackFull]
  obtain ⟨bits, st₁, hrun₁, hsat₁, hbits⟩ := unpack_complete (c := c) v vv n hfit st hv
  have hfa : List.Forall₂ (fun (x : BoolVar F) (b : Bool) =>
      CircuitType.ReadsAs (val := Bool) st₁ x b) bits.toList (unpackPure vv n).toList := by
    obtain ⟨hsc, hrd⟩ := hbits
    rw [CircuitType.scoped_vector] at hsc
    rw [CircuitType.reads_vector] at hrd
    rw [List.forall₂_iff_get]
    refine ⟨by simp, fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, Vector.getElem_toList]
    exact ⟨hsc i (by simpa using h1), hrd i (by simpa using h1)⟩
  obtain ⟨_, st₂, hrun₂, hsat₂, -⟩ :=
    assertBitsBelow_complete (c := c) m n hm bits.toList (unpackPure vv n).toList (by simp)
      (by rwa [natVal_unpackPure hfit]) st₁ hfa
  refine ⟨bits, st₂, hrun₁.bind (hrun₂.bind rfl), ?_, hbits.mono hrun₂.nv_le hrun₂.le⟩
  intro stf hnv hle
  exact Sat.bind hrun₁ (hsat₁ (Nat.le_trans hrun₂.nv_le hnv) (hrun₂.le.trans hle))
    (Sat.bind hrun₂ (hsat₂ hnv hle) Sat.pure)

attribute [irreducible] unpackFull

end Schnorr
