import Mathlib.Data.List.Forall2
import Snarky.Circuit.DSL.Bits
import Snarky.Circuit.DSL.Assert

/-!
# `unpack_full` — the canonical bit decomposition

Port of OCaml `Field.Checked.unpack_full` / `lt_bitstring_value` (snark0.ml, the
base-DSL checked runtime), by way of the PS transcription
`packages/schnorr/src/Snarky/Circuit/Schnorr/UnpackFull.purs`. Plain `unpack` pins
the bits' weighted sum to the operand only mod the field — any representative's
decomposition satisfies it. `unpackFull` adds the strict bits-below-the-modulus
comparison, locking the decomposition to the canonical representative.

`ltBitstringValue` compares an MSB-first bit vector against a constant pattern,
LSB-outward: at a `1` bit of the pattern the operand may drop below (`or`), at a `0`
bit it must stay equal (`and`). `ltPure` is its pure mirror: the MSB-first lists
compare as `natLsbVal` of their reversals.

Deviations from the PS original (Lean-only consumer; no constraint diffing):
- PS builds the comparison as a `Binary` tree, regroups runs into N-ary nodes evaluated
  with the sum-based `allBools`/`anyBools` constraint-savers, and short-circuits the
  last one and two bits. The port emits the uniform binary recursion — the same value,
  more rows.
- The modulus arrives as an explicit bound `m` (PS reads it from the `PrimeField`
  instance); the consumer pins it to the field's cardinality.
-/

namespace Snarky

variable {F c : Type}

/-! ## The value layer -/

/-- The comparison's pure mirror: MSB-first `xs < ys` (`false` on any length
mismatch). -/
def ltPure : List Bool → List Bool → Bool
  | x :: xs, true :: ys => !x || ltPure xs ys
  | x :: xs, false :: ys => !x && ltPure xs ys
  | _, _ => false

/-- `ltPure` decides the value comparison on equal lengths. -/
theorem ltPure_iff_lt : ∀ {xs ys : List Bool}, xs.length = ys.length →
    (ltPure xs ys = true ↔ natLsbVal xs.reverse < natLsbVal ys.reverse) := by
  intro xs
  induction xs with
  | nil =>
    intro ys hlen
    rw [List.length_nil] at hlen
    rw [(List.length_eq_zero_iff).mp hlen.symm]
    simp [ltPure, natLsbVal]
  | cons x xs ih =>
    intro ys hlen
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hx := natLsbVal_lt xs.reverse
      have hy := natLsbVal_lt ys.reverse
      rw [List.length_reverse] at hx hy
      rw [hlen] at hx
      have hih := ih hlen
      cases x <;> cases y <;>
        simp only [ltPure, List.reverse_cons, natLsbVal_append_singleton,
          List.length_reverse, hlen, Bool.toNat_false, Bool.toNat_true,
          Bool.not_false, Bool.not_true, Bool.true_or, Bool.false_or, Bool.true_and,
          Bool.false_and, hih, false_iff, true_iff, Bool.false_eq_true] <;>
        omega

/-- MSB-first bit decomposition of `m` at width `n` (PS `modulusBitsMsb`). -/
def modBitsMsb (m n : ℕ) : List Bool :=
  ((List.range n).map m.testBit).reverse

/-- The pattern has the requested width. -/
theorem modBitsMsb_length (m n : ℕ) : (modBitsMsb m n).length = n := by
  simp [modBitsMsb]

/-- The modulus pattern's value is the modulus. -/
theorem natLsbVal_reverse_modBitsMsb {m n : ℕ} (h : m < 2 ^ n) :
    natLsbVal (modBitsMsb m n).reverse = m := by
  rw [modBitsMsb, List.reverse_reverse, natLsbVal_testBit_range h]

/-! ## The gadgets -/

/-- `xs < ys` for an MSB-first bit vector against a constant pattern (OCaml
`lt_bitstring_value`; see the module docstring for the emitted-constraint
deviation). -/
def ltBitstringValue [Field F] [DecidableEq F] [BasicSystem F c] :
    List (BoolVar F) → List Bool → CircuitM F c (BoolVar F)
  | x :: xs, true :: ys => do
    let r ← ltBitstringValue xs ys
    Snarky.or (Snarky.not x) r
  | x :: xs, false :: ys => do
    let r ← ltBitstringValue xs ys
    Snarky.and (Snarky.not x) r
  | _, _ => pure false_

/-- Assert an LSB-first bit list's ℕ value lies strictly below `m` at width `n` — the
canonicity lock as one gadget (the `lt_bitstring_value …; assert` composition).
`unpackFull` pays it on fresh bits; a ladder consumer pays it on bits it already
holds. -/
def assertBitsBelow [Field F] [DecidableEq F] [BasicSystem F c]
    (m n : ℕ) (bits : List (BoolVar F)) : CircuitM F c PUnit := do
  let lt ← ltBitstringValue bits.reverse (modBitsMsb m n)
  Snarky.assert lt

/-- `unpack_full` (OCaml `Field.Checked.unpack_full`): decompose into `n` LSB-first
bits with the canonical `< m` lock. -/
def unpackFull [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    (m n : ℕ) (v : FVar F) : CircuitM F c (Vector (BoolVar F) n) := do
  let bits ← unpack v n
  assertBitsBelow m n bits.toList
  pure bits

/-! ## The circuit laws -/

open Std.Do in
/-- The comparison reads as `ltPure` of the read bits against the pattern. -/
@[spec] theorem ltBitstringValue_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c]
    (xs : List (BoolVar F)) (ys : List Bool) :
    ⦃⌜True⌝⦄
    (ltBitstringValue (c := Builder V c) xs ys)
    ⦃⇓ r _ => ⌜∀ bs : List Bool,
        List.Forall₂ (fun (x : BoolVar F) (b : Bool) =>
          (↑x : CVar F).val V = bit b) xs bs →
        (↑r : CVar F).val V = bit (ltPure bs ys)⌝⦄ := by
  induction xs, ys using ltBitstringValue.induct with
  | case1 x xs ys ih =>
    simp only [ltBitstringValue]
    mvcgen [ih]
    rename_i r _ hr _ _
    intro hout bs hbs
    cases hbs with
    | cons hx htl =>
      rename_i b bs'
      rw [hout (!b) (ltPure bs' ys) (not_val hx) (hr bs' htl)]
      simp [ltPure]
  | case2 x xs ys ih =>
    simp only [ltBitstringValue]
    mvcgen [ih]
    rename_i r _ hr _ _
    intro hout bs hbs
    cases hbs with
    | cons hx htl =>
      rename_i b bs'
      rw [hout (!b) (ltPure bs' ys) (not_val hx) (hr bs' htl)]
      simp [ltPure]
  | case3 xs ys h1 h2 =>
    simp only [ltBitstringValue]
    mvcgen
    intro bs hbs
    cases hbs with
    | nil => cases ys <;> simp [ltPure, false_, circuitVal, bit]
    | cons hx htl =>
      cases ys with
      | nil => simp [ltPure, false_, circuitVal, bit]
      | cons y ys' =>
        cases y
        · exact ((h2 _ _ _ rfl rfl)).elim
        · exact ((h1 _ _ _ rfl rfl)).elim

/-- The state and result of `ltBitstringValue`'s honest run: its recursion over
`orRun`/`andRun`. -/
def ltRun {F : Type} [Field F] [DecidableEq F] (st : ProverState F) :
    List (BoolVar F) → List Bool → ProverState F × BoolVar F
  | x :: xs, true :: ys =>
    let r := ltRun st xs ys
    orRun r.1 (Snarky.not x) r.2
  | x :: xs, false :: ys =>
    let r := ltRun st xs ys
    andRun r.1 (Snarky.not x) r.2
  | _, _ => (st, false_)

/-- `ltRun` only grows the table, and its result is in scope at the state after. -/
theorem ltRun_scope [Field F] [DecidableEq F] {st : ProverState F} :
    ∀ (xs : List (BoolVar F)) (ys : List Bool), (∀ x ∈ xs, (↑x : CVar F).Scoped st) →
      st.env.Le (ltRun st xs ys).1.env ∧
        (↑(ltRun st xs ys).2 : CVar F).Scoped (ltRun st xs ys).1
  | x :: xs, true :: ys, hxs =>
    have ⟨hle, hr⟩ := ltRun_scope xs ys (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    have h := mulRun_grants
      (not_scoped (not_scoped ((hxs x (List.mem_cons_self ..)).of_le hle))) (not_scoped hr)
    ⟨hle.trans h.le, not_scoped h.fvar_scoped⟩
  | x :: xs, false :: ys, hxs =>
    have ⟨hle, hr⟩ := ltRun_scope xs ys (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    have h := mulRun_grants (not_scoped ((hxs x (List.mem_cons_self ..)).of_le hle)) hr
    ⟨hle.trans h.le, h.fvar_scoped⟩
  | [], _, _ => ⟨Assignments.Le.refl _, trivial⟩
  | _ :: _, [], _ => ⟨Assignments.Le.refl _, trivial⟩

/-- `ltRun` reads as the comparison of the bits against the pattern. -/
theorem ltRun_val [Field F] [DecidableEq F] {st : ProverState F} :
    ∀ (xs : List (BoolVar F)) (ys : List Bool) (bs : List Bool),
      (∀ x ∈ xs, (↑x : CVar F).Scoped st) →
      List.Forall₂ (fun (x : BoolVar F) (b : Bool) =>
        (↑x : CVar F).val st.env.toValuation = bit b) xs bs →
      (↑(ltRun st xs ys).2 : CVar F).val (ltRun st xs ys).1.env.toValuation
        = bit (ltPure bs ys)
  | x :: xs, true :: ys, _, hxs, .cons hx htl => by
    rename_i b bs'
    have hx' := hxs x (List.mem_cons_self ..)
    obtain ⟨hle, hr⟩ := ltRun_scope xs ys (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    have hv := ltRun_val xs ys bs' (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) htl
    have h := orRun_grants (not_scoped (hx'.of_le hle)) hr
      (not_val (by rw [CVar.val_of_le hle hx']; exact hx)) hv
    show (↑(orRun (ltRun st xs ys).1 (Snarky.not x) (ltRun st xs ys).2).2 : CVar F).val
      (orRun (ltRun st xs ys).1 (Snarky.not x) (ltRun st xs ys).2).1.env.toValuation = _
    rw [h.bool_val]
    simp [ltPure]
  | x :: xs, false :: ys, _, hxs, .cons hx htl => by
    rename_i b bs'
    have hx' := hxs x (List.mem_cons_self ..)
    obtain ⟨hle, hr⟩ := ltRun_scope xs ys (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    have hv := ltRun_val xs ys bs' (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) htl
    have h := andRun_grants (not_scoped (hx'.of_le hle)) hr
      (not_val (by rw [CVar.val_of_le hle hx']; exact hx)) hv
    show (↑(andRun (ltRun st xs ys).1 (Snarky.not x) (ltRun st xs ys).2).2 : CVar F).val
      (andRun (ltRun st xs ys).1 (Snarky.not x) (ltRun st xs ys).2).1.env.toValuation = _
    rw [h.bool_val]
    simp [ltPure]
  | [], ys, _, _, .nil => by cases ys <;> simp [ltRun, ltPure, false_, circuitVal, bit]
  | _ :: _, [], _, _, .cons _ _ => by simp [ltRun, ltPure, false_, circuitVal, bit]

/-- The comparison's honest run lands at `ltRun`. -/
theorem ltBitstringValue_run [Field F] [DecidableEq F] [BasicSystem F c] [Checker F c]
    [LawfulChecker F c] {xs : List (BoolVar F)} {ys : List Bool} (st : ProverState F)
    (hxs : ∀ x ∈ xs, (↑x : CVar F).Scoped st) :
    prove (Checker.holds (F := F) (c := c)) (ltBitstringValue (c := c) xs ys) st.nv st.env
      = .ok ((ltRun st xs ys).1.out (ltRun st xs ys).2) := by
  induction xs, ys using ltBitstringValue.induct with
  | case1 x xs ys ih =>
    obtain ⟨hle, hr⟩ := ltRun_scope xs ys (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    simp only [ltBitstringValue, ltRun, prove_bind,
      ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy)), Except.bind]
    exact or_run _ (not_scoped ((hxs x (List.mem_cons_self ..)).of_le hle)) hr
  | case2 x xs ys ih =>
    obtain ⟨hle, hr⟩ := ltRun_scope xs ys (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    simp only [ltBitstringValue, ltRun, prove_bind,
      ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy)), Except.bind]
    exact and_run _ (not_scoped ((hxs x (List.mem_cons_self ..)).of_le hle)) hr
  | case3 xs ys h1 h2 =>
    simp only [ltBitstringValue, ltRun]
    rfl

open Std.Do in
/-- The lock's rows force the read bits' ℕ value strictly below `m`. -/
@[spec] theorem assertBitsBelow_spec {V : Valuation F} [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c]
    (m n : ℕ) (hm : m < 2 ^ n) (bits : List (BoolVar F)) (hlen : bits.length = n) :
    ⦃⌜True⌝⦄
    (assertBitsBelow (c := Builder V c) m n bits)
    ⦃⇓ _ _ => ⌜∀ bs : List Bool,
        List.Forall₂ (fun (x : BoolVar F) (b : Bool) =>
          (↑x : CVar F).val V = bit b) bits bs →
        natLsbVal bs < m⌝⦄ := by
  simp only [assertBitsBelow]
  mvcgen
  rename_i lt _ hlt _ _
  intro hassert bs hfa
  have hltv := hlt bs.reverse (List.forall₂_reverse_iff.mpr hfa)
  rw [hassert] at hltv
  have hltrue : ltPure bs.reverse (modBitsMsb m n) = true := by
    by_contra h
    rw [Bool.not_eq_true] at h
    rw [h] at hltv
    simp [bit] at hltv
  have := (ltPure_iff_lt (by
    rw [List.length_reverse, modBitsMsb_length, ← hfa.length_eq, hlen])).mp hltrue
  rwa [natLsbVal_reverse_modBitsMsb hm, List.reverse_reverse] at this

/-- The lock's honest run on bits reading as a value below `m`: the comparison's run,
the assertion accepted. -/
theorem assertBitsBelow_run [Field F] [DecidableEq F] [BasicSystem F c] [Checker F c]
    [LawfulChecker F c] (m n : ℕ) (hm : m < 2 ^ n) {bits : List (BoolVar F)}
    (hlen : bits.length = n) (st : ProverState F) (hbits : ∀ x ∈ bits, (↑x : CVar F).Scoped st)
    {bs : List Bool}
    (hbs : List.Forall₂ (fun (x : BoolVar F) (b : Bool) =>
      (↑x : CVar F).val st.env.toValuation = bit b) bits bs)
    (hval : natLsbVal bs < m) :
    prove (Checker.holds (F := F) (c := c)) (assertBitsBelow (c := c) m n bits) st.nv st.env
      = .ok ((ltRun st bits.reverse (modBitsMsb m n)).1.out ()) := by
  have hrev : ∀ x ∈ bits.reverse, (↑x : CVar F).Scoped st :=
    fun x hx => hbits x (List.mem_reverse.mp hx)
  simp only [assertBitsBelow, prove_bind, ltBitstringValue_run st hrev, Except.bind]
  refine assert_run _ (ltRun_scope _ _ hrev).2 ?_
  rw [ltRun_val _ _ bs.reverse hrev (List.forall₂_reverse_iff.mpr hbs)]
  have hltrue : ltPure bs.reverse (modBitsMsb m n) = true := by
    rw [ltPure_iff_lt (by rw [List.length_reverse, modBitsMsb_length, ← hbs.length_eq, hlen])]
    rwa [natLsbVal_reverse_modBitsMsb hm, List.reverse_reverse]
  rw [hltrue]
  rfl

open Std.Do in
/-- `unpackFull`'s rows force bits whose ℕ value casts to the operand's reading AND
lies below `m` — the canonical lock the plain `unpack` lacks: at `m` the reader's
`card`, the value IS the reading's representative (`toNat_eq_of_natCast_eq`). -/
@[spec] theorem unpackFull_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c]
    (m n : ℕ) (hm : m < 2 ^ n) (v : FVar F) :
    ⦃⌜True⌝⦄
    (unpackFull (c := Builder V c) m n v)
    ⦃⇓ r _ => ⌜∃ bs : Vector Bool n,
        (∀ i (hi : i < n), (r[i].toCVar).val V = bit bs[i]) ∧
        ((natLsbVal bs.toList : Nat) : F) = v.val V ∧ natLsbVal bs.toList < m⌝⦄ := by
  simp only [unpackFull]
  mvcgen
  case hlen => simp
  rename_i bits _ hbits _ _ hlockv
  obtain ⟨bs, hread, hsum⟩ := hbits
  refine ⟨bs, hread, by rw [← packPure_natCast]; exact hsum, ?_⟩
  refine hlockv bs.toList ?_
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h1 h2 => ?_⟩
  simp only [List.get_eq_getElem, Vector.getElem_toList]
  exact hread i (by simpa using h1)

/-- The state and result of `unpackFull`'s honest run: `unpack`'s, then the lock's. -/
def unpackFullRun {F : Type} [Field F] [DecidableEq F] [ToNat F] (st : ProverState F) (m n : ℕ)
    (v : FVar F) : ProverState F × Vector (BoolVar F) n :=
  let u := unpackRun st v n
  ((ltRun u.1 u.2.toList.reverse (modBitsMsb m n)).1, u.2)

/-- `unpackFull`'s honest run on a representative that fits the width and lies below
`m` lands at `unpackFullRun`. -/
theorem unpackFull_run [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F] [BasicSystem F c]
    [Checker F c] [LawfulChecker F c] (m n : ℕ) (hm : m < 2 ^ n) {v : FVar F}
    (st : ProverState F) (hv : v.Scoped st)
    (hlt : ToNat.toNat (v.val st.env.toValuation) < 2 ^ n)
    (hbelow : ToNat.toNat (v.val st.env.toValuation) < m) :
    prove (Checker.holds (F := F) (c := c)) (unpackFull (c := c) m n v) st.nv st.env
      = .ok ((unpackFullRun st m n v).1.out (unpackFullRun st m n v).2) := by
  have hscope : ∀ x ∈ (unpackRun st v n).2.toList, (↑x : CVar F).Scoped (unpackRun st v n).1 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [Vector.getElem_toList]
    exact unpackRun_scoped st v n i (by simpa using hi)
  have hbs : List.Forall₂ (fun (x : BoolVar F) (b : Bool) =>
      (↑x : CVar F).val (unpackRun st v n).1.env.toValuation = bit b)
      (unpackRun st v n).2.toList (unpackPure (v.val st.env.toValuation) n).toList := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp, fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, Vector.getElem_toList]
    rw [unpackRun_bit st v n i (by simpa using h1)]
    simp [unpackPure]
  simp only [unpackFull, prove_bind, unpack_run st hv hlt, Except.bind]
  rw [assertBitsBelow_run m n hm (by simp) _ hscope hbs
    (by rw [natLsbVal_unpackPure hlt]; exact hbelow)]
  rfl

end Snarky
