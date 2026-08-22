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

/-- `not`'s reading, val-level (the eval-level law is `not_eval`). -/
private theorem not_val [Field F] [DecidableEq F] {x : BoolVar F}
    {V : Valuation F} {xb : Bool} (hx : (↑x : CVar F).val V = bit xb) :
    (↑(Snarky.not x) : CVar F).val V = bit (!xb) := by
  cases xb <;> simp [Snarky.not, circuitVal, hx, bit]

open Std.Do in
/-- The comparison reads as `ltPure` of the read bits against the pattern. -/
@[spec] theorem ltBitstringValue_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c]
    (xs : List (BoolVar F)) (ys : List Bool)
    (Q : PostCond (BoolVar F) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : BoolVar F) => ∀ bs : List Bool,
        List.Forall₂ (fun (x : BoolVar F) (b : Bool) =>
          (↑x : CVar F).val V = bit b) xs bs →
        (↑r : CVar F).val V = bit (ltPure bs ys)) Q⦄
    (ltBitstringValue (c := c) xs ys)
    ⦃Q⦄ := by
  induction xs, ys using ltBitstringValue.induct generalizing Q with
  | case1 x xs ys ih =>
    simp only [ltBitstringValue]
    mvcgen [ih]
    rename_i hpre
    intro r nv hr
    mvcgen
    intro out nv' hout
    refine hpre out nv' fun bs hbs => ?_
    cases hbs with
    | cons hx htl =>
      rename_i b bs'
      rw [hout (!b) (ltPure bs' ys) (not_val hx) (hr bs' htl)]
      simp [ltPure]
  | case2 x xs ys ih =>
    simp only [ltBitstringValue]
    mvcgen [ih]
    rename_i hpre
    intro r nv hr
    mvcgen
    intro out nv' hout
    refine hpre out nv' fun bs hbs => ?_
    cases hbs with
    | cons hx htl =>
      rename_i b bs'
      rw [hout (!b) (ltPure bs' ys) (not_val hx) (hr bs' htl)]
      simp [ltPure]
  | case3 xs ys h1 h2 =>
    simp only [ltBitstringValue]
    mvcgen
    rename_i hpre
    refine hpre false_ _ fun bs hbs => ?_
    cases hbs with
    | nil => cases ys <;> simp [ltPure, false_, circuitVal, bit]
    | cons hx htl =>
      cases ys with
      | nil => simp [ltPure, false_, circuitVal, bit]
      | cons y ys' =>
        cases y
        · exact ((h2 _ _ _ rfl rfl)).elim
        · exact ((h1 _ _ _ rfl rfl)).elim

open Std.Do in
/-- The comparison's honest run: on operands reading as the bits `bs`, it succeeds and
the result reads as `ltPure bs ys`. -/
@[spec] theorem ltBitstringValue_complete_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [Checker F c] [LawfulChecker F c]
    (xs : List (BoolVar F)) (ys : List Bool) (bs : List Bool)
    (Q : PostCond (BoolVar F) (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => List.Forall₂ (fun (x : BoolVar F) (b : Bool) =>
          (↑x : CVar F).eval env = .ok (bit b)) xs bs)
        (fun _ (r : BoolVar F) env' =>
          (↑r : CVar F).eval env' = .ok (bit (ltPure bs ys))) Q⦄
    (ltBitstringValue (c := Prover c) xs ys)
    ⦃Q⦄ := by
  induction xs, ys using ltBitstringValue.induct generalizing bs Q with
  | case1 x xs ys ih =>
    simp only [ltBitstringValue]
    intro st hpre
    obtain ⟨hfa, hk⟩ := hpre
    cases hfa with
    | cons hx htl =>
      rename_i b bs'
      simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
      refine ih bs' _ st ⟨htl, fun r st₁ hr hle₁ => ?_⟩
      have hx₁ := CVar.eval_le hle₁ hx
      have hnx : (↑(Snarky.not x) : CVar F).eval st₁.env = .ok (bit (!b)) := by
        have := not_eval (bb := b) (by simpa [bit] using hx₁)
        simpa [bit] using this
      refine Snarky.or_complete_spec (Snarky.not x) r _ st₁
        ⟨⟨isOk_of_eq hnx, isOk_of_eq hr⟩, fun out st₂ hout hle₂ => ?_⟩
      refine hk out st₂ ?_ (hle₁.trans hle₂)
      show (↑out : CVar F).eval st₂.env = .ok (bit (ltPure (b :: bs') (true :: ys)))
      rw [hout (!b) (ltPure bs' ys) hnx hr]
      simp [ltPure]
  | case2 x xs ys ih =>
    simp only [ltBitstringValue]
    intro st hpre
    obtain ⟨hfa, hk⟩ := hpre
    cases hfa with
    | cons hx htl =>
      rename_i b bs'
      simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
      refine ih bs' _ st ⟨htl, fun r st₁ hr hle₁ => ?_⟩
      have hx₁ := CVar.eval_le hle₁ hx
      have hnx : (↑(Snarky.not x) : CVar F).eval st₁.env = .ok (bit (!b)) := by
        have := not_eval (bb := b) (by simpa [bit] using hx₁)
        simpa [bit] using this
      refine Snarky.and_complete_spec (Snarky.not x) r _ st₁
        ⟨⟨isOk_of_eq hnx, isOk_of_eq hr⟩, fun out st₂ hout hle₂ => ?_⟩
      refine hk out st₂ ?_ (hle₁.trans hle₂)
      show (↑out : CVar F).eval st₂.env = .ok (bit (ltPure (b :: bs') (false :: ys)))
      rw [hout (!b) (ltPure bs' ys) hnx hr]
      simp [ltPure]
  | case3 xs ys h1 h2 =>
    simp only [ltBitstringValue]
    intro st hpre
    obtain ⟨hfa, hk⟩ := hpre
    mvcgen
    refine hk (false_ : BoolVar F) st ?_ (Assignments.Le.refl st.env)
    cases hfa with
    | nil => rfl
    | cons hx htl =>
      cases ys with
      | nil => rfl
      | cons y ys' =>
        cases y
        · exact ((h2 _ _ _ rfl rfl)).elim
        · exact ((h1 _ _ _ rfl rfl)).elim

open Std.Do in
/-- The lock's rows force the read bits' ℕ value strictly below `m`. -/
@[spec] theorem assertBitsBelow_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c]
    (m n : ℕ) (hm : m < 2 ^ n) (bits : List (BoolVar F)) (hlen : bits.length = n)
    (Q : PostCond PUnit (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (_ : PUnit) => ∀ bs : List Bool,
        List.Forall₂ (fun (x : BoolVar F) (b : Bool) =>
          (↑x : CVar F).val V = bit b) bits bs →
        natLsbVal bs < m) Q⦄
    (assertBitsBelow (c := c) m n bits)
    ⦃Q⦄ := by
  simp only [assertBitsBelow]
  mvcgen [ltBitstringValue_spec]
  rename_i s hpre
  intro lt nv₁ hlt
  mvcgen
  intro _ nv₂ hassert
  refine hpre ⟨⟩ _ fun bs hfa => ?_
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

open Std.Do in
/-- The lock's honest run succeeds on bits reading as a value below `m`. -/
@[spec] theorem assertBitsBelow_complete_spec [Field F] [DecidableEq F] [BasicSystem F c]
    [Checker F c] [LawfulChecker F c]
    (m n : ℕ) (hm : m < 2 ^ n) (bits : List (BoolVar F)) (hlen : bits.length = n)
    (bs : List Bool) (hval : natLsbVal bs < m)
    (Q : PostCond PUnit (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => List.Forall₂ (fun (x : BoolVar F) (b : Bool) =>
          (↑x : CVar F).eval env = .ok (bit b)) bits bs)
        (fun _ _ _ => True) Q⦄
    (assertBitsBelow (c := Prover c) m n bits)
    ⦃Q⦄ := by
  intro st hpre
  obtain ⟨hfa, hk⟩ := hpre
  simp only [assertBitsBelow, WPMonad.wp_bind, PredTrans.apply_Bind_bind]
  refine ltBitstringValue_complete_spec _ _ bs.reverse _ st
    ⟨List.forall₂_reverse_iff.mpr hfa, fun lt st₁ hlt hle₁ => ?_⟩
  have hltrue : ltPure bs.reverse (modBitsMsb m n) = true := by
    refine (ltPure_iff_lt (by
      rw [List.length_reverse, modBitsMsb_length, ← hfa.length_eq, hlen])).mpr ?_
    rwa [natLsbVal_reverse_modBitsMsb hm, List.reverse_reverse]
  rw [hltrue] at hlt
  refine Snarky.assert_complete_spec lt _ st₁
    ⟨⟨isOk_of_eq hlt, fun bv hbv => ?_⟩, fun _ st₂ _ hle₂ => ?_⟩
  · rw [hlt] at hbv
    injection hbv with hbv
    rw [← hbv]
    rfl
  exact hk ⟨⟩ st₂ trivial (hle₁.trans hle₂)

open Std.Do in
/-- `unpackFull`'s rows force bits whose weighted sum is the operand's reading AND
whose ℕ value is below `m` — the canonical lock the plain `unpack` lacks. -/
@[spec] theorem unpackFull_spec [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c]
    (m n : ℕ) (hm : m < 2 ^ n) (v : FVar F)
    (Q : PostCond (Vector (BoolVar F) n) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : Vector (BoolVar F) n) => ∃ bs : Vector Bool n,
        (∀ i (hi : i < n), (r[i].toCVar).val V = bit bs[i]) ∧
        packPure bs = v.val V ∧ natLsbVal bs.toList < m) Q⦄
    (unpackFull (c := c) m n v)
    ⦃Q⦄ := by
  simp only [unpackFull]
  mvcgen
  rename_i s hpre
  intro bits nv₁ hbits
  mvcgen
  case vc2.hlen => simp
  intro _ nv₂ hlockv
  mvcgen
  obtain ⟨bs, hread, hsum⟩ := hbits
  refine hpre bits nv₂ ⟨bs, hread, hsum, ?_⟩
  refine hlockv bs.toList ?_
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h1 h2 => ?_⟩
  simp only [List.get_eq_getElem, Vector.getElem_toList]
  exact hread i (by simpa using h1)

open Std.Do in
/-- `unpackFull`'s honest run succeeds on a faithful representative that fits the width
and lies below `m`; the results are the operand's binary digits. -/
@[spec] theorem unpackFull_complete_spec [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [Checker F c] [LawfulChecker F c]
    (m n : ℕ) (hm : m < 2 ^ n) (v : FVar F)
    (Q : PostCond (Vector (BoolVar F) n)
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (v.eval env).isOk ∧
          ∀ vv, v.eval env = .ok vv →
            ((ToNat.toNat vv : Nat) : F) = vv ∧ ToNat.toNat vv < 2 ^ n ∧
              ToNat.toNat vv < m)
        (fun env r env' => ∀ vv, v.eval env = .ok vv →
          ∀ i (hi : i < n), (r[i]).toCVar.eval env'
            = .ok (bit ((ToNat.toNat vv).testBit i))) Q⦄
    (unpackFull (c := Prover c) m n v)
    ⦃Q⦄ := by
  intro st hpre
  obtain ⟨⟨hokv, hcond⟩, hk⟩ := hpre
  obtain ⟨vv, hv⟩ := CVar.evalOk hokv
  obtain ⟨hfaith, hfit, hbound⟩ := hcond vv hv
  simp only [unpackFull, WPMonad.wp_bind, PredTrans.apply_Bind_bind]
  refine unpack_complete_spec v n _ st
    ⟨⟨hokv, fun vv' hv' => ?_⟩, fun bits st₁ hbits hle₁ => ?_⟩
  · rw [hv] at hv'
    injection hv' with hv'
    subst hv'
    exact ⟨hfaith, hfit⟩
  have hdig : ∀ i (hi : i < n), (bits[i]).toCVar.eval st₁.env
      = .ok (bit ((ToNat.toNat vv).testBit i)) := fun i hi => hbits vv hv i hi
  have hfa : List.Forall₂ (fun (x : BoolVar F) (b : Bool) =>
      (↑x : CVar F).eval st₁.env = .ok (bit b))
      bits.toList (unpackPure vv n).toList := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp, fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, Vector.getElem_toList, unpackPure,
      Vector.getElem_ofFn]
    exact hdig i (by simpa using h1)
  refine assertBitsBelow_complete_spec m n hm bits.toList (by simp)
    (unpackPure vv n).toList (by rwa [natLsbVal_unpackPure hfit]) _ st₁
    ⟨hfa, fun _ st₂ _ hle₂ => ?_⟩
  intro _
  refine hk bits st₂ (fun vv' hv' => ?_) (hle₁.trans hle₂)
  rw [hv] at hv'
  injection hv' with hv'
  subst hv'
  intro i hi
  exact CVar.eval_le hle₂ (hdig i hi)

end Snarky
