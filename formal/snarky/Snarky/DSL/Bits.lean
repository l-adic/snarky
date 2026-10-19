import Mathlib.Tactic.Ring.Basic
import Kimchi.Bits
import Snarky.DSL.SizedF

namespace Snarky

set_option mvcgen.warning false

variable {F c : Type}

/-! # Bit packing and unpacking

LSB-first bit decomposition and recomposition. `pack` is the weighted-sum expression,
pure; `unpack` witnesses `n` checked booleans — each paying its `boolean` row — and pins
their weighted sum to the operand with one `r1cs` row. Bits read as a number through
`Kimchi.natLsbVal`; `unpackPure` is the cut in the other direction.
-/

/-! ## The representative's law -/

/-- `ToNat`'s laws at a field of `card` elements: the representative casts back to its
element, every representative lies below `card`, and below `card` a number is its own
cast's representative (`ZMod.val` at a prime field). -/
class LawfulToNat (F : Type) [NatCast F] [ToNat F] where
  /-- The representatives' bound — the field's cardinality. -/
  card : Nat
  /-- The representative casts back to its element. -/
  cast_toNat : ∀ x : F, ((ToNat.toNat x : Nat) : F) = x
  /-- Every representative lies below `card`. -/
  toNat_lt : ∀ x : F, ToNat.toNat x < card
  /-- Below `card`, a number is its own cast's representative. -/
  toNat_natCast : ∀ n : Nat, n < card → ToNat.toNat ((n : Nat) : F) = n

/-- `ZMod.val` is lawful at every nonzero modulus: it casts back, and lies below `p`. -/
instance instLawfulToNatZMod (p : Nat) [NeZero p] : LawfulToNat (ZMod p) :=
  ⟨p, fun x => ZMod.natCast_zmod_val x, fun x => ZMod.val_lt x, fun n hn => by
    show ZMod.val ((n : Nat) : ZMod p) = n
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]⟩

/-- A representative pinned by its cast: below `card` the cast is injective, so the
element's representative is the pinned number — the canonical reading of a lock. -/
theorem toNat_eq_of_natCast_eq {F : Type} [NatCast F] [ToNat F] [LawfulToNat F]
    {n : Nat} {x : F} (h : ((n : Nat) : F) = x)
    (hn : n < LawfulToNat.card (F := F)) : ToNat.toNat x = n := by
  rw [← h, LawfulToNat.toNat_natCast n hn]

/-- An integer below the modulus is its own representative: `toNat (m : ZMod p) = m` for
`0 ≤ m < p`. The `ℤ` twin of `LawfulToNat.toNat_natCast`. -/
theorem toNat_intCast_of_lt (p : ℕ) [NeZero p] {m : ℤ} (h0 : 0 ≤ m) (hlt : m < p) :
    (ToNat.toNat ((m : ZMod p)) : ℤ) = m := by
  show ((ZMod.val ((m : ZMod p))) : ℤ) = m
  rw [ZMod.val_intCast]; exact Int.emod_eq_of_lt h0 hlt

/-! ## The value level -/

/-- The value-level unpacking: the canonical representative's `n` low binary digits,
LSB first. -/
def unpackPure [ToNat F] (x : F) (n : Nat) : Vector Bool n :=
  Vector.ofFn fun i => (ToNat.toNat x).testBit i.val

/-- The unpacking's ℕ value is the representative it was cut from. -/
theorem natLsbVal_unpackPure [ToNat F] {n : Nat} {x : F} (hlt : ToNat.toNat x < 2 ^ n) :
    Kimchi.natLsbVal (unpackPure x n).toList = ToNat.toNat x := by
  rw [unpackPure, Vector.toList_ofFn]
  exact Kimchi.natLsbVal_ofFn_testBit n _ hlt

/-- The unpacking's digits, at an index. -/
@[simp] theorem getElem_unpackPure [ToNat F] {n : Nat} (x : F) (i : Nat) (hi : i < n) :
    (unpackPure x n)[i] = (ToNat.toNat x).testBit i := by
  rw [unpackPure]
  simp

attribute [irreducible] unpackPure

/-! ## Packing -/

/-- The weighted-sum expression `acc + Σⱼ 2^(i+j)·bits[j]`, LSB first. -/
private def packAux [Semiring F] [DecidableEq F] : List (BoolVar F) → Nat → FVar F → FVar F
  | [], _, acc => acc
  | b :: bs, i, acc => packAux bs (i + 1) (CVar.add_ acc (CVar.scale_ ((2 : F) ^ i) ↑b))

/-- Pack bits into their weighted sum `Σ 2ⁱ·bᵢ`, LSB first — pure, no rows. -/
def pack [Semiring F] [DecidableEq F] {n : Nat} (bits : Vector (BoolVar F) n) : FVar F :=
  packAux bits.toList 0 (.const 0)

private theorem packAux_val [CommSemiring F] [DecidableEq F] {V : Valuation F} :
    ∀ (l : List (BoolVar F)) (bl : List Bool) (i : Nat) (acc : FVar F) (accv : F),
      l.map (fun b : BoolVar F => b.toCVar.val V) = bl.map bit → acc.val V = accv →
      (packAux l i acc).val V = accv + (2 : F) ^ i * (Kimchi.natLsbVal bl : F)
  | [], bl, i, acc, accv, hmap, hacc => by
    cases bl with
    | nil => simpa [packAux, Kimchi.natLsbVal] using hacc
    | cons _ _ => cases hmap
  | b :: l, bl, i, acc, accv, hmap, hacc => by
    cases bl with
    | nil => cases hmap
    | cons bv bl =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      rw [packAux, packAux_val l bl (i + 1) _ (accv + (2 : F) ^ i * bit bv) hmap.2
        (by simp [hacc, hmap.1]), Kimchi.natLsbVal]
      have hb : ((bv.toNat : Nat) : F) = bit bv := by cases bv <;> simp [bit]
      push_cast
      rw [hb]
      ring

/-- `pack` reads as the value-level packing of the bits it is given. -/
theorem pack_val [CommSemiring F] [DecidableEq F] {n : Nat} {bits : Vector (BoolVar F) n}
    {bs : Vector Bool n} {V : Valuation F}
    (h : ∀ i (hi : i < n), (↑bits[i] : CVar F).val V = bit bs[i]) :
    (pack bits).val V = ((Kimchi.natLsbVal bs.toList : Nat) : F) := by
  unfold pack
  rw [packAux_val bits.toList bs.toList 0 _ 0 (List.ext_getElem (by simp) fun i h1 _ => by
    simp only [List.getElem_map, Vector.getElem_toList]
    exact h i (by simpa using h1)) rfl]
  ring

attribute [irreducible] pack

/-! ## Unpacking -/

/-- Decompose a field variable into `n` LSB-first bits: witness them checked — each pays
its `boolean` row — then pin their weighted sum to the operand with one `r1cs` row. -/
def unpack [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) (n : Nat) :
    CircuitM F c (Vector (BoolVar F) n) := do
  let bits ← witness (val := Vector Bool n) (advice v n)
  addConstraint (BasicSystem.r1cs (pack bits) (.const 1) v)
  pure bits
where
  /-- The advice: the operand's canonical representative's low digits. -/
  advice (v : FVar F) (n : Nat) : AsProver F (Vector Bool n) := do
    let x ← readVar (val := F) v
    pure (unpackPure x n)

open Std.Do in
/-- `unpack`'s rows force the results to be bits whose weighted sum is the operand's
reading. That they are the operand's binary digits — their canonicity — additionally
needs a characteristic hypothesis and is not stated. -/
@[spec] theorem unpack_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) (n : Nat) :
    ⦃⌜True⌝⦄
    unpack (c := Builder V c) v n
    ⦃⇓ r _ => ⌜∃ bs : Vector Bool n,
        (∀ i (hi : i < n), (↑r[i] : CVar F).val V = bit bs[i]) ∧
        ((Kimchi.natLsbVal bs.toList : Nat) : F) = v.val V⌝⦄ := by
  simp only [unpack]
  mvcgen
  rename_i _ bits _ hpost _ _ hrow
  have hbit : ∀ i (hi : i < n), ∃ bb : Bool, (↑bits[i] : CVar F).val V = bit bb := fun i hi =>
    hpost bits[i] (Vector.mem_toList_iff.mpr (Vector.mem_iff_getElem.mpr ⟨i, hi, rfl⟩))
  choose f hf using hbit
  refine ⟨Vector.ofFn fun i : Fin n => f i.val i.isLt, fun i hi => by simpa using hf i hi, ?_⟩
  rw [← pack_val (bits := bits) fun i hi => by simpa using hf i hi]
  simpa using (LawfulBasicSystem.holds_r1cs V _ _ _).mp hrow

/-- `unpack`'s completeness law: where the operand's representative fits in `n` bits the
run succeeds, its rows are satisfied at every extension of the final table, and the bits
are scoped. -/
@[complete_law]
theorem unpack_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) (vv : F) (n : Nat)
    (hlt : ToNat.toNat vv < 2 ^ n) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st v vv)
      (unpack (c := c) v n)
      (fun a st' => CircuitType.ReadsAs (val := Vector Bool n) st' a (unpackPure vv n)) := by
  simp only [unpack]
  refine Complete.bind
    (Complete.imp (fun st h => ⟨?_, h⟩) (fun _ _ h => h)
      (Complete.frame CircuitType.monotone_readsAs
        (Complete.witness (unpack.advice v n) (unpackPure vv n) (by simp))))
    (fun r => Complete.bind (Complete.addConstraint ?_)
      fun _ => Complete.pure_of fun _ h => h.1)
  · rintro st ⟨hr, hv⟩ stf hle
    refine (LawfulBasicSystem.holds_r1cs ..).mpr ?_
    have hbits := CircuitType.reads_vector.mp (hr.2.of_le hr.1 hle)
    rw [CVar.val_of_le hle (CircuitType.scoped_fvar.mp hv.1),
      pack_val (bs := unpackPure vv n)
        fun i hi => CircuitType.reads_boolVar.mp (hbits i hi),
      natLsbVal_unpackPure hlt, LawfulToNat.cast_toNat, CircuitType.reads_fvar.mp hv.2]
    simp
  · simp [unpack.advice, readVar_run h.1, CircuitType.readVal_fvar,
      CircuitType.reads_fvar.mp h.2]

attribute [irreducible] unpack

/-- The rows `unpack` emits, in order: one `boolean` per bit, then the packing row. -/
example [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) (nv : Nat) :
    (build (unpack (c := c) v 2) nv).constraints =
      (let bits := (build (unpack (c := c) v 2) nv).result
       [BasicSystem.boolean bits[0].toCVar, BasicSystem.boolean bits[1].toCVar,
        BasicSystem.r1cs (pack bits) (.const 1) v]) := by
  unfold unpack
  simp only [build_bind, build, witness, Snarky.addConstraint]
  rfl

/-! ## The state-relative completeness law

`unpack`'s law at the prover's reading (`Snarky.Prover.WP`), and its registered reading for
`mvcgen`. -/

section ProverReading

open Std.Do

/-- `unpack.advice` returns the operand's low digits. -/
@[spec] private def Prover.unpack_advice_reg [Field F] [DecidableEq F] [ToNat F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) (n : Nat) :=
  Prover.register (Prover.witness_of_run (c := c) (unpack.advice v n) (fun st => v.Scoped st)
    (fun st => unpackPure (st.read v) n)
    (fun _ h => by simp [unpack.advice, readVar_run (CircuitType.scoped_fvar.mpr h)])
    fun _ _ => by simp)

/-- `unpack`'s completeness: where the operand's representative fits in `n` bits, each bit is
in scope and reads the representative's binary digit at its index. -/
theorem Prover.unpack_spec [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) (n : Nat)
    (st₀ : ProverState F) :
    ⦃fun s => ⌜s = st₀ ∧ v.Scoped st₀ ∧ ToNat.toNat (st₀.read v) < 2 ^ n⌝⦄
    unpack (c := Prover c) v n
    ⦃⇓ r s' => ⌜(∀ i (hi : i < n), (↑r[i] : CVar F).Scoped s') ∧
      (∀ i (hi : i < n),
        s'.read r[i] = if (ToNat.toNat (st₀.read v)).testBit i then 1 else 0) ∧
      st₀ ≤ s'⌝⦄ := by
  unfold unpack
  mvcgen
  -- the packing row: the bits read the operand's digits, whose weighted sum is its reading
  case vc2.post.success.pre =>
    rename_i s₀ h₀ r s₁ h₁
    obtain ⟨rfl, hv, hlt⟩ := h₀
    obtain ⟨⟨-, hr⟩, hle⟩ := Prover.Reg.iff.mp h₁
    refine ⟨trivial, (LawfulBasicSystem.holds_r1cs ..).mpr ?_⟩
    rw [pack_val (bs := unpackPure (s₀.read v) n) fun i hi =>
        CircuitType.reads_boolVar.mp (CircuitType.reads_vector.mp hr i hi),
      natLsbVal_unpackPure hlt, LawfulToNat.cast_toNat, CVar.val_of_le hle hv]
    simp
  all_goals grind [Prover.Reg.iff, CircuitType.ReadsAs, CircuitType.scoped_vector,
    CircuitType.reads_vector, CircuitType.scoped_boolVar, CircuitType.reads_boolVar,
    ProverState.read_of_le, CVar.Scoped.of_le, getElem_unpackPure, bit]

/-- Registered. -/
@[spec] def Prover.unpack_reg [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) (n : Nat) :=
  Prover.register (Prover.unpack_spec (c := c) v n)

end ProverReading

end Snarky
