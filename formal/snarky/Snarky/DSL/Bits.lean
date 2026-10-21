import Mathlib.Tactic.Ring.Basic
import Kimchi.Bits
import Snarky.DSL.SizedF

namespace Snarky

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

private theorem packAux_scoped [Semiring F] [DecidableEq F] {st : ProverState F} :
    ∀ (l : List (BoolVar F)) (i : Nat) (acc : FVar F), (∀ b ∈ l, (↑b : CVar F).Scoped st) →
      acc.Scoped st → (packAux l i acc).Scoped st
  | [], _, _, _, hacc => hacc
  | b :: l, i, acc, hl, hacc =>
    packAux_scoped l (i + 1) _ (fun b' hb' => hl b' (List.mem_cons_of_mem _ hb'))
      (CVar.Scoped.add_ hacc (CVar.Scoped.scale_ (hl b (List.mem_cons_self ..))))

/-- `pack` is in scope when its bits are. -/
private theorem pack_scoped [Semiring F] [DecidableEq F] {n : Nat}
    {bits : Vector (BoolVar F) n} {st : ProverState F}
    (h : ∀ i (hi : i < n), (↑bits[i] : CVar F).Scoped st) : (pack bits).Scoped st := by
  unfold pack
  refine packAux_scoped _ 0 _ (fun b hb => ?_) (CVar.scoped_const _ _)
  obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hb)
  exact h i hi

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

open Std.WP in
/-- `unpack`'s rows force the results to be bits whose weighted sum is the operand's
reading. That they are the operand's binary digits — their canonicity — additionally
needs a characteristic hypothesis and is not stated. -/
@[spec] theorem unpack_spec {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) (n : Nat) :
    ⦃fun _ => True⦄
    unpack (c := Builder V c) v n
    ⦃fun (r : Vector (BoolVar F) n) _ => ∃ bs : Vector Bool n,
        (∀ i (hi : i < n), (↑r[i] : CVar F).val V = bit bs[i]) ∧
        ((Kimchi.natLsbVal bs.toList : Nat) : F) = v.val V⦄ := by
  simp only [unpack]
  vcgen
  rename_i hpost hrow
  have hbit : ∀ i (hi : i < n), ∃ bb : Bool, (↑bits[i] : CVar F).val V = bit bb := fun i hi =>
    hpost bits[i] (Vector.mem_toList_iff.mpr (Vector.mem_iff_getElem.mpr ⟨i, hi, rfl⟩))
  choose f hf using hbit
  refine ⟨Vector.ofFn fun i : Fin n => f i.val i.isLt, fun i hi => by simpa using hf i hi, ?_⟩
  refine (pack_val (bits := bits) fun i hi => by simpa using hf i hi).symm.trans ?_
  simpa using (LawfulBasicSystem.holds_r1cs V _ _ _).mp hrow

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

/-! ## The completeness law

`unpack`'s law at the prover's reading (`Snarky.Prover.VCGen`): the operand's reading in, the
bits reading its representative's binary digits out. -/

section ProverReading

open Snarky.Prover Std.WP

/-- `unpack.advice` returns the operand's low digits. -/
private theorem Prover.unpack_advice_run [Field F] [ToNat F] {v : FVar F} {s : ProverState F}
    (hv : v.Scoped s) (n : Nat) :
    (unpack.advice v n).run s.env = .ok (unpackPure (v.val s.env.get) n) := by
  simp [unpack.advice, readVar_run (CircuitType.scoped_fvar.mpr hv)]

/-- A reading of the unpacking is, at each index, a reading of the representative's binary digit
there. -/
theorem Prover.Reads.unpackPure_eq [Field F] [DecidableEq F] [ToNat F] {n : Nat}
    (r : Vector (BoolVar F) n) (a : F) :
    Reads (F := F) r (unpackPure a n) = ⨅ i : Fin n, Reads r[i] ((ToNat.toNat a).testBit i) := by
  simp [Reads.vector_eq]

/-- `unpack`'s completeness: where the operand's representative fits in `n` bits, the bits read
its binary digits. -/
theorem Prover.unpack_spec [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) (n : Nat)
    (a : F) (hlt : ToNat.toNat a < 2 ^ n) :
    ⦃Reads v a⦄ unpack (c := Prover c) v n ⦃fun r ↦ Reads r (unpackPure a n)⦄ := by
  have hw := fun v' : FVar F ↦ Spec.witness (c := c) (unpack.advice v' n) (unpackPure a n)
    (valid_vector.mpr fun _ _ ↦ valid_bool)
  unfold unpack
  vcgen [hw]
  case vc4 =>
    prover_assert with
      intro s _ hb
      rw [Reads.unpackPure_eq, Pred.iInf_apply] at hb
      simp only [Reads.boolVar_apply] at hb
      have hp := pack_val (bs := unpackPure a n) (V := s.env.get) fun i hi ↦ by
        simpa using (hb ⟨i, hi⟩).2
      rw [natLsbVal_unpackPure hlt, LawfulToNat.cast_toNat] at hp
      have hps := pack_scoped fun i hi ↦ (hb ⟨i, hi⟩).1
      simp_all [Reads.fvar_apply, Checked.apply, LawfulBasicSystem.holds_r1cs,
        LawfulBasicSystem.cells_r1cs, CVar.val]
  all_goals prover_assert with
    (intros; simp_all [Reads.fvar_apply, Prover.unpack_advice_run])

end ProverReading

end Snarky
