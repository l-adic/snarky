import Mathlib.Tactic.Ring
import Snarky.DSL.SizedF

namespace Snarky

set_option mvcgen.warning false

variable {F c : Type}

/-! # Bit packing and unpacking

LSB-first bit decomposition and recomposition. `pack` is the weighted-sum expression,
pure; `unpack` witnesses `n` checked booleans — each paying its `boolean` row — and pins
their weighted sum to the operand with one `r1cs` row. `packPure`/`unpackPure` are the
value-level mirrors.
-/

/-! ## The representative's law -/

/-- `ToNat`'s law: the representative casts back to its element. -/
class LawfulToNat (F : Type) [NatCast F] [ToNat F] where
  /-- The representative casts back to its element. -/
  cast_toNat : ∀ x : F, ((ToNat.toNat x : Nat) : F) = x

/-! ## The value level -/

/-- The LSB-first value of a bit list. The ℕ-level reading of a decomposition, which
`packPure` casts into the field; a comparison against the modulus lives here, where it
has a meaning the field cannot express. -/
def natVal : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * natVal bs

/-- A bit list's value fits in its length. -/
theorem natVal_lt : ∀ l : List Bool, natVal l < 2 ^ l.length
  | [] => by simp [natVal]
  | b :: l => by
    have := natVal_lt l
    have hb : b.toNat ≤ 1 := by cases b <;> simp
    simp only [natVal, List.length_cons, pow_succ]
    omega

/-- Appending a bit at the top adds it at the list's own weight. -/
theorem natVal_append_singleton : ∀ (l : List Bool) (b : Bool),
    natVal (l ++ [b]) = natVal l + b.toNat * 2 ^ l.length
  | [], b => by simp [natVal]
  | x :: l, b => by
    rw [List.cons_append, natVal, natVal_append_singleton l b, natVal, List.length_cons,
      pow_succ]
    ring

/-- The value-level indexed fold under `packPure`. -/
private def packPureAux [Semiring F] : List Bool → Nat → F → F
  | [], _, acc => acc
  | b :: bs, i, acc => packPureAux bs (i + 1) (acc + (2 : F) ^ i * bit b)

/-- The value-level packing `Σ 2ⁱ·bᵢ`, LSB first. -/
def packPure [Semiring F] {n : Nat} (bs : Vector Bool n) : F := packPureAux bs.toList 0 0

/-- The value-level unpacking: the canonical representative's `n` low binary digits,
LSB first. -/
def unpackPure [ToNat F] (x : F) (n : Nat) : Vector Bool n :=
  Vector.ofFn fun i => (ToNat.toNat x).testBit i.val

/-- The indexed fold in Horner form, through the cast. -/
private theorem packPureAux_horner [CommSemiring F] :
    ∀ (bl : List Bool) (i : Nat) (acc : F),
      packPureAux bl i acc = acc + (2 : F) ^ i * (natVal bl : F)
  | [], i, acc => by simp [packPureAux, natVal]
  | b :: bs, i, acc => by
    rw [packPureAux, packPureAux_horner bs (i + 1), natVal]
    have hb : ((b.toNat : Nat) : F) = bit b := by cases b <;> simp [bit]
    push_cast
    rw [hb]
    ring

/-- The low digits of a fitting number Horner-fold back to it. -/
theorem natVal_testBit :
    ∀ (n m : Nat), m < 2 ^ n → natVal (List.ofFn fun i : Fin n => m.testBit i.val) = m
  | 0, m, hm => by simp only [List.ofFn_zero, natVal]; omega
  | n + 1, m, hm => by
    rw [List.ofFn_succ]
    simp only [natVal, Fin.val_zero, Fin.val_succ, Nat.testBit_succ, Nat.testBit_zero]
    rw [natVal_testBit n (m / 2)
      (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; simpa [pow_succ] using hm))]
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h] <;> omega

/-- The round trip: packing the unpacking is the identity on a representative fitting in
`n` bits. -/
theorem packPure_unpackPure [CommSemiring F] [ToNat F] [LawfulToNat F] {n : Nat} {x : F}
    (hlt : ToNat.toNat x < 2 ^ n) : packPure (unpackPure x n) = x := by
  rw [packPure, unpackPure, Vector.toList_ofFn, packPureAux_horner,
    natVal_testBit n _ hlt]
  simpa using LawfulToNat.cast_toNat x

attribute [irreducible] packPure unpackPure

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
      (packAux l i acc).val V = packPureAux bl i accv
  | [], bl, i, acc, accv, hmap, hacc => by
    cases bl with
    | nil => simpa [packAux, packPureAux] using hacc
    | cons _ _ => cases hmap
  | b :: l, bl, i, acc, accv, hmap, hacc => by
    cases bl with
    | nil => cases hmap
    | cons bv bl =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      refine packAux_val l bl (i + 1) _ _ hmap.2 ?_
      simp [hacc, hmap.1]

/-- `pack` reads as the value-level packing of the bits it is given. -/
theorem pack_val [CommSemiring F] [DecidableEq F] {n : Nat} {bits : Vector (BoolVar F) n}
    {bs : Vector Bool n} {V : Valuation F}
    (h : ∀ i (hi : i < n), (↑bits[i] : CVar F).val V = bit bs[i]) :
    (pack bits).val V = packPure bs := by
  unfold pack packPure
  refine packAux_val bits.toList bs.toList 0 _ _ (List.ext_getElem (by simp) ?_) rfl
  intro i h1 h2
  simp only [List.getElem_map, Vector.getElem_toList]
  exact h i (by simpa using h1)

/-- `pack` is in scope when its bits are. -/
theorem CVar.Scoped.pack [Semiring F] [DecidableEq F] {st : ProverState F} {n : Nat}
    {bits : Vector (BoolVar F) n} (h : ∀ i (hi : i < n), (↑bits[i] : CVar F).Scoped st) :
    (Snarky.pack bits).Scoped st := by
  unfold Snarky.pack
  suffices hf : ∀ (l : List (BoolVar F)) (i : Nat) (acc : FVar F), acc.Scoped st →
      (∀ b ∈ l, (↑b : CVar F).Scoped st) → (packAux l i acc).Scoped st from
    hf bits.toList 0 _ trivial (by
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
      rw [Vector.getElem_toList]
      exact h i (by simpa using hi))
  intro l
  induction l with
  | nil => exact fun _ _ hacc _ => hacc
  | cons b t ih =>
    intro i acc hacc hl
    exact ih (i + 1) _ (hacc.add_ (CVar.ScopedBy.scale_ (hl b (List.mem_cons_self ..))))
      fun x hx => hl x (List.mem_cons_of_mem _ hx)

attribute [irreducible] pack

/-- Pack the low `k` bits of an `n`-bit vector, LSB first — pure, no rows. Irreducible:
consumers read it through `packLow_val`, never by opening the fold. -/
@[irreducible] def packLow [Semiring F] [DecidableEq F] {n : Nat} (k : Nat) (hk : k ≤ n)
    (bits : Vector (BoolVar F) n) : FVar F :=
  pack (takeVec k hk bits)

/-- `packLow` reads as the value-level packing of the low bits. -/
theorem packLow_val [CommSemiring F] [DecidableEq F] {n k : Nat} (hk : k ≤ n)
    {bits : Vector (BoolVar F) n} {bs : Vector Bool n} {V : Valuation F}
    (h : ∀ i (hi : i < n), (↑bits[i] : CVar F).val V = bit bs[i]) :
    (packLow k hk bits).val V = packPure (takeVec k hk bs) := by
  unfold packLow
  refine pack_val fun i hi => ?_
  rw [getElem_takeVec, getElem_takeVec]
  exact h i (Nat.lt_of_lt_of_le hi hk)

/-! ## Unpacking -/

/-- Decompose a field variable into `n` LSB-first bits: witness them checked — each pays
its `boolean` row — then pin their weighted sum to the operand with one `r1cs` row. -/
def unpack [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] (v : FVar F) (n : Nat) :
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
        (∀ i (hi : i < n), (↑r[i] : CVar F).val V = bit bs[i]) ∧ packPure bs = v.val V⌝⦄ := by
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
theorem unpack_complete [Field F] [DecidableEq F] [ToNat F] [LawfulToNat F] [BasicSystem F c]
    [ConstraintHolds F c] [LawfulBasicSystem F c] (v : FVar F) (vv : F) (n : Nat)
    (hlt : ToNat.toNat vv < 2 ^ n) :
    Complete (fun st => CircuitType.ReadsAs (val := F) st v vv)
      (unpack (c := c) v n)
      (fun a st' => CircuitType.ReadsAs (val := Vector Bool n) st' a (unpackPure vv n)) := by
  intro st hv'
  simp only [CircuitType.ReadsAs, CircuitType.scoped_fvar, CircuitType.reads_fvar] at hv'
  obtain ⟨hv, hvv⟩ := hv'
  subst hvv
  simp only [unpack]
  obtain ⟨r, st₁, hrun, hsat, hnv, hle, hscope, hreads⟩ :=
    witness_complete (c := c) (unpack.advice v n) (st := st)
      (v := unpackPure (v.val st.env.get) n)
      (by simp) (by simp [unpack.advice, hv])
  refine ⟨r, st₁, hrun.bind rfl, ?_, hscope, hreads⟩
  intro stf hnv' hle'
  refine Sat.bind hrun (hsat hnv' hle')
    (Sat.bind Runs.addConstraint (Sat.addConstraint ?_) Sat.pure)
  refine (LawfulBasicSystem.holds_r1cs ..).mpr ?_
  have hbits := CircuitType.reads_vector.mp (hreads.of_le hscope hle')
  rw [CVar.val_of_le (hle.trans hle') hv, ← packPure_unpackPure (F := F) (n := n) hlt]
  rw [pack_val (bs := unpackPure (v.val st.env.get) n)
    fun i hi => CircuitType.reads_boolVar.mp (hbits i hi)]
  simp

attribute [irreducible] unpack

/-- The rows `unpack` emits, in order: one `boolean` per bit, then the packing row. -/
example [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] (v : FVar F) (nv : Nat) :
    (build (unpack (c := c) v 2) nv).constraints =
      (let bits := (build (unpack (c := c) v 2) nv).result
       [BasicSystem.boolean bits[0].toCVar, BasicSystem.boolean bits[1].toCVar,
        BasicSystem.r1cs (pack bits) (.const 1) v]) := by
  unfold unpack
  simp only [build_bind, build, witness, Snarky.addConstraint]
  rfl

end Snarky
