import Snarky.Circuit.DSL.Field
import Kimchi.Bits
import Mathlib.Data.ZMod.Basic

/-!
# Bit packing and unpacking

Port of `Snarky.Circuit.DSL.Bits` (packages/snarky/src/Snarky/Circuit/DSL/Bits.purs):
LSB-first bit decomposition and recomposition. `unpack` witnesses `n` CHECKED booleans
(each through `witness` at `Bool`, paying its `boolean` row) and pins their weighted
sum `Σ 2ⁱ·bᵢ` to the operand with one `r1cs` row; `pack` is the pure weighted-sum
expression; the `Pure` variants are the value-level mirrors.

Name map: `unpack_` → `unpack`, `pack_` → `pack`; `unpackPure`/`packPure` keep their PS
names. The bit width is an explicit `Nat` argument (PS reflects a type-level `n`).

Deviations from the PS original (ledger: `formal/docs/snarky-ps-alignment.md`):
- PS reads the canonical integer representative through `PrimeField.toBigInt`; the port
  has no curve-class layer, so the one fragment these gadgets need lands here as
  `Snarky.ToNat`, with its laws as `Snarky.LawfulToNat` (the representative casts back,
  and lies below the field's `card`). Width (`toNat x < 2 ^ n`) stays a per-law
  hypothesis — it is about the operand, not the reader.
- The weighted-sum folds carry their index explicitly (`packAux`), mirroring PS's
  `mapWithIndex` fold — same expression tree, LSB first.

`unpack_spec` pins any satisfying assignment's bits: boolean, and summing to the
operand (their canonicity additionally needs a characteristic hypothesis and is not
stated). `unpack_complete_spec` runs the honest prover through the `ToNat` witness.
Both walk the gadget's do-block through the vector loop rules;
`unpackWit`/`packAux` are named internals for the laws.
-/

namespace Snarky

export Kimchi (natLsbVal natLsbVal_lt natLsbVal_append_singleton natLsbVal_ofFn_testBit
  natLsbVal_testBit_range natLsbVal_take_testBit_range natLsbVal_take_drop natLsbVal_take_eq_mod
  natLsbVal_eq_zero natLsbVal_lt_of_drop_false ofFn_val_eq_map_range)

variable {F c : Type u}

/-! ## The canonical representative -/

/-- The canonical `Nat` representative of a field element — the one fragment of PS
`PrimeField` (`toBigInt`) the bit gadgets need; `LawfulToNat` carries its laws. -/
class ToNat (F : Type u) where
  /-- The canonical representative (PS `toBigInt`; `ZMod.val` at concrete fields). -/
  toNat : F → Nat

/-- `ToNat`'s laws at a field of `card` elements: the representative casts back to its
element, and every representative lies below `card` (`ZMod.val` at a prime field). -/
class LawfulToNat (F : Type u) [NatCast F] [ToNat F] where
  /-- The representatives' bound — the field's cardinality. -/
  card : Nat
  /-- The representative casts back to its element. -/
  cast_toNat : ∀ x : F, ((ToNat.toNat x : Nat) : F) = x
  /-- Every representative lies below `card`. -/
  toNat_lt : ∀ x : F, ToNat.toNat x < card
  /-- Below `card`, a number is its own cast's representative. -/
  toNat_natCast : ∀ n : Nat, n < card → ToNat.toNat ((n : Nat) : F) = n

/-- The canonical representative at a `ZMod` modulus is `ZMod.val` — every deployed
field reads through this one instance. -/
instance instToNatZMod (p : Nat) : ToNat (ZMod p) := ⟨ZMod.val⟩

/-- `ZMod.val` is lawful at every nonzero modulus: it casts back, and lies below `p`. -/
instance instLawfulToNatZMod (p : Nat) [NeZero p] : LawfulToNat (ZMod p) :=
  ⟨p, fun x => ZMod.natCast_zmod_val x, fun x => ZMod.val_lt x, fun n hn => by
    show ZMod.val ((n : Nat) : ZMod p) = n
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]⟩

/-- A representative pinned by its cast: below `card` the cast is injective, so the
element's representative is the pinned number — the canonical reading of a lock. -/
theorem toNat_eq_of_natCast_eq [NatCast F] [ToNat F] [LawfulToNat F] {n : Nat} {x : F}
    (h : ((n : Nat) : F) = x) (hn : n < LawfulToNat.card (F := F)) : ToNat.toNat x = n := by
  rw [← h, LawfulToNat.toNat_natCast n hn]

/-! ## The gadgets -/

/-- `unpack`'s per-bit witness computation: bit `i` of the operand's canonical
representative. -/
private def unpackWit {F : Type} [Add F] [Mul F] [ToNat F] (v : FVar F) (i : Nat) :
    AsProver F Bool := do
  let vv ← AsProver.readCVar v
  pure ((ToNat.toNat vv).testBit i)

/-- The weighted-sum expression `acc + Σⱼ 2^(i+j)·bits[j]`, LSB first — the indexed
fold shared by `pack` and `unpack`'s constraint (PS's `mapWithIndex` fold). -/
private def packAux [Semiring F] [DecidableEq F] : List (BoolVar F) → Nat → FVar F → FVar F
  | [], _, acc => acc
  | b :: bs, i, acc =>
    packAux bs (i + 1) (CVar.add_ acc (CVar.scale_ ((2 : F) ^ i) ↑b))

/-- Pack bits into their weighted sum `Σ 2ⁱ·bᵢ`, LSB first — pure, no constraints
(PS `pack_`). -/
def pack [Semiring F] [DecidableEq F] {n : Nat} (bits : Vector (BoolVar F) n) : FVar F :=
  packAux bits.toList 0 (.const 0)

/-- Pack the low `k` bits of an `n`-bit vector, LSB first — pure, no constraints.
Irreducible: consumers read it through `packLow_eval`/`packLow_val`, never by opening
the fold. -/
@[irreducible] def packLow [Semiring F] [DecidableEq F] {n : Nat} (k : Nat) (hk : k ≤ n)
    (bits : Vector (BoolVar F) n) : FVar F :=
  pack (Vector.ofFn fun i : Fin k => bits[i.val]'(lt_of_lt_of_le i.isLt hk))

/-- Decompose a field variable into `n` LSB-first bits (PS `unpack_`): witness each bit
CHECKED (`witness` at `Bool` pays the `boolean` row), then pin the weighted sum to the
operand with one `r1cs` row. -/
def unpack {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c]
    (v : FVar F) (n : Nat) : CircuitM F c (Vector (BoolVar F) n) := do
  let bits ← generateVec n fun i => witness (val := Bool) (unpackWit v i.val)
  addConstraint (BasicSystem.r1cs (pack bits) (.const 1) v)
  pure bits

/-- The value-level unpacking: bit `i` of the canonical representative (PS
`unpackPure`). -/
def unpackPure [ToNat F] (x : F) (n : Nat) : Vector Bool n :=
  Vector.ofFn fun i => (ToNat.toNat x).testBit i.val

/-- The value-level indexed fold under `packPure`. -/
private def packPureAux [Semiring F] : List Bool → Nat → F → F
  | [], _, acc => acc
  | b :: bs, i, acc => packPureAux bs (i + 1) (acc + (2 : F) ^ i * bit b)

/-- The value-level packing `Σ 2ⁱ·bᵢ` (PS `packPure`). -/
def packPure [Semiring F] {n : Nat} (bs : Vector Bool n) : F :=
  packPureAux bs.toList 0 0

/-! ## The pure laws -/

/-- The circuit fold evaluates to the value fold. -/
private theorem packAux_eval {F : Type u} [Semiring F] [DecidableEq F]
    {env : Assignments F} :
    ∀ (l : List (BoolVar F)) (bl : List Bool) (i : Nat) (acc : CVar F) (accv : F),
      l.map (fun b => b.toCVar.eval env) = bl.map (fun b => .ok (bit b)) →
      acc.eval env = .ok accv →
      (packAux l i acc).eval env = .ok (packPureAux bl i accv) := by
  intro l
  induction l with
  | nil =>
    intro bl i acc accv hmap hacc
    cases bl with
    | nil => simpa [packAux, packPureAux] using hacc
    | cons _ _ => cases hmap
  | cons b l ih =>
    intro bl i acc accv hmap hacc
    cases bl with
    | nil => cases hmap
    | cons bv bl =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hb, hrest⟩ := hmap
      refine ih bl (i + 1) _ _ hrest ?_
      rw [CVar.eval_add_fold]
      have hs := CVar.eval_scale_ hb ((2 : F) ^ i)
      simp only [CVar.eval, hacc, hs]

/-- `pack` evaluation: the pure gadget computes the weighted bit-sum — if each
bit variable evaluates to its bit's encoding, `pack` evaluates to `packPure`. -/
theorem pack_eval {F : Type u} [Semiring F] [DecidableEq F] {n : Nat}
    {bits : Vector (BoolVar F) n} {bs : Vector Bool n} {env : Assignments F}
    (h : ∀ i (hi : i < n), (bits[i].toCVar).eval env = .ok (bit bs[i])) :
    (pack bits).eval env = .ok (packPure bs) := by
  have hmap : bits.toList.map (fun b => b.toCVar.eval env)
      = bs.toList.map (fun b => Except.ok (bit b)) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, Vector.getElem_toList]
    exact h i (by simpa using h1)
  simpa [pack, packPure] using packAux_eval bits.toList bs.toList 0 _ _ hmap rfl

/-- The indexed value fold is the shifted Horner form, through the cast. -/
private theorem packPureAux_horner {F : Type u} [CommSemiring F] :
    ∀ (bl : List Bool) (i : Nat) (accv : F),
      packPureAux bl i accv = accv + (2 : F) ^ i * (natLsbVal bl : F) := by
  intro bl
  induction bl with
  | nil => intro i accv; simp [packPureAux, natLsbVal]
  | cons b bl ih =>
    intro i accv
    rw [packPureAux, ih, natLsbVal]
    cases b <;> simp [bit] <;> ring

/-- `packPure` is the cast of the ℕ Horner value. -/
theorem packPure_natCast {F : Type u} [CommSemiring F] {n : Nat} (bs : Vector Bool n) :
    packPure bs = ((natLsbVal bs.toList : Nat) : F) := by
  rw [packPure, packPureAux_horner]
  simp

/-- The pure round trip: packing the unpacking is the identity, given the
representative fits in `n` bits — the boundary
library's decode-encode law. -/
theorem packPure_unpackPure {F : Type u} [CommSemiring F] [ToNat F] [LawfulToNat F]
    {n : Nat} {x : F} (hlt : ToNat.toNat x < 2 ^ n) :
    packPure (unpackPure x n) = x := by
  rw [packPure, unpackPure, Vector.toList_ofFn, packPureAux_horner,
    natLsbVal_ofFn_testBit n _ hlt]
  simpa using LawfulToNat.cast_toNat x

/-- The digits of a fitting representative Horner-fold back to it. -/
theorem natLsbVal_unpackPure {F : Type u} [ToNat F] {n : Nat} {x : F}
    (hlt : ToNat.toNat x < 2 ^ n) :
    natLsbVal (unpackPure x n).toList = ToNat.toNat x := by
  rw [unpackPure, Vector.toList_ofFn]
  exact natLsbVal_ofFn_testBit n _ hlt

/-- The low `k` digits of a representative Horner-fold to its residue mod `2^k`. -/
theorem natLsbVal_take_unpackPure {F : Type u} [ToNat F] {n k : Nat} (hk : k ≤ n) (x : F) :
    natLsbVal ((unpackPure x n).toList.take k) = ToNat.toNat x % 2 ^ k := by
  rw [unpackPure, Vector.toList_ofFn, ofFn_val_eq_map_range, natLsbVal_take_testBit_range _ hk]

/-- The low slice of a vector, `ofFn`-spelled, is `toList.take`. -/
theorem toList_ofFn_take {α : Type u} {n : Nat} (k : Nat) (hk : k ≤ n) (v : Vector α n) :
    (Vector.ofFn fun i : Fin k => v[i.val]'(lt_of_lt_of_le i.isLt hk)).toList
      = v.toList.take k := by
  rw [Vector.toList_ofFn]
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_take, Vector.length_toList]
    omega
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_take, Vector.getElem_toList]

/-- `packLow` evaluation: the low bits' value, cast. -/
theorem packLow_eval {F : Type u} [CommSemiring F] [DecidableEq F] {n k : Nat} (hk : k ≤ n)
    {bits : Vector (BoolVar F) n} {bs : Vector Bool n} {env : Assignments F}
    (h : ∀ i (hi : i < n), (bits[i].toCVar).eval env = .ok (bit bs[i])) :
    (packLow k hk bits).eval env = .ok ((natLsbVal (bs.toList.take k) : Nat) : F) := by
  unfold packLow
  rw [pack_eval (bs := Vector.ofFn fun i : Fin k => bs[i.val]'(lt_of_lt_of_le i.isLt hk))
    (fun i hi => by simp only [Vector.getElem_ofFn]; exact h i (lt_of_lt_of_le hi hk)),
    packPure_natCast, toList_ofFn_take k hk]

/-! ## The circuit laws -/

/-- `pack` reads as the pure packing — `pack_eval` carried across the bridge to the
total reading. -/
theorem pack_val {F : Type} [Semiring F] [DecidableEq F] {n : Nat}
    {bits : Vector (BoolVar F) n} {bs : Vector Bool n} {V : Valuation F}
    (h : ∀ i (hi : i < n), (bits[i].toCVar).val V = bit bs[i]) :
    (pack bits).val V = packPure bs := by
  have h' : ∀ i (hi : i < n), (bits[i].toCVar).eval V.toAssignments = .ok (bit bs[i]) := by
    intro i hi
    rw [CVar.eval_toAssignments, h i hi]
  have := pack_eval (bits := bits) (bs := bs) (env := V.toAssignments) h'
  rw [CVar.eval_toAssignments] at this
  injection this

/-- `packLow` reads as the cast of the low bits' value. -/
theorem packLow_val {F : Type} [CommSemiring F] [DecidableEq F] {n k : Nat} (hk : k ≤ n)
    {bits : Vector (BoolVar F) n} {bs : Vector Bool n} {V : Valuation F}
    (h : ∀ i (hi : i < n), (bits[i].toCVar).val V = bit bs[i]) :
    (packLow k hk bits).val V = ((natLsbVal (bs.toList.take k) : Nat) : F) := by
  unfold packLow
  rw [pack_val (bs := Vector.ofFn fun i : Fin k => bs[i.val]'(lt_of_lt_of_le i.isLt hk))
    (fun i hi => by simp only [Vector.getElem_ofFn]; exact h i (lt_of_lt_of_le hi hk)),
    packPure_natCast, toList_ofFn_take k hk]

open Std.Do in
/-- `unpack`'s emitted rows force the results to be bits whose weighted sum is the
operand's reading. Their canonicity — that they are the binary digits — additionally
needs a characteristic hypothesis and is not stated. -/
@[spec] theorem unpack_spec {F c : Type} {V : Valuation F} [Field F] [DecidableEq F] [ToNat F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (v : FVar F) (n : Nat) :
    ⦃⌜True⌝⦄
    unpack (c := Builder V c) v n
    ⦃⇓ r _ => ⌜∃ bs : Vector Bool n,
        (∀ i (hi : i < n), (r[i].toCVar).val V = bit bs[i]) ∧
          packPure bs = v.val V⌝⦄ := by
  simp only [unpack]
  have hgen := generateVec_spec (V := V) n (fun i => witness (val := Bool) (unpackWit v i.val))
    (fun _ (r : BoolVar F) => (↑r : CVar F).val V = 0 ∨ (↑r : CVar F).val V = 1)
    (fun i => witness_spec (c := c) (unpackWit v i.val))
  mvcgen [hgen]
  rename_i bits _ hbitness _ _ hrow
  have hbits : ∀ i (hi : i < n), (bits[i].toCVar).val V
      = bit (decide ((bits[i].toCVar).val V = 1)) := by
    intro i hi
    have h := hbitness ⟨i, hi⟩
    simp only [Fin.getElem_fin] at h
    rcases h with h0 | h1
    · rw [h0]; simp [bit, zero_ne_one]
    · rw [h1]; simp [bit]
  refine ⟨Vector.ofFn fun i : Fin n =>
    decide ((bits[i].toCVar).val V = 1), fun i hi => ?_, ?_⟩
  · simp only [Vector.getElem_ofFn]
    exact hbits i hi
  · have hrow' := LawfulBasicSystem.holds_r1cs (c := c) V _ _ _ hrow
    have hpack : (pack bits).val V
        = packPure (Vector.ofFn fun i : Fin n =>
          decide ((bits[i].toCVar).val V = 1)) := by
      refine pack_val fun i hi => ?_
      simp only [Vector.getElem_ofFn]
      exact hbits i hi
    rw [hpack] at hrow'
    simpa [circuitVal] using hrow'

open Std.Do in
/-- `unpack`'s honest run succeeds on a representative that fits in `n` bits;
the results are the operand's binary digits. -/
@[spec] theorem unpack_complete_spec {F c : Type} [Field F] [DecidableEq F] [ToNat F]
    [LawfulToNat F] [BasicSystem F c] [Checker F c] [LawfulChecker F c]
    (v : FVar F) (n : Nat)
    (Q : PostCond (Vector (BoolVar F) n)
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (v.eval env).isOk ∧
          ∀ vv, v.eval env = .ok vv →
            ToNat.toNat vv < 2 ^ n)
        (fun env r env' => ∀ vv, v.eval env = .ok vv →
          ∀ i (hi : i < n), (r[i]).toCVar.eval env'
            = .ok (bit ((ToNat.toNat vv).testBit i))) Q⦄
    unpack (c := Prover c) v n
    ⦃Q⦄ := by
  simp only [unpack]
  intro st hpre
  obtain ⟨⟨hokv, hfaithful⟩, hk⟩ := hpre
  obtain ⟨vv, hv⟩ := CVar.evalOk hokv
  have hlt := hfaithful vv hv
  simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
  -- the component: the checked-bit witness computes the operand's `i`-th digit
  have hcomp : ∀ (i : Fin n)
      (Q : PostCond (BoolVar F) (.arg (ProverState F) (.except EvalError .pure))),
      ⦃Complete (fun env => (v.eval env).isOk)
        (fun env (r : BoolVar F) env' => ∀ vv', v.eval env = .ok vv' →
          (↑r : CVar F).eval env' = .ok (bit ((ToNat.toNat vv').testBit i.val))) Q⦄
      (witness (val := Bool) (unpackWit v i.val) : CircuitM F (Prover c) (BoolVar F))
      ⦃Q⦄ := by
    intro i Q st' hpre'
    obtain ⟨hok', hk'⟩ := hpre'
    obtain ⟨vv', hv'⟩ := CVar.evalOk hok'
    have hw : (unpackWit v i.val).run st'.env = .ok ((ToNat.toNat vv').testBit i.val) := by
      simp [unpackWit, hv', Bind.bind, Except.bind,
        Pure.pure]
    refine witness_complete_spec (val := Bool) _ _ st'
      ⟨show ((unpackWit v i.val).run st'.env).isOk = true by rw [hw]; rfl,
        fun r st'' hr hle => ?_⟩
    refine hk' r st'' (fun vv'' hv'' => ?_) hle
    rw [hv'] at hv''
    injection hv'' with hv''
    subst hv''
    exact hr _ hw
  refine generateVec_complete_spec n _ _ _ hcomp
    (fun i env env' hle hok => by
      obtain ⟨vv', hv'⟩ := CVar.evalOk hok
      rw [CVar.eval_le hle hv']
      rfl)
    (fun i e₀ e₁ r e₂ e₃ h01 h23 hpost vv' hv₀ =>
      CVar.eval_le h23 (hpost vv' (CVar.eval_le h01 hv₀))) _ st
    ⟨fun _ => hokv, fun bits st₁ hbits hle₁ => ?_⟩
  -- after the loop: the packing row accepts, and the caller reads the digits
  dsimp only
  have hv₁ : v.eval st₁.env = .ok vv := CVar.eval_le hle₁ hv
  have hbitEval : ∀ i (hi : i < n), (bits[i].toCVar).eval st₁.env
      = .ok (bit ((ToNat.toNat vv).testBit i)) := by
    intro i hi
    have h := hbits ⟨i, hi⟩ vv hv
    simpa only [Fin.getElem_fin] using h
  have hpack : (pack bits).eval st₁.env = .ok (packPure (unpackPure vv n)) := by
    refine pack_eval fun i hi => ?_
    simp only [unpackPure, Vector.getElem_ofFn]
    exact hbitEval i hi
  have hch : Checker.holds (F := F) (c := c)
      (BasicSystem.r1cs (c := c) (pack bits) (.const 1) v) st₁.env = true := by
    rw [packPure_unpackPure hlt] at hpack
    exact LawfulChecker.check_r1cs _ _ _ _ _ _ _ hpack (by rfl) hv₁ (mul_one vv)
  refine addConstraint_complete_spec (c := c) _ _ st₁ ⟨hch, fun _ st₂ _ hle₂ => ?_⟩
  intro _
  refine hk bits st₂ (fun vv' hv' => ?_) (hle₁.trans hle₂)
  rw [hv] at hv'
  injection hv' with hv'
  subst hv'
  intro i hi
  exact CVar.eval_le hle₂ (hbitEval i hi)

/-- Per-index bit readings of a vector, as the `Forall₂` a bit-list assertion consumes
at a valuation. -/
theorem forall₂_bit_of_reads [Field F] {n : Nat} {V : Valuation F}
    {v : Vector (FVar F) n} {bs : Vector Bool n}
    (h : ∀ i (hi : i < n), (v[i]).val V = bit bs[i]) :
    List.Forall₂ (fun (x : BoolVar F) (b : Bool) => (↑x : CVar F).val V = bit b)
      (v.toList.map .unchecked) bs.toList := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h1 h2 => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_map, Vector.getElem_toList,
    BoolVar.toCVar_unchecked]
  exact h i (by simpa using h2)

/-- Per-index bit evaluations of a vector against a bit function, as the `Forall₂` a
bit-list assertion's honest run consumes. -/
theorem forall₂_bit_of_evals [Field F] {n : Nat} {env : Assignments F}
    {v : Vector (FVar F) n} {f : Nat → Bool}
    (h : ∀ i (hi : i < n), (v[i]).eval env = .ok (bit (f i))) :
    List.Forall₂ (fun (x : BoolVar F) (b : Bool) => (↑x : CVar F).eval env = .ok (bit b))
      (v.toList.map .unchecked) ((List.range n).map f) := by
  rw [List.forall₂_iff_get]
  constructor
  · rw [List.length_map, Vector.length_toList, List.length_map, List.length_range]
  · intro i h1 h2
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range,
      BoolVar.toCVar_unchecked, Vector.getElem_toList]
    exact h i (by simpa using h2)

end Snarky
