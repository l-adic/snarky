import Snarky.Circuit.DSL.Field

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
  `Snarky.ToNat`. Its faithfulness (`(toNat x : F) = x`) and width (`toNat x < 2 ^ n`)
  enter the laws as hypotheses, dischargeable at any concrete prime field (`ZMod.val`).
- The weighted-sum folds carry their index explicitly (`packAux`), mirroring PS's
  `mapWithIndex` fold — same expression tree, LSB first.

`unpack_spec` pins any satisfying assignment's bits: boolean, and summing to the
operand (their canonicity additionally needs a characteristic hypothesis and is not
stated). `unpack_complete_spec` runs the honest prover through the `ToNat` witness.
Both walk the gadget's do-block through the vector loop rules;
`unpackWit`/`packAux` are named internals for the laws.
-/

namespace Snarky

variable {F c : Type u}

/-! ## The canonical representative -/

/-- The canonical `Nat` representative of a field element — the one fragment of PS
`PrimeField` (`toBigInt`) the bit gadgets need. Faithfulness and width are law-side
hypotheses, not class laws (see the module docstring). -/
class ToNat (F : Type u) where
  /-- The canonical representative (PS `toBigInt`; `ZMod.val` at concrete fields). -/
  toNat : F → Nat

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
      rw [CVar.eval_add_]
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

/-- The Horner form of the bit-sum. -/
private def natHorner : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * natHorner bs

/-- The indexed value fold is the shifted Horner form, through the cast. -/
private theorem packPureAux_horner {F : Type u} [CommSemiring F] :
    ∀ (bl : List Bool) (i : Nat) (accv : F),
      packPureAux bl i accv = accv + (2 : F) ^ i * (natHorner bl : F) := by
  intro bl
  induction bl with
  | nil => intro i accv; simp [packPureAux, natHorner]
  | cons b bl ih =>
    intro i accv
    rw [packPureAux, ih, natHorner]
    cases b <;> simp [bit] <;> ring

/-- The Horner form reconstructs a number from its bits. -/
private theorem natHorner_testBit :
    ∀ (n m : Nat), m < 2 ^ n →
      natHorner (List.ofFn fun i : Fin n => m.testBit i.val) = m := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have h0 : m = 0 := by omega
    subst h0
    rfl
  | succ n ih =>
    intro m hm
    simp only [List.ofFn_succ, Fin.val_zero, Fin.val_succ]
    have htail : (List.ofFn fun i : Fin n => m.testBit (i.val + 1))
        = List.ofFn fun i : Fin n => (m / 2).testBit i.val := by
      congr 1
      funext i
      simp [Nat.testBit_add_one]
    rw [htail, natHorner, ih (m / 2) (by rw [pow_succ] at hm; omega)]
    have hbit := Nat.bit_testBit_zero_shiftRight_one m
    rw [Nat.shiftRight_one] at hbit
    cases htb : m.testBit 0 <;> rw [htb] at hbit <;> simp [Nat.bit] at hbit <;>
      simp <;> omega

/-- The pure round trip: packing the unpacking is the identity, given the
representative is faithful (`(toNat x : F) = x`) and fits in `n` bits — the boundary
library's decode-encode law. -/
theorem packPure_unpackPure {F : Type u} [CommSemiring F] [ToNat F] {n : Nat} {x : F}
    (hval : ((ToNat.toNat x : Nat) : F) = x) (hlt : ToNat.toNat x < 2 ^ n) :
    packPure (unpackPure x n) = x := by
  rw [packPure, unpackPure, Vector.toList_ofFn, packPureAux_horner,
    natHorner_testBit n _ hlt]
  simpa using hval

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

open Std.Do in
/-- The emitted rows force the results to be bits whose weighted sum is the
operand's reading. Their canonicity — that they are the binary digits — additionally
needs a characteristic hypothesis and is not stated. -/
@[spec] theorem unpack_spec {F c : Type} [Field F] [DecidableEq F] [ToNat F]
    [BasicSystem F c] [ConstraintHolds F c] [LawfulBasicSystem F c]
    (v : FVar F) (n : Nat)
    (Q : PostCond (Vector (BoolVar F) n) (.arg (BuilderState F) .pure)) :
    ⦃Sound (fun V (r : Vector (BoolVar F) n) => ∃ bs : Vector Bool n,
        (∀ i (hi : i < n), (r[i].toCVar).val V = bit bs[i]) ∧
          packPure bs = v.val V) Q⦄
    unpack (c := c) v n
    ⦃Q⦄ := by
  simp only [unpack]
  intro s hpre
  simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
  refine generateVec_spec n _ _ (fun i Q => witnessBool_spec (unpackWit v i.val) Q) _ s
    (fun bits nv₁ hbitness => ?_)
  simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
  refine addConstraint_spec _ _ ⟨s.V, nv₁⟩ (fun _ nv₂ hrow => ?_)
  intro _
  have hbits : ∀ i (hi : i < n), (bits[i].toCVar).val s.V
      = bit (decide ((bits[i].toCVar).val s.V = 1)) := by
    intro i hi
    have h := hbitness ⟨i, hi⟩
    simp only [Fin.getElem_fin] at h
    rcases h with h0 | h1
    · rw [h0]; simp [bit, zero_ne_one]
    · rw [h1]; simp [bit]
  refine hpre bits nv₂ ⟨Vector.ofFn fun i : Fin n =>
    decide ((bits[i].toCVar).val s.V = 1), fun i hi => ?_, ?_⟩
  · simp only [Vector.getElem_ofFn]
    exact hbits i hi
  · have hrow' := LawfulBasicSystem.holds_r1cs (c := c) s.V _ _ _ hrow
    have hpack : (pack bits).val s.V
        = packPure (Vector.ofFn fun i : Fin n =>
          decide ((bits[i].toCVar).val s.V = 1)) := by
      refine pack_val fun i hi => ?_
      simp only [Vector.getElem_ofFn]
      exact hbits i hi
    rw [hpack] at hrow'
    simpa [circuitVal] using hrow'

open Std.Do in
/-- On a faithful representative
that fits in `n` bits, the honest run succeeds and the results are the operand's
binary digits. -/
@[spec] theorem unpack_complete_spec {F : Type} [Field F] [DecidableEq F] [ToNat F]
    (v : FVar F) (n : Nat)
    (Q : PostCond (Vector (BoolVar F) n)
      (.arg (ProverState F) (.except EvalError .pure))) :
    ⦃Complete
        (fun env => (v.eval env).isOk ∧
          ∀ vv, v.eval env = .ok vv →
            ((ToNat.toNat vv : Nat) : F) = vv ∧ ToNat.toNat vv < 2 ^ n)
        (fun env r env' => ∀ vv, v.eval env = .ok vv →
          ∀ i (hi : i < n), (r[i]).toCVar.eval env'
            = .ok (bit ((ToNat.toNat vv).testBit i))) Q⦄
    unpack (c := ProverC F) v n
    ⦃Q⦄ := by
  simp only [unpack]
  intro st hpre
  obtain ⟨⟨hokv, hfaithful⟩, hk⟩ := hpre
  obtain ⟨vv, hv⟩ := CVar.evalOk hokv
  obtain ⟨hval, hlt⟩ := hfaithful vv hv
  simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
  -- the component: the checked-bit witness computes the operand's `i`-th digit
  have hcomp : ∀ (i : Fin n)
      (Q : PostCond (BoolVar F) (.arg (ProverState F) (.except EvalError .pure))),
      ⦃Complete (fun env => (v.eval env).isOk)
        (fun env (r : BoolVar F) env' => ∀ vv', v.eval env = .ok vv' →
          (↑r : CVar F).eval env' = .ok (bit ((ToNat.toNat vv').testBit i.val))) Q⦄
      (witness (val := Bool) (unpackWit v i.val) : CircuitM F (ProverC F) (BoolVar F))
      ⦃Q⦄ := by
    intro i Q st' hpre'
    obtain ⟨hok', hk'⟩ := hpre'
    obtain ⟨vv', hv'⟩ := CVar.evalOk hok'
    have hw : unpackWit v i.val st'.env = .ok ((ToNat.toNat vv').testBit i.val) := by
      simp [unpackWit, AsProver.readCVar, hv', Bind.bind, ReaderT.bind, Except.bind,
        Pure.pure, ReaderT.pure, Except.pure]
    refine witnessBool_complete_spec _ _ st'
      ⟨show (unpackWit v i.val st'.env).isOk = true by rw [hw]; rfl,
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
  simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
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
  have hch : Basic.holds
      (BasicSystem.r1cs (c := ProverC F) (pack bits) (.const 1) v) st₁.env = true := by
    show Basic.holds (.r1cs _ _ _) st₁.env = true
    rw [packPure_unpackPure hval hlt] at hpack
    simp [Basic.holds, hpack, CVar.eval, hv₁]
  refine addConstraint_complete_spec _ _ st₁ ⟨hch, fun _ st₂ _ hle₂ => ?_⟩
  intro _
  refine hk bits st₂ (fun vv' hv' => ?_) (hle₁.trans hle₂)
  rw [hv] at hv'
  injection hv' with hv'
  subst hv'
  intro i hi
  exact CVar.eval_le hle₂ (hbitEval i hi)

end Snarky
