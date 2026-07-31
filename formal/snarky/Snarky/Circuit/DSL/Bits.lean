import Snarky.Circuit.DSL.Field

/-!
# Bit packing and unpacking

Port of `Snarky.Circuit.DSL.Bits` (packages/snarky/src/Snarky/Circuit/DSL/Bits.purs):
LSB-first bit decomposition and recomposition. `unpack` witnesses `n` CHECKED booleans
(each through `witness` at `Bool`, paying its `boolean` row) and pins their weighted sum
`Σ 2ⁱ·bᵢ` to the operand with one `r1cs` row; `pack` is the pure weighted-sum
expression; the `Pure` variants are the value-level mirrors.

These are the faithfulness arc's boundary engines
(`formal/docs/circuit-verifier-faithfulness.md`): challenge bit-packs cross the field
boundary through exactly these round trips.

Name map (D7): `unpack_` → `unpack`, `pack_` → `pack`, `unpackPure`/`packPure` keep
their PS names. The bit width is an explicit `Nat` argument (PS reflects a type-level
`n`); the result is the same sized `Vector`.

Deviations from the PS original (per `formal/docs/snarky-ps-alignment.md`):
- PS reads the canonical integer representative through `PrimeField.toBigInt`; the port
  has no curve-class layer, so the ONE fragment these gadgets need lands here as
  `Snarky.ToNat` — the canonical `Nat` representative. Its faithfulness (`(toNat x : F)
  = x`) and width (`toNat x < 2 ^ n`) enter the laws as hypotheses, dischargeable at any
  concrete prime field (`ZMod.val` with `ZMod.natCast_val` and the modulus bound); the
  `FieldSizeInBits` class the plan defers to `SizedF` (§6) will build on it.
- The weighted-sum folds carry their index explicitly (`packAux`), mirroring PS's
  `mapWithIndex` fold — same expression tree, LSB first.

D9 survey (the `snarky-test-utils` Bits spec), in the D12 form, laws beside the
gadgets: the pure round trip `packPure_unpackPure` closes the spec's round-trip row at
the value level under the `ToNat` faithfulness hypotheses; `pack_eval` is the pure
gadget's evaluation law (like `sum_eval`); `unpack_sound` pins any satisfying
assignment's bits — boolean, and summing to the operand (their CANONICITY additionally
needs the standing characteristic hypothesis, recorded with the other sum-based
obligations); `unpack_complete` runs the honest prover through the `ToNat` witness.

Public results: `pack_eval`, `packPure_unpackPure`, `unpack_sound`, `unpack_complete` —
`roots.txt` entries; `unpackWit`/`packAux` are named internals for the laws.
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
representative. Public only for the gadget laws. -/
def unpackWit {F : Type} [Add F] [Mul F] [ToNat F] (v : FVar F) (i : Nat) :
    AsProver F Bool := do
  let vv ← AsProver.readCVar v
  pure ((ToNat.toNat vv).testBit i)

/-- The weighted-sum expression `acc + Σⱼ 2^(i+j)·bits[j]`, LSB first — the indexed
fold shared by `pack` and `unpack`'s constraint (PS's `mapWithIndex` fold). Public only
for the gadget laws. -/
def packAux [Semiring F] [DecidableEq F] : List (BoolVar F) → Nat → FVar F → FVar F
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

/-- The value-level indexed fold under `packPure`. Public only for the gadget laws. -/
def packPureAux [Semiring F] : List Bool → Nat → F → F
  | [], _, acc => acc
  | b :: bs, i, acc => packPureAux bs (i + 1) (acc + (2 : F) ^ i * bit b)

/-- The value-level packing `Σ 2ⁱ·bᵢ` (PS `packPure`). -/
def packPure [Semiring F] {n : Nat} (bs : Vector Bool n) : F :=
  packPureAux bs.toList 0 0

/-! ## The pure laws (D12) -/

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

/-- **`pack` evaluation** (D12): the pure gadget computes the weighted bit-sum — if each
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

/-- **The pure round trip** (D12): packing the unpacking is the identity, given the
representative is faithful (`(toNat x : F) = x`) and fits in `n` bits — the boundary
library's decode-encode law. -/
theorem packPure_unpackPure {F : Type u} [CommSemiring F] [ToNat F] {n : Nat} {x : F}
    (hval : ((ToNat.toNat x : Nat) : F) = x) (hlt : ToNat.toNat x < 2 ^ n) :
    packPure (unpackPure x n) = x := by
  rw [packPure, unpackPure, Vector.toList_ofFn, packPureAux_horner,
    natHorner_testBit n _ hlt]
  simpa using hval

/-! ## The circuit laws (D12) -/

/-- Pushing the last entry completes an `ofFn` vector. -/
private theorem ofFn_push {α : Type u} {n : Nat} (f : Fin (n + 1) → α) :
    (Vector.ofFn fun i : Fin n => f i.castSucc).push (f (Fin.last n))
      = Vector.ofFn f := by
  ext i hi
  simp only [Vector.getElem_push, Vector.getElem_ofFn]
  split
  · next h => simp [Fin.castSucc, Fin.castAdd, Fin.castLE]
  · next h =>
    have : i = n := by omega
    subst this
    simp [Fin.last]

/-- What one checked-`Bool` witness builds: a fresh variable and its `boolean` row. -/
private theorem build_witnessBool {F : Type} [Zero F] [One F] [DecidableEq F]
    (w : AsProver F Bool) (nv : Nat) :
    build (witness (val := Bool) w : CircuitM F (Basic F) (BoolVar F)) nv
      = ⟨.unchecked (.var nv), nv + 1, [.boolean (.var nv)]⟩ := rfl

/-- What the bit-witnessing prefix of `unpack` builds: `n` fresh variables, each with
its `boolean` row. -/
private theorem build_unpackBits {F : Type} [Field F] [DecidableEq F] [ToNat F]
    (v : FVar F) :
    ∀ (n nv : Nat),
      build (generateVec n (fun i => witness (val := Bool) (unpackWit v i.val)) :
          CircuitM F (Basic F) _) nv
        = ⟨Vector.ofFn (fun i : Fin n => BoolVar.unchecked (.var (nv + i.val))), nv + n,
           (List.range n).map fun i => .boolean (.var (nv + i))⟩ := by
  intro n
  induction n with
  | zero => intro nv; rfl
  | succ n ih =>
    intro nv
    show build ((generateVec n _ >>= fun init =>
      witness (val := Bool) (unpackWit v n) >>= fun last => pure (init.push last)) :
        CircuitM F (Basic F) _) nv = _
    rw [build_bind]
    simp only [Fin.val_castSucc]
    rw [ih nv, build_bind, build_witnessBool]
    refine Built.mk.injEq .. ▸ ⟨?_, ?_, ?_⟩
    · show (Vector.ofFn fun i : Fin n => BoolVar.unchecked (.var (nv + i.val))).push
        (BoolVar.unchecked (.var (nv + n))) = _
      exact ofFn_push fun i : Fin (n + 1) => BoolVar.unchecked (.var (nv + i.val))
    · rfl
    · show ((List.range n).map fun i => Basic.boolean (.var (nv + i)))
          ++ ([.boolean (.var (nv + n))] ++ []) = _
      rw [List.range_succ, List.map_append, List.append_nil]
      rfl

/-- What `unpack` builds: the bit rows then the packing row. -/
private theorem build_unpack {F : Type} [Field F] [DecidableEq F] [ToNat F]
    (v : FVar F) (n nv : Nat) :
    build (unpack (c := Basic F) v n) nv
      = ⟨Vector.ofFn (fun i : Fin n => BoolVar.unchecked (.var (nv + i.val))), nv + n,
         ((List.range n).map fun i => .boolean (.var (nv + i)))
           ++ [.r1cs
                (pack (Vector.ofFn fun i : Fin n => BoolVar.unchecked (.var (nv + i.val))))
                (.const 1) v]⟩ := by
  show build ((generateVec n (fun i => witness (val := Bool) (unpackWit v i.val))
      >>= fun bits => addConstraint (BasicSystem.r1cs (pack bits) (.const 1) v)
      >>= fun _ => pure bits) : CircuitM F (Basic F) _) nv = _
  rw [build_bind, build_unpackBits]
  rfl

/-- **`unpack` soundness** (D12): any satisfying assignment's bits are boolean and
their weighted sum is the operand's value. (Their CANONICITY — that they are THE binary
digits — additionally needs the standing characteristic hypothesis, with the other
sum-based obligations.) -/
theorem unpack_sound {F : Type} [Field F] [DecidableEq F] [ToNat F] {v : FVar F}
    {n nv : Nat} {env : Assignments F} {vv : F}
    (hsat : ∀ con ∈ (build (unpack (c := Basic F) v n) nv).constraints,
      con.holds env = true)
    (hv : v.eval env = .ok vv) :
    ∃ bs : Vector Bool n,
      (∀ i (hi : i < n),
        ((build (unpack (c := Basic F) v n) nv).result[i]).toCVar.eval env
          = .ok (bit bs[i])) ∧
      packPure bs = vv := by
  rw [build_unpack] at hsat ⊢
  refine ⟨Vector.ofFn fun i : Fin n => decide ((CVar.var (nv + i.val)).eval env = .ok 1),
    ?_, ?_⟩
  all_goals
    have hbits : ∀ i, i < n → (CVar.var (nv + i)).eval env
        = .ok (bit (decide ((CVar.var (nv + i)).eval env = .ok 1))) := by
      intro i hi
      obtain ⟨x, hx, hx01⟩ := Basic.boolean_inv
        (hsat _ (List.mem_append_left _ (List.mem_map_of_mem
          (List.mem_range.mpr hi))))
      rcases hx01 with h0 | h1
      · subst h0
        rw [hx]
        simp [bit, zero_ne_one]
      · subst h1
        rw [hx]
        simp [bit]
  · intro i hi
    simp only [Vector.getElem_ofFn]
    exact hbits i hi
  · obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := Basic.r1cs_inv
      (hsat _ (List.mem_append_right _ (List.mem_cons_self ..)))
    have hy1 : (1 : F) = y := by simpa [CVar.eval] using hy
    rw [hv] at hz
    injection hz with hz'
    have hxval : (pack (Vector.ofFn fun i : Fin n =>
        BoolVar.unchecked (.var (nv + i.val)))).eval env
        = .ok (packPure (Vector.ofFn fun i : Fin n =>
          decide ((CVar.var (nv + i.val)).eval env = .ok 1))) := by
      apply pack_eval
      intro i hi
      simp only [Vector.getElem_ofFn]
      exact hbits i hi
    rw [hxval] at hx
    injection hx with hx'
    rw [← hx', ← hy1, mul_one] at hxyz
    rw [hxyz, hz']

/-- The honest run of one checked-`Bool` witness: the `boolean` row always accepts a
bit. -/
private theorem prove_witnessBool {F : Type} [Field F] [DecidableEq F]
    {w : AsProver F Bool} {nv : Nat} {env : Assignments F} {b : Bool}
    (hw : w env = .ok b) (hfresh : env.FreshFrom nv) :
    prove Basic.holds (witness (val := Bool) w : CircuitM F (Basic F) (BoolVar F)) nv env
      = .ok ⟨.unchecked (.var nv), nv + 1, env.extend nv (bit b)⟩ := by
  have hnv : env nv = none := hfresh nv (Nat.le_refl nv)
  have hwit : (w env).map (CircuitType.valueToFields (F := F) (val := Bool))
      = .ok ⟨#[bit b], rfl⟩ := by rw [hw]; rfl
  have hext : env.extendPairs
      ((allocRange nv 1).toList.zip (⟨#[bit b], rfl⟩ : Vector F 1).toList)
      = .ok (env.extend nv (bit b)) := by
    show env.extendPairs [(nv, bit b)] = .ok _
    simp [Assignments.extendPairs, hnv]
  have hch : Basic.holds (.boolean (.var nv)) (env.extend nv (bit b)) = true := by
    cases b <;> simp [Basic.holds, CVar.eval, Assignments.extend, bit]
  show prove Basic.holds (.existsOp 1 (fun e => (w e).map _) _) nv env = _
  simp only [prove, hwit, hext]
  show prove Basic.holds
    (.addConstraintOp (.boolean (.var nv)) (.pure (BoolVar.unchecked (.var nv)))) (nv + 1)
    (env.extend nv (bit b)) = _
  simp only [prove, hch, if_true]

/-- The honest run of `unpack`'s bit-witnessing prefix. -/
private theorem prove_unpackBits {F : Type} [Field F] [DecidableEq F] [ToNat F]
    {v : FVar F} {vv : F} :
    ∀ (n nv : Nat) (env : Assignments F), env.FreshFrom nv → v.eval env = .ok vv →
      ∃ env', prove Basic.holds
          (generateVec n (fun i => witness (val := Bool) (unpackWit v i.val)) :
            CircuitM F (Basic F) _) nv env
        = .ok ⟨Vector.ofFn (fun i : Fin n => BoolVar.unchecked (.var (nv + i.val))),
            nv + n, env'⟩ ∧
        env.Le env' ∧ env'.FreshFrom (nv + n) ∧
        ∀ i, i < n → env' (nv + i) = some (bit ((ToNat.toNat vv).testBit i)) := by
  intro n
  induction n with
  | zero =>
    intro nv env hfresh hv
    exact ⟨env, rfl, Assignments.Le.refl env, hfresh, fun i hi => absurd hi (by omega)⟩
  | succ n ih =>
    intro nv env hfresh hv
    obtain ⟨env₁, hr₁, hle₁, hfresh₁, hbits₁⟩ := ih nv env hfresh hv
    have hv₁ : v.eval env₁ = .ok vv := CVar.eval_le hle₁ hv
    have hw : unpackWit v n env₁ = .ok ((ToNat.toNat vv).testBit n) := by
      simp [unpackWit, AsProver.readCVar, hv₁, Bind.bind, ReaderT.bind, Except.bind,
        Pure.pure, ReaderT.pure, Except.pure]
    refine ⟨env₁.extend (nv + n) (bit ((ToNat.toNat vv).testBit n)), ?_, ?_, ?_, ?_⟩
    · show prove Basic.holds ((generateVec n _ >>= fun init =>
        witness (val := Bool) (unpackWit v n) >>= fun last => pure (init.push last)) :
          CircuitM F (Basic F) _) nv env = _
      rw [prove_bind]
      simp only [Fin.val_castSucc]
      rw [hr₁]
      simp only [Except.bind]
      rw [prove_bind, prove_witnessBool hw hfresh₁]
      simp only [Except.bind, prove]
      congr 2
      exact ofFn_push fun i : Fin (n + 1) => BoolVar.unchecked (.var (nv + i.val))
    · refine hle₁.trans ?_
      intro w x hw'
      simp only [Assignments.extend]
      split
      · next h => rw [h, hfresh₁ (nv + n) (Nat.le_refl _)] at hw'; cases hw'
      · exact hw'
    · intro w hw'
      have h1 : w ≠ nv + n := by omega
      simp only [Assignments.extend, if_neg h1]
      exact hfresh₁ w (by omega)
    · intro i hi
      by_cases hin : i = n
      · subst hin
        simp [Assignments.extend]
      · have : nv + i ≠ nv + n := by omega
        simp only [Assignments.extend, if_neg this]
        exact hbits₁ i (by omega)

/-- **`unpack` completeness** (D12): on a faithful representative that fits in `n` bits,
the honest run succeeds, the bits are the operand's binary digits, and freshness is
re-established. -/
theorem unpack_complete {F : Type} [Field F] [DecidableEq F] [ToNat F] {v : FVar F}
    {n nv : Nat} {env : Assignments F} {vv : F}
    (hfresh : env.FreshFrom nv) (hv : v.eval env = .ok vv)
    (hval : ((ToNat.toNat vv : Nat) : F) = vv) (hlt : ToNat.toNat vv < 2 ^ n) :
    ∃ out, prove Basic.holds (unpack (c := Basic F) v n) nv env = .ok out ∧
      out.assignments.FreshFrom out.nextVar ∧
      ∀ i (hi : i < n), (out.result[i]).toCVar.eval out.assignments
        = .ok (bit ((ToNat.toNat vv).testBit i)) := by
  obtain ⟨env', hr, hle, hfresh', hbits⟩ := prove_unpackBits n nv env hfresh hv
  have hbitEval : ∀ i, i < n → (CVar.var (nv + i)).eval env'
      = .ok (bit ((ToNat.toNat vv).testBit i)) := by
    intro i hi
    simp [CVar.eval, hbits i hi]
  have hpack : (pack (Vector.ofFn fun i : Fin n =>
      BoolVar.unchecked (.var (nv + i.val)))).eval env'
      = .ok (packPure (unpackPure vv n)) := by
    apply pack_eval
    intro i hi
    simp only [Vector.getElem_ofFn, unpackPure]
    exact hbitEval i hi
  have hch : Basic.holds
      (BasicSystem.r1cs (pack (Vector.ofFn fun i : Fin n =>
        BoolVar.unchecked (.var (nv + i.val)))) (.const 1) v) env' = true := by
    show Basic.holds (.r1cs _ _ _) env' = true
    have hv' := CVar.eval_le hle hv
    rw [packPure_unpackPure hval hlt] at hpack
    simp [Basic.holds, hpack, CVar.eval, hv']
  refine ⟨⟨Vector.ofFn (fun i : Fin n => BoolVar.unchecked (.var (nv + i.val))),
    nv + n, env'⟩, ?_, hfresh', ?_⟩
  · show prove Basic.holds ((generateVec n (fun i =>
        witness (val := Bool) (unpackWit v i.val))
      >>= fun bits => addConstraint (BasicSystem.r1cs (pack bits) (.const 1) v)
      >>= fun _ => pure bits) : CircuitM F (Basic F) _) nv env = _
    rw [prove_bind, hr]
    simp only [Except.bind]
    show prove Basic.holds (.addConstraintOp _ (.pure _)) (nv + n) env' = _
    simp only [prove, hch, if_true]
  · intro i hi
    simp only [Vector.getElem_ofFn]
    exact hbitEval i hi

end Snarky
