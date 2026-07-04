import Kimchi.Circuits.VarBaseMulStep
import Kimchi.Circuits.AddCompleteStep

/-!
# Rung 1: the fully-public scale-and-combine circuit

The dumped `scale_combine` circuit pins *everything* to public inputs: rows 0–1 carry the base `T`
into the init doubling; row 2 carries the scalar into the chain's **final register** `n'` (the
Type1 shifted value); rows 3–4 carry the accumulator `acc` into the combine; rows 5–6 carry the
**output**. So the honest soundness statement is a relation purely over the public vector:

> any satisfying witness has `(pub 5, pub 6) = (pub 3, pub 4) + [unshiftType1 (pub 2)] • (pub 0,
> pub 1)` — up to the complete-add's flagged vertical case.

This file reconstructs that circuit *whole* — 7 public rows, the init `CompleteAdd` doubling, the
`VarBaseMul` chain embedded at row 8 (wires shifted, `Satisfies.of_embed`), the combine
`CompleteAdd`, and the trailing `inf`-assert `Generic` row — and proves `scaleCombinePub_sound`.
Everything Rung 0 hypothesized is now *derived from the circuit*:

* the base, accumulator, scalar, and output are the public inputs (public rows + copies);
* the chain's init `P₀ = [2]·T` comes from the doubling row (its own `inf = 0` refuted at
  infinity, its inputs the public base);
* the register init `n₀ = 0` comes from the doubling's `inf` cell wired into the register
  column, with `inf = 0` asserted by the trailing `Generic` row — exactly the dump's trick;
* the scalar's field image is pinned by `gateRegister_cast` + `gateLadder_eq_register`:
  `(s : F) = 2·(pub 2) + 2^(5m) + 1 = unshiftType1 (5m) (pub 2)`;
* the `y ≠ 0` side conditions come from the odd group order.

Remaining hypotheses: the base and accumulator are on the curve (genuinely external), the bit
budget, and (at full width only) the forbidden-band exclusion on the witness's ladder value — the
deployed guard's soundness condition.
-/

namespace Kimchi.Circuit.VarBaseMul

open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine
open Kimchi.Circuit (Cell Satisfies genEval)
open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Kimchi.Pasta Kimchi.Shifted

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The register cast: `gateRegister` lands on the chain's final register cell -/

/-- The unsigned ladder bit casts to the (boolean) witness bit: `(ubit g j : F) = gateBit g j`
    whenever the bit satisfies its boolean constraint. -/
theorem ubit_cast (g : ℕ → Kimchi.Gate.VarBaseMul.Witness F) (j : ℕ)
    (hb : gateBit g j * gateBit g j - gateBit g j = 0) :
    ((ubit g j : ℤ) : F) = gateBit g j := by
  have hbool : gateBit g j = 0 ∨ gateBit g j = 1 := by
    rcases mul_eq_zero.mp (show gateBit g j * (gateBit g j - 1) = 0 by linear_combination hb) with
      h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  rw [ubit]
  split
  · next h => rw [h]; norm_num
  · next h =>
      rcases hbool with h0 | h1
      · rw [h0]; norm_num
      · exact absurd h1 h

/-- **The register cast.** Under the chain's constraints (`Holds` per gate), register threading,
    and the zero init, the ℤ-valued `gateRegister` reconstruction casts to the field register:
    after `i` gates it is `(g (i-1)).nPrime` — so at the top, the value the circuit's register
    column carries. Induction over the gates: each gate's decomposition constraint is the
    `32·n + 16b₀ + 8b₁ + 4b₂ + 2b₃ + b₄` step, its booleanity making the ℤ bits match the cells. -/
theorem gateRegister_cast (m : ℕ) (g : ℕ → Kimchi.Gate.VarBaseMul.Witness F)
    (hHolds : ∀ i, i < m → Holds (g i))
    (hreg : ∀ i, i + 1 < m → (g i).nPrime = (g (i + 1)).n)
    (hn0 : (g 0).n = 0) :
    ∀ i, i < m → ((gateRegister g (5 * i) : ℤ) : F) = (g i).n
      ∧ ((gateRegister g (5 * (i + 1)) : ℤ) : F) = (g i).nPrime := by
  -- one gate's step: from `cast (reg 5i) = n` to `cast (reg 5(i+1)) = n'`
  have step : ∀ i, i < m → ((gateRegister g (5 * i) : ℤ) : F) = (g i).n →
      ((gateRegister g (5 * (i + 1)) : ℤ) : F) = (g i).nPrime := by
    intro i hi hcast
    obtain ⟨hdec, hs0, hs1, hs2, hs3, hs4⟩ := (holds_iff (g i)).mp (hHolds i hi)
    obtain ⟨hgb0, hgb1, hgb2, hgb3, hgb4⟩ := gateBit_block g i
    have e : gateRegister g (5 * (i + 1))
        = 32 * gateRegister g (5 * i) + 16 * ubit g (5 * i) + 8 * ubit g (5 * i + 1)
          + 4 * ubit g (5 * i + 2) + 2 * ubit g (5 * i + 3) + ubit g (5 * i + 4) := by
      show gateRegister g (5 * i + 5) = _
      rw [show 5 * i + 5 = (5 * i + 4) + 1 from rfl, gateRegister_succ,
        show 5 * i + 4 = (5 * i + 3) + 1 from rfl, gateRegister_succ,
        show 5 * i + 3 = (5 * i + 2) + 1 from rfl, gateRegister_succ,
        show 5 * i + 2 = (5 * i + 1) + 1 from rfl, gateRegister_succ,
        gateRegister_succ]
      ring
    have u0 := ubit_cast g (5 * i) (by rw [hgb0]; exact hs0.bool)
    have u1 := ubit_cast g (5 * i + 1) (by rw [hgb1]; exact hs1.bool)
    have u2 := ubit_cast g (5 * i + 2) (by rw [hgb2]; exact hs2.bool)
    have u3 := ubit_cast g (5 * i + 3) (by rw [hgb3]; exact hs3.bool)
    have u4 := ubit_cast g (5 * i + 4) (by rw [hgb4]; exact hs4.bool)
    rw [e]
    push_cast
    rw [u0, u1, u2, u3, u4, hgb0, hgb1, hgb2, hgb3, hgb4, hcast]
    have hd : decompCons (g i) = 0 := hdec
    rw [decompCons, sub_eq_zero] at hd
    rw [hd]; ring
  intro i hi
  induction i with
  | zero =>
    have h0 : ((gateRegister g 0 : ℤ) : F) = (g 0).n := by
      rw [show gateRegister g 0 = 0 from rfl, hn0]; norm_num
    exact ⟨by simpa using h0, step 0 hi (by simpa using h0)⟩
  | succ j ih =>
    obtain ⟨-, hout⟩ := ih (by omega)
    have hin : ((gateRegister g (5 * (j + 1)) : ℤ) : F) = (g (j + 1)).n := by
      rw [hout]; exact hreg j hi
    exact ⟨hin, step (j + 1) hi hin⟩

/-! ## The fully-public circuit -/

/-- A public-input pin row: `Generic` with coeffs `[1,0,0,0,0]` (asserting `w[·][0] = pub[·]`),
    its register-0 cell wired to `t`. -/
def pubPin (t : Cell) : Kimchi.Circuit.Gate F :=
  { kind := .generic, coeffs := #[1, 0, 0, 0, 0], wires := #[t] }

/-- The init doubling row (row 7): inputs tied together (`x₁=x₂`, `y₁=y₂`) and to the chain's
    base cells `(8,0)/(8,1)`; output into the chain's input accumulator `(8,2)/(8,3)`; the `inf`
    cell wired into the chain's register column `(8,4)` — the dump's `n₀ = inf` trick. -/
def initDouble : Kimchi.Circuit.Gate F :=
  { kind := .completeAdd, coeffs := #[]
  , wires := #[(7, 2), (7, 3), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4)] }

/-- The combine row (row `8+2m`): inputs the public `acc` (rows 3–4) and the chain's output
    accumulator (`(7+2m, 0/1)`); outputs the public result (rows 5–6). -/
def combPub (m : ℕ) : Kimchi.Circuit.Gate F :=
  { kind := .completeAdd, coeffs := #[]
  , wires := #[(3, 0), (4, 0), (7 + 2 * m, 0), (7 + 2 * m, 1), (5, 0), (6, 0), (8 + 2 * m, 6)] }

/-- The trailing `inf`-assert row: `Generic` `[1,0,0,0,0]` on a non-public row forces its cell 0
    to `0`, and the wire carries that into the doubling's `inf` cell `(7,6)`. -/
def infAssert : Kimchi.Circuit.Gate F :=
  { kind := .generic, coeffs := #[1, 0, 0, 0, 0], wires := #[(7, 6)] }

/-- The 8-row prefix: seven public pins (base → init row; scalar → final register; acc → combine
    inputs; output → combine outputs) and the init doubling. -/
def scPrefix (m : ℕ) : Array (Kimchi.Circuit.Gate F) :=
  #[pubPin (7, 0), pubPin (7, 1), pubPin (6 + 2 * m, 5), pubPin (8 + 2 * m, 0),
    pubPin (8 + 2 * m, 1), pubPin (8 + 2 * m, 4), pubPin (8 + 2 * m, 5), initDouble]

/-- The fully-public scale-and-combine circuit: prefix, the `VarBaseMul` chain embedded at row 8
    (wires shifted), the combine, and the `inf` assert — the shape of the real dump. -/
def scaleCombinePubCircuit (m : ℕ) : Kimchi.Circuit.Circuit F :=
  (({ publicInputSize := 7, gates := scPrefix m } : Kimchi.Circuit.Circuit F).append
      ((vbmCircuit m).gates.map (Kimchi.Circuit.Gate.shiftWires 8))).append
    #[combPub m, infAssert]

@[simp] theorem scPub_size (m : ℕ) :
    (scaleCombinePubCircuit m (F := F)).gates.size = 2 * m + 10 := by
  simp [scaleCombinePubCircuit, scPrefix]
  omega

/-- Rows 0–7 are the prefix gates. -/
theorem scPub_gateAt_pre (m j : ℕ) (hj : j < 8) :
    (scaleCombinePubCircuit m (F := F)).gateAt j
      = (scPrefix m).getD j Kimchi.Circuit.defaultGate := by
  rw [scaleCombinePubCircuit,
    Circuit.gateAt_append_left _ _ j (by simp [scPrefix]; omega),
    Circuit.gateAt_append_left _ _ j (by simp [scPrefix]; omega)]
  rfl

/-- Rows 8 … 7+2m are the chain's gates, wires shifted by 8. -/
theorem scPub_gateAt_chain (m r : ℕ) (hr : r < 2 * m) :
    (scaleCombinePubCircuit m (F := F)).gateAt (8 + r)
      = ((vbmCircuit m (F := F)).gateAt r).shiftWires 8 := by
  rw [scaleCombinePubCircuit, Circuit.gateAt_append_left _ _ (8 + r) (by simp [scPrefix]; omega)]
  have h := Circuit.gateAt_append_right
    ({ publicInputSize := 7, gates := scPrefix m } : Kimchi.Circuit.Circuit F)
    ((vbmCircuit m (F := F)).gates.map (Kimchi.Circuit.Gate.shiftWires 8)) r
    (by simp; omega)
  rw [show ({ publicInputSize := 7, gates := scPrefix m } :
      Kimchi.Circuit.Circuit F).gates.size = 8 from rfl] at h
  rw [h, Array.getElem_map]
  congr 1
  rw [Circuit.gateAt, Array.getD, dif_pos (by rw [vbmCircuit_size]; omega)]
  rfl

/-- Row `8+2m` is the combine. -/
theorem scPub_gateAt_comb (m : ℕ) :
    (scaleCombinePubCircuit m (F := F)).gateAt (8 + 2 * m) = combPub m := by
  have h := Circuit.gateAt_append_right
    (({ publicInputSize := 7, gates := scPrefix m } : Kimchi.Circuit.Circuit F).append
      ((vbmCircuit m (F := F)).gates.map (Kimchi.Circuit.Gate.shiftWires 8)))
    #[combPub m, infAssert] 0 (by show 0 < 2; decide)
  have hsz : (({ publicInputSize := 7, gates := scPrefix m } :
      Kimchi.Circuit.Circuit F).append
      ((vbmCircuit m (F := F)).gates.map (Kimchi.Circuit.Gate.shiftWires 8))).gates.size
      = 8 + 2 * m := by simp [scPrefix]
  rw [hsz] at h
  exact h

/-- Row `9+2m` is the `inf` assert. -/
theorem scPub_gateAt_inf (m : ℕ) :
    (scaleCombinePubCircuit m (F := F)).gateAt (9 + 2 * m) = infAssert := by
  have h := Circuit.gateAt_append_right
    (({ publicInputSize := 7, gates := scPrefix m } : Kimchi.Circuit.Circuit F).append
      ((vbmCircuit m (F := F)).gates.map (Kimchi.Circuit.Gate.shiftWires 8)))
    #[combPub m, infAssert] 1 (by show 1 < 2; decide)
  have hsz : (({ publicInputSize := 7, gates := scPrefix m } :
      Kimchi.Circuit.Circuit F).append
      ((vbmCircuit m (F := F)).gates.map (Kimchi.Circuit.Gate.shiftWires 8))).gates.size
      = 8 + 2 * m := by simp [scPrefix]
  rw [hsz] at h
  rw [show 9 + 2 * m = 8 + 2 * m + 1 by omega]
  exact h


/-! ## The fully-public soundness theorem -/

/-- **Rung 1: soundness over the public vector alone.** Any witness satisfying
    `scaleCombinePubCircuit m` (with the base `(pub 0, pub 1)` and accumulator `(pub 3, pub 4)`
    on the curve) certifies

        `(pub 5, pub 6) = (pub 3, pub 4) + [s] • (pub 0, pub 1)`,
        `(s : F) = unshiftType1 (5m) (pub 2)`

    — up to the combine's flagged vertical case. The init `[2]·T`, the register init `n₀ = 0`,
    the scalar's register pin, the output pin, and every `y ≠ 0` are **derived** from the circuit
    (copies + gate identities + odd group order). Remaining hypotheses: the two on-curve facts,
    the bit budget, and (at full width) the forbidden-band exclusion on the witness's ladder. -/
theorem scaleCombinePub_sound
    (m : ℕ) (hm : 0 < m) (w : Kimchi.Circuit.Witness VestaBaseField)
    (pub : Array VestaBaseField)
    (hsat : Satisfies (scaleCombinePubCircuit m) w pub)
    (hTpub : Vesta.curve.toAffine.Nonsingular (pub.getD 0 0) (pub.getD 1 0))
    (hAccPub : Vesta.curve.toAffine.Nonsingular (pub.getD 3 0) (pub.getD 4 0))
    (hbits : 5 * m ≤ pastaFieldBits)
    (hnf : 5 * m = pastaFieldBits →
      gateLadder (gwit (w.shift 8)) (5 * m) ∉ forbiddenValues Vesta.curve.toAffine.order) :
    ∃ s : ℤ,
      (s : VestaBaseField) = unshiftType1 (5 * m) (pub.getD 2 0)
      ∧ (((Kimchi.Gate.AddComplete.ofRow (w.row (8 + 2 * m))).inf = 1
            ∧ Point.some _ _ hAccPub + s • Point.some _ _ hTpub = 0)
        ∨ ((Kimchi.Gate.AddComplete.ofRow (w.row (8 + 2 * m))).inf = 0
            ∧ ∃ hOut : Vesta.curve.toAffine.Nonsingular (pub.getD 5 0) (pub.getD 6 0),
              Point.some _ _ hOut = Point.some _ _ hAccPub + s • Point.some _ _ hTpub)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  have ha4 := short4 Vesta.curve.toAffine
  -- the chain block, projected out of the host
  have hemb : Satisfies (vbmCircuit (k + 1)) (w.shift 8) #[] :=
    Satisfies.of_embed 8 (by show (7 : ℕ) ≤ 8; decide)
      (by rw [vbmCircuit_size, scPub_size]; omega)
      (fun r hr => scPub_gateAt_chain (k + 1) r (by rwa [vbmCircuit_size] at hr)) hsat
  obtain ⟨hg, hc⟩ := hsat
  -- a public pin row forces its target cell to the public value
  have pin : ∀ j t, j < 7 →
      (scaleCombinePubCircuit (k + 1) (F := VestaBaseField)).gateAt j = pubPin t →
      pub.getD j 0 = w.cell t := by
    intro j t hj hgat
    have hgj := hg j (by rw [scPub_size]; omega)
    rw [hgat] at hgj
    have heq : (w.row j).getD 0 0 = (scaleCombinePubCircuit (k + 1)).pubTerm pub j := by
      have : Kimchi.Checker.Generic.eval (#[1, 0, 0, 0, 0] : Array VestaBaseField) (w.row j)
          = (scaleCombinePubCircuit (k + 1)).pubTerm pub j := hgj.1
      rwa [genEval] at this
    have hpt : (scaleCombinePubCircuit (k + 1) (F := VestaBaseField)).pubTerm pub j
        = pub.getD j 0 := by
      rw [Circuit.pubTerm,
        show (scaleCombinePubCircuit (k + 1) (F := VestaBaseField)).publicInputSize = 7 from rfl,
        if_pos (show j < 7 by omega)]
    have hcj := hc j (by rw [scPub_size]; omega) 0 (by omega)
    rw [hgat] at hcj
    have hw : (pubPin t (F := VestaBaseField)).wires.getD 0 (j, 0) = t := rfl
    rw [hw] at hcj
    calc pub.getD j 0 = (w.row j).getD 0 0 := by rw [heq, hpt]
      _ = w.cell t := hcj
  -- the seven public pins
  have e0 : pub.getD 0 0 = w.cell (7, 0) :=
    pin 0 (7, 0) (by omega) ((scPub_gateAt_pre (k + 1) 0 (by omega)).trans rfl)
  have e1 : pub.getD 1 0 = w.cell (7, 1) :=
    pin 1 (7, 1) (by omega) ((scPub_gateAt_pre (k + 1) 1 (by omega)).trans rfl)
  have e2 : pub.getD 2 0 = w.cell (6 + 2 * (k + 1), 5) :=
    pin 2 (6 + 2 * (k + 1), 5) (by omega) ((scPub_gateAt_pre (k + 1) 2 (by omega)).trans rfl)
  have e3 : pub.getD 3 0 = w.cell (8 + 2 * (k + 1), 0) :=
    pin 3 (8 + 2 * (k + 1), 0) (by omega) ((scPub_gateAt_pre (k + 1) 3 (by omega)).trans rfl)
  have e4 : pub.getD 4 0 = w.cell (8 + 2 * (k + 1), 1) :=
    pin 4 (8 + 2 * (k + 1), 1) (by omega) ((scPub_gateAt_pre (k + 1) 4 (by omega)).trans rfl)
  have e5 : pub.getD 5 0 = w.cell (8 + 2 * (k + 1), 4) :=
    pin 5 (8 + 2 * (k + 1), 4) (by omega) ((scPub_gateAt_pre (k + 1) 5 (by omega)).trans rfl)
  have e6 : pub.getD 6 0 = w.cell (8 + 2 * (k + 1), 5) :=
    pin 6 (8 + 2 * (k + 1), 5) (by omega) ((scPub_gateAt_pre (k + 1) 6 (by omega)).trans rfl)
  -- the init doubling row's copies (row 7)
  have hgat7 : (scaleCombinePubCircuit (k + 1) (F := VestaBaseField)).gateAt 7 = initDouble :=
    (scPub_gateAt_pre (k + 1) 7 (by omega)).trans rfl
  have c7 : ∀ k, k < 7 → w.cell (7, k)
      = w.cell ((initDouble (F := VestaBaseField)).wires.getD k (7, k)) := by
    intro k hk
    have := hc 7 (by rw [scPub_size]; omega) k hk
    rwa [hgat7] at this
  have c70 : w.cell (7, 0) = w.cell (7, 2) := c7 0 (by omega)
  have c71 : w.cell (7, 1) = w.cell (7, 3) := c7 1 (by omega)
  have c72 : w.cell (7, 2) = w.cell (8, 0) := c7 2 (by omega)
  have c73 : w.cell (7, 3) = w.cell (8, 1) := c7 3 (by omega)
  have c74 : w.cell (7, 4) = w.cell (8, 2) := c7 4 (by omega)
  have c75 : w.cell (7, 5) = w.cell (8, 3) := c7 5 (by omega)
  have c76 : w.cell (7, 6) = w.cell (8, 4) := c7 6 (by omega)
  -- the inf assert (row 9+2m): the doubling's inf cell is 0, hence the register init n₀ = 0
  have hinf0 : w.cell (7, 6) = 0 := by
    have hgi := hg (9 + 2 * (k + 1)) (by rw [scPub_size]; omega)
    rw [scPub_gateAt_inf (k + 1)] at hgi
    have hval : (w.row (9 + 2 * (k + 1))).getD 0 0 = 0 := by
      have : Kimchi.Checker.Generic.eval (#[1, 0, 0, 0, 0] : Array VestaBaseField)
          (w.row (9 + 2 * (k + 1)))
          = (scaleCombinePubCircuit (k + 1)).pubTerm pub (9 + 2 * (k + 1)) := hgi.1
      rw [genEval] at this
      rwa [Circuit.pubTerm,
        show (scaleCombinePubCircuit (k + 1) (F := VestaBaseField)).publicInputSize = 7 from rfl,
        if_neg (show ¬ 9 + 2 * (k + 1) < 7 by omega)] at this
    have hci := hc (9 + 2 * (k + 1)) (by rw [scPub_size]; omega) 0 (by omega)
    rw [scPub_gateAt_inf (k + 1)] at hci
    have hw : (infAssert (F := VestaBaseField)).wires.getD 0 (9 + 2 * (k + 1), 0) = (7, 6) := rfl
    rw [hw] at hci
    calc w.cell (7, 6) = w.cell (9 + 2 * (k + 1), 0) := hci.symm
      _ = 0 := hval
  have hn0 : (gwit (w.shift 8) 0).n = 0 := by
    show ((w.shift 8).row 0).getD 4 0 = 0
    rw [Witness.row_shift]
    calc (w.row (8 + 0)).getD 4 0 = w.cell (8, 4) := rfl
      _ = w.cell (7, 6) := c76.symm
      _ = 0 := hinf0
  -- the init doubling computes [2]·T
  have h7cons : Kimchi.Gate.AddComplete.Holds (Kimchi.Gate.AddComplete.ofRow (w.row 7)) := by
    have := hg 7 (by rw [scPub_size]; omega)
    rwa [hgat7] at this
  have hT7 : Vesta.curve.toAffine.Nonsingular (Kimchi.Gate.AddComplete.ofRow (w.row 7)).x1
      (Kimchi.Gate.AddComplete.ofRow (w.row 7)).y1 := by
    show Vesta.curve.toAffine.Nonsingular (w.cell (7, 0)) (w.cell (7, 1))
    rw [← e0, ← e1]; exact hTpub
  obtain ⟨h37, hdbl⟩ := Kimchi.Circuit.InitGrounding.completeAdd_doubles Vesta.curve.toAffine ha4
    (w.row 7) hT7 c70 c71 h7cons
    (Point.y_ne_zero_of_odd_order rfl rfl vesta_order_odd hT7) (by decide)
  -- the target point and the chain's base/init, transported onto the shifted cells
  set T : Vesta.curve.toAffine.Point := Point.some _ _ hTpub with hTdef
  have exT : (gwit (w.shift 8) 0).xT = pub.getD 0 0 := by
    show ((w.shift 8).row 0).getD 0 0 = _
    rw [Witness.row_shift]
    calc (w.row (8 + 0)).getD 0 0 = w.cell (8, 0) := rfl
      _ = w.cell (7, 2) := c72.symm
      _ = w.cell (7, 0) := c70.symm
      _ = pub.getD 0 0 := e0.symm
  have eyT : (gwit (w.shift 8) 0).yT = pub.getD 1 0 := by
    show ((w.shift 8).row 0).getD 1 0 = _
    rw [Witness.row_shift]
    calc (w.row (8 + 0)).getD 1 0 = w.cell (8, 1) := rfl
      _ = w.cell (7, 3) := c73.symm
      _ = w.cell (7, 1) := c71.symm
      _ = pub.getD 1 0 := e1.symm
  have hTns : Vesta.curve.toAffine.Nonsingular (gwit (w.shift 8) 0).xT
      (gwit (w.shift 8) 0).yT := by rw [exT, eyT]; exact hTpub
  have hTeq : T = Point.some _ _ hTns := Point.some_congr hTpub hTns exT.symm eyT.symm
  have ex0 : (gwit (w.shift 8) 0).x0 = (Kimchi.Gate.AddComplete.ofRow (w.row 7)).x3 := by
    show ((w.shift 8).row 0).getD 2 0 = w.cell (7, 4)
    rw [Witness.row_shift]
    exact c74.symm
  have ey0 : (gwit (w.shift 8) 0).y0 = (Kimchi.Gate.AddComplete.ofRow (w.row 7)).y3 := by
    show ((w.shift 8).row 0).getD 3 0 = w.cell (7, 5)
    rw [Witness.row_shift]
    exact c75.symm
  have hP0ns : Vesta.curve.toAffine.Nonsingular (gwit (w.shift 8) 0).x0
      (gwit (w.shift 8) 0).y0 := by rw [ex0, ey0]; exact h37
  have hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T := by
    rw [Point.some_congr hP0ns h37 ex0 ey0, hdbl, hTdef,
      Point.some_congr hT7 hTpub e0.symm e1.symm]
  -- the chain computes [s]·T
  obtain ⟨hfin, hptS, -⟩ := varBaseMul_circuit_scaleFast1 (k + 1) (w.shift 8) #[] hemb T
    (gateLadder (gwit (w.shift 8)) (5 * (k + 1))) (Point.some_ne_zero _) hTns hTeq hP0ns hP0
    hbits rfl hnf
  -- the scalar's field image is the unshift of the public register (pub 2)
  obtain ⟨hHolds, -, -, hregs⟩ := satisfies_extract (k + 1) (w.shift 8) #[] hemb
  have hcast := (gateRegister_cast (k + 1) (gwit (w.shift 8)) hHolds hregs hn0 k (by omega)).2
  have ereg : (gwit (w.shift 8) k).nPrime = pub.getD 2 0 := by
    show ((w.shift 8).row (2 * k)).getD 5 0 = _
    rw [Witness.row_shift]
    calc (w.row (8 + 2 * k)).getD 5 0
        = w.cell (8 + 2 * k, 5) := rfl
      _ = w.cell (6 + 2 * (k + 1), 5) := by congr 2; omega
      _ = pub.getD 2 0 := e2.symm
  have hsF : ((gateLadder (gwit (w.shift 8)) (5 * (k + 1)) : ℤ) : VestaBaseField)
      = unshiftType1 (5 * (k + 1)) (pub.getD 2 0) := by
    rw [gateLadder_eq_register, unshiftType1, ← ereg, ← hcast]
    push_cast
    ring
  -- the combine row
  have hgatC : (scaleCombinePubCircuit (k + 1) (F := VestaBaseField)).gateAt (8 + 2 * (k + 1))
      = combPub (k + 1) :=
    scPub_gateAt_comb (k + 1)
  have hCcons : Kimchi.Gate.AddComplete.Holds
      (Kimchi.Gate.AddComplete.ofRow (w.row (8 + 2 * (k + 1)))) := by
    have hh := hg (8 + 2 * (k + 1)) (by rw [scPub_size]; omega)
    rwa [hgatC] at hh
  have hcc2 : w.cell (8 + 2 * (k + 1), 2)
      = w.cell ((combPub (k + 1) (F := VestaBaseField)).wires.getD 2 (8 + 2 * (k + 1), 2)) := by
    have hh := hc (8 + 2 * (k + 1)) (by rw [scPub_size]; omega) 2 (by omega)
    rwa [hgatC] at hh
  have hcc3 : w.cell (8 + 2 * (k + 1), 3)
      = w.cell ((combPub (k + 1) (F := VestaBaseField)).wires.getD 3 (8 + 2 * (k + 1), 3)) := by
    have hh := hc (8 + 2 * (k + 1)) (by rw [scPub_size]; omega) 3 (by omega)
    rwa [hgatC] at hh
  have ex2 : (Kimchi.Gate.AddComplete.ofRow (w.row (8 + 2 * (k + 1)))).x2
      = accX (gwit (w.shift 8)) (k + 1) := by
    show w.cell (8 + 2 * (k + 1), 2) = ((w.shift 8).row (2 * k + 1)).getD 0 0
    rw [Witness.row_shift]
    calc w.cell (8 + 2 * (k + 1), 2) = w.cell (7 + 2 * (k + 1), 0) := hcc2
      _ = w.cell (8 + (2 * k + 1), 0) := by
          rw [show 7 + 2 * (k + 1) = 8 + (2 * k + 1) by omega]
  have ey2 : (Kimchi.Gate.AddComplete.ofRow (w.row (8 + 2 * (k + 1)))).y2
      = accY (gwit (w.shift 8)) (k + 1) := by
    show w.cell (8 + 2 * (k + 1), 3) = ((w.shift 8).row (2 * k + 1)).getD 1 0
    rw [Witness.row_shift]
    calc w.cell (8 + 2 * (k + 1), 3) = w.cell (7 + 2 * (k + 1), 1) := hcc3
      _ = w.cell (8 + (2 * k + 1), 1) := by
          rw [show 7 + 2 * (k + 1) = 8 + (2 * k + 1) by omega]
  have haccC : Vesta.curve.toAffine.Nonsingular
      (Kimchi.Gate.AddComplete.ofRow (w.row (8 + 2 * (k + 1)))).x1
      (Kimchi.Gate.AddComplete.ofRow (w.row (8 + 2 * (k + 1)))).y1 := by
    show Vesta.curve.toAffine.Nonsingular (w.cell (8 + 2 * (k + 1), 0))
      (w.cell (8 + 2 * (k + 1), 1))
    rw [← e3, ← e4]; exact hAccPub
  have h2C : Vesta.curve.toAffine.Nonsingular
      (Kimchi.Gate.AddComplete.ofRow (w.row (8 + 2 * (k + 1)))).x2
      (Kimchi.Gate.AddComplete.ofRow (w.row (8 + 2 * (k + 1)))).y2 := by
    rw [ex2, ey2]
    -- `accX/accY` at `k + 1` expose the recursion definitionally; transport `hfin`
    exact hfin
  have heq2 : Point.some _ _ h2C
      = (gateLadder (gwit (w.shift 8)) (5 * (k + 1))) • T :=
    (Point.some_congr h2C hfin ex2 ey2).trans hptS
  have heqAcc : Point.some _ _ haccC = Point.some _ _ hAccPub :=
    Point.some_congr haccC hAccPub e3.symm e4.symm
  refine ⟨gateLadder (gwit (w.shift 8)) (5 * (k + 1)), hsF, ?_⟩
  rcases Kimchi.Gate.AddComplete.sound Vesta.curve.toAffine ha4
      (Kimchi.Gate.AddComplete.ofRow (w.row (8 + 2 * (k + 1)))) haccC h2C hCcons
      (Point.y_ne_zero_of_odd_order rfl rfl vesta_order_odd haccC) (by decide) with
    ⟨hinf, hsum⟩ | ⟨hinf, h3C, hsum⟩
  · exact Or.inl ⟨hinf, by rw [← heqAcc, ← heq2, hTdef] at *; exact hsum⟩
  · refine Or.inr ⟨hinf, ?_⟩
    have hOut : Vesta.curve.toAffine.Nonsingular (pub.getD 5 0) (pub.getD 6 0) := by
      rw [e5, e6]; exact h3C
    refine ⟨hOut, ?_⟩
    calc Point.some _ _ hOut = Point.some _ _ h3C :=
          Point.some_congr hOut h3C e5 e6
      _ = Point.some _ _ haccC + Point.some _ _ h2C := hsum.symm
      _ = Point.some _ _ hAccPub + (gateLadder (gwit (w.shift 8)) (5 * (k + 1))) • T := by
          rw [heqAcc, heq2]

end Kimchi.Circuit.VarBaseMul
