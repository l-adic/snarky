import Kimchi.Cycle.NonDegen
import Kimchi.Circuit.VarBaseMul
import Kimchi.Ladder

/-!
# VarBaseMul soundness: `s ∉ forbiddenBand ⟹ every gate row is non-degenerate`

This is the genuine `hsound` for the kimchi VarBaseMul gate. The complete forbidden set
is the band `s ∈ [-15, 15] (mod order)` (the small scalars whose double-and-add drives
the accumulator onto `±T` in the final doublings; the number-theoretic core is
`Kimchi.Ladder.ladder_nondegen`). Excluding it makes EVERY satisfying witness's gate rows
non-degenerate — the property the (incomplete-addition) gate needs and the deployed
two-residue check fails to guarantee.
-/

namespace Kimchi.Cycle

open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine Kimchi.Circuit.VarBaseMul
  Kimchi.Shifted

variable {F : Type*} [Field F] [DecidableEq F]

/-- The forbidden set for VarBaseMul non-degeneracy: the EXACT Pasta reachable
    degenerate residues `forbiddenResidues = {0, ±1, ±2, ±3, 5, 7, 9, 11}`. Sound for any
    prime `order ≡ 1 (mod 4)` (the actual degenerate set is `⊆` these), and exactly tight
    for the Pasta primes. -/
def forbiddenValues (order : ℕ) : Set ℤ :=
  {s | ∃ t ∈ Kimchi.Ladder.forbiddenResidues, (order : ℤ) ∣ (s - t)}

/-- **Prime order ⇒ full order.** For a nonzero point `T` on a `CMCurve`, a scalar
    multiple `m • T` vanishes iff `order ∣ m`. (`order` is prime and `order • T = 0`, so
    `addOrderOf T ∣ order`; nonzero `T` rules out `addOrderOf T = 1`, hence it equals
    `order`.) -/
lemma zsmul_eq_zero_iff_order_dvd (c : CMCurve F) {T : c.W.Point} (hT : T ≠ 0) (m : ℤ) :
    m • T = 0 ↔ (c.order : ℤ) ∣ m := by
  have hdvd : (addOrderOf T : ℤ) ∣ (c.order : ℤ) :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mpr (c.order_smul T)
  have horder : addOrderOf T = c.order := by
    have hnat : addOrderOf T ∣ c.order := by exact_mod_cast hdvd
    rcases (Nat.Prime.eq_one_or_self_of_dvd c.order_prime _ hnat) with h1 | h1
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hT
    · exact h1
  rw [← addOrderOf_dvd_iff_zsmul_eq_zero, horder]

/-
**Per sub-step advance (mod-based).** Given the gate's per-bit constraints
    `singleBitHolds` with input accumulator `Pᵢ = k·T` and the abstract-ladder
    non-degeneracy facts at `k` (`k ≢ ±1` and `2k ≢ ±1 (mod order)`), the two additions
    are non-vertical (`xᵢ ≠ xT`, `tⱼ ≠ 0`) and the output accumulator is `(2k+e)·T`,
    `e = ±1`. This is the curve-level bridge from `ladder_nondegen`'s arithmetic
    non-degeneracy to the gate's field side conditions, via `smul_ne_base` /
    `x_ne_xT_of_ne_base` / `singleBit_tne_of_double_ne` (re-stated for the mod hypotheses
    using prime `order`: `m·T = 0 ↔ order ∣ m`).
-/
lemma gate_step_advance (c : CMCurve F)
    {xT yT b s1 xi yi xo yo : F}
    (hTns : c.W.Nonsingular xT yT)
    (hI : c.W.Nonsingular xi yi)
    (hQ : c.W.Nonsingular xT ((2 * b - 1) * yT))
    (hbit : b = 0 ∨ b = 1)
    (hTne : Point.some hTns ≠ 0)
    (k : ℤ) (hIk : Point.some hI = k • Point.some hTns)
    (hkx1 : ¬ ((c.order : ℤ) ∣ (k - 1))) (hkx2 : ¬ ((c.order : ℤ) ∣ (k + 1)))
    (hkt1 : ¬ ((c.order : ℤ) ∣ (2 * k - 1))) (hkt2 : ¬ ((c.order : ℤ) ∣ (2 * k + 1)))
    (hh : singleBitHolds b xT yT s1 xi yi xo yo) :
    xi ≠ xT ∧ (2 * xi + xT - s1 * s1 ≠ 0) ∧
      ∃ (hO : c.W.Nonsingular xo yo) (e : ℤ),
        (e = 1 ∨ e = -1) ∧ (e : F) = 2 * b - 1 ∧
          Point.some hO = (2 * k + e) • Point.some hTns := by
  obtain ⟨ e, he, he' ⟩ := signed_target c.W c.short hTns hQ hbit;
  refine' ⟨ _, _, _ ⟩;
  · apply x_ne_xT_of_ne_base c hI hTns;
    · contrapose! hkx1;
      have h_div : (k - 1) • Point.some hTns = 0 := by
        rw [ sub_smul, one_smul, ← hIk, hkx1, sub_self ];
      exact zsmul_eq_zero_iff_order_dvd c hTne _ |>.1 h_div;
    · contrapose! hkx2;
      rw [ ← zsmul_eq_zero_iff_order_dvd c hTne ];
      rw [ add_zsmul, one_zsmul, ← hIk, hkx2, neg_add_cancel ];
  · apply singleBit_tne_of_double_ne c hI hQ (by
    apply x_ne_xT_of_ne_base c hI hTns;
    · contrapose! hkx1;
      rw [ ← zsmul_eq_zero_iff_order_dvd c hTne ];
      rw [ sub_smul, one_smul, ← hIk, hkx1, sub_self ];
    · intro h
      have h_contra : (k + 1 : ℤ) • Point.some hTns = 0 := by
        rw [ add_zsmul, one_zsmul ];
        rw [ ← hIk, h, neg_add_cancel ];
      exact hkx2 ( zsmul_eq_zero_iff_order_dvd c hTne _ |>.1 h_contra )) hh (by
    intro h
    have h_div : (c.order : ℤ) ∣ (2 * k + e) := by
      rw [ ← zsmul_eq_zero_iff_order_dvd c hTne ];
      convert h using 1;
      rw [ hIk, he ];
      module;
    grind +qlia);
  · obtain ⟨ hO, hOeq ⟩ :=
      singleBit_sound c.W c.short b xT yT s1 xi yi xo yo hI hQ
        ( x_ne_xT_of_ne_base c hI hTns ( by
      contrapose! hkx1;
      rw [ ← zsmul_eq_zero_iff_order_dvd c hTne ];
      rw [ sub_smul, one_smul, ← hIk, hkx1, sub_self ] ) ( by
      intro h
      have h_contra : (k + 1 : ℤ) • Point.some hTns = 0 := by
        rw [ add_zsmul, one_zsmul ];
        rw [ ← hIk, h, neg_add_cancel ];
      exact hkx2 ( zsmul_eq_zero_iff_order_dvd c hTne _ |>.1 h_contra ) ) ) ( by
      apply Kimchi.Cycle.singleBit_tne_of_double_ne c hI hQ ( x_ne_xT_of_ne_base c hI hTns ( by
        contrapose! hkx1;
        rw [ ← zsmul_eq_zero_iff_order_dvd c hTne ];
        rw [ sub_smul, one_smul, ← hIk, hkx1, sub_self ] ) ( by
        intro h
        have h_contra : (k + 1 : ℤ) • Point.some hTns = 0 := by
          rw [ add_zsmul, one_zsmul ];
          rw [ ← hIk, h, neg_add_cancel ];
        exact hkx2 ( zsmul_eq_zero_iff_order_dvd c hTne _ |>.1 h_contra ) ) ) hh ( by
        intro h
        have h_div : (c.order : ℤ) ∣ (2 * k + e) := by
          rw [ ← zsmul_eq_zero_iff_order_dvd c hTne ];
          convert h using 1;
          rw [ hIk, he ];
          module;
        grind +qlia ) ) hh;
    refine' ⟨ hO, e, he'.2, he'.1, _ ⟩;
    rw [ hOeq, hIk, he ];
    module

/-! ## Assembling the per-row non-degeneracy from the abstract ladder

The `m` gates × 5 sub-steps form one length-`5m` double-and-add ladder of accumulator
points.  We package the signed bits of the witnesses into an integer ladder `gateLadder`,
transport `ladder_nondegen_tight`'s arithmetic non-degeneracy along it with
`gate_step_advance`, and read off `NonDegen` for every row. -/

/-- The raw bit processed at sub-step `j`: bit `j % 5` of gate `j / 5`. -/
def gateBit (g : ℕ → Witness F) (j : ℕ) : F :=
  match j % 5 with
  | 0 => (g (j / 5)).b0
  | 1 => (g (j / 5)).b1
  | 2 => (g (j / 5)).b2
  | 3 => (g (j / 5)).b3
  | _ => (g (j / 5)).b4

/-- The signed bit `±1` at sub-step `j`. -/
def gateBitSign (g : ℕ → Witness F) (j : ℕ) : ℤ := if gateBit g j = 1 then 1 else -1

/-- The integer double-and-add ladder over the gate bits, with `k 0 = 2`. -/
def gateLadder (g : ℕ → Witness F) : ℕ → ℤ
  | 0 => 2
  | j + 1 => 2 * gateLadder g j + gateBitSign g j

@[simp] lemma gateLadder_zero (g : ℕ → Witness F) : gateLadder g 0 = 2 := rfl

lemma gateLadder_succ (g : ℕ → Witness F) (j : ℕ) :
    gateLadder g (j + 1) = 2 * gateLadder g j + gateBitSign g j := rfl

lemma gateBitSign_eq (g : ℕ → Witness F) (j : ℕ) :
    gateBitSign g j = 1 ∨ gateBitSign g j = -1 := by
  unfold gateBitSign; split <;> simp

/-
The five raw bits of gate `i` are the sub-step bits `5i … 5i+4`.
-/
omit [Field F] [DecidableEq F] in
lemma gateBit_block (g : ℕ → Witness F) (i : ℕ) :
    gateBit g (5 * i) = (g i).b0 ∧ gateBit g (5 * i + 1) = (g i).b1
      ∧ gateBit g (5 * i + 2) = (g i).b2 ∧ gateBit g (5 * i + 3) = (g i).b3
      ∧ gateBit g (5 * i + 4) = (g i).b4 := by
  unfold gateBit; simp +decide [ Nat.add_mod ] ;
  norm_num [ Nat.add_div ]

/-
The signed bit `e` produced by `signed_target` matches `gateBitSign`.
-/
lemma e_eq_gateBitSign (g : ℕ → Witness F) (j : ℕ) {b : F} (hgb : gateBit g j = b)
    (hbit : b = 0 ∨ b = 1) {e : ℤ} (he2 : (e : F) = 2 * b - 1) (he : e = 1 ∨ e = -1)
    (h2 : (2 : F) ≠ 0) : e = gateBitSign g j := by
  cases hbit <;> simp_all +decide [ gateBitSign ];
  · cases he <;> simp_all +decide;
    exact h2 ( by linear_combination' he2 );
  · rcases he with ( rfl | rfl ) <;> norm_num at *;
    grind +extAll

/-
**One gate block.** Given a gate's constraint data `gd`, the input accumulator equal
    to `gateLadder g (5i) • T`, and the ladder non-degeneracy at all five sub-step scalars
    `gateLadder g (5i+ℓ)` (`ℓ < 5`), every one of the gate's ten side conditions holds
    (`NonDegen (g i)`) and the output accumulator advances to `gateLadder g (5i+5) • T`.
-/
lemma gate_block (c : CMCurve F) (g : ℕ → Witness F) (i : ℕ)
    (h2 : (2 : F) ≠ 0)
    {T : c.W.Point} (hTne : T ≠ 0)
    (gd : GateData c.W (g i)) (hTeq : T = Point.some gd.hT)
    (ha0 : Point.some gd.a0 = gateLadder g (5 * i) • T)
    (hnd : ∀ ℓ, ℓ < 5 →
        ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) - 1)
          ∧ ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) + 1)
          ∧ ¬ (c.order : ℤ) ∣ (2 * gateLadder g (5 * i + ℓ) - 1)
          ∧ ¬ (c.order : ℤ) ∣ (2 * gateLadder g (5 * i + ℓ) + 1)) :
    NonDegen (g i) ∧ Point.some gd.a5 = gateLadder g (5 * i + 5) • T := by
  have hT0 : Point.some gd.hT ≠ 0 := by rw [← hTeq]; exact hTne
  obtain ⟨_hdec, hsb0, hsb1, hsb2, hsb3, hsb4⟩ := gd.holds
  obtain ⟨gb0, gb1, gb2, gb3, gb4⟩ := gateBit_block g i
  -- booleanity from the `b * b - b = 0` constraint
  have bit : ∀ {x : F}, x * x - x = 0 → x = 0 ∨ x = 1 := by
    intro x hx
    rcases mul_eq_zero.mp (show x * (x - 1) = 0 by linear_combination hx) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  -- sub-step 0
  have ha0' : Point.some gd.a0 = gateLadder g (5 * i) • Point.some gd.hT := by
    rw [hTeq] at ha0; exact ha0
  obtain ⟨hx0, ht0, hO0, e0, hepm0, hef0, hOeq0⟩ :=
    gate_step_advance c gd.hT gd.a0 gd.q0 (bit hsb0.1) hT0 (gateLadder g (5 * i)) ha0'
      (hnd 0 (by omega)).1 (hnd 0 (by omega)).2.1 (hnd 0 (by omega)).2.2.1
      (hnd 0 (by omega)).2.2.2 hsb0
  have ha1 : Point.some gd.a1 = gateLadder g (5 * i + 1) • Point.some gd.hT := by
    rw [show Point.some gd.a1 = Point.some hO0 from rfl, hOeq0,
      e_eq_gateBitSign g (5 * i) gb0 (bit hsb0.1) hef0 hepm0 h2, ← gateLadder_succ]
  -- sub-step 1
  obtain ⟨hx1, ht1, hO1, e1, hepm1, hef1, hOeq1⟩ :=
    gate_step_advance c gd.hT gd.a1 gd.q1 (bit hsb1.1) hT0 (gateLadder g (5 * i + 1)) ha1
      (hnd 1 (by omega)).1 (hnd 1 (by omega)).2.1 (hnd 1 (by omega)).2.2.1
      (hnd 1 (by omega)).2.2.2 hsb1
  have ha2 : Point.some gd.a2 = gateLadder g (5 * i + 2) • Point.some gd.hT := by
    rw [show Point.some gd.a2 = Point.some hO1 from rfl, hOeq1,
      e_eq_gateBitSign g (5 * i + 1) gb1 (bit hsb1.1) hef1 hepm1 h2, ← gateLadder_succ]
  -- sub-step 2
  obtain ⟨hx2, ht2, hO2, e2, hepm2, hef2, hOeq2⟩ :=
    gate_step_advance c gd.hT gd.a2 gd.q2 (bit hsb2.1) hT0 (gateLadder g (5 * i + 2)) ha2
      (hnd 2 (by omega)).1 (hnd 2 (by omega)).2.1 (hnd 2 (by omega)).2.2.1
      (hnd 2 (by omega)).2.2.2 hsb2
  have ha3 : Point.some gd.a3 = gateLadder g (5 * i + 3) • Point.some gd.hT := by
    rw [show Point.some gd.a3 = Point.some hO2 from rfl, hOeq2,
      e_eq_gateBitSign g (5 * i + 2) gb2 (bit hsb2.1) hef2 hepm2 h2, ← gateLadder_succ]
  -- sub-step 3
  obtain ⟨hx3, ht3, hO3, e3, hepm3, hef3, hOeq3⟩ :=
    gate_step_advance c gd.hT gd.a3 gd.q3 (bit hsb3.1) hT0 (gateLadder g (5 * i + 3)) ha3
      (hnd 3 (by omega)).1 (hnd 3 (by omega)).2.1 (hnd 3 (by omega)).2.2.1
      (hnd 3 (by omega)).2.2.2 hsb3
  have ha4 : Point.some gd.a4 = gateLadder g (5 * i + 4) • Point.some gd.hT := by
    rw [show Point.some gd.a4 = Point.some hO3 from rfl, hOeq3,
      e_eq_gateBitSign g (5 * i + 3) gb3 (bit hsb3.1) hef3 hepm3 h2, ← gateLadder_succ]
  -- sub-step 4
  obtain ⟨hx4, ht4, hO4, e4, hepm4, hef4, hOeq4⟩ :=
    gate_step_advance c gd.hT gd.a4 gd.q4 (bit hsb4.1) hT0 (gateLadder g (5 * i + 4)) ha4
      (hnd 4 (by omega)).1 (hnd 4 (by omega)).2.1 (hnd 4 (by omega)).2.2.1
      (hnd 4 (by omega)).2.2.2 hsb4
  have ha5 : Point.some gd.a5 = gateLadder g (5 * i + 5) • Point.some gd.hT := by
    rw [show Point.some gd.a5 = Point.some hO4 from rfl, hOeq4,
      e_eq_gateBitSign g (5 * i + 4) gb4 (bit hsb4.1) hef4 hepm4 h2, ← gateLadder_succ]
  refine ⟨⟨hx0, hx1, hx2, hx3, hx4, ht0, ht1, ht2, ht3, ht4⟩, ?_⟩
  rw [hTeq]; exact ha5

/-
**VarBaseMul soundness (`hsound`).** For ANY witness satisfying the gate constraints
    (`GateData` for every row) at the real init (`P 0 = 2·T`), in the one-wrap regime
    `2^(5m-1) < order < 2^(5m)`, if the integer scalar `s` computed by the gate bits
    (`s = gateLadder g (5m)`, the double-and-add ladder top) avoids the forbidden residues
    `forbiddenValues order` and `order ≡ 1 (mod 4)`, then every gate row is `NonDegen`.

    This discharges the soundness assumption of
    `Kimchi.Circuit.VarBaseMul.varBaseMul_sound`: a non-forbidden scalar forces every
    incomplete-addition step non-degenerate.

    Hypothesis adjustments vs. the original stub (the conclusion is unchanged):
    the cross-field register bookkeeping (`N`, `hN0`, `hNs`, `hregIn`, `hregOut`) is
    replaced by stating the scalar directly as the bit-determined ladder top
    (`hs : s = gateLadder g (5 * m)`), and the one-wrap regime bounds (`hreg₁`, `hreg₂`)
    are added — both are needed to invoke the number-theoretic core
    `Kimchi.Ladder.ladder_nondegen_tight`.
-/
theorem nonDegen_of_not_forbidden (c : CMCurve F)
    (m : ℕ) (g : ℕ → Witness F)
    (T : c.W.Point) (P : ℕ → c.W.Point) (s : ℤ)
    (hTne : T ≠ 0)
    (hd : ∀ i, i < m → GateData c.W (g i))
    (hT : ∀ i (hi : i < m), T = Point.some (hd i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some (hd i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some (hd i hi).a5)
    (hP0 : P 0 = (2 : ℤ) • T)
    (h2 : (2 : F) ≠ 0)
    (hreg₁ : 2 ^ (5 * m - 1) < c.order) (hreg₂ : c.order < 2 ^ (5 * m))
    (hq4 : c.order % 4 = 1)
    (hs : s = gateLadder g (5 * m)) (hnf : s ∉ forbiddenValues c.order) :
    ∀ i, i < m → NonDegen (g i) := by
  -- Transport `hnf` from `s` to the bit-determined ladder top.
  have hnf' : ∀ t ∈ Kimchi.Ladder.forbiddenResidues,
      ¬ (c.order : ℤ) ∣ (gateLadder g (5 * m) - t) := by
    intro t ht hdvd
    exact hnf ⟨t, ht, by rw [hs]; exact hdvd⟩
  -- Global ladder non-degeneracy from the number-theoretic core.
  have hND := Kimchi.Ladder.ladder_nondegen_tight c.order (5 * m) c.order_prime hq4 hreg₁ hreg₂
    (gateLadder g) (gateBitSign g) (gateLadder_zero g) (fun j _ => gateBitSign_eq g j)
    (fun j _ => gateLadder_succ g j) hnf'
  -- Fold the gate blocks: each accumulator is `gateLadder g (5i) • T` and every row is
  -- non-degenerate.
  have key : ∀ i, i ≤ m →
      P i = gateLadder g (5 * i) • T ∧ (∀ i', i' < i → NonDegen (g i')) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [hP0]; simp [gateLadder_zero]
      · intro i' hi'; omega
    | succ i ih =>
      intro hi1
      have hi : i < m := by omega
      obtain ⟨hPi, hNDi⟩ := ih (by omega)
      have ha0 : Point.some (hd i hi).a0 = gateLadder g (5 * i) • T := by
        rw [← hin i hi]; exact hPi
      obtain ⟨hNDgi, ha5⟩ := gate_block c g i h2 hTne (hd i hi) (hT i hi) ha0
        (fun ℓ hℓ => hND (5 * i + ℓ) (by omega))
      refine ⟨?_, ?_⟩
      · rw [hout i hi, show 5 * (i + 1) = 5 * i + 5 from by ring]; exact ha5
      · intro i' hi'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | h
        · exact hNDi i' h
        · subst h; exact hNDgi
  intro i hi
  exact (key m le_rfl).2 i hi

/-! ## Deployed soundness: from the constraints + the register field bound (no forbidden set)

The §6 conclusion of `docs/varbasemul-soundness-analysis.md`, formalized: the deployed
circuit is sound because (A) the t-conditions are forced by the gate constraints
(`tne_of_holds`) and (B) the x-conditions are excluded by the circuit-field register
bound (`Kimchi.Ladder.ladder_x_nondegen`) — the forbidden check appears NOWHERE. -/

/-- Per sub-step advance using ONLY the x-condition `k ≢ ±1`; the t-condition `t ≠ 0`
    is supplied by `tne_of_holds` (the constraints + prime order), not by `2k ≢ ±1`. -/
lemma gate_step_advance' (c : CMCurve F) (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    {xT yT b s1 xi yi xo yo : F}
    (hTns : c.W.Nonsingular xT yT)
    (hI : c.W.Nonsingular xi yi)
    (hQ : c.W.Nonsingular xT ((2 * b - 1) * yT))
    (hbit : b = 0 ∨ b = 1)
    (hTne : Point.some hTns ≠ 0)
    (k : ℤ) (hIk : Point.some hI = k • Point.some hTns)
    (hkx1 : ¬ ((c.order : ℤ) ∣ (k - 1))) (hkx2 : ¬ ((c.order : ℤ) ∣ (k + 1)))
    (hh : singleBitHolds b xT yT s1 xi yi xo yo) :
    xi ≠ xT ∧ (2 * xi + xT - s1 * s1 ≠ 0) ∧
      ∃ (hO : c.W.Nonsingular xo yo) (e : ℤ),
        (e = 1 ∨ e = -1) ∧ (e : F) = 2 * b - 1 ∧
          Point.some hO = (2 * k + e) • Point.some hTns := by
  obtain ⟨e, he, he'⟩ := signed_target c.W c.short hTns hQ hbit
  have hxne : xi ≠ xT := by
    apply x_ne_xT_of_ne_base c hI hTns
    · contrapose! hkx1
      have hd : (k - 1) • Point.some hTns = 0 := by
        rw [sub_smul, one_smul, ← hIk, hkx1, sub_self]
      exact (zsmul_eq_zero_iff_order_dvd c hTne _).1 hd
    · contrapose! hkx2
      rw [← zsmul_eq_zero_iff_order_dvd c hTne, add_zsmul, one_zsmul, ← hIk, hkx2,
        neg_add_cancel]
  have htne : 2 * xi + xT - s1 * s1 ≠ 0 := tne_of_holds c h2 hodd hI hh
  obtain ⟨hO, hOeq⟩ := singleBit_sound c.W c.short b xT yT s1 xi yi xo yo hI hQ hxne htne hh
  refine ⟨hxne, htne, hO, e, he'.2, he'.1, ?_⟩
  rw [hOeq, hIk, he]
  module

/-- One gate block from ONLY the x-conditions (`gate_block` needs all four; this needs
    two). The t-conditions come from `gate_step_advance'` via `tne_of_holds`. -/
lemma gate_block' (c : CMCurve F) (g : ℕ → Witness F) (i : ℕ)
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    {T : c.W.Point} (hTne : T ≠ 0)
    (gd : GateData c.W (g i)) (hTeq : T = Point.some gd.hT)
    (ha0 : Point.some gd.a0 = gateLadder g (5 * i) • T)
    (hnd : ∀ ℓ, ℓ < 5 →
        ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) - 1)
          ∧ ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) + 1)) :
    NonDegen (g i) ∧ Point.some gd.a5 = gateLadder g (5 * i + 5) • T := by
  have hT0 : Point.some gd.hT ≠ 0 := by rw [← hTeq]; exact hTne
  obtain ⟨_hdec, hsb0, hsb1, hsb2, hsb3, hsb4⟩ := gd.holds
  obtain ⟨gb0, gb1, gb2, gb3, gb4⟩ := gateBit_block g i
  have bit : ∀ {x : F}, x * x - x = 0 → x = 0 ∨ x = 1 := by
    intro x hx
    rcases mul_eq_zero.mp (show x * (x - 1) = 0 by linear_combination hx) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  have ha0' : Point.some gd.a0 = gateLadder g (5 * i) • Point.some gd.hT := by
    rw [hTeq] at ha0; exact ha0
  obtain ⟨hx0, ht0, hO0, e0, hepm0, hef0, hOeq0⟩ :=
    gate_step_advance' c h2 hodd gd.hT gd.a0 gd.q0 (bit hsb0.1) hT0 (gateLadder g (5 * i)) ha0'
      (hnd 0 (by omega)).1 (hnd 0 (by omega)).2 hsb0
  have ha1 : Point.some gd.a1 = gateLadder g (5 * i + 1) • Point.some gd.hT := by
    rw [show Point.some gd.a1 = Point.some hO0 from rfl, hOeq0,
      e_eq_gateBitSign g (5 * i) gb0 (bit hsb0.1) hef0 hepm0 h2, ← gateLadder_succ]
  obtain ⟨hx1, ht1, hO1, e1, hepm1, hef1, hOeq1⟩ :=
    gate_step_advance' c h2 hodd gd.hT gd.a1 gd.q1 (bit hsb1.1) hT0 (gateLadder g (5 * i + 1)) ha1
      (hnd 1 (by omega)).1 (hnd 1 (by omega)).2 hsb1
  have ha2 : Point.some gd.a2 = gateLadder g (5 * i + 2) • Point.some gd.hT := by
    rw [show Point.some gd.a2 = Point.some hO1 from rfl, hOeq1,
      e_eq_gateBitSign g (5 * i + 1) gb1 (bit hsb1.1) hef1 hepm1 h2, ← gateLadder_succ]
  obtain ⟨hx2, ht2, hO2, e2, hepm2, hef2, hOeq2⟩ :=
    gate_step_advance' c h2 hodd gd.hT gd.a2 gd.q2 (bit hsb2.1) hT0 (gateLadder g (5 * i + 2)) ha2
      (hnd 2 (by omega)).1 (hnd 2 (by omega)).2 hsb2
  have ha3 : Point.some gd.a3 = gateLadder g (5 * i + 3) • Point.some gd.hT := by
    rw [show Point.some gd.a3 = Point.some hO2 from rfl, hOeq2,
      e_eq_gateBitSign g (5 * i + 2) gb2 (bit hsb2.1) hef2 hepm2 h2, ← gateLadder_succ]
  obtain ⟨hx3, ht3, hO3, e3, hepm3, hef3, hOeq3⟩ :=
    gate_step_advance' c h2 hodd gd.hT gd.a3 gd.q3 (bit hsb3.1) hT0 (gateLadder g (5 * i + 3)) ha3
      (hnd 3 (by omega)).1 (hnd 3 (by omega)).2 hsb3
  have ha4 : Point.some gd.a4 = gateLadder g (5 * i + 4) • Point.some gd.hT := by
    rw [show Point.some gd.a4 = Point.some hO3 from rfl, hOeq3,
      e_eq_gateBitSign g (5 * i + 3) gb3 (bit hsb3.1) hef3 hepm3 h2, ← gateLadder_succ]
  obtain ⟨hx4, ht4, hO4, e4, hepm4, hef4, hOeq4⟩ :=
    gate_step_advance' c h2 hodd gd.hT gd.a4 gd.q4 (bit hsb4.1) hT0 (gateLadder g (5 * i + 4)) ha4
      (hnd 4 (by omega)).1 (hnd 4 (by omega)).2 hsb4
  have ha5 : Point.some gd.a5 = gateLadder g (5 * i + 5) • Point.some gd.hT := by
    rw [show Point.some gd.a5 = Point.some hO4 from rfl, hOeq4,
      e_eq_gateBitSign g (5 * i + 4) gb4 (bit hsb4.1) hef4 hepm4 h2, ← gateLadder_succ]
  refine ⟨⟨hx0, hx1, hx2, hx3, hx4, ht0, ht1, ht2, ht3, ht4⟩, ?_⟩
  rw [hTeq]; exact ha5

/-- **Top-level deployed VarBaseMul circuit theorem: correct (hence sound).** For ANY
    witness satisfying the gate constraints at the real init (`P 0 = 2·T`), in the one-wrap
    regime with the Pasta register-field relation `circuitMod + 2^(5m-1) + 2 ≤ 2·order`,
    whose register is a valid circuit-field element
    (`s = gateLadder g (5m) < 2·circuitMod + 2^(5m)`), the `m` gates **compute `P m = s·T`**
    and every gate row is `NonDegen`. The forbidden-value check appears NOWHERE: the
    t-conditions come from the constraints + prime order (`tne_of_holds`), the x-conditions
    from the register field bound (`ladder_x_nondegen`), and `P m = s·T` directly from the
    chained per-row advance (`gate_block'`). The `.2` (non-degeneracy) is the deployed
    soundness; the `.1` is the deployed correctness. -/
theorem varBaseMul_deployed_correct (c : CMCurve F)
    (m : ℕ) (g : ℕ → Witness F) (circuitMod : ℕ)
    (T : c.W.Point) (P : ℕ → c.W.Point) (s : ℤ)
    (hTne : T ≠ 0)
    (hd : ∀ i, i < m → GateData c.W (g i))
    (hT : ∀ i (hi : i < m), T = Point.some (hd i hi).hT)
    (hin : ∀ i (hi : i < m), P i = Point.some (hd i hi).a0)
    (hout : ∀ i (hi : i < m), P (i + 1) = Point.some (hd i hi).a5)
    (hP0 : P 0 = (2 : ℤ) • T)
    (h2 : (2 : F) ≠ 0) (horder : 3 < c.order)
    (hreg₁ : 2 ^ (5 * m - 1) < c.order) (hreg₂ : c.order < 2 ^ (5 * m))
    (hbound : circuitMod + 2 ^ (5 * m - 1) + 2 ≤ 2 * c.order)
    (hs : s = gateLadder g (5 * m))
    (hreg : s < 2 * (circuitMod : ℤ) + 2 ^ (5 * m)) :
    P m = s • T ∧ ∀ i, i < m → NonDegen (g i) := by
  have hodd : c.order ≠ 2 := by omega
  have hND := Kimchi.Ladder.ladder_x_nondegen c.order circuitMod (5 * m)
    hreg₁ hreg₂ (c.order_prime.odd_of_ne_two hodd) horder hbound
    (gateLadder g) (gateBitSign g) (gateLadder_zero g) (fun j _ => gateBitSign_eq g j)
    (fun j _ => gateLadder_succ g j) (by rw [← hs]; exact hreg)
  have key : ∀ i, i ≤ m →
      P i = gateLadder g (5 * i) • T ∧ (∀ i', i' < i → NonDegen (g i')) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [hP0]; simp [gateLadder_zero]
      · intro i' hi'; omega
    | succ i ih =>
      intro hi1
      have hi : i < m := by omega
      obtain ⟨hPi, hNDi⟩ := ih (by omega)
      have ha0 : Point.some (hd i hi).a0 = gateLadder g (5 * i) • T := by
        rw [← hin i hi]; exact hPi
      obtain ⟨hNDgi, ha5⟩ := gate_block' c g i h2 hodd hTne (hd i hi) (hT i hi) ha0
        (fun ℓ hℓ => hND (5 * i + ℓ) (by omega))
      refine ⟨?_, ?_⟩
      · rw [hout i hi, show 5 * (i + 1) = 5 * i + 5 from by ring]; exact ha5
      · intro i' hi'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | h
        · exact hNDi i' h
        · subst h; exact hNDgi
  exact ⟨by rw [hs]; exact (key m le_rfl).1, fun i hi => (key m le_rfl).2 i hi⟩

end Kimchi.Cycle
