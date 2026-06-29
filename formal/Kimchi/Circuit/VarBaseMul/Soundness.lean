import Kimchi.Circuit.VarBaseMul.NonDegen
import Kimchi.Circuit.VarBaseMul.Basic
import Kimchi.Circuit.VarBaseMul.Ladder

/-!
# VarBaseMul soundness: `s ∉ forbiddenBand ⟹ every gate row is non-degenerate`

This is the genuine `hsound` for the kimchi VarBaseMul gate. The complete forbidden set
is the band `s ∈ [-15, 15] (mod order)` (the small scalars whose double-and-add drives
the accumulator onto `±T` in the final doublings; the number-theoretic core is
`Ladder.ladder_nondegen_tight`). Excluding it makes EVERY satisfying witness's gate rows
non-degenerate — the property the (incomplete-addition) gate needs and the deployed
two-residue check fails to guarantee.
-/

namespace Kimchi.Circuit.VarBaseMul

open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine Kimchi.Circuit.VarBaseMul
  Kimchi.Shifted

variable {F : Type*} [Field F] [DecidableEq F]

/-- The forbidden set for VarBaseMul non-degeneracy: the EXACT Pasta reachable
    degenerate residues `forbiddenResidues = {0, ±1, ±2, ±3, 5, 7, 9, 11}`. Sound for any
    prime `order ≡ 1 (mod 4)` (the actual degenerate set is `⊆` these), and exactly tight
    for the Pasta primes. -/
def forbiddenValues (order : ℕ) : Set ℤ :=
  {s | ∃ t ∈ Ladder.forbiddenResidues, (order : ℤ) ∣ (s - t)}

/-- **Prime order ⇒ full order.** For a nonzero point `T` on a `short-Weierstrass curve`, a scalar
    multiple `m • T` vanishes iff `order ∣ m`. (`order` is prime and `order • T = 0`, so
    `addOrderOf T ∣ order`; nonzero `T` rules out `addOrderOf T = 1`, hence it equals
    `order`.) -/
lemma zsmul_eq_zero_iff_order_dvd (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] {T : c.Point} (hT : T ≠ 0) (m : ℤ) :
    m • T = 0 ↔ (c.order : ℤ) ∣ m := by
  have hdvd : (addOrderOf T : ℤ) ∣ (c.order : ℤ) :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mpr (c.order_smul T)
  have horder : addOrderOf T = c.order := by
    have hnat : addOrderOf T ∣ c.order := by exact_mod_cast hdvd
    rcases (Nat.Prime.eq_one_or_self_of_dvd c.order_prime _ hnat) with h1 | h1
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hT
    · exact h1
  rw [← addOrderOf_dvd_iff_zsmul_eq_zero, horder]

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

/-- The unsigned bit at sub-step `j`: `1` if set, else `0` (same `= 1` test as `gateBitSign`). -/
def ubit (g : ℕ → Witness F) (j : ℕ) : ℤ := if gateBit g j = 1 then 1 else 0

/-- The signed digit is `2·(unsigned bit) − 1`, unconditionally (same `gateBit = 1` test). -/
lemma gateBitSign_eq_ubit (g : ℕ → Witness F) (j : ℕ) :
    gateBitSign g j = 2 * ubit g j - 1 := by
  unfold gateBitSign ubit; split <;> ring

/-- The unsigned scalar register the ladder bits encode (Horner over `ubit`), `r 0 = 0`. -/
def gateRegister (g : ℕ → Witness F) : ℕ → ℤ
  | 0 => 0
  | j + 1 => 2 * gateRegister g j + ubit g j

lemma gateRegister_succ (g : ℕ → Witness F) (j : ℕ) :
    gateRegister g (j + 1) = 2 * gateRegister g j + ubit g j := rfl

/-- **Signed ladder ↔ unsigned register bridge.** The signed double-and-add top is the `Type1`
    unshift of the unsigned register it encodes, as an honest **ℤ** identity (no booleanity needed —
    the signed digits are `2·ubit − 1`): `gateLadder g L = 2·gateRegister g L + 2^L + 1`. This links
    the non-degeneracy path (`gateLadder`) to the scalar-register path: a range-check
    `gateRegister < 2^k` directly bounds the ladder top, hence the deployed `hcanonical`. -/
lemma gateLadder_eq_register (g : ℕ → Witness F) (L : ℕ) :
    gateLadder g L = 2 * gateRegister g L + 2 ^ L + 1 := by
  induction L with
  | zero => norm_num [gateLadder, gateRegister]
  | succ j ih =>
    rw [gateLadder_succ, ih, gateBitSign_eq_ubit, gateRegister_succ, pow_succ]; ring

omit [Field F] [DecidableEq F] in
/-- The five raw bits of gate `i` are the sub-step bits `5i … 5i+4`. -/
lemma gateBit_block (g : ℕ → Witness F) (i : ℕ) :
    gateBit g (5 * i) = (g i).b0 ∧ gateBit g (5 * i + 1) = (g i).b1
      ∧ gateBit g (5 * i + 2) = (g i).b2 ∧ gateBit g (5 * i + 3) = (g i).b3
      ∧ gateBit g (5 * i + 4) = (g i).b4 := by
  unfold gateBit; simp +decide [ Nat.add_mod ] ;
  norm_num [ Nat.add_div ]

/-- The signed bit `e` produced by `signed_target` matches `gateBitSign`. -/
lemma e_eq_gateBitSign (g : ℕ → Witness F) (j : ℕ) {b : F} (hgb : gateBit g j = b)
    (hbit : b = 0 ∨ b = 1) {e : ℤ} (he2 : (e : F) = 2 * b - 1) (he : e = 1 ∨ e = -1)
    (h2 : (2 : F) ≠ 0) : e = gateBitSign g j := by
  cases hbit <;> simp_all +decide [ gateBitSign ];
  · cases he <;> simp_all +decide;
    exact h2 ( by linear_combination' he2 );
  · rcases he with ( rfl | rfl ) <;> norm_num at *;
    grind +extAll

/-- Per sub-step advance using ONLY the x-condition `k ≢ ±1`; the t-condition `t ≠ 0`
    is supplied by `tne_of_holds` (the constraints + prime order), not by `2k ≢ ±1`. -/
lemma gate_step_advance' (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    {xT yT b s1 xi yi xo yo : F}
    (hTns : c.Nonsingular xT yT)
    (hI : c.Nonsingular xi yi)
    (hQ : c.Nonsingular xT ((2 * b - 1) * yT))
    (hbit : b = 0 ∨ b = 1)
    (hTne : Point.some _ _ hTns ≠ 0)
    (k : ℤ) (hIk : Point.some _ _ hI = k • Point.some _ _ hTns)
    (hkx1 : ¬ ((c.order : ℤ) ∣ (k - 1))) (hkx2 : ¬ ((c.order : ℤ) ∣ (k + 1)))
    (hh : singleBitHolds b xT yT s1 xi yi xo yo) :
    xi ≠ xT ∧ (2 * xi + xT - s1 * s1 ≠ 0) ∧
      ∃ (hO : c.Nonsingular xo yo) (e : ℤ),
        (e = 1 ∨ e = -1) ∧ (e : F) = 2 * b - 1 ∧
          Point.some _ _ hO = (2 * k + e) • Point.some _ _ hTns := by
  obtain ⟨e, he, he'⟩ := signed_target c c.short hTns hQ hbit
  have hxne : xi ≠ xT := by
    apply x_ne_xT_of_ne_base c hI hTns
    · contrapose! hkx1
      have hd : (k - 1) • Point.some _ _ hTns = 0 := by
        rw [sub_smul, one_smul, ← hIk, hkx1, sub_self]
      exact (zsmul_eq_zero_iff_order_dvd c hTne _).1 hd
    · contrapose! hkx2
      rw [← zsmul_eq_zero_iff_order_dvd c hTne, add_zsmul, one_zsmul, ← hIk, hkx2,
        neg_add_cancel]
  have htne : 2 * xi + xT - s1 * s1 ≠ 0 := tne_of_holds c h2 hodd hI hh
  obtain ⟨hO, hOeq⟩ := singleBit_sound c c.short b xT yT s1 xi yi xo yo hI hQ hxne htne hh
  refine ⟨hxne, htne, hO, e, he'.2, he'.1, ?_⟩
  rw [hOeq, hIk, he]
  module

/-- **Producing variant of `gate_block`.** One gate block deriving the output point's
    nonsingularity rather than asserting it: from the *input* point `a0` on-curve (only) plus the
    constraint `Holds` and the base, it chains the five `gate_step_advance'`s and *produces* `a5`
    (existentially). The leaner-interface analog of EndoMul's `gate_advance` — so the deployed
    soundness needs no per-row `GateValid` bundle, only the threaded input. -/
lemma gate_block_produce (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] (g : ℕ → Witness F) (i : ℕ)
    (h2 : (2 : F) ≠ 0)
    {T : c.Point} (hTne : T ≠ 0)
    (hTns : c.Nonsingular (g i).xT (g i).yT) (hTeq : T = Point.some _ _ hTns)
    (ha0ns : c.Nonsingular (g i).x0 (g i).y0) (hh : Holds (g i))
    (ha0 : Point.some _ _ ha0ns = gateLadder g (5 * i) • T)
    (hodd : c.order ≠ 2)
    (hnd : ∀ ℓ, ℓ < 5 →
        ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) - 1)
          ∧ ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) + 1)) :
    NonDegen (g i) ∧ ∃ ha5ns : c.Nonsingular (g i).x5 (g i).y5,
      Point.some _ _ ha5ns = gateLadder g (5 * i + 5) • T := by
  have hT0 : Point.some _ _ hTns ≠ 0 := by rw [← hTeq]; exact hTne
  obtain ⟨_hdec, hsb0, hsb1, hsb2, hsb3, hsb4⟩ := hh
  obtain ⟨gb0, gb1, gb2, gb3, gb4⟩ := gateBit_block g i
  have bit : ∀ {x : F}, x * x - x = 0 → x = 0 ∨ x = 1 := by
    intro x hx
    rcases mul_eq_zero.mp (show x * (x - 1) = 0 by linear_combination hx) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  have ha0' : Point.some _ _ ha0ns = gateLadder g (5 * i) • Point.some _ _ hTns := by
    rw [hTeq] at ha0; exact ha0
  obtain ⟨hx0, ht0, hO0, e0, hepm0, hef0, hOeq0⟩ :=
    gate_step_advance' c h2 hodd hTns ha0ns (signed_target_nonsingular c c.short hTns (bit hsb0.1))
      (bit hsb0.1) hT0 (gateLadder g (5 * i)) ha0'
      (hnd 0 (by omega)).1 (hnd 0 (by omega)).2 hsb0
  have ha1 : Point.some _ _ hO0 = gateLadder g (5 * i + 1) • Point.some _ _ hTns := by
    rw [hOeq0, e_eq_gateBitSign g (5 * i) gb0 (bit hsb0.1) hef0 hepm0 h2, ← gateLadder_succ]
  obtain ⟨hx1, ht1, hO1, e1, hepm1, hef1, hOeq1⟩ :=
    gate_step_advance' c h2 hodd hTns hO0 (signed_target_nonsingular c c.short hTns (bit hsb1.1))
      (bit hsb1.1) hT0 (gateLadder g (5 * i + 1)) ha1
      (hnd 1 (by omega)).1 (hnd 1 (by omega)).2 hsb1
  have ha2 : Point.some _ _ hO1 = gateLadder g (5 * i + 2) • Point.some _ _ hTns := by
    rw [hOeq1, e_eq_gateBitSign g (5 * i + 1) gb1 (bit hsb1.1) hef1 hepm1 h2, ← gateLadder_succ]
  obtain ⟨hx2, ht2, hO2, e2, hepm2, hef2, hOeq2⟩ :=
    gate_step_advance' c h2 hodd hTns hO1 (signed_target_nonsingular c c.short hTns (bit hsb2.1))
      (bit hsb2.1) hT0 (gateLadder g (5 * i + 2)) ha2
      (hnd 2 (by omega)).1 (hnd 2 (by omega)).2 hsb2
  have ha3 : Point.some _ _ hO2 = gateLadder g (5 * i + 3) • Point.some _ _ hTns := by
    rw [hOeq2, e_eq_gateBitSign g (5 * i + 2) gb2 (bit hsb2.1) hef2 hepm2 h2, ← gateLadder_succ]
  obtain ⟨hx3, ht3, hO3, e3, hepm3, hef3, hOeq3⟩ :=
    gate_step_advance' c h2 hodd hTns hO2 (signed_target_nonsingular c c.short hTns (bit hsb3.1))
      (bit hsb3.1) hT0 (gateLadder g (5 * i + 3)) ha3
      (hnd 3 (by omega)).1 (hnd 3 (by omega)).2 hsb3
  have ha4 : Point.some _ _ hO3 = gateLadder g (5 * i + 4) • Point.some _ _ hTns := by
    rw [hOeq3, e_eq_gateBitSign g (5 * i + 3) gb3 (bit hsb3.1) hef3 hepm3 h2, ← gateLadder_succ]
  obtain ⟨hx4, ht4, hO4, e4, hepm4, hef4, hOeq4⟩ :=
    gate_step_advance' c h2 hodd hTns hO3 (signed_target_nonsingular c c.short hTns (bit hsb4.1))
      (bit hsb4.1) hT0 (gateLadder g (5 * i + 4)) ha4
      (hnd 4 (by omega)).1 (hnd 4 (by omega)).2 hsb4
  have ha5 : Point.some _ _ hO4 = gateLadder g (5 * i + 5) • Point.some _ _ hTns := by
    rw [hOeq4, e_eq_gateBitSign g (5 * i + 4) gb4 (bit hsb4.1) hef4 hepm4 h2, ← gateLadder_succ]
  exact ⟨⟨hx0, hx1, hx2, hx3, hx4, ht0, ht1, ht2, ht3, ht4⟩, hO4, by rw [hTeq]; exact ha5⟩

/-- **Full producing variant of `gate_block`.** Like `gate_block_produce`, but returns ALL five
    derived accumulator points `a1..a5` (not just `a5`) so the register subsystem
    (`scalarMul`/`scalarMul_type2`, which consume the whole `GateStep` bundle) can be fed the
    derived `GateValid` data. Same five-`gate_step_advance'` chain. -/
lemma gate_block_full (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)]
    [Fact (Nat.Prime c.order)] (g : ℕ → Witness F) (i : ℕ)
    (h2 : (2 : F) ≠ 0)
    {T : c.Point} (hTne : T ≠ 0)
    (hTns : c.Nonsingular (g i).xT (g i).yT) (hTeq : T = Point.some _ _ hTns)
    (ha0ns : c.Nonsingular (g i).x0 (g i).y0) (hh : Holds (g i))
    (ha0 : Point.some _ _ ha0ns = gateLadder g (5 * i) • T)
    (hodd : c.order ≠ 2)
    (hnd : ∀ ℓ, ℓ < 5 →
        ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) - 1)
          ∧ ¬ (c.order : ℤ) ∣ (gateLadder g (5 * i + ℓ) + 1)) :
    NonDegen (g i) ∧ ∃ (a1 : c.Nonsingular (g i).x1 (g i).y1)
      (_a2 : c.Nonsingular (g i).x2 (g i).y2) (_a3 : c.Nonsingular (g i).x3 (g i).y3)
      (_a4 : c.Nonsingular (g i).x4 (g i).y4) (a5 : c.Nonsingular (g i).x5 (g i).y5),
      Point.some _ _ a5 = gateLadder g (5 * i + 5) • T := by
  have hT0 : Point.some _ _ hTns ≠ 0 := by rw [← hTeq]; exact hTne
  obtain ⟨_hdec, hsb0, hsb1, hsb2, hsb3, hsb4⟩ := hh
  obtain ⟨gb0, gb1, gb2, gb3, gb4⟩ := gateBit_block g i
  have bit : ∀ {x : F}, x * x - x = 0 → x = 0 ∨ x = 1 := by
    intro x hx
    rcases mul_eq_zero.mp (show x * (x - 1) = 0 by linear_combination hx) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  have ha0' : Point.some _ _ ha0ns = gateLadder g (5 * i) • Point.some _ _ hTns := by
    rw [hTeq] at ha0; exact ha0
  obtain ⟨hx0, ht0, hO0, e0, hepm0, hef0, hOeq0⟩ :=
    gate_step_advance' c h2 hodd hTns ha0ns (signed_target_nonsingular c c.short hTns (bit hsb0.1))
      (bit hsb0.1) hT0 (gateLadder g (5 * i)) ha0'
      (hnd 0 (by omega)).1 (hnd 0 (by omega)).2 hsb0
  have ha1 : Point.some _ _ hO0 = gateLadder g (5 * i + 1) • Point.some _ _ hTns := by
    rw [hOeq0, e_eq_gateBitSign g (5 * i) gb0 (bit hsb0.1) hef0 hepm0 h2, ← gateLadder_succ]
  obtain ⟨hx1, ht1, hO1, e1, hepm1, hef1, hOeq1⟩ :=
    gate_step_advance' c h2 hodd hTns hO0 (signed_target_nonsingular c c.short hTns (bit hsb1.1))
      (bit hsb1.1) hT0 (gateLadder g (5 * i + 1)) ha1
      (hnd 1 (by omega)).1 (hnd 1 (by omega)).2 hsb1
  have ha2 : Point.some _ _ hO1 = gateLadder g (5 * i + 2) • Point.some _ _ hTns := by
    rw [hOeq1, e_eq_gateBitSign g (5 * i + 1) gb1 (bit hsb1.1) hef1 hepm1 h2, ← gateLadder_succ]
  obtain ⟨hx2, ht2, hO2, e2, hepm2, hef2, hOeq2⟩ :=
    gate_step_advance' c h2 hodd hTns hO1 (signed_target_nonsingular c c.short hTns (bit hsb2.1))
      (bit hsb2.1) hT0 (gateLadder g (5 * i + 2)) ha2
      (hnd 2 (by omega)).1 (hnd 2 (by omega)).2 hsb2
  have ha3 : Point.some _ _ hO2 = gateLadder g (5 * i + 3) • Point.some _ _ hTns := by
    rw [hOeq2, e_eq_gateBitSign g (5 * i + 2) gb2 (bit hsb2.1) hef2 hepm2 h2, ← gateLadder_succ]
  obtain ⟨hx3, ht3, hO3, e3, hepm3, hef3, hOeq3⟩ :=
    gate_step_advance' c h2 hodd hTns hO2 (signed_target_nonsingular c c.short hTns (bit hsb3.1))
      (bit hsb3.1) hT0 (gateLadder g (5 * i + 3)) ha3
      (hnd 3 (by omega)).1 (hnd 3 (by omega)).2 hsb3
  have ha4 : Point.some _ _ hO3 = gateLadder g (5 * i + 4) • Point.some _ _ hTns := by
    rw [hOeq3, e_eq_gateBitSign g (5 * i + 3) gb3 (bit hsb3.1) hef3 hepm3 h2, ← gateLadder_succ]
  obtain ⟨hx4, ht4, hO4, e4, hepm4, hef4, hOeq4⟩ :=
    gate_step_advance' c h2 hodd hTns hO3 (signed_target_nonsingular c c.short hTns (bit hsb4.1))
      (bit hsb4.1) hT0 (gateLadder g (5 * i + 4)) ha4
      (hnd 4 (by omega)).1 (hnd 4 (by omega)).2 hsb4
  have ha5 : Point.some _ _ hO4 = gateLadder g (5 * i + 5) • Point.some _ _ hTns := by
    rw [hOeq4, e_eq_gateBitSign g (5 * i + 4) gb4 (bit hsb4.1) hef4 hepm4 h2, ← gateLadder_succ]
  exact ⟨⟨hx0, hx1, hx2, hx3, hx4, ht0, ht1, ht2, ht3, ht4⟩, hO0, hO1, hO2, hO3, hO4,
    by rw [hTeq]; exact ha5⟩

/-- Final-accumulator coordinates after `m` rows (row 0's `x0`/`y0` if `m = 0`, else row `(m-1)`'s
    `x5`/`y5`) — the leaner interface's stand-in for `P m`. -/
def accX (g : ℕ → Witness F) : ℕ → F
  | 0 => (g 0).x0
  | k + 1 => (g k).x5

def accY (g : ℕ → Witness F) : ℕ → F
  | 0 => (g 0).y0
  | k + 1 => (g k).y5

/-- **Producing variant of `gate_chain` — the leaner fold.** Over `m` rows
    the prover supplies only `Holds` per row, the base nonsingularity (row 0), the column threading
    (`(g (i+1)).x0 = (g i).x5`), and the initial accumulator `2·T`; every intermediate point's
    nonsingularity is *derived* (`gate_block_produce`), threaded through the chain. Same conclusion
    as `gate_chain` (`= s·T`, every row `NonDegen`), but no per-row `GateValid` bundle — the leaner
    interface, exactly as EndoMul's `endoMul`/`accumulator_chain` replaced its `EndoStep` bundle.

    Proof sketch (mirror `gate_chain` + EndoMul's `key` induction): induct on `k ≤ m` proving
    `∃ hk : Nonsingular (accX g k) (accY g k), Point.some _ _ hk = gateLadder g (5*k) • T`; base
    `k=0` is `hP0ns`/`hP0` (`gateLadder g 0 = 2`); step feeds the threaded input to
    `gate_block_produce` (base transported to row `k` via `hbase`), yielding row `k`'s `NonDegen`
    and the next point. Read off `hfin := key m`, `s = gateLadder g (5m)` via `hs`. -/
lemma gate_chain_produce (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (m : ℕ) (g : ℕ → Witness F) (T : c.Point) (s : ℤ) (hTne : T ≠ 0)
    (hholds : ∀ i, i < m → Holds (g i))
    (hTns : c.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).x0 = (g i).x5 ∧ (g (i + 1)).y0 = (g i).y5)
    (hP0ns : c.Nonsingular (g 0).x0 (g 0).y0)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    (hND : ∀ n, n < 5 * m →
        ¬ (c.order : ℤ) ∣ (gateLadder g n - 1) ∧ ¬ (c.order : ℤ) ∣ (gateLadder g n + 1)
          ∧ ¬ (c.order : ℤ) ∣ (2 * gateLadder g n - 1)
          ∧ ¬ (c.order : ℤ) ∣ (2 * gateLadder g n + 1))
    (hs : s = gateLadder g (5 * m)) :
    ∃ hfin : c.Nonsingular (accX g m) (accY g m),
      Point.some _ _ hfin = s • T ∧ ∀ i, i < m → NonDegen (g i) := by
  -- Point congruence across equal coordinates (local analog of `Gate.EndoMul.some_congr`).
  have some_congr : ∀ {x x' y y' : F} (h : c.Nonsingular x y) (h' : c.Nonsingular x' y'),
      x = x' → y = y' → Point.some _ _ h = Point.some _ _ h' := by
    intro x x' y y' h h' hx hy; subst hx; subst hy; rfl
  -- coordinate threading: row `k`'s input column equals the accumulator at step `k`
  have haccP : ∀ k, k < m → (g k).x0 = accX g k ∧ (g k).y0 = accY g k := by
    intro k hk
    cases k with
    | zero => exact ⟨rfl, rfl⟩
    | succ j => exact hthread j hk
  -- per-step accumulator nonsingularity + point value + accumulated non-degeneracy
  have key : ∀ k, k ≤ m → ∃ hk : c.Nonsingular (accX g k) (accY g k),
      Point.some _ _ hk = gateLadder g (5 * k) • T ∧ (∀ i, i < k → NonDegen (g i)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨hP0ns, ?_, ?_⟩
      · change Point.some (g 0).x0 (g 0).y0 hP0ns = gateLadder g (5 * 0) • T
        rw [hP0]; simp only [Nat.mul_zero, gateLadder_zero]
      · intro i hi; omega
    | succ j ih =>
      intro hj1
      have hj' : j < m := by omega
      obtain ⟨hk, hPk, hNDk⟩ := ih (by omega)
      -- transport the base nonsingularity to row `j`
      obtain ⟨hbx, hby⟩ := hbase j hj'
      have hTns_j : c.Nonsingular (g j).xT (g j).yT := by rw [hbx, hby]; exact hTns
      have hTeq_j : T = Point.some _ _ hTns_j := by
        rw [hTeq]; exact some_congr hTns hTns_j hbx.symm hby.symm
      -- transport the threaded input accumulator to row `j`'s input column
      obtain ⟨hx0, hy0⟩ := haccP j hj'
      have ha0ns_j : c.Nonsingular (g j).x0 (g j).y0 := by rw [hx0, hy0]; exact hk
      have ha0_j : Point.some _ _ ha0ns_j = gateLadder g (5 * j) • T := by
        rw [some_congr ha0ns_j hk hx0 hy0]; exact hPk
      obtain ⟨hNDj, ha5ns, ha5eq⟩ :=
        gate_block_produce c g j h2 hTne hTns_j hTeq_j ha0ns_j (hholds j hj') ha0_j hodd
          (fun ℓ _ => ⟨(hND (5 * j + ℓ) (by omega)).1, (hND (5 * j + ℓ) (by omega)).2.1⟩)
      -- `accX g (j+1) = (g j).x5` and `gateLadder g (5*(j+1)) = gateLadder g (5*j+5)` defeq
      refine ⟨ha5ns, ?_, ?_⟩
      · rw [show 5 * (j + 1) = 5 * j + 5 from by ring]; exact ha5eq
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact hNDk i h
        · subst h; exact hNDj
  obtain ⟨hfin, hPfin, hNDfin⟩ := key m le_rfl
  exact ⟨hfin, by rw [hs]; exact hPfin, hNDfin⟩

/-- **`GateStep`-producing fold (leaner interface).** From `Holds` per row + base + threading +
    initial accumulator `2·T`, derives the full per-row `GateStep` bundle (every `a0..a5` via
    `gate_block_full`) together with the threaded point sequence `P` — exactly the inputs the
    register subsystem (`scalarMul`/`scalarMul_type2`) consumes. The `scaleFast2` analog of
    `gate_chain_produce`, replacing the prover-supplied `GateValid`/`GateStep`. -/
lemma gateStep_chain (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (m : ℕ) (g : ℕ → Witness F) (T : c.Point) (hTne : T ≠ 0)
    (hholds : ∀ i, i < m → Holds (g i))
    (hTns : c.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).x0 = (g i).x5 ∧ (g (i + 1)).y0 = (g i).y5)
    (hP0ns : c.Nonsingular (g 0).x0 (g 0).y0)
    (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    (hND : ∀ n, n < 5 * m →
        ¬ (c.order : ℤ) ∣ (gateLadder g n - 1) ∧ ¬ (c.order : ℤ) ∣ (gateLadder g n + 1)) :
    ∃ (gs : ∀ i, i < m → GateStep c (g i)) (P : ℕ → c.Point),
      (∀ i (hi : i < m), T = Point.some _ _ (gs i hi).hT)
        ∧ (∀ i (hi : i < m), P i = Point.some _ _ (gs i hi).a0)
        ∧ (∀ i (hi : i < m), P (i + 1) = Point.some _ _ (gs i hi).a5)
        ∧ P 0 = (2 : ℤ) • T := by
  -- Point congruence across equal coordinates (local analog of `Gate.EndoMul.some_congr`).
  have some_congr : ∀ {x x' y y' : F} (h : c.Nonsingular x y) (h' : c.Nonsingular x' y'),
      x = x' → y = y' → Point.some _ _ h = Point.some _ _ h' := by
    intro x x' y y' h h' hx hy; subst hx; subst hy; rfl
  -- coordinate threading: row `k`'s input column equals the accumulator at step `k`
  have haccP : ∀ k, k < m → (g k).x0 = accX g k ∧ (g k).y0 = accY g k := by
    intro k hk
    cases k with
    | zero => exact ⟨rfl, rfl⟩
    | succ j => exact hthread j hk
  -- per-step accumulator nonsingularity + point value + accumulated full `GateStep`
  have key : ∀ k, k ≤ m → ∃ hk : c.Nonsingular (accX g k) (accY g k),
      Point.some _ _ hk = gateLadder g (5 * k) • T ∧ (∀ i, i < k → GateStep c (g i)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨hP0ns, ?_, ?_⟩
      · change Point.some (g 0).x0 (g 0).y0 hP0ns = gateLadder g (5 * 0) • T
        rw [hP0]; simp only [Nat.mul_zero, gateLadder_zero]
      · intro i hi; omega
    | succ j ih =>
      intro hj1
      have hj' : j < m := by omega
      obtain ⟨hk, hPk, hGSk⟩ := ih (by omega)
      -- transport the base nonsingularity to row `j`
      obtain ⟨hbx, hby⟩ := hbase j hj'
      have hTns_j : c.Nonsingular (g j).xT (g j).yT := by rw [hbx, hby]; exact hTns
      have hTeq_j : T = Point.some _ _ hTns_j := by
        rw [hTeq]; exact some_congr hTns hTns_j hbx.symm hby.symm
      -- transport the threaded input accumulator to row `j`'s input column
      obtain ⟨hx0, hy0⟩ := haccP j hj'
      have ha0ns_j : c.Nonsingular (g j).x0 (g j).y0 := by rw [hx0, hy0]; exact hk
      have ha0_j : Point.some _ _ ha0ns_j = gateLadder g (5 * j) • T := by
        rw [some_congr ha0ns_j hk hx0 hy0]; exact hPk
      obtain ⟨nd, a1, a2, a3, a4, a5, ha5eq⟩ :=
        gate_block_full c g j h2 hTne hTns_j hTeq_j ha0ns_j (hholds j hj') ha0_j hodd
          (fun ℓ _ => hND (5 * j + ℓ) (by omega))
      -- the full per-row `GateStep` bundle at row `j`
      have hGSj : GateStep c (g j) :=
        ⟨ha0ns_j, a1, a2, a3, a4, a5, hTns_j, hholds j hj',
          nd.x0, nd.x1, nd.x2, nd.x3, nd.x4, nd.t0, nd.t1, nd.t2, nd.t3, nd.t4⟩
      -- `accX g (j+1) = (g j).x5` and `gateLadder g (5*(j+1)) = gateLadder g (5*j+5)` defeq
      refine ⟨a5, ?_, ?_⟩
      · rw [show 5 * (j + 1) = 5 * j + 5 from by ring]; exact ha5eq
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact hGSk i h
        · subst h; exact hGSj
  choose kf hkf using key
  -- kf : ∀ k, k ≤ m → c.Nonsingular (accX g k) (accY g k)
  -- hkf k hk : Point.some _ _ (kf k hk) = gateLadder g (5*k) • T ∧ (∀ i < k, GateStep c (g i))
  have gs := (hkf m le_rfl).2
  refine ⟨gs, fun k => if hk : k ≤ m then Point.some _ _ (kf k hk) else 0, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact hTeq.trans (some_congr hTns (gs i hi).hT (hbase i hi).1.symm (hbase i hi).2.symm)
  · intro i hi
    simp only [dif_pos (le_of_lt hi)]
    exact some_congr (kf i (le_of_lt hi)) (gs i hi).a0 (haccP i hi).1.symm (haccP i hi).2.symm
  · intro i hi
    simp only [dif_pos (Nat.succ_le_of_lt hi)]
    exact some_congr (kf (i + 1) (Nat.succ_le_of_lt hi)) (gs i hi).a5 rfl rfl
  · simp only [dif_pos (Nat.zero_le m)]
    rw [(hkf 0 (Nat.zero_le m)).1]; simp only [Nat.mul_zero, gateLadder_zero]

/-- **VarBaseMul correctness + soundness via the forbidden band (leaner interface).** For any
    witness satisfying the gate constraints (`Holds` per row) at the real init `P₀ = 2·T`, in the
    one-wrap regime, if the ladder top `s` avoids the forbidden band `forbiddenValues order`, the
    `m` rows compute the final accumulator `= s·T` and every row is `NonDegen`. The prover supplies
    only `Holds` + base + threading + initial — no per-row `GateValid` bundle (`gate_chain_produce`
    derives the accumulator nonsingularity). -/
theorem varBaseMul_forbidden_correct (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (m : ℕ) (g : ℕ → Witness F) (T : c.Point) (s : ℤ) (hTne : T ≠ 0)
    (hholds : ∀ i, i < m → Holds (g i))
    (hTns : c.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).x0 = (g i).x5 ∧ (g (i + 1)).y0 = (g i).y5)
    (hP0ns : c.Nonsingular (g 0).x0 (g 0).y0) (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    (hreg₁ : 2 ^ (5 * m - 1) < c.order) (hreg₂ : c.order < 2 ^ (5 * m))
    (hq4 : c.order % 4 = 1)
    (hs : s = gateLadder g (5 * m)) (hnf : s ∉ forbiddenValues c.order) :
    ∃ hfin : c.Nonsingular (accX g m) (accY g m),
      Point.some _ _ hfin = s • T ∧ ∀ i, i < m → NonDegen (g i) := by
  have hnf' : ∀ t ∈ Ladder.forbiddenResidues, ¬ (c.order : ℤ) ∣ (gateLadder g (5 * m) - t) := by
    intro t ht hdvd; exact hnf ⟨t, ht, by rw [hs]; exact hdvd⟩
  exact gate_chain_produce c m g T s hTne hholds hTns hTeq hbase hthread hP0ns hP0 h2 hodd
    (Ladder.ladder_nondegen_tight c.order (5 * m) c.order_prime hq4 hreg₁ hreg₂
      (gateLadder g) (gateBitSign g) (gateLadder_zero g) (fun j _ => gateBitSign_eq g j)
      (fun j _ => gateLadder_succ g j) hnf') hs

/-- **VarBaseMul correctness + soundness in the sub-wrap regime (leaner interface) — no forbidden
    check.** When `3·2^(5m) ≤ order` the whole ladder fits below the order, so every row is
    `NonDegen` unconditionally. Prover supplies only `Holds` + base + threading + initial. -/
theorem varBaseMul_subwrap_correct (c : WeierstrassCurve.Affine F)
    [Fact (c.a₁ = 0 ∧ c.a₂ = 0 ∧ c.a₃ = 0)] [Fact (Nat.Prime c.order)]
    (m : ℕ) (g : ℕ → Witness F) (T : c.Point) (s : ℤ) (hTne : T ≠ 0)
    (hholds : ∀ i, i < m → Holds (g i))
    (hTns : c.Nonsingular (g 0).xT (g 0).yT) (hTeq : T = Point.some _ _ hTns)
    (hbase : ∀ i, i < m → (g i).xT = (g 0).xT ∧ (g i).yT = (g 0).yT)
    (hthread : ∀ i, i + 1 < m → (g (i + 1)).x0 = (g i).x5 ∧ (g (i + 1)).y0 = (g i).y5)
    (hP0ns : c.Nonsingular (g 0).x0 (g 0).y0) (hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T)
    (h2 : (2 : F) ≠ 0) (hodd : c.order ≠ 2)
    (hsub : 3 * 2 ^ (5 * m) ≤ c.order) (hs : s = gateLadder g (5 * m)) :
    ∃ hfin : c.Nonsingular (accX g m) (accY g m),
      Point.some _ _ hfin = s • T ∧ ∀ i, i < m → NonDegen (g i) :=
  gate_chain_produce c m g T s hTne hholds hTns hTeq hbase hthread hP0ns hP0 h2 hodd
    (Ladder.ladder_subwrap_nondegen c.order (5 * m) hsub
      (gateLadder g) (gateBitSign g) (gateLadder_zero g) (fun j _ => gateBitSign_eq g j)
      (fun j _ => gateLadder_succ g j)) hs

end Kimchi.Circuit.VarBaseMul
