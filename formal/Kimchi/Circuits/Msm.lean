import Kimchi.Circuits.VarBaseMulStep

/-!
# Rung 2: the parametric `n`-term multi-scalar multiplication

`acc + ∑ᵢ [sᵢ]·Gᵢ` — the core of the verifier's Lagrange-base / IPA MSM, as scale-and-combine
blocks folded through their `CompleteAdd`s. Block `i` occupies rows `[i·(2m+2), (i+1)·(2m+2))`:
an init `CompleteAdd` (doubling the block's base into the chain's input accumulator), the `2m`-row
`VarBaseMul` chain, and the combine whose first input is the *previous* combine's output (block 0:
the external accumulator) and whose second input is the chain's output. This is the real dump's
layout (`fixtures/msm2_step.json`: blocks of `2m+2` rows, uniform and contiguous).

The circuit is **recursive** (`msmCircuit m (n+1) = (msmCircuit m n).append (block n)`), so
soundness is a structural induction: `Satisfies.of_append` hands the prefix to the induction
hypothesis, `Satisfies.of_embed` projects the last block's chain, and `blockStep` (init doubling →
`scaleFast1` → combine) advances the accumulator by `[sₙ]·Tₙ`.

Per-block hypotheses mirror the single-term theorems (base on curve, full-width forbidden-band
exclusion); each combine's `inf = 0` is a hypothesis (`hinfs`) — an `n`-fold statement under
flagged verticals would enumerate first-failure prefixes, and the per-term vertical case is
already fully handled by `scaleCombine_sound`'s disjunction. `y ≠ 0` everywhere is derived from
the odd group order.
-/

namespace Kimchi.Circuit.VarBaseMul

open Kimchi.Gate.VarBaseMul WeierstrassCurve.Affine
open Kimchi.Circuit (Cell Satisfies)
open CompElliptic.Curves.Pasta CompElliptic.Fields.Pasta Kimchi.Pasta

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Layout -/

/-- Block `i` starts at row `i·(2m+2)`. -/
def blockOff (m i : ℕ) : ℕ := i * (2 * m + 2)

/-- Block `i`'s chain starts one row in (after the init add). -/
def chainOff (m i : ℕ) : ℕ := blockOff m i + 1

/-- Block `i`'s combine row (the last row of the block). -/
def cbRow (m i : ℕ) : ℕ := blockOff m i + 2 * m + 1

/-- Block `i`'s init `CompleteAdd`: inputs tied (`x₁ = x₂`, `y₁ = y₂`) and to the chain's base
    cells; output into the chain's input accumulator. -/
def msmInit (m i : ℕ) : Kimchi.Circuit.Gate F :=
  { kind := .completeAdd, coeffs := #[]
  , wires := #[(blockOff m i, 2), (blockOff m i, 3), (chainOff m i, 0), (chainOff m i, 1),
               (chainOff m i, 2), (chainOff m i, 3), (blockOff m i, 6)] }

/-- Block `i`'s combine: input 1 the previous combine's output (block 0: self-loops — the
    external accumulator); input 2 the chain's output (the last `Zero` row `blockOff + 2m`). -/
def msmComb (m i : ℕ) : Kimchi.Circuit.Gate F :=
  { kind := .completeAdd, coeffs := #[]
  , wires :=
      if i = 0 then
        #[(cbRow m 0, 0), (cbRow m 0, 1), (blockOff m 0 + 2 * m, 0), (blockOff m 0 + 2 * m, 1),
          (cbRow m 0, 4), (cbRow m 0, 5), (cbRow m 0, 6)]
      else
        #[(cbRow m (i - 1), 4), (cbRow m (i - 1), 5),
          (blockOff m i + 2 * m, 0), (blockOff m i + 2 * m, 1),
          (cbRow m i, 4), (cbRow m i, 5), (cbRow m i, 6)] }

omit [Field F] [DecidableEq F] in
theorem msmComb_get2 (m i : ℕ) (d : Cell) :
    (msmComb m i (F := F)).wires.getD 2 d = (blockOff m i + 2 * m, 0) := by
  by_cases h : i = 0 <;> simp [msmComb, h]

omit [Field F] [DecidableEq F] in
theorem msmComb_get3 (m i : ℕ) (d : Cell) :
    (msmComb m i (F := F)).wires.getD 3 d = (blockOff m i + 2 * m, 1) := by
  by_cases h : i = 0 <;> simp [msmComb, h]

omit [Field F] [DecidableEq F] in
theorem msmComb_get0_succ (m i : ℕ) (hi : i ≠ 0) (d : Cell) :
    (msmComb m i (F := F)).wires.getD 0 d = (cbRow m (i - 1), 4) := by
  simp [msmComb, hi]

omit [Field F] [DecidableEq F] in
theorem msmComb_get1_succ (m i : ℕ) (hi : i ≠ 0) (d : Cell) :
    (msmComb m i (F := F)).wires.getD 1 d = (cbRow m (i - 1), 5) := by
  simp [msmComb, hi]

/-- One block: init, the chain (wires shifted to the block's rows), the combine. -/
def msmBlock (m i : ℕ) : Array (Kimchi.Circuit.Gate F) :=
  Array.ofFn (n := 2 * m + 2) fun j =>
    if j.val = 0 then msmInit m i
    else if j.val < 2 * m + 1 then
      ((vbmCircuit m).gateAt (j.val - 1)).shiftWires (chainOff m i)
    else msmComb m i

/-- The `n`-term MSM circuit, built block by block. -/
def msmCircuit (m : ℕ) : ℕ → Kimchi.Circuit.Circuit F
  | 0 => { publicInputSize := 0, gates := #[] }
  | n + 1 => (msmCircuit m n).append (msmBlock m n)

@[simp] theorem msm_size (m n : ℕ) :
    (msmCircuit m n (F := F)).gates.size = n * (2 * m + 2) := by
  induction n with
  | zero => simp [msmCircuit]
  | succ k ih =>
    show ((msmCircuit m k).append (msmBlock m k)).gates.size = _
    rw [Circuit.size_append, ih]
    simp [msmBlock]
    ring

@[simp] theorem msm_pubSize (m n : ℕ) :
    (msmCircuit m n (F := F)).publicInputSize = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

/-- The last block's row `j` within `msmCircuit m (n+1)`. -/
theorem gateAt_msm_last (m n j : ℕ) (hj : j < 2 * m + 2) :
    (msmCircuit m (n + 1) (F := F)).gateAt (n * (2 * m + 2) + j)
      = (if j = 0 then msmInit m n
         else if j < 2 * m + 1 then
           ((vbmCircuit m (F := F)).gateAt (j - 1)).shiftWires (chainOff m n)
         else msmComb m n) := by
  show ((msmCircuit m n).append (msmBlock m n)).gateAt _ = _
  have h := Circuit.gateAt_append_right (msmCircuit m n (F := F)) (msmBlock m n) j
    (by simp [msmBlock]; omega)
  rw [msm_size] at h
  rw [h]
  simp [msmBlock]

/-! ## Soundness -/

/-- Block `i`'s ladder scalar. -/
def msmScalar (m : ℕ) (w : Kimchi.Circuit.Witness F) (i : ℕ) : ℤ :=
  gateLadder (gwit (w.shift (chainOff m i))) (5 * m)

/-- **One block advances the accumulator.** Within `msmCircuit m (n+1)`, block `n`'s init doubles
    its base into the chain, the chain computes `[sₙ]·Tₙ`, and the combine (with `inf = 0`) adds
    it to the point `Q` sitting in its first-input cells. -/
theorem blockStep (μ n : ℕ) (w : Kimchi.Circuit.Witness VestaBaseField)
    (pub : Array VestaBaseField)
    (hsat : Satisfies (msmCircuit (μ + 1) (n + 1) (F := VestaBaseField)) w pub)
    (T : Vesta.curve.toAffine.Point)
    (hTns : Vesta.curve.toAffine.Nonsingular
      (gwit (w.shift (chainOff (μ + 1) n)) 0).xT (gwit (w.shift (chainOff (μ + 1) n)) 0).yT)
    (hTeq : T = Point.some _ _ hTns)
    (hbits : 5 * (μ + 1) ≤ pastaFieldBits)
    (hnf : 5 * (μ + 1) = pastaFieldBits →
      msmScalar (μ + 1) w n ∉ forbiddenValues Vesta.curve.toAffine.order)
    (hinf : (Kimchi.Gate.AddComplete.ofRow (w.row (cbRow (μ + 1) n))).inf = 0)
    (Q : Vesta.curve.toAffine.Point)
    (hIn : Vesta.curve.toAffine.Nonsingular
      (Kimchi.Gate.AddComplete.ofRow (w.row (cbRow (μ + 1) n))).x1
      (Kimchi.Gate.AddComplete.ofRow (w.row (cbRow (μ + 1) n))).y1)
    (hQ : Point.some _ _ hIn = Q) :
    ∃ hOut : Vesta.curve.toAffine.Nonsingular
        (w.cell (cbRow (μ + 1) n, 4)) (w.cell (cbRow (μ + 1) n, 5)),
      Point.some _ _ hOut = Q + msmScalar (μ + 1) w n • T := by
  have ha4 : Vesta.curve.toAffine.a₁ = 0 ∧ Vesta.curve.toAffine.a₂ = 0
      ∧ Vesta.curve.toAffine.a₃ = 0 ∧ Vesta.curve.toAffine.a₄ = 0 := ⟨rfl, rfl, rfl, rfl⟩
  -- the chain, embedded at `chainOff`
  have hemb : Satisfies (vbmCircuit (μ + 1)) (w.shift (chainOff (μ + 1) n)) #[] := by
    refine Satisfies.of_embed (host := msmCircuit (μ + 1) (n + 1)) (block := vbmCircuit (μ + 1))
      (chainOff (μ + 1) n) (by rw [msm_pubSize]; omega) ?_ ?_ hsat
    · rw [vbmCircuit_size, msm_size]
      show n * (2 * (μ + 1) + 2) + 1 + 2 * (μ + 1) ≤ (n + 1) * (2 * (μ + 1) + 2)
      ring_nf
      omega
    · intro r hr
      rw [vbmCircuit_size] at hr
      have h := gateAt_msm_last (F := VestaBaseField) (μ + 1) n (1 + r) (by omega)
      rw [show n * (2 * (μ + 1) + 2) + (1 + r) = chainOff (μ + 1) n + r by
        show _ = n * (2 * (μ + 1) + 2) + 1 + r; omega] at h
      rw [h, if_neg (by omega), if_pos (by omega)]
      congr 2
      omega
  obtain ⟨hg, hc⟩ := hsat
  -- the init row: identity + copies give the chain's init `[2]·Tₙ`
  have hgat0 : (msmCircuit (μ + 1) (n + 1) (F := VestaBaseField)).gateAt (blockOff (μ + 1) n)
      = msmInit (μ + 1) n := by
    have h := gateAt_msm_last (F := VestaBaseField) (μ + 1) n 0 (by omega)
    rwa [if_pos rfl, Nat.add_zero] at h
  have hrow0 : blockOff (μ + 1) n < (msmCircuit (μ + 1) (n + 1)
      (F := VestaBaseField)).gates.size := by
    rw [msm_size]
    show n * (2 * (μ + 1) + 2) < (n + 1) * (2 * (μ + 1) + 2)
    ring_nf
    omega
  have c0 : ∀ j, j < 7 → w.cell (blockOff (μ + 1) n, j)
      = w.cell ((msmInit (μ + 1) n (F := VestaBaseField)).wires.getD j
          (blockOff (μ + 1) n, j)) := by
    intro j hj
    have := hc (blockOff (μ + 1) n) hrow0 j hj
    rwa [hgat0] at this
  have h0cons : Kimchi.Gate.AddComplete.Holds
      (Kimchi.Gate.AddComplete.ofRow (w.row (blockOff (μ + 1) n))) := by
    have := hg (blockOff (μ + 1) n) hrow0
    rwa [hgat0] at this
  have exT : (Kimchi.Gate.AddComplete.ofRow (w.row (blockOff (μ + 1) n))).x1
      = (gwit (w.shift (chainOff (μ + 1) n)) 0).xT := by
    show w.cell (blockOff (μ + 1) n, 0) = ((w.shift (chainOff (μ + 1) n)).row 0).getD 0 0
    rw [Witness.row_shift]
    calc w.cell (blockOff (μ + 1) n, 0)
        = w.cell (blockOff (μ + 1) n, 2) := c0 0 (by omega)
      _ = w.cell (chainOff (μ + 1) n, 0) := c0 2 (by omega)
      _ = (w.row (chainOff (μ + 1) n + 0)).getD 0 0 := rfl
  have eyT : (Kimchi.Gate.AddComplete.ofRow (w.row (blockOff (μ + 1) n))).y1
      = (gwit (w.shift (chainOff (μ + 1) n)) 0).yT := by
    show w.cell (blockOff (μ + 1) n, 1) = ((w.shift (chainOff (μ + 1) n)).row 0).getD 1 0
    rw [Witness.row_shift]
    calc w.cell (blockOff (μ + 1) n, 1)
        = w.cell (blockOff (μ + 1) n, 3) := c0 1 (by omega)
      _ = w.cell (chainOff (μ + 1) n, 1) := c0 3 (by omega)
      _ = (w.row (chainOff (μ + 1) n + 0)).getD 1 0 := rfl
  have hT0 : Vesta.curve.toAffine.Nonsingular
      (Kimchi.Gate.AddComplete.ofRow (w.row (blockOff (μ + 1) n))).x1
      (Kimchi.Gate.AddComplete.ofRow (w.row (blockOff (μ + 1) n))).y1 := by
    rw [exT, eyT]; exact hTns
  obtain ⟨h3, hdbl⟩ := Kimchi.Circuit.InitGrounding.completeAdd_doubles Vesta.curve.toAffine ha4
    (w.row (blockOff (μ + 1) n)) hT0 (c0 0 (by omega)) (c0 1 (by omega)) h0cons
    (Point.y_ne_zero_of_odd_order rfl rfl vesta_order_odd hT0) (by decide)
  have ex0 : (gwit (w.shift (chainOff (μ + 1) n)) 0).x0
      = (Kimchi.Gate.AddComplete.ofRow (w.row (blockOff (μ + 1) n))).x3 := by
    show ((w.shift (chainOff (μ + 1) n)).row 0).getD 2 0 = w.cell (blockOff (μ + 1) n, 4)
    rw [Witness.row_shift]
    exact (c0 4 (by omega)).symm
  have ey0 : (gwit (w.shift (chainOff (μ + 1) n)) 0).y0
      = (Kimchi.Gate.AddComplete.ofRow (w.row (blockOff (μ + 1) n))).y3 := by
    show ((w.shift (chainOff (μ + 1) n)).row 0).getD 3 0 = w.cell (blockOff (μ + 1) n, 5)
    rw [Witness.row_shift]
    exact (c0 5 (by omega)).symm
  have hP0ns : Vesta.curve.toAffine.Nonsingular
      (gwit (w.shift (chainOff (μ + 1) n)) 0).x0
      (gwit (w.shift (chainOff (μ + 1) n)) 0).y0 := by
    rw [ex0, ey0]; exact h3
  have hP0 : Point.some _ _ hP0ns = (2 : ℤ) • T := by
    rw [Point.some_congr hP0ns h3 ex0 ey0, hdbl,
      Point.some_congr hT0 hTns exT eyT, ← hTeq]
  -- the chain: `[sₙ]·Tₙ`
  obtain ⟨hfin, hpt, -⟩ := varBaseMul_circuit_scaleFast1 (μ + 1) (w.shift (chainOff (μ + 1) n))
    #[] hemb T (msmScalar (μ + 1) w n) (hTeq ▸ Point.some_ne_zero _) hTns hTeq hP0ns hP0
    hbits rfl hnf
  -- the combine row
  have hgatC : (msmCircuit (μ + 1) (n + 1) (F := VestaBaseField)).gateAt (cbRow (μ + 1) n)
      = msmComb (μ + 1) n := by
    have h := gateAt_msm_last (F := VestaBaseField) (μ + 1) n (2 * (μ + 1) + 1) (by omega)
    rwa [if_neg (by omega), if_neg (by omega),
      show n * (2 * (μ + 1) + 2) + (2 * (μ + 1) + 1) = cbRow (μ + 1) n by
        show _ = blockOff (μ + 1) n + 2 * (μ + 1) + 1
        show _ = n * (2 * (μ + 1) + 2) + 2 * (μ + 1) + 1
        omega] at h
  have hrowC : cbRow (μ + 1) n < (msmCircuit (μ + 1) (n + 1)
      (F := VestaBaseField)).gates.size := by
    rw [msm_size]
    show blockOff (μ + 1) n + 2 * (μ + 1) + 1 < (n + 1) * (2 * (μ + 1) + 2)
    show n * (2 * (μ + 1) + 2) + 2 * (μ + 1) + 1 < (n + 1) * (2 * (μ + 1) + 2)
    ring_nf
    omega
  have hCcons : Kimchi.Gate.AddComplete.Holds
      (Kimchi.Gate.AddComplete.ofRow (w.row (cbRow (μ + 1) n))) := by
    have := hg (cbRow (μ + 1) n) hrowC
    rwa [hgatC] at this
  have hcc2 := hc (cbRow (μ + 1) n) hrowC 2 (by omega)
  have hcc3 := hc (cbRow (μ + 1) n) hrowC 3 (by omega)
  rw [hgatC, msmComb_get2] at hcc2
  rw [hgatC, msmComb_get3] at hcc3
  have ex2 : (Kimchi.Gate.AddComplete.ofRow (w.row (cbRow (μ + 1) n))).x2
      = accX (gwit (w.shift (chainOff (μ + 1) n))) (μ + 1) := by
    show w.cell (cbRow (μ + 1) n, 2)
      = ((w.shift (chainOff (μ + 1) n)).row (2 * μ + 1)).getD 0 0
    rw [Witness.row_shift]
    calc w.cell (cbRow (μ + 1) n, 2)
        = w.cell (blockOff (μ + 1) n + 2 * (μ + 1), 0) := hcc2
      _ = w.cell (chainOff (μ + 1) n + (2 * μ + 1), 0) := by
          rw [show blockOff (μ + 1) n + 2 * (μ + 1) = chainOff (μ + 1) n + (2 * μ + 1) by
            show _ = blockOff (μ + 1) n + 1 + (2 * μ + 1); omega]
  have ey2 : (Kimchi.Gate.AddComplete.ofRow (w.row (cbRow (μ + 1) n))).y2
      = accY (gwit (w.shift (chainOff (μ + 1) n))) (μ + 1) := by
    show w.cell (cbRow (μ + 1) n, 3)
      = ((w.shift (chainOff (μ + 1) n)).row (2 * μ + 1)).getD 1 0
    rw [Witness.row_shift]
    calc w.cell (cbRow (μ + 1) n, 3)
        = w.cell (blockOff (μ + 1) n + 2 * (μ + 1), 1) := hcc3
      _ = w.cell (chainOff (μ + 1) n + (2 * μ + 1), 1) := by
          rw [show blockOff (μ + 1) n + 2 * (μ + 1) = chainOff (μ + 1) n + (2 * μ + 1) by
            show _ = blockOff (μ + 1) n + 1 + (2 * μ + 1); omega]
  have h2C : Vesta.curve.toAffine.Nonsingular
      (Kimchi.Gate.AddComplete.ofRow (w.row (cbRow (μ + 1) n))).x2
      (Kimchi.Gate.AddComplete.ofRow (w.row (cbRow (μ + 1) n))).y2 := by
    rw [ex2, ey2]; exact hfin
  have heq2 : Point.some _ _ h2C = msmScalar (μ + 1) w n • T :=
    (Point.some_congr h2C hfin ex2 ey2).trans hpt
  rcases Kimchi.Gate.AddComplete.sound Vesta.curve.toAffine ha4
      (Kimchi.Gate.AddComplete.ofRow (w.row (cbRow (μ + 1) n))) hIn h2C hCcons
      (Point.y_ne_zero_of_odd_order rfl rfl vesta_order_odd hIn) (by decide) with
    ⟨hinf1, -⟩ | ⟨-, h3C, hsum⟩
  · rw [hinf] at hinf1
    exact absurd hinf1 zero_ne_one
  · refine ⟨h3C, ?_⟩
    calc Point.some _ _ h3C
        = Point.some _ _ hIn + Point.some _ _ h2C := hsum.symm
      _ = Q + msmScalar (μ + 1) w n • T := by rw [hQ, heq2]

/-- **The `n`-term MSM.** Any witness satisfying `msmCircuit m (n+1)` — with each block's base on
    the curve (`hTnsAll`/`hT`), the bit budget, the per-block forbidden-band exclusions, and every
    combine's `inf` clear — has the last combine's output cells carrying

        `acc + ∑_{i ≤ n} [sᵢ]·Tᵢ`

    where `acc` is the point in block 0's first-input cells and `sᵢ` block `i`'s ladder scalar. -/
theorem msm_sound (μ : ℕ) (w : Kimchi.Circuit.Witness VestaBaseField)
    (pub : Array VestaBaseField) (T : ℕ → Vesta.curve.toAffine.Point)
    (hT : ∀ i (hns : Vesta.curve.toAffine.Nonsingular
        (gwit (w.shift (chainOff (μ + 1) i)) 0).xT (gwit (w.shift (chainOff (μ + 1) i)) 0).yT),
      T i = Point.some _ _ hns)
    (hbits : 5 * (μ + 1) ≤ pastaFieldBits)
    (hAccNs : Vesta.curve.toAffine.Nonsingular
      (w.cell (cbRow (μ + 1) 0, 0)) (w.cell (cbRow (μ + 1) 0, 1))) :
    ∀ n, Satisfies (msmCircuit (μ + 1) (n + 1) (F := VestaBaseField)) w pub →
    (∀ i, i ≤ n → Vesta.curve.toAffine.Nonsingular
        (gwit (w.shift (chainOff (μ + 1) i)) 0).xT
        (gwit (w.shift (chainOff (μ + 1) i)) 0).yT) →
    (∀ i, i ≤ n → 5 * (μ + 1) = pastaFieldBits →
        msmScalar (μ + 1) w i ∉ forbiddenValues Vesta.curve.toAffine.order) →
    (∀ i, i ≤ n → (Kimchi.Gate.AddComplete.ofRow (w.row (cbRow (μ + 1) i))).inf = 0) →
    ∃ hOut : Vesta.curve.toAffine.Nonsingular
        (w.cell (cbRow (μ + 1) n, 4)) (w.cell (cbRow (μ + 1) n, 5)),
      Point.some _ _ hOut = Point.some _ _ hAccNs
        + ∑ i ∈ Finset.range (n + 1), msmScalar (μ + 1) w i • T i := by
  intro n
  induction n with
  | zero =>
    intro hsat hTnsAll hnfAll hinfsAll
    obtain ⟨hOut, hout⟩ := blockStep μ 0 w pub hsat (T 0) (hTnsAll 0 (by omega))
      (hT 0 (hTnsAll 0 (by omega))) hbits (hnfAll 0 (by omega)) (hinfsAll 0 (by omega))
      (Point.some _ _ hAccNs) hAccNs rfl
    exact ⟨hOut, by rw [hout, Finset.sum_range_one]⟩
  | succ k ih =>
    intro hsat hTnsAll hnfAll hinfsAll
    -- the prefix: the first k+1 blocks
    have hpre : Satisfies (msmCircuit (μ + 1) (k + 1) (F := VestaBaseField)) w pub :=
      Satisfies.of_append (c := msmCircuit (μ + 1) (k + 1)) (gs := msmBlock (μ + 1) (k + 1)) hsat
    obtain ⟨hOutPrev, houtPrev⟩ := ih hpre (fun i hi => hTnsAll i (by omega))
      (fun i hi => hnfAll i (by omega)) (fun i hi => hinfsAll i (by omega))
    -- the last combine's input 1 is the previous combine's output (copy)
    have hc := hsat.2
    have hgatC : (msmCircuit (μ + 1) (k + 2) (F := VestaBaseField)).gateAt (cbRow (μ + 1) (k + 1))
        = msmComb (μ + 1) (k + 1) := by
      have h := gateAt_msm_last (F := VestaBaseField) (μ + 1) (k + 1) (2 * (μ + 1) + 1)
        (by omega)
      rwa [if_neg (by omega), if_neg (by omega),
        show (k + 1) * (2 * (μ + 1) + 2) + (2 * (μ + 1) + 1) = cbRow (μ + 1) (k + 1) by
          show _ = blockOff (μ + 1) (k + 1) + 2 * (μ + 1) + 1
          show _ = (k + 1) * (2 * (μ + 1) + 2) + 2 * (μ + 1) + 1
          omega] at h
    have hrowC : cbRow (μ + 1) (k + 1) < (msmCircuit (μ + 1) (k + 2)
        (F := VestaBaseField)).gates.size := by
      rw [msm_size]
      show (k + 1) * (2 * (μ + 1) + 2) + 2 * (μ + 1) + 1 < (k + 2) * (2 * (μ + 1) + 2)
      ring_nf
      omega
    have hi0 := hc (cbRow (μ + 1) (k + 1)) hrowC 0 (by omega)
    have hi1 := hc (cbRow (μ + 1) (k + 1)) hrowC 1 (by omega)
    rw [hgatC, msmComb_get0_succ (μ + 1) (k + 1) (by omega)] at hi0
    rw [hgatC, msmComb_get1_succ (μ + 1) (k + 1) (by omega)] at hi1
    have hIn : Vesta.curve.toAffine.Nonsingular
        (Kimchi.Gate.AddComplete.ofRow (w.row (cbRow (μ + 1) (k + 1)))).x1
        (Kimchi.Gate.AddComplete.ofRow (w.row (cbRow (μ + 1) (k + 1)))).y1 := by
      show Vesta.curve.toAffine.Nonsingular
        (w.cell (cbRow (μ + 1) (k + 1), 0)) (w.cell (cbRow (μ + 1) (k + 1), 1))
      rw [hi0, hi1]
      exact hOutPrev
    have hQ : Point.some _ _ hIn
        = Point.some _ _ hAccNs + ∑ i ∈ Finset.range (k + 1), msmScalar (μ + 1) w i • T i := by
      rw [Point.some_congr hIn hOutPrev hi0 hi1, houtPrev]
    obtain ⟨hOut, hout⟩ := blockStep μ (k + 1) w pub hsat (T (k + 1))
      (hTnsAll (k + 1) (by omega)) (hT (k + 1) (hTnsAll (k + 1) (by omega))) hbits
      (hnfAll (k + 1) (by omega)) (hinfsAll (k + 1) (by omega)) _ hIn hQ
    refine ⟨hOut, ?_⟩
    rw [hout]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [add_assoc]

end Kimchi.Circuit.VarBaseMul
