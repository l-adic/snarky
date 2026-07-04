import Kimchi.Circuits.PoseidonStep
import Kimchi.Circuits.EndoScalarStep
import Kimchi.Circuits.ScaleCombinePub

/-!
# Rung 4: Fiat–Shamir inside the proof

The transcript-to-challenge pipeline, reconstructed whole from the real dump
(`fixtures/fiat_shamir_step.json`): a Poseidon sponge run over the public inputs, the squeezed
state split as `sq = lo + 2¹²⁸·hi` (the challenge truncation, one half of a double `Generic`
row), and the 128-bit challenge `lo` decoded by an `EndoMulScalar` chain whose final register is
copy-wired to `lo` — its crumbs *are* a base-4 decomposition of the truncated transcript output.
A final double `Generic` row computes the effective scalar `λ·a₈ + b₈` into the public output.

`fiatShamir_sound` is the statement the composition earns, purely over the public vector:

> the sponge output — `chainPerm coeffs (pub 0, pub 1, pub 2)`, a *function of the public
> inputs* — equals `nReconstruct (crumbs) + 2¹²⁸·hi`, and `pub 3 = toField (crumbs) λ`

for the ES block's crumb stream and some `hi`. I.e. the circuit's output is the endo-decode of a
challenge that the circuit itself derives from the Poseidon transcript — the challenge is no
longer a free hypothesis. (`λ` here is the concrete `vesta_lam`: this Pallas-base-field circuit
decodes a Wrap-side challenge.)

**Fidelity note.** `hi`'s range is not constrained by this circuit (nor by the dumped one): `lo`
is forced below `2¹²⁸` by the ES crumbs, but `sq = lo + 2¹²⁸·hi` admits aliasing mod `p` without a
range check on `hi`. The real protocol's challenge canonicity rests on that check; adding it (a
second decomposition block on `hi`) is mechanical and orthogonal to the composition proven here.

Two pieces of machinery earn their keep: `Satisfies.of_embed` (the Poseidon block, exact), and
the new `Satisfies.of_embed'` — the ES block's *first* row carries the dump's pin wires
(`n₀ → 0`, `a₀/b₀ → 2`) on cells the block model leaves self-looped, which the generalized
embedding permits.
-/

namespace Kimchi.Circuit.FiatShamir

open Kimchi.Gate.Poseidon (chainPerm)
open Kimchi.Circuit (Cell Satisfies genEval)
open Kimchi.Circuit.Poseidon (posGate posCircuit)
open Kimchi.Circuit.EndoScalar (esGate esCircuit esCircuit_size gateAt_es)
open Kimchi.Circuit.VarBaseMul (pubPin)
open CompElliptic.Fields.Pasta Kimchi.Pasta

/-- `2¹²⁸`, the challenge-truncation radix. -/
def fsP128 : PallasBaseField := 340282366920938463463374607431768211456

/-- Row offsets (the sponge output row, the split row, the ES block, the final row). -/
def spOut (mP : ℕ) : ℕ := 4 + mP
def splitRow (mP : ℕ) : ℕ := 5 + mP
def esOff (mP : ℕ) : ℕ := 6 + mP
def finRow (mP : ℕ) : ℕ := 14 + mP

/-- The sponge output row (`Zero`; carries the squeezed state in cols 0–2). -/
def fsZero : Kimchi.Circuit.Gate PallasBaseField := { kind := .zero, coeffs := #[], wires := #[] }

/-- The split row: gate 1 pins its cell 0 to `2` (the ES init constant, shared by the pin wires);
    gate 2 is the truncation `w₃ + 2¹²⁸·w₄ − w₅ = 0` with `w₃ ↔` the ES final register (`lo`),
    `w₄ = hi` (free), `w₅ ↔` the sponge output. -/
def fsSplit (mP : ℕ) : Kimchi.Circuit.Gate PallasBaseField :=
  { kind := .generic
  , coeffs := #[1, 0, 0, 0, -2, 1, fsP128, -1, 0, 0]
  , wires := #[(splitRow mP, 0), (splitRow mP, 1), (splitRow mP, 2),
               (esOff mP + 7, 1), (splitRow mP, 4), (spOut mP, 0), (splitRow mP, 6)] }

/-- The ES block's first row, with the dump's pin wires: `n₀ ↔` the final row's zero cell,
    `a₀/b₀ ↔` the split row's `2`-pinned cell. (The block model's row 0 is all self-loops, so
    `Satisfies.of_embed'` accepts these extra pins.) -/
def fsEs0 (mP : ℕ) : Kimchi.Circuit.Gate PallasBaseField :=
  { kind := .endoMulScalar, coeffs := #[]
  , wires := #[(finRow mP, 3), (esOff mP, 1), (splitRow mP, 0), (splitRow mP, 0),
               (esOff mP, 4), (esOff mP, 5), (esOff mP, 6)] }

/-- The ES segment: the pinned first row, then the chain rows shifted to the block's offset. -/
def fsEsSeg (mP : ℕ) : Array (Kimchi.Circuit.Gate PallasBaseField) :=
  Array.ofFn (n := 8) fun j =>
    if j.val = 0 then fsEs0 mP
    else (esGate j.val).shiftWires (esOff mP)

/-- The final row: gate 1 is the scale-and-add `λ·w₀ + w₁ − w₂ = 0` (`w₀ ↔ a₈`, `w₁ ↔ b₈`,
    `w₂ ↔` the public output); gate 2 pins its cell 3 to `0` (the `n₀` init source). -/
def fsFinal (mP : ℕ) : Kimchi.Circuit.Gate PallasBaseField :=
  { kind := .generic
  , coeffs := #[(vesta_lam : PallasBaseField), 1, -1, 0, 0, 1, 0, 0, 0, 0]
  , wires := #[(esOff mP + 7, 4), (esOff mP + 7, 5), (finRow mP, 2),
               (finRow mP, 3), (finRow mP, 4), (finRow mP, 5), (finRow mP, 6)] }

/-- The whole circuit: 4 public rows (3 sponge inputs, the output), the Poseidon block, the
    output row, the split, the ES block, the final scale-and-add — the dump's shape. -/
def fsCircuit (mP : ℕ) (coeffs : ℕ → Array PallasBaseField) : Kimchi.Circuit.Circuit
    PallasBaseField :=
  ((({ publicInputSize := 4
     , gates := #[pubPin (4, 0), pubPin (4, 1), pubPin (4, 2), pubPin (finRow mP, 2)] }
      : Kimchi.Circuit.Circuit PallasBaseField).append
    (Array.ofFn (n := mP) fun r => posGate (coeffs r.val))).append
    #[fsZero, fsSplit mP]).append
    (fsEsSeg mP) |>.append #[fsFinal mP]

@[simp] theorem fs_size (mP : ℕ) (coeffs : ℕ → Array PallasBaseField) :
    (fsCircuit mP coeffs).gates.size = 15 + mP := by
  simp [fsCircuit, fsEsSeg]
  omega

/-! ## Row lookups -/

/-- The base prefix (4 public rows). -/
private abbrev fsBase (mP : ℕ) : Kimchi.Circuit.Circuit PallasBaseField :=
  { publicInputSize := 4
  , gates := #[pubPin (4, 0), pubPin (4, 1), pubPin (4, 2), pubPin (finRow mP, 2)] }

private abbrev fsL1 (mP : ℕ) (coeffs : ℕ → Array PallasBaseField) :=
  (fsBase mP).append (Array.ofFn (n := mP) fun r => posGate (coeffs r.val))

private abbrev fsL2 (mP : ℕ) (coeffs : ℕ → Array PallasBaseField) :=
  (fsL1 mP coeffs).append #[fsZero, fsSplit mP]

private abbrev fsL3 (mP : ℕ) (coeffs : ℕ → Array PallasBaseField) :=
  (fsL2 mP coeffs).append (fsEsSeg mP)

@[simp] private theorem fsL1_size (mP : ℕ) (coeffs : ℕ → Array PallasBaseField) :
    (fsL1 mP coeffs).gates.size = 4 + mP := by simp

@[simp] private theorem fsL2_size (mP : ℕ) (coeffs : ℕ → Array PallasBaseField) :
    (fsL2 mP coeffs).gates.size = 6 + mP := by simp; omega

@[simp] private theorem fsL3_size (mP : ℕ) (coeffs : ℕ → Array PallasBaseField) :
    (fsL3 mP coeffs).gates.size = 14 + mP := by simp [fsEsSeg]; omega

theorem gateAt_fs_pub (mP : ℕ) (coeffs : ℕ → Array PallasBaseField) (j : ℕ) (hj : j < 4) :
    (fsCircuit mP coeffs).gateAt j
      = (fsBase mP).gates.getD j Kimchi.Circuit.defaultGate := by
  show ((fsL3 mP coeffs).append #[fsFinal mP]).gateAt j = _
  rw [Circuit.gateAt_append_left _ _ j (by simp [fsEsSeg]; omega),
    Circuit.gateAt_append_left _ _ j (by simp; omega),
    Circuit.gateAt_append_left _ _ j (by simp; omega),
    Circuit.gateAt_append_left _ _ j (by simp; omega)]
  rfl

theorem gateAt_fs_pos (mP : ℕ) (coeffs : ℕ → Array PallasBaseField) (r : ℕ) (hr : r < mP) :
    (fsCircuit mP coeffs).gateAt (4 + r) = posGate (coeffs r) := by
  show ((fsL3 mP coeffs).append #[fsFinal mP]).gateAt (4 + r) = _
  rw [Circuit.gateAt_append_left _ _ _ (by simp [fsEsSeg]; omega),
    Circuit.gateAt_append_left _ _ _ (by simp; omega),
    Circuit.gateAt_append_left _ _ _ (by simp; omega)]
  have h := Circuit.gateAt_append_right (fsBase mP)
    (Array.ofFn (n := mP) fun r => posGate (coeffs r.val)) r (by simpa using hr)
  rw [show (fsBase mP).gates.size = 4 from rfl] at h
  rw [h, Array.getElem_ofFn]

theorem gateAt_fs_zero (mP : ℕ) (coeffs : ℕ → Array PallasBaseField) :
    (fsCircuit mP coeffs).gateAt (spOut mP) = fsZero := by
  show ((fsL3 mP coeffs).append #[fsFinal mP]).gateAt _ = _
  rw [Circuit.gateAt_append_left _ _ _ (by simp [fsEsSeg, spOut]; omega),
    Circuit.gateAt_append_left _ _ _ (by simp [spOut])]
  have h := Circuit.gateAt_append_right (fsL1 mP coeffs) #[fsZero, fsSplit mP] 0
    (by show 0 < 2; decide)
  rw [fsL1_size] at h
  rw [show spOut mP = 4 + mP + 0 by show 4 + mP = _; omega]
  exact h

theorem gateAt_fs_split (mP : ℕ) (coeffs : ℕ → Array PallasBaseField) :
    (fsCircuit mP coeffs).gateAt (splitRow mP) = fsSplit mP := by
  show ((fsL3 mP coeffs).append #[fsFinal mP]).gateAt _ = _
  rw [Circuit.gateAt_append_left _ _ _ (by simp [fsEsSeg, splitRow]; omega),
    Circuit.gateAt_append_left _ _ _ (by simp [splitRow]; omega)]
  have h := Circuit.gateAt_append_right (fsL1 mP coeffs) #[fsZero, fsSplit mP] 1
    (by show 1 < 2; decide)
  rw [fsL1_size] at h
  rw [show splitRow mP = 4 + mP + 1 by show 5 + mP = _; omega]
  exact h

theorem gateAt_fs_es (mP : ℕ) (coeffs : ℕ → Array PallasBaseField) (j : ℕ) (hj : j < 8) :
    (fsCircuit mP coeffs).gateAt (esOff mP + j)
      = (if j = 0 then fsEs0 mP else (esGate j).shiftWires (esOff mP)) := by
  show ((fsL3 mP coeffs).append #[fsFinal mP]).gateAt _ = _
  rw [Circuit.gateAt_append_left _ _ _ (by simp [fsEsSeg, esOff]; omega)]
  have h := Circuit.gateAt_append_right (fsL2 mP coeffs) (fsEsSeg mP) j
    (by simp [fsEsSeg]; omega)
  rw [fsL2_size] at h
  rw [show esOff mP + j = 6 + mP + j by show 6 + mP + j = _; omega, h]
  simp only [fsEsSeg, Array.getElem_ofFn]

theorem gateAt_fs_final (mP : ℕ) (coeffs : ℕ → Array PallasBaseField) :
    (fsCircuit mP coeffs).gateAt (finRow mP) = fsFinal mP := by
  show ((fsL3 mP coeffs).append #[fsFinal mP]).gateAt _ = _
  have h := Circuit.gateAt_append_right (fsL3 mP coeffs) #[fsFinal mP] 0 (by show 0 < 1; decide)
  rw [fsL3_size] at h
  rw [show finRow mP = 14 + mP + 0 by show 14 + mP = _; omega]
  exact h

@[simp] theorem fs_pubSize (mP : ℕ) (coeffs : ℕ → Array PallasBaseField) :
    (fsCircuit mP coeffs).publicInputSize = 4 := rfl

/- Everything below goes through the row-lookup equations; sealing the circuit stops the
   elaborator from unfolding the nested-append gates array during unification. -/
attribute [irreducible] fsCircuit

/-! ## Soundness -/

/-- **Rung 4: Fiat–Shamir.** Any witness satisfying `fsCircuit mP coeffs` ties its public output
    to the transcript of its public inputs: for the ES block's crumb stream `cs` and some `hi`,

        `(chainPerm coeffs (pub 0, pub 1, pub 2) mP).1 = nReconstruct cs + 2¹²⁸·hi`
        `pub 3 = toField cs (vesta_lam)`

    — the sponge output (a *function of the public inputs*) equals the crumb-reconstructed
    challenge plus `2¹²⁸·hi`, and the output is that challenge's effective endo-scalar. The
    challenge is derived, not hypothesized. (`hi`'s range is the documented fidelity gap.) -/
theorem fiatShamir_sound (mP : ℕ) (coeffs : ℕ → Array PallasBaseField)
    (w : Kimchi.Circuit.Witness PallasBaseField) (pub : Array PallasBaseField)
    (hsat : Satisfies (fsCircuit mP coeffs) w pub) :
    ∃ hi : PallasBaseField,
      (chainPerm coeffs (pub.getD 0 0, pub.getD 1 0, pub.getD 2 0) mP).1
          = Kimchi.Circuit.EndoScalar.nReconstruct
              (Kimchi.Circuit.EndoScalar.chainCrumbs
                (Kimchi.Circuit.EndoScalar.gwit (w.shift (esOff mP))) 8)
            + fsP128 * hi
      ∧ pub.getD 3 0
          = Kimchi.Circuit.EndoScalar.toField
              (Kimchi.Circuit.EndoScalar.chainCrumbs
                (Kimchi.Circuit.EndoScalar.gwit (w.shift (esOff mP))) 8)
              (vesta_lam : PallasBaseField) := by
  -- the Poseidon block (exact embed: its wires are all defaults)
  have hpos : Satisfies (posCircuit mP coeffs) (w.shift 4) #[] := by
    refine Satisfies.of_embed (host := fsCircuit mP coeffs) (block := posCircuit mP coeffs) 4
      (by rw [fs_pubSize])
      (by rw [Kimchi.Circuit.Poseidon.posCircuit_size, fs_size]; omega)
      (fun r hr => ?_) hsat
    rw [Kimchi.Circuit.Poseidon.posCircuit_size] at hr
    rw [gateAt_fs_pos mP coeffs r hr, Kimchi.Circuit.Poseidon.gateAt_pos mP r coeffs hr]
    simp [Kimchi.Circuit.Gate.shiftWires, Kimchi.Circuit.Poseidon.posGate]
  -- the ES block (generalized embed: its first row carries the dump's pin wires)
  have hes : Satisfies (esCircuit 7) (w.shift (esOff mP)) #[] := by
    refine Satisfies.of_embed' (host := fsCircuit mP coeffs) (block := esCircuit 7) (esOff mP)
      (by rw [fs_pubSize]; show 4 ≤ 6 + mP; omega)
      (by rw [esCircuit_size, fs_size]; show 6 + mP + 8 ≤ 15 + mP; omega)
      (fun r hr => ?_) (fun r hr => ?_) (fun r j hr hj => ?_) hsat
    · rw [esCircuit_size] at hr
      rw [gateAt_fs_es mP coeffs r (by omega), gateAt_es 7 r (by omega)]
      by_cases h0 : r = 0
      · subst h0; rw [if_pos rfl]; rfl
      · rw [if_neg h0]; rfl
    · rw [esCircuit_size] at hr
      rw [gateAt_fs_es mP coeffs r (by omega), gateAt_es 7 r (by omega)]
      by_cases h0 : r = 0
      · subst h0; rw [if_pos rfl]; rfl
      · rw [if_neg h0]; rfl
    · rw [esCircuit_size] at hr
      by_cases h0 : r = 0
      · subst h0
        left
        rw [gateAt_es 7 0 (by omega)]
        interval_cases j <;> rfl
      · right
        rw [gateAt_fs_es mP coeffs r (by omega), if_neg h0, gateAt_es 7 r (by omega)]
        exact Kimchi.Circuit.Gate.wires_getD_shift _ _ _ _ _
  obtain ⟨hg, hc⟩ := hsat
  -- the public pins
  have pin : ∀ j t, j < 4 → (fsCircuit mP coeffs).gateAt j = pubPin t →
      pub.getD j 0 = w.cell t := by
    intro j t hj hgat
    have hgj := hg j (by rw [fs_size]; omega)
    rw [hgat] at hgj
    have heq : (w.row j).getD 0 0 = (fsCircuit mP coeffs).pubTerm pub j := by
      have h1 : Kimchi.Checker.Generic.eval (#[1, 0, 0, 0, 0] : Array PallasBaseField) (w.row j)
          = (fsCircuit mP coeffs).pubTerm pub j := hgj.1
      rwa [genEval] at h1
    have hpt : (fsCircuit mP coeffs).pubTerm pub j = pub.getD j 0 := by
      rw [Circuit.pubTerm, fs_pubSize, if_pos (show j < 4 by omega)]
    have hcj := hc j (by rw [fs_size]; omega) 0 (by omega)
    rw [hgat] at hcj
    have hw : (pubPin t (F := PallasBaseField)).wires.getD 0 (j, 0) = t := rfl
    rw [hw] at hcj
    calc pub.getD j 0 = (w.row j).getD 0 0 := by rw [heq, hpt]
      _ = w.cell t := hcj
  have e0 : pub.getD 0 0 = w.cell (4, 0) :=
    pin 0 (4, 0) (by omega) ((gateAt_fs_pub mP coeffs 0 (by omega)).trans rfl)
  have e1 : pub.getD 1 0 = w.cell (4, 1) :=
    pin 1 (4, 1) (by omega) ((gateAt_fs_pub mP coeffs 1 (by omega)).trans rfl)
  have e2 : pub.getD 2 0 = w.cell (4, 2) :=
    pin 2 (4, 2) (by omega) ((gateAt_fs_pub mP coeffs 2 (by omega)).trans rfl)
  have e3 : pub.getD 3 0 = w.cell (finRow mP, 2) :=
    pin 3 (finRow mP, 2) (by omega) ((gateAt_fs_pub mP coeffs 3 (by omega)).trans rfl)
  -- the transcript: the sponge output is `chainPerm` of the public inputs
  have hperm := Kimchi.Circuit.Poseidon.circuit_sound mP coeffs (w.shift 4) #[] hpos
  rw [Witness.row_shift, Witness.row_shift] at hperm
  have hsq : w.cell (spOut mP, 0)
      = (chainPerm coeffs (pub.getD 0 0, pub.getD 1 0, pub.getD 2 0) mP).1 := by
    have h1 := congrArg Prod.fst hperm
    simp only at h1
    rw [show spOut mP = 4 + mP from rfl]
    rw [e0, e1, e2]
    exact h1
  -- the split row: cell 0 pinned to 2, and the truncation equation
  have hgatS : (fsCircuit mP coeffs).gateAt (splitRow mP) = fsSplit mP :=
    gateAt_fs_split mP coeffs
  have hsplit := hg (splitRow mP) (by rw [fs_size]; show 5 + mP < 15 + mP; omega)
  rw [hgatS] at hsplit
  have hptS : (fsCircuit mP coeffs).pubTerm pub (splitRow mP) = 0 := by
    rw [Circuit.pubTerm, fs_pubSize,
      if_neg (show ¬ splitRow mP < 4 by show ¬ 5 + mP < 4; omega)]
  have hpin2 : (w.row (splitRow mP)).getD 0 0 = 2 := by
    have h1 : Kimchi.Checker.Generic.eval (fsSplit mP).coeffs (w.row (splitRow mP))
        = (fsCircuit mP coeffs).pubTerm pub (splitRow mP) := hsplit.1
    rw [hptS] at h1
    have h1' : (1 : PallasBaseField) * (w.row (splitRow mP)).getD 0 0
        + 0 * (w.row (splitRow mP)).getD 1 0 + 0 * (w.row (splitRow mP)).getD 2 0
        + 0 * ((w.row (splitRow mP)).getD 0 0 * (w.row (splitRow mP)).getD 1 0)
        + -2 = 0 := h1
    linear_combination h1'
  have htrunc : (w.row (splitRow mP)).getD 3 0
      + fsP128 * (w.row (splitRow mP)).getD 4 0
      - (w.row (splitRow mP)).getD 5 0 = 0 := by
    have h2 : Kimchi.Checker.Generic.eval2 (fsSplit mP).coeffs (w.row (splitRow mP)) = 0 :=
      hsplit.2
    have h2' : (1 : PallasBaseField) * (w.row (splitRow mP)).getD 3 0
        + fsP128 * (w.row (splitRow mP)).getD 4 0
        + -1 * (w.row (splitRow mP)).getD 5 0
        + 0 * ((w.row (splitRow mP)).getD 3 0 * (w.row (splitRow mP)).getD 4 0)
        + 0 = 0 := h2
    linear_combination h2'
  -- split copies: `lo ↔` the ES final register, `sq ↔` the sponge output
  have hcS3 := hc (splitRow mP) (by rw [fs_size]; show 5 + mP < 15 + mP; omega) 3 (by omega)
  have hcS5 := hc (splitRow mP) (by rw [fs_size]; show 5 + mP < 15 + mP; omega) 5 (by omega)
  rw [hgatS] at hcS3 hcS5
  have hlo : w.cell (splitRow mP, 3) = w.cell (esOff mP + 7, 1) := hcS3
  have hsq5 : w.cell (splitRow mP, 5) = w.cell (spOut mP, 0) := hcS5
  -- the ES init pins: row 0's host wires point at the `2` cell and the `0` cell
  have hgatE0 : (fsCircuit mP coeffs).gateAt (esOff mP) = fsEs0 mP := by
    have h := gateAt_fs_es mP coeffs 0 (by omega)
    rwa [if_pos rfl, Nat.add_zero] at h
  have hcE0 : ∀ j, j < 7 → w.cell (esOff mP, j)
      = w.cell ((fsEs0 mP).wires.getD j (esOff mP, j)) := by
    intro j hj
    have := hc (esOff mP) (by rw [fs_size]; show 6 + mP < 15 + mP; omega) j hj
    rwa [hgatE0] at this
  -- the final row: the scale-and-add and the `0` pin
  have hgatF : (fsCircuit mP coeffs).gateAt (finRow mP) = fsFinal mP := gateAt_fs_final mP coeffs
  have hfinal := hg (finRow mP) (by rw [fs_size]; show 14 + mP < 15 + mP; omega)
  rw [hgatF] at hfinal
  have hptF : (fsCircuit mP coeffs).pubTerm pub (finRow mP) = 0 := by
    rw [Circuit.pubTerm, fs_pubSize,
      if_neg (show ¬ finRow mP < 4 by show ¬ 14 + mP < 4; omega)]
  have hzero : (w.row (finRow mP)).getD 3 0 = 0 := by
    have h2 : Kimchi.Checker.Generic.eval2 (fsFinal mP).coeffs (w.row (finRow mP)) = 0 :=
      hfinal.2
    have h2' : (1 : PallasBaseField) * (w.row (finRow mP)).getD 3 0
        + 0 * (w.row (finRow mP)).getD 4 0 + 0 * (w.row (finRow mP)).getD 5 0
        + 0 * ((w.row (finRow mP)).getD 3 0 * (w.row (finRow mP)).getD 4 0)
        + 0 = 0 := h2
    linear_combination h2'
  have hscale : (vesta_lam : PallasBaseField) * (w.row (finRow mP)).getD 0 0
      + (w.row (finRow mP)).getD 1 0 - (w.row (finRow mP)).getD 2 0 = 0 := by
    have h1 : Kimchi.Checker.Generic.eval (fsFinal mP).coeffs (w.row (finRow mP))
        = (fsCircuit mP coeffs).pubTerm pub (finRow mP) := hfinal.1
    rw [hptF] at h1
    have h1' : (vesta_lam : PallasBaseField) * (w.row (finRow mP)).getD 0 0
        + 1 * (w.row (finRow mP)).getD 1 0 + -1 * (w.row (finRow mP)).getD 2 0
        + 0 * ((w.row (finRow mP)).getD 0 0 * (w.row (finRow mP)).getD 1 0)
        + 0 = 0 := h1
    linear_combination h1'
  have hcF0 := hc (finRow mP) (by rw [fs_size]; show 14 + mP < 15 + mP; omega) 0 (by omega)
  have hcF1 := hc (finRow mP) (by rw [fs_size]; show 14 + mP < 15 + mP; omega) 1 (by omega)
  rw [hgatF] at hcF0 hcF1
  -- the ES run: inits from the pins, then the circuit soundness at `vesta_lam`
  have ha0 : (Kimchi.Circuit.EndoScalar.gwit (w.shift (esOff mP)) 0).a0 = 2 := by
    show ((w.shift (esOff mP)).row 0).getD 2 0 = 2
    rw [Witness.row_shift]
    calc (w.row (esOff mP + 0)).getD 2 0 = w.cell (esOff mP, 2) := rfl
      _ = w.cell (splitRow mP, 0) := hcE0 2 (by omega)
      _ = 2 := hpin2
  have hb0 : (Kimchi.Circuit.EndoScalar.gwit (w.shift (esOff mP)) 0).b0 = 2 := by
    show ((w.shift (esOff mP)).row 0).getD 3 0 = 2
    rw [Witness.row_shift]
    calc (w.row (esOff mP + 0)).getD 3 0 = w.cell (esOff mP, 3) := rfl
      _ = w.cell (splitRow mP, 0) := hcE0 3 (by omega)
      _ = 2 := hpin2
  have hn0 : (Kimchi.Circuit.EndoScalar.gwit (w.shift (esOff mP)) 0).n0 = 0 := by
    show ((w.shift (esOff mP)).row 0).getD 0 0 = 0
    rw [Witness.row_shift]
    calc (w.row (esOff mP + 0)).getD 0 0 = w.cell (esOff mP, 0) := rfl
      _ = w.cell (finRow mP, 3) := hcE0 0 (by omega)
      _ = 0 := hzero
  obtain ⟨hES1, hES2⟩ := Kimchi.Circuit.EndoScalar.pallas_circuit_sound
    (vesta_lam : PallasBaseField) 7 (w.shift (esOff mP)) #[] hes ha0 hb0 hn0
  -- assemble
  refine ⟨(w.row (splitRow mP)).getD 4 0, ?_, ?_⟩
  · -- transcript = challenge + 2¹²⁸·hi
    have hn8 : (w.row (esOff mP + 7)).getD 1 0
        = Kimchi.Circuit.EndoScalar.nReconstruct
            (Kimchi.Circuit.EndoScalar.chainCrumbs
              (Kimchi.Circuit.EndoScalar.gwit (w.shift (esOff mP))) 8) := by
      calc (w.row (esOff mP + 7)).getD 1 0
          = ((w.shift (esOff mP)).row 7).getD 1 0 := by rw [Witness.row_shift]
        _ = _ := hES2
    rw [← hsq, ← hn8]
    show (w.row (spOut mP)).getD 0 0
      = (w.row (esOff mP + 7)).getD 1 0 + fsP128 * (w.row (splitRow mP)).getD 4 0
    have hlo' : (w.row (splitRow mP)).getD 3 0 = (w.row (esOff mP + 7)).getD 1 0 := hlo
    have hsq5' : (w.row (splitRow mP)).getD 5 0 = (w.row (spOut mP)).getD 0 0 := hsq5
    linear_combination -hsq5' - htrunc + hlo'
  · -- output = the effective scalar of the crumbs
    have ha8 : (w.row (finRow mP)).getD 0 0
        = (Kimchi.Circuit.EndoScalar.gwit (w.shift (esOff mP)) 7).a8 := by
      show w.cell (finRow mP, 0) = ((w.shift (esOff mP)).row 7).getD 4 0
      rw [Witness.row_shift]
      calc w.cell (finRow mP, 0) = w.cell (esOff mP + 7, 4) := hcF0
        _ = (w.row (esOff mP + 7)).getD 4 0 := rfl
    have hb8 : (w.row (finRow mP)).getD 1 0
        = (Kimchi.Circuit.EndoScalar.gwit (w.shift (esOff mP)) 7).b8 := by
      show w.cell (finRow mP, 1) = ((w.shift (esOff mP)).row 7).getD 5 0
      rw [Witness.row_shift]
      calc w.cell (finRow mP, 1) = w.cell (esOff mP + 7, 5) := hcF1
        _ = (w.row (esOff mP + 7)).getD 5 0 := rfl
    rw [e3]
    rw [← hES1]
    have := hscale
    rw [ha8, hb8] at this
    show (w.row (finRow mP)).getD 2 0 = _
    linear_combination -this

end Kimchi.Circuit.FiatShamir
