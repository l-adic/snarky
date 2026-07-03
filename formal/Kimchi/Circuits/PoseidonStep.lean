import Kimchi.Circuit
import Kimchi.Gate.Poseidon

/-!
# End-to-end soundness for a chained `Poseidon` circuit

The composition proof for the Poseidon permutation gate, completing the set alongside
`VarBaseMulStep` / `EndoMulStep` / `EndoScalarStep`. Unlike the EC gates there is no external
Mathlib spec — the gate *defines* the permutation — so the "intended operation" is the Poseidon
round function iterated over the chain. A chain of `m` `Poseidon` rows (each five rounds
`state' = MDS·sbox(state) + roundConstants`) is reconstructed as a concrete `Circuit`, and we prove
any satisfying witness computes the `5m`-fold round iteration of the initial state.

Structurally this is the simplest chain: Poseidon lays its rows *consecutively* and a row's output
state `s5` lives in the next row's cols 0–2, which is exactly that row's input state `s0` — the same
physical cells. So the state threading is definitional (no copy constraints at all), and the only
per-row datum is the gate's round-constant coefficient row (a parameter here). The composition is a
plain fold of the row permutation, its per-row step read from `Satisfies` via the gate constraints.
-/

namespace Kimchi.Gate.Poseidon

open Kimchi.Gate (Row)

variable {F : Type*}

/-- One Poseidon round as a function: `(o0,o1,o2) = MDS·sbox(x0,x1,x2) + (r0,r1,r2)`. -/
def round [CommRing F] (r0 r1 r2 x0 x1 x2 : F) : F × F × F :=
  ( r0 + m00 * x0 ^ 7 + m01 * x1 ^ 7 + m02 * x2 ^ 7
  , r1 + m10 * x0 ^ 7 + m11 * x1 ^ 7 + m12 * x2 ^ 7
  , r2 + m20 * x0 ^ 7 + m21 * x1 ^ 7 + m22 * x2 ^ 7 )

/-- `roundHolds` says the outputs are exactly one round of the inputs. -/
theorem roundHolds_iff [CommRing F] (x0 x1 x2 o0 o1 o2 r0 r1 r2 : F) :
    roundHolds x0 x1 x2 o0 o1 o2 r0 r1 r2 ↔ (o0, o1, o2) = round r0 r1 r2 x0 x1 x2 := by
  simp only [roundHolds, round, Prod.mk.injEq, sub_eq_zero]

/-- Apply a round to a packed state triple. -/
def roundP [CommRing F] (r0 r1 r2 : F) (p : F × F × F) : F × F × F :=
  round r0 r1 r2 p.1 p.2.1 p.2.2

/-- One row's permutation: the five rounds of a `Poseidon` row (constants `c`, in the gate's
    coefficient layout) applied to the input state. -/
def rowPerm [CommRing F] (c : Array F) (s : F × F × F) : F × F × F :=
  roundP (c.getD 12 0) (c.getD 13 0) (c.getD 14 0)
    (roundP (c.getD 9 0) (c.getD 10 0) (c.getD 11 0)
      (roundP (c.getD 6 0) (c.getD 7 0) (c.getD 8 0)
        (roundP (c.getD 3 0) (c.getD 4 0) (c.getD 5 0)
          (roundP (c.getD 0 0) (c.getD 1 0) (c.getD 2 0) s))))

/-- **Per-row I/O.** A satisfying `Poseidon` row sends its input state (`curr` cols 0–2) to its
    output state (`next` cols 0–2) by exactly one application of `rowPerm`. -/
theorem holds_rowPerm [CommRing F] (coeffs : Array F) (curr next : Row F)
    (h : holds coeffs curr next) :
    (next.getD 0 0, next.getD 1 0, next.getD 2 0)
      = rowPerm coeffs (curr.getD 0 0, curr.getD 1 0, curr.getD 2 0) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [roundHolds_iff] at h1 h2 h3 h4 h5
  simp only [rowPerm, roundP, ← h1, ← h2, ← h3, ← h4, ← h5]

/-- The chain permutation: fold `rowPerm` over rows `0 … k-1`. -/
def chainPerm [CommRing F] (coeffs : ℕ → Array F) (s : F × F × F) : ℕ → F × F × F
  | 0 => s
  | k + 1 => rowPerm (coeffs k) (chainPerm coeffs s k)

end Kimchi.Gate.Poseidon

namespace Kimchi.Circuit.Poseidon

open Kimchi.Gate.Poseidon
open Kimchi.Circuit (Cell Satisfies gatesHold)

variable {F : Type*} [CommRing F] [DecidableEq F]

/-- Gate `i`'s `Poseidon` row carries its round-constant coefficient row `coeffs i`; the state
    threading is definitional (consecutive rows share cells), so no copy wiring is needed. -/
def posGate (c : Array F) : Kimchi.Circuit.Gate F :=
  { kind := .poseidon, coeffs := c, wires := #[] }

/-- The reconstructed `m`-row `Poseidon` chain with per-row round constants `coeffs`. -/
def posCircuit (m : ℕ) (coeffs : ℕ → Array F) : Kimchi.Circuit.Circuit F :=
  { publicInputSize := 0
  , gates := Array.ofFn (n := m) fun idx => posGate (coeffs idx.val) }

@[simp] theorem posCircuit_size (m : ℕ) (coeffs : ℕ → Array F) :
    (posCircuit m coeffs).gates.size = m := by simp [posCircuit]

/-- The row of gate `i` reconstructs to `posGate (coeffs i)`. -/
theorem gateAt_pos (m i : ℕ) (coeffs : ℕ → Array F) (hi : i < m) :
    (posCircuit m coeffs).gateAt i = posGate (coeffs i) := by
  rw [Circuit.gateAt, posCircuit, getD_ofFn_lt _ _ _ _ hi]

/-- **End-to-end soundness for the reconstructed `Poseidon` chain.** Any witness satisfying
    `posCircuit m coeffs` computes the `5m`-round Poseidon permutation: the state at row `m`
    (cols 0–2) is the chain fold of the per-row permutations applied to the initial state (row 0,
    cols 0–2). Each row's five-round step is *derived* from `gatesHold`; the state threading is
    definitional. -/
theorem circuit_sound (m : ℕ) (coeffs : ℕ → Array F)
    (w : Kimchi.Circuit.Witness F) (pub : Array F)
    (hsat : Satisfies (posCircuit m coeffs) w pub) :
    ((w.row m).getD 0 0, (w.row m).getD 1 0, (w.row m).getD 2 0)
      = chainPerm coeffs ((w.row 0).getD 0 0, (w.row 0).getD 1 0, (w.row 0).getD 2 0) m := by
  obtain ⟨hgates, _⟩ := hsat
  have hstep : ∀ k, k < m → holds (coeffs k) (w.row k) (w.row (k + 1)) := by
    intro k hk
    have hg := hgates k (by rw [posCircuit_size]; omega)
    rw [gateAt_pos m k coeffs hk] at hg
    exact hg
  have key : ∀ k, k ≤ m →
      ((w.row k).getD 0 0, (w.row k).getD 1 0, (w.row k).getD 2 0)
        = chainPerm coeffs ((w.row 0).getD 0 0, (w.row 0).getD 1 0, (w.row 0).getD 2 0) k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ j ih =>
      intro hk
      rw [chainPerm, holds_rowPerm (coeffs j) (w.row j) (w.row (j + 1)) (hstep j (by omega)),
        ih (by omega)]
  exact key m (le_refl m)

end Kimchi.Circuit.Poseidon
