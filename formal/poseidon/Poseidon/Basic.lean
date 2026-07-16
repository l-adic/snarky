import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Fin.VecNotation
import CompElliptic.Fields.Pasta
import Poseidon.ConstantsFq
import Poseidon.ConstantsFp

/-!
# The kimchi Poseidon sponge

The Poseidon permutation and the duplex sponge automaton of kimchi's Fiat-Shamir transform,
transcribed from proof-systems `mina_poseidon` (`permutation.rs`, `poseidon.rs`,
`PlonkSpongeConstantsKimchi`): state width 3, rate 2, capacity 1; a permutation of 55 full
rounds, each applying the `x^7` S-box to every state element, then the full 3 × 3 MDS matrix,
then adding that round's constants (no initial ARK). The absorb/squeeze automaton tracks a
mode `absorbed n` / `squeezed n` with `n ≤ rate`; crossing the rate boundary (or switching
direction into `squeezed`) runs the permutation.

The width-3 state is the concrete triple `Triple F = F × F × F` rather than `Fin 3 → F`: the
compiler eta-expands function-valued definitions, under which a fold of rounds re-evaluates
its whole prefix at every component lookup — exponentially in the round count. Constructor
arguments are forced at construction, keeping the fold linear.

Everything is executable. `Fq` and `Fp` instantiate the sponge at the Vesta and Pallas base
fields with the generated `fq_kimchi` / `fp_kimchi` parameters (`PoseidonConstantsFq.lean` /
`PoseidonConstantsFp.lean`) — the sponges of kimchi proofs over Vesta and Pallas
respectively. Both validated against `mina_poseidon` absorb/squeeze traces by
`scripts/check_sponge_vectors.lean`.

The sponge is the *definitional* layer of the Fiat-Shamir instantiation: the security of the
transform (that these challenges behave as the abstract soundness hypotheses require) is a
separate, explicitly flagged assumption where the instantiation meets the soundness theorems.

## Contents

* `Triple`, `Params`, `sbox`, `fullRound`, `blockCipher` — the permutation.
* `Mode`, `State`, `init`, `absorb`, `squeeze`, `squeezeN` — the duplex automaton.
* `fqParams` / `fpParams` — the concrete `fq_kimchi` / `fp_kimchi` instantiations.
-/

namespace Poseidon

variable {F : Type*} [Field F]

/-! ## The permutation -/

/-- A width-3 state: the components `(s₀, s₁, s₂)`. -/
abbrev Triple (F : Type*) := F × F × F

/-- Poseidon parameters: one constant triple per round, and the MDS matrix as three rows. -/
structure Params (F : Type*) where
  roundConstants : Array (Triple F)
  mds : Triple (Triple F)

/-- The S-box `x ↦ x^7`. -/
def sbox (x : F) : F := x ^ 7

/-- One full round: S-box every state element, apply the MDS matrix, add the round
constants (`permutation.rs` `full_round`). -/
def fullRound (mds : Triple (Triple F)) (rc : Triple F) (s : Triple F) : Triple F :=
  let t0 := sbox s.1; let t1 := sbox s.2.1; let t2 := sbox s.2.2
  let m0 := mds.1; let m1 := mds.2.1; let m2 := mds.2.2
  (m0.1 * t0 + m0.2.1 * t1 + m0.2.2 * t2 + rc.1,
   m1.1 * t0 + m1.2.1 * t1 + m1.2.2 * t2 + rc.2.1,
   m2.1 * t0 + m2.2.1 * t1 + m2.2.2 * t2 + rc.2.2)

/-- The Poseidon permutation: the full rounds folded over the round-constant table
(`permutation.rs` `poseidon_block_cipher`, no initial ARK). -/
def blockCipher (p : Params F) (s : Triple F) : Triple F :=
  p.roundConstants.foldl (fun s rc => fullRound p.mds rc s) s

/-! ## The duplex automaton -/

/-- The sponge direction and intra-block position: `absorbed n` after `n` absorptions into
the current block, `squeezed n` after `n` squeezes from the current block (`n ≤ 2`). -/
inductive Mode
  | absorbed (n : Fin 3)
  | squeezed (n : Fin 3)
deriving Repr, DecidableEq

/-- A sponge in flight: the width-3 state and the mode. -/
structure State (F : Type*) where
  state : Triple F
  mode : Mode

/-- Read rate slot `n` (`n < 2`). -/
def slot (s : Triple F) : Fin 3 → F
  | 0 => s.1
  | 1 => s.2.1
  | _ => s.2.2

/-- Add `x` into rate slot `n` (`n < 2`). -/
def addSlot (s : Triple F) (n : Fin 3) (x : F) : Triple F :=
  match n with
  | 0 => (s.1 + x, s.2.1, s.2.2)
  | 1 => (s.1, s.2.1 + x, s.2.2)
  | _ => (s.1, s.2.1, s.2.2 + x)

/-- The fresh sponge: zero state, `absorbed 0`. -/
def init : State F := ⟨(0, 0, 0), .absorbed 0⟩

/-- Absorb one field element (`poseidon.rs` `absorb`): add into the next rate slot,
permuting first when the rate is full; absorbing after a squeeze restarts at slot 0. -/
def absorb1 (p : Params F) (sp : State F) (x : F) : State F :=
  match sp.mode with
  | .absorbed n =>
    if n.val = 2 then
      ⟨addSlot (blockCipher p sp.state) 0 x, .absorbed 1⟩
    else
      ⟨addSlot sp.state n x, .absorbed (n + 1)⟩
  | .squeezed _ =>
    ⟨addSlot sp.state 0 x, .absorbed 1⟩

/-- Absorb a list of field elements, left to right. -/
def absorb (p : Params F) (sp : State F) (xs : List F) : State F :=
  xs.foldl (absorb1 p) sp

/-- Squeeze one field element (`poseidon.rs` `squeeze`): read the next rate slot, permuting
first when entering squeeze mode or when the rate is exhausted. -/
def squeeze (p : Params F) (sp : State F) : F × State F :=
  match sp.mode with
  | .squeezed n =>
    if n.val = 2 then
      let st := blockCipher p sp.state
      (slot st 0, ⟨st, .squeezed 1⟩)
    else
      (slot sp.state n, ⟨sp.state, .squeezed (n + 1)⟩)
  | .absorbed _ =>
    let st := blockCipher p sp.state
    (slot st 0, ⟨st, .squeezed 1⟩)

/-- Squeeze `n` field elements, in order. -/
def squeezeN (p : Params F) (sp : State F) : ℕ → List F × State F
  | 0 => ([], sp)
  | n + 1 =>
    let (x, sp) := squeeze p sp
    let (xs, sp) := squeezeN p sp n
    (x :: xs, sp)

/-! ## The Pasta instantiations -/

open CompElliptic.Fields.Pasta in
/-- The `fq_kimchi` parameters over the Vesta base field, from the generated constant
tables. -/
def fqParams : Params Fq where
  roundConstants := FqKimchi.roundConstants.map fun row =>
    (((row[0]! : ℕ) : Fq), ((row[1]! : ℕ) : Fq),
     ((row[2]! : ℕ) : Fq))
  mds :=
    match FqKimchi.mds.map fun row =>
        (((row[0]! : ℕ) : Fq), ((row[1]! : ℕ) : Fq),
         ((row[2]! : ℕ) : Fq)) with
    | m => (m[0]!, m[1]!, m[2]!)

open CompElliptic.Fields.Pasta in
/-- The `fp_kimchi` parameters over the Pallas base field, from the generated constant
tables. -/
def fpParams : Params Fp where
  roundConstants := FpKimchi.roundConstants.map fun row =>
    (((row[0]! : ℕ) : Fp), ((row[1]! : ℕ) : Fp),
     ((row[2]! : ℕ) : Fp))
  mds :=
    match FpKimchi.mds.map fun row =>
        (((row[0]! : ℕ) : Fp), ((row[1]! : ℕ) : Fp),
         ((row[2]! : ℕ) : Fp)) with
    | m => (m[0]!, m[1]!, m[2]!)

end Poseidon
