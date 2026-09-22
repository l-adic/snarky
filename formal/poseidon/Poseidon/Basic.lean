import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Fin.VecNotation
import CompElliptic.Fields.Pasta
import Poseidon.ConstantsFq
import Poseidon.ConstantsFp

/-!
# The kimchi Poseidon sponge

The Poseidon permutation and the duplex sponge automaton of kimchi's Fiat–Shamir transform,
transcribed from proof-systems' Poseidon crate (`permutation.rs`, `poseidon.rs`). The
parameter set is width 3, rate 2, capacity 1, with 55 full rounds, an `x^7` S-box, a full
3 × 3 MDS matrix, and no initial ARK (no round-constant addition before the first round).
The automaton tracks a mode `absorbed n` / `squeezed n` with `n ≤ rate`; crossing the rate
boundary, or switching direction into `squeezed`, runs the permutation.

Everything is executable. `fqParams` and `fpParams` instantiate the sponge at the Vesta and
Pallas base fields from the generated tables of `Poseidon/ConstantsFq.lean` and
`Poseidon/ConstantsFp.lean`. Both are checked against upstream absorb/squeeze traces by
`poseidon/scripts/check_sponge_vectors.lean`.

## Why the state is a triple

The width-3 state is the concrete triple `Triple F = F × F × F` rather than `Fin 3 → F`. The
compiler eta-expands function-valued definitions, and under that a fold of rounds
re-evaluates its whole prefix at every component lookup — exponentially in the round count.
Constructor arguments are forced at construction, which keeps the fold linear.

## What is not claimed

This module fixes what the Fiat–Shamir challenges are, not that they are secure.
-/

namespace Poseidon

variable {F : Type*} [Field F]

/-! ## The permutation -/

/-- A width-3 Poseidon state. -/
abbrev Triple (F : Type*) := F × F × F

/-- The deployed round count: `fqParams` and `fpParams` carry one constant triple per full
round. -/
abbrev fullRounds : Nat := 55

/-- Poseidon parameters: a round-constant table and an MDS matrix. -/
structure Params (F : Type*) where
  /-- One constant triple per round, added after that round's MDS pass (no initial ARK). -/
  roundConstants : Array (Triple F)
  /-- The MDS matrix, as three rows. -/
  mds : Triple (Triple F)

/-- The S-box `x ↦ x^7`. -/
def sbox (x : F) : F := x ^ 7

/-- One full round: S-box every state element, apply the MDS matrix, add the round
constants. -/
def fullRound (mds : Triple (Triple F)) (rc : Triple F) (s : Triple F) : Triple F :=
  let t0 := sbox s.1; let t1 := sbox s.2.1; let t2 := sbox s.2.2
  let m0 := mds.1; let m1 := mds.2.1; let m2 := mds.2.2
  (m0.1 * t0 + m0.2.1 * t1 + m0.2.2 * t2 + rc.1,
   m1.1 * t0 + m1.2.1 * t1 + m1.2.2 * t2 + rc.2.1,
   m2.1 * t0 + m2.2.1 * t1 + m2.2.2 * t2 + rc.2.2)

/-- The Poseidon permutation: `fullRound` folded over the round-constant table, with no
initial ARK. -/
def blockCipher (p : Params F) (s : Triple F) : Triple F :=
  p.roundConstants.foldl (fun s rc => fullRound p.mds rc s) s

/-! ## The duplex automaton -/

/-- The sponge direction and the position within the current block. -/
inductive SpongeMode
  /-- `n` absorptions into the current block. -/
  | absorbed (n : Fin 3)
  /-- `n` squeezes from the current block. -/
  | squeezed (n : Fin 3)

/-- A sponge in flight: the width-3 state and the mode. -/
structure State (F : Type*) where
  /-- The width-3 Poseidon state. -/
  state : Triple F
  /-- The automaton direction and intra-block position. -/
  mode : SpongeMode

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

/-- Absorb one field element: add it into the next rate slot, permuting first when the rate
is full; absorbing after a squeeze restarts at slot 0 without permuting. -/
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

/-- Squeeze one field element: read the next rate slot, permuting first when entering
squeeze mode or when the rate is exhausted. -/
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
/-- The parameters over the Vesta base field, from `FqKimchi.roundConstants` and
`FqKimchi.mds`. -/
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
/-- The parameters over the Pallas base field, from `FpKimchi.roundConstants` and
`FpKimchi.mds`. -/
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
