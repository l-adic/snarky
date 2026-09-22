import Snarky.Encoding
import Snarky.Prover
import Kimchi.Columns

/-!
# A verifier key's commitments as a record

The group half reads a verifier key's commitments: the index digest absorbs every one, `ftComm`
scales the last permutation column, and the opening batch takes the rest. `VkComms nc f` holds
them by name, `nc` chunks each, polymorphic in its cells like the statement records: at
`AffinePoint (FVar F)` it is the cells a circuit holds, as constants or as an input (its
`CircuitType` instance).

The orders the group half reads the key in are defined here, once each: the batch's
selectors (`selectors`: generic, poseidon, complete-add, mul, emul, endomul-scalar) and
permutation columns (`sigmaBatch`: `σ₀…σ₅`), and `ftComm`'s `σ₆` (`sigmaLast`).
-/

namespace Pickles

open Snarky Kimchi

/-- A verifier key's commitments, `nc` chunks each (the commitment fields of `KimchiVK`). -/
structure VkComms (nc : ℕ) (f : Type) where
  /-- The seven permutation commitments `σ₀…σ₆`. -/
  sigmaComm : Vector (Vector f nc) permCols
  /-- The fifteen coefficient commitments. -/
  coefficientsComm : Vector (Vector f nc) coeffCols
  /-- The generic selector's commitment. -/
  genericComm : Vector f nc
  /-- The poseidon selector's commitment. -/
  poseidonComm : Vector f nc
  /-- The complete-add selector's commitment. -/
  completeAddComm : Vector f nc
  /-- The variable-base-mul selector's commitment. -/
  mulComm : Vector f nc
  /-- The endo-mul selector's commitment. -/
  emulComm : Vector f nc
  /-- The endo-mul-scalar selector's commitment. -/
  endomulScalarComm : Vector f nc

namespace VkComms

variable {nc : ℕ} {f : Type}

/-- The six selector commitments in batch order: generic, poseidon, complete-add, mul, emul,
endomul-scalar. -/
def selectors (k : VkComms nc f) : List (Vector f nc) :=
  [k.genericComm, k.poseidonComm, k.completeAddComm, k.mulComm, k.emulComm,
   k.endomulScalarComm]

/-- The permutation commitments the batch opens: `σ₀…σ₅`. -/
def sigmaBatch (k : VkComms nc f) : List (Vector f nc) :=
  (k.sigmaComm.take sigmaRows).toList

/-- The last permutation commitment `σ₆`, which `ftComm` scales. -/
def sigmaLast (k : VkComms nc f) : Vector f nc :=
  k.sigmaComm[6]

end VkComms

end Pickles
