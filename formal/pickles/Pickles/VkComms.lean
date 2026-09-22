import Snarky.Encoding
import Snarky.Prover
import Kimchi.Columns

/-!
# A verifier key's commitments as a record

The group half reads a verifier key's commitments: the index digest absorbs every one, `ft_comm`
scales the last permutation column, and the opening batch takes the rest. `VkComms nc f` holds
them by name, `nc` chunks each, polymorphic in its cells like the statement records: at
`AffinePoint (FVar F)` it is the cells a circuit holds, as constants or as an input (its
`CircuitType` instance).

The orders the group half reads the key in are defined here, once each: the batch's
selectors (`selectors`: generic, poseidon, complete-add, mul, emul, endomul-scalar) and
permutation columns (`sigmaBatch`: `σ₀…σ₅`), and `ft_comm`'s `σ₆` (`sigmaLast`).
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

/-- The last permutation commitment `σ₆`, which `ft_comm` scales. -/
def sigmaLast (k : VkComms nc f) : Vector f nc :=
  k.sigmaComm[6]

end VkComms

/-- A key's commitments are its permutation, coefficient and selector columns. -/
@[simps apply] def VkComms.equivProd (nc : ℕ) (f : Type) :
    VkComms nc f ≃
      Vector (Vector f nc) permCols × Vector (Vector f nc) coeffCols × Vector f nc ×
        Vector f nc × Vector f nc × Vector f nc × Vector f nc × Vector f nc :=
  ⟨fun k => (k.sigmaComm, k.coefficientsComm, k.genericComm, k.poseidonComm,
      k.completeAddComm, k.mulComm, k.emulComm, k.endomulScalarComm),
   fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
     p.2.2.2.2.2.2.2⟩,
   fun _ => rfl, fun _ => rfl⟩

instance instVkCommsCircuitType {F v w : Type} {nc : ℕ} [CircuitType F v w] :
    CircuitType F (VkComms nc v) (VkComms nc w) :=
  CircuitType.ofEquiv (VkComms.equivProd nc v) (VkComms.equivProd nc w)

end Pickles
