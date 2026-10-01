import Snarky.Encoding
import Snarky.Prover
import Snarky.Witness
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
def selectors (k : VkComms nc f) : Vector (Vector f nc) 6 :=
  #v[k.genericComm, k.poseidonComm, k.completeAddComm, k.mulComm, k.emulComm,
    k.endomulScalarComm]

/-- The key's commitment chunks in absorb order: `σ₀…σ₆`, the coefficients, the selectors. -/
def indexPoints (k : VkComms nc f) : List f :=
  (k.sigmaComm.toList ++ k.coefficientsComm.toList ++ k.selectors.toList).flatMap Vector.toList

/-- The permutation commitments the batch opens: `σ₀…σ₅`. -/
def sigmaBatch (k : VkComms nc f) : Vector (Vector f nc) sigmaRows :=
  k.sigmaComm.take sigmaRows

/-- The last permutation commitment `σ₆`, which `ftComm` scales. -/
def sigmaLast (k : VkComms nc f) : Vector f nc :=
  k.sigmaComm[6]

/-- The record with `g` applied to every commitment chunk. -/
def map {f' : Type} (g : f → f') (k : VkComms nc f) : VkComms nc f' :=
  ⟨k.sigmaComm.map (·.map g), k.coefficientsComm.map (·.map g), k.genericComm.map g,
    k.poseidonComm.map g, k.completeAddComm.map g, k.mulComm.map g, k.emulComm.map g,
    k.endomulScalarComm.map g⟩

end VkComms

/-- A key's commitments are its permutation, coefficient and six selector commitments, in
absorb order. -/
def VkComms.equivProd (nc : ℕ) (f : Type) :
    VkComms nc f ≃ Vector (Vector f nc) permCols × Vector (Vector f nc) coeffCols ×
      Vector f nc × Vector f nc × Vector f nc × Vector f nc × Vector f nc × Vector f nc :=
  ⟨fun k => (k.sigmaComm, k.coefficientsComm, k.genericComm, k.poseidonComm, k.completeAddComm,
      k.mulComm, k.emulComm, k.endomulScalarComm),
    fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2⟩,
    fun _ => rfl, fun _ => rfl⟩

instance instVkCommsCircuitType {F v w : Type} {nc : ℕ} [CircuitType F v w] :
    CircuitType F (VkComms nc v) (VkComms nc w) :=
  CircuitType.ofEquiv (VkComms.equivProd nc v) (VkComms.equivProd nc w)

/-- A key is checked commitment by commitment: at checked points, every chunk on the curve. -/
instance instVkCommsCheckedType {F c v w : Type} {nc : ℕ} [Field F]
    [BasicSystem F c] [ConstraintHolds F c] [CircuitType F v w] [CheckedType F c v w] :
    CheckedType F c (VkComms nc v) (VkComms nc w) :=
  CheckedType.ofEquiv (VkComms.equivProd nc v) (VkComms.equivProd nc w)

end Pickles
