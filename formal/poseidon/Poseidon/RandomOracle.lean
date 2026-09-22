import Poseidon.Basic

/-!
# The block-mode random-oracle hash

Transcribes packages/random-oracle/src/RandomOracle.purs, Mina's block-mode Poseidon hash.
"Random oracle" is the name of that hashing construction; nothing here models an idealised
oracle. The hash chunks the input into rate-2 blocks (zero-padded, one zero block for empty
input), adds each block into the state and permutes, and reads slot 0. There is no mode:
every block costs one permutation, eagerly.

`hash_eq_squeeze` identifies it with absorb-then-squeeze on the duplex sponge of
`Poseidon/Basic.lean`. The two differ only in when the permutation runs (after each block
here, before the next absorption or at the squeeze there), and a zero pad adds `0`, which is
the identity. The module carries no test vectors: through that theorem it inherits the
duplex sponge's fixture checks.
-/

namespace Poseidon.RandomOracle

variable {F : Type*} [Field F]

/-- The fresh block-hash state: all zeros. -/
def initialState : Triple F := (0, 0, 0)

/-- Chunk into rate-2 blocks, zero-padding an odd tail; `toBlocks` handles empty input. -/
def chunk : List F → List (F × F)
  | [] => []
  | [x] => [(x, 0)]
  | x :: y :: rest => (x, y) :: chunk rest

/-- The block decomposition: `chunk`, plus one zero block for empty input. -/
def toBlocks : List F → List (F × F)
  | [] => [(0, 0)]
  | xs => chunk xs

/-- Add a block into the two rate slots. -/
def addBlock (st : Triple F) (b : F × F) : Triple F :=
  (st.1 + b.1, st.2.1 + b.2, st.2.2)

/-- Fold the blocks into the state, permuting after each. -/
def update (p : Params F) (st : Triple F) (xs : List F) : Triple F :=
  (toBlocks xs).foldl (fun s b => blockCipher p (addBlock s b)) st

/-- The digest: slot 0. -/
def digest (st : Triple F) : F := st.1

/-- The block-mode hash: update the fresh state, read slot 0. -/
def hash (p : Params F) (xs : List F) : F :=
  digest (update p initialState xs)

/-! ## The identification with the duplex sponge -/

/-- From a full block (`absorbed 2`), the duplex run is the block fold from the permuted
state: the permutation the duplex side has pending is the one the block side already ran. -/
private theorem absorbed_two_eq (p : Params F) :
    ∀ (xs : List F) (st : Triple F),
      (Poseidon.squeeze p (Poseidon.absorb p ⟨st, .absorbed 2⟩ xs)).1
        = ((chunk xs).foldl (fun s b => blockCipher p (addBlock s b))
            (blockCipher p st)).1
  | [], st => by
    simp [Poseidon.absorb, Poseidon.squeeze, Poseidon.slot, chunk]
  | [x], st => by
    simp [Poseidon.absorb, Poseidon.absorb1, Poseidon.addSlot, Poseidon.squeeze,
      Poseidon.slot, chunk, addBlock]
  | x :: y :: rest, st => by
    have ih := absorbed_two_eq p rest (addBlock (blockCipher p st) (x, y))
    simpa [Poseidon.absorb, Poseidon.absorb1, Poseidon.addSlot, chunk,
      addBlock] using ih

/-- From the fresh mode (`absorbed 0`), the duplex run is the block fold: nothing is
pending, so both sides add the first block before permuting. -/
private theorem absorbed_zero_eq (p : Params F) :
    ∀ (xs : List F) (st : Triple F),
      (Poseidon.squeeze p (Poseidon.absorb p ⟨st, .absorbed 0⟩ xs)).1
        = ((toBlocks xs).foldl (fun s b => blockCipher p (addBlock s b)) st).1
  | [], st => by
    simp [Poseidon.absorb, Poseidon.squeeze, Poseidon.slot, toBlocks, addBlock]
  | [x], st => by
    simp [Poseidon.absorb, Poseidon.absorb1, Poseidon.addSlot, Poseidon.squeeze,
      Poseidon.slot, toBlocks, chunk, addBlock]
  | x :: y :: rest, st => by
    have ih := absorbed_two_eq p rest (addBlock st (x, y))
    simpa [Poseidon.absorb, Poseidon.absorb1, Poseidon.addSlot, toBlocks, chunk,
      addBlock] using ih

/-- **Block mode is the duplex sponge.** The block-mode hash of any input is
absorb-then-squeeze from `Poseidon.init`: permutation scheduling and zero padding wash out. -/
theorem hash_eq_squeeze (p : Params F) (xs : List F) :
    hash p xs = (Poseidon.squeeze p (Poseidon.absorb p Poseidon.init xs)).1 :=
  (absorbed_zero_eq p xs (0, 0, 0)).symm

end Poseidon.RandomOracle
