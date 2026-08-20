import Poseidon.Basic

/-!
# The block-mode random-oracle hash

Port of the PS `RandomOracle` module (packages/random-oracle/src/RandomOracle.purs),
Mina's `Random_oracle.hash` shape: chunk the input into rate-2 blocks (zero-padded, one
zero block for empty input), fold each block into the state and permute, read slot 0.
Unlike the duplex automaton of `Poseidon/Basic.lean` there is no mode — every block
costs one permutation, eagerly.

`hash_eq_squeeze` identifies the two: block-mode hashing is absorb-then-squeeze on the
duplex sponge. The two schedules differ only in when the permutation runs (eagerly
after each block here, lazily before the next absorption or at the squeeze there), and
zero-padding adds `0` to a rate slot, which is the identity. That theorem is this
module's validation — it inherits the duplex automaton's fixture validation instead of
carrying vectors of its own.

Name map: `hash`/`update`/`digest`/`initialState` keep their names; PS's private
`toBlocks`/`addBlock` are public here as the vocabulary the circuit-level laws quote,
and its `sponge` helper (a fold parameterized by the permutation) is inlined into
`update` at `blockCipher`.

Deviations from the PS original:
- PS's ambient `PoseidonField` class arrives as the explicit `p : Params F`.
- PS's width-3 / width-2 `Vector`s render as the triple and the pair.
- PS's index-arithmetic chunking (`numBlocks`, `fillBlock` over positions) renders as
  the structural recursion `chunk`, preserving the odd-tail zero-pad and the
  one-zero-block rule for empty input.
-/

namespace Poseidon.RandomOracle

variable {F : Type*} [Field F]

/-- The fresh block-hash state: all zeros (PS `initialState`). -/
def initialState : F × F × F := (0, 0, 0)

/-- Chunk into rate-2 blocks, zero-padding an odd tail. Empty input is handled by
`toBlocks`. -/
def chunk : List F → List (F × F)
  | [] => []
  | [x] => [(x, 0)]
  | x :: y :: rest => (x, y) :: chunk rest

/-- The block decomposition (PS `toBlocks`): rate-2 chunks, zero-padded, with one zero
block for empty input. -/
def toBlocks : List F → List (F × F)
  | [] => [(0, 0)]
  | xs => chunk xs

/-- Add a block into the rate slots (PS `addBlock`). -/
def addBlock (st : F × F × F) (b : F × F) : F × F × F :=
  (st.1 + b.1, st.2.1 + b.2, st.2.2)

/-- Fold blocks into the state (PS `update`): add each block, permute after each. -/
def update (p : Params F) (st : F × F × F) (xs : List F) : F × F × F :=
  (toBlocks xs).foldl (fun s b => blockCipher p (addBlock s b)) st

/-- Read the digest from slot 0 (PS `digest`). -/
def digest (st : F × F × F) : F := st.1

/-- The block-mode hash (PS `hash`): update the fresh state, read slot 0. -/
def hash (p : Params F) (xs : List F) : F :=
  digest (update p initialState xs)

/-! ## The identification with the duplex sponge -/

/-- From a full block (`absorbed 2`), the duplex remainder is the eager block fold on
the permuted state: the pending permutation this side runs lazily is the one the block
side has already run. -/
private theorem absorbed_two_eq (p : Params F) :
    ∀ (xs : List F) (st : F × F × F),
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

/-- From the fresh mode (`absorbed 0`), the duplex run is the eager block fold: no
permutation is pending, so the first block is added before any permutation on either
side. -/
private theorem absorbed_zero_eq (p : Params F) :
    ∀ (xs : List F) (st : F × F × F),
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
absorb-then-squeeze on the duplex automaton: eager-vs-lazy permutation scheduling and
the zero-padding wash out. This is the module's validation — the right side is the
fixture-validated production sponge. -/
theorem hash_eq_squeeze (p : Params F) (xs : List F) :
    hash p xs = (Poseidon.squeeze p (Poseidon.absorb p Poseidon.init xs)).1 :=
  (absorbed_zero_eq p xs (0, 0, 0)).symm

end Poseidon.RandomOracle
