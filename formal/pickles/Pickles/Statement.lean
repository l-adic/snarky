import Snarky.DSL.SizedF

/-!
# The pickles statement records

The records a proof's public input is made of, transcribed from `Pickles/Types.purs` and
`Pickles/DeferredValues.purs` (OCaml `composition_types.ml`). `sf` is the side's
shifted-scalar type (`Type1` or `Type2`): the `sf` fields are the scalars of the other field.

* `DeferredValues`: what one half of a proof's verification computes and the other certifies;
* `UnfinalizedProof`: the step statement's per-predecessor entry;
* `WrapStatement`, `StepStatement`: the two public inputs.
-/

namespace Pickles

open Snarky

/-! ## The recursion constants -/

/-- The number of predecessor slots of a step proof; a rule with fewer predecessors pads with
dummies. -/
def MaxProofsVerified : ℕ := 2

/-- The step SRS's round count: a step proof's opening has this many rounds, and so does each
of its old accumulators. -/
def StepIPARounds : ℕ := 16

/-- The wrap SRS's round count. -/
def WrapIPARounds : ℕ := 15

/-- The plonk claims: four 128-bit prechallenges and three shifted linearization scalars. -/
structure PlonkInCircuit (f sf : Type) where
  /-- The 128-bit `α` prechallenge. -/
  alpha : SizedF 128 f
  /-- The 128-bit `β`. -/
  beta : SizedF 128 f
  /-- The 128-bit `γ`. -/
  gamma : SizedF 128 f
  /-- The 128-bit `ζ` prechallenge. -/
  zeta : SizedF 128 f
  /-- The shifted permutation scalar. -/
  perm : sf
  /-- The shifted `ζ^(srs length)`. -/
  zetaToSrsLength : sf
  /-- The shifted `ζⁿ`. -/
  zetaToDomainSize : sf

/-- The deferred values of a proof: its plonk claims and its opening's scalars. -/
structure DeferredValues (k : ℕ) (f sf : Type) where
  /-- The plonk claims. -/
  plonk : PlonkInCircuit f sf
  /-- The shifted combined inner product. -/
  combinedInnerProduct : sf
  /-- The 128-bit `ξ` prechallenge. -/
  xi : SizedF 128 f
  /-- The `k` raw 128-bit bulletproof challenges. -/
  bulletproofChallenges : Vector (SizedF 128 f) k
  /-- The shifted `b`. -/
  b : sf

/-- A step statement's entry for one predecessor: its deferred values, whether they are to be
finalized (false for a dummy predecessor at the base of a chain), and its fq-sponge digest
before evaluations. -/
structure UnfinalizedProof (k : ℕ) (f bc sf : Type) where
  /-- The deferred values. -/
  deferredValues : DeferredValues k f sf
  /-- Whether the finalize check is asserted for this predecessor. -/
  shouldFinalize : bc
  /-- The fq-sponge digest before evaluations. -/
  spongeDigestBeforeEvaluations : f

/-- The verified step proof's rule, as its domain size and its proofs-verified mask. -/
structure BranchData (f bc : Type) where
  /-- `log2` of the rule's domain size. -/
  domainLog2 : f
  /-- The proofs-verified mask, one bit per predecessor slot. -/
  proofsVerifiedMask : Vector bc MaxProofsVerified

/-- A wrap statement's deferred values: the deferred values with the branch data. -/
structure WrapDeferredValues (k : ℕ) (f bc sf : Type) extends DeferredValues k f sf where
  /-- The branch data. -/
  branchData : BranchData f bc

/-- The proof-state part of a wrap statement. -/
structure WrapProofState (k : ℕ) (f bc sf : Type) where
  /-- The verified step proof's deferred values. -/
  deferredValues : WrapDeferredValues k f bc sf
  /-- The verified step proof's fq-sponge digest before evaluations. -/
  spongeDigestBeforeEvaluations : f
  /-- The `hashMessagesForNextWrapProof` digest: the step proof's `sg` and the accumulated
  round challenges. -/
  messagesForNextWrapProof : f

/-- The public input of a wrap proof. -/
structure WrapStatement (k : ℕ) (f bc sf : Type) where
  /-- The proof state. -/
  proofState : WrapProofState k f bc sf
  /-- The step-side message digest, copied from the step statement. -/
  messagesForNextStepProof : f

/-- The proof-state part of a step statement. -/
structure StepProofState (k n : ℕ) (f bc sf : Type) where
  /-- One entry per predecessor slot: the rule's `n` slots, not padded. -/
  unfinalizedProofs : Vector (UnfinalizedProof k f bc sf) n
  /-- The step-side message digest: the application state and the predecessors' `sg`s and
  round challenges. -/
  messagesForNextStepProof : f

/-- The public input of a step proof. -/
structure StepStatement (k n : ℕ) (f bc sf : Type) where
  /-- The proof state. -/
  proofState : StepProofState k n f bc sf
  /-- One `hashMessagesForNextWrapProof` digest per predecessor slot. -/
  messagesForNextWrapProof : Vector f n

end Pickles
