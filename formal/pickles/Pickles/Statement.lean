import Snarky.DSL.SizedF

/-!
# The pickles statement records

The records a proof's public input is made of, transcribed from the PureScript
`Pickles.Types` and `Pickles.Verify.Types` (OCaml `composition_types.ml`), at the circuit's
variable types. `sf` is the side's shifted-scalar type — `Type1 (FVar F)` for an `Fp` scalar
carried in `Fq`, `Type2 …` for an `Fq` scalar carried in `Fp` — so a record's type says which
of its scalars belong to the other field.

* `DeferredValues`: what one half of a proof's verification computes and the other certifies;
* `UnfinalizedProof`: a deferred-values record with its digest and the finalize flag, the
  step statement's per-predecessor entry;
* `WrapStatement`, `StepStatement`: the two public inputs.

Only `UnfinalizedProof` is consumed by a gadget here (`finalizeOtherProof`); the statements
are the vocabulary the boundary glue is stated over.
-/

namespace Pickles

open Snarky

/-! ## The recursion constants -/

/-- `Max_proofs_verified` (`Pickles_types.Nat.N2`, `Wrap_hack.Padded_length`): the number of
predecessor slots of a step proof; a rule with fewer predecessors pads with dummies. -/
def MaxProofsVerified : ℕ := 2

/-- The step SRS's round count (`Common.Max_degree.step_log2`): a step proof's opening has
this many rounds, and so does each of its old accumulators. -/
def StepIPARounds : ℕ := 16

/-- The wrap SRS's round count (`Common.Max_degree.wrap_log2`). -/
def WrapIPARounds : ℕ := 15

/-- The plonk claims (PS `PlonkInCircuit`, OCaml `Plonk.In_circuit`): the four
prechallenges and the three shifted linearization scalars. -/
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

/-- The deferred values of a proof (PS `DeferredValues`, OCaml
`Proof_state.Deferred_values`): the plonk claims, the shifted combined inner product, the
128-bit `ξ`, the `k` raw 128-bit bulletproof challenges, and the shifted `b`. -/
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

/-- A step statement's entry for one predecessor (PS `UnfinalizedProof`): its deferred
values, whether it is to be finalized (false for a dummy predecessor at the base of a chain),
and its fq-sponge digest before evaluations. -/
structure UnfinalizedProof (k : ℕ) (f bc sf : Type) where
  /-- The deferred values. -/
  deferredValues : DeferredValues k f sf
  /-- Whether `finalize` is asserted for this predecessor. -/
  shouldFinalize : bc
  /-- The fq-sponge digest before evaluations. -/
  spongeDigestBeforeEvaluations : f

/-- The branch data of a wrap statement (PS `BranchData`): the verified step proof's rule,
as its domain size and its proofs-verified mask. -/
structure BranchData (f bc : Type) where
  /-- `log2` of the rule's domain size. -/
  domainLog2 : f
  /-- The two mask bits of `proofs_verified`. -/
  proofsVerifiedMask : Vector bc MaxProofsVerified

/-- A wrap statement's deferred values (PS `WrapDeferredValues`): the deferred values with the
branch data. -/
structure WrapDeferredValues (k : ℕ) (f bc sf : Type) extends DeferredValues k f sf where
  /-- The branch data. -/
  branchData : BranchData f bc

/-- The proof-state part of a wrap statement (PS `WrapStatement`'s `proofState`). -/
structure WrapProofState (k : ℕ) (f bc sf : Type) where
  /-- The verified step proof's deferred values. -/
  deferredValues : WrapDeferredValues k f bc sf
  /-- The verified step proof's fq-sponge digest before evaluations. -/
  spongeDigestBeforeEvaluations : f
  /-- The digest of `messages_for_next_wrap_proof`: the step proof's `sg` and its round
  challenges. -/
  messagesForNextWrapProof : f

/-- The public input of a wrap proof (PS `WrapStatement`, OCaml `Wrap.Statement`). -/
structure WrapStatement (k : ℕ) (f bc sf : Type) where
  /-- The proof state. -/
  proofState : WrapProofState k f bc sf
  /-- The digest of `messages_for_next_step_proof`, copied from the step statement. -/
  messagesForNextStepProof : f

/-- The proof-state part of a step statement (PS `StepStatement`'s `proofState`). -/
structure StepProofState (k n : ℕ) (f bc sf : Type) where
  /-- One entry per predecessor slot: the rule's `n` slots, not padded. -/
  unfinalizedProofs : Vector (UnfinalizedProof k f bc sf) n
  /-- The digest of `messages_for_next_step_proof`: the application state and the
  predecessors' `sg`s and round challenges. -/
  messagesForNextStepProof : f

/-- The public input of a step proof (PS `StepStatement`, OCaml `Step.Statement`). -/
structure StepStatement (k n : ℕ) (f bc sf : Type) where
  /-- The proof state. -/
  proofState : StepProofState k n f bc sf
  /-- One `messages_for_next_wrap_proof` digest per predecessor slot. -/
  messagesForNextWrapProof : Vector f n

end Pickles
