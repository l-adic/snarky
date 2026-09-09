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

/-- The plonk claims (PS `PlonkInCircuit`, OCaml `Plonk.In_circuit`): the four
prechallenges and the three shifted linearization scalars. -/
structure PlonkInCircuit (F sf : Type) where
  /-- The 128-bit `α` prechallenge. -/
  alpha : SizedF 128 (FVar F)
  /-- The 128-bit `β`. -/
  beta : SizedF 128 (FVar F)
  /-- The 128-bit `γ`. -/
  gamma : SizedF 128 (FVar F)
  /-- The 128-bit `ζ` prechallenge. -/
  zeta : SizedF 128 (FVar F)
  /-- The shifted permutation scalar. -/
  perm : sf
  /-- The shifted `ζ^(srs length)`. -/
  zetaToSrsLength : sf
  /-- The shifted `ζⁿ`. -/
  zetaToDomainSize : sf

/-- The deferred values of a proof (PS `DeferredValues`, OCaml
`Proof_state.Deferred_values`): the plonk claims, the shifted combined inner product, the
128-bit `ξ`, the 16 raw 128-bit bulletproof challenges, and the shifted `b`. -/
structure DeferredValues (F sf : Type) where
  /-- The plonk claims. -/
  plonk : PlonkInCircuit F sf
  /-- The shifted combined inner product. -/
  combinedInnerProduct : sf
  /-- The 128-bit `ξ` prechallenge. -/
  xi : SizedF 128 (FVar F)
  /-- The 16 raw 128-bit bulletproof challenges. -/
  bulletproofChallenges : List (SizedF 128 (FVar F))
  /-- The shifted `b`. -/
  b : sf

/-- A step statement's entry for one predecessor (PS `UnfinalizedProof`): its deferred
values, whether it is to be finalized (false for a dummy predecessor at the base of a chain),
and its fq-sponge digest before evaluations. -/
structure UnfinalizedProof (F sf : Type) where
  /-- The deferred values. -/
  deferredValues : DeferredValues F sf
  /-- Whether `finalize` is asserted for this predecessor. -/
  shouldFinalize : BoolVar F
  /-- The fq-sponge digest before evaluations. -/
  spongeDigestBeforeEvaluations : FVar F

/-- The branch data of a wrap statement (PS `BranchData`): the verified step proof's rule,
as its domain size and its proofs-verified mask. -/
structure BranchData (F : Type) where
  /-- `log2` of the rule's domain size. -/
  domainLog2 : FVar F
  /-- The two mask bits of `proofs_verified`. -/
  proofsVerifiedMask : List (BoolVar F)

/-- A wrap statement's deferred values (PS `WrapDeferredValues`): the deferred values with the
branch data. -/
structure WrapDeferredValues (F sf : Type) extends DeferredValues F sf where
  /-- The branch data. -/
  branchData : BranchData F

/-- The proof-state part of a wrap statement (PS `WrapStatement`'s `proofState`). -/
structure WrapProofState (F sf : Type) where
  /-- The verified step proof's deferred values. -/
  deferredValues : WrapDeferredValues F sf
  /-- The verified step proof's fq-sponge digest before evaluations. -/
  spongeDigestBeforeEvaluations : FVar F
  /-- The digest of `messages_for_next_wrap_proof`: the step proof's `sg` and its round
  challenges. -/
  messagesForNextWrapProof : FVar F

/-- The public input of a wrap proof (PS `WrapStatement`, OCaml `Wrap.Statement`). -/
structure WrapStatement (F sf : Type) where
  /-- The proof state. -/
  proofState : WrapProofState F sf
  /-- The digest of `messages_for_next_step_proof`, copied from the step statement. -/
  messagesForNextStepProof : FVar F

/-- The proof-state part of a step statement (PS `StepStatement`'s `proofState`). -/
structure StepProofState (F sf : Type) where
  /-- One entry per predecessor wrap proof. -/
  unfinalizedProofs : List (UnfinalizedProof F sf)
  /-- The digest of `messages_for_next_step_proof`: the application state and the
  predecessors' `sg`s and round challenges. -/
  messagesForNextStepProof : FVar F

/-- The public input of a step proof (PS `StepStatement`, OCaml `Step.Statement`). -/
structure StepStatement (F sf : Type) where
  /-- The proof state. -/
  proofState : StepProofState F sf
  /-- One `messages_for_next_wrap_proof` digest per predecessor. -/
  messagesForNextWrapProof : List (FVar F)

end Pickles
