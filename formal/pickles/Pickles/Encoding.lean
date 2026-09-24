import Snarky.Prover
import Snarky.Witness
import Pickles.Statement
import Pickles.FinalizeOtherProof
import Pickles.CheckBulletproof

/-!
# The statement records as circuit inputs

Every record a pickles gadget takes is polymorphic in its cell type: `UnfinalizedProof k F
Bool (Type1 F)` holds a proof's deferred values, `UnfinalizedProof k (FVar F) (BoolVar F)
(Type1 (FVar F))` the cells a circuit reads them from. `CircuitType` relates the two, derived
record by record from the product decomposition (`CircuitType.ofEquiv`), so a record is seeded
and allocated like any input.

The leaves: a `SizedF`, `Type1` or `Type2` is its one cell; a `SplitField` its half and
parity; a `PointEvaluations` its two cells; the round-challenge and `(L, R)` vectors take the
`Vector` former.
-/

namespace Pickles

open Snarky Kimchi Kimchi.Verifier

/-! ## The cell wrappers -/

/-- A `SizedF` is its cell. -/
def _root_.Snarky.SizedF.equivVal (n : ℕ) (α : Type) : SizedF n α ≃ α :=
  ⟨SizedF.val, SizedF.mk, fun _ => rfl, fun _ => rfl⟩

instance instSizedFCircuitType {F v w : Type} {n : ℕ} [CircuitType F v w] :
    CircuitType F (SizedF n v) (SizedF n w) :=
  CircuitType.ofEquiv (SizedF.equivVal n v) (SizedF.equivVal n w)

/-- A `Type1` is its cell. -/
def _root_.Snarky.Type1.equivVal (α : Type) : Type1 α ≃ α :=
  ⟨Type1.val, Type1.mk, fun _ => rfl, fun _ => rfl⟩

instance instType1CircuitType {F v w : Type} [CircuitType F v w] :
    CircuitType F (Type1 v) (Type1 w) :=
  CircuitType.ofEquiv (Type1.equivVal v) (Type1.equivVal w)

/-- A `Type2` is its cell. -/
def _root_.Snarky.Type2.equivVal (α : Type) : Type2 α ≃ α :=
  ⟨Type2.val, Type2.mk, fun _ => rfl, fun _ => rfl⟩

instance instType2CircuitType {F v w : Type} [CircuitType F v w] :
    CircuitType F (Type2 v) (Type2 w) :=
  CircuitType.ofEquiv (Type2.equivVal v) (Type2.equivVal w)

/-- A `Type2` is checked as its cell. -/
instance instType2CheckedType {F c v w : Type} [Add F] [Mul F] [Zero F] [One F]
    [BasicSystem F c] [CircuitType F v w] [CheckedType F c v w] :
    CheckedType F c (Type2 v) (Type2 w) :=
  CheckedType.ofEquiv (Type2.equivVal v) (Type2.equivVal w)

/-- A split scalar is its half and its parity. -/
def _root_.Snarky.SplitField.equivProd (α β : Type) : SplitField α β ≃ α × β :=
  ⟨fun s => (s.sDiv2, s.sOdd), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

instance instSplitFieldCircuitType {F a va b vb : Type} [CircuitType F a va]
    [CircuitType F b vb] : CircuitType F (SplitField a b) (SplitField va vb) :=
  CircuitType.ofEquiv (SplitField.equivProd a b) (SplitField.equivProd va vb)

/-- A split scalar is checked as its half, then its parity: at `(FVar, BoolVar)` the
parity's booleanity. -/
instance instSplitFieldCheckedType {F c a va b vb : Type} [Add F] [Mul F] [Zero F] [One F]
    [BasicSystem F c] [CircuitType F a va] [CircuitType F b vb] [CheckedType F c a va]
    [CheckedType F c b vb] : CheckedType F c (SplitField a b) (SplitField va vb) :=
  CheckedType.ofEquiv (SplitField.equivProd a b) (SplitField.equivProd va vb)

/-! ## The evaluations -/

/-- An evaluation pair is its two entries. -/
def _root_.Kimchi.Verifier.PointEvaluations.equivProd (α : Type) :
    PointEvaluations α ≃ α × α :=
  ⟨fun e => (e.zeta, e.zetaOmega), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

instance instPointEvaluationsCircuitType {F v w : Type} [CircuitType F v w] :
    CircuitType F (PointEvaluations v) (PointEvaluations w) :=
  CircuitType.ofEquiv (PointEvaluations.equivProd v) (PointEvaluations.equivProd w)

/-- The evaluation record is its ten families, in field order. -/
def _root_.Kimchi.Verifier.ProofEvaluations.equivProd (α : Type) :
    ProofEvaluations α ≃
      Vector (PointEvaluations α) wCols × PointEvaluations α ×
        Vector (PointEvaluations α) sigmaRows × Vector (PointEvaluations α) coeffCols ×
        PointEvaluations α × PointEvaluations α × PointEvaluations α × PointEvaluations α ×
        PointEvaluations α × PointEvaluations α where
  toFun e := (e.w, e.z, e.s, e.coefficients, e.genericSelector, e.poseidonSelector,
    e.completeAddSelector, e.mulSelector, e.emulSelector, e.endomulScalarSelector)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instProofEvaluationsCircuitType {F v w : Type} [CircuitType F v w] :
    CircuitType F (ProofEvaluations v) (ProofEvaluations w) :=
  CircuitType.ofEquiv (ProofEvaluations.equivProd v) (ProofEvaluations.equivProd w)

/-- The chunked evaluations: `ft(ζω)`, the public chunks, the record's chunks. -/
def ChunkedEvals.equivProd (nc : ℕ) (f : Type) :
    ChunkedEvals nc f ≃ f × PointEvaluations (Vector f nc) × ProofEvaluations (Vector f nc) :=
  ⟨fun e => (e.ftEval1, e.pub, e.evals), fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl,
   fun _ => rfl⟩

instance instChunkedEvalsCircuitType {F v w : Type} {nc : ℕ} [CircuitType F v w] :
    CircuitType F (ChunkedEvals nc v) (ChunkedEvals nc w) :=
  CircuitType.ofEquiv (ChunkedEvals.equivProd nc v) (ChunkedEvals.equivProd nc w)

/-! ## The deferred values -/

/-- The plonk claims are the four prechallenges and the three shifted scalars, in field
order. -/
def PlonkInCircuit.equivProd (f sf : Type) :
    PlonkInCircuit f sf ≃
      SizedF 128 f × SizedF 128 f × SizedF 128 f × SizedF 128 f × sf × sf × sf where
  toFun p := (p.alpha, p.beta, p.gamma, p.zeta, p.perm, p.zetaToSrsLength, p.zetaToDomainSize)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instPlonkInCircuitCircuitType {F f w sv sf : Type} [CircuitType F f w]
    [CircuitType F sv sf] : CircuitType F (PlonkInCircuit f sv) (PlonkInCircuit w sf) :=
  CircuitType.ofEquiv (PlonkInCircuit.equivProd f sv) (PlonkInCircuit.equivProd w sf)

/-- The deferred values are the plonk claims, `cip`, `ξ`, the `k` round challenges and `b`, in
field order. -/
def DeferredValues.equivProd (k : ℕ) (f sf : Type) :
    DeferredValues k f sf ≃
      PlonkInCircuit f sf × sf × SizedF 128 f × Vector (SizedF 128 f) k × sf where
  toFun d := (d.plonk, d.combinedInnerProduct, d.xi, d.bulletproofChallenges, d.b)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instDeferredValuesCircuitType {F f w sv sf : Type} {k : ℕ} [CircuitType F f w]
    [CircuitType F sv sf] : CircuitType F (DeferredValues k f sv) (DeferredValues k w sf) :=
  CircuitType.ofEquiv (DeferredValues.equivProd k f sv) (DeferredValues.equivProd k w sf)

/-- An unfinalized proof is its deferred values, its finalize bit and its digest. -/
def UnfinalizedProof.equivProd (k : ℕ) (f bc sf : Type) :
    UnfinalizedProof k f bc sf ≃ DeferredValues k f sf × bc × f :=
  ⟨fun u => (u.deferredValues, u.shouldFinalize, u.spongeDigestBeforeEvaluations),
   fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance instUnfinalizedProofCircuitType {F f w b vb sv sf : Type} {k : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] :
    CircuitType F (UnfinalizedProof k f b sv) (UnfinalizedProof k w vb sf) :=
  CircuitType.ofEquiv (UnfinalizedProof.equivProd k f b sv) (UnfinalizedProof.equivProd k w vb sf)

/-! ## The wrap statement -/

/-- The branch data is the domain's `log2` and the mask. -/
def BranchData.equivProd (f bc : Type) :
    BranchData f bc ≃ f × Vector bc MaxProofsVerified :=
  ⟨fun d => (d.domainLog2, d.proofsVerifiedMask), fun p => ⟨p.1, p.2⟩, fun _ => rfl,
   fun _ => rfl⟩

instance instBranchDataCircuitType {F f w b vb : Type} [CircuitType F f w] [CircuitType F b vb] :
    CircuitType F (BranchData f b) (BranchData w vb) :=
  CircuitType.ofEquiv (BranchData.equivProd f b) (BranchData.equivProd w vb)

/-- The branch data's check, through the same decomposition: nothing on the log2, the
boolean constraint on each mask bit.

The deployed check also range-checks the log2 by expanding its 16 bits through the endo at one
row; `toField_spec` is proved at 8 rows only, so that check is absent here and this one emits
fewer rows. The deployed allocation also puts the mask bits before the log2, a variable order
a dump comparison would see. -/
instance instBranchDataCheckedType {F c f w b vb : Type} [Add F] [Mul F] [Zero F] [One F]
    [BasicSystem F c] [CircuitType F f w] [CircuitType F b vb] [CheckedType F c f w]
    [CheckedType F c b vb] : CheckedType F c (BranchData f b) (BranchData w vb) :=
  CheckedType.ofEquiv (BranchData.equivProd f b) (BranchData.equivProd w vb)

/-- A wrap statement's deferred values are the deferred values and the branch data. -/
def WrapDeferredValues.equivProd (k : ℕ) (f bc sf : Type) :
    WrapDeferredValues k f bc sf ≃ DeferredValues k f sf × BranchData f bc :=
  ⟨fun d => (d.toDeferredValues, d.branchData), fun p => ⟨p.1, p.2⟩, fun _ => rfl,
   fun _ => rfl⟩

instance instWrapDeferredValuesCircuitType {F f w b vb sv sf : Type} {k : ℕ}
    [CircuitType F f w] [CircuitType F b vb] [CircuitType F sv sf] :
    CircuitType F (WrapDeferredValues k f b sv) (WrapDeferredValues k w vb sf) :=
  CircuitType.ofEquiv (WrapDeferredValues.equivProd k f b sv)
    (WrapDeferredValues.equivProd k w vb sf)

/-- A wrap proof state is its deferred values and its two digests. -/
def WrapProofState.equivProd (k : ℕ) (f bc sf : Type) :
    WrapProofState k f bc sf ≃ WrapDeferredValues k f bc sf × f × f :=
  ⟨fun s => (s.deferredValues, s.spongeDigestBeforeEvaluations, s.messagesForNextWrapProof),
   fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance instWrapProofStateCircuitType {F f w b vb sv sf : Type} {k : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] :
    CircuitType F (WrapProofState k f b sv) (WrapProofState k w vb sf) :=
  CircuitType.ofEquiv (WrapProofState.equivProd k f b sv) (WrapProofState.equivProd k w vb sf)

/-- A wrap statement is its proof state and the step-message digest. -/
def WrapStatement.equivProd (k : ℕ) (f bc sf : Type) :
    WrapStatement k f bc sf ≃ WrapProofState k f bc sf × f :=
  ⟨fun s => (s.proofState, s.messagesForNextStepProof), fun p => ⟨p.1, p.2⟩, fun _ => rfl,
   fun _ => rfl⟩

instance instWrapStatementCircuitType {F f w b vb sv sf : Type} {k : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] :
    CircuitType F (WrapStatement k f b sv) (WrapStatement k w vb sf) :=
  CircuitType.ofEquiv (WrapStatement.equivProd k f b sv) (WrapStatement.equivProd k w vb sf)

/-! ## The step statement -/

/-- A step proof state is its slots and the step-message digest. -/
def StepProofState.equivProd (k n : ℕ) (f bc sf : Type) :
    StepProofState k n f bc sf ≃ Vector (UnfinalizedProof k f bc sf) n × f :=
  ⟨fun s => (s.unfinalizedProofs, s.messagesForNextStepProof), fun p => ⟨p.1, p.2⟩,
   fun _ => rfl, fun _ => rfl⟩

instance instStepProofStateCircuitType {F f w b vb sv sf : Type} {k n : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] :
    CircuitType F (StepProofState k n f b sv) (StepProofState k n w vb sf) :=
  CircuitType.ofEquiv (StepProofState.equivProd k n f b sv) (StepProofState.equivProd k n w vb sf)

/-- A step statement is its proof state and the slots' wrap-message digests. -/
def StepStatement.equivProd (k n : ℕ) (f bc sf : Type) :
    StepStatement k n f bc sf ≃ StepProofState k n f bc sf × Vector f n :=
  ⟨fun s => (s.proofState, s.messagesForNextWrapProof), fun p => ⟨p.1, p.2⟩, fun _ => rfl,
   fun _ => rfl⟩

instance instStepStatementCircuitType {F f w b vb sv sf : Type} {k n : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] :
    CircuitType F (StepStatement k n f b sv) (StepStatement k n w vb sf) :=
  CircuitType.ofEquiv (StepStatement.equivProd k n f b sv) (StepStatement.equivProd k n w vb sf)

/-! ## The scalar half's input -/

/-- What a circuit's scalar half is given for one slot: its deferred claims, the evaluations
and the previous challenges. -/
structure FopInput (k nc : ℕ) (f bc sf : Type) where
  /-- The slot's deferred claims. -/
  claims : UnfinalizedProof k f bc sf
  /-- The evaluation cells, at `nc` chunks. -/
  evals : ChunkedEvals nc f
  /-- The previous challenges, one vector per slot. -/
  prev : Vector (Vector f k) MaxProofsVerified

/-- A scalar half's input is its claims, its evaluations and its previous challenges. -/
def FopInput.equivProd (k nc : ℕ) (f bc sf : Type) :
    FopInput k nc f bc sf ≃
      UnfinalizedProof k f bc sf × ChunkedEvals nc f × Vector (Vector f k) MaxProofsVerified :=
  ⟨fun i => (i.claims, i.evals, i.prev), fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl,
   fun _ => rfl⟩

instance instFopInputCircuitType {F f w b vb sv sf : Type} {k nc : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] :
    CircuitType F (FopInput k nc f b sv) (FopInput k nc w vb sf) :=
  CircuitType.ofEquiv (FopInput.equivProd k nc f b sv) (FopInput.equivProd k nc w vb sf)

/-! ## The opening -/

/-- An opening is its `(L, R)` rounds, the two shifted scalars, `δ` and `sg`. -/
def BulletproofOpening.equivProd (k : ℕ) (f sf : Type) :
    BulletproofOpening k f sf ≃
      Vector (AffinePoint f × AffinePoint f) k × sf × sf × AffinePoint f × AffinePoint f :=
  ⟨fun o => (o.lr, o.z1, o.z2, o.delta, o.sg), fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩,
   fun _ => rfl, fun _ => rfl⟩

instance instBulletproofOpeningCircuitType {F sv sf : Type} {k : ℕ} [CircuitType F sv sf] :
    CircuitType F (BulletproofOpening k F sv) (BulletproofOpening k (FVar F) sf) :=
  CircuitType.ofEquiv (BulletproofOpening.equivProd k F sv)
    (BulletproofOpening.equivProd k (FVar F) sf)

end Pickles
