import Snarky.Prover
import Snarky.Witness
import Pickles.Statement
import Pickles.FinalizeOtherProof
import Pickles.CheckBulletproof

/-!
# The statement records as circuit inputs

Every record a pickles gadget takes is polymorphic in its cell type: `UnfinalizedProof k F
Bool (Type1 F)` holds a proof's deferred values, `UnfinalizedProof k (FVar F) (BoolVar F)
(Type1 (FVar F))` holds the cells a circuit reads them from. `CircuitType` relates the two,
derived record by record from the product decomposition (`CircuitType.ofEquiv`), so a
value is seeded and a bundle allocated the way any input is — and a fixture supplies the
gadget's own record, never a flat layout.

The leaves: a `SizedF`, `Type1`, `Type2` wrapper is its one cell; a `SplitField` its half and
parity; a `PointEvaluations` its two cells; the round-challenge and `(L, R)` vectors are
vectors, so the `Vector` former applies.
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

@[simp] theorem scoped_sizedF {F v w : Type} {n : ℕ} [CircuitType F v w] {st : ProverState F}
    {x : SizedF n w} :
    CircuitType.Scoped (val := SizedF n v) st x ↔ CircuitType.Scoped (val := v) st x.val :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_sizedF {F v w : Type} [Add F] [Mul F] [Zero F] {n : ℕ} [CircuitType F v w]
    {V : Valuation F} {x : SizedF n w} {a : SizedF n v} :
    CircuitType.Reads V x a ↔ CircuitType.Reads V x.val a.val :=
  CircuitType.reads_ofEquiv _ _

/-- A `Type1` is its cell. -/
def _root_.Snarky.Type1.equivVal (α : Type) : Type1 α ≃ α :=
  ⟨Type1.val, Type1.mk, fun _ => rfl, fun _ => rfl⟩

instance instType1CircuitType {F v w : Type} [CircuitType F v w] :
    CircuitType F (Type1 v) (Type1 w) :=
  CircuitType.ofEquiv (Type1.equivVal v) (Type1.equivVal w)

@[simp] theorem scoped_type1 {F v w : Type} [CircuitType F v w] {st : ProverState F}
    {x : Type1 w} :
    CircuitType.Scoped (val := Type1 v) st x ↔ CircuitType.Scoped (val := v) st x.val :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_type1 {F v w : Type} [Add F] [Mul F] [Zero F] [CircuitType F v w]
    {V : Valuation F} {x : Type1 w} {a : Type1 v} :
    CircuitType.Reads V x a ↔ CircuitType.Reads V x.val a.val :=
  CircuitType.reads_ofEquiv _ _

/-- A `Type2` is its cell. -/
def _root_.Snarky.Type2.equivVal (α : Type) : Type2 α ≃ α :=
  ⟨Type2.val, Type2.mk, fun _ => rfl, fun _ => rfl⟩

instance instType2CircuitType {F v w : Type} [CircuitType F v w] :
    CircuitType F (Type2 v) (Type2 w) :=
  CircuitType.ofEquiv (Type2.equivVal v) (Type2.equivVal w)

@[simp] theorem scoped_type2 {F v w : Type} [CircuitType F v w] {st : ProverState F}
    {x : Type2 w} :
    CircuitType.Scoped (val := Type2 v) st x ↔ CircuitType.Scoped (val := v) st x.val :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_type2 {F v w : Type} [Add F] [Mul F] [Zero F] [CircuitType F v w]
    {V : Valuation F} {x : Type2 w} {a : Type2 v} :
    CircuitType.Reads V x a ↔ CircuitType.Reads V x.val a.val :=
  CircuitType.reads_ofEquiv _ _

/-- A split scalar is its half and its parity. -/
def _root_.Snarky.SplitField.equivProd (α β : Type) : SplitField α β ≃ α × β :=
  ⟨fun s => (s.sDiv2, s.sOdd), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

instance instSplitFieldCircuitType {F a va b vb : Type} [CircuitType F a va]
    [CircuitType F b vb] : CircuitType F (SplitField a b) (SplitField va vb) :=
  CircuitType.ofEquiv (SplitField.equivProd a b) (SplitField.equivProd va vb)

@[simp] theorem scoped_splitField {F a va b vb : Type} [CircuitType F a va] [CircuitType F b vb]
    {st : ProverState F} {x : SplitField va vb} :
    CircuitType.Scoped (val := SplitField a b) st x ↔
      CircuitType.Scoped (val := a × b) st (SplitField.equivProd va vb x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_splitField {F a va b vb : Type} [Add F] [Mul F] [Zero F]
    [CircuitType F a va] [CircuitType F b vb] {V : Valuation F} {x : SplitField va vb}
    {y : SplitField a b} :
    CircuitType.Reads V x y ↔
      CircuitType.Reads V (SplitField.equivProd va vb x) (SplitField.equivProd a b y) :=
  CircuitType.reads_ofEquiv _ _

/-! ## The evaluations -/

/-- An evaluation pair is its two entries. -/
def _root_.Kimchi.Verifier.PointEvaluations.equivProd (α : Type) :
    PointEvaluations α ≃ α × α :=
  ⟨fun e => (e.zeta, e.zetaOmega), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

instance instPointEvaluationsCircuitType {F v w : Type} [CircuitType F v w] :
    CircuitType F (PointEvaluations v) (PointEvaluations w) :=
  CircuitType.ofEquiv (PointEvaluations.equivProd v) (PointEvaluations.equivProd w)

@[simp] theorem scoped_pointEvaluations {F v w : Type} [CircuitType F v w] {st : ProverState F}
    {x : PointEvaluations w} :
    CircuitType.Scoped (val := PointEvaluations v) st x ↔
      CircuitType.Scoped (val := v × v) st (PointEvaluations.equivProd w x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_pointEvaluations {F v w : Type} [Add F] [Mul F] [Zero F]
    [CircuitType F v w] {V : Valuation F} {x : PointEvaluations w} {a : PointEvaluations v} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (PointEvaluations.equivProd w x) (PointEvaluations.equivProd v a) :=
  CircuitType.reads_ofEquiv _ _

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

@[simp] theorem scoped_proofEvaluations {F v w : Type} [CircuitType F v w] {st : ProverState F}
    {x : ProofEvaluations w} :
    CircuitType.Scoped (val := ProofEvaluations v) st x ↔
      CircuitType.Scoped (val := Vector (PointEvaluations v) wCols × PointEvaluations v ×
        Vector (PointEvaluations v) sigmaRows × Vector (PointEvaluations v) coeffCols ×
        PointEvaluations v × PointEvaluations v × PointEvaluations v × PointEvaluations v ×
        PointEvaluations v × PointEvaluations v) st (ProofEvaluations.equivProd w x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_proofEvaluations {F v w : Type} [Add F] [Mul F] [Zero F]
    [CircuitType F v w] {V : Valuation F} {x : ProofEvaluations w} {a : ProofEvaluations v} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (ProofEvaluations.equivProd w x) (ProofEvaluations.equivProd v a) :=
  CircuitType.reads_ofEquiv _ _

/-- The finalized proof's evaluations: `ft(ζω)`, the public pair, the record. -/
def AllEvals.equivProd (f : Type) : AllEvals f ≃ f × PointEvaluations f × ProofEvaluations f :=
  ⟨fun e => (e.ftEval1, e.pub, e.evals), fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl,
   fun _ => rfl⟩

instance instAllEvalsCircuitType {F v w : Type} [CircuitType F v w] :
    CircuitType F (AllEvals v) (AllEvals w) :=
  CircuitType.ofEquiv (AllEvals.equivProd v) (AllEvals.equivProd w)

@[simp] theorem scoped_allEvals {F v w : Type} [CircuitType F v w] {st : ProverState F}
    {x : AllEvals w} :
    CircuitType.Scoped (val := AllEvals v) st x ↔
      CircuitType.Scoped (val := v × PointEvaluations v × ProofEvaluations v) st
        (AllEvals.equivProd w x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_allEvals {F v w : Type} [Add F] [Mul F] [Zero F] [CircuitType F v w]
    {V : Valuation F} {x : AllEvals w} {a : AllEvals v} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (AllEvals.equivProd w x) (AllEvals.equivProd v a) :=
  CircuitType.reads_ofEquiv _ _

/-- The chunked evaluations: `ft(ζω)`, the public chunks, the record's chunks. -/
def ChunkedEvals.equivProd (nc : ℕ) (f : Type) :
    ChunkedEvals nc f ≃ f × PointEvaluations (Vector f nc) × ProofEvaluations (Vector f nc) :=
  ⟨fun e => (e.ftEval1, e.pub, e.evals), fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl,
   fun _ => rfl⟩

instance instChunkedEvalsCircuitType {F v w : Type} {nc : ℕ} [CircuitType F v w] :
    CircuitType F (ChunkedEvals nc v) (ChunkedEvals nc w) :=
  CircuitType.ofEquiv (ChunkedEvals.equivProd nc v) (ChunkedEvals.equivProd nc w)

@[simp] theorem scoped_chunkedEvals {F v w : Type} {nc : ℕ} [CircuitType F v w]
    {st : ProverState F} {x : ChunkedEvals nc w} :
    CircuitType.Scoped (val := ChunkedEvals nc v) st x ↔
      CircuitType.Scoped
        (val := v × PointEvaluations (Vector v nc) × ProofEvaluations (Vector v nc)) st
        (ChunkedEvals.equivProd nc w x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_chunkedEvals {F v w : Type} {nc : ℕ} [Add F] [Mul F] [Zero F]
    [CircuitType F v w] {V : Valuation F} {x : ChunkedEvals nc w} {a : ChunkedEvals nc v} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (ChunkedEvals.equivProd nc w x) (ChunkedEvals.equivProd nc v a) :=
  CircuitType.reads_ofEquiv _ _

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

@[simp] theorem scoped_plonkInCircuit {F f w sv sf : Type} [CircuitType F f w]
    [CircuitType F sv sf] {st : ProverState F} {x : PlonkInCircuit w sf} :
    CircuitType.Scoped (val := PlonkInCircuit f sv) st x ↔
      CircuitType.Scoped (val := SizedF 128 f × SizedF 128 f × SizedF 128 f × SizedF 128 f ×
        sv × sv × sv) st (PlonkInCircuit.equivProd w sf x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_plonkInCircuit {F f w sv sf : Type} [Add F] [Mul F] [Zero F]
    [CircuitType F f w] [CircuitType F sv sf] {V : Valuation F} {x : PlonkInCircuit w sf}
    {a : PlonkInCircuit f sv} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (PlonkInCircuit.equivProd w sf x) (PlonkInCircuit.equivProd f sv a) :=
  CircuitType.reads_ofEquiv _ _

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

@[simp] theorem scoped_deferredValues {F f w sv sf : Type} {k : ℕ} [CircuitType F f w]
    [CircuitType F sv sf] {st : ProverState F} {x : DeferredValues k w sf} :
    CircuitType.Scoped (val := DeferredValues k f sv) st x ↔
      CircuitType.Scoped (val := PlonkInCircuit f sv × sv × SizedF 128 f ×
        Vector (SizedF 128 f) k × sv) st (DeferredValues.equivProd k w sf x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_deferredValues {F f w sv sf : Type} {k : ℕ} [Add F] [Mul F] [Zero F]
    [CircuitType F f w] [CircuitType F sv sf] {V : Valuation F} {x : DeferredValues k w sf}
    {a : DeferredValues k f sv} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (DeferredValues.equivProd k w sf x)
        (DeferredValues.equivProd k f sv a) :=
  CircuitType.reads_ofEquiv _ _

/-- An unfinalized proof is its deferred values, its finalize bit and its digest. -/
def UnfinalizedProof.equivProd (k : ℕ) (f bc sf : Type) :
    UnfinalizedProof k f bc sf ≃ DeferredValues k f sf × bc × f :=
  ⟨fun u => (u.deferredValues, u.shouldFinalize, u.spongeDigestBeforeEvaluations),
   fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance instUnfinalizedProofCircuitType {F f w b vb sv sf : Type} {k : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] :
    CircuitType F (UnfinalizedProof k f b sv) (UnfinalizedProof k w vb sf) :=
  CircuitType.ofEquiv (UnfinalizedProof.equivProd k f b sv) (UnfinalizedProof.equivProd k w vb sf)

@[simp] theorem scoped_unfinalizedProof {F f w b vb sv sf : Type} {k : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] {st : ProverState F}
    {x : UnfinalizedProof k w vb sf} :
    CircuitType.Scoped (val := UnfinalizedProof k f b sv) st x ↔
      CircuitType.Scoped (val := DeferredValues k f sv × b × f) st
        (UnfinalizedProof.equivProd k w vb sf x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_unfinalizedProof {F f w b vb sv sf : Type} {k : ℕ} [Add F] [Mul F]
    [Zero F] [CircuitType F f w] [CircuitType F b vb] [CircuitType F sv sf] {V : Valuation F}
    {x : UnfinalizedProof k w vb sf} {a : UnfinalizedProof k f b sv} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (UnfinalizedProof.equivProd k w vb sf x)
        (UnfinalizedProof.equivProd k f b sv a) :=
  CircuitType.reads_ofEquiv _ _

/-! ## The wrap statement -/

/-- The branch data is the domain's `log2` and the mask. -/
def BranchData.equivProd (f bc : Type) : BranchData f bc ≃ f × Vector bc MaxProofsVerified :=
  ⟨fun d => (d.domainLog2, d.proofsVerifiedMask), fun p => ⟨p.1, p.2⟩, fun _ => rfl,
   fun _ => rfl⟩

instance instBranchDataCircuitType {F f w b vb : Type} [CircuitType F f w] [CircuitType F b vb] :
    CircuitType F (BranchData f b) (BranchData w vb) :=
  CircuitType.ofEquiv (BranchData.equivProd f b) (BranchData.equivProd w vb)

/-- The branch data's check: its cells' own, through the same decomposition — nothing on
`domain_log2`, the boolean constraint on each mask bit. That is the first line of PureScript's
`CheckedType (AllocBranchData …)` (`check (branchTuple r)`, `Pickles/Step/Types.purs`).

Two differences from that instance, neither of which a statement about the mask depends on.
PureScript's check goes on to range-check `domain_log2` by expanding its 16 bits through the
endo (`EndoScalar.toField @1`); `toField_spec` is proved at 8 rows only, so that line is not
here and this check emits fewer rows than the deployed one. And PureScript allocates the two
mask bits before `domain_log2`, where this record's decomposition puts `domain_log2` first:
an order of variables, which a byte comparison against a dump would see. -/
instance instBranchDataCheckedType {F c f w b vb : Type} [Add F] [Mul F] [Zero F] [One F]
    [BasicSystem F c] [CircuitType F f w] [CircuitType F b vb] [CheckedType F c f w]
    [CheckedType F c b vb] : CheckedType F c (BranchData f b) (BranchData w vb) :=
  CheckedType.ofEquiv (BranchData.equivProd f b) (BranchData.equivProd w vb)

@[simp] theorem scoped_branchData {F f w b vb : Type} [CircuitType F f w] [CircuitType F b vb]
    {st : ProverState F} {x : BranchData w vb} :
    CircuitType.Scoped (val := BranchData f b) st x ↔
      CircuitType.Scoped (val := f × Vector b MaxProofsVerified) st (BranchData.equivProd w vb x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_branchData {F f w b vb : Type} [Add F] [Mul F] [Zero F] [CircuitType F f w]
    [CircuitType F b vb] {V : Valuation F} {x : BranchData w vb} {a : BranchData f b} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (BranchData.equivProd w vb x) (BranchData.equivProd f b a) :=
  CircuitType.reads_ofEquiv _ _

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

@[simp] theorem scoped_wrapDeferredValues {F f w b vb sv sf : Type} {k : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] {st : ProverState F}
    {x : WrapDeferredValues k w vb sf} :
    CircuitType.Scoped (val := WrapDeferredValues k f b sv) st x ↔
      CircuitType.Scoped (val := DeferredValues k f sv × BranchData f b) st
        (WrapDeferredValues.equivProd k w vb sf x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_wrapDeferredValues {F f w b vb sv sf : Type} {k : ℕ} [Add F] [Mul F]
    [Zero F] [CircuitType F f w] [CircuitType F b vb] [CircuitType F sv sf] {V : Valuation F}
    {x : WrapDeferredValues k w vb sf} {a : WrapDeferredValues k f b sv} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (WrapDeferredValues.equivProd k w vb sf x)
        (WrapDeferredValues.equivProd k f b sv a) :=
  CircuitType.reads_ofEquiv _ _

/-- A wrap proof state is its deferred values and its two digests. -/
def WrapProofState.equivProd (k : ℕ) (f bc sf : Type) :
    WrapProofState k f bc sf ≃ WrapDeferredValues k f bc sf × f × f :=
  ⟨fun s => (s.deferredValues, s.spongeDigestBeforeEvaluations, s.messagesForNextWrapProof),
   fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl, fun _ => rfl⟩

instance instWrapProofStateCircuitType {F f w b vb sv sf : Type} {k : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] :
    CircuitType F (WrapProofState k f b sv) (WrapProofState k w vb sf) :=
  CircuitType.ofEquiv (WrapProofState.equivProd k f b sv) (WrapProofState.equivProd k w vb sf)

@[simp] theorem scoped_wrapProofState {F f w b vb sv sf : Type} {k : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] {st : ProverState F}
    {x : WrapProofState k w vb sf} :
    CircuitType.Scoped (val := WrapProofState k f b sv) st x ↔
      CircuitType.Scoped (val := WrapDeferredValues k f b sv × f × f) st
        (WrapProofState.equivProd k w vb sf x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_wrapProofState {F f w b vb sv sf : Type} {k : ℕ} [Add F] [Mul F] [Zero F]
    [CircuitType F f w] [CircuitType F b vb] [CircuitType F sv sf] {V : Valuation F}
    {x : WrapProofState k w vb sf} {a : WrapProofState k f b sv} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (WrapProofState.equivProd k w vb sf x)
        (WrapProofState.equivProd k f b sv a) :=
  CircuitType.reads_ofEquiv _ _

/-- A wrap statement is its proof state and the step-message digest. -/
def WrapStatement.equivProd (k : ℕ) (f bc sf : Type) :
    WrapStatement k f bc sf ≃ WrapProofState k f bc sf × f :=
  ⟨fun s => (s.proofState, s.messagesForNextStepProof), fun p => ⟨p.1, p.2⟩, fun _ => rfl,
   fun _ => rfl⟩

instance instWrapStatementCircuitType {F f w b vb sv sf : Type} {k : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] :
    CircuitType F (WrapStatement k f b sv) (WrapStatement k w vb sf) :=
  CircuitType.ofEquiv (WrapStatement.equivProd k f b sv) (WrapStatement.equivProd k w vb sf)

@[simp] theorem scoped_wrapStatement {F f w b vb sv sf : Type} {k : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] {st : ProverState F}
    {x : WrapStatement k w vb sf} :
    CircuitType.Scoped (val := WrapStatement k f b sv) st x ↔
      CircuitType.Scoped (val := WrapProofState k f b sv × f) st
        (WrapStatement.equivProd k w vb sf x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_wrapStatement {F f w b vb sv sf : Type} {k : ℕ} [Add F] [Mul F] [Zero F]
    [CircuitType F f w] [CircuitType F b vb] [CircuitType F sv sf] {V : Valuation F}
    {x : WrapStatement k w vb sf} {a : WrapStatement k f b sv} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (WrapStatement.equivProd k w vb sf x)
        (WrapStatement.equivProd k f b sv a) :=
  CircuitType.reads_ofEquiv _ _

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

@[simp] theorem scoped_stepProofState {F f w b vb sv sf : Type} {k n : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] {st : ProverState F}
    {x : StepProofState k n w vb sf} :
    CircuitType.Scoped (val := StepProofState k n f b sv) st x ↔
      CircuitType.Scoped (val := Vector (UnfinalizedProof k f b sv) n × f) st
        (StepProofState.equivProd k n w vb sf x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_stepProofState {F f w b vb sv sf : Type} {k n : ℕ} [Add F] [Mul F] [Zero F]
    [CircuitType F f w] [CircuitType F b vb] [CircuitType F sv sf] {V : Valuation F}
    {x : StepProofState k n w vb sf} {a : StepProofState k n f b sv} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (StepProofState.equivProd k n w vb sf x)
        (StepProofState.equivProd k n f b sv a) :=
  CircuitType.reads_ofEquiv _ _

/-- A step statement is its proof state and the slots' wrap-message digests. -/
def StepStatement.equivProd (k n : ℕ) (f bc sf : Type) :
    StepStatement k n f bc sf ≃ StepProofState k n f bc sf × Vector f n :=
  ⟨fun s => (s.proofState, s.messagesForNextWrapProof), fun p => ⟨p.1, p.2⟩, fun _ => rfl,
   fun _ => rfl⟩

instance instStepStatementCircuitType {F f w b vb sv sf : Type} {k n : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] :
    CircuitType F (StepStatement k n f b sv) (StepStatement k n w vb sf) :=
  CircuitType.ofEquiv (StepStatement.equivProd k n f b sv) (StepStatement.equivProd k n w vb sf)

@[simp] theorem scoped_stepStatement {F f w b vb sv sf : Type} {k n : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] {st : ProverState F}
    {x : StepStatement k n w vb sf} :
    CircuitType.Scoped (val := StepStatement k n f b sv) st x ↔
      CircuitType.Scoped (val := StepProofState k n f b sv × Vector f n) st
        (StepStatement.equivProd k n w vb sf x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_stepStatement {F f w b vb sv sf : Type} {k n : ℕ} [Add F] [Mul F] [Zero F]
    [CircuitType F f w] [CircuitType F b vb] [CircuitType F sv sf] {V : Valuation F}
    {x : StepStatement k n w vb sf} {a : StepStatement k n f b sv} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (StepStatement.equivProd k n w vb sf x)
        (StepStatement.equivProd k n f b sv a) :=
  CircuitType.reads_ofEquiv _ _

/-! ## The scalar half's input -/

/-- What a circuit's scalar half is given for one slot: its deferred claims, the evaluations,
and the previous challenges, one vector per slot. -/
structure FopInput (k : ℕ) (f bc sf : Type) where
  /-- The slot's deferred claims. -/
  claims : UnfinalizedProof k f bc sf
  /-- The evaluation cells. -/
  evals : AllEvals f
  /-- The previous challenges, one vector per slot. -/
  prev : Vector (Vector f k) MaxProofsVerified

/-- A scalar half's input is its claims, its evaluations and its previous challenges. -/
def FopInput.equivProd (k : ℕ) (f bc sf : Type) :
    FopInput k f bc sf ≃
      UnfinalizedProof k f bc sf × AllEvals f × Vector (Vector f k) MaxProofsVerified :=
  ⟨fun i => (i.claims, i.evals, i.prev), fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl,
   fun _ => rfl⟩

instance instFopInputCircuitType {F f w b vb sv sf : Type} {k : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] :
    CircuitType F (FopInput k f b sv) (FopInput k w vb sf) :=
  CircuitType.ofEquiv (FopInput.equivProd k f b sv) (FopInput.equivProd k w vb sf)

@[simp] theorem scoped_fopInput {F f w b vb sv sf : Type} {k : ℕ} [CircuitType F f w]
    [CircuitType F b vb] [CircuitType F sv sf] {st : ProverState F} {x : FopInput k w vb sf} :
    CircuitType.Scoped (val := FopInput k f b sv) st x ↔
      CircuitType.Scoped (val := UnfinalizedProof k f b sv × AllEvals f ×
        Vector (Vector f k) MaxProofsVerified) st (FopInput.equivProd k w vb sf x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_fopInput {F f w b vb sv sf : Type} {k : ℕ} [Add F] [Mul F] [Zero F]
    [CircuitType F f w] [CircuitType F b vb] [CircuitType F sv sf] {V : Valuation F}
    {x : FopInput k w vb sf} {a : FopInput k f b sv} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (FopInput.equivProd k w vb sf x) (FopInput.equivProd k f b sv a) :=
  CircuitType.reads_ofEquiv _ _

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

@[simp] theorem scoped_bulletproofOpening {F sv sf : Type} {k : ℕ} [CircuitType F sv sf]
    {st : ProverState F} {x : BulletproofOpening k (FVar F) sf} :
    CircuitType.Scoped (val := BulletproofOpening k F sv) st x ↔
      CircuitType.Scoped (val := Vector (AffinePoint F × AffinePoint F) k × sv × sv ×
        AffinePoint F × AffinePoint F) st (BulletproofOpening.equivProd k (FVar F) sf x) :=
  CircuitType.scoped_ofEquiv _ _

@[simp] theorem reads_bulletproofOpening {F sv sf : Type} {k : ℕ} [Add F] [Mul F] [Zero F]
    [CircuitType F sv sf] {V : Valuation F} {x : BulletproofOpening k (FVar F) sf}
    {a : BulletproofOpening k F sv} :
    CircuitType.Reads V x a ↔
      CircuitType.Reads V (BulletproofOpening.equivProd k (FVar F) sf x)
        (BulletproofOpening.equivProd k F sv a) :=
  CircuitType.reads_ofEquiv _ _

end Pickles
