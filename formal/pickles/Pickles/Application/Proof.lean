import Pickles.TwoHalves

/-!
# Verification of proofs reconstructed from cells

Reconstructing a proof carries the public evaluations read from scalar cells. A verifier
proof may instead compute those evaluations from its public input. Replacing that source
with the same carried values preserves the verifier run and its deferred equation.
-/

namespace Pickles.Application

open Snarky Snarky.Kimchi Bulletproof Kimchi.Verifier
open CompElliptic.CurveForms.ShortWeierstrass

variable {C : Ipa.KimchiCurve} {nc : Nat}

private def carried (σ : SRS C.Point) (vk : KimchiVK C nc) (p : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) : KimchiProof C nc σ.k :=
  { p with pubEvals := .carried (runPubEvals C σ vk p pub) }

private theorem carried_oracles (σ : SRS C.Point) (vk : KimchiVK C nc)
    (p : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    runOracles C σ vk (carried σ vk p pub) pub = runOracles C σ vk p pub := by
  simp only [runOracles, fqOracles, fqRun, carried]

private theorem carried_input (σ : SRS C.Point) (vk : KimchiVK C nc)
    (p : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    runInput C σ vk (carried σ vk p pub) pub = runInput C σ vk p pub := by
  simp only [runInput, runInputP, runStreamP, runFrOracles, runFtComm, runFComm, runFtEval0P,
    runPScalar, runLinEvals, runZetaOmega, runZetaN, runZetaM, runZetaOmegaM,
    carried_oracles]
  simp only [carried, KimchiProof.linEvals, frOracles, frRun, tailRowsOf, litRowsOf]
  rfl

private theorem carried_verify (σ : SRS C.Point) (vk : KimchiVK C nc)
    (p : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    kimchiVerify C σ vk (carried σ vk p pub) pub = kimchiVerify C σ vk p pub := by
  apply Bool.eq_iff_iff.mpr
  simp only [kimchiVerify_reflects, carried_oracles, carried_input]
  rfl

private theorem carried_challenges (σ : SRS C.Point) (vk : KimchiVK C nc)
    (p : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    wireChallenges σ vk (carried σ vk p pub) pub = wireChallenges σ vk p pub := by
  simp only [wireChallenges, carried_oracles, carried_input]
  rfl

private theorem carried_sgOk (σ : SRS C.Point) (vk : KimchiVK C nc)
    (p : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    SgOk σ vk (carried σ vk p pub) pub ↔ SgOk σ vk p pub := by
  simp only [SgOk, wireChallenges, carried_oracles, carried_input]
  rfl

private theorem readPt_of_reads {V : Valuation C.BaseField}
    {p : AffinePoint (FVar C.BaseField)} {P : C.Point}
    (h : OnCurveAt C.E.toAffine V p (SWPoint.equivPoint C.E P)) : readPt V p = P := by
  apply (SWPoint.equivPoint C.E).injective
  exact (onCurveAt_readPt (equation_toW.mp h.1.left)).eq h rfl rfl

private theorem comm_read {V : Valuation C.BaseField}
    {cells : List (AffinePoint (FVar C.BaseField))} {Ps : List C.Point}
    (h : CommReads C V cells Ps) : cells.map (readPt V) = Ps := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons, readPt_of_reads h, ih]

private theorem read_of_proofReads {V : Valuation C.BaseField} {sf : Type}
    {ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf} {k : Nat}
    (S : IvpSide C V ops) (pr : IvpProof k nc (FVar C.BaseField) sf)
    (p : KimchiProof C nc k) (h : ProofReads S pr.wComm pr.zComm pr.tComm pr.opening p) :
    pr.read S p.evals p.pubEvals p.ftEval1 p.olds = p := by
  apply IvpProof.read_eq S pr p
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    apply Vector.toList_inj.mp
    simpa only [Vector.toList_map] using comm_read (h.w ⟨i, hi⟩)
  · apply Vector.toList_inj.mp
    simpa only [Vector.toList_map] using comm_read h.z
  · apply Array.toList_inj.mp
    simpa only [Vector.toArray_map, Array.toList_map, Vector.toList] using comm_read h.t
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    exact Prod.ext (readPt_of_reads (h.lr ⟨i, hi⟩).1) (readPt_of_reads (h.lr ⟨i, hi⟩).2)
  · exact readPt_of_reads h.delta
  · exact h.z1
  · exact h.z2
  · exact readPt_of_reads h.sg

/-- Reading a proof's cells preserves its opening, old accumulators, transcript and verification,
when its scalar cells carry the same evaluations as the verifier computes. -/
theorem readProof_verification {V : Valuation C.BaseField} {sf : Type}
    {ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf}
    (S : IvpSide C V ops) (σ : SRS C.Point) (vk : KimchiVK C nc)
    (pr : IvpProof σ.k nc (FVar C.BaseField) sf) (p : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField)
    (evals : ProofEvaluations (Vector C.ScalarField nc))
    (pe : PointEvaluations (Vector C.ScalarField nc)) (ft : C.ScalarField)
    (olds : Array (Accumulator C σ.k))
    (h : ProofReads S pr.wComm pr.zComm pr.tComm pr.opening p)
    (he : evals = p.evals) (hpe : pe = runPubEvals C σ vk p pub)
    (hft : ft = p.ftEval1) (ho : olds = p.olds) :
    let q := pr.read S evals (.carried pe) ft olds
    q.opening.sg = p.opening.sg ∧ q.olds = p.olds ∧
    wireChallenges σ vk q pub = wireChallenges σ vk p pub ∧
    (SgOk σ vk q pub ↔ SgOk σ vk p pub) ∧
    kimchiVerify C σ vk q pub = kimchiVerify C σ vk p pub := by
  subst he hpe hft ho
  have hc : ProofReads S pr.wComm pr.zComm pr.tComm pr.opening (carried σ vk p pub) :=
    ⟨h.w, h.z, h.t, h.lr, h.delta, h.sg, h.z1, h.z2⟩
  have hr : pr.read S p.evals (.carried (runPubEvals C σ vk p pub)) p.ftEval1 p.olds =
      carried σ vk p pub := read_of_proofReads S pr (carried σ vk p pub) hc
  dsimp only
  rw [hr]
  exact ⟨rfl, rfl, carried_challenges σ vk p pub, carried_sgOk σ vk p pub,
    carried_verify σ vk p pub⟩

end Pickles.Application
