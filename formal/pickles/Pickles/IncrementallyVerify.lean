import Pickles.FtComm
import Pickles.VkComms
import Pickles.Env
import Pickles.FqSpongeTranscript
import Kimchi.Columns
import Pickles.ListLemmas

/-!
# The group half of the verifier

The verifier's group half, one circuit on either side of the cycle, transcribing the group
half of `step_verifier.ml` and `wrap_verifier.ml`. `incrementallyVerifyProof` squeezes the
index digest and runs the fq-sponge transcript: `fqSpongeTranscript` on the step side's plain
sponge, with the public-input commitment computed at its point of the schedule, and
`fqSpongeTranscriptOpt` on the wrap side's conditional sponge, the old accumulators under their
keep bits. It then asserts the deferred plonk claims equal the squeezed challenges, builds the
linearization commitment (`ftComm`), assembles the commitment bases in batch order
(`IvpInput.bases`) and runs `checkBulletproof` from the pre-digest sponge. It returns the
digest, the success bit and the round prechallenges (`IvpOutput`).

The original asserts the plonk claims last. An equality between two variables adds no row, so
asserting them right after the transcript leaves the constraint system unchanged.

The scalar side of the opening — recomputing `cip`, `b`, `ξ` and the permutation scalar —
belongs to `finalizeOtherProofCore`; the group circuit consumes them as claims (`IvpClaims`)
and scales by them. `verifyProof` ties the two.

## The read

`IvpReads` is the read, on either side (`IvpSide`): the digest is the wire's (`fqRun`'s
digest element), the four plonk claims and the returned round prechallenges are the wire's fq
and IPA prechallenges, and the success bit holds exactly when the Schnorr equation
`Ipa.schnorrAt` holds — at the circuit's own transcript (the wire's), over the wire's batch
stream `runInput`, at the claimed `ξ`, `cip`, `b`. The `sg`-correctness equation of
`Ipa.verifyWith` is not the circuit's: pickles defers it to the next proof, whose verifier
absorbs this `sg` as an old accumulator (`KimchiProof.olds`). `IvpTies` names what the read
assumes: the cells read as the wire's key, proof and claims.

`incrementallyVerifyProof_reads` is the read on any side, generic in `IvpSide` — the ladder
reading, the decode, the group facts, the endomorphism and map-to-curve data, the absorbed
limbs and the two group bridges a side supplies, from which its opening check reads as the
wire's (`IvpSide.opening_reads`). `wrapSide` and `stepSide` are the two deployed values. The
step side's claimed `cip` absorbs canonically because its own ladder range-checks the halved
limb to 253 bits (`IvpSide.absorb_limbs`).
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass
open scoped Kimchi

/-! ## The gadget -/

section Gadget

variable {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]
  {k : ℕ}

/-- What the group half returns: the fq-sponge digest before evaluations, the opening check's
acceptance bit, and the raw 128-bit round prechallenges. -/
structure IvpOutput (F : Type) where
  /-- The fq-sponge digest before evaluations. -/
  spongeDigest : FVar F
  /-- Whether the opening's Schnorr equation holds. -/
  success : BoolVar F
  /-- The squeezed round prechallenges, in round order, raw 128-bit. -/
  bulletproofChallenges : List (SizedF 128 (FVar F))

/-- The deferred plonk claims the group half consumes: the four 128-bit challenges, asserted
against the squeezes, and the three shifted scalars `ftComm` scales by. -/
structure IvpPlonk (f sf : Type) where
  /-- `α`, `β`, `γ`, `ζ`. -/
  chals : PlonkClaims f
  /-- The permutation scalar claim. -/
  perm : sf
  /-- The `ζ^{2^k}` claim. -/
  zetaToSrsLength : sf
  /-- The `ζⁿ` claim. -/
  zetaToDomainSize : sf

/-- The deferred claims the group half consumes: the plonk claims, the polyscale `ξ` and the
opening's `cip`, `b`. The cells the read `IvpReads` speaks about; the rest of `IvpInput`
enters the read only through `IvpTies`. -/
structure IvpClaims (f sf : Type) where
  /-- The deferred plonk claims. -/
  plonk : IvpPlonk f sf
  /-- The deferred polyscale `ξ`, 128 bits. -/
  xi : SizedF 128 f
  /-- The deferred `cip` and `b`. -/
  deferred : BulletproofDeferred sf

/-- What the group half consumes: the claims, the old accumulators' commitments, the key's
commitments at `nc` chunks, the proof's commitments as chunk lists, and the opening proof. -/
structure IvpInput (k nc : ℕ) (f bc sf : Type) extends IvpClaims f sf where
  /-- The previous proofs' challenge-polynomial commitments, each under its keep bit on the
  wrap side and unmasked on the step side. -/
  sgOld : List (Option bc × AffinePoint f)
  /-- The verifier key's commitments. -/
  key : VkComms nc (AffinePoint f)
  /-- The proof's fifteen witness commitments. -/
  wComm : List (List (AffinePoint f))
  /-- The proof's permutation-accumulator commitment. -/
  zComm : List (AffinePoint f)
  /-- The proof's quotient chunks. -/
  tComm : List (AffinePoint f)
  /-- The opening proof. -/
  opening : BulletproofOpening k f sf

/-- The shifted scalars the circuit scales by: the three `ftComm` scales by and the four of the
opening check. -/
def IvpInput.shifted {F sf : Type} {nc : ℕ} (inp : IvpInput k nc (FVar F) (BoolVar F) sf) :
    List sf :=
  [inp.plonk.perm, inp.plonk.zetaToSrsLength, inp.plonk.zetaToDomainSize,
   inp.deferred.combinedInnerProduct, inp.deferred.b, inp.opening.z1, inp.opening.z2]

/-- The batch bases in batch order: the old accumulators under their masks, then unmasked the
public-input commitment `xHat`, the linearization commitment `ftc`, `z`, the six selectors,
the witness columns, the coefficients and `σ₀…σ₅`, each commitment's chunks adjacent. -/
def IvpInput.bases {F sf : Type} {nc : ℕ} (inp : IvpInput k nc (FVar F) (BoolVar F) sf)
    (xHat : List (AffinePoint (FVar F)))
    (ftc : AffinePoint (FVar F)) : List (AffinePoint (FVar F) × Option (BoolVar F)) :=
  inp.sgOld.map (fun m => (m.2, m.1))
    ++ (xHat ++ [ftc] ++ inp.zComm ++ (inp.key.selectors.map Vector.toList).flatten
        ++ inp.wComm.flatten ++ (inp.key.coefficientsComm.toList.map Vector.toList).flatten
        ++ (inp.key.sigmaBatch.map Vector.toList).flatten).map (fun P => (P, none))

/-- The group half: squeeze the index digest from `spongeAfterIndex`; run the fq-sponge
transcript — under `optSponge`, `computeXHat` first, then the conditional sponge with the old
accumulators under their keep bits; otherwise the plain sponge with `computeXHat` run at its
point of the schedule; assert the plonk claims equal the squeezes; build `ftComm`; run
`checkBulletproof` on `IvpInput.bases` from the pre-digest sponge. -/
def incrementallyVerifyProof {sf : Type} (ops : IpaScalarOps F c sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F)
    (optSponge : Bool) (blindingH : AffinePoint (FVar F)) (spongeAfterIndex : SpongeVar F)
    (computeXHat : CircuitM F c (List (AffinePoint (FVar F))))
    {nc : ℕ} (inp : IvpInput k nc (FVar F) (BoolVar F) sf) :
    CircuitM F c (IvpOutput F) := do
  let (indexDigest, _) ← SpongeVar.squeeze p spongeAfterIndex
  let tr ←
    if optSponge then do
      let xHat ← computeXHat
      fqSpongeTranscriptOpt p endo indexDigest (inp.sgOld.map fun m => (m.1.getD true_, m.2))
        xHat inp.wComm inp.zComm inp.tComm
    else
      fqSpongeTranscript p endo indexDigest (inp.sgOld.map (·.2)) computeXHat inp.wComm
        inp.zComm inp.tComm
  assertPlonkChallenges tr inp.plonk.chals
  let ftc ← ftComm ops inp.key.sigmaLast.toList inp.tComm inp.plonk.perm inp.plonk.zetaToSrsLength
    inp.plonk.zetaToDomainSize
  let o ← checkBulletproof ops e p endo gm sqrtF tr.sponge (inp.bases tr.xHat ftc)
    ⟨inp.xi, inp.deferred, inp.opening, blindingH⟩
  pure ⟨tr.digest, o.success, o.challenges⟩

end Gadget

/-! ## The read -/

section Read

variable {C : KimchiCurve} {V : Valuation C.BaseField} {sf : Type}
  {ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf}

/-- A list of chunked commitment cells reads, column by column, as the wire's commitments. -/
def ColumnsRead (C : KimchiCurve) (V : Valuation C.BaseField) {nc : ℕ}
    (cols : List (List (AffinePoint (FVar C.BaseField)))) (Ps : List (Vector C.Point nc)) :
    Prop :=
  List.Forall₂ (fun col P => CommReads C V col P.toList) cols Ps

/-- A key's commitment cells read as the key's commitments, field by field. -/
structure KeyReads (C : KimchiCurve) (V : Valuation C.BaseField) {nc : ℕ}
    (key : VkComms nc (AffinePoint (FVar C.BaseField))) (cvk : KimchiVK C nc) : Prop where
  /-- The permutation commitments `σ₀…σ₆`. -/
  sigma : ∀ i : Fin permCols, CommReads C V key.sigmaComm[i].toList cvk.sigmaComm[i].toList
  /-- The coefficient commitments. -/
  coefficients : ∀ i : Fin coeffCols,
    CommReads C V key.coefficientsComm[i].toList cvk.coefficientsComm[i].toList
  /-- The generic selector's commitment. -/
  generic : CommReads C V key.genericComm.toList cvk.genericComm.toList
  /-- The poseidon selector's commitment. -/
  poseidon : CommReads C V key.poseidonComm.toList cvk.poseidonComm.toList
  /-- The complete-add selector's commitment. -/
  completeAdd : CommReads C V key.completeAddComm.toList cvk.completeAddComm.toList
  /-- The variable-base-mul selector's commitment. -/
  mul : CommReads C V key.mulComm.toList cvk.mulComm.toList
  /-- The endo-mul selector's commitment. -/
  emul : CommReads C V key.emulComm.toList cvk.emulComm.toList
  /-- The endo-mul-scalar selector's commitment. -/
  endomulScalar : CommReads C V key.endomulScalarComm.toList cvk.endomulScalarComm.toList

/-- Vectors of columns read entrywise read as their lists of columns. -/
private theorem columnsRead_of_forall {nc m : ℕ}
    {cells : Vector (Vector (AffinePoint (FVar C.BaseField)) nc) m}
    {Ps : Vector (Vector C.Point nc) m}
    (h : ∀ i : Fin m, CommReads C V cells[i].toList Ps[i].toList) :
    ColumnsRead C V (cells.toList.map Vector.toList) Ps.toList :=
  List.forall₂_iff_get.mpr ⟨by simp, fun i h₁ h₂ => by
    simpa using h ⟨i, by simpa using h₂⟩⟩

/-- The selector cells read as the key's selectors, in batch order. -/
theorem KeyReads.selectorsRead {nc : ℕ} {key : VkComms nc (AffinePoint (FVar C.BaseField))}
    {cvk : KimchiVK C nc} (h : KeyReads C V key cvk) :
    ColumnsRead C V (key.selectors.map Vector.toList)
      [cvk.genericComm, cvk.poseidonComm, cvk.completeAddComm, cvk.mulComm, cvk.emulComm,
       cvk.endomulScalarComm] :=
  .cons h.generic (.cons h.poseidon (.cons h.completeAdd (.cons h.mul (.cons h.emul
    (.cons h.endomulScalar .nil)))))

/-- The coefficient cells read as the key's coefficients. -/
theorem KeyReads.coefficientsRead {nc : ℕ} {key : VkComms nc (AffinePoint (FVar C.BaseField))}
    {cvk : KimchiVK C nc} (h : KeyReads C V key cvk) :
    ColumnsRead C V (key.coefficientsComm.toList.map Vector.toList) cvk.coefficientsComm.toList :=
  columnsRead_of_forall h.coefficients

/-- The batch's permutation cells read as the key's `σ₀…σ₅`. -/
theorem KeyReads.sigmaBatchRead {nc : ℕ} {key : VkComms nc (AffinePoint (FVar C.BaseField))}
    {cvk : KimchiVK C nc} (h : KeyReads C V key cvk) :
    ColumnsRead C V (key.sigmaBatch.map Vector.toList) (cvk.sigmaComm.take sigmaRows).toList :=
  columnsRead_of_forall (cells := key.sigmaComm.take sigmaRows) fun i => by
    simpa using h.sigma ⟨i, lt_of_lt_of_le i.isLt (Nat.min_le_right _ _)⟩

/-- The `σ₆` cells read as the key's `σ₆`. -/
theorem KeyReads.sigmaLastRead {nc : ℕ} {key : VkComms nc (AffinePoint (FVar C.BaseField))}
    {cvk : KimchiVK C nc} (h : KeyReads C V key cvk) :
    CommReads C V key.sigmaLast.toList cvk.sigmaComm[6].toList :=
  h.sigma 6

/-- The old-accumulator cells read as the proof's old accumulators: they read as the points
`oldsW` under their keep bits, and the kept points are the old accumulators' commitments, in
order. -/
structure OldsRead {nc k : ℕ} (V : Valuation C.BaseField)
    (sgOld : List (Option (BoolVar C.BaseField) × AffinePoint (FVar C.BaseField)))
    (cp : KimchiProof C nc k) (oldsW : List (C.Point × Bool)) : Prop where
  /-- The cells read as `oldsW`'s points under their bits. -/
  cells : List.Forall₂ (MaskedBaseReads C.E.toAffine V) (sgOld.map fun m => (m.2, m.1))
    (oldsW.map fun b => (SWPoint.equivPoint C.E b.1, b.2))
  /-- The kept points are the proof's old accumulators' commitments, in order. -/
  kept : (oldsW.filter (·.2)).map (·.1) = (cp.olds.map (·.sg)).toList

/-- A proof's cells read as the wire proof `cp`: the witness, permutation and quotient
commitment columns read as the proof's, the opening's `(L, R)`, `δ` and `sg` cells read as its
points, and its `z₁`, `z₂` decode to its scalars. -/
structure ProofReads {nc k : ℕ} (S : IvpSide C V ops)
    (wComm : List (List (AffinePoint (FVar C.BaseField))))
    (zComm tComm : List (AffinePoint (FVar C.BaseField)))
    (opening : BulletproofOpening k (FVar C.BaseField) sf) (cp : KimchiProof C nc k) : Prop where
  /-- The witness commitments. -/
  w : ColumnsRead C V wComm cp.wComm.toList
  /-- The permutation accumulator's commitment. -/
  z : CommReads C V zComm cp.zComm.toList
  /-- The quotient chunks. -/
  t : CommReads C V tComm cp.tComm.toList
  /-- The `(L, R)` cells read as the proof's pairs. -/
  lr : List.Forall₂ (PairReads C.E.toAffine V) opening.lr.toList
    (cp.opening.lr.toList.map fun q => (SWPoint.equivPoint C.E q.1, SWPoint.equivPoint C.E q.2))
  /-- The `δ` cell reads as the proof's. -/
  delta : OnCurveAt C.E.toAffine V opening.delta (SWPoint.equivPoint C.E cp.opening.delta)
  /-- The `sg` cell reads as the proof's. -/
  sg : OnCurveAt C.E.toAffine V opening.sg (SWPoint.equivPoint C.E cp.opening.sg)
  /-- The opening's `z₁` decodes to the proof's. -/
  z1 : S.decode opening.z1 = cp.opening.z1
  /-- The opening's `z₂` decodes to the proof's. -/
  z2 : S.decode opening.z2 = cp.opening.z2

/-- What the group half's read assumes of its cells, read as the wire's key `cvk` and proof
`cp`: the kept old accumulators are the proof's, each commitment column reads as its wire
column, the opening's `z₁`, `z₂` decode to the proof's, every shifted scalar satisfies
`IvpSide.ClaimOk`, and the opening's points read as the proof's. The deferred claims are tied
to nothing here: `ξ`, `cip`, `b` are scaled by as claimed, and `perm`, `ζ^{2^k}`, `ζⁿ` enter
only `ftComm`, so their being the wire's is a premise of `IvpReads`' opening clause. -/
structure IvpTies {nc : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k)
    (inp : IvpInput σ.k nc (FVar C.BaseField) (BoolVar C.BaseField) sf)
    (oldsW : List (C.Point × Bool)) : Prop where
  /-- The old-accumulator cells read as the proof's old accumulators, through `oldsW`. -/
  olds : OldsRead V inp.sgOld cp oldsW
  /-- The proof's cells read as the proof's. -/
  proof : ProofReads S inp.wComm inp.zComm inp.tComm inp.opening cp
  /-- The key's commitments. -/
  key : KeyReads C V inp.key cvk
  /-- Every shifted scalar the circuit scales by is a claim the ladder read speaks about. -/
  claimOk : ∀ x ∈ inp.shifted, S.ClaimOk x

/-! The read's opening clause. The claimed `perm`, `ζ^{2^k}` and `ζⁿ` enter the linearization
commitment alone, so the digest and plonk clauses of `IvpReads` hold without them; this is what
lets the scalar half's permutation check supply the first. Where they decode to the wire's, for
any prechallenge the claimed `ξ` reads as, the clause names the IPA run's challenge base (the
`uBase` of its `t`), its round prechallenges and its Schnorr prechallenge. The success bit then
reads `1` exactly when `Ipa.schnorrAt` holds at that base, the expansions of those
prechallenges, the claimed `cip` and `b`, the wire's batch stream combined at the expansion of
the `ξ` reading, and the proof's opening. These witnesses are stated under the `ξ` reading
because the opening check's read is; they do not depend on it. -/

/-- The group half's read, at the wire's raw fq run `pre` (`fqRun`) and its IPA run `r` from the
warm post-`ζ` state at the claimed `cip` (`ipaRunAt`, the claim in place of the wire's
`cipOf`): the digest cell is the wire's digest element; the claimed `β`, `γ` read as `pre`'s
prechallenges (the transcript range-checks them), and the claimed `α`, `ζ`, once read, are
`pre`'s; the opening clause is described in the note above. -/
def IvpReads {nc : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) (inp : IvpClaims (FVar C.BaseField) sf)
    (o : IvpOutput C.BaseField) : Prop :=
  let pre := fqRun C cvk cp (publicCommitment C σ cvk pub)
  let r := ipaRunAt C pre.warm (S.decode inp.deferred.combinedInnerProduct) cp.opening
  let run := runInput C σ cvk cp pub
  pre.digestElem = o.spongeDigest.val V ∧
  Reads128 V inp.plonk.chals.beta pre.beta ∧
  Reads128 V inp.plonk.chals.gamma pre.gamma ∧
  (∀ m, Reads128 V inp.plonk.chals.alpha m → m = pre.alpha) ∧
  (∀ m, Reads128 V inp.plonk.chals.zeta m → m = pre.zeta) ∧
  (S.decode inp.plonk.perm = runPScalar C σ cvk cp pub →
   S.decode inp.plonk.zetaToSrsLength = runZetaM C σ cvk cp pub →
   S.decode inp.plonk.zetaToDomainSize = runZetaN C σ cvk cp pub →
   ∀ ξ₀, Reads128 V inp.xi ξ₀ →
    ∃ (U : C.Point) (ns : List Prechallenge) (c₀ : Prechallenge)
      (chals : Vector C.ScalarField σ.k),
      U = C.uBase r.1 ∧
      List.Forall₂ (Reads128 V) o.bulletproofChallenges ns ∧
      ns = r.2.1.toList ∧ c₀ = r.2.2 ∧
      chals.toList = ns.map (fun m => Poseidon.FqSponge.endoExpand C.lam m.val) ∧
      (((↑o.success : CVar C.BaseField).val V = 1) ↔
        schnorrAt C σ U chals (Poseidon.FqSponge.endoExpand C.lam c₀.val)
          (S.decode inp.deferred.combinedInnerProduct) (S.decode inp.deferred.b)
          (combineCommitments C (Poseidon.FqSponge.endoExpand C.lam ξ₀.val)
            run.commitments.toArray)
          run.proof))

/-- What the group half's read assumes of its cells and constants, on the side `S`: the
sponge after the index digest squeezes to the key's digest, the old-accumulator cells are
masked as the side's sponge expects, the cells read as the wire's key and proof (`IvpTies`), and the
shape guards a key and proof satisfy: a chunk, a quotient chunk, a round, and a base field
wider than the absorb count. -/
structure IvpHyps {nc : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) (optSponge : Bool)
    (spongeAfterIndex : SpongeVar C.BaseField)
    (inp : IvpInput σ.k nc (FVar C.BaseField) (BoolVar C.BaseField) sf)
    (oldsW : List (C.Point × Bool)) : Prop where
  /-- The sponge after the index digest squeezes to the key's digest. -/
  idx : ∃ s : Poseidon.State C.BaseField, SpongeVar.ReadsAt V spongeAfterIndex s ∧
    (Poseidon.squeeze C.sponge.params s).1 = cvk.digest
  /-- Every old-accumulator cell carries a keep bit exactly on the conditional sponge. -/
  mask : ∀ m ∈ inp.sgOld, m.1.isSome = optSponge
  /-- The cells read as the wire's key and proof. -/
  ties : IvpTies S σ cvk cp inp oldsW
  /-- At least one chunk. -/
  nc_pos : 0 < nc
  /-- At least one quotient chunk. -/
  t_ne : inp.tComm ≠ []
  /-- At least one round. -/
  lr_ne : inp.opening.lr.toList ≠ []
  /-- The base field's characteristic exceeds the absorb count. -/
  char : ∀ k : ℕ, k ≤ 1 + 2 * (inp.sgOld.length + nc + inp.wComm.flatten.length
    + inp.zComm.length + inp.tComm.length) → (k : C.BaseField) = 0 → k = 0

end Read

/-! ## Reading helpers -/

section Helpers

open WeierstrassCurve.Affine

variable {C : KimchiCurve} {V : Valuation C.BaseField}

/-- A cell reading as a wire point across `SWPoint.equivPoint` has the point's coordinates: the
wire's points are all finite (the `𝒪` sentinel is not a curve read). -/
private theorem onCurveAt_equivPoint_coords {cell : AffinePoint (FVar C.BaseField)} {P : C.Point}
    (h : OnCurveAt C.E.toAffine V cell (SWPoint.equivPoint C.E P)) :
    cell.x.val V = P.x ∧ cell.y.val V = P.y := by
  obtain ⟨hns, hP⟩ := h
  rcases P.onCurve with hon | h0
  · rw [SWPoint.equivPoint_eq_some P hon] at hP
    have := (Point.some.injEq _ _ _ _ _ _).mp hP
    exact ⟨this.1.symm, this.2.symm⟩
  · exfalso
    have hz : SWPoint.equivPoint C.E P = 0 := by
      show toPt C.E.A C.E.B (P.x, P.y) = 0
      have : (P.x, P.y) = ((0 : C.BaseField), (0 : C.BaseField)) := h0
      rw [this]
      exact toPt_zero C.E.B_nonzero
    rw [hz] at hP
    exact Point.some_ne_zero _ hP.symm

/-- A wire point as the coordinate value the transcript specs read cells at. -/
private def wirePt (P : C.Point) : AffinePoint C.BaseField := ⟨P.x, P.y⟩

/-- A commitment read gives the cells' coordinate readings. -/
private theorem CommReads.reads {cells : List (AffinePoint (FVar C.BaseField))} {Ps : List C.Point}
    (h : CommReads C V cells Ps) : List.Forall₂ (CircuitType.Reads V) cells (Ps.map wirePt) :=
  List.forall₂_map_right_iff.2 (h.imp fun _ _ hc => reads_affinePoint.mpr
    (onCurveAt_equivPoint_coords hc))

/-- A column read gives the columns' coordinate readings. -/
private theorem ColumnsRead.reads {nc : ℕ} {cols : List (List (AffinePoint (FVar C.BaseField)))}
    {Ps : List (Vector C.Point nc)} (h : ColumnsRead C V cols Ps) :
    List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) cols
      (Ps.map fun P => P.toList.map wirePt) :=
  List.forall₂_map_right_iff.2 (h.imp fun _ _ hc => hc.reads)

/-- Unmasked bases read as their points, kept. -/
private theorem CommReads.masked {cells : List (AffinePoint (FVar C.BaseField))} {Ps : List C.Point}
    (h : CommReads C V cells Ps) :
    List.Forall₂ (MaskedBaseReads C.E.toAffine V) (cells.map fun P => (P, none))
      (Ps.map fun P => (SWPoint.equivPoint C.E P, true)) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact h.imp fun _ _ hc => ⟨hc, rfl⟩

/-- Unmasked chunked columns read as their points, kept, flattened. -/
private theorem ColumnsRead.masked {nc : ℕ} {cols : List (List (AffinePoint (FVar C.BaseField)))}
    {Ps : List (Vector C.Point nc)} (h : ColumnsRead C V cols Ps) :
    List.Forall₂ (MaskedBaseReads C.E.toAffine V) (cols.flatten.map fun P => (P, none))
      ((Ps.map Vector.toList).flatten.map fun P => (SWPoint.equivPoint C.E P, true)) := by
  rw [List.map_flatten, List.map_flatten]
  refine List.rel_flatten ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_map_right_iff]
  exact h.imp fun _ _ hc => hc.masked

/-- A batch row's commitments. -/
private theorem zipSeg_fst {nc : ℕ} (comm : Vector C.Point nc)
    (ev : PointEvaluations (Vector C.ScalarField nc)) : (zipSeg C comm ev).map (·.1) = comm := by
  ext i hi
  simp [zipSeg]

/-- The tail rows' commitments, flattened: `z`, the six selectors, the witness columns, the
coefficients, `σ₀…σ₅`, each column's chunks adjacent. -/
private theorem tailRows_comms {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k) :
    ((tailRowsOf C cvk cp).flatten.map (·.1)).toList
      = cp.zComm.toList
        ++ ([cvk.genericComm, cvk.poseidonComm, cvk.completeAddComm, cvk.mulComm, cvk.emulComm,
            cvk.endomulScalarComm].map Vector.toList).flatten
        ++ (cp.wComm.toList.map Vector.toList).flatten
        ++ (cvk.coefficientsComm.toList.map Vector.toList).flatten
        ++ ((cvk.sigmaComm.take sigmaRows).toList.map Vector.toList).flatten := by
  have hmap : ∀ {m : ℕ} (v : Vector (Vector (C.Point × C.ScalarField × C.ScalarField) nc) m),
      (v.flatten.map (·.1)).toList = ((v.map (·.map (·.1))).toList.map Vector.toList).flatten := by
    intro m v
    simp only [Vector.toList_map, toList_flatten', List.map_flatten, List.map_map,
      Function.comp_def]
  rw [hmap]
  -- `tailRowsOf` is typed at `tailRowCount`, its body at the sum of the four region lengths;
  -- split the appends at generic lengths, then instantiate by unification.
  have key : ∀ {a b c d : ℕ} (A : Vector (Vector (C.Point × C.ScalarField × C.ScalarField) nc) a)
      (B : Vector (Vector (C.Point × C.ScalarField × C.ScalarField) nc) b)
      (Cc : Vector (Vector (C.Point × C.ScalarField × C.ScalarField) nc) c)
      (D : Vector (Vector (C.Point × C.ScalarField × C.ScalarField) nc) d),
      ((A ++ B ++ Cc ++ D).map (·.map (·.1))).toList
        = (A.map (·.map (·.1))).toList ++ (B.map (·.map (·.1))).toList
          ++ (Cc.map (·.map (·.1))).toList ++ (D.map (·.map (·.1))).toList := by
    intro a b c d A B Cc D
    simp only [Vector.map_append, Vector.toList_append]
  unfold tailRowsOf
  refine (congrArg (fun l => (List.map Vector.toList l).flatten) (key _ _ _ _)).trans ?_
  unfold litRowsOf
  simp only [List.map_append, List.flatten_append, Vector.toList_map, Vector.toList_mk,
    List.map_cons, List.map_nil, Vector.toList_zip, List.map_map, Function.comp_def, zipSeg_fst,
    toList_map_fst_zip, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

/-- The wire's batch stream commitments: the olds' `sg`, the public chunks, `runFtComm`, the
tail. -/
private theorem runInput_comms {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    (runInput C σ cvk cp pub).commitments.toList
      = (cp.olds.map (·.sg)).toList ++ ((publicCommitment C σ cvk pub).toList
        ++ [runFtComm C σ cvk cp pub] ++ ((tailRowsOf C cvk cp).flatten.map (·.1)).toList) := by
  show ((runStreamP C σ cvk cp pub (runPubEvals C σ cvk cp pub)).map (·.1)).toList = _
  simp [runStreamP, Vector.toList_append, Function.comp_def, Vector.toList_push]

/-- The wire's stream after the olds' `sg`: the public chunks, `runFtComm`, the tail
commitments. -/
private def restOf {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) : List C.Point :=
  (publicCommitment C σ cvk pub).toList ++ [runFtComm C σ cvk cp pub]
    ++ ((tailRowsOf C cvk cp).flatten.map (·.1)).toList

/-- The masked bases the wire's stream reads as: the olds under their bits, the rest kept. -/
private def streamBv {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k)
    (pub : Array C.ScalarField) (oldsW : List (C.Point × Bool)) : List (C.Point × Bool) :=
  oldsW ++ (restOf σ cvk cp pub).map fun P => (P, true)

/-- The kept points of the stream bases are `runInput`'s commitments. -/
private theorem streamBv_kept {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) (oldsW : List (C.Point × Bool))
    (hkept : (oldsW.filter (·.2)).map (·.1) = (cp.olds.map (·.sg)).toList) :
    ((streamBv σ cvk cp pub oldsW).filter (·.2)).map (·.1)
      = (runInput C σ cvk cp pub).commitments.toList := by
  unfold streamBv
  rw [List.filter_append, List.map_append, hkept, runInput_comms, List.filter_eq_self.2 (by simp),
    List.map_map]
  simp [restOf, Function.comp_def]

/-- The last stream base is kept (the stream is nonempty). -/
private theorem streamBv_last {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) (oldsW : List (C.Point × Bool)) :
    ∀ h, (streamBv σ cvk cp pub oldsW).getLast? = some h → h.2 = true := by
  intro h hh
  unfold streamBv at hh
  rw [List.getLast?_append, List.getLast?_map] at hh
  rcases hl : (restOf σ cvk cp pub).getLast? with _ | P
  · exact absurd (List.getLast?_eq_none_iff.mp hl) (by simp [restOf])
  · rw [hl] at hh
    change some (P, true) = some h at hh
    cases hh
    rfl

/-- The batch bases read as the stream bases: the old-accumulator cells as the olds under
their bits, `xHat` as the public chunks, `ftc` as `runFtComm`, the columns as the tail. -/
private theorem bases_reads {nc : ℕ} {sf : Type}
    {ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf}
    {S : IvpSide C V ops} {σ : SRS C.Point} {cvk : KimchiVK C nc} {cp : KimchiProof C nc σ.k}
    {pub : Array C.ScalarField} {inp : IvpInput σ.k nc (FVar C.BaseField) (BoolVar C.BaseField) sf}
    {oldsW : List (C.Point × Bool)}
    (hties : IvpTies S σ cvk cp inp oldsW) {xHat : List (AffinePoint (FVar C.BaseField))}
    (hx : CommReads C V xHat (publicCommitment C σ cvk pub).toList)
    {ftc : AffinePoint (FVar C.BaseField)}
    (hf : OnCurveAt C.E.toAffine V ftc (SWPoint.equivPoint C.E (runFtComm C σ cvk cp pub))) :
    List.Forall₂ (MaskedBaseReads C.E.toAffine V) (inp.bases xHat ftc)
      ((streamBv σ cvk cp pub oldsW).map fun b => (SWPoint.equivPoint C.E b.1, b.2)) := by
  unfold IvpInput.bases streamBv restOf
  rw [tailRows_comms]
  have hi := hties.key.selectorsRead.masked
  have hw := hties.proof.w.masked
  have hc := hties.key.coefficientsRead.masked
  have hs := hties.key.sigmaBatchRead.masked
  simp only [List.map_append, List.map_map, List.append_assoc, List.map_cons, List.map_nil,
    Function.comp_def] at hi hw hc hs ⊢
  refine List.rel_append hties.olds.cells ?_
  refine List.rel_append hx.masked ?_
  refine List.rel_append (.cons ⟨hf, rfl⟩ .nil) ?_
  refine List.rel_append hties.proof.z.masked ?_
  refine List.rel_append hi ?_
  refine List.rel_append hw ?_
  exact List.rel_append hc hs

/-- Cells read as commitments have the commitments' coordinates. -/
private theorem CommReads.coords :
    ∀ {cells : List (AffinePoint (FVar C.BaseField))} {Ps : List C.Point},
      CommReads C V cells Ps →
      cells.flatMap (fun P => [P.x.val V, P.y.val V]) = Ps.flatMap fun P => [P.x, P.y]
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    obtain ⟨hx, hy⟩ := onCurveAt_equivPoint_coords h
    simp only [List.flatMap_cons, hx, hy, CommReads.coords hs]

/-- Columns read as commitments have the commitments' coordinates. -/
private theorem ColumnsRead.coords {nc : ℕ} :
    ∀ {cols : List (List (AffinePoint (FVar C.BaseField)))} {Ps : List (Vector C.Point nc)},
      ColumnsRead C V cols Ps →
      cols.flatMap (fun col => col.flatMap fun P => [P.x.val V, P.y.val V])
        = Ps.flatMap (fun v => v.toList.flatMap fun P => [P.x, P.y])
  | [], [], .nil => rfl
  | col :: cols, v :: Ps, .cons hc hs => by
    simp only [List.flatMap_cons, ColumnsRead.coords hs, CommReads.coords hc]

/-- Key cells reading as the key have its coordinates, in absorb order. -/
theorem KeyReads.indexCoords {nc : ℕ} {key : VkComms nc (AffinePoint (FVar C.BaseField))}
    {cvk : KimchiVK C nc} (h : KeyReads C V key cvk) :
    key.indexPoints.flatMap (fun P => [P.x.val V, P.y.val V])
      = cvk.comms.indexPoints.flatMap fun P => [P.x, P.y] := by
  have hc : ColumnsRead C V
      ((key.sigmaComm.toList ++ key.coefficientsComm.toList ++ key.selectors).map Vector.toList)
      (cvk.sigmaComm.toList ++ cvk.coefficientsComm.toList ++ cvk.comms.selectors) := by
    simp only [List.map_append]
    exact List.rel_append (List.rel_append (columnsRead_of_forall h.sigma) h.coefficientsRead)
      h.selectorsRead
  have := ColumnsRead.coords hc
  simp only [List.flatMap_map] at this
  simp only [VkComms.indexPoints, List.flatMap_assoc]
  exact this

end Helpers

/-! ## The side-generic readings -/

section Assembly

variable {C : KimchiCurve} {V : Valuation C.BaseField} {sf : Type}
  {ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf}

/-- Exact readings compose: the cells' readings are the wire's prechallenges. -/
private theorem forall₂_exact {pres : List ℕ} {us : List (SizedF 128 (FVar C.BaseField))}
    {ns : List Prechallenge}
    (h1 : List.Forall₂ (fun (pre : ℕ) (u : SizedF 128 (FVar C.BaseField)) =>
      ∀ m, Reads128 V u m → m.val = pre) pres us)
    (h2 : List.Forall₂ (Reads128 V) us ns) :
    ns.map Subtype.val = pres := by
  induction h1 generalizing ns with
  | nil => cases h2; rfl
  | cons h hs ih => cases h2 with | cons h' hs' => rw [List.map_cons, h _ h', ih hs']

/-- A pair read as two wire points reads as their coordinates. -/
private theorem pairReads_reads
    {q : AffinePoint (FVar C.BaseField) × AffinePoint (FVar C.BaseField)} {P : C.Point × C.Point}
    (h : PairReads C.E.toAffine V q (SWPoint.equivPoint C.E P.1, SWPoint.equivPoint C.E P.2)) :
    CircuitType.Reads V q (wirePt P.1, wirePt P.2) :=
  CircuitType.reads_prod.mpr
    ⟨reads_affinePoint.mpr (onCurveAt_equivPoint_coords h.1),
     reads_affinePoint.mpr (onCurveAt_equivPoint_coords h.2)⟩

/-- The conditional sponge's old-accumulator cells, each under a keep bit, read as the olds'
bits and coordinates. -/
private theorem olds_reads :
    ∀ {sgOld : List (Option (BoolVar C.BaseField) × AffinePoint (FVar C.BaseField))}
      {oldsW : List (C.Point × Bool)},
      (∀ m ∈ sgOld, m.1.isSome) →
      List.Forall₂ (MaskedBaseReads C.E.toAffine V) (sgOld.map fun m => (m.2, m.1))
        (oldsW.map fun b => (SWPoint.equivPoint C.E b.1, b.2)) →
      List.Forall₂ (CircuitType.Reads V) (sgOld.map fun m => (m.1.getD true_, m.2))
        (oldsW.map fun b => (b.2, wirePt b.1))
  | [], [], _, _ => .nil
  | m :: sg, b :: os, hm, h => by
    rw [List.map_cons, List.map_cons] at h ⊢
    cases h with
    | cons h1 hs =>
      obtain ⟨keep, hk⟩ := Option.isSome_iff_exists.mp (hm m (List.mem_cons_self ..))
      refine .cons ?_ (olds_reads (fun x hx => hm x (List.mem_cons_of_mem _ hx)) hs)
      rw [hk] at h1 ⊢
      simp only [MaskedBaseReads, Option.getD_some] at h1 ⊢
      exact CircuitType.reads_prod.mpr ⟨CircuitType.reads_boolVar.mpr h1.2,
        reads_affinePoint.mpr (onCurveAt_equivPoint_coords h1.1)⟩
  | [], _ :: _, _, h => by rw [List.map_cons] at h; cases h
  | _ :: _, [], _, h => by rw [List.map_cons] at h; cases h

/-- The plain sponge's unmasked old-accumulator cells read as the olds' coordinates, every old
kept. -/
private theorem olds_reads_plain :
    ∀ {sgOld : List (Option (BoolVar C.BaseField) × AffinePoint (FVar C.BaseField))}
      {oldsW : List (C.Point × Bool)},
      (∀ m ∈ sgOld, m.1.isSome = false) →
      List.Forall₂ (MaskedBaseReads C.E.toAffine V) (sgOld.map fun m => (m.2, m.1))
        (oldsW.map fun b => (SWPoint.equivPoint C.E b.1, b.2)) →
      List.Forall₂ (CircuitType.Reads V) (sgOld.map (·.2)) (oldsW.map fun b => wirePt b.1) ∧
        ∀ b ∈ oldsW, b.2 = true
  | [], [], _, _ => ⟨.nil, fun _ h => nomatch h⟩
  | m :: sg, b :: os, hm, h => by
    rw [List.map_cons, List.map_cons] at h
    rw [List.map_cons, List.map_cons]
    cases h with
    | cons h1 hs =>
      obtain ⟨ih1, ih2⟩ := olds_reads_plain (fun x hx => hm x (List.mem_cons_of_mem _ hx)) hs
      have hk : m.1 = none := by
        have := hm m (List.mem_cons_self ..)
        cases hm1 : m.1 with
        | none => rfl
        | some k => rw [hm1] at this; simp at this
      rw [hk] at h1
      simp only [MaskedBaseReads] at h1
      refine ⟨.cons (reads_affinePoint.mpr (onCurveAt_equivPoint_coords h1.1)) ih1, ?_⟩
      intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact h1.2
      · exact ih2 b' hb'
  | [], _ :: _, _, h => by rw [List.map_cons] at h; cases h
  | _ :: _, [], _, h => by rw [List.map_cons] at h; cases h

/-- The wire's IPA run at a claim read through its own ladder: its `t`, round and Schnorr
prechallenges are `ipaPrechallenges` at the claim's absorbed limbs and the pairs' and `δ`'s
coordinate readings — what the opening check's transcript read (`CheckBulletproofReads`)
speaks about. -/
private theorem ipaRunAt_reads {k : ℕ} (S : IvpSide C V ops) (st : Poseidon.State C.BaseField)
    (cip : sf) {w : S.R.wit} (hw : S.R.PreCip cip w) (pr : Ipa.Proof C k) :
    let r := ipaPrechallenges C.sponge.params st ((ops.shiftedToAbsorbFields cip).map (·.val V))
      ((pr.lr.toList.map fun q => (wirePt q.1, wirePt q.2)).map coordsPair)
      ((wirePt pr.delta).x, (wirePt pr.delta).y)
    (ipaRunAt C ⟨st, []⟩ (S.decode cip) pr).1 = r.1 ∧
    (ipaRunAt C ⟨st, []⟩ (S.decode cip) pr).2.1.toList.map Subtype.val = r.2.1 ∧
    (ipaRunAt C ⟨st, []⟩ (S.decode cip) pr).2.2.val = r.2.2 := by
  have h := ipaRunAt_eq_ipaPrechallenges C st (S.decode cip) pr
  dsimp only at h ⊢
  rw [← S.absorb_limbs hw] at h
  simpa only [List.map_map, Function.comp_def, coordsPair, wirePt] using h

/-- The success clause at the stream bases and the proof record is `IvpReads`'s, at
`runInput`'s commitments and `cp.opening`. -/
private theorem success_eq {nc : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point)
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (oldsW : List (C.Point × Bool))
    (hkept : (oldsW.filter (·.2)).map (·.1) = (cp.olds.map (·.sg)).toList)
    (z1 z2 : sf) (hz1 : S.decode z1 = cp.opening.z1) (hz2 : S.decode z2 = cp.opening.z2)
    (U : C.Point) (chals : Vector C.ScalarField σ.k) (c cip b ξ : C.ScalarField) (P : Prop) :
    (P ↔ schnorrAt C σ U chals c cip b
        (combineCommitments C ξ ((((streamBv σ cvk cp pub oldsW).filter (·.2)).map (·.1)).toArray))
        ⟨cp.opening.lr, cp.opening.delta, S.decode z1, S.decode z2, cp.opening.sg⟩) →
    (P ↔ schnorrAt C σ U chals c cip b
        (combineCommitments C ξ (runInput C σ cvk cp pub).commitments.toArray)
        (runInput C σ cvk cp pub).proof) := by
  rw [streamBv_kept σ cvk cp pub oldsW hkept, Array.toArray_toList, hz1, hz2]
  exact id

/-- The assembly's read from the transcript on: with the transcript's public-input commitment
read as the wire's and its outputs at the wire's commitment readings (the index digest
already the key's), the plonk claims asserted equal to the squeezes, `ftc` read and the
opening check read, the output satisfies `IvpReads`. -/
private theorem tail_reads {nc : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point)
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (inp : IvpInput σ.k nc (FVar C.BaseField) (BoolVar C.BaseField) sf)
    (oldsW : List (C.Point × Bool))
    (blindingH : AffinePoint (FVar C.BaseField)) (hties : IvpTies S σ cvk cp inp oldsW)
    (hh : OnCurveAt C.E.toAffine V blindingH (SWPoint.equivPoint C.E σ.h))
    (hlrne : inp.opening.lr.toList ≠ [])
    (tr : FqTranscriptOutput C.BaseField)
    (hx : CommReads C V tr.xHat (publicCommitment C σ cvk pub).toList)
    (hFq : FqTranscriptReads C.sponge.params cvk.digest ((cp.olds.map (·.sg)).toList.map wirePt)
      ((publicCommitment C σ cvk pub).toList.map wirePt)
      (cp.wComm.toList.map fun P => P.toList.map wirePt) (cp.zComm.toList.map wirePt)
      (cp.tComm.toList.map wirePt) V tr)
    (hasrt : inp.plonk.chals.beta.val.val V = tr.beta.val.val V ∧
      inp.plonk.chals.gamma.val.val V = tr.gamma.val.val V ∧
      inp.plonk.chals.alpha.val.val V = tr.alpha.val.val V ∧
      inp.plonk.chals.zeta.val.val V = tr.zeta.val.val V)
    (ftc : AffinePoint (FVar C.BaseField))
    (hft : FtCommReads S σ cvk cp pub ftc inp.plonk.perm inp.plonk.zetaToSrsLength
      inp.plonk.zetaToDomainSize inp.key.sigmaLast inp.tComm)
    (o : CheckBulletproofOutput C.BaseField)
    (hcb : S.OpeningReads tr.sponge (inp.bases tr.xHat ftc)
      ⟨inp.xi, inp.deferred, inp.opening, blindingH⟩ o) :
    IvpReads S σ cvk cp pub inp.toIvpClaims ⟨tr.digest, o.success, o.challenges⟩ := by
  -- the wire's fq squeezes at these readings are `IvpReads`'s
  have hpre : fqSqueezes C.sponge.params cvk.digest
      (((cp.olds.map (·.sg)).toList.map wirePt).map pointCoords)
      (((publicCommitment C σ cvk pub).toList.map wirePt).map pointCoords)
      ((cp.wComm.toList.map fun P => P.toList.map wirePt).map (·.map pointCoords))
      ((cp.zComm.toList.map wirePt).map pointCoords) ((cp.tComm.toList.map wirePt).map pointCoords)
      = fqSqueezes C.sponge.params cvk.digest
        ((cp.olds.map (·.sg)).toList.map fun P => (P.x, P.y))
        (coords C (publicCommitment C σ cvk pub))
        (cp.wComm.toList.map (coords C)) (coords C cp.zComm)
        (cp.tComm.toList.map fun P => (P.x, P.y)) := by
    delta Kimchi.Verifier.coords
    simp only [pointCoords, wirePt, List.map_map, Function.comp_def]
  set fqW := fqSqueezes C.sponge.params cvk.digest
    (((cp.olds.map (·.sg)).toList.map wirePt).map pointCoords)
    (((publicCommitment C σ cvk pub).toList.map wirePt).map pointCoords)
    ((cp.wComm.toList.map fun P => P.toList.map wirePt).map (·.map pointCoords))
    ((cp.zComm.toList.map wirePt).map pointCoords) ((cp.tComm.toList.map wirePt).map pointCoords)
    with hfqW
  -- the wire's raw run, field by field, at those squeezes
  obtain ⟨hβ, hγ, hα, hζ, hd, hwarm⟩ :=
    fqRun_eq_fqSqueezes C cvk cp (publicCommitment C σ cvk pub)
  rw [← hpre] at hβ hγ hα hζ hd hwarm
  unfold IvpReads
  dsimp only
  rw [hd, hwarm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the digest
    exact hFq.2.2.2.2.2.2.2.1.symm
  · -- `β` and `γ`: the transcript's range-checked reads are the wire's prechallenges
    obtain ⟨m, hm⟩ := hFq.2.2.2.2.1
    show _ = _
    rw [hβ, hFq.1.exact hm]
    exact hasrt.1.trans hm
  · obtain ⟨m, hm⟩ := hFq.2.2.2.2.2.1
    show _ = _
    rw [hγ, hFq.2.1.exact hm]
    exact hasrt.2.1.trans hm
  · -- `α` and `ζ`, once read
    intro m hm
    exact Subtype.ext (by rw [hα, hFq.2.2.1.exact (hasrt.2.2.1.symm.trans hm)])
  · intro m hm
    exact Subtype.ext (by rw [hζ, hFq.2.2.2.1.exact (hasrt.2.2.2.symm.trans hm)])
  · intro hperm hzetaM hzetaN ξ₀ hξ
    -- `ftc` reads as `runFtComm`: the claims decode and the chunk cells read as the ties say
    have hmem : ∀ x ∈ ([inp.plonk.perm, inp.plonk.zetaToSrsLength, inp.plonk.zetaToDomainSize] :
        List sf), x ∈ inp.shifted := fun x hx =>
      (List.sublist_append_left [inp.plonk.perm, inp.plonk.zetaToSrsLength,
        inp.plonk.zetaToDomainSize] [inp.deferred.combinedInnerProduct, inp.deferred.b,
        inp.opening.z1, inp.opening.z2]).subset hx
    have hftc := hft hperm hzetaM hzetaN
      (hties.claimOk _ (hmem _ (by simp))) (hties.claimOk _ (hmem _ (by simp)))
      (hties.claimOk _ (hmem _ (by simp))) hties.key.sigmaLastRead hties.proof.t
    -- the bases read as the stream bases; the opening's points as the proof's
    have hb := bases_reads hties hx hftc
    have hbne : inp.bases tr.xHat ftc ≠ [] := by simp [IvpInput.bases]
    have hclaims : ∀ x ∈ (⟨inp.xi, inp.deferred, inp.opening, blindingH⟩ :
        CheckBulletproofInput σ.k (FVar C.BaseField) sf).scaled, S.ClaimOk x := fun x hxs =>
      hties.claimOk x ((List.sublist_append_right [inp.plonk.perm, inp.plonk.zetaToSrsLength,
        inp.plonk.zetaToDomainSize] [inp.deferred.combinedInnerProduct, inp.deferred.b,
        inp.opening.z1, inp.opening.z2]).subset hxs)
    obtain ⟨U, ns, c₀, chals, hU, hns, hc, hchals, ⟨wc, hwc⟩, hiff⟩ :=
      hcb.2 _ hb hbne (streamBv_last σ cvk cp pub oldsW) hclaims ξ₀ hξ σ cp.opening.lr
        cp.opening.delta cp.opening.sg hties.proof.lr hlrne hties.proof.delta hties.proof.sg hh
    have hlrv : List.Forall₂ (CircuitType.Reads V) inp.opening.lr.toList
        (cp.opening.lr.toList.map fun q => (wirePt q.1, wirePt q.2)) :=
      List.forall₂_map_right_iff.2
        ((List.forall₂_map_right_iff.1 hties.proof.lr).imp fun _ _ h => pairReads_reads h)
    have hδv : CircuitType.Reads V inp.opening.delta (wirePt cp.opening.delta) :=
      reads_affinePoint.mpr (onCurveAt_equivPoint_coords hties.proof.delta)
    -- the opening transcript, from the warm sponge
    have hT := CheckBulletproofReads.wire (hcb.1 _ _ _ hFq.2.2.2.2.2.2.2.2 hlrv hδv)
    -- the wire's IPA run at the claimed `cip` is the opening check's transcript
    obtain ⟨h1, h2, h3⟩ :=
      ipaRunAt_reads S fqW.2.2 inp.deferred.combinedInnerProduct hwc cp.opening
    rw [h1]
    refine ⟨U, ns, c₀, chals, ?_, hns, ?_, Subtype.ext ((hT.2.2 c₀ hc).trans h3.symm), hchals,
      ?_⟩
    · rw [← hT.1]
      exact hU
    · exact List.map_injective_iff.mpr Subtype.val_injective
        ((forall₂_exact hT.2.1 hns).trans h2.symm)
    · exact success_eq S σ cvk cp pub oldsW hties.olds.kept inp.opening.z1 inp.opening.z2
        hties.proof.z1 hties.proof.z2 U chals _ _ _ _ _ hiff

/-! ## The read theorem -/

/-- **The group half reads as the wire's, on either side.** On the side `S`, given
`computeXHat` reads as the wire's `publicCommitment` chunk by chunk (on the wrap side through
`xHat_reads_publicCommitment`), `blindingH` reads as the SRS's `h`, and the cells and
constants read as the wire's (`IvpHyps`), the output satisfies `IvpReads`. -/
theorem incrementallyVerifyProof_reads {nc : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point)
    (cvk : KimchiVK C nc) (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (endo : FVar C.BaseField) (sqrtF : C.BaseField → Option C.BaseField) (optSponge : Bool)
    (blindingH : AffinePoint (FVar C.BaseField)) (spongeAfterIndex : SpongeVar C.BaseField)
    (computeXHat : CircuitM C.BaseField (Builder V (KimchiConstraint C.BaseField))
      (List (AffinePoint (FVar C.BaseField))))
    (inp : IvpInput σ.k nc (FVar C.BaseField) (BoolVar C.BaseField) sf)
    (oldsW : List (C.Point × Bool))
    (hXhat : ⦃⌜True⌝⦄ computeXHat
      ⦃⇓ pts _ => ⌜CommReads C V pts (publicCommitment C σ cvk pub).toList⌝⦄)
    (hh : OnCurveAt C.E.toAffine V blindingH (SWPoint.equivPoint C.E σ.h))
    (h : IvpHyps S σ cvk cp pub optSponge spongeAfterIndex inp oldsW) :
    ⦃⌜True⌝⦄
    incrementallyVerifyProof ops S.curve.e C.sponge.params endo (.ofSpec C.groupMap) sqrtF
      optSponge
      blindingH
      spongeAfterIndex computeXHat inp
    ⦃⇓ o _ => ⌜IvpReads S σ cvk cp pub inp.toIvpClaims o⌝⦄ := by
  obtain ⟨hIdx, hmask, hties, hnc, htne, hlrne, hchar⟩ := h
  have hasrt := fun (tr : FqTranscriptOutput C.BaseField) =>
    assertPlonkChallenges_spec (V := V) tr inp.plonk.chals
  have hft := ftComm_reads S σ cvk cp pub inp.plonk.perm inp.plonk.zetaToSrsLength
    inp.plonk.zetaToDomainSize inp.key.sigmaLast inp.tComm hnc htne
  have hcb := fun (sv : SpongeVar C.BaseField)
    (bases : List (AffinePoint (FVar C.BaseField) × Option (BoolVar C.BaseField))) =>
    S.opening_reads endo sqrtF sv bases ⟨inp.xi, inp.deferred, inp.opening, blindingH⟩
  obtain ⟨sIdx, hsIdx, hdig⟩ := hIdx
  cases optSponge with
  | true =>
    simp only [incrementallyVerifyProof, if_true]
    have htr := fun (d : FVar C.BaseField) (xHat : List (AffinePoint (FVar C.BaseField))) =>
      fqSpongeTranscriptOpt_reads (V := V) S.curve.two_ne S.curve.three_ne S.curve.splitWidth _
        C.sponge.hsize
        S.curve.small_inj endo d
        (inp.sgOld.map fun m => (m.1.getD true_, m.2)) xHat inp.wComm inp.zComm inp.tComm
    mvcgen -trivial [hXhat, htr, hasrt, hft, hcb]
    case vc1.hsize => exact C.sponge.hsize
    rename_i _ rIdx _ hIdx' xHat _ hx tr _ htr' _ _ hasrt' ftc _ hft' o _ hcb'
    have hd : rIdx.1.val V = cvk.digest := (hIdx' sIdx hsIdx).1.trans hdig
    -- the transcript, at the wire readings of every absorbed cell
    have hsgv := olds_reads hmask hties.olds.cells
    have hzne : (cp.zComm.toList.map wirePt) ≠ [] := by
      intro h
      have := congrArg List.length h
      simp at this
      omega
    have htne' : (cp.tComm.toList.map wirePt) ≠ [] := by
      intro h
      apply htne
      rw [List.map_eq_nil_iff] at h
      exact List.eq_nil_of_length_eq_zero (hties.proof.t.length_eq.trans (by rw [h]; rfl))
    have hchar' : ∀ k : ℕ, k ≤ 1 + 2 * ((oldsW.map fun b => (b.2, wirePt b.1)).length
        + ((publicCommitment C σ cvk pub).toList.map wirePt).length
        + (cp.wComm.toList.map fun P => P.toList.map wirePt).flatten.length
        + (cp.zComm.toList.map wirePt).length + (cp.tComm.toList.map wirePt).length) →
        (k : C.BaseField) = 0 → k = 0 := by
      intro k hk
      refine hchar k ?_
      have h1 := hsgv.length_eq
      have h2 := (List.rel_flatten hties.proof.w.reads).length_eq
      have h3 := hties.proof.z.length_eq
      have h4 := hties.proof.t.length_eq
      simp only [List.length_map, Vector.length_toList] at h1 h2 h3 h4 hk ⊢
      omega
    have hFq := htr'.2 _ _ _ _ _ hsgv hx.reads hties.proof.w.reads hties.proof.z.reads
      hties.proof.t.reads hzne
      htne' hchar'
    rw [hd] at hFq
    -- the kept old-accumulator readings are the olds' `sg`
    have hkept : ((oldsW.map fun b => (b.2, wirePt b.1)).filter (·.1)).map (·.2)
        = (cp.olds.map (·.sg)).toList.map wirePt := by
      rw [← hties.olds.kept, List.filter_map, List.map_map, List.map_map]
      rfl
    rw [hkept] at hFq
    exact tail_reads S σ cvk cp pub inp oldsW blindingH hties hh hlrne tr
      (htr'.1 ▸ hx) hFq hasrt' ftc hft' o hcb'
  | false =>
    simp only [incrementallyVerifyProof, Bool.false_eq_true, if_false]
    have htr := fun (d : FVar C.BaseField) =>
      fqSpongeTranscript_reads (V := V) S.curve.two_ne S.curve.three_ne S.curve.splitWidth _
        C.sponge.hsize endo d
        (inp.sgOld.map (·.2))
        computeXHat (fun pts => CommReads C V pts (publicCommitment C σ cvk pub).toList) _
        (builder_spec_imp _ _ _ hXhat fun _ h => ⟨h, h.reads⟩) inp.wComm inp.zComm inp.tComm
    mvcgen -trivial [htr, hasrt, hft, hcb]
    case vc1.hsize => exact C.sponge.hsize
    rename_i _ rIdx _ hIdx' tr _ htr' _ _ hasrt' ftc _ hft' o _ hcb'
    have hd : rIdx.1.val V = cvk.digest := (hIdx' sIdx hsIdx).1.trans hdig
    -- every old is kept: the plain sponge absorbs them all
    obtain ⟨hsgv, hall⟩ := olds_reads_plain hmask hties.olds.cells
    have hkept : oldsW.map (fun b => wirePt b.1) = (cp.olds.map (·.sg)).toList.map wirePt := by
      rw [← hties.olds.kept, List.filter_eq_self.2 hall, List.map_map]
      rfl
    have hFq := htr'.2 _ _ _ _ hsgv hties.proof.w.reads hties.proof.z.reads hties.proof.t.reads
    rw [hd, hkept] at hFq
    exact tail_reads S σ cvk cp pub inp oldsW blindingH hties hh hlrne tr htr'.1
      hFq hasrt' ftc hft' o hcb'

end Assembly

/-! The gadget is sealed after its read: a consumer composes `incrementallyVerifyProof_reads`,
never the body. -/
attribute [irreducible] incrementallyVerifyProof

end Pickles
