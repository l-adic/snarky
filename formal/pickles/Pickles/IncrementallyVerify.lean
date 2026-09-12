import Pickles.FtComm
import Pickles.FqSpongeTranscript
import Kimchi.Columns

/-!
# The group half (`incrementally_verify_proof`)

The port of PS `Pickles.IncrementallyVerifyProof.incrementallyVerifyProof` (OCaml
`Step_verifier.incrementally_verify_proof`, `step_verifier.ml:536–786`, and
`Wrap_verifier.incrementally_verify_proof`, `wrap_verifier.ml:1418–1546`): the verifier's
group half, one circuit on either side of the cycle. It squeezes the index digest, runs the
fq-sponge transcript (`fqSpongeTranscript` on the step side's plain sponge, with `x_hat`
computed at its point of the schedule; `fqSpongeTranscriptOpt` on the wrap side's conditional
sponge, `sg_old` under its keep bits), asserts the deferred plonk claims equal the squeezed
challenges, constructs `ft_comm`, assembles the commitment bases in `to_batch` order —
`sg_old`, `x_hat`, `ft_comm`, `z`, the six selectors, `w₀…w₁₄`, the fifteen coefficients,
`σ₀…σ₅` — and runs `checkBulletproof` from the pre-digest sponge, returning the digest, the
success bit and the round prechallenges (`wrap_verifier.mli:438–441`).

The scalar side of the opening — recomputing `cip`, `b`, `ξ` and the permutation scalar — is
`finalize_other_proof`'s; the group circuit consumes them as claims (`advice`, `plonk`, the
deferred `ξ`) and scales by them. Their relation to the statement `finalize` checks is
`verify`'s (`step_verifier.ml:1340`), stated above this module.

`IvpReads` is the read, on either side (`IvpSide`): the digest is the wire's
(`runOracles`), the four plonk claims and the returned round prechallenges are the wire's
fq / IPA prechallenges up to the `lowest_128_bits` slack `PrechallengeAlias`, and the success
bit holds exactly when the Schnorr equation `Ipa.schnorrAt` holds — at the circuit's own
transcript (the wire's up to those slacks and the map-to-curve's sign), over the wire's
batch stream `runInput`, at the claimed `ξ`, `cip`, `b`. The `sg`-correctness equation of
`Ipa.verifyWith` is NOT the circuit's: pickles defers it to the next proof, whose verifier
absorbs this `sg` as an old accumulator (`KimchiProof.olds`). `IvpTies` names what the read
assumes: the cells read as the wire's key, proof and claims.

`incrementallyVerifyProof_wrap_reads` is the wrap side's read; the step side's is pending on
its `x_hat` gadget.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta
open CompElliptic.CurveForms.ShortWeierstrass
open scoped Kimchi

/-! ## The gadget -/

section Gadget

variable {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]

/-- The deployed `incrementally_verify_proof` return
(`Field.t * (`Success of Boolean.var * Bulletproof_challenge.t array)`): the fq-sponge
digest before evaluations, the group-side acceptance bit, and the raw 128-bit round
prechallenges. -/
structure IvpOutput (F : Type) where
  /-- `sponge_digest_before_evaluations`. -/
  spongeDigest : FVar F
  /-- `Success`: the opening's Schnorr equation holds. -/
  success : BoolVar F
  /-- The squeezed round prechallenges, in round order, raw 128-bit. -/
  bulletproofChallenges : List (SizedF 128 (FVar F))

/-- The deferred plonk claims the group half consumes (OCaml `plonk`, PS
`deferredValues.plonk`): the four 128-bit challenges, asserted against the squeezes, and the
three shifted scalars `ft_comm` scales by. -/
structure IvpPlonk (F sf : Type) where
  /-- `α`, `β`, `γ`, `ζ`. -/
  chals : PlonkClaims F
  /-- The permutation scalar claim (`perm`). -/
  perm : sf
  /-- The `ζ^{2^k}` claim (`zeta_to_srs_length`). -/
  zetaToSrsLength : sf
  /-- The `ζⁿ` claim (`zeta_to_domain_size`). -/
  zetaToDomainSize : sf

/-- What the group half consumes (PS `IncrementallyVerifyProofInput`; the OCaml arguments
`sg_old`, `plonk`, `xi`, `advice`, `verification_key`, `messages`, `opening`): every
commitment as its chunk list, in the key's and proof's column order. -/
structure IvpInput (F sf : Type) where
  /-- The previous proofs' challenge-polynomial commitments, each under its keep bit on the
  wrap side (`Opt.Maybe (keep, p)`) and unmasked on the step side (padded with dummies). -/
  sgOld : List (Option (BoolVar F) × AffinePoint (FVar F))
  /-- The deferred plonk claims. -/
  plonk : IvpPlonk F sf
  /-- The deferred polyscale `ξ`, 128 bits. -/
  xi : SizedF 128 (FVar F)
  /-- The deferred `cip` and `b` (`advice`). -/
  deferred : BulletproofDeferred sf
  /-- The key's last permutation commitment `σ₆`, absorbed in the index digest and read by
  `ft_comm` — not a batch base. -/
  sigmaLast : List (AffinePoint (FVar F))
  /-- The key's six selector commitments: generic, poseidon, complete-add, mul, emul,
  endomul-scalar. -/
  indexComms : List (List (AffinePoint (FVar F)))
  /-- The key's fifteen coefficient commitments. -/
  coefficientsComm : List (List (AffinePoint (FVar F)))
  /-- The key's permutation commitments `σ₀…σ₅`. -/
  sigmaComm : List (List (AffinePoint (FVar F)))
  /-- The proof's fifteen witness commitments. -/
  wComm : List (List (AffinePoint (FVar F)))
  /-- The proof's permutation-accumulator commitment. -/
  zComm : List (AffinePoint (FVar F))
  /-- The proof's quotient chunks. -/
  tComm : List (AffinePoint (FVar F))
  /-- The opening proof. -/
  opening : BulletproofOpening F sf

/-- The shifted scalars the circuit scales by: the three of `ft_comm` and the four of the
opening check. -/
def IvpInput.shifted {F sf : Type} (inp : IvpInput F sf) : List sf :=
  [inp.plonk.perm, inp.plonk.zetaToSrsLength, inp.plonk.zetaToDomainSize,
   inp.deferred.combinedInnerProduct, inp.deferred.b, inp.opening.z1, inp.opening.z2]

/-- The batch bases in `to_batch` order (`step_verifier.ml:745–759`, `wrap_verifier.ml:1458–1490`):
`sg_old` under its masks, then unmasked `x_hat`, `ft_comm`, `z`, the six selectors, the
witness columns, the coefficients and `σ₀…σ₅`, each commitment's chunks adjacent. -/
def IvpInput.bases {F sf : Type} (inp : IvpInput F sf) (xHat : List (AffinePoint (FVar F)))
    (ftc : AffinePoint (FVar F)) : List (AffinePoint (FVar F) × Option (BoolVar F)) :=
  inp.sgOld.map (fun m => (m.2, m.1))
    ++ (xHat ++ [ftc] ++ inp.zComm ++ inp.indexComms.flatten ++ inp.wComm.flatten
        ++ inp.coefficientsComm.flatten ++ inp.sigmaComm.flatten).map (fun P => (P, none))

/-- `incrementally_verify_proof`: squeeze the index digest from the copied
`sponge_after_index`; the fq-sponge transcript — on the wrap side (`optSponge`) `x_hat` first
then the conditional sponge with `sg_old` under its keep bits, on the step side the plain
sponge with `x_hat` computed at its point of the schedule; assert the plonk claims equal the
squeezes (OCaml asserts them last; `Field.Assert.equal` on variables wires without a row, so
the placement is constraint-invariant, and the PS port asserts here); `ft_comm`; the bases;
`checkBulletproof` from the pre-digest sponge. -/
def incrementallyVerifyProof {sf : Type} (ops : IpaScalarOps F c sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F)
    (optSponge : Bool) (blindingH : AffinePoint (FVar F)) (spongeAfterIndex : SpongeVar F)
    (computeXHat : CircuitM F c (List (AffinePoint (FVar F)))) (inp : IvpInput F sf) :
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
  let ftc ← ftComm ops inp.sigmaLast inp.tComm inp.plonk.perm inp.plonk.zetaToSrsLength
    inp.plonk.zetaToDomainSize
  let o ← checkBulletproof ops e p endo gm sqrtF tr.sponge (inp.bases tr.xHat ftc)
    ⟨inp.xi, inp.deferred, inp.opening, blindingH⟩
  pure ⟨tr.digest, o.success, o.challenges⟩

end Gadget

/-! ## The read -/

section Read

variable {C : CommitmentCurve} {V : Valuation C.BaseField} {sf : Type}
  {ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf}

/-- A list of chunked commitment cells reads, column by column, as the wire's commitments. -/
def ColumnsRead (C : CommitmentCurve) (V : Valuation C.BaseField) {nc : ℕ}
    (cols : List (List (AffinePoint (FVar C.BaseField)))) (Ps : List (Vector C.Point nc)) :
    Prop :=
  List.Forall₂ (fun col P => CommReads C V col P.toList) cols Ps

/-- What the group half's read assumes of its cells (the OCaml inputs, read as the wire's
key `cvk`, proof `cp` and the claims): the kept `sg_old` are the proof's old accumulators'
commitments, each commitment column reads as its wire column, the shifted claims decode to the
wire's scalars where the wire has them (`perm`, `ζ^{2^k}`, `ζⁿ`, `z₁`, `z₂`) and are claims the
ladder read speaks about (`IvpSide.ClaimOk`), and the opening's points read as the proof's. The
deferred `ξ`, `cip`, `b` are tied to nothing here: the group half scales by them as claimed,
and the read speaks at their decodes. -/
structure IvpTies {nc : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) (inp : IvpInput C.BaseField sf)
    (oldsW : List (C.Point × Bool)) : Prop where
  /-- The `sg_old` cells read as `oldsW`'s points under their bits. -/
  olds : List.Forall₂ (MaskedBaseReads C.E.toAffine V) (inp.sgOld.map fun m => (m.2, m.1))
    (oldsW.map fun b => (SWPoint.equivPoint C.E b.1, b.2))
  /-- The kept `sg_old` are the proof's old accumulators' commitments, in order. -/
  olds_kept : (oldsW.filter (·.2)).map (·.1) = (cp.olds.map (·.sg)).toList
  /-- The witness commitments. -/
  w : ColumnsRead C V inp.wComm cp.wComm.toList
  /-- The permutation accumulator's commitment. -/
  z : CommReads C V inp.zComm cp.zComm.toList
  /-- The quotient chunks. -/
  t : CommReads C V inp.tComm cp.tComm.toList
  /-- The six selector commitments, in `to_batch` order. -/
  index : ColumnsRead C V inp.indexComms
    [cvk.genericComm, cvk.poseidonComm, cvk.completeAddComm, cvk.mulComm, cvk.emulComm,
     cvk.endomulScalarComm]
  /-- The coefficient commitments. -/
  coefficients : ColumnsRead C V inp.coefficientsComm cvk.coefficientsComm.toList
  /-- The permutation commitments `σ₀…σ₅`. -/
  sigma : ColumnsRead C V inp.sigmaComm (cvk.sigmaComm.take sigmaRows).toList
  /-- The last permutation commitment `σ₆`. -/
  sigmaLast : CommReads C V inp.sigmaLast (cvk.sigmaComm[6]).toList
  /-- The permutation-scalar claim decodes to the wire's. -/
  perm : S.decode inp.plonk.perm = runPScalar C σ cvk cp pub
  /-- The `ζ^{2^k}` claim decodes to the wire's. -/
  zetaM : S.decode inp.plonk.zetaToSrsLength = runZetaM C σ cvk cp pub
  /-- The `ζⁿ` claim decodes to the wire's. -/
  zetaN : S.decode inp.plonk.zetaToDomainSize = runZetaN C σ cvk cp pub
  /-- The opening's `z₁` decodes to the proof's. -/
  z1 : S.decode inp.opening.z1 = cp.opening.z1
  /-- The opening's `z₂` decodes to the proof's. -/
  z2 : S.decode inp.opening.z2 = cp.opening.z2
  /-- Every shifted scalar the circuit scales by is a claim the ladder read speaks about. -/
  claimOk : ∀ x ∈ inp.shifted, S.ClaimOk x
  /-- The `(L, R)` cells read as the proof's pairs. -/
  lr : List.Forall₂ (PairReads C.E.toAffine V) inp.opening.lr
    (cp.opening.lr.toList.map fun q => (SWPoint.equivPoint C.E q.1, SWPoint.equivPoint C.E q.2))
  /-- The `δ` cell reads as the proof's. -/
  delta : OnCurveAt C.E.toAffine V inp.opening.delta (SWPoint.equivPoint C.E cp.opening.delta)
  /-- The `sg` cell reads as the proof's. -/
  sg : OnCurveAt C.E.toAffine V inp.opening.sg (SWPoint.equivPoint C.E cp.opening.sg)

/-- The group half's read. With `pre` the wire's fq prechallenges (`fqOracles`' own,
`fqOracles_eq_fqPrechallenges`) and `r` its IPA prechallenges from the warm post-`ζ` state at
the claimed `cip` (`transcriptFrom_eq_ipaPrechallenges`'s form, the claim in place of the
wire's `cipOf`): (1) the digest cell, cast as the wire casts it, is the wire's digest; (2) the
four plonk claims, once read as prechallenges, are `pre`'s up to `PrechallengeAlias`; (3) for
any prechallenge `ξ₀` the claimed `ξ` reads as, the returned round prechallenges read as some
`ns`, `r`'s up to the alias, and, with `U` the map-to-curve of `r`'s `t` up to sign and `c₀`
`r`'s Schnorr prechallenge up to the alias, the success bit reads `1` exactly when
`Ipa.schnorrAt` holds at `U`, the expansions of `ns` and `c₀`, the claimed `cip` and `b`, the
wire's batch stream combined at `ξ₀`'s expansion, and the proof's opening. (The witnesses are
stated under the `ξ` reading because the opening check's read is; they do not depend on it.) -/
def IvpReads {nc : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) (inp : IvpInput C.BaseField sf)
    (o : IvpOutput C.BaseField) : Prop :=
  let pre := fqPrechallenges C.sponge.params cvk.digest
    ((cp.olds.map (·.sg)).toList.map fun P => (P.x, P.y))
    (coords C (publicCommitment C σ cvk pub)) (cp.wComm.toList.map (coords C))
    (coords C cp.zComm) (cp.tComm.toList.map fun P => (P.x, P.y))
  let ora := runOracles C σ cvk cp pub
  let r := ipaPrechallenges C.sponge.params ora.warm.sponge
    (scalarLimbs C (shiftScalar C (S.decode inp.deferred.combinedInnerProduct)))
    (cp.opening.lr.toList.map fun q => ((q.1.x, q.1.y), (q.2.x, q.2.y)))
    (cp.opening.delta.x, cp.opening.delta.y)
  let run := runInput C σ cvk cp pub
  ora.digest = castDigest C (o.spongeDigest.val V) ∧
  (∀ m, Reads128 V inp.plonk.chals.beta m → PrechallengeAlias C.base pre.1.1 m) ∧
  (∀ m, Reads128 V inp.plonk.chals.gamma m → PrechallengeAlias C.base pre.1.2.1 m) ∧
  (∀ m, Reads128 V inp.plonk.chals.alpha m → PrechallengeAlias C.base pre.1.2.2.1 m) ∧
  (∀ m, Reads128 V inp.plonk.chals.zeta m → PrechallengeAlias C.base pre.1.2.2.2 m) ∧
  ∀ ξ₀, Reads128 V inp.xi ξ₀ →
    ∃ (U : C.Point) (ns : List Prechallenge) (c₀ : Prechallenge)
      (chals : Vector C.ScalarField σ.k),
      (U = C.toGroup r.1 ∨ U = -C.toGroup r.1) ∧
      List.Forall₂ (Reads128 V) o.bulletproofChallenges ns ∧
      List.Forall₂ (PrechallengeAlias C.base) r.2.1 ns ∧
      PrechallengeAlias C.base r.2.2 c₀ ∧
      chals.toList = ns.map (fun m => Poseidon.FqSponge.endoExpand C.sponge.lam m.val) ∧
      (((↑o.success : CVar C.BaseField).val V = 1) ↔
        schnorrAt C σ U chals (Poseidon.FqSponge.endoExpand C.sponge.lam c₀.val)
          (S.decode inp.deferred.combinedInnerProduct) (S.decode inp.deferred.b)
          (combineCommitments C (Poseidon.FqSponge.endoExpand C.sponge.lam ξ₀.val)
            run.commitments.toArray)
          run.proof)

end Read

/-! ## Reading helpers -/

section Helpers

open WeierstrassCurve.Affine

variable {C : CommitmentCurve} {V : Valuation C.BaseField}

/-- A cell reading as a wire point across `equivPoint` has the point's coordinates: the wire's
points are all finite (the `𝒪` sentinel is not a curve read). -/
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

private theorem forall₂_append' {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {u₁ : List β} (l₂ : List α) (u₂ : List β),
      List.Forall₂ R l₁ u₁ → List.Forall₂ R l₂ u₂ → List.Forall₂ R (l₁ ++ l₂) (u₁ ++ u₂)
  | [], [], _, _, .nil, h₂ => h₂
  | _ :: _, _ :: _, l₂, u₂, .cons h hs, h₂ => .cons h (forall₂_append' l₂ u₂ hs h₂)

private theorem forall₂_flatten' {α β : Type} {R : α → β → Prop} :
    ∀ {l : List (List α)} {u : List (List β)}, List.Forall₂ (List.Forall₂ R) l u →
      List.Forall₂ R l.flatten u.flatten
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => forall₂_append' _ _ h (forall₂_flatten' hs)

/-- Unmasked chunked columns read as their points, kept, flattened. -/
private theorem ColumnsRead.masked {nc : ℕ} {cols : List (List (AffinePoint (FVar C.BaseField)))}
    {Ps : List (Vector C.Point nc)} (h : ColumnsRead C V cols Ps) :
    List.Forall₂ (MaskedBaseReads C.E.toAffine V) (cols.flatten.map fun P => (P, none))
      ((Ps.map Vector.toList).flatten.map fun P => (SWPoint.equivPoint C.E P, true)) := by
  rw [List.map_flatten, List.map_flatten]
  refine forall₂_flatten' ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_map_right_iff]
  exact h.imp fun _ _ hc => hc.masked

/-- A batch row's commitments. -/
private theorem zipSeg_fst {nc : ℕ} (comm : Vector C.Point nc)
    (ev : PointEvaluations (Vector C.ScalarField nc)) : (zipSeg C comm ev).map (·.1) = comm := by
  ext i hi
  simp [zipSeg]

private theorem map_fst_zip' {α β : Type} {n : ℕ} (as : Vector α n) (bs : Vector β n) :
    (as.zip bs).map (·.1) = as := by
  ext i hi
  simp

private theorem toList_map_fst_zip {α β γ : Type} {n : ℕ} (as : Vector α n) (bs : Vector β n)
    (f : α → γ) : List.map (fun x => f x.1) (as.toList.zip bs.toList) = as.toList.map f := by
  show List.map (f ∘ (fun x : α × β => x.1)) _ = _
  rw [← List.map_map, ← Vector.toList_zip, ← Vector.toList_map, map_fst_zip']

private theorem toList_flatten' {α : Type} {m n : ℕ} (v : Vector (Vector α n) m) :
    v.flatten.toList = (v.toList.map Vector.toList).flatten := by
  simp [Vector.flatten, Vector.toList, Function.comp_def]
  rfl

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

/-- The wire's batch stream commitments: the olds' `sg`, the public chunks, `ft_comm`, the tail. -/
private theorem runInput_comms {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    (runInput C σ cvk cp pub).commitments.toList
      = (cp.olds.map (·.sg)).toList ++ ((publicCommitment C σ cvk pub).toList
        ++ [runFtComm C σ cvk cp pub] ++ ((tailRowsOf C cvk cp).flatten.map (·.1)).toList) := by
  show ((runStreamP C σ cvk cp pub (runPubEvals C σ cvk cp pub)).map (·.1)).toList = _
  simp [runStreamP, Vector.toList_append, Function.comp_def, Vector.toList_push]

/-- The wire's stream after the olds' `sg`: the public chunks, `ft_comm`, the tail commitments. -/
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

/-- The batch bases read as the stream bases: the `sg_old` cells as the olds under their bits,
`x_hat` as the public chunks, `ft_comm` as `runFtComm`, the columns as the tail. -/
private theorem bases_reads {nc : ℕ} {sf : Type}
    {ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf}
    {S : IvpSide C V ops} {σ : SRS C.Point} {cvk : KimchiVK C nc} {cp : KimchiProof C nc σ.k}
    {pub : Array C.ScalarField} {inp : IvpInput C.BaseField sf} {oldsW : List (C.Point × Bool)}
    (hties : IvpTies S σ cvk cp pub inp oldsW) {xHat : List (AffinePoint (FVar C.BaseField))}
    (hx : CommReads C V xHat (publicCommitment C σ cvk pub).toList)
    {ftc : AffinePoint (FVar C.BaseField)}
    (hf : OnCurveAt C.E.toAffine V ftc (SWPoint.equivPoint C.E (runFtComm C σ cvk cp pub))) :
    List.Forall₂ (MaskedBaseReads C.E.toAffine V) (inp.bases xHat ftc)
      ((streamBv σ cvk cp pub oldsW).map fun b => (SWPoint.equivPoint C.E b.1, b.2)) := by
  unfold IvpInput.bases streamBv restOf
  rw [tailRows_comms]
  have hi := hties.index.masked
  have hw := hties.w.masked
  have hc := hties.coefficients.masked
  have hs := hties.sigma.masked
  simp only [List.map_append, List.map_map, List.append_assoc, List.map_cons, List.map_nil,
    Function.comp_def] at hi hw hc hs ⊢
  refine forall₂_append' _ _ hties.olds ?_
  refine forall₂_append' _ _ hx.masked ?_
  refine forall₂_append' _ _ (.cons ⟨hf, rfl⟩ .nil) ?_
  refine forall₂_append' _ _ hties.z.masked ?_
  refine forall₂_append' _ _ hi ?_
  refine forall₂_append' _ _ hw ?_
  exact forall₂_append' _ _ hc hs

end Helpers

/-! ## The wrap side's readings -/

section WrapHelpers

open Kimchi.Gate.VarBaseMul Pasta.Shifted

/-- At Vesta the one-wrap regime is the off-band condition: the subwrap disjunct is false. -/
private theorem vesta_regime_offBand {z : ℤ} (h : HasCurve.vesta.LadderRegime 255 z) :
    z ∉ forbiddenValues PALLAS_BASE_CARD := by
  rcases h with h | ⟨_, _, _, h⟩
  · exfalso
    have hO : HasCurve.vesta.W.order = PALLAS_BASE_CARD := Pasta.vesta_card
    rw [hO] at h
    exact absurd h (by norm_num [PALLAS_BASE_CARD])
  · have hO : HasCurve.vesta.W.order = PALLAS_BASE_CARD := Pasta.vesta_card
    rwa [hO] at h

/-- The wrap circuit absorbs the claimed `cip` as its one `Type1` limb, and the wire absorbs
`scalarLimbs (shiftScalar cip)`: at Vesta these agree, the ladder witness bounding the cell
below the scalar modulus so the decode's re-shift is the cell. -/
private theorem wrap_cip_limbs {V : Valuation Fq} {x : Type1 (FVar Fq)} {z : ℤ}
    (h : WrapLadderPre V x z) :
    scalarLimbs IpaVesta.curve (shiftScalar IpaVesta.curve (wrapDecode V x)) = [x.val.val V] := by
  have hsz : Nat.size IpaVesta.curve.scalar = 255 :=
    le_antisymm (Nat.size_le.mpr (by norm_num [PALLAS_BASE_CARD]))
      (Nat.lt_size.mpr (by norm_num [PALLAS_BASE_CARD]))
  have hlt : IpaVesta.curve.scalar < IpaVesta.curve.base := by decide
  simp only [scalarLimbs, shiftScalar, if_pos hlt, hsz, wrapDecode,
    shiftType1_unshiftType1 (by decide : (2 : Fp) ≠ 0)]
  obtain ⟨h0, hlt', hz⟩ := h
  have hval : ((x.val.val V).val : ℤ) = z := by
    rw [← hz, ZMod.val_intCast, Int.emod_eq_of_lt h0
      (lt_of_lt_of_le hlt' (by norm_num [PALLAS_SCALAR_CARD]))]
  have hv : (x.val.val V).val < PALLAS_BASE_CARD := by
    have : ((x.val.val V).val : ℤ) < 2 ^ 254 := hval ▸ hlt'
    have : (x.val.val V).val < 2 ^ 254 := by exact_mod_cast this
    exact lt_trans this (by norm_num [PALLAS_BASE_CARD])
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hv, ZMod.natCast_zmod_val]

/-! The wire bridges below are stated at a generic curve or at variables, projected to the
component in use, and only ever *rewritten* with at Vesta. The kernel compares same-headed
applications argument-first, so a goal `(⟨…⟩ : _ × _).2.2 = (fqSqueezes …).2.2` at the deployed
Poseidon parameters makes it try `⟨…⟩ ≡ fqSqueezes …` — and expand the sponge permutation
symbolically before that fails — where the projected `(fqPrechallenges …).2.2 =
(fqSqueezes …).2.2` closes syntactically. -/

/-- The wire's digest, through `fqOracles_eq_fqPrechallenges`. -/
private theorem fqOracles_digest_eq (C : CommitmentCurve) {nc k : ℕ} (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc k) (pc : Vector C.Point nc) :
    (fqOracles C cvk cp pc).digest
      = castDigest C (fqPrechallenges C.sponge.params cvk.digest
          ((cp.olds.map (·.sg)).toList.map fun P => (P.x, P.y)) (coords C pc)
          (cp.wComm.toList.map (coords C)) (coords C cp.zComm)
          (cp.tComm.toList.map fun P => (P.x, P.y))).2.1 := by
  rw [fqOracles_eq_fqPrechallenges]
  rfl

/-- The wire's warm state, through `fqOracles_eq_fqPrechallenges`. -/
private theorem fqOracles_warm_eq (C : CommitmentCurve) {nc k : ℕ} (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc k) (pc : Vector C.Point nc) :
    (fqOracles C cvk cp pc).warm.sponge
      = (fqPrechallenges C.sponge.params cvk.digest
          ((cp.olds.map (·.sg)).toList.map fun P => (P.x, P.y)) (coords C pc)
          (cp.wComm.toList.map (coords C)) (coords C cp.zComm)
          (cp.tComm.toList.map fun P => (P.x, P.y))).2.2 := by
  rw [fqOracles_eq_fqPrechallenges]

section Prechallenges

variable (C : CommitmentCurve) (p : Poseidon.Params (ZMod C.base)) (d : ZMod C.base)
  (a b : List (ZMod C.base × ZMod C.base)) (c : List (List (ZMod C.base × ZMod C.base)))
  (e f : List (ZMod C.base × ZMod C.base))

/-- `fqPrechallenges`'s `β` packing, at variables. -/
private theorem fqPrechallenges_beta :
    (fqPrechallenges p d a b c e f).1.1 = (fqSqueezes p d a b c e f).1.1.val % 2 ^ 128 := rfl

/-- `fqPrechallenges`'s `γ` packing, at variables. -/
private theorem fqPrechallenges_gamma :
    (fqPrechallenges p d a b c e f).1.2.1 = (fqSqueezes p d a b c e f).1.2.1.val % 2 ^ 128 :=
  rfl

/-- `fqPrechallenges`'s `α` packing, at variables. -/
private theorem fqPrechallenges_alpha :
    (fqPrechallenges p d a b c e f).1.2.2.1
      = (fqSqueezes p d a b c e f).1.2.2.1.val % 2 ^ 128 := rfl

/-- `fqPrechallenges`'s `ζ` packing, at variables. -/
private theorem fqPrechallenges_zeta :
    (fqPrechallenges p d a b c e f).1.2.2.2
      = (fqSqueezes p d a b c e f).1.2.2.2.val % 2 ^ 128 := rfl

/-- `fqPrechallenges`'s digest element, at variables. -/
private theorem fqPrechallenges_digestElem :
    (fqPrechallenges p d a b c e f).2.1 = (fqSqueezes p d a b c e f).2.1 := rfl

/-- `fqPrechallenges`'s pre-digest state, at variables. -/
private theorem fqPrechallenges_warm :
    (fqPrechallenges p d a b c e f).2.2 = (fqSqueezes p d a b c e f).2.2 := rfl

end Prechallenges

/-- The wrap field spelled as the wire's `ZMod IpaVesta.curve.base` (at the generic bridges'
instance) and as `Fq` name the same `fqSqueezes`, at variables. -/
private theorem fqSqueezes_base_eq (p : Poseidon.Params Fq) (d : Fq) (a b : List (Fq × Fq))
    (c : List (List (Fq × Fq))) (e f : List (Fq × Fq)) :
    (@fqSqueezes (ZMod IpaVesta.curve.base) (ZMod.instField _) p d a b c e f)
      = (fqSqueezes (F := Fq) p d a b c e f) := rfl

/-- Alias readings compose: the wire's prechallenges alias the cells' readings. -/
private theorem forall₂_alias {V : Valuation Fq} {pres : List ℕ}
    {us : List (SizedF 128 (FVar Fq))} {ns : List Prechallenge}
    (h1 : List.Forall₂ (fun (pre : ℕ) (u : SizedF 128 (FVar Fq)) =>
      ∀ m, Reads128 V u m → PrechallengeAlias PALLAS_SCALAR_CARD pre m) pres us)
    (h2 : List.Forall₂ (Reads128 V) us ns) :
    List.Forall₂ (PrechallengeAlias PALLAS_SCALAR_CARD) pres ns := by
  induction h1 generalizing ns with
  | nil => cases h2; exact .nil
  | cons h hs ih => cases h2 with | cons h' hs' => exact .cons (h _ h') (ih hs')

/-- A pair read as two wire points reads as their coordinates. -/
private theorem pairReads_reads {V : Valuation Fq}
    {q : AffinePoint (FVar Fq) × AffinePoint (FVar Fq)}
    {P : IpaVesta.curve.Point × IpaVesta.curve.Point}
    (h : PairReads IpaEndo.vesta.d.W V q
      (SWPoint.equivPoint Vesta.curve P.1, SWPoint.equivPoint Vesta.curve P.2)) :
    CircuitType.Reads V q (wirePt P.1, wirePt P.2) :=
  CircuitType.reads_prod.mpr
    ⟨reads_affinePoint.mpr (onCurveAt_equivPoint_coords (C := IpaVesta.curve) h.1),
     reads_affinePoint.mpr (onCurveAt_equivPoint_coords (C := IpaVesta.curve) h.2)⟩

/-- The wrap side's `sg_old` cells, each under its keep bit, read as the olds' bits and
coordinates — the conditional transcript's reading of the masked list. -/
private theorem olds_reads {V : Valuation Fq} :
    ∀ {sgOld : List (Option (BoolVar Fq) × AffinePoint (FVar Fq))}
      {oldsW : List (IpaVesta.curve.Point × Bool)},
      (∀ m ∈ sgOld, m.1.isSome) →
      List.Forall₂ (MaskedBaseReads HasCurve.vesta.W V) (sgOld.map fun m => (m.2, m.1))
        (oldsW.map fun b => (SWPoint.equivPoint Vesta.curve b.1, b.2)) →
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
        reads_affinePoint.mpr (onCurveAt_equivPoint_coords (C := IpaVesta.curve) h1.1)⟩
  | [], _ :: _, _, h => by rw [List.map_cons] at h; cases h
  | _ :: _, [], _, h => by rw [List.map_cons] at h; cases h

/-- The conditional transcript returns the `x_hat` it was given. -/
private theorem transcriptOpt_xHat {V : Valuation Fq} (p : Poseidon.Params Fq)
    (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (endo indexDigest : FVar Fq) (sgOld : List (BoolVar Fq × AffinePoint (FVar Fq)))
    (xHat : List (AffinePoint (FVar Fq))) (wComm : List (List (AffinePoint (FVar Fq))))
    (zComm tComm : List (AffinePoint (FVar Fq))) :
    ⦃⌜True⌝⦄ fqSpongeTranscriptOpt (c := Builder V (KimchiConstraint Fq)) p endo indexDigest sgOld
      xHat wComm zComm tComm
    ⦃⇓ o _ => ⌜o.xHat = xHat⌝⦄ := by
  simp only [fqSpongeTranscriptOpt]
  have h1 := fun (b : Bool) ov => builder_spec_true
    (optSqueezePrechallenge (c := Builder V (KimchiConstraint Fq)) p b endo ov)
  have h2 := fun sv => builder_spec_true
    (SpongeVar.squeeze (c := Builder V (KimchiConstraint Fq)) p sv)
  mvcgen -trivial [h1, h2]
  case vc1.hsize => exact hsize

/-- The opening's ties at the wrap side's spellings (`IpaEndo.vesta.d.W`, `Vesta.curve`), as
`checkBulletproof_wrap_spec` and `checkBulletproof_spec` consume them. A separate declaration
so the curve-spelling conversions are kernel-checked on their own. -/
private theorem wrap_opening_ties {nc : ℕ} {V : Valuation Fq} {σ : SRS IpaVesta.curve.Point}
    {cvk : KimchiVK IpaVesta.curve nc} {cp : KimchiProof IpaVesta.curve nc σ.k} {pub : Array Fp}
    {inp : IvpInput Fq (Type1 (FVar Fq))} {oldsW : List (IpaVesta.curve.Point × Bool)}
    (hties : IvpTies (wrapSide V) σ cvk cp pub inp oldsW) {blindingH : AffinePoint (FVar Fq)}
    (hh : OnCurveAt HasCurve.vesta.W V blindingH (SWPoint.equivPoint Vesta.curve σ.h)) :
    List.Forall₂ (PairReads IpaEndo.vesta.d.W V) inp.opening.lr (cp.opening.lr.toList.map fun q =>
      (SWPoint.equivPoint Vesta.curve q.1, SWPoint.equivPoint Vesta.curve q.2)) ∧
    OnCurveAt IpaEndo.vesta.d.W V inp.opening.delta
      (SWPoint.equivPoint Vesta.curve cp.opening.delta) ∧
    OnCurveAt IpaEndo.vesta.d.W V inp.opening.sg (SWPoint.equivPoint Vesta.curve cp.opening.sg) ∧
    OnCurveAt IpaEndo.vesta.d.W V blindingH (SWPoint.equivPoint Vesta.curve σ.h) ∧
    List.Forall₂ (CircuitType.Reads V) inp.opening.lr
      (cp.opening.lr.toList.map fun q => (wirePt q.1, wirePt q.2)) ∧
    CircuitType.Reads V inp.opening.delta (wirePt cp.opening.delta) :=
  ⟨hties.lr, hties.delta, hties.sg, hh,
   List.forall₂_map_right_iff.2
     ((List.forall₂_map_right_iff.1 hties.lr).imp fun _ _ h => pairReads_reads h),
   reads_affinePoint.mpr (onCurveAt_equivPoint_coords (C := IpaVesta.curve) hties.delta)⟩

/-- `bases_reads` at the wrap side's spellings (a separate declaration, as above). -/
private theorem wrap_bases_reads {nc : ℕ} {V : Valuation Fq} {σ : SRS IpaVesta.curve.Point}
    {cvk : KimchiVK IpaVesta.curve nc} {cp : KimchiProof IpaVesta.curve nc σ.k} {pub : Array Fp}
    {inp : IvpInput Fq (Type1 (FVar Fq))} {oldsW : List (IpaVesta.curve.Point × Bool)}
    (hties : IvpTies (wrapSide V) σ cvk cp pub inp oldsW) {xHat : List (AffinePoint (FVar Fq))}
    (hx : CommReads IpaVesta.curve V xHat (publicCommitment IpaVesta.curve σ cvk pub).toList)
    {ftc : AffinePoint (FVar Fq)}
    (hf : OnCurveAt IpaVesta.curve.E.toAffine V ftc
      (SWPoint.equivPoint IpaVesta.curve.E (runFtComm IpaVesta.curve σ cvk cp pub))) :
    List.Forall₂ (MaskedBaseReads IpaEndo.vesta.d.W V) (inp.bases xHat ftc)
      ((streamBv σ cvk cp pub oldsW).map fun b => (SWPoint.equivPoint Vesta.curve b.1, b.2)) :=
  bases_reads hties hx hf

/-- The wire's warm state at the transcript readings is the raw pre-digest state. -/
private theorem wrap_warm_eq {nc : ℕ} (σ : SRS IpaVesta.curve.Point)
    (cvk : KimchiVK IpaVesta.curve nc) (cp : KimchiProof IpaVesta.curve nc σ.k) (pub : Array Fp)
    (hpre : fqSqueezes (F := Fq) IpaVesta.curve.sponge.params cvk.digest
      (((cp.olds.map (·.sg)).toList.map wirePt).map pointCoords)
      (((publicCommitment IpaVesta.curve σ cvk pub).toList.map wirePt).map pointCoords)
      ((cp.wComm.toList.map fun P => P.toList.map wirePt).map (·.map pointCoords))
      ((cp.zComm.toList.map wirePt).map pointCoords)
      ((cp.tComm.toList.map wirePt).map pointCoords)
      = fqSqueezes (F := Fq) IpaVesta.curve.sponge.params cvk.digest
        ((cp.olds.map (·.sg)).toList.map fun P => (P.x, P.y))
        (coords IpaVesta.curve (publicCommitment IpaVesta.curve σ cvk pub))
        (cp.wComm.toList.map (coords IpaVesta.curve)) (coords IpaVesta.curve cp.zComm)
        (cp.tComm.toList.map fun P => (P.x, P.y))) :
    (runOracles IpaVesta.curve σ cvk cp pub).warm.sponge
      = (fqSqueezes (F := Fq) IpaVesta.curve.sponge.params cvk.digest
        (((cp.olds.map (·.sg)).toList.map wirePt).map pointCoords)
        (((publicCommitment IpaVesta.curve σ cvk pub).toList.map wirePt).map pointCoords)
        ((cp.wComm.toList.map fun P => P.toList.map wirePt).map (·.map pointCoords))
        ((cp.zComm.toList.map wirePt).map pointCoords)
        ((cp.tComm.toList.map wirePt).map pointCoords)).2.2 := by
  show (fqOracles IpaVesta.curve cvk cp (publicCommitment IpaVesta.curve σ cvk pub)).warm.sponge = _
  rw [fqOracles_warm_eq, fqPrechallenges_warm IpaVesta.curve, fqSqueezes_base_eq, ← hpre]

/-- `IvpReads`'s IPA prechallenges at the wrap side are the opening check's, at the claimed
`cip`'s one limb and the pairs' and `δ`'s coordinate readings. -/
private theorem wrap_ipa_pre_eq {nc : ℕ} {V : Valuation Fq} (σ : SRS IpaVesta.curve.Point)
    (cvk : KimchiVK IpaVesta.curve nc) (cp : KimchiProof IpaVesta.curve nc σ.k) (pub : Array Fp)
    (cip : Type1 (FVar Fq)) {zc : ℤ} (hzc : WrapLadderPre V cip zc)
    (s : Poseidon.State Fq) (hw : (runOracles IpaVesta.curve σ cvk cp pub).warm.sponge = s) :
    ipaPrechallenges Poseidon.FqVesta.spec.params
        (runOracles IpaVesta.curve σ cvk cp pub).warm.sponge
        (scalarLimbs IpaVesta.curve (shiftScalar IpaVesta.curve ((wrapSide V).decode cip)))
        (cp.opening.lr.toList.map fun q => ((q.1.x, q.1.y), (q.2.x, q.2.y)))
        (cp.opening.delta.x, cp.opening.delta.y)
      = ipaPrechallenges IpaVesta.curve.sponge.params s [cip.val.val V]
          ((cp.opening.lr.toList.map fun q => (wirePt q.1, wirePt q.2)).map coordsPair)
          ((wirePt cp.opening.delta).x, (wirePt cp.opening.delta).y) := by
  show ipaPrechallenges IpaVesta.curve.sponge.params _
    (scalarLimbs IpaVesta.curve (shiftScalar IpaVesta.curve (wrapDecode V cip))) _ _ = _
  rw [wrap_cip_limbs hzc, hw, List.map_map]
  rfl

/-- The success clause at the stream bases and the proof record is `IvpReads`'s, at
`runInput`'s commitments and `cp.opening`. -/
private theorem wrap_success_eq {nc : ℕ} {V : Valuation Fq} (σ : SRS IpaVesta.curve.Point)
    (cvk : KimchiVK IpaVesta.curve nc) (cp : KimchiProof IpaVesta.curve nc σ.k) (pub : Array Fp)
    (oldsW : List (IpaVesta.curve.Point × Bool))
    (hkept : (oldsW.filter (·.2)).map (·.1) = (cp.olds.map (·.sg)).toList)
    (z1 z2 : Type1 (FVar Fq)) (hz1 : wrapDecode V z1 = cp.opening.z1)
    (hz2 : wrapDecode V z2 = cp.opening.z2) (U : IpaVesta.curve.Point)
    (chals : Vector Fp σ.k) (c cip b ξ : Fp) (P : Prop) :
    (P ↔ schnorrAt IpaVesta.curve σ U chals c cip b
        (combineCommitments IpaVesta.curve ξ
          ((((streamBv σ cvk cp pub oldsW).filter (·.2)).map (·.1)).toArray))
        ⟨cp.opening.lr, cp.opening.delta, wrapDecode V z1, wrapDecode V z2, cp.opening.sg⟩) →
    (P ↔ schnorrAt IpaVesta.curve σ U chals c cip b
        (combineCommitments IpaVesta.curve ξ
          (runInput IpaVesta.curve σ cvk cp pub).commitments.toArray)
        (runInput IpaVesta.curve σ cvk cp pub).proof) := by
  rw [streamBv_kept σ cvk cp pub oldsW hkept, Array.toArray_toList, hz1, hz2]
  exact id

/-- `fqSpongeTranscriptOpt_spec` at the wrap field, its readings moved into the postcondition
so the assembly can feed it to `mvcgen` before the readings are in hand, together with the
returned `x_hat`. -/
private theorem transcriptOpt_wrap {V : Valuation Fq}
    (hsize : IpaVesta.curve.sponge.params.roundConstants.size = Poseidon.fullRounds)
    (endo indexDigest : FVar Fq) (sgOld : List (BoolVar Fq × AffinePoint (FVar Fq)))
    (xHat : List (AffinePoint (FVar Fq))) (wComm : List (List (AffinePoint (FVar Fq))))
    (zComm tComm : List (AffinePoint (FVar Fq))) :
    ⦃⌜True⌝⦄ fqSpongeTranscriptOpt (c := Builder V (KimchiConstraint Fq))
      IpaVesta.curve.sponge.params endo indexDigest sgOld xHat wComm zComm tComm
    ⦃⇓ o _ => ⌜o.xHat = xHat ∧
      ∀ (sgv : List (Bool × AffinePoint Fq)) (xv : List (AffinePoint Fq))
      (wv : List (List (AffinePoint Fq))) (zv tv : List (AffinePoint Fq)),
      List.Forall₂ (CircuitType.Reads V) sgOld sgv → List.Forall₂ (CircuitType.Reads V) xHat xv →
      List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) wComm wv →
      List.Forall₂ (CircuitType.Reads V) zComm zv → List.Forall₂ (CircuitType.Reads V) tComm tv →
      zv ≠ [] → tv ≠ [] →
      (∀ k : ℕ, k ≤ 1 + 2 * (sgv.length + xv.length + wv.flatten.length + zv.length + tv.length) →
        (k : Fq) = 0 → k = 0) →
      FqTranscriptReads IpaVesta.curve.sponge.params (indexDigest.val V)
        ((sgv.filter (·.1)).map (·.2)) xv wv zv tv V o⌝⦄ := by
  have hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : Fq) = k → j = k := by
    intro j k hj hk h
    interval_cases j <;> interval_cases k <;> first | rfl | exact absurd h (by decide)
  rw [builder_spec_iff]
  intro nv hsat
  refine ⟨(builder_spec_iff _ _).mp (transcriptOpt_xHat _ hsize endo indexDigest sgOld xHat wComm
    zComm tComm) nv hsat, fun sgv xv wv zv tv hsg hx hw hz ht hzne htne hchar => ?_⟩
  exact (builder_spec_iff _ _).mp (fqSpongeTranscriptOpt_spec (by decide) (by decide) _ hsize
    hall endo indexDigest sgOld sgv hsg xHat xv hx wComm wv hw zComm tComm zv tv hz ht
    hzne htne hchar) nv hsat

/-- The wrap side's `checkBulletproof` on one run: the transcript reading
(`checkBulletproof_spec`) and the algebra (`checkBulletproof_wrap_spec`), their readings moved
into the postcondition. -/
private theorem checkBulletproof_wrap {V : Valuation Fq}
    (hsize : IpaVesta.curve.sponge.params.roundConstants.size = Poseidon.fullRounds)
    (endo : FVar Fq) (sqrtF : Fq → Option Fq) (sv : SpongeVar Fq)
    (bases : List (AffinePoint (FVar Fq) × Option (BoolVar Fq)))
    (inp : CheckBulletproofInput Fq (Type1 (FVar Fq))) :
    ⦃⌜True⌝⦄ checkBulletproof (c := Builder V (KimchiConstraint Fq)) IpaScalarOps.wrap
      IpaEndo.vesta IpaVesta.curve.sponge.params endo groupMapParamsVesta sqrtF sv bases inp
    ⦃⇓ o _ => ⌜(∀ (s₀ : Poseidon.State Fq) (lrv : List (AffinePoint Fq × AffinePoint Fq))
        (δv : AffinePoint Fq), SpongeVar.ReadsAt V sv s₀ →
        List.Forall₂ (CircuitType.Reads V) inp.opening.lr lrv →
        CircuitType.Reads V inp.opening.delta δv →
        CheckBulletproofReads IpaVesta.curve.sponge.params s₀
          [inp.deferred.combinedInnerProduct.val.val V] lrv δv V o) ∧
      (∀ (bvW : List (SWPoint Vesta.curve × Bool)),
        List.Forall₂ (MaskedBaseReads IpaEndo.vesta.d.W V) bases
          (bvW.map fun b => ((SWPoint.equivPoint Vesta.curve) b.1, b.2)) →
        bases ≠ [] → (∀ h, bvW.getLast? = some h → h.2 = true) →
        (∀ (x : Type1 (FVar Fq)) (z : ℤ), x ∈ inp.scaled → WrapLadderPre V x z →
          wrapLadderDec z ∉ forbiddenValues PALLAS_BASE_CARD) →
        ∀ (n : Prechallenge), Reads128 V inp.xi n →
        ∀ (σ : SRS (SWPoint Vesta.curve))
          (lrW : Vector (SWPoint Vesta.curve × SWPoint Vesta.curve) σ.k)
          (δW sgW : SWPoint Vesta.curve),
        List.Forall₂ (PairReads IpaEndo.vesta.d.W V) inp.opening.lr (lrW.toList.map fun q =>
          ((SWPoint.equivPoint Vesta.curve) q.1, (SWPoint.equivPoint Vesta.curve) q.2)) →
        inp.opening.lr ≠ [] →
        OnCurveAt IpaEndo.vesta.d.W V inp.opening.delta ((SWPoint.equivPoint Vesta.curve) δW) →
        OnCurveAt IpaEndo.vesta.d.W V inp.opening.sg ((SWPoint.equivPoint Vesta.curve) sgW) →
        OnCurveAt IpaEndo.vesta.d.W V inp.blindingGenerator ((SWPoint.equivPoint Vesta.curve) σ.h) →
        ∃ (U : SWPoint Vesta.curve) (ns : List Prechallenge) (c₀ : Prechallenge)
          (chals : Vector Fp σ.k),
          (U = Poseidon.GroupMap.toGroup Poseidon.GroupMapVesta.spec (o.t.val V) ∨
            U = -Poseidon.GroupMap.toGroup Poseidon.GroupMapVesta.spec (o.t.val V)) ∧
          List.Forall₂ (Reads128 V) o.challenges ns ∧ Reads128 V o.c c₀ ∧
          chals.toList
            = ns.map (fun m => Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam m.val) ∧
          (∃ z : ℤ, WrapLadderPre V inp.deferred.combinedInnerProduct z) ∧
          ((↑o.success : CVar Fq).val V = 1 ↔
            schnorrAt IpaVesta.curve σ U chals
              (Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam c₀.val)
              (wrapDecode V inp.deferred.combinedInnerProduct) (wrapDecode V inp.deferred.b)
              (combineCommitments IpaVesta.curve
                (Poseidon.FqSponge.endoExpand Poseidon.FqVesta.spec.lam n.val)
                ((bvW.filter (·.2)).map (·.1)).toArray)
              ⟨lrW, δW, wrapDecode V inp.opening.z1, wrapDecode V inp.opening.z2, sgW⟩))⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat
  refine ⟨fun s₀ lrv δv hs hlr hδ => ?_, fun bvW hb hbne hlast hband n hxi σ lrW δW sgW hlr hlrne
    hδ hsg hh => ?_⟩
  · exact (builder_spec_iff _ _).mp (checkBulletproof_spec (by decide) (by decide)
      IpaScalarOps.wrap IpaEndo.vesta _ hsize endo groupMapParamsVesta sqrtF sv s₀ hs bases inp
      lrv hlr δv hδ) nv hsat
  · exact (builder_spec_iff _ _).mp (checkBulletproof_wrap_spec _ hsize endo sqrtF sv bases bvW
      hb hbne hlast inp hband n hxi σ lrW δW sgW hlr hlrne hδ hsg hh) nv hsat

end WrapHelpers

/-! ## The wrap side -/

/-- **The wrap side's group half reads as the wire's.** At Vesta (`IpaVesta.curve`, the wrap
circuit over `Fq` verifying a step proof), on the conditional sponge with every `sg_old`
under a keep bit, given the index-digest squeeze reads as the key's digest, `x_hat` reads as
the wire's `publicCommitment` (`xHat_reads_publicCommitment` supplies this from
`XhatBinding`), and the cells tie as `IvpTies`, the output satisfies `IvpReads`. -/
theorem incrementallyVerifyProof_wrap_reads {nc : ℕ} {V : Valuation Fq}
    (σ : SRS IpaVesta.curve.Point) (cvk : KimchiVK IpaVesta.curve nc)
    (cp : KimchiProof IpaVesta.curve nc σ.k) (pub : Array Fp)
    (hsize : IpaVesta.curve.sponge.params.roundConstants.size = Poseidon.fullRounds)
    (endo : FVar Fq) (sqrtF : Fq → Option Fq) (blindingH : AffinePoint (FVar Fq))
    (spongeAfterIndex : SpongeVar Fq)
    (computeXHat : CircuitM Fq (Builder V (KimchiConstraint Fq)) (List (AffinePoint (FVar Fq))))
    (inp : IvpInput Fq (Type1 (FVar Fq))) (oldsW : List (IpaVesta.curve.Point × Bool))
    (hIdx : ∃ s : Poseidon.State Fq, SpongeVar.ReadsAt V spongeAfterIndex s ∧
      (Poseidon.squeeze IpaVesta.curve.sponge.params s).1 = cvk.digest)
    (hXhat : ⦃⌜True⌝⦄ computeXHat ⦃⇓ pts _ =>
      ⌜CommReads IpaVesta.curve V pts (publicCommitment IpaVesta.curve σ cvk pub).toList⌝⦄)
    (hmask : ∀ m ∈ inp.sgOld, m.1.isSome)
    (hties : IvpTies (wrapSide V) σ cvk cp pub inp oldsW)
    (hh : OnCurveAt HasCurve.vesta.W V blindingH (SWPoint.equivPoint Vesta.curve σ.h))
    (hnc : 0 < nc) (htne : inp.tComm ≠ []) (hlrne : inp.opening.lr ≠ [])
    (hchar : ∀ k : ℕ, k ≤ 1 + 2 * (inp.sgOld.length + nc + inp.wComm.flatten.length
      + inp.zComm.length + inp.tComm.length) → (k : Fq) = 0 → k = 0) :
    ⦃⌜True⌝⦄
    incrementallyVerifyProof IpaScalarOps.wrap IpaEndo.vesta IpaVesta.curve.sponge.params endo
      groupMapParamsVesta sqrtF true blindingH spongeAfterIndex computeXHat inp
    ⦃⇓ o _ => ⌜IvpReads (wrapSide V) σ cvk cp pub inp o⌝⦄ := by
  have hσlen : inp.sigmaLast.toArray.size = nc := by
    have := hties.sigmaLast.length_eq
    simpa using this
  simp only [incrementallyVerifyProof, if_true]
  have htr := fun (d : FVar Fq) (xHat : List (AffinePoint (FVar Fq))) =>
    transcriptOpt_wrap (V := V) hsize endo d (inp.sgOld.map fun m => (m.1.getD true_, m.2)) xHat
      inp.wComm inp.zComm inp.tComm
  have hasrt := fun (tr : FqTranscriptOutput Fq) =>
    assertPlonkChallenges_spec (V := V) tr inp.plonk.chals
  have hft := ftComm_reads (wrapSide V) σ cvk cp pub inp.plonk.perm inp.plonk.zetaToSrsLength
    inp.plonk.zetaToDomainSize ⟨inp.sigmaLast.toArray, hσlen⟩ inp.tComm hnc htne
  simp only [Vector.toList_mk] at hft
  have hcb := fun (sv : SpongeVar Fq)
    (bases : List (AffinePoint (FVar Fq) × Option (BoolVar Fq))) =>
    checkBulletproof_wrap (V := V) hsize endo sqrtF sv bases
      ⟨inp.xi, inp.deferred, inp.opening, blindingH⟩
  mvcgen -trivial [hXhat, htr, hasrt, hft, hcb]
  case vc1.hsize => exact hsize
  rename_i _ rIdx _ hIdx' xHat _ hx tr _ htr' _ _ hasrt' ftc _ hft' o _ hcb'
  -- the index digest
  obtain ⟨sIdx, hsIdx, hdig⟩ := hIdx
  have hd : rIdx.1.val V = cvk.digest := (hIdx' sIdx hsIdx).1.trans hdig
  -- the transcript, at the wire readings of every absorbed cell
  have hsgv := olds_reads hmask hties.olds
  have hzne : (cp.zComm.toList.map wirePt) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  have htne' : (cp.tComm.toList.map wirePt) ≠ [] := by
    intro h
    apply htne
    rw [List.map_eq_nil_iff] at h
    exact List.eq_nil_of_length_eq_zero (hties.t.length_eq.trans (by rw [h]; rfl))
  have hchar' : ∀ k : ℕ, k ≤ 1 + 2 * ((oldsW.map fun b => (b.2, wirePt b.1)).length
      + ((publicCommitment IpaVesta.curve σ cvk pub).toList.map wirePt).length
      + (cp.wComm.toList.map fun P => P.toList.map wirePt).flatten.length
      + (cp.zComm.toList.map wirePt).length + (cp.tComm.toList.map wirePt).length) →
      (k : Fq) = 0 → k = 0 := by
    intro k hk
    refine hchar k ?_
    have h1 := hsgv.length_eq
    have h2 := (forall₂_flatten' hties.w.reads).length_eq
    have h3 := hties.z.length_eq
    have h4 := hties.t.length_eq
    simp only [List.length_map, Vector.length_toList] at h1 h2 h3 h4 hk ⊢
    omega
  have hFq := htr'.2 _ _ _ _ _ hsgv hx.reads hties.w.reads hties.z.reads hties.t.reads hzne htne'
    hchar'
  have hx' : CommReads IpaVesta.curve V tr.xHat
      (publicCommitment IpaVesta.curve σ cvk pub).toList :=
    htr'.1 ▸ hx
  rw [hd] at hFq
  -- the kept `sg_old` readings are the olds' `sg`
  have hkept : ((oldsW.map fun b => (b.2, wirePt b.1)).filter (·.1)).map (·.2)
      = (cp.olds.map (·.sg)).toList.map wirePt := by
    rw [← hties.olds_kept, List.filter_map, List.map_map, List.map_map]
    rfl
  rw [hkept] at hFq
  have hp : 2 ^ 254 < PALLAS_SCALAR_CARD := by norm_num [PALLAS_SCALAR_CARD]
  -- the wire's fq squeezes at these readings are `IvpReads`'s
  have hpre : fqSqueezes (F := Fq) IpaVesta.curve.sponge.params cvk.digest
      (((cp.olds.map (·.sg)).toList.map wirePt).map pointCoords)
      (((publicCommitment IpaVesta.curve σ cvk pub).toList.map wirePt).map pointCoords)
      ((cp.wComm.toList.map fun P => P.toList.map wirePt).map (·.map pointCoords))
      ((cp.zComm.toList.map wirePt).map pointCoords) ((cp.tComm.toList.map wirePt).map pointCoords)
      = fqSqueezes (F := Fq) IpaVesta.curve.sponge.params cvk.digest
        ((cp.olds.map (·.sg)).toList.map fun P => (P.x, P.y))
        (coords IpaVesta.curve (publicCommitment IpaVesta.curve σ cvk pub))
        (cp.wComm.toList.map (coords IpaVesta.curve)) (coords IpaVesta.curve cp.zComm)
        (cp.tComm.toList.map fun P => (P.x, P.y)) := by
    delta Kimchi.Verifier.coords
    simp only [pointCoords, wirePt, List.map_map, Function.comp_def]
  unfold IvpReads
  dsimp only
  rw [fqPrechallenges_beta IpaVesta.curve, fqPrechallenges_gamma IpaVesta.curve,
    fqPrechallenges_alpha IpaVesta.curve, fqPrechallenges_zeta IpaVesta.curve,
    fqSqueezes_base_eq, ← hpre]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the digest
    show (fqOracles IpaVesta.curve cvk cp (publicCommitment IpaVesta.curve σ cvk pub)).digest = _
    rw [fqOracles_digest_eq, fqPrechallenges_digestElem IpaVesta.curve, fqSqueezes_base_eq,
      ← hpre, ← hFq.2.2.2.2.2.2.2.1]
  · intro m hm
    exact Low128.alias hp hFq.1 (hasrt'.1.symm.trans hm)
  · intro m hm
    exact Low128.alias hp hFq.2.1 (hasrt'.2.1.symm.trans hm)
  · intro m hm
    exact Low128.alias hp hFq.2.2.1 (hasrt'.2.2.1.symm.trans hm)
  · intro m hm
    exact Low128.alias hp hFq.2.2.2.1 (hasrt'.2.2.2.symm.trans hm)
  · intro ξ₀ hξ
    -- `ft_comm` reads as `runFtComm`: the claims decode and the chunk cells read as the ties say
    have hmem : ∀ x ∈ ([inp.plonk.perm, inp.plonk.zetaToSrsLength, inp.plonk.zetaToDomainSize] :
        List (Type1 (FVar Fq))), x ∈ inp.shifted := fun x hx =>
      (List.sublist_append_left [inp.plonk.perm, inp.plonk.zetaToSrsLength,
        inp.plonk.zetaToDomainSize] [inp.deferred.combinedInnerProduct, inp.deferred.b,
        inp.opening.z1, inp.opening.z2]).subset hx
    have hftc := hft' hties.perm hties.zetaM hties.zetaN
      (hties.claimOk _ (hmem _ (by simp))) (hties.claimOk _ (hmem _ (by simp)))
      (hties.claimOk _ (hmem _ (by simp))) (by simpa using hties.sigmaLast) hties.t
    -- the bases read as the stream bases
    have hb := wrap_bases_reads hties hx' hftc
    obtain ⟨hlrW, hδW, hsgW, hhW, hlrv, hδv⟩ := wrap_opening_ties hties hh
    have hbne : inp.bases tr.xHat ftc ≠ [] := by simp [IvpInput.bases]
    have hband : ∀ (x : Type1 (FVar Fq)) (z : ℤ),
        x ∈ (⟨inp.xi, inp.deferred, inp.opening, blindingH⟩ :
          CheckBulletproofInput Fq (Type1 (FVar Fq))).scaled →
        WrapLadderPre V x z →
        wrapLadderDec z ∉ Kimchi.Gate.VarBaseMul.forbiddenValues PALLAS_BASE_CARD := by
      intro x z hxs hpre
      have hxm : x ∈ inp.shifted :=
        (List.sublist_append_right [inp.plonk.perm, inp.plonk.zetaToSrsLength,
          inp.plonk.zetaToDomainSize] [inp.deferred.combinedInnerProduct, inp.deferred.b,
          inp.opening.z1, inp.opening.z2]).subset hxs
      exact vesta_regime_offBand ((hties.claimOk x hxm).2 z hpre)
    obtain ⟨U, ns, c₀, chals, hU, hns, hc, hchals, ⟨zc, hzc⟩, hiff⟩ :=
      hcb'.2 _ hb hbne (streamBv_last σ cvk cp pub oldsW) hband ξ₀ hξ σ cp.opening.lr
        cp.opening.delta cp.opening.sg hlrW hlrne hδW hsgW hhW
    -- the opening transcript, from the warm sponge
    have hT := CheckBulletproofReads.wire hp (hcb'.1 _ _ _ hFq.2.2.2.2.2.2.2.2 hlrv hδv)
    -- the wire's IPA prechallenges at these readings are `IvpReads`'s
    rw [wrap_ipa_pre_eq σ cvk cp pub inp.deferred.combinedInnerProduct hzc _
      (wrap_warm_eq σ cvk cp pub hpre)]
    refine ⟨U, ns, c₀, chals, ?_, hns, forall₂_alias hT.2.1 hns, hT.2.2 c₀ hc, hchals, ?_⟩
    · unfold Poseidon.GroupMapVesta.toGroup
      rw [← hT.1]
      exact hU
    · exact wrap_success_eq σ cvk cp pub oldsW hties.olds_kept inp.opening.z1 inp.opening.z2
        hties.z1 hties.z2 U chals _ _ _ _ _ hiff

end Pickles
