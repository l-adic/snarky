import Pickles.CheckBulletproof
import Kimchi.Verifier.Reflect

/-!
# The `ft_comm` commitment (`Common.ft_comm`)

The port of PS `Pickles.FtComm.ftComm` (OCaml `Common.ft_comm`, `common.ml:307–326`), called by
both verifiers (`step_verifier.ml:724` at `scale_fast2`, `wrap_verifier.ml:1428` at
`scale_fast`): the linearization commitment the group half constructs from the verification
key's last permutation commitment `σ₆`, the proof's quotient chunks `t_comm`, and the shifted
deferred claims `perm`, `ζ^{2^k}` (`zeta_to_srs_length`) and `ζⁿ` (`zeta_to_domain_size`):

  `ft_comm = scale (reduce σ₆) perm + reduce t_comm + negate (scale (reduce t_comm) ζⁿ)`

where `reduce` is the `ζ^{2^k}`-Horner collapse of a chunk array (`reduce_chunks`). The
emission order follows OCaml's right-to-left argument evaluation: reduce `σ₆`, scale by `perm`,
reduce `t_comm`, scale by `ζⁿ` and negate, then `f_comm + reduced_t`, then `+ negated`.

The gadget is generic in the side's shifted-scalar operations (`IpaScalarOps`); so is its read.
`IvpSide` names what a side supplies to read the group half's gadgets on the wire's commitment
curve: its ladder reading (`IpaScalarOps.Reading`), the scalar-field decode of a shifted claim
with the law tying a ladder witness's integer decode to it, the curve's group facts, and — for
the assembly `Pickles.IncrementallyVerify` — the endomorphism and map-to-curve data, the field
facts the transcript needs, the absorbed limbs of a claim, and the opening check's read. The
two deployed values, `wrapSide` and `stepSide`, live beside that assembly. `FtCommReads` is the
leg's read: the constructed cell crosses to the wire's `runFtComm`
(`combine(ζ^{2^k}, perm·σ₆) − (ζⁿ − 1)·combine(ζ^{2^k}, t_comm)`), given the claims decode to
the wire's scalars, each a claim the ladder read speaks about (`IvpSide.ClaimOk`: well-formed,
and its witnesses in the ladder regime — the forbidden-band premise of the `scale_fast` family),
and the commitment cells read as the key's / proof's commitments.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta Bulletproof Bulletproof.Ipa
open CompElliptic.CurveForms.ShortWeierstrass

/-! ## The gadget -/

section Gadget

variable {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]

/-- `reduce_chunks` (`common.ml:311–318`): the `z`-Horner collapse of the chunks `c₀, …, cₙ₋₁`
— `res := cₙ₋₁; for i = n−2 downto 0: res := cᵢ + scale res z`. Recursively
`c₀ + scale (reduce [c₁, …]) z`, whose evaluation emits the innermost (last-chunk) scale first,
as the OCaml loop does. The empty list is the unused origin. -/
def hornerReduce {sf : Type} (ops : IpaScalarOps F c sf) (z : sf) :
    List (AffinePoint (FVar F)) → CircuitM F c (AffinePoint (FVar F))
  | [] => pure ⟨.const 0, .const 0⟩
  | [chunk] => pure chunk
  | chunk :: rest => do
      let r ← hornerReduce ops z rest
      let s ← ops.scaleByShifted r z
      (·.p) <$> addFast .checkFinite chunk s

/-- `Common.ft_comm`: reduce `σ₆` and scale by `perm`; reduce `t_comm`; scale that by `ζⁿ` and
negate (the outer `+`'s right argument, evaluated first); then `f_comm + reduced_t`, then
`+ negated`. The negation is the pure `y ↦ −y` (OCaml `Inner_curve.negate`, PS
`Curves.negate`). -/
def ftComm {sf : Type} (ops : IpaScalarOps F c sf)
    (sigmaLast tComm : List (AffinePoint (FVar F)))
    (perm zetaToSrsLength zetaToDomainSize : sf) : CircuitM F c (AffinePoint (FVar F)) := do
  let reducedSigma ← hornerReduce ops zetaToSrsLength sigmaLast
  let fComm ← ops.scaleByShifted reducedSigma perm
  let chunkedT ← hornerReduce ops zetaToSrsLength tComm
  let zetaDom ← ops.scaleByShifted chunkedT zetaToDomainSize
  let r1 ← addFast .checkFinite fComm chunkedT
  (·.p) <$> addFast .checkFinite r1.p ⟨zetaDom.x, CVar.negate_ zetaDom.y⟩

end Gadget

/-! ## A side of the group half -/

/-- What a side supplies to read the group half's gadgets on the wire's commitment curve `C`:
how its shifted-scalar ladder reads (`R`); the scalar-field decode of a shifted claim, with the
law that a ladder witness's integer decode casts to it; the facts about `C`'s affine group the
adds and negations need — the scalar order kills the group (so an integer acts as its residue's
representative), the curve is short (`A = 0`), the base field is not of characteristic 2 and
the group has no 2-torsion; the endomorphism bundle and map-to-curve parameters the opening
check runs on; the field facts the transcript's squeezes need; the limbs a claim absorbs as,
tied to the wire's; and the opening check's read (`checkBulletproof_wrap_spec`,
`checkBulletproof_step_spec`, in the side-generic vocabulary). One value per deployed side:
`wrapSide`, `stepSide` (`Pickles.IncrementallyVerify`). -/
structure IvpSide (C : CommitmentCurve) (V : Valuation C.BaseField) {sf : Type}
    (ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf) where
  /-- The ladder's reading on the wire curve's affine group. -/
  R : IpaScalarOps.Reading (V := V) ops C.E.toAffine
  /-- The canonical decode of a shifted claim in the scalar field. -/
  decode : sf → C.ScalarField
  /-- A ladder witness of a claim decodes, in the scalar field, to the claim's decode. -/
  dec_cast : ∀ {x : sf} {w : R.wit}, R.Pre x w → (R.dec w : C.ScalarField) = decode x
  /-- The scalar order kills the wire point group. -/
  card_nsmul : ∀ X : C.Point, C.scalar • X = 0
  /-- The curve is short: `y² = x³ + B`. -/
  a_zero : C.E.A = 0
  /-- The base field is not of characteristic 2. -/
  two_ne : (2 : C.BaseField) ≠ 0
  /-- The affine group has no 2-torsion. -/
  two_torsion_free : ∀ P : C.E.toAffine.Point, P ≠ 0 → P + P ≠ 0
  /-- The endomorphism bundle the opening check's `endo_mul`s and challenge expansions run on. -/
  e : IpaEndo C.BaseField
  /-- The map-to-curve parameters deriving the `U` base. -/
  gm : GroupMapParams C.BaseField
  /-- The base field is not of characteristic 3 (the prechallenge squeeze's `endo_scalar`). -/
  three_ne : (3 : C.BaseField) ≠ 0
  /-- Naturals up to 3 cast injectively (the conditional sponge's mask count). -/
  small_inj : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : C.BaseField) = k → j = k
  /-- The base field has more than 254 bits: a low-128-bit read is a `PrechallengeAlias`. -/
  base_big : 2 ^ 254 < C.base
  /-- A claim whose absorbed limbs are canonical: on the wrap side every `Type1` claim (its
  ladder witness is below `2²⁵⁴ < |Fq|`); on the step side a split claim whose halved limb
  keeps `2·sDiv2 + sOdd` below the scalar modulus — the 254-bit range check alone leaves one
  bit of slack, the `scale_fast2` top-bit family (#341). -/
  Canon : sf → Prop
  /-- At a ladder witness of a canonical claim, the limbs the claim absorbs as are the wire's
  `scalarLimbs` of the shifted decode. -/
  absorb_limbs : ∀ {x : sf} {w : R.wit}, Canon x → R.Pre x w →
    (ops.shiftedToAbsorbFields x).map (·.val V) = scalarLimbs C (shiftScalar C (decode x))
  /-- The opening check's read: with the bases reading as `bvW` under their bits (the last
  kept), every scaled claim well-formed with its witnesses in regime, `ξ` reading as `n` and the
  opening's points as the wire's, the challenges read as some `ns`, `c` as some `c₀`, `U` is the
  map-to-curve of `t` up to sign, `cip` has a ladder witness, and the success bit reads `1`
  exactly when the Schnorr equation holds at the decodes over the kept bases combined at `n`'s
  expansion. -/
  opening : ∀ (endo : FVar C.BaseField) (sqrtF : C.BaseField → Option C.BaseField)
    (sv : SpongeVar C.BaseField)
    (bases : List (AffinePoint (FVar C.BaseField) × Option (BoolVar C.BaseField)))
    (bvW : List (C.Point × Bool)),
    List.Forall₂ (MaskedBaseReads C.E.toAffine V) bases
      (bvW.map fun b => (SWPoint.equivPoint C.E b.1, b.2)) →
    bases ≠ [] → (∀ h, bvW.getLast? = some h → h.2 = true) →
    ∀ inp : CheckBulletproofInput C.BaseField sf,
    (∀ x ∈ inp.scaled, R.WellFormed x ∧ ∀ w, R.Pre x w → R.Reg w) →
    ∀ n : Prechallenge, Reads128 V inp.xi n →
    ∀ (σ : SRS C.Point) (lrW : Vector (C.Point × C.Point) σ.k) (δW sgW : C.Point),
    List.Forall₂ (PairReads C.E.toAffine V) inp.opening.lr
      (lrW.toList.map fun q => (SWPoint.equivPoint C.E q.1, SWPoint.equivPoint C.E q.2)) →
    inp.opening.lr ≠ [] →
    OnCurveAt C.E.toAffine V inp.opening.delta (SWPoint.equivPoint C.E δW) →
    OnCurveAt C.E.toAffine V inp.opening.sg (SWPoint.equivPoint C.E sgW) →
    OnCurveAt C.E.toAffine V inp.blindingGenerator (SWPoint.equivPoint C.E σ.h) →
    C.sponge.params.roundConstants.size = Poseidon.fullRounds →
    ⦃⌜True⌝⦄ checkBulletproof ops e C.sponge.params endo gm sqrtF sv bases inp
    ⦃⇓ o _ => ⌜∃ (U : C.Point) (ns : List Prechallenge) (c₀ : Prechallenge)
      (chals : Vector C.ScalarField σ.k),
      (U = C.toGroup (o.t.val V) ∨ U = -C.toGroup (o.t.val V)) ∧
      List.Forall₂ (Reads128 V) o.challenges ns ∧ Reads128 V o.c c₀ ∧
      chals.toList = ns.map (fun m => Poseidon.FqSponge.endoExpand C.sponge.lam m.val) ∧
      (∃ w : R.wit, R.Pre inp.deferred.combinedInnerProduct w) ∧
      ((↑o.success : CVar C.BaseField).val V = 1 ↔
        schnorrAt C σ U chals (Poseidon.FqSponge.endoExpand C.sponge.lam c₀.val)
          (decode inp.deferred.combinedInnerProduct) (decode inp.deferred.b)
          (combineCommitments C (Poseidon.FqSponge.endoExpand C.sponge.lam n.val)
            ((bvW.filter (·.2)).map (·.1)).toArray)
          ⟨lrW, δW, decode inp.opening.z1, decode inp.opening.z2, sgW⟩)⌝⦄

section Side

variable {C : CommitmentCurve} {V : Valuation C.BaseField} {sf : Type}
  {ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf}

/-- A shifted claim the ladder read speaks about: well-formed for the side, and every witness
reading it in the ladder's regime (at the deployed curves: the decode is off the forbidden
band — the `scale_fast`-family premise #341 tracks). -/
def IvpSide.ClaimOk (S : IvpSide C V ops) (x : sf) : Prop :=
  S.R.WellFormed x ∧ ∀ w, S.R.Pre x w → S.R.Reg w

/-- A commitment cell list reads as a wire commitment list, pointwise through `equivPoint`. -/
def CommReads (C : CommitmentCurve) (V : Valuation C.BaseField)
    (cells : List (AffinePoint (FVar C.BaseField))) (Ps : List C.Point) : Prop :=
  List.Forall₂ (fun cell P => OnCurveAt C.E.toAffine V cell (SWPoint.equivPoint C.E P)) cells Ps

/-- The `ft_comm` read: given the claims decode to the wire's permutation scalar and `ζ` powers
(each a claim the ladder read speaks about), and the `σ₆` chunk cells and `t_comm` cells read as
the verification key's and the proof's commitments, the constructed cell crosses to `runFtComm`
(`combine(ζ^{2^k}, perm·σ₆) − (ζⁿ − 1)·combine(ζ^{2^k}, t_comm)`). -/
def FtCommReads {nc : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (ftCommCell : AffinePoint (FVar C.BaseField)) (permCell zetaMCell zetaNCell : sf)
    (sigma6Cells : Vector (AffinePoint (FVar C.BaseField)) nc)
    (tCommCells : List (AffinePoint (FVar C.BaseField))) : Prop :=
  S.decode permCell = runPScalar C σ cvk cp pub →
  S.decode zetaMCell = runZetaM C σ cvk cp pub →
  S.decode zetaNCell = runZetaN C σ cvk cp pub →
  S.ClaimOk permCell → S.ClaimOk zetaMCell → S.ClaimOk zetaNCell →
  CommReads C V sigma6Cells.toList (cvk.sigmaComm[6]).toList →
  CommReads C V tCommCells cp.tComm.toList →
  OnCurveAt C.E.toAffine V ftCommCell (SWPoint.equivPoint C.E (runFtComm C σ cvk cp pub))

/-! ## Reading helpers -/

/-- In a group killed by `n`, an integer acts as its residue's canonical representative
(restated; private in `CheckBulletproof`). -/
private theorem zsmul_eq_val_nsmul {G : Type} [AddCommGroup G] (n : ℕ) [NeZero n]
    (hn : ∀ x : G, n • x = 0) (z : ℤ) (x : G) : z • x = ((z : ZMod n).val : ℕ) • x := by
  have hv : (((z : ZMod n).val : ℕ) : ℤ) = z % n := ZMod.val_intCast z
  rw [← natCast_zsmul, hv]
  conv_lhs => rw [← Int.emod_add_mul_ediv z n]
  rw [add_zsmul, mul_zsmul, natCast_zsmul, hn, _root_.add_zero]

/-- The scalar order kills the affine group too, across `equivPoint`. -/
private theorem IvpSide.aff_nsmul (S : IvpSide C V ops) (X : C.E.toAffine.Point) :
    C.scalar • X = 0 := by
  rw [← (SWPoint.equivPoint C.E).apply_symm_apply X, ← map_nsmul, S.card_nsmul, map_zero]

/-- An integer acts on the affine group as its residue's representative in the scalar field. -/
private theorem IvpSide.zsmul_eq (S : IvpSide C V ops) (z : ℤ) (X : C.E.toAffine.Point) :
    z • X = ((z : C.ScalarField).val : ℕ) • X :=
  haveI : NeZero C.scalar := ⟨C.primeScalar.out.ne_zero⟩
  zsmul_eq_val_nsmul C.scalar S.aff_nsmul z X

/-- A scale by a claim decoding to `s` acts by `s.val`: the witness's integer decode is `s`'s
representative (`dec_cast`) and the group is killed by the scalar order. -/
private theorem IvpSide.scale_val (S : IvpSide C V ops) {x : sf} {w : S.R.wit}
    {s : C.ScalarField} (hpre : S.R.Pre x w) (hdec : S.decode x = s)
    (T : C.E.toAffine.Point) : S.R.dec w • T = s.val • T := by
  rw [S.zsmul_eq, S.dec_cast hpre, hdec]

/-- The side's scaling read with the well-formedness moved into the postcondition, so it serves
as a `mvcgen` spec before the claim's well-formedness is in hand. -/
private theorem IvpSide.scale_reads (S : IvpSide C V ops) (pt : AffinePoint (FVar C.BaseField))
    (x : sf) :
    ⦃⌜True⌝⦄ ops.scaleByShifted pt x
    ⦃⇓ r _ => ⌜S.R.WellFormed x → ∀ T : C.E.toAffine.Point, OnCurveAt C.E.toAffine V pt T →
      ∃ w, S.R.Pre x w ∧ (S.R.Reg w → OnCurveAt C.E.toAffine V r (S.R.dec w • T))⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat hwf
  exact (builder_spec_iff _ _).mp (S.R.scale pt x hwf) nv hsat

/-- The scalar-field Horner collapse of a point list, `P₀ + ξ·(P₁ + ξ·(…))` — `Σᵢ ξⁱ·Pᵢ`. -/
private def hornerVal (C : CommitmentCurve) (ξ : C.ScalarField)
    (Ps : List C.E.toAffine.Point) : C.E.toAffine.Point :=
  Ps.foldr (fun P acc => P + ξ.val • acc) 0

/-- Horner is linear in the points, across the crossing: the crossed collapse of the
`s`-scaled wire points is `s.val` times the crossed collapse. Stated on the wire's own list
shape (`map e (map (s • ·) cs)`) so the read can rewrite with it directly. -/
private theorem hornerVal_map_smul (C : CommitmentCurve) (ξ s : C.ScalarField)
    (cs : List C.Point) :
    hornerVal C ξ (List.map (SWPoint.equivPoint C.E) (List.map (fun P => s.val • P) cs))
      = s.val • hornerVal C ξ (List.map (SWPoint.equivPoint C.E) cs) := by
  induction cs with
  | nil => simp [hornerVal]
  | cons P cs ih =>
      simp only [hornerVal, List.map_cons, List.foldr_cons] at ih ⊢
      rw [map_nsmul, ih, nsmul_add]
      congr 1
      exact smul_comm _ _ _

/-- `equivPoint` carries the wire's Horner fold to `hornerVal` over the mapped points. -/
private theorem equivPoint_hornerVal (C : CommitmentCurve) (ξ : C.ScalarField)
    (cs : List C.Point) :
    (SWPoint.equivPoint C.E) (cs.foldr (fun P acc => P + ξ.val • acc) 0)
      = hornerVal C ξ (cs.map (SWPoint.equivPoint C.E)) := by
  induction cs with
  | nil => simp [hornerVal]
  | cons P cs ih =>
      simp only [hornerVal, List.map_cons, List.foldr_cons] at ih ⊢
      rw [map_add, map_nsmul, ih]

/-- `(ζ − 1)` acts as `ζ` minus the identity: the scalar-field subtraction is exact on a group
killed by the scalar order. -/
private theorem IvpSide.sub_one_val_smul (S : IvpSide C V ops) (ζ : C.ScalarField)
    (X : C.E.toAffine.Point) : (ζ - 1).val • X = ζ.val • X - X := by
  haveI : NeZero C.scalar := ⟨C.primeScalar.out.ne_zero⟩
  have h : (((ζ.val : ℤ) - 1 : ℤ) : C.ScalarField) = ζ - 1 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [← h, ← S.zsmul_eq, sub_zsmul, natCast_zsmul, one_zsmul, sub_eq_add_neg]

/-- `hornerReduce` reads as the scalar-field Horner collapse of the chunks' points: given the
`ζ^{2^k}` claim decodes to `ξ` and is a claim the ladder speaks about, and the chunks read as
`Ps`. Needs a chunk (the empty collapse is the unused origin). -/
private theorem hornerReduce_reads (S : IvpSide C V ops) (zM : sf) :
    ∀ chunks : List (AffinePoint (FVar C.BaseField)), chunks ≠ [] →
      ⦃⌜True⌝⦄ hornerReduce ops zM chunks
      ⦃⇓ r _ => ⌜∀ ξ : C.ScalarField, S.decode zM = ξ → S.ClaimOk zM →
        ∀ Ps : List C.E.toAffine.Point,
          List.Forall₂ (OnCurveAt C.E.toAffine V) chunks Ps →
          OnCurveAt C.E.toAffine V r (hornerVal C ξ Ps)⌝⦄
  | [], hne => absurd rfl hne
  | [c], _ => by
      simp only [hornerReduce]
      mvcgen
      intro ξ _ _ Ps hf
      cases hf with
      | cons hc hnil =>
        cases hnil
        simpa [hornerVal] using hc
  | c :: c' :: rest, _ => by
      simp only [hornerReduce]
      have ih := hornerReduce_reads S zM (c' :: rest) (List.cons_ne_nil _ _)
      have hsc := fun (r : AffinePoint (FVar C.BaseField)) => S.scale_reads r zM
      have hadd := fun (s : AffinePoint (FVar C.BaseField)) =>
        addFast_checkFinite_spec (V := V) C.E.toAffine ⟨rfl, rfl, rfl, S.a_zero⟩ S.two_ne
          S.two_torsion_free c s
      mvcgen -trivial [-Snarky.Kimchi.addFast_spec, ih, hsc, hadd]
      clear ih
      rename_i _ _ _ hih _ _ hsc' _ _
      intro haddpost ξ hdec hok Ps hf
      cases hf with
      | cons hc hrest =>
        have hr := hih ξ hdec hok _ hrest
        obtain ⟨w, hpre, hpt⟩ := hsc' hok.1 _ hr
        have hs := hpt (hok.2 w hpre)
        rw [S.scale_val hpre hdec] at hs
        simpa [hornerVal] using haddpost _ _ hc hs

/-- A commitment-cell read gives the chunk points, crossed, for the Horner read. -/
private theorem CommReads.forall₂ {cells : List (AffinePoint (FVar C.BaseField))}
    {Ps : List C.Point} (h : CommReads C V cells Ps) :
    List.Forall₂ (OnCurveAt C.E.toAffine V) cells (Ps.map (SWPoint.equivPoint C.E)) :=
  List.forall₂_map_right_iff.2 h

/-- Transport a curve read along a point equation. Used in place of `convert`, whose closing
`rfl` unfolds the Weierstrass group law (and with it the field inversion on the 2²⁵⁴ modulus)
and recurses. -/
private theorem OnCurveAt.congr_pt {F : Type} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} {V : Valuation F} {c : AffinePoint (FVar F)} {P Q : W.Point}
    (h : OnCurveAt W V c P) (e : P = Q) : OnCurveAt W V c Q :=
  e ▸ h

/-- **The `ft_comm` gadget reads as the wire's `runFtComm`.** On either side, on the `σ₆` chunk
cells and the `t_comm` cells, the gadget's output satisfies `FtCommReads`. Needs a chunk on each
side (the empty collapse is the unused origin). Each `scale` reads through the side's
`IpaScalarOps.Reading`, each collapse through `hornerReduce_reads`; the wire's `runFtComm` is
then the same expression, `combineCommitments` being Horner (`combineCommitments_eq_foldr`) and
`equivPoint` carrying it across. -/
theorem ftComm_reads {nc : ℕ} (S : IvpSide C V ops) (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) (permCell zetaMCell zetaNCell : sf)
    (sigma6Cells : Vector (AffinePoint (FVar C.BaseField)) nc)
    (tCommCells : List (AffinePoint (FVar C.BaseField))) (hnc : 0 < nc)
    (hne : tCommCells ≠ []) :
    ⦃⌜True⌝⦄ ftComm ops sigma6Cells.toList tCommCells permCell zetaMCell zetaNCell
    ⦃⇓ r _ => ⌜FtCommReads S σ cvk cp pub r permCell zetaMCell zetaNCell sigma6Cells
      tCommCells⌝⦄ := by
  have hσne : sigma6Cells.toList ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  simp only [ftComm]
  have hhσ := hornerReduce_reads S zetaMCell sigma6Cells.toList hσne
  have hscP := fun (r : AffinePoint (FVar C.BaseField)) => S.scale_reads r permCell
  have hht := hornerReduce_reads S zetaMCell tCommCells hne
  have hscN := fun (r : AffinePoint (FVar C.BaseField)) => S.scale_reads r zetaNCell
  have hadd := fun (a b : AffinePoint (FVar C.BaseField)) =>
    addFast_checkFinite_spec (V := V) C.E.toAffine ⟨rfl, rfl, rfl, S.a_zero⟩ S.two_ne
      S.two_torsion_free a b
  mvcgen -trivial [-Snarky.Kimchi.addFast_spec, hhσ, hscP, hht, hscN, hadd]
  clear hhσ hht
  rename_i _ _ _ hhσ' _ _ hscP' _ _ hht' _ _ hscN' _ _ hadd1 _ _
  intro hadd2
  unfold FtCommReads
  intro hperm hzM hzN hokP hokM hokN hσ ht
  -- make the wire's closed forms opaque before any algebra: `runZetaM`/`runZetaN`/`runPScalar`
  -- hide the whole fq-sponge run, and a defeq check that unfolds them sends the kernel into
  -- deep recursion. Everything below is stated over the three names.
  generalize hζM : runZetaM C σ cvk cp pub = ζM at hzM
  generalize hsP : runPScalar C σ cvk cp pub = sP at hperm
  generalize hζN : runZetaN C σ cvk cp pub = ζN at hzN
  -- the σ₆ leg: collapse, then scale by `perm`
  have hRσ := hhσ' _ hzM hokM _ hσ.forall₂
  obtain ⟨wP, hpreP, hptP⟩ := hscP' hokP.1 _ hRσ
  have hF := hptP (hokP.2 wP hpreP)
  rw [S.scale_val hpreP hperm] at hF
  -- the t_comm leg: collapse, scale by `ζⁿ`, negate
  have hRt := hht' _ hzM hokM _ ht.forall₂
  obtain ⟨wN, hpreN, hptN⟩ := hscN' hokN.1 _ hRt
  have hZ := hptN (hokN.2 wN hpreN)
  rw [S.scale_val hpreN hzN] at hZ
  have hnegZ := OnCurveAt.neg ⟨rfl, rfl⟩ hZ
  -- the two adds
  have h1 := hadd1 _ _ hF hRt
  have h2 := hadd2 _ _ h1 hnegZ
  -- the wire's `runFtComm`, crossed, is the same expression: unfold it and name its closed
  -- forms, collapse the two `combineCommitments` via `combineCommitments_eq_foldr` on their
  -- list forms (`Array.toArray_toList`, `Vector.toArray_map`), push `equivPoint` through to
  -- `hornerVal`, pull the `perm` scaling out, split `ζⁿ − 1`, and match `h2`.
  simp only [runFtComm, runFComm]
  rw [hζM, hsP, hζN]
  have hcT := combineCommitments_eq_foldr C S.card_nsmul ζM cp.tComm.toList
  rw [Array.toArray_toList] at hcT
  have hcσ := combineCommitments_eq_foldr C S.card_nsmul ζM
    ((cvk.sigmaComm[6]).toList.map (fun P => sP.val • P))
  rw [show ((cvk.sigmaComm[6]).toList.map (fun P => sP.val • P)).toArray
      = ((cvk.sigmaComm[6]).map (fun P => sP.val • P)).toArray
    from by rw [Vector.toArray_map, List.map_toArray, Vector.toList, Array.toArray_toList]] at hcσ
  rw [hcσ, hcT, map_sub, map_nsmul, equivPoint_hornerVal, equivPoint_hornerVal,
    hornerVal_map_smul, S.sub_one_val_smul]
  exact OnCurveAt.congr_pt h2 (by rw [sub_sub_eq_add_sub, sub_eq_add_neg])

end Side

/-! The gadgets are sealed after their reads: a consumer composes `ftComm_reads`, never the
body. -/
attribute [irreducible] hornerReduce ftComm

end Pickles
