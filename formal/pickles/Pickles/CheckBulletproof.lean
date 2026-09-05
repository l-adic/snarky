import Pickles.FqSpongeTranscript
import Snarky.Kimchi.Circuit.EndoMul
import Snarky.Kimchi.Circuit.VarBaseMul
import Snarky.Kimchi.Circuit.GroupMap
import Snarky.Types.Shifted
import Snarky.Kimchi.Circuit.Point
import Pickles.FrSponge

/-!
# The in-circuit IPA opening check

The port of PS `Pickles.IPA.checkBulletproof` (OCaml `check_bulletproof`,
`wrap_verifier.ml`/`step_verifier.ml`): from the sponge at `sponge_before_evaluations`,
absorb the shifted combined inner product, squeeze the `U` base's preimage and map it to
the curve, combine the commitments by `ξ`, then the opening: one scalar challenge per
`(L, R)` pair, the challenge-folded `lr_prod`, `δ` absorbed and `c` squeezed, and the
Schnorr equation `c·Q + δ = z₁·(sg + b·u) + z₂·h` at the deferred `cip` and `b`, decided
into the success bit.

## Main definitions

- `IpaScalarOps`: a side's shifted-scalar handling (PS `IpaScalarOps`), with the deployed
  `IpaScalarOps.wrap` (`scaleFast1`, one limb) and `IpaScalarOps.step` (`scaleFast2`, two
  limbs);
- `extractScalarChallenges`, `bulletReduce`, `combinePolynomials`, `ipaFinalCheck`,
  `checkBulletproof`: the gadgets, in PS's emission order (the shifted scalar's limbs
  absorbed by `absorbList`, the point select the generic `select` at `AffinePoint`).
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi CompElliptic.Fields.Pasta

variable {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]

/-- A side's shifted-scalar handling (PS `IpaScalarOps`): scaling a point by a shifted
scalar, and the limbs a shifted scalar absorbs as (OCaml `absorb_shifted`). -/
structure IpaScalarOps (F c sf : Type) where
  /-- Scale a point by the shifted scalar (PS `scaleByShifted`). -/
  scaleByShifted : AffinePoint (FVar F) → sf → CircuitM F c (AffinePoint (FVar F))
  /-- The limbs the shifted scalar absorbs as (PS `shiftedToAbsorbFields`). -/
  shiftedToAbsorbFields : sf → List (FVar F)

/-- The wrap side's operations (PS `Pickles.Wrap.OtherField.ipaScalarOps`): `scaleFast1`
at 51 chunks over the `Type1` representative, absorbed as one limb. -/
def IpaScalarOps.wrap : IpaScalarOps F c (Type1 (FVar F)) where
  scaleByShifted p t := scaleFast1 255 51 p t
  shiftedToAbsorbFields t := [t.val]

/-- The step side's operations (PS `Pickles.Step.OtherField.ipaScalarOps`): `scaleFast2`
at 51 chunks and 254 halved bits over the `Type2` split representative, absorbed as the
halved limb then the parity bit. -/
def IpaScalarOps.step : IpaScalarOps F c (Type2 (SplitField (FVar F) (BoolVar F))) where
  scaleByShifted p t := scaleFast2 255 51 254 p t.val.sDiv2 t.val.sOdd
  shiftedToAbsorbFields t := [t.val.sDiv2, (↑t.val.sOdd : CVar F)]

/-- A side's endomorphism data with the scalar field named (the `endoInv` witness needs the
group order as a numeral): the `HasEndo`, the order `q`, its primality, and `λ` in `ZMod q`. -/
structure IpaEndo (F : Type) [Field F] [DecidableEq F] where
  /-- The curve, endomorphism coefficient and eigenvalue. -/
  d : HasEndo F
  /-- The group order, as a numeral. -/
  q : ℕ
  /-- The order is prime. -/
  hq : q.Prime
  /-- The eigenvalue in the scalar field. -/
  lam : ZMod q

/-- The step side's data: Pallas over `Fp`. -/
def IpaEndo.pallas : IpaEndo Fp where
  d := HasEndo.pallas
  q := PALLAS_SCALAR_CARD
  hq := Pasta.pallas_card ▸
    (Fact.out : Nat.Prime CompElliptic.Curves.Pasta.Pallas.curve.toAffine.order)
  lam := ((Pasta.pallasLam : ℤ) : ZMod PALLAS_SCALAR_CARD)

/-- The wrap side's data: Vesta over `Fq`. -/
def IpaEndo.vesta : IpaEndo Fq where
  d := HasEndo.vesta
  q := PALLAS_BASE_CARD
  hq := Pasta.vesta_card ▸
    (Fact.out : Nat.Prime CompElliptic.Curves.Pasta.Vesta.curve.toAffine.order)
  lam := ((Pasta.vestaLam : ℤ) : ZMod PALLAS_BASE_CARD)

/-- The opening data `check_bulletproof` consumes (PS `CheckBulletproofInput`): the
polyscale challenge, the opening proof's points and shifted scalars, the deferred `cip`
and `b`, and the blinding base `h`. -/
structure CheckBulletproofInput (F sf : Type) where
  /-- The polyscale challenge `ξ`, 128 bits. -/
  xi : SizedF 128 (FVar F)
  /-- The opening's `δ`. -/
  delta : AffinePoint (FVar F)
  /-- The opening's challenge polynomial commitment `sg`. -/
  sg : AffinePoint (FVar F)
  /-- The `(L, R)` pairs, one per round. -/
  lr : List (AffinePoint (FVar F) × AffinePoint (FVar F))
  /-- The opening's `z₁`, shifted. -/
  z1 : sf
  /-- The opening's `z₂`, shifted. -/
  z2 : sf
  /-- The deferred combined inner product, shifted. -/
  combinedInnerProduct : sf
  /-- The deferred challenge-polynomial evaluation `b`, shifted. -/
  b : sf
  /-- The SRS blinding base `h`. -/
  blindingGenerator : AffinePoint (FVar F)

/-- The check's outputs (PS `IpaFinalCheckResult`, with the transcript's intermediates
named): the success bit, the round prechallenges, the `U` base's preimage `t`, the
Schnorr prechallenge `c`, and the sponge after `c`. -/
structure CheckBulletproofOutput (F : Type) where
  /-- The Schnorr equation's truth value. -/
  success : BoolVar F
  /-- The 128-bit round prechallenges, in round order. -/
  challenges : List (SizedF 128 (FVar F))
  /-- The squeezed preimage of the `U` base. -/
  t : FVar F
  /-- The 128-bit Schnorr prechallenge. -/
  c : SizedF 128 (FVar F)
  /-- The sponge after squeezing `c`. -/
  sponge : SpongeVar F

/-- The round prechallenges (PS `extractScalarChallenges`, `bullet_reduce`'s first pass):
per pair absorb `L` then `R` and squeeze a scalar challenge. -/
def extractScalarChallenges (p : Poseidon.Params F) (endo : FVar F) :
    SpongeVar F → List (AffinePoint (FVar F) × AffinePoint (FVar F)) →
    CircuitM F c (List (SizedF 128 (FVar F)) × SpongeVar F)
  | sv, [] => pure ([], sv)
  | sv, q :: qs => do
    let sv ← absorbPoint p sv q.1
    let sv ← absorbPoint p sv q.2
    let (u, sv) ← squeezePrechallenge p false endo sv
    let (us, sv) ← extractScalarChallenges p endo sv qs
    pure (u :: us, sv)

/-- The per-pair terms of `lr_prod`: `endoInv(L, u) + endo(R, u)`, in order. -/
def bulletTerms (e : IpaEndo F) :
    List ((AffinePoint (FVar F) × AffinePoint (FVar F)) × SizedF 128 (FVar F)) →
    CircuitM F c (List (AffinePoint (FVar F)))
  | [] => pure []
  | q :: qs => do
    let lScaled ← endoInv e.d.endo e.d.W e.q e.hq e.lam q.1.1 q.2
    let rScaled ← endoMul e.d.endo 32 q.1.2 q.2
    let r ← addFast .checkFinite lScaled rScaled
    let rest ← bulletTerms e qs
    pure (r.p :: rest)

/-- The running sum of points from an accumulator (OCaml `Array.reduce_exn ~f:add_fast`). -/
def sumPoints : AffinePoint (FVar F) → List (AffinePoint (FVar F)) →
    CircuitM F c (AffinePoint (FVar F))
  | acc, [] => pure acc
  | acc, q :: qs => do
    let r ← addFast .checkFinite acc q
    sumPoints r.p qs

/-- The challenge fold `lr_prod` (PS `bulletReduceCircuit`, `bullet_reduce`'s second pass):
per pair `endoInv(L, u) + endo(R, u)`, then the running sum. Empty input yields the
origin. -/
def bulletReduce (e : IpaEndo F)
    (pairs : List ((AffinePoint (FVar F) × AffinePoint (FVar F)) × SizedF 128 (FVar F))) :
    CircuitM F c (AffinePoint (FVar F)) := do
  let terms ← bulletTerms e pairs
  match terms with
  | [] => pure ⟨.const 0, .const 0⟩
  | h :: t => sumPoints h t

/-- The Horner fold of `combinePolynomials` from an accumulator over the remaining (reversed)
bases: `acc ← base + ξ·acc`, a masked base kept or skipped by its bit. -/
def hornerFold (e : IpaEndo F) (xi : SizedF 128 (FVar F)) :
    AffinePoint (FVar F) → List (AffinePoint (FVar F) × Option (BoolVar F)) →
    CircuitM F c (AffinePoint (FVar F))
  | acc, [] => pure acc
  | acc, bm :: bases => do
    let xiAcc ← endoMul e.d.endo 32 acc xi
    let r ← addFast .checkFinite bm.1 xiAcc
    let acc' ← match bm.2 with
      | none => pure r.p
      | some keep => select keep r.p acc
    hornerFold e xi acc' bases

/-- The polyscale combination of the commitment bases (PS `combinePolynomials`, OCaml
`Split_commitments.combine`): Horner from the last base, `acc ← base + ξ·acc`, a masked
base kept or skipped by its bit — skipped without consuming a power of `ξ`. Empty input
yields the origin. -/
def combinePolynomials (e : IpaEndo F) (xi : SizedF 128 (FVar F))
    (bases : List (AffinePoint (FVar F) × Option (BoolVar F))) :
    CircuitM F c (AffinePoint (FVar F)) :=
  match bases.reverse with
  | [] => pure ⟨.const 0, .const 0⟩
  | h :: t => hornerFold e xi h.1 t

/-- The opening's final check (PS `ipaFinalCheckCircuit`), given `t`, `u` and the combined
commitment: the round challenges, `lr_prod`, `Q = P + cip·u + lr_prod`, `δ` absorbed and
`c` squeezed, and the Schnorr equation decided. -/
def ipaFinalCheck {sf : Type} (ops : IpaScalarOps F c sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (endo : FVar F) (sv : SpongeVar F) (t : FVar F)
    (u combinedPolynomial : AffinePoint (FVar F)) (inp : CheckBulletproofInput F sf) :
    CircuitM F c (CheckBulletproofOutput F) := do
  let (chals, sv) ← extractScalarChallenges p endo sv inp.lr
  let lrProd ← bulletReduce e (inp.lr.zip chals)
  let cipU ← ops.scaleByShifted u inp.combinedInnerProduct
  let pPrime ← (·.p) <$> addFast .checkFinite combinedPolynomial cipU
  let q ← (·.p) <$> addFast .checkFinite pPrime lrProd
  let sv ← absorbPoint p sv inp.delta
  let (cc, sv) ← squeezePrechallenge p false endo sv
  let cQ ← endoMul e.d.endo 32 q cc
  let lhs ← (·.p) <$> addFast .checkFinite cQ inp.delta
  let bU ← ops.scaleByShifted u inp.b
  let sgPlusBU ← (·.p) <$> addFast .checkFinite inp.sg bU
  let z1Term ← ops.scaleByShifted sgPlusBU inp.z1
  let z2Term ← ops.scaleByShifted inp.blindingGenerator inp.z2
  let rhs ← (·.p) <$> addFast .checkFinite z1Term z2Term
  let xEq ← equals lhs.x rhs.x
  let yEq ← equals lhs.y rhs.y
  let success ← Snarky.and xEq yEq
  pure ⟨success, chals, t, cc, sv⟩

/-- The opening check (PS `checkBulletproof`, OCaml `check_bulletproof`): from the sponge at
`sponge_before_evaluations`, absorb the shifted `cip`, squeeze and map the `U` base,
combine the bases by `ξ` under their masks, and run the final check. -/
def checkBulletproof {sf : Type} (ops : IpaScalarOps F c sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F)
    (sv : SpongeVar F) (bases : List (AffinePoint (FVar F) × Option (BoolVar F)))
    (inp : CheckBulletproofInput F sf) : CircuitM F c (CheckBulletproofOutput F) := do
  let sv ← absorbList p sv (ops.shiftedToAbsorbFields inp.combinedInnerProduct)
  let (t, sv) ← SpongeVar.squeeze p sv
  let u ← groupMapCircuit sqrtF gm t
  let combined ← combinePolynomials e inp.xi bases
  ipaFinalCheck ops e p endo sv t u combined inp

/-! ## Soundness: the transcript -/

variable {V : Valuation F}

/-- A pair of points' coordinates, the form `Bulletproof.Ipa.ipaSqueezes` takes. -/
private def coordsPair (q : AffinePoint F × AffinePoint F) : (F × F) × (F × F) :=
  ((q.1.x, q.1.y), (q.2.x, q.2.y))

/-- A raw squeeze and a 128-bit circuit value in the `lowest_128_bits` relation:
`x = lo + 2¹²⁸·hi` with `hi < 2¹²⁸`. -/
def Low128 (V : Valuation F) (x : F) (u : SizedF 128 (FVar F)) : Prop :=
  ∃ hi : ℕ, hi < 2 ^ 128 ∧ x = u.val.val V + 2 ^ 128 * hi

open Bulletproof.Ipa in
/-- The transcript reading of the check's outputs (`checkBulletproof_spec`): with
`(t, us, c)` the wire verifier's `ipaSqueezes` from the sponge's reading over the limbs,
pairs and `δ` readings, `t` reads exactly, each round prechallenge and `c` are the low
128 bits of theirs. -/
def CheckBulletproofReads (p : Poseidon.Params F) (s₀ : Poseidon.State F) (cipLimbs : List F)
    (lrv : List (AffinePoint F × AffinePoint F)) (δv : AffinePoint F) (V : Valuation F)
    (o : CheckBulletproofOutput F) : Prop :=
  let r := ipaSqueezes p s₀ cipLimbs (lrv.map coordsPair) (δv.x, δv.y)
  o.t.val V = r.1 ∧ List.Forall₂ (Low128 V) r.2.1 o.challenges ∧ Low128 V r.2.2 o.c

open Bulletproof.Ipa in
/-- Under any valuation satisfying the emitted constraints, with the sponge reading as `s`
and the pairs as `qs`, the challenges read as the low halves of the round squeezes and
the sponge as the fold's state. -/
theorem extractScalarChallenges_spec (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (endo : FVar F) :
    ∀ (sv : SpongeVar F) (lr : List (AffinePoint (FVar F) × AffinePoint (FVar F)))
      (qs : List (AffinePoint F × AffinePoint F)),
      List.Forall₂ (CircuitType.Reads V) lr qs →
      ⦃⌜True⌝⦄ extractScalarChallenges (c := Builder V (KimchiConstraint F)) p endo sv lr
      ⦃⇓ r _ => ⌜∀ s, SpongeVar.ReadsAt V sv s →
        List.Forall₂ (Low128 V) ((qs.map coordsPair).foldl (ipaRound p) ([], s)).1 r.1 ∧
        SpongeVar.ReadsAt V r.2 ((qs.map coordsPair).foldl (ipaRound p) ([], s)).2⌝⦄
  | sv, [], [], .nil => by
    simp only [extractScalarChallenges]
    mvcgen
    intro s hs
    exact ⟨.nil, hs⟩
  | sv, q :: lr, qv :: qs, .cons hq hqs => by
    simp only [extractScalarChallenges]
    obtain ⟨hl, hr⟩ := CircuitType.reads_prod.mp hq
    obtain ⟨hlx, hly⟩ := reads_affinePoint.mp hl
    obtain ⟨hrx, hry⟩ := reads_affinePoint.mp hr
    have hL := absorbPoint_spec (V := V) p hsize sv q.1
    have hR := fun sv' => absorbPoint_spec (V := V) p hsize sv' q.2
    have hpre := fun sv' => squeezePrechallenge_spec (V := V) h2 h3 p hsize false endo sv'
    have ih := fun sv' => extractScalarChallenges_spec h2 h3 p hsize endo sv' lr qs hqs
    mvcgen [hL, hR, hpre, ih]
    rename_i _ svA _ hA svB _ hB u _ hu rest _ hrest
    intro s hs
    have s1 := hA s hs
    have s2 := hB _ s1
    obtain ⟨⟨hi, hhi, hx⟩, -, s3⟩ := hu _ s2
    obtain ⟨hall, s4⟩ := hrest _ s3
    simp only [hlx, hly, hrx, hry] at hx s3 hall s4
    simp only [List.map_cons, List.foldl_cons, ipaRound, coordsPair, List.nil_append]
    rw [ipaRound_foldl]
    exact ⟨List.Forall₂.cons ⟨hi, hhi, hx⟩ hall, s4⟩

open Bulletproof.Ipa in
/-- Under any valuation satisfying the emitted constraints, with the sponge reading as `s₀`,
the pairs as `lrv` and `δ` as `δv`, the outputs satisfy `CheckBulletproofReads` at the
limbs' readings: the transcript half of `check_bulletproof`, against the wire verifier's
`ipaSqueezes`. -/
theorem checkBulletproof_spec (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {sf : Type}
    (ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F) (sv : SpongeVar F)
    (s₀ : Poseidon.State F) (hs : SpongeVar.ReadsAt V sv s₀)
    (bases : List (AffinePoint (FVar F) × Option (BoolVar F))) (inp : CheckBulletproofInput F sf)
    (lrv : List (AffinePoint F × AffinePoint F))
    (hlr : List.Forall₂ (CircuitType.Reads V) inp.lr lrv)
    (δv : AffinePoint F) (hδ : CircuitType.Reads V inp.delta δv) :
    ⦃⌜True⌝⦄ checkBulletproof ops e p endo gm sqrtF sv bases inp
    ⦃⇓ o _ => ⌜CheckBulletproofReads p s₀
      ((ops.shiftedToAbsorbFields inp.combinedInnerProduct).map (·.val V)) lrv δv V o⌝⦄ := by
  simp only [checkBulletproof, ipaFinalCheck]
  obtain ⟨hδx, hδy⟩ := reads_affinePoint.mp hδ
  have hlimbs := absorbList_spec (V := V) p hsize sv
    (ops.shiftedToAbsorbFields inp.combinedInnerProduct)
  have hsq := fun sv' => SpongeVar.squeeze_spec (V := V) p hsize sv'
  have hgm := fun t => builder_spec_true (groupMapCircuit (c := Builder V (KimchiConstraint F))
    sqrtF gm t)
  have hcomb := fun xi bs => builder_spec_true
    (combinePolynomials (c := Builder V (KimchiConstraint F)) e xi bs)
  have hext := fun sv' =>
    extractScalarChallenges_spec (V := V) h2 h3 p hsize endo sv' inp.lr lrv hlr
  have hbr := fun ps => builder_spec_true (bulletReduce (c := Builder V (KimchiConstraint F)) e ps)
  have hsc := fun u x => builder_spec_true (ops.scaleByShifted u x)
  have hadd := fun f a b => builder_spec_true (addFast (c := Builder V (KimchiConstraint F)) f a b)
  have hem := fun g x => builder_spec_true
    (endoMul (c := Builder V (KimchiConstraint F)) e.d.endo 32 g x)
  have hδs := fun sv' => absorbPoint_spec (V := V) p hsize sv' inp.delta
  have hpre := fun sv' => squeezePrechallenge_spec (V := V) h2 h3 p hsize false endo sv'
  have heq := fun a b => builder_spec_true (equals (c := Builder V (KimchiConstraint F)) a b)
  have hand := fun a b => builder_spec_true (Snarky.and (c := Builder V (KimchiConstraint F)) a b)
  mvcgen [hlimbs, hsq, hgm, hcomb, hext, hbr, hsc, hadd, hem, hδs, hpre, heq, hand]
  case vc2.W => exact e.d.W
  case vc3.ha => exact e.d.short
  case vc5.W => exact e.d.W
  case vc6.ha => exact e.d.short
  case vc8.W => exact e.d.W
  case vc9.ha => exact e.d.short
  case vc11.W => exact e.d.W
  case vc12.ha => exact e.d.short
  case vc14.W => exact e.d.W
  case vc15.ha => exact e.d.short
  rename_i _ svL _ hL sqT _ hT u _ comb _ ext _ hext lrProd _ cipU _ pP _ _ q _ _ svD _ hD cP _ hC
    cQ _ lhs _ _ bU _ sgBU _ _ z1T _ z2T _ rhs _ xEq _ _ yEq _ _ succ _ _ _
  have s1 := hL s₀ hs
  obtain ⟨htv, s2⟩ := hT _ s1
  obtain ⟨hchals, s3⟩ := hext _ s2
  have s4 := hD _ s3
  obtain ⟨⟨hi, hhi, hc⟩, -, -⟩ := hC _ s4
  simp only [hδx, hδy] at hc
  unfold CheckBulletproofReads ipaSqueezes
  exact ⟨htv, hchals, hi, hhi, hc⟩


/-! ## Soundness: the algebra

The group-side readings, over Mathlib's `W.Point` where the gadget specs are stated:
`combinePolynomials` reads as the masked Horner fold `hornerCombine`, `bulletReduce` as the
challenge-folded sum `lrSum`. The scalars are the gadgets' own: `endoExpandZ` of the
128-bit prechallenges, its inverse in `ZMod W.order` for the `L` terms. -/

open Snarky.Kimchi.EndoMul Snarky.Kimchi.VarBaseMul
open Kimchi.Gate.EndoScalar (endoExpandZ)

section Model

variable {W : WeierstrassCurve.Affine F}

/-- The masked Horner step over the group: `base + ξ·acc` when kept, `acc` otherwise. -/
def hornerStep (ξ : ℤ) (acc : W.Point) (bm : W.Point × Bool) : W.Point :=
  if bm.2 then bm.1 + ξ • acc else acc

/-- `combinePolynomials`' value: Horner from the last base — its own flag unread, as the
circuit's — over the reversed list; the origin on no bases. -/
def hornerCombine (ξ : ℤ) (bv : List (W.Point × Bool)) : W.Point :=
  match bv.reverse with
  | [] => 0
  | h :: t => t.foldl (hornerStep ξ) h.1

/-- One `lr_prod` term: `u⁻¹·L + u·R` at the expanded challenge `u = endoExpandZ lam n`, the
inverse taken in `ZMod W.order`. -/
noncomputable def lrTerm (lam : ℤ) (q : W.Point × W.Point) (n : ℕ) : W.Point :=
  ((((endoExpandZ lam n : ℤ) : ZMod W.order)⁻¹).val : ℕ) • q.1 + endoExpandZ lam n • q.2

/-- `bulletReduce`'s value: the running sum of the terms; the origin on no pairs. -/
def lrSum (terms : List W.Point) : W.Point :=
  match terms with
  | [] => 0
  | h :: t => t.foldl (· + ·) h

end Model

/-- A masked base reads as a point and a bit: the point on the curve, the mask bit reading as
the bit — or no mask, and the bit `true`. -/
def MaskedBaseReads (W : WeierstrassCurve.Affine F) (V : Valuation F)
    (bm : AffinePoint (FVar F) × Option (BoolVar F)) (v : W.Point × Bool) : Prop :=
  OnCurveAt W V bm.1 v.1 ∧
    match bm.2 with
    | none => v.2 = true
    | some keep => (↑keep : CVar F).val V = bit v.2

/-- Under any valuation satisfying the emitted constraints, with the bases reading as `bv`,
the Horner fold from an accumulator reading as `accv` reads as the model fold. `n` is the
challenge's reading, pinned to the gadgets' own by `hchar`. -/
private theorem hornerFold_spec (e : IpaEndo F) (xi : SizedF 128 (FVar F)) (n : ℕ)
    (hn : n < 2 ^ 128) (hxi : xi.val.val V = n)
    (hchar : ∀ a b : ℕ, a < 2 ^ 128 → b < 2 ^ 128 → (a : F) = b → a = b) :
    ∀ (acc : AffinePoint (FVar F)) (bases : List (AffinePoint (FVar F) × Option (BoolVar F)))
      (bv : List (e.d.W.Point × Bool)), List.Forall₂ (MaskedBaseReads e.d.W V) bases bv →
      ⦃⌜True⌝⦄ hornerFold (c := Builder V (KimchiConstraint F)) e xi acc bases
      ⦃⇓ r _ => ⌜∀ accv : e.d.W.Point, OnCurveAt e.d.W V acc accv →
        OnCurveAt e.d.W V r (bv.foldl (hornerStep (endoExpandZ e.d.lam n)) accv)⌝⦄
  | acc, [], [], .nil => by
    simp only [hornerFold, List.foldl_nil]
    mvcgen
    exact fun _ h => h
  | acc, (b, mask) :: bases, (bvp, bb) :: bv, .cons hbm hrest => by
    obtain ⟨hpt, hmask⟩ := hbm
    simp only [hornerFold, List.foldl_cons]
    have hem := endoMul_spec (V := V) e.d acc xi
    have hadd := fun q => addFast_checkFinite_spec (V := V) e.d.W e.d.short e.d.two_ne
      e.d.two_torsion_free b q
    have ih := fun acc' => hornerFold_spec e xi n hn hxi hchar acc' bases bv hrest
    cases mask with
    | none =>
      simp only at hmask
      subst hmask
      mvcgen [-Snarky.Kimchi.addFast_spec, hem, hadd, ih]
      rename_i _ xiAcc _ hxa r _ hr rr _
      intro hrest' accv hacc
      obtain ⟨n', hn', hxi', hxa'⟩ := hxa accv hacc
      obtain rfl : n' = n := hchar n' n hn' hn (hxi'.symm.trans hxi)
      exact hrest' _ (by simpa [hornerStep] using hr bvp _ hpt hxa')
    | some keep =>
      simp only at hmask
      have hsel := fun r => select_affinePoint_spec (V := V) (c := KimchiConstraint F) keep r acc
      mvcgen [-Snarky.Kimchi.addFast_spec, hem, hadd, hsel, ih]
      rename_i _ xiAcc _ hxa r _ hr sel _ hsel' rr _
      intro hrest' accv hacc
      obtain ⟨n', hn', hxi', hxa'⟩ := hxa accv hacc
      obtain rfl : n' = n := hchar n' n hn' hn (hxi'.symm.trans hxi)
      have hs := hsel' bb hmask _ _ (hr bvp _ hpt hxa') hacc
      refine hrest' _ ?_
      cases bb <;> simpa [hornerStep] using hs


/-- Under any valuation satisfying the emitted constraints, with the bases reading as `bv`
(non-empty), the combination reads as `hornerCombine` at the expanded challenge. -/
theorem combinePolynomials_spec (e : IpaEndo F) (xi : SizedF 128 (FVar F)) (n : ℕ)
    (hn : n < 2 ^ 128) (hxi : xi.val.val V = n)
    (hchar : ∀ a b : ℕ, a < 2 ^ 128 → b < 2 ^ 128 → (a : F) = b → a = b)
    (bases : List (AffinePoint (FVar F) × Option (BoolVar F))) (bv : List (e.d.W.Point × Bool))
    (hb : List.Forall₂ (MaskedBaseReads e.d.W V) bases bv) (hne : bases ≠ []) :
    ⦃⌜True⌝⦄ combinePolynomials (c := Builder V (KimchiConstraint F)) e xi bases
    ⦃⇓ r _ => ⌜OnCurveAt e.d.W V r (hornerCombine (endoExpandZ e.d.lam n) bv)⌝⦄ := by
  have hrev := List.forall₂_reverse_iff.mpr hb
  simp only [combinePolynomials, hornerCombine]
  rcases hbr : bases.reverse with _ | ⟨h, t⟩
  · exact absurd (List.reverse_eq_nil_iff.mp hbr) hne
  · rw [hbr] at hrev
    rcases hvr : bv.reverse with _ | ⟨hv, tv⟩
    · rw [hvr] at hrev
      exact absurd hrev (by simp)
    · rw [hvr] at hrev
      obtain ⟨⟨hhpt, -⟩, htail⟩ := List.forall₂_cons.mp hrev
      have hf := hornerFold_spec (V := V) e xi n hn hxi hchar h.1 t tv htail
      exact builder_spec_imp _ _ _ hf fun r hr => hr _ hhpt

/-- A pair reads as two curve points. -/
def PairReads (W : WeierstrassCurve.Affine F) (V : Valuation F)
    (q : AffinePoint (FVar F) × AffinePoint (FVar F)) (v : W.Point × W.Point) : Prop :=
  OnCurveAt W V q.1 v.1 ∧ OnCurveAt W V q.2 v.2

/-- A 128-bit circuit value reads as the natural `m`. -/
def Reads128 (V : Valuation F) (u : SizedF 128 (FVar F)) (m : ℕ) : Prop :=
  m < 2 ^ 128 ∧ u.val.val V = (m : F)

/-- Under any valuation satisfying the emitted constraints, with the pairs reading as `pv`,
the terms read as `lrTerm` at the readings, the challenges reading as some `ns`. -/
private theorem bulletTerms_spec (e : IpaEndo F)
    (hchar : ∀ a b : ℕ, a < 2 ^ 128 → b < 2 ^ 128 → (a : F) = b → a = b) :
    ∀ (pairs : List ((AffinePoint (FVar F) × AffinePoint (FVar F)) × SizedF 128 (FVar F)))
      (pv : List (e.d.W.Point × e.d.W.Point)),
      List.Forall₂ (fun q v => PairReads e.d.W V q.1 v) pairs pv →
      ⦃⌜True⌝⦄ bulletTerms (c := Builder V (KimchiConstraint F)) e pairs
      ⦃⇓ r _ => ⌜∃ ns : List ℕ, List.Forall₂ (fun q m => Reads128 V q.2 m) pairs ns ∧
        List.Forall₂ (OnCurveAt e.d.W V) r (List.zipWith (lrTerm e.d.lam) pv ns)⌝⦄
  | [], [], .nil => by
    simp only [bulletTerms]
    mvcgen
    exact ⟨[], .nil, .nil⟩
  | q :: pairs, v :: pv, .cons ⟨hL, hR⟩ hpv => by
    simp only [bulletTerms]
    have hinv := endoInv_spec (V := V) e.d e.q e.hq e.lam q.1.1 q.2
    have hem := endoMul_spec (V := V) e.d q.1.2 q.2
    have hadd := fun a b => addFast_checkFinite_spec (V := V) e.d.W e.d.short e.d.two_ne
      e.d.two_torsion_free a b
    have ih := bulletTerms_spec e hchar pairs pv hpv
    mvcgen [-Snarky.Kimchi.addFast_spec, hinv, hem, hadd, ih]
    rename_i _ lS _ hinv' rS _ hem' r _ hr rest _ hrest
    obtain ⟨n', hn', hq', R, hRs, -, -, hRform⟩ := hinv' v.1 hL
    obtain ⟨n'', hn'', hq'', hRr⟩ := hem' v.2 hR
    obtain rfl : n' = n'' := hchar n' n'' hn' hn'' (hq'.symm.trans hq'')
    obtain ⟨ns, hns, hterms⟩ := hrest
    refine ⟨n' :: ns, .cons ⟨hn', hq'⟩ hns, List.Forall₂.cons ?_ hterms⟩
    have hadd' := hr R _ hRs hRr
    rw [hRform] at hadd'
    unfold lrTerm
    exact hadd'

omit [ToNat F] in
/-- Under any valuation satisfying the emitted constraints, the running sum from an
accumulator reads as the fold of the readings. -/
private theorem sumPoints_spec (e : IpaEndo F) :
    ∀ (acc : AffinePoint (FVar F)) (qs : List (AffinePoint (FVar F))),
      ⦃⌜True⌝⦄ sumPoints (c := Builder V (KimchiConstraint F)) acc qs
      ⦃⇓ r _ => ⌜∀ qv : List e.d.W.Point, List.Forall₂ (OnCurveAt e.d.W V) qs qv →
        ∀ accv : e.d.W.Point, OnCurveAt e.d.W V acc accv →
          OnCurveAt e.d.W V r (qv.foldl (· + ·) accv)⌝⦄
  | acc, [] => by
    simp only [sumPoints]
    mvcgen
    intro qv hqv accv hacc
    cases hqv
    exact hacc
  | acc, q :: qs => by
    simp only [sumPoints]
    have hadd := addFast_checkFinite_spec (V := V) e.d.W e.d.short e.d.two_ne
      e.d.two_torsion_free acc q
    have ih := fun acc' => sumPoints_spec e acc' qs
    mvcgen [-Snarky.Kimchi.addFast_spec, hadd, ih]
    rename_i _ r _ hr rr _
    intro hrest' qv hqv accv hacc
    rcases hqv with _ | ⟨hq, hqs⟩
    exact hrest' _ hqs _ (hr accv _ hacc hq)

/-- Under any valuation satisfying the emitted constraints, with the pairs (non-empty)
reading as `pv` and their challenges as `ns`, `lr_prod` reads as `lrSum` of the terms. -/
theorem bulletReduce_spec (e : IpaEndo F)
    (hchar : ∀ a b : ℕ, a < 2 ^ 128 → b < 2 ^ 128 → (a : F) = b → a = b)
    (pairs : List ((AffinePoint (FVar F) × AffinePoint (FVar F)) × SizedF 128 (FVar F)))
    (pv : List (e.d.W.Point × e.d.W.Point))
    (hp : List.Forall₂ (fun q v => PairReads e.d.W V q.1 v) pairs pv) (hne : pairs ≠ []) :
    ⦃⌜True⌝⦄ bulletReduce (c := Builder V (KimchiConstraint F)) e pairs
    ⦃⇓ r _ => ⌜∃ ns : List ℕ, List.Forall₂ (fun q m => Reads128 V q.2 m) pairs ns ∧
      OnCurveAt e.d.W V r (lrSum (List.zipWith (lrTerm e.d.lam) pv ns))⌝⦄ := by
  simp only [bulletReduce]
  have ht := bulletTerms_spec (V := V) e hchar pairs pv hp
  have hs := fun acc qs => sumPoints_spec (V := V) e acc qs
  mvcgen [ht, hs]
  · rename_i terms _ _ hterms
    obtain ⟨ns, hns, hterms⟩ := hterms
    rcases pairs with _ | ⟨q, pairs⟩
    · exact absurd rfl hne
    · rcases hp with _ | ⟨_, _⟩
      rcases hns with _ | ⟨_, _⟩
      exact absurd hterms (by simp)
  · rename_i _ _ h t _ _ hterms r _
    intro hrest
    obtain ⟨ns, hns, hterms⟩ := hterms
    refine ⟨ns, hns, ?_⟩
    rcases hz : List.zipWith (lrTerm e.d.lam) pv ns with _ | ⟨w, ws⟩
    · rw [hz] at hterms
      exact absurd hterms (by simp)
    · rw [hz] at hterms
      rcases hterms with _ | ⟨hw, hws⟩
      simpa [lrSum] using hrest ws hws w hw


/-- The Schnorr equation over the gadgets' group, at readings: `Q = P + cip·u + lrProd` and
`c·Q + δ = z₁·(sg + b·u) + z₂·h`, the scalars integers (`endoExpandZ` of the challenges, the
shifted scalars' decodes). -/
def SchnorrPoint {W : WeierstrassCurve.Affine F} (lam : ℤ) (c : ℕ) (u P lrProd δ sg h : W.Point)
    (cip b z₁ z₂ : ℤ) : Prop :=
  endoExpandZ lam c • (P + cip • u + lrProd) + δ = z₁ • (sg + b • u) + z₂ • h

/-- The extraction returns one challenge per pair. -/
private theorem extractScalarChallenges_length (p : Poseidon.Params F) (endo : FVar F) :
    ∀ (sv : SpongeVar F) (lr : List (AffinePoint (FVar F) × AffinePoint (FVar F))),
      ⦃⌜True⌝⦄ extractScalarChallenges (c := Builder V (KimchiConstraint F)) p endo sv lr
      ⦃⇓ r _ => ⌜r.1.length = lr.length⌝⦄
  | sv, [] => by
    simp only [extractScalarChallenges]
    mvcgen
  | sv, q :: lr => by
    simp only [extractScalarChallenges]
    have hL := fun sv' P => builder_spec_true
      (absorbPoint (c := Builder V (KimchiConstraint F)) p sv' P)
    have hpre := fun sv' => builder_spec_true
      (squeezePrechallenge (c := Builder V (KimchiConstraint F)) p false endo sv')
    have ih := fun sv' => extractScalarChallenges_length p endo sv' lr
    mvcgen [hL, hpre, ih]
    rename_i _ _ _ _ _ _ _ _ _ h
    simp [h]

omit [DecidableEq F] [ToNat F] in
/-- Pairing a list with another of the same length keeps a relation on the first. -/
private theorem forall₂_zip_left {α β γ : Type} {R : α → γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List γ} (l : List β), List.Forall₂ R l₁ l₂ → l.length = l₁.length →
      List.Forall₂ (fun q v => R q.1 v) (l₁.zip l) l₂
  | [], [], _, .nil, _ => .nil
  | _ :: _, _ :: _, [], .cons _ _, h => absurd h (by simp)
  | _ :: _, _ :: _, _ :: l, .cons hq hs, h =>
    .cons hq (forall₂_zip_left l hs (by simpa using h))

omit [DecidableEq F] [ToNat F] in
/-- A relation on the second components of a zip, at equal lengths, is one on the list. -/
private theorem forall₂_zip_right {α β γ : Type} {R : β → γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {ns : List γ}, l₂.length = l₁.length →
      List.Forall₂ (fun q m => R q.2 m) (l₁.zip l₂) ns → List.Forall₂ R l₂ ns
  | [], [], _, _, h => by cases h; exact .nil
  | _ :: _, _ :: l₂, _ :: _, hl, .cons hq hs => .cons hq (forall₂_zip_right (by simpa using hl) hs)
  | [], _ :: _, _, hl, _ => absurd hl (by simp)
  | _ :: _, [], _, hl, _ => absurd hl (by simp)

/-- `bulletReduce_spec` with the readings carried into the postcondition. -/
private theorem bulletReduce_spec' (e : IpaEndo F)
    (hchar : ∀ a b : ℕ, a < 2 ^ 128 → b < 2 ^ 128 → (a : F) = b → a = b)
    (pairs : List ((AffinePoint (FVar F) × AffinePoint (FVar F)) × SizedF 128 (FVar F))) :
    ⦃⌜True⌝⦄ bulletReduce (c := Builder V (KimchiConstraint F)) e pairs
    ⦃⇓ r _ => ⌜∀ pv : List (e.d.W.Point × e.d.W.Point),
      List.Forall₂ (fun q v => PairReads e.d.W V q.1 v) pairs pv → pairs ≠ [] →
      ∃ ns : List ℕ, List.Forall₂ (fun q m => Reads128 V q.2 m) pairs ns ∧
        OnCurveAt e.d.W V r (lrSum (List.zipWith (lrTerm e.d.lam) pv ns))⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat pv hp hne
  exact (builder_spec_iff _ _).mp (bulletReduce_spec e hchar pairs pv hp hne) nv hsat

/-- Under any valuation satisfying the emitted constraints, with `u`, the combined
commitment, the pairs, `δ`, `sg` and `h` reading as points, and the side's scaling reading as
`dec` (`hscale`), the challenges read as some `ns` and `c` as some `c₀`, and the success bit
reads `1` exactly when `SchnorrPoint` holds at those readings. -/
theorem ipaFinalCheck_spec {sf : Type} (ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf)
    (e : IpaEndo F) (p : Poseidon.Params F) (endo : FVar F)
    (hchar : ∀ a b : ℕ, a < 2 ^ 128 → b < 2 ^ 128 → (a : F) = b → a = b)
    (dec : sf → ℤ)
    (hscale : ∀ (pt : AffinePoint (FVar F)) (x : sf),
      ⦃⌜True⌝⦄ ops.scaleByShifted pt x
      ⦃⇓ r _ => ⌜∀ T : e.d.W.Point, OnCurveAt e.d.W V pt T → OnCurveAt e.d.W V r (dec x • T)⌝⦄)
    (sv : SpongeVar F) (t : FVar F) (u combined : AffinePoint (FVar F))
    (inp : CheckBulletproofInput F sf) (δv sgv hv : e.d.W.Point)
    (lrv : List (e.d.W.Point × e.d.W.Point))
    (hlr : List.Forall₂ (PairReads e.d.W V) inp.lr lrv) (hlrne : inp.lr ≠ [])
    (hδ : OnCurveAt e.d.W V inp.delta δv) (hsg : OnCurveAt e.d.W V inp.sg sgv)
    (hh : OnCurveAt e.d.W V inp.blindingGenerator hv) :
    ⦃⌜True⌝⦄ ipaFinalCheck ops e p endo sv t u combined inp
    ⦃⇓ o _ => ⌜∀ uv Pv : e.d.W.Point, OnCurveAt e.d.W V u uv → OnCurveAt e.d.W V combined Pv →
      o.t = t ∧ ∃ (ns : List ℕ) (c₀ : ℕ), List.Forall₂ (Reads128 V) o.challenges ns ∧
      Reads128 V o.c c₀ ∧
      ((↑o.success : CVar F).val V = 1 ↔
        SchnorrPoint e.d.lam c₀ uv Pv (lrSum (List.zipWith (lrTerm e.d.lam) lrv ns)) δv sgv hv
          (dec inp.combinedInnerProduct) (dec inp.b) (dec inp.z1) (dec inp.z2))⌝⦄ := by
  simp only [ipaFinalCheck]
  have hext := fun sv' => extractScalarChallenges_length (V := V) p endo sv' inp.lr
  have hbr := fun pairs => bulletReduce_spec' (V := V) e hchar pairs
  have hadd := fun a b => addFast_checkFinite_spec (V := V) e.d.W e.d.short e.d.two_ne
    e.d.two_torsion_free a b
  have hδs := fun sv' => builder_spec_true
    (absorbPoint (c := Builder V (KimchiConstraint F)) p sv' inp.delta)
  have hpre := fun sv' => builder_spec_true
    (squeezePrechallenge (c := Builder V (KimchiConstraint F)) p false endo sv')
  have hem := fun g x => endoMul_spec (V := V) e.d g x
  mvcgen -trivial [-Snarky.Kimchi.addFast_spec, hext, hbr, hscale, hadd, hδs, hpre, hem]
  rename_i _ ext _ hlen lrProd _ hbr' cipU _ hcip pP _ hpP q _ hq svD _ cP _ cQ _ hcQ lhs _ hlhs
    bU _ hbU sgBU _ hsgBU z1T _ hz1 z2T _ hz2 rhs _ hrhs xEq _ hx yEq _ hy succ _ hand
  intro uv Pv hu hP
  have hzne : inp.lr.zip ext.1 ≠ [] := fun h => by
    rcases List.zip_eq_nil_iff.mp h with h | h
    · exact hlrne h
    · exact hlrne (List.length_eq_zero_iff.mp (by rw [← hlen, h]; rfl))
  obtain ⟨ns, hns, hlr'⟩ := hbr' lrv (forall₂_zip_left ext.1 hlr hlen) hzne
  have hcipU := hcip uv hu
  have hpP' := hpP _ _ hP hcipU
  have hq' := hq _ _ hpP' hlr'
  obtain ⟨c₀, hc₀, hcv, hcQ'⟩ := hcQ _ hq'
  have hlhs' := hlhs _ _ hcQ' hδ
  have hbU' := hbU uv hu
  have hsgBU' := hsgBU _ _ hsg hbU'
  have hz1' := hz1 _ hsgBU'
  have hz2' := hz2 _ hh
  have hrhs' := hrhs _ _ hz1' hz2'
  have hxb : (↑xEq : CVar F).val V = bit (decide (lhs.p.x.val V = rhs.p.x.val V)) := by
    rw [hx]; simp only [bit, decide_eq_true_eq]
  have hyb : (↑yEq : CVar F).val V = bit (decide (lhs.p.y.val V = rhs.p.y.val V)) := by
    rw [hy]; simp only [bit, decide_eq_true_eq]
  have hsucc := hand _ _ hxb hyb
  refine ⟨trivial, ns, c₀, forall₂_zip_right hlen hns, ⟨hc₀, hcv⟩, ?_⟩
  unfold SchnorrPoint
  constructor
  · intro hs1
    rw [hs1] at hsucc
    have hboth : (decide (lhs.p.x.val V = rhs.p.x.val V) &&
        decide (lhs.p.y.val V = rhs.p.y.val V)) = true := by
      by_contra hne
      rw [Bool.not_eq_true] at hne
      rw [hne] at hsucc
      exact one_ne_zero (by rw [hsucc]; simp [bit])
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hboth
    exact OnCurveAt.eq hlhs' hrhs' hboth.1 hboth.2
  · intro hS
    rw [hS] at hlhs'
    obtain ⟨hxe, hye⟩ := Kimchi.Gate.AddComplete.IsPoint.coords_eq hlhs' hrhs'
    simp only [hxe, hye, decide_true, Bool.and_self] at hsucc
    simpa [bit] using hsucc


/-- The algebra half of `check_bulletproof`. Under any valuation satisfying the emitted
constraints, with the bases reading as `bv` (non-empty, `ξ` reading as `n`), the pairs, `δ`,
`sg` and `h` as points, the side's scaling reading as `dec` (`hscale`) and the map-to-curve
as `umap` (`hgm`): the challenges read as some `ns`, `c` as some `c₀`, and the success bit
reads `1` exactly when the Schnorr equation holds at the readings — `u = umap t`, the combined
commitment `hornerCombine`, `lr_prod` the `lrSum` of the terms. -/
theorem checkBulletproof_spec_success {sf : Type}
    (ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds) (endo : FVar F)
    (gm : GroupMapParams F) (sqrtF : F → Option F)
    (hchar : ∀ a b : ℕ, a < 2 ^ 128 → b < 2 ^ 128 → (a : F) = b → a = b)
    (dec : sf → ℤ)
    (hscale : ∀ (pt : AffinePoint (FVar F)) (x : sf),
      ⦃⌜True⌝⦄ ops.scaleByShifted pt x
      ⦃⇓ r _ => ⌜∀ T : e.d.W.Point, OnCurveAt e.d.W V pt T → OnCurveAt e.d.W V r (dec x • T)⌝⦄)
    (umap : F → e.d.W.Point)
    (hgm : ∀ t : FVar F, ⦃⌜True⌝⦄ groupMapCircuit (c := Builder V (KimchiConstraint F)) sqrtF gm t
      ⦃⇓ r _ => ⌜OnCurveAt e.d.W V r (umap (t.val V))⌝⦄)
    (sv : SpongeVar F) (bases : List (AffinePoint (FVar F) × Option (BoolVar F)))
    (bv : List (e.d.W.Point × Bool)) (hb : List.Forall₂ (MaskedBaseReads e.d.W V) bases bv)
    (hbne : bases ≠ []) (inp : CheckBulletproofInput F sf) (n : ℕ) (hn : n < 2 ^ 128)
    (hxi : inp.xi.val.val V = n) (δv sgv hv : e.d.W.Point)
    (lrv : List (e.d.W.Point × e.d.W.Point))
    (hlr : List.Forall₂ (PairReads e.d.W V) inp.lr lrv) (hlrne : inp.lr ≠ [])
    (hδ : OnCurveAt e.d.W V inp.delta δv) (hsg : OnCurveAt e.d.W V inp.sg sgv)
    (hh : OnCurveAt e.d.W V inp.blindingGenerator hv) :
    ⦃⌜True⌝⦄ checkBulletproof ops e p endo gm sqrtF sv bases inp
    ⦃⇓ o _ => ⌜∃ (ns : List ℕ) (c₀ : ℕ), List.Forall₂ (Reads128 V) o.challenges ns ∧
      Reads128 V o.c c₀ ∧
      ((↑o.success : CVar F).val V = 1 ↔
        SchnorrPoint e.d.lam c₀ (umap (o.t.val V)) (hornerCombine (endoExpandZ e.d.lam n) bv)
          (lrSum (List.zipWith (lrTerm e.d.lam) lrv ns)) δv sgv hv
          (dec inp.combinedInnerProduct) (dec inp.b) (dec inp.z1) (dec inp.z2))⌝⦄ := by
  simp only [checkBulletproof]
  have habs := fun sv' limbs => builder_spec_true
    (absorbList (c := Builder V (KimchiConstraint F)) p sv' limbs)
  have hsq := fun sv' => builder_spec_true
    (SpongeVar.squeeze (c := Builder V (KimchiConstraint F)) p sv')
  have hcomb := combinePolynomials_spec (V := V) e inp.xi n hn hxi hchar bases bv hb hbne
  have hfin := fun sv' t u comb => ipaFinalCheck_spec (V := V) ops e p endo hchar dec hscale sv' t
    u comb inp δv sgv hv lrv hlr hlrne hδ hsg hh
  mvcgen -trivial [habs, hsq, hgm, hcomb, hfin]
  case vc1.hsize => exact hsize
  rename_i _ _ _ tv _ _ u _ hu comb _ hP o _
  intro ho
  obtain ⟨ht, hrest⟩ := ho _ _ hu hP
  rw [ht]
  exact hrest

/-! ## The wire reading -/

open Kimchi.Verifier Bulletproof.Ipa in
/-- `CheckBulletproofReads` at a deployed field, against the wire verifier: with `(t, us, c)`
the verifier's `ipaPrechallenges`, `t` reads exactly, and each round prechallenge and `c`,
once identified with a 128-bit value, is its counterpart up to `PrechallengeAlias`
(`transcriptFrom_eq_ipaPrechallenges` carries these to `transcriptFrom`'s `U` base, round
challenges and Schnorr challenge). -/
def CheckBulletproofReadsWire {p : ℕ} [Fact p.Prime] (params : Poseidon.Params (ZMod p))
    (s₀ : Poseidon.State (ZMod p)) (cipLimbs : List (ZMod p))
    (lrv : List (AffinePoint (ZMod p) × AffinePoint (ZMod p))) (δv : AffinePoint (ZMod p))
    (V : Valuation (ZMod p)) (o : CheckBulletproofOutput (ZMod p)) : Prop :=
  let r := ipaPrechallenges params s₀ cipLimbs (lrv.map coordsPair) (δv.x, δv.y)
  o.t.val V = r.1 ∧
  List.Forall₂ (fun (pre : ℕ) (u : SizedF 128 (FVar (ZMod p))) =>
    ∀ u₀ : ℕ, u₀ < 2 ^ 128 → u.val.val V = u₀ → PrechallengeAlias p pre u₀) r.2.1 o.challenges ∧
  (∀ c₀ : ℕ, c₀ < 2 ^ 128 → o.c.val.val V = c₀ → PrechallengeAlias p r.2.2 c₀)

open Kimchi.Verifier Bulletproof.Ipa in
/-- At a prime field of more than 254 bits, the exact reading is the wire reading
(`low128_of_decomp`). -/
theorem CheckBulletproofReads.wire {p : ℕ} [Fact p.Prime] (hp : 2 ^ 254 < p)
    {params : Poseidon.Params (ZMod p)} {s₀ : Poseidon.State (ZMod p)} {cipLimbs : List (ZMod p)}
    {lrv : List (AffinePoint (ZMod p) × AffinePoint (ZMod p))} {δv : AffinePoint (ZMod p)}
    {V : Valuation (ZMod p)} {o : CheckBulletproofOutput (ZMod p)}
    (h : CheckBulletproofReads params s₀ cipLimbs lrv δv V o) :
    CheckBulletproofReadsWire params s₀ cipLimbs lrv δv V o := by
  obtain ⟨ht, hus, ⟨hi, hhi, hc⟩⟩ := h
  refine ⟨ht, ?_, fun c₀ hc₀ hcv => low128_of_decomp hp _ c₀ hi hc₀ hhi (by rw [hc, hcv])⟩
  simp only [ipaPrechallenges]
  exact List.forall₂_map_left_iff.mpr (hus.imp fun _ _ ⟨hi, hhi, hx⟩ u₀ hu₀ huv =>
    low128_of_decomp hp _ u₀ hi hu₀ hhi (by rw [hx, huv]))

end Pickles
