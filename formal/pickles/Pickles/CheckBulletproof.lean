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

/-- The four scalars the check scales by: `cip`, `b`, `z₁`, `z₂`. -/
def CheckBulletproofInput.scaled {F sf : Type} (inp : CheckBulletproofInput F sf) : List sf :=
  [inp.combinedInnerProduct, inp.b, inp.z1, inp.z2]

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

variable {G : Type} [AddCommGroup G] {W : WeierstrassCurve.Affine F}

/-- The masked Horner step over a group: `base + ξ·acc` when kept, `acc` otherwise. -/
def hornerStep (ξ : ℤ) (acc : G) (bm : G × Bool) : G :=
  if bm.2 then bm.1 + ξ • acc else acc

/-- `combinePolynomials`' value: Horner from the last base — its own flag unread, as the
circuit's — over the reversed list; the origin on no bases. -/
def hornerCombine (ξ : ℤ) (bv : List (G × Bool)) : G :=
  match bv.reverse with
  | [] => 0
  | h :: t => t.foldl (hornerStep ξ) h.1

/-- One `lr_prod` term: `u⁻¹·L + u·R` at the expanded challenge `u = endoExpandZ lam n`, the
inverse taken in `ZMod W.order`. -/
noncomputable def lrTerm (lam : ℤ) (q : W.Point × W.Point) (n : ℕ) : W.Point :=
  ((((endoExpandZ lam n : ℤ) : ZMod W.order)⁻¹).val : ℕ) • q.1 + endoExpandZ lam n • q.2

/-- `bulletReduce`'s value: the running sum of the terms; the origin on no pairs. -/
def lrSum (terms : List G) : G :=
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
commitment, the pairs, `δ`, `sg` and `h` reading as points, and the side's scaling reading
through a ladder witness (`hscale`: some `w` with `Pre x w`, the result `dec w • T` once `w`
is in the regime `Reg`; `hreg`: every such witness is), the challenges read as some `ns`, `c`
as some `c₀`, each scaled scalar through some witness, and the success bit reads `1` exactly
when `SchnorrPoint` holds at those readings. -/
theorem ipaFinalCheck_spec {sf ω : Type} (ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf)
    (e : IpaEndo F) (p : Poseidon.Params F) (endo : FVar F)
    (hchar : ∀ a b : ℕ, a < 2 ^ 128 → b < 2 ^ 128 → (a : F) = b → a = b)
    (Pre : sf → ω → Prop) (Reg : ω → Prop) (dec : ω → ℤ)
    (sv : SpongeVar F) (t : FVar F) (u combined : AffinePoint (FVar F))
    (inp : CheckBulletproofInput F sf)
    (hscale : ∀ (pt : AffinePoint (FVar F)) (x : sf), x ∈ inp.scaled →
      ⦃⌜True⌝⦄ ops.scaleByShifted pt x
      ⦃⇓ r _ => ⌜∀ T : e.d.W.Point, OnCurveAt e.d.W V pt T →
        ∃ w : ω, Pre x w ∧ (Reg w → OnCurveAt e.d.W V r (dec w • T))⌝⦄)
    (hreg : ∀ (x : sf) (w : ω), x ∈ inp.scaled → Pre x w → Reg w)
    (δv sgv hv : e.d.W.Point)
    (lrv : List (e.d.W.Point × e.d.W.Point))
    (hlr : List.Forall₂ (PairReads e.d.W V) inp.lr lrv) (hlrne : inp.lr ≠ [])
    (hδ : OnCurveAt e.d.W V inp.delta δv) (hsg : OnCurveAt e.d.W V inp.sg sgv)
    (hh : OnCurveAt e.d.W V inp.blindingGenerator hv) :
    ⦃⌜True⌝⦄ ipaFinalCheck ops e p endo sv t u combined inp
    ⦃⇓ o _ => ⌜∀ uv Pv : e.d.W.Point, OnCurveAt e.d.W V u uv → OnCurveAt e.d.W V combined Pv →
      o.t = t ∧ ∃ (ns : List ℕ) (c₀ : ℕ) (wcip wb w₁ w₂ : ω),
      List.Forall₂ (Reads128 V) o.challenges ns ∧ ns.length = lrv.length ∧ Reads128 V o.c c₀ ∧
      Pre inp.combinedInnerProduct wcip ∧ Pre inp.b wb ∧ Pre inp.z1 w₁ ∧ Pre inp.z2 w₂ ∧
      ((↑o.success : CVar F).val V = 1 ↔
        SchnorrPoint e.d.lam c₀ uv Pv (lrSum (List.zipWith (lrTerm e.d.lam) lrv ns)) δv sgv hv
          (dec wcip) (dec wb) (dec w₁) (dec w₂))⌝⦄ := by
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
  have hsc1 := fun pt => hscale pt inp.combinedInnerProduct (by simp [CheckBulletproofInput.scaled])
  have hsc2 := fun pt => hscale pt inp.b (by simp [CheckBulletproofInput.scaled])
  have hsc3 := fun pt => hscale pt inp.z1 (by simp [CheckBulletproofInput.scaled])
  have hsc4 := fun pt => hscale pt inp.z2 (by simp [CheckBulletproofInput.scaled])
  have hr1 := hreg inp.combinedInnerProduct
  have hr2 := hreg inp.b
  have hr3 := hreg inp.z1
  have hr4 := hreg inp.z2
  simp only [CheckBulletproofInput.scaled, List.mem_cons, List.mem_singleton, true_or, or_true,
    forall_const] at hr1 hr2 hr3 hr4
  mvcgen -trivial [-Snarky.Kimchi.addFast_spec, hext, hbr, hsc1, hsc2, hsc3, hsc4, hadd, hδs, hpre,
    hem]
  rename_i _ ext _ hlen lrProd _ hbr' cipU _ hcip pP _ hpP q _ hq svD _ cP _ cQ _ hcQ lhs _ hlhs
    bU _ hbU sgBU _ hsgBU z1T _ hz1 z2T _ hz2 rhs _ hrhs xEq _ hx yEq _ hy succ _ hand
  intro uv Pv hu hP
  have hzne : inp.lr.zip ext.1 ≠ [] := fun h => by
    rcases List.zip_eq_nil_iff.mp h with h | h
    · exact hlrne h
    · exact hlrne (List.length_eq_zero_iff.mp (by rw [← hlen, h]; rfl))
  obtain ⟨ns, hns, hlr'⟩ := hbr' lrv (forall₂_zip_left ext.1 hlr hlen) hzne
  obtain ⟨wcip, hpcip, hcipU⟩ := hcip uv hu
  have hpP' := hpP _ _ hP (hcipU (hr1 _ hpcip))
  have hq' := hq _ _ hpP' hlr'
  obtain ⟨c₀, hc₀, hcv, hcQ'⟩ := hcQ _ hq'
  have hlhs' := hlhs _ _ hcQ' hδ
  obtain ⟨wb, hpb, hbU'⟩ := hbU uv hu
  have hsgBU' := hsgBU _ _ hsg (hbU' (hr2 _ hpb))
  obtain ⟨w₁, hp1, hz1'⟩ := hz1 _ hsgBU'
  obtain ⟨w₂, hp2, hz2'⟩ := hz2 _ hh
  have hrhs' := hrhs _ _ (hz1' (hr3 _ hp1)) (hz2' (hr4 _ hp2))
  have hxb : (↑xEq : CVar F).val V = bit (decide (lhs.p.x.val V = rhs.p.x.val V)) := by
    rw [hx]; simp only [bit, decide_eq_true_eq]
  have hyb : (↑yEq : CVar F).val V = bit (decide (lhs.p.y.val V = rhs.p.y.val V)) := by
    rw [hy]; simp only [bit, decide_eq_true_eq]
  have hsucc := hand _ _ hxb hyb
  refine ⟨trivial, ns, c₀, wcip, wb, w₁, w₂, forall₂_zip_right hlen hns,
    by rw [← hns.length_eq, List.length_zip, hlen, hlr.length_eq, min_self], ⟨hc₀, hcv⟩, hpcip,
    hpb, hp1, hp2, ?_⟩
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
`sg` and `h` as points, the side's scaling reading through ladder witnesses (`hscale`, `hreg`,
the shape the `scaleFast` laws give) and the map-to-curve as `umap` up to the ordinate's sign
(`hgm`, the shape `groupMapCircuit_toGroup_spec` gives): the challenges read as some `ns`, `c`
as some `c₀`, the four scaled scalars through some witnesses, and the success bit reads `1`
exactly when the Schnorr equation holds at the readings — `u` the map's point or its negation,
the combined commitment `hornerCombine`, `lr_prod` the `lrSum` of the terms. -/
theorem checkBulletproof_spec_success {sf ω : Type}
    (ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds) (endo : FVar F)
    (gm : GroupMapParams F) (sqrtF : F → Option F)
    (hchar : ∀ a b : ℕ, a < 2 ^ 128 → b < 2 ^ 128 → (a : F) = b → a = b)
    (Pre : sf → ω → Prop) (Reg : ω → Prop) (dec : ω → ℤ)
    (umap : F → e.d.W.Point)
    (hgm : ∀ t : FVar F, ⦃⌜True⌝⦄ groupMapCircuit (c := Builder V (KimchiConstraint F)) sqrtF gm t
      ⦃⇓ r _ => ⌜∃ U : e.d.W.Point, OnCurveAt e.d.W V r U ∧
        (U = umap (t.val V) ∨ U = -umap (t.val V))⌝⦄)
    (sv : SpongeVar F) (bases : List (AffinePoint (FVar F) × Option (BoolVar F)))
    (bv : List (e.d.W.Point × Bool)) (hb : List.Forall₂ (MaskedBaseReads e.d.W V) bases bv)
    (hbne : bases ≠ []) (inp : CheckBulletproofInput F sf)
    (hscale : ∀ (pt : AffinePoint (FVar F)) (x : sf), x ∈ inp.scaled →
      ⦃⌜True⌝⦄ ops.scaleByShifted pt x
      ⦃⇓ r _ => ⌜∀ T : e.d.W.Point, OnCurveAt e.d.W V pt T →
        ∃ w : ω, Pre x w ∧ (Reg w → OnCurveAt e.d.W V r (dec w • T))⌝⦄)
    (hreg : ∀ (x : sf) (w : ω), x ∈ inp.scaled → Pre x w → Reg w)
    (n : ℕ) (hn : n < 2 ^ 128) (hxi : inp.xi.val.val V = n) (δv sgv hv : e.d.W.Point)
    (lrv : List (e.d.W.Point × e.d.W.Point))
    (hlr : List.Forall₂ (PairReads e.d.W V) inp.lr lrv) (hlrne : inp.lr ≠ [])
    (hδ : OnCurveAt e.d.W V inp.delta δv) (hsg : OnCurveAt e.d.W V inp.sg sgv)
    (hh : OnCurveAt e.d.W V inp.blindingGenerator hv) :
    ⦃⌜True⌝⦄ checkBulletproof ops e p endo gm sqrtF sv bases inp
    ⦃⇓ o _ => ⌜∃ (U : e.d.W.Point) (ns : List ℕ) (c₀ : ℕ) (wcip wb w₁ w₂ : ω),
      (U = umap (o.t.val V) ∨ U = -umap (o.t.val V)) ∧
      List.Forall₂ (Reads128 V) o.challenges ns ∧ ns.length = lrv.length ∧ Reads128 V o.c c₀ ∧
      Pre inp.combinedInnerProduct wcip ∧ Pre inp.b wb ∧ Pre inp.z1 w₁ ∧ Pre inp.z2 w₂ ∧
      ((↑o.success : CVar F).val V = 1 ↔
        SchnorrPoint e.d.lam c₀ U (hornerCombine (endoExpandZ e.d.lam n) bv)
          (lrSum (List.zipWith (lrTerm e.d.lam) lrv ns)) δv sgv hv
          (dec wcip) (dec wb) (dec w₁) (dec w₂))⌝⦄ := by
  simp only [checkBulletproof]
  have habs := fun sv' limbs => builder_spec_true
    (absorbList (c := Builder V (KimchiConstraint F)) p sv' limbs)
  have hsq := fun sv' => builder_spec_true
    (SpongeVar.squeeze (c := Builder V (KimchiConstraint F)) p sv')
  have hcomb := combinePolynomials_spec (V := V) e inp.xi n hn hxi hchar bases bv hb hbne
  have hfin := fun sv' t u comb => ipaFinalCheck_spec (V := V) ops e p endo hchar Pre Reg dec
    sv' t u comb inp hscale hreg δv sgv hv lrv hlr hlrne hδ hsg hh
  mvcgen -trivial [habs, hsq, hgm, hcomb, hfin]
  case vc1.hsize => exact hsize
  rename_i _ _ _ tv _ _ u _ hu comb _ hP o _
  intro ho
  obtain ⟨U, hU, hsign⟩ := hu
  obtain ⟨ht, ns, c₀, wcip, wb, w₁, w₂, hns, hlen, hc, hpcip, hpb, hp1, hp2, hiff⟩ :=
    ho _ _ hU hP
  rw [ht]
  exact ⟨U, ns, c₀, wcip, wb, w₁, w₂, hsign, hns, hlen, hc, hpcip, hpb, hp1, hp2, hiff⟩


/-! ## The deployed ladders

The two sides' scaling gadgets read through the ladder laws at the deployed curves: a
witness integer standing for the shifted scalar, its decode acting once it is in the one-wrap
regime. The witness is the prover's — `scale_fast` pins its bit decomposition only through
the scalar it packs to, on every side — so the readings quantify over it. -/

section Deployed

open CompElliptic.Curves.Pasta Pasta.Shifted

/-- The wrap side's ladder witness of a `Type1` scalar: an integer below `2²⁵⁵` reading as
its representative. -/
def WrapLadderPre (V : Valuation Fq) (x : Type1 (FVar Fq)) (z : ℤ) : Prop :=
  0 ≤ z ∧ z < 2 ^ 255 ∧ (z : Fq) = x.val.val V

/-- The wrap side's decode of a witness: the `Type1` unshift. -/
def wrapLadderDec (z : ℤ) : ℤ := unshiftType1 255 z

/-- The wrap side's regime: the Vesta one-wrap regime at the decode. -/
def WrapLadderReg (z : ℤ) : Prop := HasCurve.vesta.LadderRegime 255 (wrapLadderDec z)

/-- `IpaScalarOps.wrap`'s scaling reads through `scaleFast1_spec` at Vesta. -/
theorem wrap_scale_reads {V : Valuation Fq} (pt : AffinePoint (FVar Fq)) (x : Type1 (FVar Fq)) :
    ⦃⌜True⌝⦄ (IpaScalarOps.wrap (c := Builder V (KimchiConstraint Fq))).scaleByShifted pt x
    ⦃⇓ r _ => ⌜∀ T : IpaEndo.vesta.d.W.Point, OnCurveAt IpaEndo.vesta.d.W V pt T →
      ∃ z : ℤ, WrapLadderPre V x z ∧
        (WrapLadderReg z → OnCurveAt IpaEndo.vesta.d.W V r (wrapLadderDec z • T))⌝⦄ := by
  refine builder_spec_imp _ _ _
    (scaleFast1_spec (V := V) HasCurve.vesta 255 51 (by norm_num) pt x) fun r hr T hT => ?_
  obtain ⟨z, h0, hlt, hz, hreg⟩ := hr T hT
  exact ⟨z, ⟨h0, hlt, hz⟩, fun hR => hreg hR⟩

/-- The step side's ladder witness of a split `Type2` scalar: the parity bit's reading and
an integer below `2²⁵⁴` reading as the halved representative. -/
def StepLadderPre (V : Valuation Fp) (x : Type2 (SplitField (FVar Fp) (BoolVar Fp)))
    (w : ℤ × Bool) : Prop :=
  (↑x.val.sOdd : CVar Fp).val V = bit w.2 ∧ 0 ≤ w.1 ∧ w.1 < 2 ^ 254 ∧
    (w.1 : Fp) = x.val.sDiv2.val V

/-- The step side's decode of a witness: the `Type2` unshift of the half and the parity. -/
def stepLadderDec (w : ℤ × Bool) : ℤ := unshiftType2 255 w.1 (if w.2 then 1 else 0)

/-- The step side's regime: the Pallas one-wrap regime at the half's `Type1` decode, the
ladder's own operand. -/
def StepLadderReg (w : ℤ × Bool) : Prop := HasCurve.pallas.LadderRegime 255 (unshiftType1 255 w.1)

/-- `IpaScalarOps.step`'s scaling reads through `scaleFast2_spec` at Pallas, given the parity
bit reads as a bit. -/
theorem step_scale_reads {V : Valuation Fp} (pt : AffinePoint (FVar Fp))
    (x : Type2 (SplitField (FVar Fp) (BoolVar Fp))) (bb : Bool)
    (hbit : (↑x.val.sOdd : CVar Fp).val V = bit bb) :
    ⦃⌜True⌝⦄ (IpaScalarOps.step (c := Builder V (KimchiConstraint Fp))).scaleByShifted pt x
    ⦃⇓ r _ => ⌜∀ T : IpaEndo.pallas.d.W.Point, OnCurveAt IpaEndo.pallas.d.W V pt T →
      ∃ w : ℤ × Bool, StepLadderPre V x w ∧
        (StepLadderReg w → OnCurveAt IpaEndo.pallas.d.W V r (stepLadderDec w • T))⌝⦄ := by
  refine builder_spec_imp _ _ _
    (scaleFast2_spec (V := V) HasCurve.pallas 255 51 254 (by norm_num) (by norm_num) pt
      x.val.sDiv2 x.val.sOdd) fun r hr T hT => ?_
  obtain ⟨z, h0, hlt, hz, hreg⟩ := hr T hT bb hbit
  exact ⟨(z, bb), ⟨hbit, h0, hlt, hz⟩, fun hR => hreg hR⟩

end Deployed


section DeployedVesta

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Curves.Pasta Poseidon.GroupMap
open WeierstrassCurve.Affine

/-- The wrap side's group-map parameters (PS `groupMapParams (Proxy @VestaG)`): the Vesta
BW19 `setup()` spec with the non-residue `5`. -/
abbrev groupMapParamsVesta : GroupMapParams Fq := .ofSpec Poseidon.GroupMapVesta.spec 5

/-- No Vesta point has ordinate zero — it would be 2-torsion — so no candidate ordinate
square vanishes. -/
theorem vesta_curveEqn_ne_zero (x : Fq) : curveEqn Poseidon.GroupMapVesta.spec x ≠ 0 := by
  intro h0
  have hon : OnCurve Vesta.curve.A Vesta.curve.B (x, 0) := by
    have hA : Vesta.curve.A = 0 := Poseidon.GroupMapVesta.spec.hA
    simp only [OnCurve, hA, zero_mul, _root_.add_zero]
    simpa [curveEqn, Poseidon.GroupMapVesta.spec] using h0.symm
  have hns := nonsingular_toW hon
  have hQ2 : Point.some x 0 hns + Point.some x 0 hns = 0 :=
    Point.add_self_of_Y_eq (by simp [negY, toW])
  exact HasEndo.vesta.two_torsion_free _ (Point.some_ne_zero hns) hQ2

/-- The wrap side's map-to-curve reads as the wire map `toGroup`'s point, up to sign. -/
theorem vesta_groupMap_reads {V : Valuation Fq} (sqrtF : Fq → Option Fq) (t : FVar Fq) :
    ⦃⌜True⌝⦄ groupMapCircuit (c := Builder V (KimchiConstraint Fq)) sqrtF groupMapParamsVesta t
    ⦃⇓ r _ => ⌜∃ U : IpaEndo.vesta.d.W.Point, OnCurveAt IpaEndo.vesta.d.W V r U ∧
      (U = SWPoint.equivPoint Poseidon.GroupMapVesta.spec.E
          (toGroup Poseidon.GroupMapVesta.spec (t.val V)) ∨
        U = -SWPoint.equivPoint Poseidon.GroupMapVesta.spec.E
          (toGroup Poseidon.GroupMapVesta.spec (t.val V)))⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat
  obtain ⟨hx, hy⟩ := (builder_spec_iff _ _).mp (groupMapCircuit_toGroup_spec (V := V)
    (c := KimchiConstraint Fq) Poseidon.GroupMapVesta.spec 5 Vesta.five_not_isSquare
    vesta_curveEqn_ne_zero sqrtF t) nv hsat
  obtain ⟨-, hcurve⟩ := (builder_spec_iff _ _).mp (groupMapCircuit_spec (V := V)
    (c := KimchiConstraint Fq) sqrtF groupMapParamsVesta t) nv hsat
  generalize (build (groupMapCircuit (c := Builder V (KimchiConstraint Fq)) sqrtF
    groupMapParamsVesta t) nv).result = r at hx hy hcurve ⊢
  generalize toGroup Poseidon.GroupMapVesta.spec (t.val V) = P at hx hy ⊢
  have hon : OnCurve Vesta.curve.A Vesta.curve.B (P.x, P.y) := by
    rcases P.onCurve with h | h
    · exact h
    · exfalso
      obtain ⟨hpx, hpy⟩ := Prod.mk.injEq _ _ _ _ ▸ h
      rw [hpx] at hx
      rw [hpy] at hy
      have hy0 : r.y.val V = 0 := by rcases hy with hy | hy <;> simp [hy]
      rw [hy0, hx] at hcurve
      simp [ySquared, GroupMapParams.ofSpec] at hcurve
      exact absurd hcurve (by decide)
  have hns := nonsingular_toW hon
  rw [SWPoint.equivPoint_eq_some P hon]
  rcases hy with hy | hy
  · exact ⟨_, OnCurveAt.of_reads hx hy hns, Or.inl rfl⟩
  · have hr' : OnCurveAt (toW Vesta.curve.A Vesta.curve.B) V ⟨r.x, CVar.negate_ r.y⟩
        (Point.some P.x P.y hns) :=
      OnCurveAt.of_reads (p := ⟨r.x, CVar.negate_ r.y⟩) hx
        (by simp only [CVar.val_negate_, hy, _root_.neg_neg]) hns
    have hneg := OnCurveAt.neg ⟨rfl, rfl⟩ hr'
    refine ⟨-(Point.some P.x P.y hns), ?_, Or.inr rfl⟩
    have hval : (CVar.negate_ (CVar.negate_ r.y)).val V = r.y.val V := by
      simp only [CVar.val_negate_, _root_.neg_neg]
    simpa only [OnCurveAt, hval] using hneg

end DeployedVesta

section DeployedPallas

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Curves.Pasta Poseidon.GroupMap
open WeierstrassCurve.Affine

/-- The step side's group-map parameters (PS `groupMapParams (Proxy @PallasG)`): the Pallas
BW19 `setup()` spec with the non-residue `5`. -/
abbrev groupMapParamsPallas : GroupMapParams Fp := .ofSpec Poseidon.GroupMapPallas.spec 5

/-- No Pallas point has ordinate zero — it would be 2-torsion — so no candidate ordinate
square vanishes. -/
theorem pallas_curveEqn_ne_zero (x : Fp) : curveEqn Poseidon.GroupMapPallas.spec x ≠ 0 := by
  intro h0
  have hon : OnCurve Pallas.curve.A Pallas.curve.B (x, 0) := by
    have hA : Pallas.curve.A = 0 := Poseidon.GroupMapPallas.spec.hA
    simp only [OnCurve, hA, zero_mul, _root_.add_zero]
    simpa [curveEqn, Poseidon.GroupMapPallas.spec] using h0.symm
  have hns := nonsingular_toW hon
  have hQ2 : Point.some x 0 hns + Point.some x 0 hns = 0 :=
    Point.add_self_of_Y_eq (by simp [negY, toW])
  exact HasEndo.pallas.two_torsion_free _ (Point.some_ne_zero hns) hQ2

/-- The step side's map-to-curve reads as the wire map `toGroup`'s point, up to sign. -/
theorem pallas_groupMap_reads {V : Valuation Fp} (sqrtF : Fp → Option Fp) (t : FVar Fp) :
    ⦃⌜True⌝⦄ groupMapCircuit (c := Builder V (KimchiConstraint Fp)) sqrtF groupMapParamsPallas t
    ⦃⇓ r _ => ⌜∃ U : IpaEndo.pallas.d.W.Point, OnCurveAt IpaEndo.pallas.d.W V r U ∧
      (U = SWPoint.equivPoint Poseidon.GroupMapPallas.spec.E
          (toGroup Poseidon.GroupMapPallas.spec (t.val V)) ∨
        U = -SWPoint.equivPoint Poseidon.GroupMapPallas.spec.E
          (toGroup Poseidon.GroupMapPallas.spec (t.val V)))⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat
  obtain ⟨hx, hy⟩ := (builder_spec_iff _ _).mp (groupMapCircuit_toGroup_spec (V := V)
    (c := KimchiConstraint Fp) Poseidon.GroupMapPallas.spec 5 Pallas.five_not_isSquare
    pallas_curveEqn_ne_zero sqrtF t) nv hsat
  obtain ⟨-, hcurve⟩ := (builder_spec_iff _ _).mp (groupMapCircuit_spec (V := V)
    (c := KimchiConstraint Fp) sqrtF groupMapParamsPallas t) nv hsat
  generalize (build (groupMapCircuit (c := Builder V (KimchiConstraint Fp)) sqrtF
    groupMapParamsPallas t) nv).result = r at hx hy hcurve ⊢
  generalize toGroup Poseidon.GroupMapPallas.spec (t.val V) = P at hx hy ⊢
  have hon : OnCurve Pallas.curve.A Pallas.curve.B (P.x, P.y) := by
    rcases P.onCurve with h | h
    · exact h
    · exfalso
      obtain ⟨hpx, hpy⟩ := Prod.mk.injEq _ _ _ _ ▸ h
      rw [hpx] at hx
      rw [hpy] at hy
      have hy0 : r.y.val V = 0 := by rcases hy with hy | hy <;> simp [hy]
      rw [hy0, hx] at hcurve
      simp [ySquared, GroupMapParams.ofSpec] at hcurve
      exact absurd hcurve (by decide)
  have hns := nonsingular_toW hon
  rw [SWPoint.equivPoint_eq_some P hon]
  rcases hy with hy | hy
  · exact ⟨_, OnCurveAt.of_reads hx hy hns, Or.inl rfl⟩
  · have hr' : OnCurveAt (toW Pallas.curve.A Pallas.curve.B) V ⟨r.x, CVar.negate_ r.y⟩
        (Point.some P.x P.y hns) :=
      OnCurveAt.of_reads (p := ⟨r.x, CVar.negate_ r.y⟩) hx
        (by simp only [CVar.val_negate_, hy, _root_.neg_neg]) hns
    have hneg := OnCurveAt.neg ⟨rfl, rfl⟩ hr'
    refine ⟨-(Point.some P.x P.y hns), ?_, Or.inr rfl⟩
    have hval : (CVar.negate_ (CVar.negate_ r.y)).val V = r.y.val V := by
      simp only [CVar.val_negate_, _root_.neg_neg]
    simpa only [OnCurveAt, hval] using hneg

end DeployedPallas


/-! ## The bridge to the wire group

Pure algebra, no circuit: the gadgets' readings live in Mathlib's point group with integer
scalars, the wire verifier in `SWPoint` with `ZMod`-valued scalars acting by their canonical
representatives. The lemmas below move the Schnorr equation between the two forms. -/

section Bridge

variable {G : Type} [AddCommGroup G]

omit [Field F] [DecidableEq F] [ToNat F] in
/-- In a group killed by `n`, an integer acts as its residue's canonical representative. -/
private theorem zsmul_eq_val_nsmul (n : ℕ) [NeZero n] (hn : ∀ x : G, n • x = 0) (z : ℤ) (x : G) :
    z • x = ((z : ZMod n).val : ℕ) • x := by
  have hv : (((z : ZMod n).val : ℕ) : ℤ) = z % n := ZMod.val_intCast z
  rw [← natCast_zsmul, hv]
  conv_lhs => rw [← Int.emod_add_ediv z n]
  rw [add_zsmul, mul_zsmul, natCast_zsmul, hn, add_zero]

omit [Field F] [DecidableEq F] [ToNat F] in
/-- In a group killed by `n`, the representative of a product acts as the composite. -/
private theorem val_mul_nsmul (n : ℕ) [NeZero n] (hn : ∀ x : G, n • x = 0) (a b : ZMod n) (X : G) :
    (a * b).val • X = a.val • b.val • X := by
  rw [ZMod.val_mul, ← mul_nsmul']
  conv_rhs => rw [← Nat.mod_add_div (a.val * b.val) n, add_nsmul, mul_nsmul', hn, _root_.add_zero]

omit [Field F] [DecidableEq F] [ToNat F] in
/-- The masked Horner fold skips exactly the unkept bases. -/
private theorem foldl_hornerStep_eq (ξ : ℤ) :
    ∀ (t : List (G × Bool)) (acc : G),
      t.foldl (hornerStep ξ) acc = ((t.filter (·.2)).map (·.1)).foldl (fun acc P => P + ξ • acc) acc
  | [], _ => rfl
  | (P, true) :: t, acc => by
    simp only [List.foldl_cons, hornerStep, ite_true, List.filter_cons_of_pos, List.map_cons]
    exact foldl_hornerStep_eq ξ t _
  | (P, false) :: t, acc => by
    simp only [List.foldl_cons, hornerStep, Bool.false_eq_true, ite_false,
      List.filter_cons_of_neg]
    exact foldl_hornerStep_eq ξ t _

omit [Field F] [DecidableEq F] [ToNat F] in
/-- With its last base kept, the masked Horner fold is Horner's rule over the kept bases:
`C₀ + ξ·(C₁ + ξ·(… + ξ·Cₘ))`. -/
private theorem hornerCombine_eq_foldr (ξ : ℤ) (bv : List (G × Bool))
    (hlast : ∀ h, bv.getLast? = some h → h.2 = true) :
    hornerCombine ξ bv = ((bv.filter (·.2)).map (·.1)).foldr (fun P acc => P + ξ • acc) 0 := by
  unfold hornerCombine
  rcases hrev : bv.reverse with _ | ⟨h, t⟩
  · simp [List.reverse_eq_nil_iff.mp hrev]
  · have hbv : bv = t.reverse ++ [h] := by
      rw [← List.reverse_reverse bv, hrev, List.reverse_cons]
    have hh : h.2 = true := hlast h (by rw [hbv, List.getLast?_append_of_ne_nil _ (by simp)]; rfl)
    show List.foldl (hornerStep ξ) h.1 t = _
    rw [foldl_hornerStep_eq, hbv, List.filter_append, List.map_append,
      List.filter_cons_of_pos hh, List.filter_nil, List.map_cons, List.map_nil,
      List.foldr_append, List.foldr_cons, List.foldr_nil, zsmul_zero, add_zero,
      List.filter_reverse, List.map_reverse, List.foldr_reverse]

omit [Field F] [DecidableEq F] [ToNat F] in
/-- A left fold of addition from a start is the start plus the sum. -/
private theorem foldl_add_eq (init : G) : ∀ l : List G, l.foldl (· + ·) init = init + l.sum
  | [] => by simp
  | x :: l => by
    rw [List.foldl_cons, foldl_add_eq (init + x) l, List.sum_cons, add_assoc]

omit [Field F] [DecidableEq F] [ToNat F] in
/-- The running sum of terms is their sum. -/
private theorem lrSum_eq_sum : ∀ l : List G, lrSum l = l.sum
  | [] => rfl
  | h :: t => by simp only [lrSum, foldl_add_eq, List.sum_cons]

end Bridge

section TransportVesta

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass Poseidon.FqSponge
open Kimchi.Gate.EndoScalar Bulletproof Bulletproof.Ipa

/-- The Vesta point group is killed by its order. -/
private theorem vesta_card_nsmul (X : Vesta.curve.toAffine.Point) : PALLAS_BASE_CARD • X = 0 :=
  ZModModule.char_nsmul_eq_zero (n := PALLAS_BASE_CARD) X

/-- An integer acts on Vesta points as its residue's representative in the scalar field. -/
private theorem vesta_zsmul_eq (z : ℤ) (X : Vesta.curve.toAffine.Point) :
    z • X = ((z : Fp).val : ℕ) • X :=
  zsmul_eq_val_nsmul PALLAS_BASE_CARD vesta_card_nsmul z X

/-- The gadgets' integer endo-expansion at Vesta's eigenvalue casts to the wire's. -/
private theorem vesta_endoExpandZ_cast (n : ℕ) :
    ((endoExpandZ Pasta.vestaLam n : ℤ) : Fp) = endoExpand Poseidon.FqVesta.spec.lam n :=
  endoExpandZ_cast (by decide) (by decide) Pasta.vestaLam n

/-- The inverse's representative does not depend on how the order is named. -/
private theorem zmod_inv_val_congr (n m : ℕ) (h : n = m) (z : ℤ) :
    ((z : ZMod n)⁻¹).val = ((z : ZMod m)⁻¹).val := by
  subst h
  rfl

/-- A round term of `lr_prod`, read back in the wire group, is the wire's round term at the
expanded challenge. -/
private theorem vesta_lrTerm_eq (q : SWPoint Vesta.curve × SWPoint Vesta.curve) (n : ℕ) :
    (SWPoint.equivPoint Vesta.curve).symm
        (lrTerm Pasta.vestaLam ((SWPoint.equivPoint Vesta.curve) q.1,
          (SWPoint.equivPoint Vesta.curve) q.2) n)
      = ((endoExpand Poseidon.FqVesta.spec.lam n)⁻¹).val • q.1
        + (endoExpand Poseidon.FqVesta.spec.lam n).val • q.2 := by
  unfold lrTerm
  rw [map_add]
  rw [map_nsmul, map_zsmul]
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  rw [zmod_inv_val_congr _ PALLAS_BASE_CARD Pasta.vesta_card]
  rw [vesta_endoExpandZ_cast]
  rw [zsmul_eq_val_nsmul PALLAS_BASE_CARD
    (fun X => ZModModule.char_nsmul_eq_zero (n := PALLAS_BASE_CARD) X), vesta_endoExpandZ_cast]

/-- The round terms of `lr_prod`, read back in the wire group, are the wire's round terms at
the expanded challenges. -/
private theorem vesta_zipTerms :
    ∀ (l : List (SWPoint Vesta.curve × SWPoint Vesta.curve)) (ns : List ℕ),
      (List.zipWith (lrTerm Pasta.vestaLam)
        (l.map fun q =>
          ((SWPoint.equivPoint Vesta.curve) q.1, (SWPoint.equivPoint Vesta.curve) q.2)) ns).map
        (SWPoint.equivPoint Vesta.curve).symm
      = (l.zip (ns.map (endoExpand Poseidon.FqVesta.spec.lam))).map
          fun x => (x.2⁻¹).val • x.1.1 + x.2.val • x.1.2
  | [], _ => by simp
  | _ :: _, [] => by simp
  | q :: l, n :: ns => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.zip_cons_cons, vesta_lrTerm_eq]
    exact congrArg _ (vesta_zipTerms l ns)

/-- The wire's polyscale combination is Horner's rule over the list, the scalar acting by
its representative. -/
private theorem combineCommitments_eq_foldr_vesta (ξ : Fp) (cs : List (SWPoint Vesta.curve)) :
    combineCommitments IpaVesta.curve ξ cs.toArray
      = cs.foldr (fun P acc => P + ξ.val • acc) 0 := by
  have hn : ∀ x : SWPoint Vesta.curve, PALLAS_BASE_CARD • x = 0 := fun x =>
    ZModModule.char_nsmul_eq_zero (n := PALLAS_BASE_CARD) x
  have key : ∀ (l : List (SWPoint Vesta.curve)) (acc : SWPoint Vesta.curve) (pw : Fp),
      (l.foldl (fun (acc : SWPoint Vesta.curve × Fp) P => (acc.1 + acc.2.val • P, acc.2 * ξ))
        (acc, pw)).1 = acc + pw.val • l.foldr (fun P acc => P + ξ.val • acc) 0 := by
    intro l
    induction l with
    | nil => intro acc pw; simp
    | cons P l ih =>
      intro acc pw
      rw [List.foldl_cons, ih, List.foldr_cons, nsmul_add, val_mul_nsmul PALLAS_BASE_CARD hn,
        _root_.add_assoc]
  unfold combineCommitments
  rw [← Array.foldl_toList, List.toList_toArray, key, ZMod.val_one, one_nsmul, _root_.zero_add]
/-- Horner's rule over the kept bases, read back in the wire group, is the wire's polyscale
combination at the expanded challenge. -/
private theorem vesta_hornerCombine_eq (n : ℕ) (bvW : List (SWPoint Vesta.curve × Bool))
    (hlast : ∀ h, bvW.getLast? = some h → h.2 = true) :
    (SWPoint.equivPoint Vesta.curve).symm
        (hornerCombine (endoExpandZ Pasta.vestaLam n)
          (bvW.map fun b => ((SWPoint.equivPoint Vesta.curve) b.1, b.2)))
      = combineCommitments IpaVesta.curve (endoExpand Poseidon.FqVesta.spec.lam n)
          ((bvW.filter (·.2)).map (·.1)).toArray := by
  have hn : ∀ x : SWPoint Vesta.curve, PALLAS_BASE_CARD • x = 0 := fun x =>
    ZModModule.char_nsmul_eq_zero (n := PALLAS_BASE_CARD) x
  have hlast' : ∀ h, (bvW.map fun b => ((SWPoint.equivPoint Vesta.curve) b.1, b.2)).getLast?
      = some h → h.2 = true := by
    intro h hh
    rw [List.getLast?_map] at hh
    rcases hl : bvW.getLast? with _ | g
    · rw [hl] at hh; cases hh
    · rw [hl] at hh
      simp only [Option.map_some, Option.some.injEq] at hh
      rw [← hh]
      exact hlast g hl
  rw [hornerCombine_eq_foldr _ _ hlast', combineCommitments_eq_foldr_vesta]
  have hfl : (bvW.map fun b => ((SWPoint.equivPoint Vesta.curve) b.1, b.2)).filter (·.2)
      = (bvW.filter (·.2)).map fun b => ((SWPoint.equivPoint Vesta.curve) b.1, b.2) := by
    rw [List.filter_map]; rfl
  have hm : ((·.1) ∘ fun b : SWPoint Vesta.curve × Bool =>
      ((SWPoint.equivPoint Vesta.curve) b.1, b.2)) = (SWPoint.equivPoint Vesta.curve) ∘ (·.1) := rfl
  rw [hfl, List.map_map, hm, ← List.map_map, ← vesta_endoExpandZ_cast]
  generalize (bvW.filter (·.2)).map (·.1) = cs
  generalize endoExpandZ Pasta.vestaLam n = z
  induction cs with
  | nil => simp
  | cons P cs ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, map_add, map_zsmul, ih,
      AddEquiv.symm_apply_apply, zsmul_eq_val_nsmul PALLAS_BASE_CARD hn]

/-- The bridge: the gadgets' Schnorr equation over Mathlib's Vesta point group, at the
readings' images under `SWPoint.equivPoint`, is the wire verifier's `schnorrAt` at the
expanded challenges and the cast scalars. -/
theorem schnorrPoint_iff_schnorrAt_vesta (σ : SRS (SWPoint Vesta.curve)) (U P : SWPoint Vesta.curve)
    (chals : Vector Fp σ.k) (c₀ : ℕ) (cip b z₁ z₂ : ℤ) (pr : Ipa.Proof IpaVesta.curve σ.k)
    (ns : List ℕ) (hchals : chals.toList = ns.map (endoExpand Poseidon.FqVesta.spec.lam))
    (hz1 : pr.z1 = (z₁ : Fp)) (hz2 : pr.z2 = (z₂ : Fp)) :
    SchnorrPoint Pasta.vestaLam c₀ (SWPoint.equivPoint Vesta.curve U)
        (SWPoint.equivPoint Vesta.curve P)
        (lrSum (List.zipWith (lrTerm Pasta.vestaLam) (pr.lr.toList.map fun q =>
          ((SWPoint.equivPoint Vesta.curve) q.1, (SWPoint.equivPoint Vesta.curve) q.2)) ns))
        (SWPoint.equivPoint Vesta.curve pr.delta) (SWPoint.equivPoint Vesta.curve pr.sg)
        (SWPoint.equivPoint Vesta.curve σ.h) cip b z₁ z₂
      ↔ schnorrAt IpaVesta.curve σ U chals (endoExpand Poseidon.FqVesta.spec.lam c₀) (cip : Fp)
          (b : Fp) P pr := by
  have hsm : ∀ (z : ℤ) (X : Vesta.curve.toAffine.Point), z • X = ((z : Fp).val : ℕ) • X :=
    vesta_zsmul_eq
  have hzip := vesta_zipTerms pr.lr.toList ns
  -- the wire's fold as a start plus a sum
  have hfold : ∀ (l : List ((SWPoint Vesta.curve × SWPoint Vesta.curve) × Fp))
      (init : SWPoint Vesta.curve),
      l.foldl (fun acc (LRu : (SWPoint Vesta.curve × SWPoint Vesta.curve) × Fp) =>
        acc + ((LRu.2⁻¹).val • LRu.1.1 + LRu.2.val • LRu.1.2)) init
        = init + (l.map fun x => (x.2⁻¹).val • x.1.1 + x.2.val • x.1.2).sum := by
    intro l init
    rw [← List.foldl_map, foldl_add_eq]
  unfold SchnorrPoint schnorrAt
  dsimp only
  rw [hz1, hz2, ← Array.foldl_toList, Array.toList_zip, hfold]
  have hl1 : pr.lr.toArray.toList = pr.lr.toList := rfl
  have hl2 : chals.toArray.toList = ns.map (endoExpand Poseidon.FqVesta.spec.lam) := hchals
  rw [hl1, hl2]
  have hZ : List.zipWith (lrTerm Pasta.vestaLam) (List.map (fun q =>
        ((SWPoint.equivPoint Vesta.curve) q.1, (SWPoint.equivPoint Vesta.curve) q.2))
          pr.lr.toList) ns
      = ((pr.lr.toList.zip (ns.map (endoExpand Poseidon.FqVesta.spec.lam))).map
          fun x => (x.2⁻¹).val • x.1.1 + x.2.val • x.1.2).map
            (SWPoint.equivPoint Vesta.curve) := by
    rw [← hzip, List.map_map]
    simp only [Function.comp_def, AddEquiv.apply_symm_apply, List.map_id']
  have key1 : (SWPoint.equivPoint Vesta.curve) ((endoExpand Poseidon.FqVesta.spec.lam c₀).val •
        (P + (cip : Fp).val • U + ((pr.lr.toList.zip
          (ns.map (endoExpand Poseidon.FqVesta.spec.lam))).map
            fun x => (x.2⁻¹).val • x.1.1 + x.2.val • x.1.2).sum) + pr.delta)
      = endoExpandZ Pasta.vestaLam c₀ • ((SWPoint.equivPoint Vesta.curve) P +
          cip • (SWPoint.equivPoint Vesta.curve) U +
          lrSum (List.zipWith (lrTerm Pasta.vestaLam) (List.map (fun q =>
            ((SWPoint.equivPoint Vesta.curve) q.1, (SWPoint.equivPoint Vesta.curve) q.2))
              pr.lr.toList) ns)) + (SWPoint.equivPoint Vesta.curve) pr.delta := by
    rw [hZ, lrSum_eq_sum, ← map_list_sum, map_add, map_nsmul, map_add, map_add, map_nsmul,
      hsm (endoExpandZ _ _), vesta_endoExpandZ_cast, hsm cip]
  have key2 : (SWPoint.equivPoint Vesta.curve)
        ((z₁ : Fp).val • pr.sg + ((z₁ : Fp) * (b : Fp)).val • U + (z₂ : Fp).val • σ.h)
      = z₁ • ((SWPoint.equivPoint Vesta.curve) pr.sg + b • (SWPoint.equivPoint Vesta.curve) U)
        + z₂ • (SWPoint.equivPoint Vesta.curve) σ.h := by
    rw [map_add, map_add, map_nsmul, map_nsmul, map_nsmul, smul_add, ← mul_zsmul, hsm z₁,
      hsm (z₁ * b), hsm z₂, Int.cast_mul]
  rw [← key1, ← key2]
  exact (SWPoint.equivPoint Vesta.curve).injective.eq_iff

end TransportVesta

section DeployedWrap

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass Poseidon.FqSponge
open Kimchi.Gate.EndoScalar Kimchi.Gate.VarBaseMul Bulletproof Bulletproof.Ipa

/-- Naturals below `2¹²⁸` cast injectively into `Fq`. -/
private theorem fq_natCast_inj (a b : ℕ) (ha : a < 2 ^ 128) (hb : b < 2 ^ 128)
    (h : (a : Fq) = b) : a = b := by
  have h' := (ZMod.natCast_eq_natCast_iff' a b _).mp h
  rwa [Nat.mod_eq_of_lt (lt_trans ha (by decide)), Nat.mod_eq_of_lt (lt_trans hb (by decide))] at h'

/-- **The wrap side's `check_bulletproof` at the wire.** Under any valuation satisfying the
emitted constraints — the bases reading as Vesta points (the last kept), the pairs, `δ`, `sg`
and `h` as points, the ladder witnesses off the forbidden band — the challenges read as some
`ns`, `c` as some `c₀`, the four `Type1` scalars through witnesses below `2²⁵⁵`, and the
success bit reads `1` exactly when the wire verifier's `schnorrAt` holds at `IpaVesta.curve`:
the `U` base the deployed map-to-curve's point or its negation, the challenges the
endo-expansions of `ns`, the combined commitment `combineCommitments` over the kept bases at
the expanded `ξ`, and `cip`, `b`, `z₁`, `z₂` the witnesses' `Type1` decodes cast to `Fp`.
With `verifyWith_eq`, `success ∧ sg = ⟨bPolyCoefficients chals, g⟩` is `verifyWith` at those
readings. -/
theorem checkBulletproof_wrap_spec {V : Valuation Fq}
    (p : Poseidon.Params Fq) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (endo : FVar Fq) (sqrtF : Fq → Option Fq) (sv : SpongeVar Fq)
    (bases : List (AffinePoint (FVar Fq) × Option (BoolVar Fq)))
    (bvW : List (SWPoint Vesta.curve × Bool))
    (hb : List.Forall₂ (MaskedBaseReads IpaEndo.vesta.d.W V) bases
      (bvW.map fun b => ((SWPoint.equivPoint Vesta.curve) b.1, b.2)))
    (hbne : bases ≠ []) (hlast : ∀ h, bvW.getLast? = some h → h.2 = true)
    (inp : CheckBulletproofInput Fq (Type1 (FVar Fq)))
    (hband : ∀ (x : Type1 (FVar Fq)) (z : ℤ), x ∈ inp.scaled → WrapLadderPre V x z →
      wrapLadderDec z ∉ forbiddenValues PALLAS_BASE_CARD)
    (n : ℕ) (hn : n < 2 ^ 128) (hxi : inp.xi.val.val V = n)
    (σ : SRS (SWPoint Vesta.curve))
    (lrW : Vector (SWPoint Vesta.curve × SWPoint Vesta.curve) σ.k) (δW sgW : SWPoint Vesta.curve)
    (hlr : List.Forall₂ (PairReads IpaEndo.vesta.d.W V) inp.lr (lrW.toList.map fun q =>
      ((SWPoint.equivPoint Vesta.curve) q.1, (SWPoint.equivPoint Vesta.curve) q.2)))
    (hlrne : inp.lr ≠ [])
    (hδ : OnCurveAt IpaEndo.vesta.d.W V inp.delta ((SWPoint.equivPoint Vesta.curve) δW))
    (hsg : OnCurveAt IpaEndo.vesta.d.W V inp.sg ((SWPoint.equivPoint Vesta.curve) sgW))
    (hh : OnCurveAt IpaEndo.vesta.d.W V inp.blindingGenerator
      ((SWPoint.equivPoint Vesta.curve) σ.h)) :
    ⦃⌜True⌝⦄ checkBulletproof (c := Builder V (KimchiConstraint Fq)) IpaScalarOps.wrap IpaEndo.vesta
      p endo groupMapParamsVesta sqrtF sv bases inp
    ⦃⇓ o _ => ⌜∃ (U : SWPoint Vesta.curve) (ns : List ℕ) (c₀ : ℕ) (zcip zb z₁ z₂ : ℤ)
        (chals : Vector Fp σ.k),
      (U = Poseidon.GroupMap.toGroup Poseidon.GroupMapVesta.spec (o.t.val V) ∨
        U = -Poseidon.GroupMap.toGroup Poseidon.GroupMapVesta.spec (o.t.val V)) ∧
      List.Forall₂ (Reads128 V) o.challenges ns ∧ Reads128 V o.c c₀ ∧
      chals.toList = ns.map (endoExpand Poseidon.FqVesta.spec.lam) ∧
      WrapLadderPre V inp.combinedInnerProduct zcip ∧ WrapLadderPre V inp.b zb ∧
      WrapLadderPre V inp.z1 z₁ ∧ WrapLadderPre V inp.z2 z₂ ∧
      ((↑o.success : CVar Fq).val V = 1 ↔
        schnorrAt IpaVesta.curve σ U chals (endoExpand Poseidon.FqVesta.spec.lam c₀)
          (wrapLadderDec zcip : Fp) (wrapLadderDec zb : Fp)
          (combineCommitments IpaVesta.curve (endoExpand Poseidon.FqVesta.spec.lam n)
            ((bvW.filter (·.2)).map (·.1)).toArray)
          ⟨lrW, δW, (wrapLadderDec z₁ : Fp), (wrapLadderDec z₂ : Fp), sgW⟩)⌝⦄ := by
  refine builder_spec_imp _ _ _
    (checkBulletproof_spec_success IpaScalarOps.wrap IpaEndo.vesta p hsize endo
      groupMapParamsVesta sqrtF fq_natCast_inj (WrapLadderPre V) WrapLadderReg wrapLadderDec
      (fun t => SWPoint.equivPoint Vesta.curve
        (Poseidon.GroupMap.toGroup Poseidon.GroupMapVesta.spec t)) (vesta_groupMap_reads sqrtF)
      sv bases _ hb hbne inp (fun pt x _ => wrap_scale_reads pt x)
      (fun x z hx hpre => HasCurve.vesta_ladderRegime _ (hband x z hx hpre))
      n hn hxi _ _ _ _ hlr hlrne hδ hsg hh) fun o ho => ?_
  obtain ⟨U, ns, c₀, wcip, wb, w₁, w₂, hU, hns, hlen, hc, hpcip, hpb, hp1, hp2, hiff⟩ := ho
  have hlen' : ns.length = σ.k := by rw [hlen, List.length_map, Vector.length_toList]
  refine ⟨(SWPoint.equivPoint Vesta.curve).symm U, ns, c₀, wcip, wb, w₁, w₂,
    ⟨(ns.map (endoExpand Poseidon.FqVesta.spec.lam)).toArray, by simp [hlen']⟩, ?_, hns, hc,
    by simp, hpcip, hpb, hp1, hp2, ?_⟩
  · beta_reduce at hU
    generalize Poseidon.GroupMap.toGroup Poseidon.GroupMapVesta.spec (CVar.val o.t V) = T at hU ⊢
    rcases hU with h | h
    · left; rw [h, AddEquiv.symm_apply_apply]
    · right
      rw [h]
      exact (congrArg (SWPoint.equivPoint Vesta.curve).symm
        (map_neg (SWPoint.equivPoint Vesta.curve) T).symm).trans (AddEquiv.symm_apply_apply _ _)
  · rw [hiff, ← schnorrPoint_iff_schnorrAt_vesta σ _ _ _ c₀ _ _ _ _ ⟨lrW, δW, _, _, sgW⟩ ns
      (by simp) rfl rfl]
    simp only [AddEquiv.apply_symm_apply]
    rw [← vesta_hornerCombine_eq n bvW hlast, AddEquiv.apply_symm_apply]
    exact Iff.rfl

end DeployedWrap

section TransportPallas

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass Poseidon.FqSponge
open Kimchi.Gate.EndoScalar Bulletproof Bulletproof.Ipa

/-- The Pallas point group is killed by its order. -/
private theorem pallas_card_nsmul (X : Pallas.curve.toAffine.Point) : PALLAS_SCALAR_CARD • X = 0 :=
  ZModModule.char_nsmul_eq_zero (n := PALLAS_SCALAR_CARD) X

/-- An integer acts on Pallas points as its residue's representative in the scalar field. -/
private theorem pallas_zsmul_eq (z : ℤ) (X : Pallas.curve.toAffine.Point) :
    z • X = ((z : Fq).val : ℕ) • X :=
  zsmul_eq_val_nsmul PALLAS_SCALAR_CARD pallas_card_nsmul z X

/-- The gadgets' integer endo-expansion at Pallas's eigenvalue casts to the wire's. -/
private theorem pallas_endoExpandZ_cast (n : ℕ) :
    ((endoExpandZ Pasta.pallasLam n : ℤ) : Fq) = endoExpand Poseidon.FqPallas.spec.lam n :=
  endoExpandZ_cast (by decide) (by decide) Pasta.pallasLam n

/-- A round term of `lr_prod`, read back in the wire group, is the wire's round term at the
expanded challenge. -/
private theorem pallas_lrTerm_eq (q : SWPoint Pallas.curve × SWPoint Pallas.curve) (n : ℕ) :
    (SWPoint.equivPoint Pallas.curve).symm
        (lrTerm Pasta.pallasLam ((SWPoint.equivPoint Pallas.curve) q.1,
          (SWPoint.equivPoint Pallas.curve) q.2) n)
      = ((endoExpand Poseidon.FqPallas.spec.lam n)⁻¹).val • q.1
        + (endoExpand Poseidon.FqPallas.spec.lam n).val • q.2 := by
  unfold lrTerm
  rw [map_add]
  rw [map_nsmul, map_zsmul]
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  rw [zmod_inv_val_congr _ PALLAS_SCALAR_CARD Pasta.pallas_card]
  rw [pallas_endoExpandZ_cast]
  rw [zsmul_eq_val_nsmul PALLAS_SCALAR_CARD
    (fun X => ZModModule.char_nsmul_eq_zero (n := PALLAS_SCALAR_CARD) X), pallas_endoExpandZ_cast]

/-- The round terms of `lr_prod`, read back in the wire group, are the wire's round terms at
the expanded challenges. -/
private theorem pallas_zipTerms :
    ∀ (l : List (SWPoint Pallas.curve × SWPoint Pallas.curve)) (ns : List ℕ),
      (List.zipWith (lrTerm Pasta.pallasLam)
        (l.map fun q =>
          ((SWPoint.equivPoint Pallas.curve) q.1, (SWPoint.equivPoint Pallas.curve) q.2)) ns).map
        (SWPoint.equivPoint Pallas.curve).symm
      = (l.zip (ns.map (endoExpand Poseidon.FqPallas.spec.lam))).map
          fun x => (x.2⁻¹).val • x.1.1 + x.2.val • x.1.2
  | [], _ => by simp
  | _ :: _, [] => by simp
  | q :: l, n :: ns => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.zip_cons_cons, pallas_lrTerm_eq]
    exact congrArg _ (pallas_zipTerms l ns)

/-- The wire's polyscale combination is Horner's rule over the list, the scalar acting by
its representative. -/
private theorem combineCommitments_eq_foldr_pallas (ξ : Fq) (cs : List (SWPoint Pallas.curve)) :
    combineCommitments IpaPallas.curve ξ cs.toArray
      = cs.foldr (fun P acc => P + ξ.val • acc) 0 := by
  have hn : ∀ x : SWPoint Pallas.curve, PALLAS_SCALAR_CARD • x = 0 := fun x =>
    ZModModule.char_nsmul_eq_zero (n := PALLAS_SCALAR_CARD) x
  have key : ∀ (l : List (SWPoint Pallas.curve)) (acc : SWPoint Pallas.curve) (pw : Fq),
      (l.foldl (fun (acc : SWPoint Pallas.curve × Fq) P => (acc.1 + acc.2.val • P, acc.2 * ξ))
        (acc, pw)).1 = acc + pw.val • l.foldr (fun P acc => P + ξ.val • acc) 0 := by
    intro l
    induction l with
    | nil => intro acc pw; simp
    | cons P l ih =>
      intro acc pw
      rw [List.foldl_cons, ih, List.foldr_cons, nsmul_add, val_mul_nsmul PALLAS_SCALAR_CARD hn,
        _root_.add_assoc]
  unfold combineCommitments
  rw [← Array.foldl_toList, List.toList_toArray, key, ZMod.val_one, one_nsmul, _root_.zero_add]
/-- Horner's rule over the kept bases, read back in the wire group, is the wire's polyscale
combination at the expanded challenge. -/
private theorem pallas_hornerCombine_eq (n : ℕ) (bvW : List (SWPoint Pallas.curve × Bool))
    (hlast : ∀ h, bvW.getLast? = some h → h.2 = true) :
    (SWPoint.equivPoint Pallas.curve).symm
        (hornerCombine (endoExpandZ Pasta.pallasLam n)
          (bvW.map fun b => ((SWPoint.equivPoint Pallas.curve) b.1, b.2)))
      = combineCommitments IpaPallas.curve (endoExpand Poseidon.FqPallas.spec.lam n)
          ((bvW.filter (·.2)).map (·.1)).toArray := by
  have hn : ∀ x : SWPoint Pallas.curve, PALLAS_SCALAR_CARD • x = 0 := fun x =>
    ZModModule.char_nsmul_eq_zero (n := PALLAS_SCALAR_CARD) x
  have hlast' : ∀ h, (bvW.map fun b => ((SWPoint.equivPoint Pallas.curve) b.1, b.2)).getLast?
      = some h → h.2 = true := by
    intro h hh
    rw [List.getLast?_map] at hh
    rcases hl : bvW.getLast? with _ | g
    · rw [hl] at hh; cases hh
    · rw [hl] at hh
      simp only [Option.map_some, Option.some.injEq] at hh
      rw [← hh]
      exact hlast g hl
  rw [hornerCombine_eq_foldr _ _ hlast', combineCommitments_eq_foldr_pallas]
  have hfl : (bvW.map fun b => ((SWPoint.equivPoint Pallas.curve) b.1, b.2)).filter (·.2)
      = (bvW.filter (·.2)).map fun b => ((SWPoint.equivPoint Pallas.curve) b.1, b.2) := by
    rw [List.filter_map]; rfl
  have hm : ((·.1) ∘ fun b : SWPoint Pallas.curve × Bool =>
      ((SWPoint.equivPoint Pallas.curve) b.1, b.2))
        = (SWPoint.equivPoint Pallas.curve) ∘ (·.1) := rfl
  rw [hfl, List.map_map, hm, ← List.map_map, ← pallas_endoExpandZ_cast]
  generalize (bvW.filter (·.2)).map (·.1) = cs
  generalize endoExpandZ Pasta.pallasLam n = z
  induction cs with
  | nil => simp
  | cons P cs ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, map_add, map_zsmul, ih,
      AddEquiv.symm_apply_apply, zsmul_eq_val_nsmul PALLAS_SCALAR_CARD hn]

/-- The bridge: the gadgets' Schnorr equation over Mathlib's Pallas point group, at the
readings' images under `SWPoint.equivPoint`, is the wire verifier's `schnorrAt` at the
expanded challenges and the cast scalars. -/
theorem schnorrPoint_iff_schnorrAt_pallas (σ : SRS (SWPoint Pallas.curve))
    (U P : SWPoint Pallas.curve)
    (chals : Vector Fq σ.k) (c₀ : ℕ) (cip b z₁ z₂ : ℤ) (pr : Ipa.Proof IpaPallas.curve σ.k)
    (ns : List ℕ) (hchals : chals.toList = ns.map (endoExpand Poseidon.FqPallas.spec.lam))
    (hz1 : pr.z1 = (z₁ : Fq)) (hz2 : pr.z2 = (z₂ : Fq)) :
    SchnorrPoint Pasta.pallasLam c₀ (SWPoint.equivPoint Pallas.curve U)
        (SWPoint.equivPoint Pallas.curve P)
        (lrSum (List.zipWith (lrTerm Pasta.pallasLam) (pr.lr.toList.map fun q =>
          ((SWPoint.equivPoint Pallas.curve) q.1, (SWPoint.equivPoint Pallas.curve) q.2)) ns))
        (SWPoint.equivPoint Pallas.curve pr.delta) (SWPoint.equivPoint Pallas.curve pr.sg)
        (SWPoint.equivPoint Pallas.curve σ.h) cip b z₁ z₂
      ↔ schnorrAt IpaPallas.curve σ U chals (endoExpand Poseidon.FqPallas.spec.lam c₀) (cip : Fq)
          (b : Fq) P pr := by
  have hsm : ∀ (z : ℤ) (X : Pallas.curve.toAffine.Point), z • X = ((z : Fq).val : ℕ) • X :=
    pallas_zsmul_eq
  have hzip := pallas_zipTerms pr.lr.toList ns
  -- the wire's fold as a start plus a sum
  have hfold : ∀ (l : List ((SWPoint Pallas.curve × SWPoint Pallas.curve) × Fq))
      (init : SWPoint Pallas.curve),
      l.foldl (fun acc (LRu : (SWPoint Pallas.curve × SWPoint Pallas.curve) × Fq) =>
        acc + ((LRu.2⁻¹).val • LRu.1.1 + LRu.2.val • LRu.1.2)) init
        = init + (l.map fun x => (x.2⁻¹).val • x.1.1 + x.2.val • x.1.2).sum := by
    intro l init
    rw [← List.foldl_map, foldl_add_eq]
  unfold SchnorrPoint schnorrAt
  dsimp only
  rw [hz1, hz2, ← Array.foldl_toList, Array.toList_zip, hfold]
  have hl1 : pr.lr.toArray.toList = pr.lr.toList := rfl
  have hl2 : chals.toArray.toList = ns.map (endoExpand Poseidon.FqPallas.spec.lam) := hchals
  rw [hl1, hl2]
  have hZ : List.zipWith (lrTerm Pasta.pallasLam) (List.map (fun q =>
        ((SWPoint.equivPoint Pallas.curve) q.1, (SWPoint.equivPoint Pallas.curve) q.2))
          pr.lr.toList) ns
      = ((pr.lr.toList.zip (ns.map (endoExpand Poseidon.FqPallas.spec.lam))).map
          fun x => (x.2⁻¹).val • x.1.1 + x.2.val • x.1.2).map
            (SWPoint.equivPoint Pallas.curve) := by
    rw [← hzip, List.map_map]
    simp only [Function.comp_def, AddEquiv.apply_symm_apply, List.map_id']
  have key1 : (SWPoint.equivPoint Pallas.curve) ((endoExpand Poseidon.FqPallas.spec.lam c₀).val •
        (P + (cip : Fq).val • U + ((pr.lr.toList.zip
          (ns.map (endoExpand Poseidon.FqPallas.spec.lam))).map
            fun x => (x.2⁻¹).val • x.1.1 + x.2.val • x.1.2).sum) + pr.delta)
      = endoExpandZ Pasta.pallasLam c₀ • ((SWPoint.equivPoint Pallas.curve) P +
          cip • (SWPoint.equivPoint Pallas.curve) U +
          lrSum (List.zipWith (lrTerm Pasta.pallasLam) (List.map (fun q =>
            ((SWPoint.equivPoint Pallas.curve) q.1, (SWPoint.equivPoint Pallas.curve) q.2))
              pr.lr.toList) ns)) + (SWPoint.equivPoint Pallas.curve) pr.delta := by
    rw [hZ, lrSum_eq_sum, ← map_list_sum, map_add, map_nsmul, map_add, map_add, map_nsmul,
      hsm (endoExpandZ _ _), pallas_endoExpandZ_cast, hsm cip]
  have key2 : (SWPoint.equivPoint Pallas.curve)
        ((z₁ : Fq).val • pr.sg + ((z₁ : Fq) * (b : Fq)).val • U + (z₂ : Fq).val • σ.h)
      = z₁ • ((SWPoint.equivPoint Pallas.curve) pr.sg + b • (SWPoint.equivPoint Pallas.curve) U)
        + z₂ • (SWPoint.equivPoint Pallas.curve) σ.h := by
    rw [map_add, map_add, map_nsmul, map_nsmul, map_nsmul, smul_add, ← mul_zsmul, hsm z₁,
      hsm (z₁ * b), hsm z₂, Int.cast_mul]
  rw [← key1, ← key2]
  exact (SWPoint.equivPoint Pallas.curve).injective.eq_iff

end TransportPallas

section DeployedStep

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass Poseidon.FqSponge
open Kimchi.Gate.EndoScalar Kimchi.Gate.VarBaseMul Bulletproof Bulletproof.Ipa Pasta.Shifted

/-- Naturals below `2¹²⁸` cast injectively into `Fp`. -/
private theorem fp_natCast_inj (a b : ℕ) (ha : a < 2 ^ 128) (hb : b < 2 ^ 128)
    (h : (a : Fp) = b) : a = b := by
  have h' := (ZMod.natCast_eq_natCast_iff' a b _).mp h
  rwa [Nat.mod_eq_of_lt (lt_trans ha (by decide)), Nat.mod_eq_of_lt (lt_trans hb (by decide))] at h'

/-- **The step side's `check_bulletproof` at the wire.** Under any valuation satisfying the
emitted constraints — the bases reading as Pallas points (the last kept), the pairs, `δ`, `sg`
and `h` as points, the parity bits reading as bits, the ladder witnesses' halves off the
forbidden band — the challenges read as some `ns`, `c` as some `c₀`, the four split `Type2`
scalars through witnesses (a parity bit and a half below `2²⁵⁴`), and the success bit reads
`1` exactly when the wire verifier's `schnorrAt` holds at `IpaPallas.curve`:
the `U` base the deployed map-to-curve's point or its negation, the challenges the
endo-expansions of `ns`, the combined commitment `combineCommitments` over the kept bases at
the expanded `ξ`, and `cip`, `b`, `z₁`, `z₂` the witnesses' `Type2` decodes cast to `Fq`.
With `verifyWith_eq`, `success ∧ sg = ⟨bPolyCoefficients chals, g⟩` is `verifyWith` at those
readings. -/
theorem checkBulletproof_step_spec {V : Valuation Fp}
    (p : Poseidon.Params Fp) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (endo : FVar Fp) (sqrtF : Fp → Option Fp) (sv : SpongeVar Fp)
    (bases : List (AffinePoint (FVar Fp) × Option (BoolVar Fp)))
    (bvW : List (SWPoint Pallas.curve × Bool))
    (hb : List.Forall₂ (MaskedBaseReads IpaEndo.pallas.d.W V) bases
      (bvW.map fun b => ((SWPoint.equivPoint Pallas.curve) b.1, b.2)))
    (hbne : bases ≠ []) (hlast : ∀ h, bvW.getLast? = some h → h.2 = true)
    (inp : CheckBulletproofInput Fp (Type2 (SplitField (FVar Fp) (BoolVar Fp))))
    (hbits : ∀ x ∈ inp.scaled, ∃ bb : Bool, (↑x.val.sOdd : CVar Fp).val V = bit bb)
    (hband : ∀ (x : Type2 (SplitField (FVar Fp) (BoolVar Fp))) (w : ℤ × Bool), x ∈ inp.scaled →
      StepLadderPre V x w → unshiftType1 255 w.1 ∉ forbiddenValues PALLAS_SCALAR_CARD)
    (n : ℕ) (hn : n < 2 ^ 128) (hxi : inp.xi.val.val V = n)
    (σ : SRS (SWPoint Pallas.curve))
    (lrW : Vector (SWPoint Pallas.curve × SWPoint Pallas.curve) σ.k) (δW sgW : SWPoint Pallas.curve)
    (hlr : List.Forall₂ (PairReads IpaEndo.pallas.d.W V) inp.lr (lrW.toList.map fun q =>
      ((SWPoint.equivPoint Pallas.curve) q.1, (SWPoint.equivPoint Pallas.curve) q.2)))
    (hlrne : inp.lr ≠ [])
    (hδ : OnCurveAt IpaEndo.pallas.d.W V inp.delta ((SWPoint.equivPoint Pallas.curve) δW))
    (hsg : OnCurveAt IpaEndo.pallas.d.W V inp.sg ((SWPoint.equivPoint Pallas.curve) sgW))
    (hh : OnCurveAt IpaEndo.pallas.d.W V inp.blindingGenerator
      ((SWPoint.equivPoint Pallas.curve) σ.h)) :
    ⦃⌜True⌝⦄ checkBulletproof (c := Builder V (KimchiConstraint Fp)) IpaScalarOps.step
      IpaEndo.pallas p endo groupMapParamsPallas sqrtF sv bases inp
    ⦃⇓ o _ => ⌜∃ (U : SWPoint Pallas.curve) (ns : List ℕ) (c₀ : ℕ) (zcip zb z₁ z₂ : ℤ × Bool)
        (chals : Vector Fq σ.k),
      (U = Poseidon.GroupMap.toGroup Poseidon.GroupMapPallas.spec (o.t.val V) ∨
        U = -Poseidon.GroupMap.toGroup Poseidon.GroupMapPallas.spec (o.t.val V)) ∧
      List.Forall₂ (Reads128 V) o.challenges ns ∧ Reads128 V o.c c₀ ∧
      chals.toList = ns.map (endoExpand Poseidon.FqPallas.spec.lam) ∧
      StepLadderPre V inp.combinedInnerProduct zcip ∧ StepLadderPre V inp.b zb ∧
      StepLadderPre V inp.z1 z₁ ∧ StepLadderPre V inp.z2 z₂ ∧
      ((↑o.success : CVar Fp).val V = 1 ↔
        schnorrAt IpaPallas.curve σ U chals (endoExpand Poseidon.FqPallas.spec.lam c₀)
          (stepLadderDec zcip : Fq) (stepLadderDec zb : Fq)
          (combineCommitments IpaPallas.curve (endoExpand Poseidon.FqPallas.spec.lam n)
            ((bvW.filter (·.2)).map (·.1)).toArray)
          ⟨lrW, δW, (stepLadderDec z₁ : Fq), (stepLadderDec z₂ : Fq), sgW⟩)⌝⦄ := by
  refine builder_spec_imp _ _ _
    (checkBulletproof_spec_success IpaScalarOps.step IpaEndo.pallas p hsize endo
      groupMapParamsPallas sqrtF fp_natCast_inj (StepLadderPre V) StepLadderReg stepLadderDec
      (fun t => SWPoint.equivPoint Pallas.curve
        (Poseidon.GroupMap.toGroup Poseidon.GroupMapPallas.spec t)) (pallas_groupMap_reads sqrtF)
      sv bases _ hb hbne inp
      (fun pt x hx => (hbits x hx).elim fun bb hbit => step_scale_reads pt x bb hbit)
      (fun x w hx hpre => HasCurve.pallas_ladderRegime _ (hband x w hx hpre))
      n hn hxi _ _ _ _ hlr hlrne hδ hsg hh) fun o ho => ?_
  obtain ⟨U, ns, c₀, wcip, wb, w₁, w₂, hU, hns, hlen, hc, hpcip, hpb, hp1, hp2, hiff⟩ := ho
  have hlen' : ns.length = σ.k := by rw [hlen, List.length_map, Vector.length_toList]
  refine ⟨(SWPoint.equivPoint Pallas.curve).symm U, ns, c₀, wcip, wb, w₁, w₂,
    ⟨(ns.map (endoExpand Poseidon.FqPallas.spec.lam)).toArray, by simp [hlen']⟩, ?_, hns, hc,
    by simp, hpcip, hpb, hp1, hp2, ?_⟩
  · beta_reduce at hU
    generalize Poseidon.GroupMap.toGroup Poseidon.GroupMapPallas.spec (CVar.val o.t V) = T at hU ⊢
    rcases hU with h | h
    · left; rw [h, AddEquiv.symm_apply_apply]
    · right
      rw [h]
      exact (congrArg (SWPoint.equivPoint Pallas.curve).symm
        (map_neg (SWPoint.equivPoint Pallas.curve) T).symm).trans (AddEquiv.symm_apply_apply _ _)
  · rw [hiff, ← schnorrPoint_iff_schnorrAt_pallas σ _ _ _ c₀ _ _ _ _ ⟨lrW, δW, _, _, sgW⟩ ns
      (by simp) rfl rfl]
    simp only [AddEquiv.apply_symm_apply]
    rw [← pallas_hornerCombine_eq n bvW hlast, AddEquiv.apply_symm_apply]
    exact Iff.rfl

end DeployedStep

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
