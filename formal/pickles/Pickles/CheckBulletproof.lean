import Pickles.FqSpongeTranscript
import Snarky.Kimchi.Circuit.EndoMul
import Snarky.Kimchi.Circuit.VarBaseMul
import Snarky.Kimchi.Circuit.GroupMap
import Snarky.Types.Shifted

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
  `checkBulletproof`: the gadgets, in PS's emission order.
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

/-- Absorb a shifted scalar's limbs, left to right (OCaml `absorb_shifted`). -/
def absorbShifted (p : Poseidon.Params F) :
    SpongeVar F → List (FVar F) → CircuitM F c (SpongeVar F)
  | sv, [] => pure sv
  | sv, x :: xs => do
    let sv' ← SpongeVar.absorb p sv x
    absorbShifted p sv' xs

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

/-- The challenge fold `lr_prod` (PS `bulletReduceCircuit`, `bullet_reduce`'s second pass):
per pair `endoInv(L, u) + endo(R, u)`, then the running sum. Empty input yields the
origin. -/
def bulletReduce (e : IpaEndo F)
    (pairs : List ((AffinePoint (FVar F) × AffinePoint (FVar F)) × SizedF 128 (FVar F))) :
    CircuitM F c (AffinePoint (FVar F)) := do
  let terms ← pairs.mapM fun q => do
    let lScaled ← endoInv e.d.endo e.d.W e.q e.hq e.lam q.1.1 q.2
    let rScaled ← endoMul e.d.endo 32 q.1.2 q.2
    (·.p) <$> addFast .checkFinite lScaled rScaled
  match terms with
  | [] => pure ⟨.const 0, .const 0⟩
  | h :: t => t.foldlM (fun acc q => (·.p) <$> addFast .checkFinite acc q) h

/-- Select a point by a bit (PS `if_` at `AffinePoint`, OCaml's reverse array order): `y`
then `x`. -/
def selectPoint (b : BoolVar F) (t e : AffinePoint (FVar F)) :
    CircuitM F c (AffinePoint (FVar F)) := do
  let y ← selectField b t.y e.y
  let x ← selectField b t.x e.x
  pure ⟨x, y⟩

/-- The polyscale combination of the commitment bases (PS `combinePolynomials`, OCaml
`Split_commitments.combine`): Horner from the last base, `acc ← base + ξ·acc`, a masked
base kept or skipped by its bit — skipped without consuming a power of `ξ`. Empty input
yields the origin. -/
def combinePolynomials (e : IpaEndo F) (xi : SizedF 128 (FVar F))
    (bases : List (AffinePoint (FVar F) × Option (BoolVar F))) :
    CircuitM F c (AffinePoint (FVar F)) :=
  match bases.reverse with
  | [] => pure ⟨.const 0, .const 0⟩
  | h :: t =>
    t.foldlM
      (fun acc bm => do
        let xiAcc ← endoMul e.d.endo 32 acc xi
        let r ← addFast .checkFinite bm.1 xiAcc
        match bm.2 with
        | none => pure r.p
        | some keep => selectPoint keep r.p acc)
      h.1

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
  let sv ← absorbShifted p sv (ops.shiftedToAbsorbFields inp.combinedInnerProduct)
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

omit [ToNat F] in
/-- Under any valuation satisfying the emitted constraints, absorbing limbs reads as
absorbing their values. -/
theorem absorbShifted_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) :
    ∀ (sv : SpongeVar F) (limbs : List (FVar F)),
      ⦃⌜True⌝⦄ absorbShifted (c := Builder V (KimchiConstraint F)) p sv limbs
      ⦃⇓ r _ => ⌜∀ s, SpongeVar.ReadsAt V sv s →
        SpongeVar.ReadsAt V r (Poseidon.absorb p s (limbs.map (·.val V)))⌝⦄
  | sv, [] => by
    simp only [absorbShifted]
    mvcgen
    intro s hs
    simpa [Poseidon.absorb] using hs
  | sv, x :: xs => by
    simp only [absorbShifted]
    have hx := SpongeVar.absorb_spec (V := V) p hsize sv x
    have ih := fun sv' => absorbShifted_spec p hsize sv' xs
    mvcgen [hx, ih]
    rename_i _ _ _ hstep _ _
    intro hrest s hs
    simpa [Poseidon.absorb] using hrest _ (hstep s hs)

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
  have hlimbs := absorbShifted_spec (V := V) p hsize sv
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
