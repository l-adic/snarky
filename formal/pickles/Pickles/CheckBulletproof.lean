import Pickles.FqSpongeTranscript
import Snarky.Kimchi.Circuit.EndoMul
import Snarky.Kimchi.Circuit.VarBaseMul
import Snarky.Kimchi.Circuit.GroupMap
import Snarky.Types.Shifted
import Snarky.Kimchi.Circuit.Point
import Pickles.FrSponge
import Pickles.Prechallenge
import Pickles.Curve
import Pickles.ListLemmas

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
  {k : ℕ}

/-- A side's shifted-scalar handling (PS `IpaScalarOps`): scaling a point by a shifted
scalar, and the limbs a shifted scalar absorbs as (OCaml `absorb_shifted`). -/
structure IpaScalarOps (F c sf : Type) where
  /-- Scale a point by the shifted scalar (PS `scaleByShifted`). -/
  scaleByShifted : AffinePoint (FVar F) → sf → CircuitM F c (AffinePoint (FVar F))
  /-- Scale a point by the claimed combined inner product, the one shifted scalar the
  transcript absorbs (PS `scaleByCip`): on the step side the ladder one bit narrower, so the
  absorbed cells are the canonical representative's; on the wrap side `scaleByShifted`. -/
  scaleByCip : AffinePoint (FVar F) → sf → CircuitM F c (AffinePoint (FVar F))
  /-- The limbs the shifted scalar absorbs as (PS `shiftedToAbsorbFields`). -/
  shiftedToAbsorbFields : sf → List (FVar F)

/-- The wrap side's operations (PS `Pickles.Wrap.OtherField.ipaScalarOps`): `scaleFast1`
at 51 chunks over the `Type1` representative, absorbed as one limb. -/
def IpaScalarOps.wrap : IpaScalarOps F c (Type1 (FVar F)) where
  scaleByShifted p t := scaleFast1 255 51 p t
  scaleByCip p t := scaleFast1 255 51 p t
  shiftedToAbsorbFields t := [t.val]

/-- The step side's operations (PS `Pickles.Step.OtherField.ipaScalarOps`): `scaleFast2`
at 51 chunks and 254 halved bits over the `Type2` split representative, absorbed as the
halved limb then the parity bit. -/
def IpaScalarOps.step : IpaScalarOps F c (Type2 (SplitField (FVar F) (BoolVar F))) where
  scaleByShifted p t := scaleFast2 255 51 254 p t.val.sDiv2 t.val.sOdd
  scaleByCip p t := scaleFast2 255 51 253 p t.val.sDiv2 t.val.sOdd
  shiftedToAbsorbFields t := [t.val.sDiv2, (↑t.val.sOdd : CVar F)]

/-- A side's endomorphism data with the scalar field named: the `HasEndo`, and the group order
as a numeral, which the `endoInv` witness needs and `W.order` cannot supply. Only the numeral
is data — its primality and the eigenvalue's residue follow from the dictionary, so the numeral
cannot silently name a group other than the curve's. -/
structure IpaEndo (F : Type) [Field F] [DecidableEq F] where
  /-- The curve, endomorphism coefficient and eigenvalue. -/
  d : HasEndo F
  /-- The group order, as a numeral. -/
  q : ℕ
  /-- The numeral is the curve's group order. -/
  q_eq : q = d.W.order

omit [Field F] [DecidableEq F] [ToNat F] in
/-- The order is prime, by the dictionary. -/
theorem IpaEndo.hq [Field F] [DecidableEq F] (e : IpaEndo F) : e.q.Prime := e.q_eq ▸ e.d.prime

/-- The eigenvalue in the scalar field. -/
def IpaEndo.lam [Field F] [DecidableEq F] (e : IpaEndo F) : ZMod e.q := ((e.d.lam : ℤ) : ZMod e.q)

/-- The step side's data: Pallas over `Fp`. -/
def IpaEndo.pallas : IpaEndo Fp where
  d := pastaShapePallas.e
  q := PALLAS_SCALAR_CARD
  q_eq := (Bulletproof.Ipa.CommitmentCurve.order_eq
    Bulletproof.IpaPallas.curve.toCommitmentCurve).symm

/-- The wrap side's data: Vesta over `Fq`. -/
def IpaEndo.vesta : IpaEndo Fq where
  d := pastaShapeVesta.e
  q := PALLAS_BASE_CARD
  q_eq := (Bulletproof.Ipa.CommitmentCurve.order_eq
    Bulletproof.IpaVesta.curve.toCommitmentCurve).symm

/-- The two deferred scalars of the opening check (PS `BulletproofDeferred`; OCaml
`Types.Step.Bulletproof.Advice`, a name not used here because in snarky and pickles
"advice" is the prover-side handler mechanism, whereas these are public input of the previous
proof): used in the Schnorr equation here, certified by the next circuit's
`finalizeOtherProof`. -/
structure BulletproofDeferred (sf : Type) where
  /-- The deferred combined inner product, shifted. -/
  combinedInnerProduct : sf
  /-- The deferred challenge-polynomial evaluation `b`, shifted. -/
  b : sf

/-- The opening proof as the circuit reads it (PS `BulletproofOpening`, OCaml
`Openings.Bulletproof.t`; the wire's `Ipa.Proof` with shifted scalars): checked in the Schnorr
equation here. Only `sg` is looked at again, one proof later, as `sg_old`. -/
structure BulletproofOpening (k : ℕ) (f sf : Type) where
  /-- The `(L, R)` pairs, one per round. -/
  lr : Vector (AffinePoint f × AffinePoint f) k
  /-- The opening's `z₁`, shifted. -/
  z1 : sf
  /-- The opening's `z₂`, shifted. -/
  z2 : sf
  /-- The opening's `δ`. -/
  delta : AffinePoint f
  /-- The opening's challenge polynomial commitment `sg`. -/
  sg : AffinePoint f

/-- What `check_bulletproof` consumes (PS `CheckBulletproofInput`): the deferred `ξ`, the
deferred `cip` and `b`, the opening proof, and the SRS blinding base `h`. -/
structure CheckBulletproofInput (k : ℕ) (f sf : Type) where
  /-- The polyscale challenge `ξ`, 128 bits — a deferred value. -/
  xi : SizedF 128 f
  /-- The deferred `cip` and `b`. -/
  deferred : BulletproofDeferred sf
  /-- The opening proof. -/
  opening : BulletproofOpening k f sf
  /-- The SRS blinding base `h`. -/
  blindingGenerator : AffinePoint f

/-- The four scalars the check scales by: `cip`, `b`, `z₁`, `z₂`. -/
def CheckBulletproofInput.scaled {F sf : Type}
    (inp : CheckBulletproofInput k (FVar F) sf) : List sf :=
  [inp.deferred.combinedInnerProduct, inp.deferred.b, inp.opening.z1, inp.opening.z2]

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
    (u combinedPolynomial : AffinePoint (FVar F)) (inp : CheckBulletproofInput k (FVar F) sf) :
    CircuitM F c (CheckBulletproofOutput F) := do
  let (chals, sv) ← extractScalarChallenges p endo sv inp.opening.lr.toList
  let lrProd ← bulletReduce e (inp.opening.lr.toList.zip chals)
  let cipU ← ops.scaleByCip u inp.deferred.combinedInnerProduct
  let pPrime ← (·.p) <$> addFast .checkFinite combinedPolynomial cipU
  let q ← (·.p) <$> addFast .checkFinite pPrime lrProd
  let sv ← absorbPoint p sv inp.opening.delta
  let (cc, sv) ← squeezePrechallenge p false endo sv
  let cQ ← endoMul e.d.endo 32 q cc
  let lhs ← (·.p) <$> addFast .checkFinite cQ inp.opening.delta
  let bU ← ops.scaleByShifted u inp.deferred.b
  let sgPlusBU ← (·.p) <$> addFast .checkFinite inp.opening.sg bU
  let z1Term ← ops.scaleByShifted sgPlusBU inp.opening.z1
  let z2Term ← ops.scaleByShifted inp.blindingGenerator inp.opening.z2
  let rhs ← (·.p) <$> addFast .checkFinite z1Term z2Term
  let xEq ← equals lhs.x rhs.x
  let yEq ← equals lhs.y rhs.y
  let success ← Snarky.and xEq yEq
  pure ⟨success, chals, t, cc, sv⟩

/-- The sign flag's advice: whether the ordinate's representative lies in the upper half,
at or above `(p + 1) / 2`. -/
private def isUpperWit (y : FVar F) : AsProver F Bool := do
  let v ← AsProver.readCVar y
  pure (decide ((fieldModulus F + 1) / 2 ≤ ToNat.toNat v))

/-- The IPA base with its ordinate in the lower half (PS `lowerHalfPoint`, OCaml
`lower_half_point`): `(x, y')` with `y' = ±y` and `y'` split below `(p + 1) / 2`. The group
map leaves the square root's sign to the prover; the wire verifier takes the lower-half root
too. -/
def lowerHalfPoint (endo : FVar F) (pt : AffinePoint (FVar F)) :
    CircuitM F c (AffinePoint (FVar F)) := do
  let isUpper ← witness (val := Bool) (isUpperWit pt.y)
  let y ← select isUpper (CVar.scale_ (-1) pt.y) pt.y
  let _ ← split128Below true endo ((fieldModulus F + 1) / 2) y
  pure ⟨pt.x, y⟩

/-- The opening check (PS `checkBulletproof`, OCaml `check_bulletproof`): from the sponge at
`sponge_before_evaluations`, absorb the shifted `cip`, squeeze and map the `U` base, pin its
ordinate to the lower half, combine the bases by `ξ` under their masks, and run the final
check. -/
def checkBulletproof {sf : Type} (ops : IpaScalarOps F c sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F)
    (sv : SpongeVar F) (bases : List (AffinePoint (FVar F) × Option (BoolVar F)))
    (inp : CheckBulletproofInput k (FVar F) sf) : CircuitM F c (CheckBulletproofOutput F) := do
  let sv ← absorbList p sv (ops.shiftedToAbsorbFields inp.deferred.combinedInnerProduct)
  let (t, sv) ← SpongeVar.squeeze p sv
  let u' ← groupMapCircuit sqrtF gm t
  let u ← lowerHalfPoint endo u'
  let combined ← combinePolynomials e inp.xi bases
  ipaFinalCheck ops e p endo sv t u combined inp

/-! ## Soundness: the transcript -/

variable {V : Valuation F}

/-- Under any valuation satisfying the emitted constraints, `lowerHalfPoint` keeps the abscissa
and reads the ordinate as the input's or its negation. -/
theorem lowerHalfPoint_spec (endo : FVar F) (pt : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄ lowerHalfPoint (c := Builder V (KimchiConstraint F)) endo pt
    ⦃⇓ r _ => ⌜r.x = pt.x ∧ (r.y.val V = pt.y.val V ∨ r.y.val V = -pt.y.val V)⌝⦄ := by
  have hsplit := fun (b : ℕ) (y : FVar F) =>
    builder_spec_true (split128Below (c := Builder V (KimchiConstraint F)) true endo b y)
  simp only [lowerHalfPoint, select_fvar]
  mvcgen [hsplit]
  rename_i hb _ _ hsel _ _
  obtain ⟨bb, hbb⟩ := hb
  have hy := hsel bb hbb
  cases bb <;> simp [hy, CVar.val_scale_]

/-- The curve reading `lowerHalfPoint_spec` gives: the output reads as the input's point or
its negation, on a curve with `a₁ = a₃ = 0`. -/
private theorem lowerHalfPoint_onCurve (endo : FVar F)
    {W : WeierstrassCurve.Affine F} (ha : W.a₁ = 0 ∧ W.a₃ = 0) (pt : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄ lowerHalfPoint (c := Builder V (KimchiConstraint F)) endo pt
    ⦃⇓ r _ => ⌜∀ U : W.Point, OnCurveAt W V pt U →
      ∃ U' : W.Point, OnCurveAt W V r U' ∧ (U' = U ∨ U' = -U)⌝⦄ := by
  refine builder_spec_imp _ _ _ (lowerHalfPoint_spec endo pt) fun r hr U hU => ?_
  obtain ⟨hx, hy | hy⟩ := hr
  · exact ⟨U, by simpa only [OnCurveAt, hx, hy] using hU, Or.inl rfl⟩
  · exact ⟨-U, by simpa only [OnCurveAt, hx, hy, CVar.val_negate_] using OnCurveAt.neg ha hU,
      Or.inr rfl⟩

/-- Under any valuation satisfying the emitted constraints, where naturals below `2^130` cast
injectively and the modulus fits in 256 bits, `lowerHalfPoint`'s ordinate reads as a natural
below `(p + 1)/2` — the lower half the wire's `uBase` picks. -/
theorem lowerHalfPoint_below (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hinj : ∀ a b : ℕ, a < 2 ^ 130 → b < 2 ^ 130 → (a : F) = b → a = b)
    (hmod : fieldModulus F < 2 ^ 256) (endo : FVar F) (pt : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄ lowerHalfPoint (c := Builder V (KimchiConstraint F)) endo pt
    ⦃⇓ r _ => ⌜∃ m : ℕ, m < (fieldModulus F + 1) / 2 ∧ r.y.val V = m⌝⦄ := by
  have hb : (fieldModulus F + 1) / 2 < 2 ^ 256 := by omega
  have hsplit := fun (y : FVar F) => builder_spec_and _ _ _
    (split128Below_spec (V := V) h2 h3 true endo ((fieldModulus F + 1) / 2) y)
    (split128Below_below (V := V) h2 h3 hinj true endo _ hb y)
  simp only [lowerHalfPoint, select_fvar]
  mvcgen [hsplit]
  all_goals
    rename_i hs
    obtain ⟨⟨-, -, -, hlo⟩, hbelow⟩ := hs
    obtain ⟨n, hn, hnv⟩ := hlo
    obtain ⟨h, -, hy, hlt⟩ := hbelow n hn hnv
    exact ⟨n + 2 ^ 128 * h, hlt, by rw [hy]; push_cast; ring⟩

attribute [irreducible] lowerHalfPoint

/-- A pair of points' coordinates, the form `Bulletproof.Ipa.ipaSqueezes` takes. -/
def coordsPair (q : AffinePoint F × AffinePoint F) : (F × F) × (F × F) :=
  ((q.1.x, q.1.y), (q.2.x, q.2.y))

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
theorem extractScalarChallenges_spec (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hsw : SplitWidth F)
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
    have hpre := fun sv' => squeezePrechallenge_spec (V := V) h2 h3 hsw p hsize false endo sv'
    have ih := fun sv' => extractScalarChallenges_spec h2 h3 hsw p hsize endo sv' lr qs hqs
    mvcgen [hL, hR, hpre, ih]
    rename_i _ svA _ hA svB _ hB u _ hu rest _ hrest
    intro s hs
    have s1 := hA s hs
    have s2 := hB _ s1
    obtain ⟨hx, -, s3⟩ := hu _ s2
    obtain ⟨hall, s4⟩ := hrest _ s3
    simp only [hlx, hly, hrx, hry] at hx s3 hall s4
    simp only [List.map_cons, List.foldl_cons, ipaRound, coordsPair, List.nil_append]
    rw [ipaRound_foldl]
    exact ⟨List.Forall₂.cons hx hall, s4⟩

open Bulletproof.Ipa in
/-- Under any valuation satisfying the emitted constraints, with the sponge reading as `s₀`,
the pairs as `lrv` and `δ` as `δv`, the outputs satisfy `CheckBulletproofReads` at the
limbs' readings: the transcript half of `check_bulletproof`, against the wire verifier's
`ipaSqueezes`. -/
theorem checkBulletproof_spec (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hsw : SplitWidth F)
    {sf : Type}
    (ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F) (sv : SpongeVar F)
    (s₀ : Poseidon.State F) (hs : SpongeVar.ReadsAt V sv s₀)
    (bases : List (AffinePoint (FVar F) × Option (BoolVar F)))
    (inp : CheckBulletproofInput k (FVar F) sf)
    (lrv : List (AffinePoint F × AffinePoint F))
    (hlr : List.Forall₂ (CircuitType.Reads V) inp.opening.lr.toList lrv)
    (δv : AffinePoint F) (hδ : CircuitType.Reads V inp.opening.delta δv) :
    ⦃⌜True⌝⦄ checkBulletproof ops e p endo gm sqrtF sv bases inp
    ⦃⇓ o _ => ⌜CheckBulletproofReads p s₀
      ((ops.shiftedToAbsorbFields inp.deferred.combinedInnerProduct).map (·.val V))
      lrv δv V o⌝⦄ := by
  simp only [checkBulletproof, ipaFinalCheck]
  obtain ⟨hδx, hδy⟩ := reads_affinePoint.mp hδ
  have hlimbs := absorbList_spec (V := V) p hsize sv
    (ops.shiftedToAbsorbFields inp.deferred.combinedInnerProduct)
  have hsq := fun sv' => SpongeVar.squeeze_spec (V := V) p hsize sv'
  have hgm := fun t => builder_spec_true (groupMapCircuit (c := Builder V (KimchiConstraint F))
    sqrtF gm t)
  have hlh := fun pt => builder_spec_true
    (lowerHalfPoint (c := Builder V (KimchiConstraint F)) endo pt)
  have hcomb := fun xi bs => builder_spec_true
    (combinePolynomials (c := Builder V (KimchiConstraint F)) e xi bs)
  have hext := fun sv' =>
    extractScalarChallenges_spec (V := V) h2 h3 hsw p hsize endo sv' inp.opening.lr.toList lrv hlr
  have hbr := fun ps => builder_spec_true (bulletReduce (c := Builder V (KimchiConstraint F)) e ps)
  have hsc := fun u x => builder_spec_true (ops.scaleByShifted u x)
  have hscc := fun u x => builder_spec_true (ops.scaleByCip u x)
  have hadd := fun f a b => builder_spec_true (addFast (c := Builder V (KimchiConstraint F)) f a b)
  have hem := fun g x => builder_spec_true
    (endoMul (c := Builder V (KimchiConstraint F)) e.d.endo 32 g x)
  have hδs := fun sv' => absorbPoint_spec (V := V) p hsize sv' inp.opening.delta
  have hpre := fun sv' => squeezePrechallenge_spec (V := V) h2 h3 hsw p hsize false endo sv'
  have heq := fun a b => builder_spec_true (equals (c := Builder V (KimchiConstraint F)) a b)
  have hand := fun a b => builder_spec_true (Snarky.and (c := Builder V (KimchiConstraint F)) a b)
  mvcgen [hlimbs, hsq, hgm, hlh, hcomb, hext, hbr, hsc, hscc, hadd, hem, hδs, hpre, heq, hand]
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
  rename_i _ svL _ hL sqT _ hT _ _ u _ comb _ ext _ hext lrProd _ cipU _ pP _ _ q _ _ svD _ hD cP _
    hC cQ _ lhs _ _ bU _ sgBU _ _ z1T _ z2T _ rhs _ xEq _ _ yEq _ _ succ _ _ _
  have s1 := hL s₀ hs
  obtain ⟨htv, s2⟩ := hT _ s1
  obtain ⟨hchals, s3⟩ := hext _ s2
  have s4 := hD _ s3
  obtain ⟨hc, -, -⟩ := hC _ s4
  simp only [hδx, hδy] at hc
  unfold CheckBulletproofReads ipaSqueezes
  exact ⟨htv, hchals, hc⟩


/-- `checkBulletproof_spec` with the sponge, pair and `δ` readings quantified in the
postcondition — the shape an assembly hands `mvcgen` before the readings are in hand, stated
once here and never restated by a consumer (`scripts/check-spec-locality.sh`). -/
theorem checkBulletproof_reads (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hsw : SplitWidth F)
    {sf : Type}
    (ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (endo : FVar F) (gm : GroupMapParams F) (sqrtF : F → Option F) (sv : SpongeVar F)
    (bases : List (AffinePoint (FVar F) × Option (BoolVar F)))
    (inp : CheckBulletproofInput k (FVar F) sf) :
    ⦃⌜True⌝⦄ checkBulletproof ops e p endo gm sqrtF sv bases inp
    ⦃⇓ o _ => ⌜∀ (s₀ : Poseidon.State F) (lrv : List (AffinePoint F × AffinePoint F))
      (δv : AffinePoint F), SpongeVar.ReadsAt V sv s₀ →
      List.Forall₂ (CircuitType.Reads V) inp.opening.lr.toList lrv →
      CircuitType.Reads V inp.opening.delta δv →
      CheckBulletproofReads p s₀
        ((ops.shiftedToAbsorbFields inp.deferred.combinedInnerProduct).map (·.val V))
        lrv δv V o⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat s₀ lrv δv hs hlr hδ
  exact (builder_spec_iff _ _).mp (checkBulletproof_spec h2 h3 hsw ops e p hsize endo gm sqrtF sv s₀
    hs bases inp lrv hlr δv hδ) nv hsat

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
private theorem hornerFold_spec (e : IpaEndo F) (xi : SizedF 128 (FVar F)) (n : Prechallenge)
    (hxi : Reads128 V xi n)
    (hchar : CastInj128 F) :
    ∀ (acc : AffinePoint (FVar F)) (bases : List (AffinePoint (FVar F) × Option (BoolVar F)))
      (bv : List (e.d.W.Point × Bool)), List.Forall₂ (MaskedBaseReads e.d.W V) bases bv →
      ⦃⌜True⌝⦄ hornerFold (c := Builder V (KimchiConstraint F)) e xi acc bases
      ⦃⇓ r _ => ⌜∀ accv : e.d.W.Point, OnCurveAt e.d.W V acc accv →
        OnCurveAt e.d.W V r (bv.foldl (hornerStep (endoExpandZ e.d.lam n.val)) accv)⌝⦄
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
    have ih := fun acc' => hornerFold_spec e xi n hxi hchar acc' bases bv hrest
    cases mask with
    | none =>
      simp only at hmask
      subst hmask
      mvcgen [-Snarky.Kimchi.addFast_spec, hem, hadd, ih]
      rename_i _ xiAcc _ hxa r _ hr rr _
      intro hrest' accv hacc
      obtain ⟨n', hn', hxi', hxa'⟩ := hxa accv hacc
      obtain rfl : n' = n.val := hchar n' n.val hn' n.property (hxi'.symm.trans hxi)
      exact hrest' _ (by simpa [hornerStep] using hr bvp _ hpt hxa')
    | some keep =>
      simp only at hmask
      have hsel := fun r => select_affinePoint_spec (V := V) (c := KimchiConstraint F) keep r acc
      mvcgen [-Snarky.Kimchi.addFast_spec, hem, hadd, hsel, ih]
      rename_i _ xiAcc _ hxa r _ hr sel _ hsel' rr _
      intro hrest' accv hacc
      obtain ⟨n', hn', hxi', hxa'⟩ := hxa accv hacc
      obtain rfl : n' = n.val := hchar n' n.val hn' n.property (hxi'.symm.trans hxi)
      have hs := hsel' bb hmask _ _ (hr bvp _ hpt hxa') hacc
      refine hrest' _ ?_
      cases bb <;> simpa [hornerStep] using hs


/-- Under any valuation satisfying the emitted constraints, with the bases reading as `bv`
(non-empty), the combination reads as `hornerCombine` at the expanded challenge. -/
theorem combinePolynomials_spec (e : IpaEndo F) (xi : SizedF 128 (FVar F)) (n : Prechallenge)
    (hxi : Reads128 V xi n)
    (hchar : CastInj128 F)
    (bases : List (AffinePoint (FVar F) × Option (BoolVar F))) (bv : List (e.d.W.Point × Bool))
    (hb : List.Forall₂ (MaskedBaseReads e.d.W V) bases bv) (hne : bases ≠ []) :
    ⦃⌜True⌝⦄ combinePolynomials (c := Builder V (KimchiConstraint F)) e xi bases
    ⦃⇓ r _ => ⌜OnCurveAt e.d.W V r (hornerCombine (endoExpandZ e.d.lam n.val) bv)⌝⦄ := by
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
      have hf := hornerFold_spec (V := V) e xi n hxi hchar h.1 t tv htail
      exact builder_spec_imp _ _ _ hf fun r hr => hr _ hhpt

/-- A pair reads as two curve points. -/
def PairReads (W : WeierstrassCurve.Affine F) (V : Valuation F)
    (q : AffinePoint (FVar F) × AffinePoint (FVar F)) (v : W.Point × W.Point) : Prop :=
  OnCurveAt W V q.1 v.1 ∧ OnCurveAt W V q.2 v.2

/-- Under any valuation satisfying the emitted constraints, with the pairs reading as `pv`,
the terms read as `lrTerm` at the readings, the challenges reading as some `ns`. -/
private theorem bulletTerms_spec (e : IpaEndo F)
    (hchar : CastInj128 F) :
    ∀ (pairs : List ((AffinePoint (FVar F) × AffinePoint (FVar F)) × SizedF 128 (FVar F)))
      (pv : List (e.d.W.Point × e.d.W.Point)),
      List.Forall₂ (fun q v => PairReads e.d.W V q.1 v) pairs pv →
      ⦃⌜True⌝⦄ bulletTerms (c := Builder V (KimchiConstraint F)) e pairs
      ⦃⇓ r _ => ⌜∃ ns : List Prechallenge, List.Forall₂ (fun q m => Reads128 V q.2 m) pairs ns ∧
        List.Forall₂ (OnCurveAt e.d.W V) r
          (List.zipWith (lrTerm e.d.lam) pv (ns.map Subtype.val))⌝⦄
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
    refine ⟨⟨n', hn'⟩ :: ns, .cons hq' hns, List.Forall₂.cons ?_ hterms⟩
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
    (hchar : CastInj128 F)
    (pairs : List ((AffinePoint (FVar F) × AffinePoint (FVar F)) × SizedF 128 (FVar F)))
    (pv : List (e.d.W.Point × e.d.W.Point))
    (hp : List.Forall₂ (fun q v => PairReads e.d.W V q.1 v) pairs pv) (hne : pairs ≠ []) :
    ⦃⌜True⌝⦄ bulletReduce (c := Builder V (KimchiConstraint F)) e pairs
    ⦃⇓ r _ => ⌜∃ ns : List Prechallenge, List.Forall₂ (fun q m => Reads128 V q.2 m) pairs ns ∧
      OnCurveAt e.d.W V r (lrSum (List.zipWith (lrTerm e.d.lam) pv (ns.map Subtype.val)))⌝⦄ := by
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
    rcases hz : List.zipWith (lrTerm e.d.lam) pv (ns.map Subtype.val) with _ | ⟨w, ws⟩
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

/-- `bulletReduce_spec` with the readings carried into the postcondition. -/
private theorem bulletReduce_spec' (e : IpaEndo F)
    (hchar : CastInj128 F)
    (pairs : List ((AffinePoint (FVar F) × AffinePoint (FVar F)) × SizedF 128 (FVar F))) :
    ⦃⌜True⌝⦄ bulletReduce (c := Builder V (KimchiConstraint F)) e pairs
    ⦃⇓ r _ => ⌜∀ pv : List (e.d.W.Point × e.d.W.Point),
      List.Forall₂ (fun q v => PairReads e.d.W V q.1 v) pairs pv → pairs ≠ [] →
      ∃ ns : List Prechallenge, List.Forall₂ (fun q m => Reads128 V q.2 m) pairs ns ∧
        OnCurveAt e.d.W V r (lrSum (List.zipWith (lrTerm e.d.lam) pv (ns.map Subtype.val)))⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat pv hp hne
  exact (builder_spec_iff _ _).mp (bulletReduce_spec e hchar pairs pv hp hne) nv hsat

/-- How a side's `scaleByShifted` reads under `V` (the proof-side companion of
`IpaScalarOps`, one value per side: `wrapReading`, `stepReading`). `scale_fast` pins the
ladder's bit decomposition only through the value it packs to, so a scalar's reading is a
witness the prover chose, not a function of the scalar: the law says some witness reads the
scalar and, once it is in the ladder's regime, its decode is what acted on the point. -/
structure IpaScalarOps.Reading {sf : Type}
    (ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf) (W : WeierstrassCurve.Affine F) where
  /-- The ladder witness type (wrap: an integer; step: the half and the parity bit). -/
  wit : Type
  /-- `Pre x w`: the witness `w` reads the circuit scalar `x`. -/
  Pre : sf → wit → Prop
  /-- `Reg w`: the ladder regime in which the scaling law speaks. -/
  Reg : wit → Prop
  /-- `dec w`: the integer the witness decodes to — the scalar that acts on the point. -/
  dec : wit → ℤ
  /-- The shape condition on a scalar the law needs (step: the parity bit reads as a bit). -/
  WellFormed : sf → Prop
  /-- The law: if the input point reads as `T`, some witness reads `x`, and in regime the
  output reads as its decode times `T`. -/
  scale : ∀ (pt : AffinePoint (FVar F)) (x : sf), WellFormed x →
    ⦃⌜True⌝⦄ ops.scaleByShifted pt x
    ⦃⇓ r _ => ⌜∀ T : W.Point, OnCurveAt W V pt T →
      ∃ w : wit, Pre x w ∧ (Reg w → OnCurveAt W V r (dec w • T))⌝⦄
  /-- `PreCip x w`: the witness `w` reads the claimed combined inner product `x` through its
  own ladder (`scaleByCip`): a reading tight enough that the limbs `x` absorbs as are
  canonical. -/
  PreCip : sf → wit → Prop
  /-- The `cip` ladder's reading is a reading. -/
  preCip_pre : ∀ {x : sf} {w : wit}, PreCip x w → Pre x w
  /-- The law of `scaleByCip`: `scale`'s, at the tighter reading. -/
  scaleCip : ∀ (pt : AffinePoint (FVar F)) (x : sf), WellFormed x →
    ⦃⌜True⌝⦄ ops.scaleByCip pt x
    ⦃⇓ r _ => ⌜∀ T : W.Point, OnCurveAt W V pt T →
      ∃ w : wit, PreCip x w ∧ (Reg w → OnCurveAt W V r (dec w • T))⌝⦄

omit [ToNat F] in
/-- The reading's scaling law with the well-formedness moved into the postcondition: the shape
an assembly hands `mvcgen` before the claim's well-formedness is in hand. -/
theorem IpaScalarOps.Reading.scale_reads {sf : Type}
    {ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf} {W : WeierstrassCurve.Affine F}
    (R : ops.Reading W) (pt : AffinePoint (FVar F)) (x : sf) :
    ⦃⌜True⌝⦄ ops.scaleByShifted pt x
    ⦃⇓ r _ => ⌜R.WellFormed x → ∀ T : W.Point, OnCurveAt W V pt T →
      ∃ w, R.Pre x w ∧ (R.Reg w → OnCurveAt W V r (R.dec w • T))⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat hwf
  exact (builder_spec_iff _ _).mp (R.scale pt x hwf) nv hsat

/-- Under any valuation satisfying the emitted constraints, with `u`, the combined
commitment, the pairs, `δ`, `sg` and `h` reading as points, the scaled scalars well-formed and
their witnesses in regime (`hreg`; at the deployed curves: the decode is off the forbidden
band), the challenges read as some `ns`, `c` as some `c₀`, each scaled scalar through some
witness of the side's `Reading`, and the success bit reads `1` exactly when `SchnorrPoint`
holds at those readings. -/
theorem ipaFinalCheck_spec {sf : Type}
    (ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf)
    (e : IpaEndo F) (p : Poseidon.Params F) (endo : FVar F)
    (hchar : CastInj128 F)
    (R : ops.Reading e.d.W)
    (sv : SpongeVar F) (t : FVar F) (u combined : AffinePoint (FVar F))
    (inp : CheckBulletproofInput k (FVar F) sf)
    (hwf : ∀ x ∈ inp.scaled, R.WellFormed x)
    (hreg : ∀ (x : sf) (w : R.wit), x ∈ inp.scaled → R.Pre x w → R.Reg w)
    (δv sgv hv : e.d.W.Point)
    (lrv : List (e.d.W.Point × e.d.W.Point))
    (hlr : List.Forall₂ (PairReads e.d.W V) inp.opening.lr.toList lrv)
    (hlrne : inp.opening.lr.toList ≠ [])
    (hδ : OnCurveAt e.d.W V inp.opening.delta δv) (hsg : OnCurveAt e.d.W V inp.opening.sg sgv)
    (hh : OnCurveAt e.d.W V inp.blindingGenerator hv) :
    ⦃⌜True⌝⦄ ipaFinalCheck ops e p endo sv t u combined inp
    ⦃⇓ o _ => ⌜∀ uv Pv : e.d.W.Point, OnCurveAt e.d.W V u uv → OnCurveAt e.d.W V combined Pv →
      o.t = t ∧ ∃ (ns : List Prechallenge) (c₀ : Prechallenge) (wcip wb w₁ w₂ : R.wit),
      List.Forall₂ (Reads128 V) o.challenges ns ∧ ns.length = lrv.length ∧ Reads128 V o.c c₀ ∧
      R.PreCip inp.deferred.combinedInnerProduct wcip ∧ R.Pre inp.deferred.b wb ∧
      R.Pre inp.opening.z1 w₁ ∧ R.Pre inp.opening.z2 w₂ ∧
      ((↑o.success : CVar F).val V = 1 ↔
        SchnorrPoint e.d.lam c₀.val uv Pv
          (lrSum (List.zipWith (lrTerm e.d.lam) lrv (ns.map Subtype.val))) δv sgv hv
          (R.dec wcip) (R.dec wb) (R.dec w₁) (R.dec w₂))⌝⦄ := by
  simp only [ipaFinalCheck]
  have hext := fun sv' => extractScalarChallenges_length (V := V) p endo sv' inp.opening.lr.toList
  have hbr := fun pairs => bulletReduce_spec' (V := V) e hchar pairs
  have hadd := fun a b => addFast_checkFinite_spec (V := V) e.d.W e.d.short e.d.two_ne
    e.d.two_torsion_free a b
  have hδs := fun sv' => builder_spec_true
    (absorbPoint (c := Builder V (KimchiConstraint F)) p sv' inp.opening.delta)
  have hpre := fun sv' => builder_spec_true
    (squeezePrechallenge (c := Builder V (KimchiConstraint F)) p false endo sv')
  have hem := fun g x => endoMul_spec (V := V) e.d g x
  have hsc1 := fun pt => R.scaleCip pt inp.deferred.combinedInnerProduct
    (hwf _ (by simp [CheckBulletproofInput.scaled]))
  have hsc2 := fun pt => R.scale pt inp.deferred.b (hwf _ (by simp [CheckBulletproofInput.scaled]))
  have hsc3 := fun pt => R.scale pt inp.opening.z1 (hwf _ (by simp [CheckBulletproofInput.scaled]))
  have hsc4 := fun pt => R.scale pt inp.opening.z2 (hwf _ (by simp [CheckBulletproofInput.scaled]))
  have hr1 := hreg inp.deferred.combinedInnerProduct
  have hr2 := hreg inp.deferred.b
  have hr3 := hreg inp.opening.z1
  have hr4 := hreg inp.opening.z2
  simp only [CheckBulletproofInput.scaled, List.mem_cons, List.mem_singleton, true_or, or_true,
    forall_const] at hr1 hr2 hr3 hr4
  mvcgen -trivial [-Snarky.Kimchi.addFast_spec, hext, hbr, hsc1, hsc2, hsc3, hsc4, hadd, hδs, hpre,
    hem]
  rename_i _ ext _ hlen lrProd _ hbr' cipU _ hcip pP _ hpP q _ hq svD _ cP _ cQ _ hcQ lhs _ hlhs
    bU _ hbU sgBU _ hsgBU z1T _ hz1 z2T _ hz2 rhs _ hrhs xEq _ hx yEq _ hy succ _ hand
  intro uv Pv hu hP
  have hzne : inp.opening.lr.toList.zip ext.1 ≠ [] := fun h => by
    rcases List.zip_eq_nil_iff.mp h with h | h
    · exact hlrne h
    · exact hlrne (List.length_eq_zero_iff.mp (by rw [← hlen, h]; rfl))
  obtain ⟨ns, hns, hlr'⟩ := hbr' lrv (forall₂_zip_left ext.1 hlr hlen) hzne
  obtain ⟨wcip, hpcip, hcipU⟩ := hcip uv hu
  have hpP' := hpP _ _ hP (hcipU (hr1 _ (R.preCip_pre hpcip)))
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
  refine ⟨trivial, ns, ⟨c₀, hc₀⟩, wcip, wb, w₁, w₂, forall₂_zip_right hlen hns,
    by rw [← hns.length_eq, List.length_zip, hlen, hlr.length_eq, min_self], hcv, hpcip,
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
`sg` and `h` as points, the side's scaling reading through the ladder witnesses of its
`IpaScalarOps.Reading` (`R`, `hwf`, `hreg`) and the map-to-curve as `umap` up to the
ordinate's sign
(`hgm`, the shape `groupMapCircuit_toGroup_spec` gives): the challenges read as some `ns`, `c`
as some `c₀`, the four scaled scalars through some witnesses, and the success bit reads `1`
exactly when the Schnorr equation holds at the readings — `u` the map's point or its negation,
the combined commitment `hornerCombine`, `lr_prod` the `lrSum` of the terms. -/
theorem checkBulletproof_spec_success {sf : Type}
    (ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf) (e : IpaEndo F)
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds) (endo : FVar F)
    (gm : GroupMapParams F) (sqrtF : F → Option F)
    (hchar : CastInj128 F) (hsw : SplitWidth F)
    (R : ops.Reading e.d.W) (umap : F → e.d.W.Point)
    (hgm : ∀ t : FVar F, ⦃⌜True⌝⦄ groupMapCircuit (c := Builder V (KimchiConstraint F)) sqrtF gm t
      ⦃⇓ r _ => ⌜∃ U : e.d.W.Point, OnCurveAt e.d.W V r U ∧
        (U = umap (t.val V) ∨ U = -umap (t.val V))⌝⦄)
    (sv : SpongeVar F) (bases : List (AffinePoint (FVar F) × Option (BoolVar F)))
    (bv : List (e.d.W.Point × Bool)) (hb : List.Forall₂ (MaskedBaseReads e.d.W V) bases bv)
    (hbne : bases ≠ []) (inp : CheckBulletproofInput k (FVar F) sf)
    (hwf : ∀ x ∈ inp.scaled, R.WellFormed x)
    (hreg : ∀ (x : sf) (w : R.wit), x ∈ inp.scaled → R.Pre x w → R.Reg w)
    (n : Prechallenge) (hxi : Reads128 V inp.xi n) (δv sgv hv : e.d.W.Point)
    (lrv : List (e.d.W.Point × e.d.W.Point))
    (hlr : List.Forall₂ (PairReads e.d.W V) inp.opening.lr.toList lrv)
    (hlrne : inp.opening.lr.toList ≠ [])
    (hδ : OnCurveAt e.d.W V inp.opening.delta δv) (hsg : OnCurveAt e.d.W V inp.opening.sg sgv)
    (hh : OnCurveAt e.d.W V inp.blindingGenerator hv) :
    ⦃⌜True⌝⦄ checkBulletproof ops e p endo gm sqrtF sv bases inp
    ⦃⇓ o _ => ⌜∃ (U : e.d.W.Point) (ns : List Prechallenge) (c₀ : Prechallenge)
      (wcip wb w₁ w₂ : R.wit),
      (U = umap (o.t.val V) ∨ U = -umap (o.t.val V)) ∧
      (∃ (x y : F) (h : e.d.W.Nonsingular x y), U = .some x y h ∧
        ∃ m : ℕ, m < (fieldModulus F + 1) / 2 ∧ y = (m : F)) ∧
      List.Forall₂ (Reads128 V) o.challenges ns ∧ ns.length = lrv.length ∧ Reads128 V o.c c₀ ∧
      R.PreCip inp.deferred.combinedInnerProduct wcip ∧ R.Pre inp.deferred.b wb ∧
      R.Pre inp.opening.z1 w₁ ∧ R.Pre inp.opening.z2 w₂ ∧
      ((↑o.success : CVar F).val V = 1 ↔
        SchnorrPoint e.d.lam c₀.val U (hornerCombine (endoExpandZ e.d.lam n.val) bv)
          (lrSum (List.zipWith (lrTerm e.d.lam) lrv (ns.map Subtype.val))) δv sgv hv
          (R.dec wcip) (R.dec wb) (R.dec w₁) (R.dec w₂))⌝⦄ := by
  simp only [checkBulletproof]
  have habs := fun sv' limbs => builder_spec_true
    (absorbList (c := Builder V (KimchiConstraint F)) p sv' limbs)
  have hsq := fun sv' => builder_spec_true
    (SpongeVar.squeeze (c := Builder V (KimchiConstraint F)) p sv')
  have hcomb := combinePolynomials_spec (V := V) e inp.xi n hxi hchar bases bv hb hbne
  have hfin := fun sv' t u comb => ipaFinalCheck_spec (V := V) ops e p endo hchar R
    sv' t u comb inp hwf hreg δv sgv hv lrv hlr hlrne hδ hsg hh
  have hlh := fun pt => builder_spec_and _ _ _
    (lowerHalfPoint_onCurve (V := V) endo ⟨e.d.short.1, e.d.short.2.2.1⟩ pt)
    (lowerHalfPoint_below (V := V) hsw.two_ne hsw.three_ne hsw.inj hsw.modulus_lt endo pt)
  mvcgen -trivial [habs, hsq, hgm, hlh, hcomb, hfin]
  case vc1.hsize => exact hsize
  rename_i _ _ _ tv _ _ _ _ hu u _ hlow comb _ hP o _
  intro ho
  obtain ⟨U₀, hU₀, hsign₀⟩ := hu
  -- the lower-half ordinate keeps the point up to sign, below `(p + 1)/2`
  obtain ⟨hlow, m, hm, hmy⟩ := hlow
  obtain ⟨U, hU, hsign'⟩ := hlow U₀ hU₀
  have hsign : U = umap (tv.1.val V) ∨ U = -umap (tv.1.val V) := by
    rcases hsign' with rfl | rfl <;> rcases hsign₀ with rfl | rfl <;> simp
  obtain ⟨hns, hUpt⟩ := hU
  obtain ⟨ht, ns, c₀, wcip, wb, w₁, w₂, hns', hlen, hc, hpcip, hpb, hp1, hp2, hiff⟩ :=
    ho _ _ ⟨hns, hUpt⟩ hP
  rw [ht]
  exact ⟨U, ns, c₀, wcip, wb, w₁, w₂, hsign, ⟨_, _, hns, hUpt, m, hm, hmy⟩, hns', hlen, hc,
    hpcip, hpb, hp1, hp2, hiff⟩

/-- `checkBulletproof_spec_success` with the reading and every point reading at a curve `W`
the endomorphism bundle's curve equals — the form a side generic in its wire curve consumes. -/
theorem checkBulletproof_spec_success_at {sf : Type}
    (ops : IpaScalarOps F (Builder V (KimchiConstraint F)) sf) (e : IpaEndo F)
    {W : WeierstrassCurve.Affine F} (hW : e.d.W = W)
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds) (endo : FVar F)
    (gm : GroupMapParams F) (sqrtF : F → Option F)
    (hchar : CastInj128 F) (hsw : SplitWidth F)
    (R : ops.Reading W) (umap : F → W.Point)
    (hgm : ∀ t : FVar F, ⦃⌜True⌝⦄ groupMapCircuit (c := Builder V (KimchiConstraint F)) sqrtF gm t
      ⦃⇓ r _ => ⌜∃ U : W.Point, OnCurveAt W V r U ∧
        (U = umap (t.val V) ∨ U = -umap (t.val V))⌝⦄)
    (sv : SpongeVar F) (bases : List (AffinePoint (FVar F) × Option (BoolVar F)))
    (bv : List (W.Point × Bool)) (hb : List.Forall₂ (MaskedBaseReads W V) bases bv)
    (hbne : bases ≠ []) (inp : CheckBulletproofInput k (FVar F) sf)
    (hwf : ∀ x ∈ inp.scaled, R.WellFormed x)
    (hreg : ∀ (x : sf) (w : R.wit), x ∈ inp.scaled → R.Pre x w → R.Reg w)
    (n : Prechallenge) (hxi : Reads128 V inp.xi n) (δv sgv hv : W.Point)
    (lrv : List (W.Point × W.Point))
    (hlr : List.Forall₂ (PairReads W V) inp.opening.lr.toList lrv)
    (hlrne : inp.opening.lr.toList ≠ [])
    (hδ : OnCurveAt W V inp.opening.delta δv) (hsg : OnCurveAt W V inp.opening.sg sgv)
    (hh : OnCurveAt W V inp.blindingGenerator hv) :
    ⦃⌜True⌝⦄ checkBulletproof ops e p endo gm sqrtF sv bases inp
    ⦃⇓ o _ => ⌜∃ (U : W.Point) (ns : List Prechallenge) (c₀ : Prechallenge)
      (wcip wb w₁ w₂ : R.wit),
      (U = umap (o.t.val V) ∨ U = -umap (o.t.val V)) ∧
      (∃ (x y : F) (h : W.Nonsingular x y), U = .some x y h ∧
        ∃ m : ℕ, m < (fieldModulus F + 1) / 2 ∧ y = (m : F)) ∧
      List.Forall₂ (Reads128 V) o.challenges ns ∧ ns.length = lrv.length ∧ Reads128 V o.c c₀ ∧
      R.PreCip inp.deferred.combinedInnerProduct wcip ∧ R.Pre inp.deferred.b wb ∧
      R.Pre inp.opening.z1 w₁ ∧ R.Pre inp.opening.z2 w₂ ∧
      ((↑o.success : CVar F).val V = 1 ↔
        SchnorrPoint e.d.lam c₀.val U (hornerCombine (endoExpandZ e.d.lam n.val) bv)
          (lrSum (List.zipWith (lrTerm e.d.lam) lrv (ns.map Subtype.val))) δv sgv hv
          (R.dec wcip) (R.dec wb) (R.dec w₁) (R.dec w₂))⌝⦄ := by
  subst hW
  exact checkBulletproof_spec_success ops e p hsize endo gm sqrtF hchar hsw R umap hgm sv bases bv
    hb
    hbne inp hwf hreg n hxi δv sgv hv lrv hlr hlrne hδ hsg hh

/-! ## A side of the group half

What a side supplies to read the group half's gadgets on the wire's commitment curve `C`
(`Bulletproof.Ipa.KimchiCurve`): its ladder reading, the decode of a shifted claim, the
curve's group facts, the map-to-curve data, the field facts the transcript's squeezes need,
the absorbed limbs of a canonical claim, and the bridges from the gadgets' group vocabulary
(`SchnorrPoint`, `hornerCombine`) to the wire's (`schnorrAt`, `combineCommitments`). One value
per deployed side, `wrapSide` and `stepSide` below. The
opening check's read on any side, `IvpSide.opening_reads`, is proved once, from
`checkBulletproof_spec_success`. -/

section Side

open Bulletproof Bulletproof.Ipa CompElliptic.CurveForms.ShortWeierstrass

/-- What the wire's commitment curve supplies to the group half's gadgets, whichever side runs
them: the map-to-curve parameters the opening check derives its `U` base from; the curve's
deployed shape, from which follow both the field facts the transcript's squeezes need
(`IvpCurve.two_ne`, `IvpCurve.three_ne`, `IvpCurve.small_inj`) and the group fact the adds and
negations need (`IvpCurve.two_torsion_free`); and the three bridges from the gadgets'
vocabulary to the wire's. The endomorphism bundle is NOT here: `IvpCurve.e` derives it from
the shape and the curve's own `Pasta.EndoSpec`, so a side cannot name a group other than its
curve's. Two of the three bridges are generic at any shaped curve (`hornerCombine_eq`,
`schnorrPoint_iff_schnorrAt`); only the map-to-curve one is per curve, since the SvdW
parameters are. The curve's shortness, its scalar order's action and its sponge's round count
are not here either: they are `C.a_zero`, `C.card_nsmul` and `C.sponge.hsize`. None of it
mentions the side's scalar representation. One value per curve: `IvpCurve.vesta`,
`IvpCurve.pallas`. -/
structure IvpCurve (C : KimchiCurve) : Prop where
  /-- The curve has the deployed shape: the base field's width gives the canonical 128-bit
  split (`IvpCurve.splitWidth`), and the scalar order's leaves the group without 2-torsion. -/
  shape : PastaShape C
  /-- The map-to-curve gadget reads as the wire's `toGroup` up to sign (`groupMap_reads` at
  any shaped curve). -/
  groupMap : ∀ (V : Valuation C.BaseField) (sqrtF : C.BaseField → Option C.BaseField)
      (t : FVar C.BaseField),
    ⦃⌜True⌝⦄ groupMapCircuit (c := Builder V (KimchiConstraint C.BaseField)) sqrtF
      (.ofSpec C.groupMap) t
    ⦃⇓ r _ => ⌜∃ U : C.E.toAffine.Point, OnCurveAt C.E.toAffine V r U ∧
      (U = SWPoint.equivPoint C.E (C.toGroup (t.val V)) ∨
        U = -SWPoint.equivPoint C.E (C.toGroup (t.val V)))⌝⦄
  /-- Horner's rule over the kept bases, read back in the wire group, is the wire's polyscale
  combination at the expanded challenge (`hornerCombine_eq` at any shaped curve). -/
  horner : ∀ (n : ℕ) (bvW : List (C.Point × Bool)), (∀ h, bvW.getLast? = some h → h.2 = true) →
    (SWPoint.equivPoint C.E).symm (hornerCombine (endoExpandZ C.endo.lam n)
        (bvW.map fun b => (SWPoint.equivPoint C.E b.1, b.2)))
      = combineCommitments C (Poseidon.FqSponge.endoExpand C.lam n)
          ((bvW.filter (·.2)).map (·.1)).toArray
  /-- The gadgets' Schnorr equation, read back in the wire group, is the wire's `schnorrAt`
  (`schnorrPoint_iff_schnorrAt` at any shaped curve). -/
  schnorr : ∀ (σ : SRS C.Point) (U P : C.Point) (chals : Vector C.ScalarField σ.k) (c₀ : ℕ)
    (cip b z₁ z₂ : ℤ) (pr : Ipa.Proof C σ.k) (ns : List ℕ),
    chals.toList = ns.map (Poseidon.FqSponge.endoExpand C.lam) →
    pr.z1 = (z₁ : C.ScalarField) → pr.z2 = (z₂ : C.ScalarField) →
    (SchnorrPoint C.endo.lam c₀ (SWPoint.equivPoint C.E U) (SWPoint.equivPoint C.E P)
        (lrSum (List.zipWith (lrTerm C.endo.lam) (pr.lr.toList.map fun q =>
          (SWPoint.equivPoint C.E q.1, SWPoint.equivPoint C.E q.2)) ns))
        (SWPoint.equivPoint C.E pr.delta) (SWPoint.equivPoint C.E pr.sg)
        (SWPoint.equivPoint C.E σ.h) cip b z₁ z₂
      ↔ schnorrAt C σ U chals (Poseidon.FqSponge.endoExpand C.lam c₀)
          (cip : C.ScalarField) (b : C.ScalarField) P pr)

/-- The endomorphism bundle the opening check's `endo_mul`s and challenge expansions run on:
the curve's own, with its scalar cardinality as the numeral `endoInv`'s witness needs. Derived
rather than supplied, so a side cannot name a group other than its curve's. -/
def IvpCurve.e {C : KimchiCurve} (S : IvpCurve C) : IpaEndo C.BaseField where
  d := S.shape.e
  q := C.scalar
  q_eq := (CommitmentCurve.order_eq C.toCommitmentCurve).symm

/-- The bundle's curve is the wire curve, now by construction. -/
theorem IvpCurve.eW {C : KimchiCurve} (S : IvpCurve C) : S.e.d.W = C.E.toAffine := rfl

/-- What a side supplies beyond its curve: how its shifted-scalar ladder reads (`R`); the
scalar-field decode of a shifted claim, with the law that a ladder witness's integer decode
casts to it; and the limbs a claimed `cip` absorbs as, at its ladder's witness. These are the
fields that genuinely differ between the wrap side's `Type1` claims and the step side's split
`Type2` ones. One value per deployed side: `wrapSide`, `stepSide`. -/
structure IvpSide (C : KimchiCurve) (V : Valuation C.BaseField) {sf : Type}
    (ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf) where
  /-- The curve's own gadget facts, shared by both sides of the cycle. -/
  curve : IvpCurve C
  /-- The ladder's reading on the wire curve's affine group. -/
  R : IpaScalarOps.Reading (V := V) ops C.E.toAffine
  /-- The canonical decode of a shifted claim in the scalar field. -/
  decode : sf → C.ScalarField
  /-- A ladder witness of a claim decodes, in the scalar field, to the claim's decode. -/
  dec_cast : ∀ {x : sf} {w : R.wit}, R.Pre x w → (R.dec w : C.ScalarField) = decode x
  /-- At the `cip` ladder's witness of a claim, the limbs the claim absorbs as are the wire's
  `scalarLimbs` of the shifted decode: the ladder's range check makes them canonical (wrap:
  the `Type1` cell is below `2²⁵⁴`, under the scalar modulus; step: `scaleByCip` pins the half
  below `2²⁵³`, so `2·sDiv2 + sOdd` is below it too). -/
  absorb_limbs : ∀ {x : sf} {w : R.wit}, R.PreCip x w →
    (ops.shiftedToAbsorbFields x).map (·.val V) = scalarLimbs C (shiftScalar C (decode x))
variable {C : KimchiCurve} {V : Valuation C.BaseField} {sf : Type} {k : ℕ}
  {ops : IpaScalarOps C.BaseField (Builder V (KimchiConstraint C.BaseField)) sf}

/-- Naturals up to 3 cast injectively (the conditional sponge's mask count). -/
theorem IvpCurve.small_inj (S : IvpCurve C) :
    ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : C.BaseField) = k → j = k :=
  fun j k _ _ h =>
    castInj128_of_lt C.base (lt_trans (by norm_num) S.shape.base_big) j k (by omega) (by omega) h

/-- The base field is not of characteristic 2. -/
theorem IvpCurve.two_ne (S : IvpCurve C) : (2 : C.BaseField) ≠ 0 := fun h =>
  absurd (S.small_inj 2 0 (by norm_num) (by norm_num) (by simpa using h)) (by norm_num)

/-- The base field is not of characteristic 3 (the prechallenge squeeze's `endo_scalar`). -/
theorem IvpCurve.three_ne (S : IvpCurve C) : (3 : C.BaseField) ≠ 0 := fun h =>
  absurd (S.small_inj 3 0 (by norm_num) (by norm_num) (by simpa using h)) (by norm_num)

/-- The base field has the canonical split's widths: between `2¹³⁰` and `2²⁵⁶`. -/
theorem IvpCurve.splitWidth (S : IvpCurve C) : SplitWidth C.BaseField :=
  SplitWidth.zmod (lt_trans (by norm_num) S.shape.base_big) (lt_trans S.shape.base_lt (by norm_num))

/-- The affine group has no 2-torsion: its order is an odd prime. -/
theorem IvpCurve.two_torsion_free (S : IvpCurve C) (P : C.E.toAffine.Point) (hne : P ≠ 0) :
    P + P ≠ 0 :=
  S.shape.d.two_torsion_free P hne

/-- A shifted claim the ladder read speaks about: well-formed for the side, and every witness
reading it in the ladder's regime (at the deployed curves: the decode is off the forbidden
band — the `scale_fast`-family premise #341 tracks). -/
def IvpSide.ClaimOk (S : IvpSide C V ops) (x : sf) : Prop :=
  S.R.WellFormed x ∧ ∀ w, S.R.Pre x w → S.R.Reg w

/-- The opening check's read at given readings (the family form `IvpSide.opening_reads`
quantifies): with the bases reading as wire points under their bits (the last kept), every
scaled claim a claim the ladder read speaks about, `ξ` reading as `n`, the pairs, `δ`, `sg` and
`h` as the wire's points — the challenges read as some `ns`, `c` as some `c₀`, `U` is the
wire's `uBase` of `t`, `cip` has a ladder witness, and the success bit reads `1` exactly when
the wire verifier's `schnorrAt` holds at the side's decodes over the kept bases combined at
`n`'s expansion. -/
private theorem IvpSide.opening_reads_at (S : IvpSide C V ops) (endo : FVar C.BaseField)
    (sqrtF : C.BaseField → Option C.BaseField)
    (sv : SpongeVar C.BaseField)
    (bases : List (AffinePoint (FVar C.BaseField) × Option (BoolVar C.BaseField)))
    (bvW : List (C.Point × Bool))
    (hb : List.Forall₂ (MaskedBaseReads C.E.toAffine V) bases
      (bvW.map fun b => (SWPoint.equivPoint C.E b.1, b.2)))
    (hbne : bases ≠ []) (hlast : ∀ h, bvW.getLast? = some h → h.2 = true)
    (inp : CheckBulletproofInput k (FVar C.BaseField) sf) (hclaims : ∀ x ∈ inp.scaled, S.ClaimOk x)
    (n : Prechallenge) (hxi : Reads128 V inp.xi n)
    (σ : SRS C.Point) (lrW : Vector (C.Point × C.Point) σ.k) (δW sgW : C.Point)
    (hlr : List.Forall₂ (PairReads C.E.toAffine V) inp.opening.lr.toList
      (lrW.toList.map fun q => (SWPoint.equivPoint C.E q.1, SWPoint.equivPoint C.E q.2)))
    (hlrne : inp.opening.lr.toList ≠ [])
    (hδ : OnCurveAt C.E.toAffine V inp.opening.delta (SWPoint.equivPoint C.E δW))
    (hsg : OnCurveAt C.E.toAffine V inp.opening.sg (SWPoint.equivPoint C.E sgW))
    (hh : OnCurveAt C.E.toAffine V inp.blindingGenerator (SWPoint.equivPoint C.E σ.h)) :
    ⦃⌜True⌝⦄ checkBulletproof (c := Builder V (KimchiConstraint C.BaseField)) ops S.curve.e
      C.sponge.params endo (.ofSpec C.groupMap) sqrtF sv bases inp
    ⦃⇓ o _ => ⌜∃ (U : C.Point) (ns : List Prechallenge) (c₀ : Prechallenge)
      (chals : Vector C.ScalarField σ.k),
      U = C.uBase (o.t.val V) ∧
      List.Forall₂ (Reads128 V) o.challenges ns ∧ Reads128 V o.c c₀ ∧
      chals.toList = ns.map (fun m => Poseidon.FqSponge.endoExpand C.lam m.val) ∧
      (∃ w : S.R.wit, S.R.PreCip inp.deferred.combinedInnerProduct w) ∧
      ((↑o.success : CVar C.BaseField).val V = 1 ↔
        schnorrAt C σ U chals (Poseidon.FqSponge.endoExpand C.lam c₀.val)
          (S.decode inp.deferred.combinedInnerProduct) (S.decode inp.deferred.b)
          (combineCommitments C (Poseidon.FqSponge.endoExpand C.lam n.val)
            ((bvW.filter (·.2)).map (·.1)).toArray)
          ⟨lrW, δW, S.decode inp.opening.z1, S.decode inp.opening.z2, sgW⟩)⌝⦄ := by
  have hcast : CastInj128 C.BaseField :=
    castInj128_of_lt C.base (lt_trans (by norm_num) S.curve.shape.base_big)
  refine builder_spec_imp _ _ _
    (checkBulletproof_spec_success_at ops S.curve.e S.curve.eW _ C.sponge.hsize endo
      (.ofSpec C.groupMap)
      sqrtF hcast S.curve.splitWidth S.R (fun t => SWPoint.equivPoint C.E (C.toGroup t))
      (S.curve.groupMap V sqrtF) sv bases _ hb hbne inp
      (fun x hx => (hclaims x hx).1) (fun x w hx hpre => (hclaims x hx).2 w hpre)
      n hxi _ _ _ _ hlr hlrne hδ hsg hh) fun o ho => ?_
  obtain ⟨U, ns, c₀, wcip, wb, w₁, w₂, hU, ⟨x, y, hxy, hUsome, m, hm, hmy⟩, hns, hlen, hc,
    hpcip, hpb, hp1, hp2, hiff⟩ := ho
  have hlen' : ns.length = σ.k := by rw [hlen, List.length_map, Vector.length_toList]
  refine ⟨(SWPoint.equivPoint C.E).symm U, ns, c₀,
    ⟨(ns.map fun m => Poseidon.FqSponge.endoExpand C.lam m.val).toArray,
      by simp [hlen']⟩, ?_, hns, hc, by simp, ⟨wcip, hpcip⟩, ?_⟩
  · -- the point is the map-to-curve's up to sign
    have hsgn : (SWPoint.equivPoint C.E).symm U = C.toGroup (o.t.val V) ∨
        (SWPoint.equivPoint C.E).symm U = -C.toGroup (o.t.val V) := by
      beta_reduce at hU
      generalize C.toGroup (o.t.val V) = T at hU ⊢
      rcases hU with h | h
      · left; rw [h, AddEquiv.symm_apply_apply]
      · right
        rw [h]
        exact (congrArg (SWPoint.equivPoint C.E).symm
          (map_neg (SWPoint.equivPoint C.E) T).symm).trans (AddEquiv.symm_apply_apply _ _)
    -- and its ordinate is the circuit's, below `(p + 1)/2`
    set U' := (SWPoint.equivPoint C.E).symm U with hU'
    have he : SWPoint.equivPoint C.E U' = .some x y hxy := by
      rw [hU', AddEquiv.apply_symm_apply]; exact hUsome
    have hy : U'.y = y := by
      rcases U'.onCurve with hon | h0
      · rw [SWPoint.equivPoint_eq_some U' hon] at he
        exact ((WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp he).2
      · exfalso
        have hz : SWPoint.equivPoint C.E U' = 0 := by
          show toPt C.E.A C.E.B (U'.x, U'.y) = 0
          have : (U'.x, U'.y) = ((0 : C.BaseField), (0 : C.BaseField)) := h0
          rw [this]
          exact toPt_zero C.E.B_nonzero
        rw [hz] at he
        exact WeierstrassCurve.Affine.Point.some_ne_zero _ he.symm
    have hbig := S.curve.shape.base_big
    rw [fieldModulus_zmod] at hm
    have hval : U'.y.val < (C.base + 1) / 2 := by
      rw [hy, hmy, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      exact hm
    exact C.lowerHalf_eq_of_lt (by omega) hsgn hval
  · rw [← S.dec_cast (S.R.preCip_pre hpcip), ← S.dec_cast hpb, ← S.dec_cast hp1,
      ← S.dec_cast hp2, hiff,
      ← S.curve.schnorr σ _ _ _ c₀.val _ _ _ _ ⟨lrW, δW, _, _, sgW⟩ (ns.map Subtype.val)
        (by simp [Function.comp_def]) rfl rfl]
    simp only [AddEquiv.apply_symm_apply]
    rw [← S.curve.horner n.val bvW hlast, AddEquiv.apply_symm_apply]
    exact Iff.rfl

/-- The opening check's read on a side, every reading quantified: the transcript half
(`CheckBulletproofReads` at the sponge, pair and `δ` readings, the claimed `cip`'s absorbed
limbs) and the algebra half — for any readings of the bases as wire points under their bits
(the last kept), with every scaled claim a claim the ladder read speaks about, `ξ` reading as
`n`, and the pairs, `δ`, `sg` and `h` reading as the wire's points: the challenges read as
some `ns`, `c` as some `c₀`, `U` is the wire's `uBase` of `t`, `cip` has a ladder witness,
and the success bit reads `1` exactly when the wire verifier's `schnorrAt` holds at the side's
decodes over the kept bases combined at `n`'s expansion. -/
def IvpSide.OpeningReads (S : IvpSide C V ops) (sv : SpongeVar C.BaseField)
    (bases : List (AffinePoint (FVar C.BaseField) × Option (BoolVar C.BaseField)))
    (inp : CheckBulletproofInput k (FVar C.BaseField) sf) (o : CheckBulletproofOutput C.BaseField) :
    Prop :=
  (∀ (s₀ : Poseidon.State C.BaseField)
    (lrv : List (AffinePoint C.BaseField × AffinePoint C.BaseField))
    (δv : AffinePoint C.BaseField),
    SpongeVar.ReadsAt V sv s₀ → List.Forall₂ (CircuitType.Reads V) inp.opening.lr.toList lrv →
    CircuitType.Reads V inp.opening.delta δv →
    CheckBulletproofReads C.sponge.params s₀
      ((ops.shiftedToAbsorbFields inp.deferred.combinedInnerProduct).map (·.val V)) lrv δv V o) ∧
  (∀ bvW : List (C.Point × Bool),
    List.Forall₂ (MaskedBaseReads C.E.toAffine V) bases
      (bvW.map fun b => (SWPoint.equivPoint C.E b.1, b.2)) →
    bases ≠ [] → (∀ h, bvW.getLast? = some h → h.2 = true) →
    (∀ x ∈ inp.scaled, S.ClaimOk x) →
    ∀ n : Prechallenge, Reads128 V inp.xi n →
    ∀ (σ : SRS C.Point) (lrW : Vector (C.Point × C.Point) σ.k) (δW sgW : C.Point),
    List.Forall₂ (PairReads C.E.toAffine V) inp.opening.lr.toList
      (lrW.toList.map fun q => (SWPoint.equivPoint C.E q.1, SWPoint.equivPoint C.E q.2)) →
    inp.opening.lr.toList ≠ [] →
    OnCurveAt C.E.toAffine V inp.opening.delta (SWPoint.equivPoint C.E δW) →
    OnCurveAt C.E.toAffine V inp.opening.sg (SWPoint.equivPoint C.E sgW) →
    OnCurveAt C.E.toAffine V inp.blindingGenerator (SWPoint.equivPoint C.E σ.h) →
    ∃ (U : C.Point) (ns : List Prechallenge) (c₀ : Prechallenge)
      (chals : Vector C.ScalarField σ.k),
      U = C.uBase (o.t.val V) ∧
      List.Forall₂ (Reads128 V) o.challenges ns ∧ Reads128 V o.c c₀ ∧
      chals.toList = ns.map (fun m => Poseidon.FqSponge.endoExpand C.lam m.val) ∧
      (∃ w : S.R.wit, S.R.PreCip inp.deferred.combinedInnerProduct w) ∧
      ((↑o.success : CVar C.BaseField).val V = 1 ↔
        schnorrAt C σ U chals (Poseidon.FqSponge.endoExpand C.lam c₀.val)
          (S.decode inp.deferred.combinedInnerProduct) (S.decode inp.deferred.b)
          (combineCommitments C (Poseidon.FqSponge.endoExpand C.lam n.val)
            ((bvW.filter (·.2)).map (·.1)).toArray)
          ⟨lrW, δW, S.decode inp.opening.z1, S.decode inp.opening.z2, sgW⟩))

/-- **The opening check reads as the wire's, on any side.** Under any valuation satisfying the
emitted constraints the outputs satisfy `IvpSide.OpeningReads`: the transcript half from
`checkBulletproof_reads`, the algebra half from `IvpSide.opening_reads_at`. The shape an
assembly hands `mvcgen`, stated once here (`scripts/check-spec-locality.sh`). -/
theorem IvpSide.opening_reads (S : IvpSide C V ops)
    (endo : FVar C.BaseField) (sqrtF : C.BaseField → Option C.BaseField)
    (sv : SpongeVar C.BaseField)
    (bases : List (AffinePoint (FVar C.BaseField) × Option (BoolVar C.BaseField)))
    (inp : CheckBulletproofInput k (FVar C.BaseField) sf) :
    ⦃⌜True⌝⦄ checkBulletproof (c := Builder V (KimchiConstraint C.BaseField)) ops S.curve.e
      C.sponge.params endo (.ofSpec C.groupMap) sqrtF sv bases inp
    ⦃⇓ o _ => ⌜S.OpeningReads sv bases inp o⌝⦄ := by
  refine builder_spec_and _ _ _
    (checkBulletproof_reads S.curve.two_ne S.curve.three_ne S.curve.splitWidth ops S.curve.e _
      C.sponge.hsize endo
      (.ofSpec C.groupMap) sqrtF sv bases inp) ?_
  rw [builder_spec_iff]
  intro nv hsat bvW hb hbne hlast hclaims n hxi σ lrW δW sgW hlr hlrne hδ hsg hh
  exact (builder_spec_iff _ _).mp (S.opening_reads_at endo sqrtF sv bases bvW hb hbne
    hlast inp hclaims n hxi σ lrW δW sgW hlr hlrne hδ hsg hh) nv hsat

end Side

/-! ## The deployed ladders

The two sides' scaling gadgets read through the ladder laws at the deployed curves: a
witness integer standing for the shifted scalar, its decode acting once it is in the one-wrap
regime. The witness is the prover's — `scale_fast` pins its bit decomposition only through
the scalar it packs to, on every side — so the readings quantify over it. -/

section Deployed

open CompElliptic.Curves.Pasta Pasta.Shifted

/-- The wrap side's ladder witness of a `Type1` scalar: an integer below `2²⁵⁴` (the ladder's
top bit is pinned) reading as its representative. -/
def WrapLadderPre (V : Valuation Fq) (x : Type1 (FVar Fq)) (z : ℤ) : Prop :=
  0 ≤ z ∧ z < 2 ^ 254 ∧ (z : Fq) = x.val.val V

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
  obtain ⟨z, h0, -, hlt, hz, hreg⟩ := hr T hT
  exact ⟨z, ⟨h0, hlt (by norm_num), hz⟩, fun hR => hreg hR⟩

/-- The canonical decode of a wrap-side shifted scalar in the scalar field: the `Type1` unshift
of the circuit value's representative — the wire's `Shifted_value.Type1.to_field` of the
crossing. -/
def wrapDecode (V : Valuation Fq) (x : Type1 (FVar Fq)) : Fp :=
  unshiftType1 255 (((x.val.val V).val : ℕ) : Fp)

/-- A wrap ladder witness is the shifted value's representative: `scaleFast1` pins the top bit
of its 255-bit decomposition, so the witness is below `2²⁵⁴ < |Fq|`. -/
private theorem wrapLadderPre_eq {V : Valuation Fq} {x : Type1 (FVar Fq)} {z : ℤ}
    (h : WrapLadderPre V x z) : z = ((x.val.val V).val : ℤ) := by
  obtain ⟨h0, hlt, hz⟩ := h
  rw [← hz]
  exact (toNat_intCast_of_lt PALLAS_SCALAR_CARD h0
    (lt_of_lt_of_le hlt (by norm_num [PALLAS_SCALAR_CARD]))).symm

/-- A wrap ladder witness decodes, in the scalar field, to `wrapDecode`. -/
theorem wrapLadderDec_cast {V : Valuation Fq} {x : Type1 (FVar Fq)} {z : ℤ}
    (h : WrapLadderPre V x z) : (wrapLadderDec z : Fp) = wrapDecode V x := by
  simp only [wrapLadderDec, wrapDecode, unshiftType1, wrapLadderPre_eq h]
  push_cast
  ring

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

/-- The step side's reading of the claimed `cip`: `StepLadderPre` with the half one bit
narrower, as `scaleByCip`'s ladder pins it. -/
def StepCipPre (V : Valuation Fp) (x : Type2 (SplitField (FVar Fp) (BoolVar Fp)))
    (w : ℤ × Bool) : Prop :=
  StepLadderPre V x w ∧ w.1 < 2 ^ 253

/-- `IpaScalarOps.step`'s `cip` scaling reads through `scaleFast2_spec` at Pallas and 253
halved bits, given the parity bit reads as a bit. -/
theorem step_scaleCip_reads {V : Valuation Fp} (pt : AffinePoint (FVar Fp))
    (x : Type2 (SplitField (FVar Fp) (BoolVar Fp))) (bb : Bool)
    (hbit : (↑x.val.sOdd : CVar Fp).val V = bit bb) :
    ⦃⌜True⌝⦄ (IpaScalarOps.step (c := Builder V (KimchiConstraint Fp))).scaleByCip pt x
    ⦃⇓ r _ => ⌜∀ T : IpaEndo.pallas.d.W.Point, OnCurveAt IpaEndo.pallas.d.W V pt T →
      ∃ w : ℤ × Bool, StepCipPre V x w ∧
        (StepLadderReg w → OnCurveAt IpaEndo.pallas.d.W V r (stepLadderDec w • T))⌝⦄ := by
  refine builder_spec_imp _ _ _
    (scaleFast2_spec (V := V) HasCurve.pallas 255 51 253 (by norm_num) (by norm_num) pt
      x.val.sDiv2 x.val.sOdd) fun r hr T hT => ?_
  obtain ⟨z, h0, hlt, hz, hreg⟩ := hr T hT bb hbit
  exact ⟨(z, bb), ⟨⟨hbit, h0, lt_trans hlt (by norm_num), hz⟩, hlt⟩, fun hR => hreg hR⟩

/-- The step side's decode of a split scalar in the scalar field: the `Type2` unshift of the
half's representative and the parity bit — canonical, the half being below `2²⁵⁴ < |Fp|`. -/
def stepDecode (V : Valuation Fp) (x : Type2 (SplitField (FVar Fp) (BoolVar Fp))) : Fq :=
  unshiftType2 255 (((x.val.sDiv2.val V).val : ℕ) : Fq)
    ((((↑x.val.sOdd : CVar Fp).val V).val : ℕ) : Fq)

/-- A step ladder witness decodes, in the scalar field, to `stepDecode`. -/
theorem stepLadderDec_cast {V : Valuation Fp}
    {x : Type2 (SplitField (FVar Fp) (BoolVar Fp))} {w : ℤ × Bool} (h : StepLadderPre V x w) :
    (stepLadderDec w : Fq) = stepDecode V x := by
  obtain ⟨hb, h0, hlt, hz⟩ := h
  have hv : (((w.1 : Fp)).val : ℤ) = w.1 :=
    toNat_intCast_of_lt PALLAS_BASE_CARD h0
      (lt_of_lt_of_le hlt (by norm_num [PALLAS_BASE_CARD]))
  rw [hz] at hv
  simp only [stepLadderDec, stepDecode, unshiftType2, hb]
  rw [← hv]
  rcases w.2 with _ | _
  · simp only [bit, Bool.false_eq_true, ↓reduceIte, ZMod.val_zero]
    push_cast
    ring
  · simp only [bit, ↓reduceIte, ZMod.val_one]
    push_cast
    ring

/-- The wrap side's reading: `IpaScalarOps.wrap` at Vesta through `wrap_scale_reads`; every
`Type1` scalar is well-formed. -/
def wrapReading (V : Valuation Fq) :
    IpaScalarOps.Reading (V := V) IpaScalarOps.wrap IpaEndo.vesta.d.W where
  wit := ℤ
  Pre := WrapLadderPre V
  Reg := WrapLadderReg
  dec := wrapLadderDec
  WellFormed _ := True
  scale pt x _ := wrap_scale_reads pt x
  PreCip := WrapLadderPre V
  preCip_pre h := h
  scaleCip pt x _ := wrap_scale_reads pt x

/-- The step side's reading: `IpaScalarOps.step` at Pallas through `step_scale_reads`; a split
scalar is well-formed when its parity bit reads as a bit. -/
def stepReading (V : Valuation Fp) :
    IpaScalarOps.Reading (V := V) IpaScalarOps.step IpaEndo.pallas.d.W where
  wit := ℤ × Bool
  Pre := StepLadderPre V
  Reg := StepLadderReg
  dec := stepLadderDec
  WellFormed x := ∃ bb : Bool, (↑x.val.sOdd : CVar Fp).val V = bit bb
  scale pt x h := h.elim fun bb hbit => step_scale_reads pt x bb hbit
  PreCip := StepCipPre V
  preCip_pre h := h.1
  scaleCip pt x h := h.elim fun bb hbit => step_scaleCip_reads pt x bb hbit

end Deployed


section GroupMapBridge

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Curves.Pasta Poseidon.GroupMap
open WeierstrassCurve.Affine Bulletproof Bulletproof.Ipa

/-- Transporting a point along an equality of curves leaves its coordinates alone. What
`KimchiCurve.toGroup`'s `▸` amounts to at the coordinate level. -/
private theorem swpoint_cast {F : Type} [Field F] [DecidableEq F] {E₁ E₂ : SWCurve F}
    (h : E₁ = E₂) (P : SWPoint E₁) : (h ▸ P).x = P.x ∧ (h ▸ P).y = P.y := by
  subst h; exact ⟨rfl, rfl⟩

/-- No candidate ordinate square vanishes on a shaped curve: a point with ordinate zero
would be 2-torsion, and a shaped curve's group has none. -/
theorem PastaShape.curveEqn_ne_zero {C : KimchiCurve} (sh : PastaShape C) (x : C.BaseField) :
    curveEqn C.groupMap x ≠ 0 := by
  intro h0
  have hE : C.groupMap.E = C.E := C.groupMap_E
  have hA : C.E.A = 0 := hE ▸ C.groupMap.hA
  simp only [curveEqn, hE] at h0
  have hon : OnCurve C.E.A C.E.B (x, 0) := by
    simp only [OnCurve, hA, zero_mul, _root_.add_zero]
    simpa using h0.symm
  have hns := nonsingular_toW hon
  exact sh.d.two_torsion_free _ (Point.some_ne_zero hns)
    (Point.add_self_of_Y_eq (by simp [negY, toW]))

/-- The map-to-curve gadget at a shaped curve's own SvdW spec reads as the wire map
`KimchiCurve.toGroup`, up to the sign of the ordinate — the constraints pin the root's
square, not its sign. The only datum beyond the curve is the non-residue the in-circuit
flagged-root trick needs, which the wire map has no counterpart for. -/
theorem groupMap_reads {C : KimchiCurve} (sh : PastaShape C) {V : Valuation C.BaseField}
    (sqrtF : C.BaseField → Option C.BaseField) (t : FVar C.BaseField) :
    ⦃⌜True⌝⦄
    groupMapCircuit (c := Builder V (KimchiConstraint C.BaseField)) sqrtF
      (.ofSpec C.groupMap) t
    ⦃⇓ r _ => ⌜∃ U : C.E.toAffine.Point, OnCurveAt C.E.toAffine V r U ∧
      (U = SWPoint.equivPoint C.E (C.toGroup (t.val V)) ∨
        U = -SWPoint.equivPoint C.E (C.toGroup (t.val V)))⌝⦄ := by
  haveI := C.primeBase
  have hE : C.groupMap.E = C.E := C.groupMap_E
  have hgx : (C.toGroup (t.val V)).x = (toGroup C.groupMap (t.val V)).x :=
    (swpoint_cast C.groupMap_E _).1
  have hgy : (C.toGroup (t.val V)).y = (toGroup C.groupMap (t.val V)).y :=
    (swpoint_cast C.groupMap_E _).2
  rw [builder_spec_iff]
  intro nv hsat
  obtain ⟨hx, hy⟩ := (builder_spec_iff _ _).mp (groupMapCircuit_toGroup_spec (V := V)
    (c := KimchiConstraint C.BaseField) C.groupMap sh.curveEqn_ne_zero sqrtF t) nv hsat
  obtain ⟨-, hcurve⟩ := (builder_spec_iff _ _).mp (groupMapCircuit_spec (V := V)
    (c := KimchiConstraint C.BaseField) sqrtF (.ofSpec C.groupMap) t) nv hsat
  rw [← hgx] at hx
  rw [← hgy] at hy
  generalize (build (groupMapCircuit (c := Builder V (KimchiConstraint C.BaseField)) sqrtF
    (.ofSpec C.groupMap) t) nv).result = r at hx hy hcurve ⊢
  generalize C.toGroup (t.val V) = P at hx hy ⊢
  have hon : OnCurve C.E.A C.E.B (P.x, P.y) := by
    rcases P.onCurve with h | h
    · exact h
    · exfalso
      obtain ⟨hpx, hpy⟩ := Prod.mk.injEq _ _ _ _ ▸ h
      rw [hpx] at hx
      rw [hpy] at hy
      have hy0 : r.y.val V = 0 := by rcases hy with hy | hy <;> simp [hy]
      rw [hy0, hx] at hcurve
      simp [ySquared, GroupMapParams.ofSpec] at hcurve
      exact C.E.B_nonzero (hE ▸ hcurve.symm)
  have hns := nonsingular_toW hon
  rw [SWPoint.equivPoint_eq_some P hon]
  rcases hy with hy | hy
  · exact ⟨_, OnCurveAt.of_reads hx hy hns, Or.inl rfl⟩
  · have hr' : OnCurveAt (toW C.E.A C.E.B) V ⟨r.x, CVar.negate_ r.y⟩
        (Point.some P.x P.y hns) :=
      OnCurveAt.of_reads (p := ⟨r.x, CVar.negate_ r.y⟩) hx
        (by simp only [CVar.val_negate_, hy, _root_.neg_neg]) hns
    have hneg := OnCurveAt.neg ⟨rfl, rfl⟩ hr'
    refine ⟨-(Point.some P.x P.y hns), ?_, Or.inr rfl⟩
    have hval : (CVar.negate_ (CVar.negate_ r.y)).val V = r.y.val V := by
      simp only [CVar.val_negate_, _root_.neg_neg]
    simpa only [OnCurveAt, hval] using hneg

/-- The wrap side's group-map parameters (PS `groupMapParams (Proxy @VestaG)`): Vesta's own
BW19 `setup()` spec, read as the gadget's parameter record. -/
abbrev groupMapParamsVesta : GroupMapParams Fq := .ofSpec IpaVesta.curve.groupMap

/-- The step side's group-map parameters (PS `groupMapParams (Proxy @PallasG)`): Pallas's own
BW19 `setup()` spec, read as the gadget's parameter record. -/
abbrev groupMapParamsPallas : GroupMapParams Fp := .ofSpec IpaPallas.curve.groupMap

end GroupMapBridge


/-! ## The bridge to the wire group

Pure algebra, no circuit: the gadgets' readings live in Mathlib's point group with integer
scalars, the wire verifier in `SWPoint` with `ZMod`-valued scalars acting by their canonical
representatives. The lemmas below move the Schnorr equation between the two forms. -/

section Bridge

variable {G : Type} [AddCommGroup G]

omit [Field F] [DecidableEq F] [ToNat F] in
/-- In a group killed by `n`, the representative of a product acts as the composite. -/
private theorem val_mul_nsmul (n : ℕ) [NeZero n] (hn : ∀ x : G, n • x = 0) (a b : ZMod n) (X : G) :
    (a * b).val • X = a.val • b.val • X := by
  rw [ZMod.val_mul, ← mul_nsmul']
  conv_rhs => rw [← Nat.mod_add_div (a.val * b.val) n, add_nsmul, mul_nsmul', hn, _root_.add_zero]

omit [Field F] [DecidableEq F] [ToNat F] in
/-- The wire's polyscale combination is Horner's rule over the list, the scalar acting by its
representative — on any commitment curve whose point group its scalar order kills. -/
theorem combineCommitments_eq_foldr (C : Bulletproof.Ipa.KimchiCurve)
    (ξ : C.ScalarField) (cs : List C.Point) :
    Bulletproof.Ipa.combineCommitments C ξ cs.toArray
      = cs.foldr (fun P acc => P + ξ.val • acc) 0 := by
  have hn : ∀ x : C.Point, C.scalar • x = 0 := C.card_nsmul
  have key : ∀ (l : List C.Point) (acc : C.Point) (pw : C.ScalarField),
      (l.foldl (fun (acc : C.Point × C.ScalarField) P => (acc.1 + acc.2.val • P, acc.2 * ξ))
        (acc, pw)).1 = acc + pw.val • l.foldr (fun P acc => P + ξ.val • acc) 0 := by
    intro l
    induction l with
    | nil => intro acc pw; simp
    | cons P l ih =>
      intro acc pw
      rw [List.foldl_cons, ih, List.foldr_cons, nsmul_add, val_mul_nsmul C.scalar hn,
        _root_.add_assoc]
  unfold Bulletproof.Ipa.combineCommitments
  rw [← Array.foldl_toList, List.toList_toArray, key, ZMod.val_one, one_nsmul, _root_.zero_add]

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

section Transport

open CompElliptic.CurveForms.ShortWeierstrass Poseidon.FqSponge
open Kimchi.Gate.EndoScalar Bulletproof Bulletproof.Ipa

variable {C : KimchiCurve} (sh : PastaShape C)

include sh in
/-- The gadgets' integer endo-expansion at the curve's eigenvalue casts to the wire's. -/
private theorem endoExpandZ_cast' (n : ℕ) :
    ((endoExpandZ C.endo.lam n : ℤ) : C.ScalarField) = endoExpand C.lam n :=
  endoExpandZ_cast sh.scalar_two_ne sh.scalar_three_ne C.endo.lam n

/-- The inverse's representative does not depend on how the order is named. -/
private theorem zmod_inv_val_congr (n m : ℕ) (h : n = m) (z : ℤ) :
    ((z : ZMod n)⁻¹).val = ((z : ZMod m)⁻¹).val := by
  subst h
  rfl

/-- A round term of `lr_prod`, read back in the wire group, is the wire's round term at the
expanded challenge. -/
private theorem lrTerm_eq (sh : PastaShape C) (q : C.Point × C.Point) (n : ℕ) :
    (SWPoint.equivPoint C.E).symm
        (lrTerm C.endo.lam ((SWPoint.equivPoint C.E) q.1, (SWPoint.equivPoint C.E) q.2) n)
      = ((endoExpand C.lam n)⁻¹).val • q.1 + (endoExpand C.lam n).val • q.2 := by
  unfold lrTerm
  rw [map_add]
  rw [map_nsmul, map_zsmul]
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  rw [zmod_inv_val_congr _ C.scalar C.order_eq]
  rw [endoExpandZ_cast' sh]
  rw [Pasta.zsmul_eq_val_nsmul C.scalar, endoExpandZ_cast' sh]

/-- The round terms of `lr_prod`, read back in the wire group, are the wire's round terms at
the expanded challenges. -/
private theorem zipTerms (sh : PastaShape C) :
    ∀ (l : List (C.Point × C.Point)) (ns : List ℕ),
      (List.zipWith (lrTerm C.endo.lam)
        (l.map fun q => ((SWPoint.equivPoint C.E) q.1, (SWPoint.equivPoint C.E) q.2)) ns).map
        (SWPoint.equivPoint C.E).symm
      = (l.zip (ns.map (endoExpand C.lam))).map
          fun x => (x.2⁻¹).val • x.1.1 + x.2.val • x.1.2
  | [], _ => by simp
  | _ :: _, [] => by simp
  | q :: l, n :: ns => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.zip_cons_cons, lrTerm_eq sh]
    exact congrArg _ (zipTerms sh l ns)

/-- Horner's rule over the kept bases, read back in the wire group, is the wire's polyscale
combination at the expanded challenge. -/
theorem hornerCombine_eq (sh : PastaShape C) (n : ℕ) (bvW : List (C.Point × Bool))
    (hlast : ∀ h, bvW.getLast? = some h → h.2 = true) :
    (SWPoint.equivPoint C.E).symm
        (hornerCombine (endoExpandZ C.endo.lam n)
          (bvW.map fun b => ((SWPoint.equivPoint C.E) b.1, b.2)))
      = combineCommitments C (endoExpand C.lam n)
          ((bvW.filter (·.2)).map (·.1)).toArray := by
  have hlast' : ∀ h, (bvW.map fun b => ((SWPoint.equivPoint C.E) b.1, b.2)).getLast?
      = some h → h.2 = true := by
    intro h hh
    rw [List.getLast?_map] at hh
    rcases hl : bvW.getLast? with _ | g
    · rw [hl] at hh; cases hh
    · rw [hl] at hh
      simp only [Option.map_some, Option.some.injEq] at hh
      rw [← hh]
      exact hlast g hl
  rw [hornerCombine_eq_foldr _ _ hlast', combineCommitments_eq_foldr C]
  have hfl : (bvW.map fun b => ((SWPoint.equivPoint C.E) b.1, b.2)).filter (·.2)
      = (bvW.filter (·.2)).map fun b => ((SWPoint.equivPoint C.E) b.1, b.2) := by
    rw [List.filter_map]; rfl
  have hm : ((·.1) ∘ fun b : C.Point × Bool =>
      ((SWPoint.equivPoint C.E) b.1, b.2)) = (SWPoint.equivPoint C.E) ∘ (·.1) := rfl
  rw [hfl, List.map_map, hm, ← List.map_map, ← endoExpandZ_cast' sh]
  generalize (bvW.filter (·.2)).map (·.1) = cs
  generalize endoExpandZ C.endo.lam n = z
  induction cs with
  | nil => simp
  | cons P cs ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, map_add, map_zsmul, ih,
      AddEquiv.symm_apply_apply, Pasta.zsmul_eq_val_nsmul C.scalar]

/-- The bridge: the gadgets' Schnorr equation over Mathlib's point group, at the readings'
images under `SWPoint.equivPoint`, is the wire verifier's `schnorrAt` at the expanded
challenges and the cast scalars. -/
theorem schnorrPoint_iff_schnorrAt (sh : PastaShape C) (σ : SRS C.Point) (U P : C.Point)
    (chals : Vector C.ScalarField σ.k) (c₀ : ℕ) (cip b z₁ z₂ : ℤ) (pr : Ipa.Proof C σ.k)
    (ns : List ℕ) (hchals : chals.toList = ns.map (endoExpand C.lam))
    (hz1 : pr.z1 = (z₁ : C.ScalarField)) (hz2 : pr.z2 = (z₂ : C.ScalarField)) :
    SchnorrPoint C.endo.lam c₀ (SWPoint.equivPoint C.E U) (SWPoint.equivPoint C.E P)
        (lrSum (List.zipWith (lrTerm C.endo.lam) (pr.lr.toList.map fun q =>
          ((SWPoint.equivPoint C.E) q.1, (SWPoint.equivPoint C.E) q.2)) ns))
        (SWPoint.equivPoint C.E pr.delta) (SWPoint.equivPoint C.E pr.sg)
        (SWPoint.equivPoint C.E σ.h) cip b z₁ z₂
      ↔ schnorrAt C σ U chals (endoExpand C.lam c₀) (cip : C.ScalarField)
          (b : C.ScalarField) P pr := by
  have hsm : ∀ (z : ℤ) (X : C.E.toAffine.Point), z • X = ((z : C.ScalarField).val : ℕ) • X :=
    fun z X => Pasta.zsmul_eq_val_nsmul C.scalar z X
  have hzip := zipTerms sh pr.lr.toList ns
  -- the wire's fold as a start plus a sum
  have hfold : ∀ (l : List ((C.Point × C.Point) × C.ScalarField)) (init : C.Point),
      l.foldl (fun acc (LRu : (C.Point × C.Point) × C.ScalarField) =>
        acc + ((LRu.2⁻¹).val • LRu.1.1 + LRu.2.val • LRu.1.2)) init
        = init + (l.map fun x => (x.2⁻¹).val • x.1.1 + x.2.val • x.1.2).sum := by
    intro l init
    rw [← List.foldl_map, foldl_add_eq]
  unfold SchnorrPoint schnorrAt
  dsimp only
  rw [hz1, hz2, ← Array.foldl_toList, Array.toList_zip, hfold]
  have hl1 : pr.lr.toArray.toList = pr.lr.toList := rfl
  have hl2 : chals.toArray.toList = ns.map (endoExpand C.lam) := hchals
  rw [hl1, hl2]
  have hZ : List.zipWith (lrTerm C.endo.lam) (List.map (fun q =>
        ((SWPoint.equivPoint C.E) q.1, (SWPoint.equivPoint C.E) q.2)) pr.lr.toList) ns
      = ((pr.lr.toList.zip (ns.map (endoExpand C.lam))).map
          fun x => (x.2⁻¹).val • x.1.1 + x.2.val • x.1.2).map (SWPoint.equivPoint C.E) := by
    rw [← hzip, List.map_map]
    simp only [Function.comp_def, AddEquiv.apply_symm_apply, List.map_id']
  have key1 : (SWPoint.equivPoint C.E) ((endoExpand C.lam c₀).val •
        (P + (cip : C.ScalarField).val • U + ((pr.lr.toList.zip (ns.map (endoExpand C.lam))).map
            fun x => (x.2⁻¹).val • x.1.1 + x.2.val • x.1.2).sum) + pr.delta)
      = endoExpandZ C.endo.lam c₀ • ((SWPoint.equivPoint C.E) P +
          cip • (SWPoint.equivPoint C.E) U +
          lrSum (List.zipWith (lrTerm C.endo.lam) (List.map (fun q =>
            ((SWPoint.equivPoint C.E) q.1, (SWPoint.equivPoint C.E) q.2))
              pr.lr.toList) ns)) + (SWPoint.equivPoint C.E) pr.delta := by
    rw [hZ, lrSum_eq_sum, ← map_list_sum, map_add, map_nsmul, map_add, map_add, map_nsmul,
      hsm (endoExpandZ _ _), endoExpandZ_cast' sh, hsm cip]
  have key2 : (SWPoint.equivPoint C.E)
        ((z₁ : C.ScalarField).val • pr.sg + ((z₁ : C.ScalarField) * (b : C.ScalarField)).val • U
          + (z₂ : C.ScalarField).val • σ.h)
      = z₁ • ((SWPoint.equivPoint C.E) pr.sg + b • (SWPoint.equivPoint C.E) U)
        + z₂ • (SWPoint.equivPoint C.E) σ.h := by
    rw [map_add, map_add, map_nsmul, map_nsmul, map_nsmul, smul_add, ← mul_zsmul, hsm z₁,
      hsm (z₁ * b), hsm z₂, Int.cast_mul]
  rw [← key1, ← key2]
  exact (SWPoint.equivPoint C.E).injective.eq_iff

end Transport

section DeployedWrap

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass Poseidon.FqSponge
open Kimchi.Gate.EndoScalar Kimchi.Gate.VarBaseMul Bulletproof Bulletproof.Ipa

/-- The wrap circuit absorbs the claimed `cip` as its one `Type1` limb, and the wire absorbs
`scalarLimbs (shiftScalar cip)`: at Vesta these agree, the ladder witness bounding the cell
below the scalar modulus so the decode's re-shift is the cell. -/
private theorem wrap_cip_limbs {V : Valuation Fq} {x : Type1 (FVar Fq)} {z : ℤ}
    (h : WrapLadderPre V x z) :
    ((IpaScalarOps.wrap (c := Builder V (KimchiConstraint Fq))).shiftedToAbsorbFields x).map
        (·.val V)
      = scalarLimbs IpaVesta.curve (shiftScalar IpaVesta.curve (wrapDecode V x)) := by
  show [x.val.val V] = _
  symm
  have hsz : Nat.size IpaVesta.curve.scalar = 255 :=
    le_antisymm (Nat.size_le.mpr (by norm_num [PALLAS_BASE_CARD]))
      (Nat.lt_size.mpr (by norm_num [PALLAS_BASE_CARD]))
  have hlt : IpaVesta.curve.scalar < IpaVesta.curve.base := by decide
  simp only [scalarLimbs, shiftScalar, if_pos hlt, hsz, wrapDecode,
    Pasta.Shifted.shiftType1_unshiftType1 (by decide : (2 : Fp) ≠ 0)]
  have hval : ((x.val.val V).val : ℤ) = z := (wrapLadderPre_eq h).symm
  have hlt' : z < 2 ^ 254 := h.2.1
  have hv : (x.val.val V).val < PALLAS_BASE_CARD := by
    have : ((x.val.val V).val : ℤ) < 2 ^ 254 := hval ▸ hlt'
    have : (x.val.val V).val < 2 ^ 254 := by exact_mod_cast this
    exact lt_trans this (by norm_num [PALLAS_BASE_CARD])
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hv, ZMod.natCast_zmod_val]

/-- **Vesta's gadget facts** (`IpaVesta.curve`, base `Fq`, scalar `Fp`): the Vesta map-to-curve
parameters with their bridge, the Pasta shape, and the two generic transport bridges at it. -/
theorem IvpCurve.vesta : IvpCurve IpaVesta.curve where
  shape := pastaShapeVesta
  groupMap _ sqrtF t := groupMap_reads pastaShapeVesta sqrtF t
  horner n bvW hlast := hornerCombine_eq pastaShapeVesta n bvW hlast
  schnorr σ U P chals c₀ cip b z₁ z₂ pr ns h1 h2 h3 :=
    schnorrPoint_iff_schnorrAt pastaShapeVesta σ U P chals c₀ cip b z₁ z₂ pr ns h1 h2 h3

/-- **The wrap side**: `IpaScalarOps.wrap` at Vesta through `wrapReading`, the `Type1` claims
decoding by `wrapDecode`, every claim canonical. The decodes are canonical because `scaleFast1`
pins the top bit of its 255-bit decomposition (`scale_fast`'s check): without it `t` and
`t + |Fq|` would both be admissible witnesses of a shifted value `t`, the second decoding to the
scalar plus `2·(|Fq| − |Fp|)`. Its opening check reads as the wire's by
`IvpSide.opening_reads`; with `verifyWith_eq`,
`success ∧ sg = ⟨bPolyCoefficients chals, g⟩` is `verifyWith` at those readings. -/
def wrapSide (V : Valuation Fq) : IvpSide IpaVesta.curve V IpaScalarOps.wrap where
  curve := IvpCurve.vesta
  R := wrapReading V
  decode := wrapDecode V
  dec_cast h := wrapLadderDec_cast h
  absorb_limbs h := wrap_cip_limbs h

end DeployedWrap

section DeployedStep

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass Poseidon.FqSponge
open Kimchi.Gate.EndoScalar Kimchi.Gate.VarBaseMul Bulletproof Bulletproof.Ipa Pasta.Shifted

/-- The `cip` ladder's pin makes the claim canonical: with the half below `2²⁵³`,
`2·sDiv2 + sOdd` is below `2²⁵⁴`, under the scalar modulus. -/
private theorem stepCipPre_canon {V : Valuation Fp}
    {x : Type2 (SplitField (FVar Fp) (BoolVar Fp))} {w : ℤ × Bool} (h : StepCipPre V x w) :
    2 * (x.val.sDiv2.val V).val + ((↑x.val.sOdd : CVar Fp).val V).val < PALLAS_SCALAR_CARD := by
  obtain ⟨⟨hb, h0, hlt, hz⟩, h253⟩ := h
  have hv : (((w.1 : Fp)).val : ℤ) = w.1 :=
    toNat_intCast_of_lt PALLAS_BASE_CARD h0
      (lt_of_lt_of_le hlt (by norm_num [PALLAS_BASE_CARD]))
  rw [hz] at hv
  have hhalf : (x.val.sDiv2.val V).val < 2 ^ 253 := by
    have : ((x.val.sDiv2.val V).val : ℤ) < 2 ^ 253 := hv ▸ h253
    exact_mod_cast this
  have hon : ((↑x.val.sOdd : CVar Fp).val V).val ≤ 1 := by
    rw [hb]
    cases w.2 <;> simp [bit, ZMod.val_one]
  have hq : (2 : ℕ) ^ 254 < PALLAS_SCALAR_CARD := by norm_num [PALLAS_SCALAR_CARD]
  omega

/-- The step circuit absorbs the claimed `cip` as its halved limb then its parity bit, and the
wire absorbs `scalarLimbs (shiftScalar cip)`: at Pallas these agree when the claim is canonical
(`2·sDiv2 + sOdd` below the scalar modulus), the decode's re-shift then splitting back into the
cells. -/
private theorem step_cip_limbs {V : Valuation Fp} {x : Type2 (SplitField (FVar Fp) (BoolVar Fp))}
    (hc : 2 * (x.val.sDiv2.val V).val + ((↑x.val.sOdd : CVar Fp).val V).val < PALLAS_SCALAR_CARD)
    {w : ℤ × Bool} (h : StepLadderPre V x w) :
    ((IpaScalarOps.step (c := Builder V (KimchiConstraint Fp))).shiftedToAbsorbFields x).map
        (·.val V)
      = scalarLimbs IpaPallas.curve (shiftScalar IpaPallas.curve (stepDecode V x)) := by
  show [x.val.sDiv2.val V, (↑x.val.sOdd : CVar Fp).val V] = _
  obtain ⟨hb, -, -, -⟩ := h
  have hsz : Nat.size IpaPallas.curve.scalar = 255 :=
    le_antisymm (Nat.size_le.mpr (by norm_num [PALLAS_SCALAR_CARD]))
      (Nat.lt_size.mpr (by norm_num [PALLAS_SCALAR_CARD]))
  have hlt : ¬ IpaPallas.curve.scalar < IpaPallas.curve.base := by decide
  simp only [scalarLimbs, shiftScalar, if_neg hlt, hsz, stepDecode, shiftType2_unshiftType2]
  have hon : ((↑x.val.sOdd : CVar Fp).val V).val ≤ 1 := by
    rw [hb]
    cases w.2 <;> simp [bit, ZMod.val_one]
  have hsum : (2 * (((x.val.sDiv2.val V).val : ℕ) : Fq) + ((((↑x.val.sOdd : CVar Fp).val V).val :
      ℕ) : Fq)).val = 2 * (x.val.sDiv2.val V).val + ((↑x.val.sOdd : CVar Fp).val V).val := by
    have : (2 * (((x.val.sDiv2.val V).val : ℕ) : Fq) + ((((↑x.val.sOdd : CVar Fp).val V).val :
        ℕ) : Fq)) = ((2 * (x.val.sDiv2.val V).val + ((↑x.val.sOdd : CVar Fp).val V).val : ℕ) :
        Fq) := by push_cast; ring
    rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt hc]
  rw [hsum]
  have h1 : (2 * (x.val.sDiv2.val V).val + ((↑x.val.sOdd : CVar Fp).val V).val) / 2
      = (x.val.sDiv2.val V).val := by omega
  have h2 : (2 * (x.val.sDiv2.val V).val + ((↑x.val.sOdd : CVar Fp).val V).val) % 2
      = ((↑x.val.sOdd : CVar Fp).val V).val := by omega
  rw [h1, h2, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/-- **Pallas's gadget facts** (`IpaPallas.curve`, base `Fp`, scalar `Fq`): the Pallas
map-to-curve parameters with their bridge, the Pasta shape, and the two generic transport
bridges at it. -/
theorem IvpCurve.pallas : IvpCurve IpaPallas.curve where
  shape := pastaShapePallas
  groupMap _ sqrtF t := groupMap_reads pastaShapePallas sqrtF t
  horner n bvW hlast := hornerCombine_eq pastaShapePallas n bvW hlast
  schnorr σ U P chals c₀ cip b z₁ z₂ pr ns h1 h2 h3 :=
    schnorrPoint_iff_schnorrAt pastaShapePallas σ U P chals c₀ cip b z₁ z₂ pr ns h1 h2 h3

/-- **The step side**: `IpaScalarOps.step` at Pallas through `stepReading`, the split `Type2`
claims decoding by `stepDecode`. The decode is canonical (the half is unpacked in
`254 < log₂ |Fp|` bits), but a claim absorbs canonically only when its `2·sDiv2 + sOdd` is below
the scalar modulus: the 254-bit range check leaves one bit of slack over the honest half, the
`scale_fast2` top-bit family (#341). Its opening check reads as the wire's by
`IvpSide.opening_reads`; with `verifyWith_eq`,
`success ∧ sg = ⟨bPolyCoefficients chals, g⟩` is `verifyWith` at those readings. -/
def stepSide (V : Valuation Fp) : IvpSide IpaPallas.curve V IpaScalarOps.step where
  curve := IvpCurve.pallas
  R := stepReading V
  decode := stepDecode V
  dec_cast h := stepLadderDec_cast h
  absorb_limbs h := step_cip_limbs (stepCipPre_canon h) h.1

end DeployedStep

/-! ## The wire reading -/

open Kimchi.Verifier Bulletproof.Ipa in
/-- `CheckBulletproofReads` at a deployed field, against the wire verifier: with `(t, us, c)`
the verifier's `ipaPrechallenges`, `t` reads exactly, and each round prechallenge and `c`,
once read as a prechallenge, is its counterpart
(`transcriptFrom_eq_ipaPrechallenges` carries these to `transcriptFrom`'s `U` base, round
challenges and Schnorr challenge). -/
def CheckBulletproofReadsWire {p : ℕ} [Fact p.Prime] (params : Poseidon.Params (ZMod p))
    (s₀ : Poseidon.State (ZMod p)) (cipLimbs : List (ZMod p))
    (lrv : List (AffinePoint (ZMod p) × AffinePoint (ZMod p))) (δv : AffinePoint (ZMod p))
    (V : Valuation (ZMod p)) (o : CheckBulletproofOutput (ZMod p)) : Prop :=
  let r := ipaPrechallenges params s₀ cipLimbs (lrv.map coordsPair) (δv.x, δv.y)
  o.t.val V = r.1 ∧
  List.Forall₂ (fun (pre : ℕ) (u : SizedF 128 (FVar (ZMod p))) =>
    ∀ m, Reads128 V u m → m.val = pre) r.2.1 o.challenges ∧
  (∀ m, Reads128 V o.c m → m.val = r.2.2)

open Kimchi.Verifier Bulletproof.Ipa in
/-- At a prime field, the exact reading is the wire reading (`Low128.exact`). -/
theorem CheckBulletproofReads.wire {p : ℕ} [Fact p.Prime]
    {params : Poseidon.Params (ZMod p)} {s₀ : Poseidon.State (ZMod p)} {cipLimbs : List (ZMod p)}
    {lrv : List (AffinePoint (ZMod p) × AffinePoint (ZMod p))} {δv : AffinePoint (ZMod p)}
    {V : Valuation (ZMod p)} {o : CheckBulletproofOutput (ZMod p)}
    (h : CheckBulletproofReads params s₀ cipLimbs lrv δv V o) :
    CheckBulletproofReadsWire params s₀ cipLimbs lrv δv V o := by
  obtain ⟨ht, hus, hlc⟩ := h
  refine ⟨ht, ?_, fun _ hm => (hlc.exact hm).symm⟩
  simp only [ipaPrechallenges]
  refine List.forall₂_map_left_iff.mpr (hus.imp ?_)
  intro _ _ hl m hm
  exact (hl.exact hm).symm

/-! The gadgets are sealed after their reads: a consumer composes `checkBulletproof_reads` and
`IvpSide.opening_reads`, never the bodies. -/
attribute [irreducible] extractScalarChallenges bulletTerms sumPoints bulletReduce hornerFold
  combinePolynomials ipaFinalCheck checkBulletproof

end Pickles
