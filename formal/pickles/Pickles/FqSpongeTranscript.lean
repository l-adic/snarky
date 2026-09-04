import Snarky.Kimchi.Circuit.Sponge
import Snarky.Kimchi.Circuit.RangeCheck
import Snarky.Kimchi.Circuit.AddComplete
import Kimchi.Verifier.Kimchi
import Pickles.OptSponge

set_option mvcgen.warning false

/-!
# The fq-sponge transcript in circuit

Port of the PureScript `Pickles.IncrementallyVerifyProof.FqSpongeTranscript.spongeTranscriptCircuit`
(OCaml `step_verifier.ml` `incrementally_verify_proof`, steps 1–3; kimchi `verifier.rs`
`oracles`): the group side's Fiat–Shamir schedule over the plain sponge — absorb the index
digest, pickles' `sg_old` commitments, `x_hat` (computed at that point of the schedule),
`w_comm`; squeeze `β`, `γ`; absorb `z_comm`; squeeze `α`; absorb `t_comm`; squeeze `ζ`; and
squeeze the digest from a copy. The four challenges leave as 128-bit prechallenges, never
expanded here.

## Main definitions

* `squeezePrechallenge`: one squeeze split by `lowest128Bits'` — OCaml's
  `squeeze_challenge` (low bits constrained) and `squeeze_scalar` (not).
* `fqSpongeTranscript`: the schedule, with the `x_hat` computation an action run after the
  `sg_old` absorbs, as the verifiers do.
* `FqTranscriptReads`, `FqTranscriptReadsWire`: the reading of the outputs against the wire
  verifier's `Kimchi.Verifier.fqSqueezes`, and its deployed-field form against
  `fqPrechallenges` up to `PrechallengeAlias`.

## Main results

* `fqSpongeTranscript_spec`: the four outputs are 128-bit decompositions of the wire
  verifier's four raw squeezes, `β, γ` below `2¹²⁸`, the digest reads as the digest element
  and the returned sponge as the pre-digest state.
* `FqTranscriptReads.wire`: at a prime field of more than 254 bits, `β, γ` are the verifier's
  prechallenges up to alias, and so are `α, ζ` once identified with 128-bit claims.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c]

/-- Absorb a point (PS `absorbPoint`): `x` then `y`. -/
private def absorbPoint (p : Poseidon.Params F) (sv : SpongeVar F) (P : AffinePoint (FVar F)) :
    CircuitM F c (SpongeVar F) := do
  let sv ← SpongeVar.absorb p sv P.x
  SpongeVar.absorb p sv P.y

/-- Absorb points, left to right. -/
private def absorbPoints (p : Poseidon.Params F) :
    SpongeVar F → List (AffinePoint (FVar F)) → CircuitM F c (SpongeVar F)
  | sv, [] => pure sv
  | sv, P :: Ps => do
    let sv' ← absorbPoint p sv P
    absorbPoints p sv' Ps

/-- Absorb column commitments, each a chunk list, left to right. -/
private def absorbColumns (p : Poseidon.Params F) :
    SpongeVar F → List (List (AffinePoint (FVar F))) → CircuitM F c (SpongeVar F)
  | sv, [] => pure sv
  | sv, col :: cols => do
    let sv' ← absorbPoints p sv col
    absorbColumns p sv' cols

/-- One squeeze split to its low 128 bits (PS `squeezeScalarChallenge` at `true`,
`squeezeScalar` at `false`): OCaml's `squeeze_challenge` / `squeeze_scalar`. -/
def squeezePrechallenge [ToNat F] (p : Poseidon.Params F) (constrainLowBits : Bool)
    (endo : FVar F) (sv : SpongeVar F) : CircuitM F c (SizedF 128 (FVar F) × SpongeVar F) := do
  let (x, sv) ← SpongeVar.squeeze p sv
  let chal ← lowest128Bits' constrainLowBits endo x
  pure (chal, sv)

/-- The transcript's outputs (PS `FqSpongeStepOutput`): the four 128-bit prechallenges,
the `x_hat` computed inside the schedule, the digest, and the sponge at
`sponge_before_evaluations`. -/
structure FqTranscriptOutput (F : Type) where
  /-- `β`, low bits constrained. -/
  beta : SizedF 128 (FVar F)
  /-- `γ`, low bits constrained. -/
  gamma : SizedF 128 (FVar F)
  /-- `α`, low bits unconstrained. -/
  alpha : SizedF 128 (FVar F)
  /-- `ζ`, low bits unconstrained. -/
  zeta : SizedF 128 (FVar F)
  /-- The public-input commitment, computed inside the schedule. -/
  xHat : List (AffinePoint (FVar F))
  /-- The digest before evaluations. -/
  digest : FVar F
  /-- The sponge at `sponge_before_evaluations`, continued by `check_bulletproof`. -/
  sponge : SpongeVar F

/-- The step side's fq-sponge transcript (PS `spongeTranscriptCircuit`): the index digest,
`sg_old`, then `computeXHat` run at that point of the schedule and its result absorbed,
`w_comm`, `β` and `γ` by `squeeze_challenge`, `z_comm`, `α` by `squeeze_scalar`, `t_comm`,
`ζ` by `squeeze_scalar`, and the digest squeezed from the pre-digest sponge, which is
returned. -/
def fqSpongeTranscript [ToNat F] (p : Poseidon.Params F) (endo indexDigest : FVar F)
    (sgOld : List (AffinePoint (FVar F)))
    (computeXHat : CircuitM F c (List (AffinePoint (FVar F))))
    (wComm : List (List (AffinePoint (FVar F)))) (zComm tComm : List (AffinePoint (FVar F))) :
    CircuitM F c (FqTranscriptOutput F) := do
  let sv ← SpongeVar.absorb p SpongeVar.init indexDigest
  let sv ← absorbPoints p sv sgOld
  let xHat ← computeXHat
  let sv ← absorbPoints p sv xHat
  let sv ← absorbColumns p sv wComm
  let (beta, sv) ← squeezePrechallenge p true endo sv
  let (gamma, sv) ← squeezePrechallenge p true endo sv
  let sv ← absorbPoints p sv zComm
  let (alpha, sv) ← squeezePrechallenge p false endo sv
  let sv ← absorbPoints p sv tComm
  let (zeta, sv) ← squeezePrechallenge p false endo sv
  let (digest, _) ← SpongeVar.squeeze p sv
  pure ⟨beta, gamma, alpha, zeta, xHat, digest, sv⟩

/-- The four deferred plonk claims, as 128-bit values. -/
structure PlonkClaims (F : Type) where
  /-- The `α` claim. -/
  alpha : SizedF 128 (FVar F)
  /-- The `β` claim. -/
  beta : SizedF 128 (FVar F)
  /-- The `γ` claim. -/
  gamma : SizedF 128 (FVar F)
  /-- The `ζ` claim. -/
  zeta : SizedF 128 (FVar F)

/-- Assert the squeezed prechallenges equal the deferred plonk claims (PS
`assertPlonkChallenges`, `step_verifier.ml:706-712`): `β, γ, α, ζ` in that order. -/
def assertPlonkChallenges (o : FqTranscriptOutput F) (claims : PlonkClaims F) :
    CircuitM F c PUnit := do
  assertEqual o.beta.val claims.beta.val
  assertEqual o.gamma.val claims.gamma.val
  assertEqual o.alpha.val claims.alpha.val
  assertEqual o.zeta.val claims.zeta.val


/-! ## The wrap side, on the conditional sponge -/

open OptSponge in
/-- Absorb a point unconditionally (PS `optAbsorbPoint`): `x` then `y` under `true_`. -/
private def optAbsorbPoint (ov : OptSpongeVar F) (P : AffinePoint (FVar F)) : OptSpongeVar F :=
  optAbsorb (optAbsorb ov (true_, P.x)) (true_, P.y)

open OptSponge in
/-- Absorb a masked point (PS `spongeTranscriptOptCircuit`'s `sg_old` loop): `x` then `y`
under the mask bit. -/
private def optAbsorbMasked (ov : OptSpongeVar F) (m : BoolVar F × AffinePoint (FVar F)) :
    OptSpongeVar F :=
  optAbsorb (optAbsorb ov (m.1, m.2.x)) (m.1, m.2.y)

open OptSponge in
/-- One squeeze of the conditional sponge split to its low 128 bits (PS `optChallenge` at
`true`, `optScalarChallenge` at `false`). -/
def optSqueezePrechallenge [ToNat F] (p : Poseidon.Params F) (constrainLowBits : Bool)
    (endo : FVar F) (ov : OptSpongeVar F) :
    CircuitM F c (SizedF 128 (FVar F) × OptSpongeVar F) := do
  let (x, ov) ← optSqueeze p ov
  let chal ← lowest128Bits' constrainLowBits endo x
  pure (chal, ov)

open OptSponge in
/-- The wrap side's fq-sponge transcript (PS `spongeTranscriptOptCircuit`): the step side's
schedule on the conditional sponge, `sg_old` absorbed under its mask bits and `x_hat` given,
the sponge handed to the plain sponge at `sponge_before_evaluations`, which is returned, and
the digest squeezed from it. -/
def fqSpongeTranscriptOpt [ToNat F] (p : Poseidon.Params F) (endo indexDigest : FVar F)
    (sgOld : List (BoolVar F × AffinePoint (FVar F))) (xHat : List (AffinePoint (FVar F)))
    (wComm : List (List (AffinePoint (FVar F)))) (zComm tComm : List (AffinePoint (FVar F))) :
    CircuitM F c (FqTranscriptOutput F) := do
  let ov := optAbsorb create (true_, indexDigest)
  let ov := sgOld.foldl optAbsorbMasked ov
  let ov := xHat.foldl optAbsorbPoint ov
  let ov := wComm.foldl (fun ov col => col.foldl optAbsorbPoint ov) ov
  let (beta, ov) ← optSqueezePrechallenge p true endo ov
  let (gamma, ov) ← optSqueezePrechallenge p true endo ov
  let ov := zComm.foldl optAbsorbPoint ov
  let (alpha, ov) ← optSqueezePrechallenge p false endo ov
  let ov := tComm.foldl optAbsorbPoint ov
  let (zeta, ov) ← optSqueezePrechallenge p false endo ov
  let sv := toRegularSponge ov
  let (digest, _) ← SpongeVar.squeeze p sv
  pure ⟨beta, gamma, alpha, zeta, xHat, digest, sv⟩

/-! ## Soundness -/

variable {V : Valuation F}

/-- A point's coordinates, the form `Kimchi.Verifier.fqSqueezes` takes. -/
private def coords (P : AffinePoint F) : F × F := (P.x, P.y)

omit [DecidableEq F] [BasicSystem F c] [KimchiSystem F c] in
/-- Points reading as values have the values' coordinates. -/
private theorem coords_of_reads :
    ∀ {Ps : List (AffinePoint (FVar F))} {vs : List (AffinePoint F)},
      List.Forall₂ (CircuitType.Reads V) Ps vs →
      Ps.map (fun P => (P.x.val V, P.y.val V)) = vs.map coords
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    obtain ⟨hx, hy⟩ := reads_affinePoint.mp h
    simp only [List.map_cons, hx, hy, coords_of_reads hs, coords]

omit [DecidableEq F] [BasicSystem F c] [KimchiSystem F c] in
/-- Columns reading as values have the values' coordinates, column by column. -/
private theorem coords_of_reads_cols :
    ∀ {cols : List (List (AffinePoint (FVar F)))} {vs : List (List (AffinePoint F))},
      List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) cols vs →
      cols.map (·.map fun P => (P.x.val V, P.y.val V)) = vs.map (·.map coords)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.map_cons, coords_of_reads h, coords_of_reads_cols hs]

omit [DecidableEq F] in
/-- The fresh circuit sponge reads as the fresh value sponge. -/
private theorem readsAt_init : SpongeVar.ReadsAt V (SpongeVar.init (F := F)) Poseidon.init :=
  ⟨rfl, rfl⟩

/-- Absorbing a point reads as absorbing its coordinates. -/
private theorem absorbPoint_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) (sv : SpongeVar F)
    (P : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄ absorbPoint (c := Builder V (KimchiConstraint F)) p sv P
    ⦃⇓ r _ => ⌜∀ s, SpongeVar.ReadsAt V sv s →
      SpongeVar.ReadsAt V r (Poseidon.absorb p s [P.x.val V, P.y.val V])⌝⦄ := by
  simp only [absorbPoint]
  have hx := fun sv x => SpongeVar.absorb_spec (V := V) p hsize sv x
  mvcgen [hx]
  · rename_i _ _ _ h1 _ _
    intro h2 s hs
    simpa [Poseidon.absorb] using h2 _ (h1 s hs)
  · intros
    exact hsize

/-- Absorbing points reads as the coordinate fold. -/
private theorem absorbPoints_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) :
    ∀ (sv : SpongeVar F) (Ps : List (AffinePoint (FVar F))),
      ⦃⌜True⌝⦄ absorbPoints (c := Builder V (KimchiConstraint F)) p sv Ps
      ⦃⇓ r _ => ⌜∀ s, SpongeVar.ReadsAt V sv s →
        SpongeVar.ReadsAt V r ((Ps.map fun P => (P.x.val V, P.y.val V)).foldl
          (fun s q => Poseidon.absorb p s [q.1, q.2]) s)⌝⦄
  | sv, [] => by
    simp only [absorbPoints]
    mvcgen
    simp
  | sv, P :: Ps => by
    simp only [absorbPoints]
    have hq := absorbPoint_spec (V := V) p hsize sv P
    have ih := fun sv' => absorbPoints_spec p hsize sv' Ps
    mvcgen [hq, ih]
    rename_i _ _ _ hstep _ _
    intro hrest s hs
    simpa using hrest _ (hstep s hs)

/-- Absorbing columns reads as the column fold. -/
private theorem absorbColumns_spec (p : Poseidon.Params F)
    (hsize : p.roundConstants.size = Poseidon.fullRounds) :
    ∀ (sv : SpongeVar F) (cols : List (List (AffinePoint (FVar F)))),
      ⦃⌜True⌝⦄ absorbColumns (c := Builder V (KimchiConstraint F)) p sv cols
      ⦃⇓ r _ => ⌜∀ s, SpongeVar.ReadsAt V sv s →
        SpongeVar.ReadsAt V r ((cols.map (·.map fun P => (P.x.val V, P.y.val V))).foldl
          (fun s l => l.foldl (fun s q => Poseidon.absorb p s [q.1, q.2]) s) s)⌝⦄
  | sv, [] => by
    simp only [absorbColumns]
    mvcgen
    simp
  | sv, col :: cols => by
    simp only [absorbColumns]
    have hc := absorbPoints_spec (V := V) p hsize sv col
    have ih := fun sv' => absorbColumns_spec p hsize sv' cols
    mvcgen [hc, ih]
    rename_i _ _ _ hstep _ _
    intro hrest s hs
    simpa using hrest _ (hstep s hs)

/-- A prechallenge squeeze reads as the low half of the value squeeze: `x = lo + 2¹²⁸·hi`
with `hi < 2¹²⁸`, `lo < 2¹²⁸` where constrained, the sponge as the squeezed state. -/
theorem squeezePrechallenge_spec [ToNat F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (constrainLowBits : Bool) (endo : FVar F) (sv : SpongeVar F) :
    ⦃⌜True⌝⦄ squeezePrechallenge (c := Builder V (KimchiConstraint F)) p constrainLowBits endo sv
    ⦃⇓ r _ => ⌜∀ s, SpongeVar.ReadsAt V sv s →
      (∃ hi : ℕ, hi < 2 ^ 128 ∧ (Poseidon.squeeze p s).1 = r.1.val.val V + 2 ^ 128 * hi) ∧
      (constrainLowBits = true → ∃ n : ℕ, n < 2 ^ 128 ∧ r.1.val.val V = n) ∧
      SpongeVar.ReadsAt V r.2 (Poseidon.squeeze p s).2⌝⦄ := by
  simp only [squeezePrechallenge]
  have hsq := SpongeVar.squeeze_spec (V := V) p hsize sv
  have hlo := fun x => lowest128Bits'_spec (V := V) h2 h3 constrainLowBits endo x
  mvcgen [hsq, hlo]
  rename_i _ x _ hx chal _ hchal
  intro s hs
  obtain ⟨hxv, hst⟩ := hx s hs
  obtain ⟨hiv, he, ⟨n, hn, rfl⟩, hlow⟩ := hchal
  exact ⟨⟨n, hn, by rw [← hxv, he]⟩, hlow, hst⟩

open Kimchi.Verifier in
/-- The reading of the transcript's outputs (`fqSpongeTranscript_spec`): with
`(β̂, γ̂, α̂, ζ̂)`, `d`, `warm` the wire verifier's `fqSqueezes` over the index digest, the
`sg_old`, `x_hat`, `w_comm`, `z_comm`, `t_comm` readings, each challenge is a 128-bit
decomposition `x̂ = chal + 2¹²⁸·h` with `h < 2¹²⁸`, `β, γ` below `2¹²⁸`, `x_hat` reads as
`xv`, the digest as `d` and the sponge as `warm`. -/
def FqTranscriptReads (p : Poseidon.Params F) (indexDigest : F)
    (sgOld xv : List (AffinePoint F)) (wComm : List (List (AffinePoint F)))
    (zComm tComm : List (AffinePoint F)) (V : Valuation F) (o : FqTranscriptOutput F) : Prop :=
  let r := fqSqueezes p indexDigest (sgOld.map coords) (xv.map coords)
    (wComm.map (·.map coords)) (zComm.map coords) (tComm.map coords)
  ∃ hβ hγ hα hζ : ℕ, hβ < 2 ^ 128 ∧ hγ < 2 ^ 128 ∧ hα < 2 ^ 128 ∧ hζ < 2 ^ 128 ∧
    r.1.1 = o.beta.val.val V + 2 ^ 128 * hβ ∧ r.1.2.1 = o.gamma.val.val V + 2 ^ 128 * hγ ∧
    r.1.2.2.1 = o.alpha.val.val V + 2 ^ 128 * hα ∧ r.1.2.2.2 = o.zeta.val.val V + 2 ^ 128 * hζ ∧
    (∃ n : ℕ, n < 2 ^ 128 ∧ o.beta.val.val V = n) ∧ (∃ n : ℕ, n < 2 ^ 128 ∧ o.gamma.val.val V = n) ∧
    List.Forall₂ (CircuitType.Reads V) o.xHat xv ∧
    o.digest.val V = r.2.1 ∧ SpongeVar.ReadsAt V o.sponge r.2.2

/-- Under any valuation satisfying the emitted constraints, with the commitments reading as
`sgv, wv, zv, tv` and `computeXHat`'s result as `xv`, the outputs satisfy
`FqTranscriptReads` at those readings. -/
theorem fqSpongeTranscript_spec [ToNat F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (endo indexDigest : FVar F) (sgOld : List (AffinePoint (FVar F))) (sgv : List (AffinePoint F))
    (hsg : List.Forall₂ (CircuitType.Reads V) sgOld sgv)
    (computeXHat : CircuitM F (Builder V (KimchiConstraint F)) (List (AffinePoint (FVar F))))
    (xv : List (AffinePoint F))
    (hx : ⦃⌜True⌝⦄ computeXHat ⦃⇓ pts _ => ⌜List.Forall₂ (CircuitType.Reads V) pts xv⌝⦄)
    (wComm : List (List (AffinePoint (FVar F)))) (wv : List (List (AffinePoint F)))
    (hw : List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) wComm wv)
    (zComm tComm : List (AffinePoint (FVar F))) (zv tv : List (AffinePoint F))
    (hz : List.Forall₂ (CircuitType.Reads V) zComm zv)
    (ht : List.Forall₂ (CircuitType.Reads V) tComm tv) :
    ⦃⌜True⌝⦄ fqSpongeTranscript (c := Builder V (KimchiConstraint F)) p endo indexDigest sgOld
      computeXHat wComm zComm tComm
    ⦃⇓ o _ => ⌜FqTranscriptReads p (indexDigest.val V) sgv xv wv zv tv V o⌝⦄ := by
  simp only [fqSpongeTranscript]
  have h0 := SpongeVar.absorb_spec (V := V) p hsize SpongeVar.init indexDigest
  have hpts := fun sv qs => absorbPoints_spec (V := V) p hsize sv qs
  have hcols := fun sv cols => absorbColumns_spec (V := V) p hsize sv cols
  have hpre := fun b sv => squeezePrechallenge_spec (V := V) h2 h3 p hsize b endo sv
  have hsq := fun sv => SpongeVar.squeeze_spec (V := V) p hsize sv
  mvcgen [h0, hpts, hx, hpts, hcols, hpre, hsq]
  rename_i _ svA _ hA svB _ hB xh _ hxh svC _ hC svD _ hD pβ _ pγ _ svE _ hE pα _ hα svF _ hF
    pζ _ hζ pd _ hdig hβ hγ
  have s1 := hA _ readsAt_init
  have s2 := hB _ s1
  have s3 := hC _ s2
  have s4 := hD _ s3
  obtain ⟨⟨nβ, hnβ, eβ⟩, ⟨mβ, hmβ, hbetaLo⟩, s5⟩ := hβ _ s4
  obtain ⟨⟨nγ, hnγ, eγ⟩, ⟨mγ, hmγ, hgammaLo⟩, s6⟩ := hγ _ s5
  have s7 := hE _ s6
  obtain ⟨⟨nα, hnα, eα⟩, -, s8⟩ := hα _ s7
  have s9 := hF _ s8
  obtain ⟨⟨nζ, hnζ, eζ⟩, -, s10⟩ := hζ _ s9
  obtain ⟨hdv, -⟩ := hdig _ s10
  simp only [Poseidon.absorb, List.foldl_cons, List.foldl_nil, coords_of_reads hsg,
    coords_of_reads hxh, coords_of_reads hz, coords_of_reads ht, coords_of_reads_cols hw]
    at eβ eγ eα eζ hdv s10
  unfold FqTranscriptReads fqSqueezes
  refine ⟨nβ, nγ, nα, nζ, hnβ, hnγ, hnα, hnζ, ?_, ?_, ?_, ?_, ⟨mβ, hmβ, hbetaLo⟩,
    ⟨mγ, hmγ, hgammaLo⟩, hxh, ?_, ?_⟩
  · exact eβ
  · exact eγ
  · exact eα
  · exact eζ
  · exact hdv
  · exact s10

/-- Under any valuation satisfying the emitted constraints, each claim reads as the
corresponding squeezed prechallenge. -/
theorem assertPlonkChallenges_spec (o : FqTranscriptOutput F) (claims : PlonkClaims F) :
    ⦃⌜True⌝⦄ assertPlonkChallenges (c := Builder V (KimchiConstraint F)) o claims
    ⦃⇓ _ _ => ⌜claims.beta.val.val V = o.beta.val.val V ∧
      claims.gamma.val.val V = o.gamma.val.val V ∧
      claims.alpha.val.val V = o.alpha.val.val V ∧ claims.zeta.val.val V = o.zeta.val.val V⌝⦄ := by
  simp only [assertPlonkChallenges]
  mvcgen
  intro hζ
  exact ⟨‹o.beta.val.val V = claims.beta.val.val V›.symm,
    ‹o.gamma.val.val V = claims.gamma.val.val V›.symm,
    ‹o.alpha.val.val V = claims.alpha.val.val V›.symm, hζ.symm⟩


/-! ## Soundness of the wrap side -/

open OptSponge

/-- The guarded flattening of masked points: each coordinate under the point's bit. -/
private def maskedFlat (l : List (Bool × AffinePoint F)) : List (Bool × F) :=
  l.flatMap fun v => [(v.1, v.2.x), (v.1, v.2.y)]

/-- The guarded flattening of unconditional points. -/
private def pointsFlat (l : List (AffinePoint F)) : List (Bool × F) :=
  l.flatMap fun P => [(true, P.x), (true, P.y)]

/-- A point's coordinate list, the wire verifier's absorb order. -/
private def flatCoords (l : List (AffinePoint F)) : List F :=
  l.flatMap fun P => [P.x, P.y]

omit [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c] in
private theorem length_maskedFlat : ∀ l : List (Bool × AffinePoint F),
    (maskedFlat l).length = 2 * l.length
  | [] => rfl
  | _ :: l => by
    have ih := length_maskedFlat l
    simp only [maskedFlat, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

omit [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c] in
private theorem length_pointsFlat : ∀ l : List (AffinePoint F),
    (pointsFlat l).length = 2 * l.length
  | [] => rfl
  | _ :: l => by
    have ih := length_pointsFlat l
    simp only [pointsFlat, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

omit [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c] in
private theorem length_flatMap_pointsFlat : ∀ l : List (List (AffinePoint F)),
    (l.flatMap pointsFlat).length = 2 * l.flatten.length
  | [] => rfl
  | _ :: l => by simp only [List.flatMap_cons, List.length_append, List.flatten_cons,
      length_pointsFlat, length_flatMap_pointsFlat l]; omega

omit [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c] in
/-- The kept entries of unconditional points are their coordinates. -/
private theorem kept_pointsFlat : ∀ l : List (AffinePoint F),
    ((pointsFlat l).filter (·.1)).map (·.2) = flatCoords l
  | [] => rfl
  | _ :: l => by
    have ih := kept_pointsFlat l
    simp only [pointsFlat, flatCoords] at ih
    simp [pointsFlat, flatCoords, ih]

omit [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c] in
/-- The kept entries of masked points are the kept points' coordinates. -/
private theorem kept_maskedFlat : ∀ l : List (Bool × AffinePoint F),
    ((maskedFlat l).filter (·.1)).map (·.2) = flatCoords ((l.filter (·.1)).map (·.2))
  | [] => rfl
  | (b, P) :: l => by
    have ih := kept_maskedFlat l
    simp only [maskedFlat, flatCoords] at ih
    cases b <;> simp [maskedFlat, flatCoords, ih]

omit [Field F] [DecidableEq F] [BasicSystem F c] [KimchiSystem F c] in
/-- The kept entries of columns are the columns' coordinates. -/
private theorem kept_flatMap_pointsFlat : ∀ l : List (List (AffinePoint F)),
    ((l.flatMap pointsFlat).filter (·.1)).map (·.2) = l.flatMap flatCoords
  | [] => rfl
  | _ :: l => by
    simp only [List.flatMap_cons, List.filter_append, List.map_append, kept_pointsFlat,
      kept_flatMap_pointsFlat l]

omit [DecidableEq F] [BasicSystem F c] [KimchiSystem F c] in
/-- Absorbing an appended list absorbs the halves in turn. -/
private theorem absorb_append (p : Poseidon.Params F) (s : Poseidon.State F) (l₁ l₂ : List F) :
    Poseidon.absorb p s (l₁ ++ l₂) = Poseidon.absorb p (Poseidon.absorb p s l₁) l₂ :=
  List.foldl_append ..

omit [DecidableEq F] [BasicSystem F c] [KimchiSystem F c] in
/-- The wire verifier's point fold is the absorb of the coordinates. -/
private theorem foldl_pts_eq (p : Poseidon.Params F) :
    ∀ (l : List (AffinePoint F)) (s : Poseidon.State F),
      (l.map coords).foldl (fun s q => Poseidon.absorb p s [q.1, q.2]) s
        = Poseidon.absorb p s (flatCoords l)
  | [], _ => rfl
  | P :: l, s => by
    simp only [List.map_cons, List.foldl_cons, foldl_pts_eq p l, flatCoords, List.flatMap_cons,
      absorb_append, coords]

omit [DecidableEq F] [BasicSystem F c] [KimchiSystem F c] in
/-- The wire verifier's column fold is the absorb of the columns' coordinates. -/
private theorem foldl_cols_eq (p : Poseidon.Params F) :
    ∀ (l : List (List (AffinePoint F))) (s : Poseidon.State F),
      (l.map (·.map coords)).foldl
          (fun s l => l.foldl (fun s q => Poseidon.absorb p s [q.1, q.2]) s) s
        = Poseidon.absorb p s (l.flatMap flatCoords)
  | [], _ => rfl
  | col :: l, s => by
    simp only [List.map_cons, List.foldl_cons, foldl_pts_eq, foldl_cols_eq p l, List.flatMap_cons,
      absorb_append]

omit [BasicSystem F c] [KimchiSystem F c] in
private theorem reads_true : CircuitType.Reads V (true_ : BoolVar F) true :=
  CircuitType.reads_boolVar.mpr (by simp [true_, bit])

omit [BasicSystem F c] [KimchiSystem F c] in
/-- Absorbing a point while absorbing appends its coordinates, kept. -/
private theorem optAbsorbPoint_reads {p : Poseidon.Params F} {ov : OptSpongeVar F} {ib : Bool}
    {ps₀ : Poseidon.State F} {pend : List (Bool × F)} (h : AbsorbingReads p V ov ib ps₀ pend)
    {P : AffinePoint (FVar F)} {Pv : AffinePoint F} (hP : CircuitType.Reads V P Pv) :
    AbsorbingReads p V (optAbsorbPoint ov P) ib ps₀ (pend ++ [(true, Pv.x), (true, Pv.y)]) := by
  obtain ⟨hx, hy⟩ := reads_affinePoint.mp hP
  have h1 := optAbsorb_reads_absorbing h (e := (true_, P.x)) (v := (true, Pv.x))
    (CircuitType.reads_prod.mpr ⟨reads_true, CircuitType.reads_fvar.mpr hx⟩)
  have h2 := optAbsorb_reads_absorbing h1 (e := (true_, P.y)) (v := (true, Pv.y))
    (CircuitType.reads_prod.mpr ⟨reads_true, CircuitType.reads_fvar.mpr hy⟩)
  simpa [optAbsorbPoint, List.append_assoc] using h2

omit [BasicSystem F c] [KimchiSystem F c] in
/-- Absorbing a point after a squeeze starts a block from the squeezed sponge with its
coordinates, kept. -/
private theorem optAbsorbPoint_reads_squeezed (p : Poseidon.Params F) {ov : OptSpongeVar F}
    {ps : Poseidon.State F} (h : SqueezedReads V ov ps)
    {P : AffinePoint (FVar F)} {Pv : AffinePoint F} (hP : CircuitType.Reads V P Pv) :
    AbsorbingReads p V (optAbsorbPoint ov P) false ps [(true, Pv.x), (true, Pv.y)] := by
  obtain ⟨hx, hy⟩ := reads_affinePoint.mp hP
  have h1 := optAbsorb_reads_squeezed p h (e := (true_, P.x)) (v := (true, Pv.x))
    (CircuitType.reads_prod.mpr ⟨reads_true, CircuitType.reads_fvar.mpr hx⟩)
  have h2 := optAbsorb_reads_absorbing h1 (e := (true_, P.y)) (v := (true, Pv.y))
    (CircuitType.reads_prod.mpr ⟨reads_true, CircuitType.reads_fvar.mpr hy⟩)
  simpa [optAbsorbPoint] using h2

omit [BasicSystem F c] [KimchiSystem F c] in
/-- Absorbing a masked point appends its coordinates under its bit. -/
private theorem optAbsorbMasked_reads {p : Poseidon.Params F} {ov : OptSpongeVar F} {ib : Bool}
    {ps₀ : Poseidon.State F} {pend : List (Bool × F)} (h : AbsorbingReads p V ov ib ps₀ pend)
    {m : BoolVar F × AffinePoint (FVar F)} {v : Bool × AffinePoint F}
    (hm : CircuitType.Reads V m v) :
    AbsorbingReads p V (optAbsorbMasked ov m) ib ps₀
      (pend ++ [(v.1, v.2.x), (v.1, v.2.y)]) := by
  obtain ⟨mb, mP⟩ := m
  obtain ⟨vb, vP⟩ := v
  obtain ⟨hb, hP⟩ := CircuitType.reads_prod.mp hm
  obtain ⟨hx, hy⟩ := reads_affinePoint.mp hP
  have h1 := optAbsorb_reads_absorbing h (e := (mb, mP.x)) (v := (vb, vP.x))
    (CircuitType.reads_prod.mpr ⟨hb, CircuitType.reads_fvar.mpr hx⟩)
  have h2 := optAbsorb_reads_absorbing h1 (e := (mb, mP.y)) (v := (vb, vP.y))
    (CircuitType.reads_prod.mpr ⟨hb, CircuitType.reads_fvar.mpr hy⟩)
  simpa [optAbsorbMasked, List.append_assoc] using h2

omit [BasicSystem F c] [KimchiSystem F c] in
/-- Absorbing points while absorbing appends their flattening. -/
private theorem foldl_optAbsorbPoint_reads {p : Poseidon.Params F} :
    ∀ {Ps : List (AffinePoint (FVar F))} {vs : List (AffinePoint F)},
      List.Forall₂ (CircuitType.Reads V) Ps vs →
      ∀ {ov : OptSpongeVar F} {ib : Bool} {ps₀ : Poseidon.State F} {pend : List (Bool × F)},
        AbsorbingReads p V ov ib ps₀ pend →
        AbsorbingReads p V (Ps.foldl optAbsorbPoint ov) ib ps₀ (pend ++ pointsFlat vs)
  | [], [], .nil, _, _, _, _, h => by simpa [pointsFlat] using h
  | _ :: _, _ :: _, .cons hP hs, _, _, _, _, h => by
    have := foldl_optAbsorbPoint_reads hs (optAbsorbPoint_reads h hP)
    simpa [pointsFlat, List.append_assoc] using this

omit [BasicSystem F c] [KimchiSystem F c] in
/-- Absorbing masked points appends their guarded flattening. -/
private theorem foldl_optAbsorbMasked_reads {p : Poseidon.Params F} :
    ∀ {ms : List (BoolVar F × AffinePoint (FVar F))} {vs : List (Bool × AffinePoint F)},
      List.Forall₂ (CircuitType.Reads V) ms vs →
      ∀ {ov : OptSpongeVar F} {ib : Bool} {ps₀ : Poseidon.State F} {pend : List (Bool × F)},
        AbsorbingReads p V ov ib ps₀ pend →
        AbsorbingReads p V (ms.foldl optAbsorbMasked ov) ib ps₀ (pend ++ maskedFlat vs)
  | [], [], .nil, _, _, _, _, h => by simpa [maskedFlat] using h
  | _ :: _, _ :: _, .cons hm hs, _, _, _, _, h => by
    have := foldl_optAbsorbMasked_reads hs (optAbsorbMasked_reads h hm)
    simpa [maskedFlat, List.append_assoc] using this

omit [BasicSystem F c] [KimchiSystem F c] in
/-- Absorbing columns appends their flattenings. -/
private theorem foldl_optAbsorbColumns_reads {p : Poseidon.Params F} :
    ∀ {cols : List (List (AffinePoint (FVar F)))} {vs : List (List (AffinePoint F))},
      List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) cols vs →
      ∀ {ov : OptSpongeVar F} {ib : Bool} {ps₀ : Poseidon.State F} {pend : List (Bool × F)},
        AbsorbingReads p V ov ib ps₀ pend →
        AbsorbingReads p V (cols.foldl (fun ov col => col.foldl optAbsorbPoint ov) ov) ib ps₀
          (pend ++ vs.flatMap pointsFlat)
  | [], [], .nil, _, _, _, _, h => by simpa using h
  | _ :: _, _ :: _, .cons hc hs, _, _, _, _, h => by
    have := foldl_optAbsorbColumns_reads hs (foldl_optAbsorbPoint_reads hc h)
    simpa [List.append_assoc] using this

/-- Under any valuation satisfying the emitted constraints, a prechallenge squeeze of the
conditional sponge reads by phase as `squeezePrechallenge_spec` does from the value squeeze
`optSqueeze_spec` gives: the low half of the squeeze, `lo < 2¹²⁸` where constrained, and the
sponge squeezed. -/
theorem optSqueezePrechallenge_spec [ToNat F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : F) = k → j = k)
    (constrainLowBits : Bool) (endo : FVar F) (ov : OptSpongeVar F) :
    ⦃⌜True⌝⦄ optSqueezePrechallenge (c := Builder V (KimchiConstraint F)) p constrainLowBits endo
      ov
    ⦃⇓ r _ => ⌜(∀ ps : Poseidon.State F, SqueezedReads V ov ps →
        (∃ hi : ℕ, hi < 2 ^ 128 ∧ (Poseidon.squeeze p ps).1 = r.1.val.val V + 2 ^ 128 * hi) ∧
        (constrainLowBits = true → ∃ n : ℕ, n < 2 ^ 128 ∧ r.1.val.val V = n) ∧
        SqueezedReads V r.2 (Poseidon.squeeze p ps).2) ∧
      (∀ (ib : Bool) (ps₀ : Poseidon.State F) (pend : List (Bool × F)),
        AbsorbingReads p V ov ib ps₀ pend →
        ((∃ v ∈ pend, v.1 = true) ∨ ps₀.mode = .absorbed 0) →
        (∀ k : ℕ, k ≤ pend.length → (k : F) = 0 → k = 0) →
        (∃ hi : ℕ, hi < 2 ^ 128 ∧
          (Poseidon.squeeze p (Poseidon.absorb p ps₀ ((pend.filter (·.1)).map (·.2)))).1
            = r.1.val.val V + 2 ^ 128 * hi) ∧
        (constrainLowBits = true → ∃ n : ℕ, n < 2 ^ 128 ∧ r.1.val.val V = n) ∧
        SqueezedReads V r.2
          (Poseidon.squeeze p (Poseidon.absorb p ps₀ ((pend.filter (·.1)).map (·.2)))).2)⌝⦄ := by
  simp only [optSqueezePrechallenge]
  have hsq := optSqueeze_spec (V := V) p hsize hall ov
  have hlo := fun x => lowest128Bits'_spec (V := V) h2 h3 constrainLowBits endo x
  mvcgen [hsq, hlo]
  rename_i _ x _ hx chal _ hchal
  obtain ⟨hiv, he, ⟨n, hn, rfl⟩, hlow⟩ := hchal
  refine ⟨fun ps hs => ?_, fun ib ps₀ pend h hne hchar => ?_⟩
  · obtain ⟨hxv, hst⟩ := hx.1 ps hs
    exact ⟨⟨n, hn, by rw [← hxv, he]⟩, hlow, hst⟩
  · obtain ⟨hxv, hst⟩ := hx.2 ib ps₀ pend h hne hchar
    exact ⟨⟨n, hn, by rw [← hxv, he]⟩, hlow, hst⟩

/-- Under any valuation satisfying the emitted constraints, with the mask bits and `sg_old`
reading as `sgv`, `x_hat` as `xv` and the commitments as `wv, zv, tv` (`z_comm` and `t_comm`
non-empty), at a characteristic above the absorb count, the outputs satisfy
`FqTranscriptReads` at the kept `sg_old` readings. -/
theorem fqSpongeTranscriptOpt_spec [ToNat F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (p : Poseidon.Params F) (hsize : p.roundConstants.size = Poseidon.fullRounds)
    (hall : ∀ j k : ℕ, j ≤ 3 → k ≤ 3 → (j : F) = k → j = k)
    (endo indexDigest : FVar F) (sgOld : List (BoolVar F × AffinePoint (FVar F)))
    (sgv : List (Bool × AffinePoint F)) (hsg : List.Forall₂ (CircuitType.Reads V) sgOld sgv)
    (xHat : List (AffinePoint (FVar F))) (xv : List (AffinePoint F))
    (hx : List.Forall₂ (CircuitType.Reads V) xHat xv)
    (wComm : List (List (AffinePoint (FVar F)))) (wv : List (List (AffinePoint F)))
    (hw : List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) wComm wv)
    (zComm tComm : List (AffinePoint (FVar F))) (zv tv : List (AffinePoint F))
    (hz : List.Forall₂ (CircuitType.Reads V) zComm zv)
    (ht : List.Forall₂ (CircuitType.Reads V) tComm tv) (hzne : zv ≠ []) (htne : tv ≠ [])
    (hchar : ∀ k : ℕ,
      k ≤ 1 + 2 * (sgv.length + xv.length + wv.flatten.length + zv.length + tv.length) →
      (k : F) = 0 → k = 0) :
    ⦃⌜True⌝⦄ fqSpongeTranscriptOpt (c := Builder V (KimchiConstraint F)) p endo indexDigest sgOld
      xHat wComm zComm tComm
    ⦃⇓ o _ => ⌜FqTranscriptReads p (indexDigest.val V) ((sgv.filter (·.1)).map (·.2)) xv wv zv tv
      V o⌝⦄ := by
  obtain ⟨zP, zs, rfl⟩ : ∃ P Ps, zComm = P :: Ps := by
    cases hz with
    | nil => exact absurd rfl hzne
    | cons _ _ => exact ⟨_, _, rfl⟩
  obtain ⟨tP, ts, rfl⟩ : ∃ P Ps, tComm = P :: Ps := by
    cases ht with
    | nil => exact absurd rfl htne
    | cons _ _ => exact ⟨_, _, rfl⟩
  obtain ⟨zPv, zvs, rfl, hzP, hzs⟩ : ∃ v vs, zv = v :: vs ∧ CircuitType.Reads V zP v ∧
      List.Forall₂ (CircuitType.Reads V) zs vs := by
    cases hz with | cons h hs => exact ⟨_, _, rfl, h, hs⟩
  obtain ⟨tPv, tvs, rfl, htP, hts⟩ : ∃ v vs, tv = v :: vs ∧ CircuitType.Reads V tP v ∧
      List.Forall₂ (CircuitType.Reads V) ts vs := by
    cases ht with | cons h hs => exact ⟨_, _, rfl, h, hs⟩
  simp only [fqSpongeTranscriptOpt, List.foldl_cons]
  -- the readings of the absorbed sponges, before the run
  have r0 := optAbsorb_reads_absorbing (create_reads (V := V) p) (e := (true_, indexDigest))
    (v := (true, indexDigest.val V)) (CircuitType.reads_prod.mpr ⟨reads_true, rfl⟩)
  have r3 := foldl_optAbsorbColumns_reads hw
    (foldl_optAbsorbPoint_reads hx (foldl_optAbsorbMasked_reads hsg r0))
  have hpre := fun b ov => optSqueezePrechallenge_spec (V := V) h2 h3 p hsize hall b endo ov
  have hsq := fun sv => SpongeVar.squeeze_spec (V := V) p hsize sv
  mvcgen [hpre, hsq]
  rename_i _ pβ _ pγ _ pα _ hα pζ _ hζ pd _ hdig hβ hγ
  -- β: the block of everything absorbed so far
  have hlen0 : ([] ++ [(true, indexDigest.val V)] ++ maskedFlat sgv ++ pointsFlat xv
      ++ wv.flatMap pointsFlat).length
      ≤ 1 + 2 * (sgv.length + xv.length + wv.flatten.length + (zPv :: zvs).length
        + (tPv :: tvs).length) := by
    simp only [List.length_append, List.length_nil, List.length_cons, length_maskedFlat,
      length_pointsFlat, length_flatMap_pointsFlat]
    omega
  obtain ⟨⟨nβ, hnβ, eβ⟩, hbetaLo, s5⟩ := hβ.2 _ _ _ r3
    (Or.inl ⟨(true, indexDigest.val V), by simp, rfl⟩) (fun k hk => hchar k (le_trans hk hlen0))
  obtain ⟨⟨nγ, hnγ, eγ⟩, hgammaLo, s6⟩ := hγ.1 _ s5
  -- α: `z_comm` from the squeezed sponge
  have rz := foldl_optAbsorbPoint_reads hzs (optAbsorbPoint_reads_squeezed p s6 hzP)
  have hlenz : ([(true, zPv.x), (true, zPv.y)] ++ pointsFlat zvs).length
      ≤ 1 + 2 * (sgv.length + xv.length + wv.flatten.length + (zPv :: zvs).length
        + (tPv :: tvs).length) := by
    simp only [List.length_append, List.length_cons, List.length_nil, length_pointsFlat]
    omega
  obtain ⟨⟨nα, hnα, eα⟩, -, s8⟩ := hα.2 _ _ _ rz (Or.inl ⟨(true, zPv.x), by simp, rfl⟩)
    (fun k hk => hchar k (le_trans hk hlenz))
  -- ζ: `t_comm` from the squeezed sponge
  have rt := foldl_optAbsorbPoint_reads hts (optAbsorbPoint_reads_squeezed p s8 htP)
  have hlent : ([(true, tPv.x), (true, tPv.y)] ++ pointsFlat tvs).length
      ≤ 1 + 2 * (sgv.length + xv.length + wv.flatten.length + (zPv :: zvs).length
        + (tPv :: tvs).length) := by
    simp only [List.length_append, List.length_cons, List.length_nil, length_pointsFlat]
    omega
  obtain ⟨⟨nζ, hnζ, eζ⟩, -, s10⟩ := hζ.2 _ _ _ rt (Or.inl ⟨(true, tPv.x), by simp, rfl⟩)
    (fun k hk => hchar k (le_trans hk hlent))
  have s11 := toRegularSponge_reads s10
  obtain ⟨hdv, -⟩ := hdig _ s11
  -- the kept inputs are the wire verifier's absorb lists
  have hkept : ((([] ++ [(true, indexDigest.val V)] ++ maskedFlat sgv ++ pointsFlat xv
      ++ wv.flatMap pointsFlat).filter (fun v : Bool × F => v.1)).map (fun v : Bool × F => v.2))
      = [indexDigest.val V] ++ flatCoords ((sgv.filter (·.1)).map (·.2)) ++ flatCoords xv
        ++ wv.flatMap flatCoords := by
    simp only [List.nil_append, List.filter_append, List.map_append, kept_maskedFlat,
      kept_pointsFlat, kept_flatMap_pointsFlat]
    rfl
  have hkz : ((([(true, zPv.x), (true, zPv.y)] ++ pointsFlat zvs).filter
      (fun v : Bool × F => v.1)).map (fun v : Bool × F => v.2))
      = flatCoords (zPv :: zvs) := by
    simp only [List.filter_append, List.map_append, kept_pointsFlat, flatCoords,
      List.flatMap_cons]
    rfl
  have hkt : ((([(true, tPv.x), (true, tPv.y)] ++ pointsFlat tvs).filter
      (fun v : Bool × F => v.1)).map (fun v : Bool × F => v.2))
      = flatCoords (tPv :: tvs) := by
    simp only [List.filter_append, List.map_append, kept_pointsFlat, flatCoords,
      List.flatMap_cons]
    rfl
  simp only [hkept, hkz, hkt] at eβ eγ eα eζ hdv s11
  unfold FqTranscriptReads fqSqueezes
  simp only [foldl_pts_eq, foldl_cols_eq, ← absorb_append]
  refine ⟨nβ, nγ, nα, nζ, hnβ, hnγ, hnα, hnζ, ?_, ?_, ?_, ?_, hbetaLo, hgammaLo, hx,
    ?_, ?_⟩
  · exact eβ
  · exact eγ
  · exact eα
  · exact eζ
  · exact hdv
  · exact s11

/-! ## The wire reading -/

open Kimchi.Verifier in
/-- `FqTranscriptReads` at a deployed field, against the wire verifier: with `pre` the
verifier's `fqPrechallenges`, `β` and `γ` are its first two up to `PrechallengeAlias`, and
`α`, `ζ` its last two once identified with 128-bit claims `a₀`, `z₀`; the digest reads as the
digest element and the sponge as the pre-digest state (`fqOracles_eq_fqPrechallenges`
carries these to `fqOracles`). -/
def FqTranscriptReadsWire {p : ℕ} [Fact p.Prime] (params : Poseidon.Params (ZMod p))
    (indexDigest : ZMod p) (sgOld xv : List (AffinePoint (ZMod p)))
    (wComm : List (List (AffinePoint (ZMod p)))) (zComm tComm : List (AffinePoint (ZMod p)))
    (V : Valuation (ZMod p)) (o : FqTranscriptOutput (ZMod p)) : Prop :=
  let pre := fqPrechallenges params indexDigest (sgOld.map coords) (xv.map coords)
    (wComm.map (·.map coords)) (zComm.map coords) (tComm.map coords)
  (∃ b₀ : ℕ, o.beta.val.val V = b₀ ∧ PrechallengeAlias p pre.1.1 b₀) ∧
  (∃ g₀ : ℕ, o.gamma.val.val V = g₀ ∧ PrechallengeAlias p pre.1.2.1 g₀) ∧
  (∀ a₀ : ℕ, a₀ < 2 ^ 128 → o.alpha.val.val V = a₀ → PrechallengeAlias p pre.1.2.2.1 a₀) ∧
  (∀ z₀ : ℕ, z₀ < 2 ^ 128 → o.zeta.val.val V = z₀ → PrechallengeAlias p pre.1.2.2.2 z₀) ∧
  List.Forall₂ (CircuitType.Reads V) o.xHat xv ∧
  o.digest.val V = pre.2.1 ∧ SpongeVar.ReadsAt V o.sponge pre.2.2

open Kimchi.Verifier in
/-- At a prime field of more than 254 bits, the exact reading is the wire reading
(`low128_of_decomp`). -/
theorem FqTranscriptReads.wire {p : ℕ} [Fact p.Prime] (hp : 2 ^ 254 < p)
    {params : Poseidon.Params (ZMod p)} {indexDigest : ZMod p}
    {sgOld xv : List (AffinePoint (ZMod p))} {wComm : List (List (AffinePoint (ZMod p)))}
    {zComm tComm : List (AffinePoint (ZMod p))}
    {V : Valuation (ZMod p)} {o : FqTranscriptOutput (ZMod p)}
    (h : FqTranscriptReads params indexDigest sgOld xv wComm zComm tComm V o) :
    FqTranscriptReadsWire params indexDigest sgOld xv wComm zComm tComm V o := by
  obtain ⟨hβ, hγ, hα, hζ, hhβ, hhγ, hhα, hhζ, eβ, eγ, eα, eζ, ⟨b₀, hb₀, hbv⟩, ⟨g₀, hg₀, hgv⟩,
    hxh, hd, hs⟩ := h
  refine ⟨⟨b₀, hbv, ?_⟩, ⟨g₀, hgv, ?_⟩, ?_, ?_, hxh, hd, hs⟩
  · exact low128_of_decomp hp _ b₀ hβ hb₀ hhβ (by rw [eβ, hbv])
  · exact low128_of_decomp hp _ g₀ hγ hg₀ hhγ (by rw [eγ, hgv])
  · intro a₀ ha₀ hav
    exact low128_of_decomp hp _ a₀ hα ha₀ hhα (by rw [eα, hav])
  · intro z₀ hz₀ hzv
    exact low128_of_decomp hp _ z₀ hζ hz₀ hhζ (by rw [eζ, hzv])

end Pickles
