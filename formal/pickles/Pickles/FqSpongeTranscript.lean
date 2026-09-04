import Snarky.Kimchi.Circuit.Sponge
import Snarky.Kimchi.Circuit.RangeCheck
import Snarky.Kimchi.Circuit.AddComplete
import Kimchi.Verifier.Kimchi

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
