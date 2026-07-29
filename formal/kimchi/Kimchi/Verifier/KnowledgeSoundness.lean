import Kimchi.Columns
import Kimchi.Verifier.Capstone.Reflection
import Kimchi.Verifier.Forking.OracleRun
import Bulletproof.Forking.KnowledgeSoundness

/-!
# Kimchi verifier knowledge soundness — the STATEMENT

This module states and proves the kimchi-level analogue of
`Bulletproof.Ipa.Forking.ipa{Vesta,Pallas}_knowledge_sound`: over a uniformly sampled setup
basis and a uniform challenge table, the executable kimchi verifier accepts while the
extractor fails to hand back a satisfying witness table only with small probability.

What the theorem bought was the retirement of the former `kimchi_fiat_shamir_{vesta,pallas}`
axioms, which asserted an accepted IPA opening of the run's combined commitment outright; here
that opening is *extracted*, by the forking argument the IPA capstone already runs, and the
cost of extraction failure is charged to discrete log.

**The modeled fragment** (what "the deployed kimchi verifier" quantifies over; external-audit
C-1/C-2, full field-by-field delineation in `docs/external-audit-report.md` Appendix W):
single, unbatched kimchi proofs over the Pasta curves, for circuits in the transcribed basic
gate set — zero, generic, poseidon, completeAdd, varBaseMul, endoMul, endoScalar — with
kimchi's public-input gadget layout, at a power-of-two domain with `nc · 2^k = n` (`hkn`).
The SUB-SRS regime `max_poly_size > n` — the common o1js/Mina configuration — is OUTSIDE the
fragment, as are lookups, optional gates (range check, foreign field, xor, rot), and
recursion (`prev_challenges = 0`). On the proof side the fragment also excludes proofs
carrying optional-gate or lookup EVALUATION fields (production fr-absorbs those even against
a basic-gate key, so such a proof's transcript differs), proofs with an empty quotient
commitment (`htpos`; the wire parse now rejects them as a declared strengthening), ragged
chunk vectors, and openings of other than `σ.k` rounds. Mina/pickles proofs use recursion,
lookups, optional gates and the sub-SRS regime, and are outside the fragment on four
independent axes.

The formulation is deliberately **analogous to the IPA one**, clause for clause:

| IPA (`Bulletproof/Forking/KnowledgeSoundness.lean`) | here |
| --- | --- |
| `DeployedFamily` | `KimchiFamily` |
| `wireWins` — `Ipa.verifyWith` at the reads | `KimchiFamily.Wins` — `kimchiVerifyWith` at them |
| `DeployedFamily.attempt` | `KimchiFamily.attempt` |
| `HasOpening` — the extractor returned `PSum.inl` | `ExtractsWitness` — that, and it satisfies |
| query loss + `(2^k+1)·ε` + `δ` | that, plus the Schwartz–Zippel budget |

## Why the extractor is data-valued

`attempt` returns data — a coefficient table or a discrete-log relation — and never a `Prop`.
Its semantic content is stated *outside* it, by `ExtractsWitness`, which is what the measure
quantifies. This is what keeps an unfinished proof honest: with the payload pure data, an open
proof can only enlarge the failure set, i.e. make the bound harder. Were the satisfaction proof
carried *inside* the returned type, leaving it open would instead make the endpoint trivially
true.

## Why `hbind` does not appear

`kimchiProof_sound_of_openings_of_vkrep` (`Verifier/Reduction/Soundness.lean`) carries
`hbind : ∀ w wh, DLRelation σ w wh → w = 0 ∧ wh = 0` — binding, which
`Bulletproof/Soundness.lean` concedes is information-theoretically false at deployed
parameters. Here it is not merely undesirable but unavailable: the measure samples the basis
as `augOfSetup (scalarBasis B s)`, where every generator is a multiple of `B`, so nontrivial
discrete-log relations exist and `∀ basis, hbind` is refutable. An endpoint carrying it would
be vacuous. Binding failures are charged instead, through `ε` and `δ`, exactly as on the IPA
side: the extractor *returns* the relation it finds.

## Why there is no grid

The un-batching from the combined commitment to per-row openings is `eval_pins_of_opening`
(`Verifier/Capstone/Algebraic.lean`), which needs the family's per-commitment representations
and **one** accepted opening, against two counted exclusion sets. `chunked_batch_soundness`,
which needs acceptance across a grid of distinct polyscales, is not on this path.

## Why the existing machinery carries over

Every kimchi challenge is a 128-bit prechallenge: `β`, `γ` via `challenge` (cast into the
field), `α`, `ζ` via `squeezeChallenge` (endo-expanded), and the fr-side `ξ`, `r` likewise
(`Verifier/Kimchi.lean`). So the oracle alphabet is `Prechallenge = Fin (2 ^ 128)` — the one
`Bulletproof.Forking.Game` is built over — and that layer is generic in the expansion map,
taking `Nat.cast` and `endoExpand` alike. The IPA extraction, the escape/counting machinery
and the discrete-log charging are reused unchanged; what is new here is modelling.
-/

namespace Kimchi.Verifier.KnowledgeSoundness

open Bulletproof Bulletproof.Forking Bulletproof.Ipa.Forking Kimchi.Protocol Kimchi.Index
open scoped ENNReal

variable {C : Ipa.CommitmentCurve}

/-! ## 1. The challenge-generic verifier

`kimchiVerify` derives every challenge internally, so it cannot serve as the win event of a
game whose challenges come from an oracle table. This is the kimchi analogue of the IPA's
`verifyWith` / `verifyFrom` split: the algebra, with the challenges handed in. -/

/-- **The kimchi verifier at given challenges.** `beta`, `gamma`, `alpha`, `zeta` are the
fq-side squeezes; `v`/`u` the fr-side polyscale/evalscale; `uBase`, `chals`, `c` the IPA
opening challenges. The body is `kimchiVerify`'s with every squeeze replaced by a parameter. -/
def kimchiVerifyWith {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField)
    (uBase : C.Point) (chals : Vector C.ScalarField σ.k) (c : C.ScalarField) : Bool :=
  let n := cvk.n
  if cvk.lagrangeBasis.size < pub.size || n < pub.size then
    false
  else
    let publicComm := publicCommitment C σ cvk pub
    let zetaOmega := zeta * cvk.omega
    let zetaN := powPow2 zeta cvk.domainLog2
    let zetaOmegaN := powPow2 zetaOmega cvk.domainLog2
    let zetaM := powPow2 zeta σ.k
    let zetaOmegaM := powPow2 zetaOmega σ.k
    let pubEvals := publicEvalChunks cp n cvk.omega zeta zetaOmega zetaN zetaOmegaN pub
    let pubEval0 := combineAt zetaM pubEvals.zeta.toArray
    let e := cp.linEvals zetaM zetaOmegaM
    let shifts : Fin permCols → C.ScalarField := fun i => cvk.shifts[i]
    let ftEval0 := Kimchi.Protocol.Linearization.ftEval0 n cvk.zkRows cvk.omega shifts
      cvk.endo (mdsOfParams C.frParams) alpha beta gamma zeta pubEval0 e
    let zkpmZ := Kimchi.Protocol.Linearization.zkpmEval n cvk.zkRows cvk.omega zeta
    let pScalar := Kimchi.Protocol.Linearization.permScalar beta gamma alpha zkpmZ e
    let fComm := cvk.sigmaComm[6].map (fun P => pScalar.val • P)
    let ftComm := Ipa.combineCommitments C zetaM fComm.toArray
      - (zetaN - 1).val • Ipa.combineCommitments C zetaM cp.tComm
    let stream : Vector (C.Point × C.ScalarField × C.ScalarField) (nc + 1 + tailRowCount * nc) :=
      (Vector.ofFn fun cc : Fin nc =>
          (publicComm[cc], pubEvals.zeta[cc], pubEvals.zetaOmega[cc]))
        ++ (⟨#[(ftComm, ftEval0, cp.ftEval1)], rfl⟩
            : Vector (C.Point × C.ScalarField × C.ScalarField) 1)
        ++ (tailRowsOf C cvk cp).flatten
    let inp : Ipa.Input C σ.k (nc + 1 + tailRowCount * nc) evalPts :=
      { commitments := stream.map (·.1)
        xs := ⟨#[zeta, zetaOmega], rfl⟩
        evals := stream.map (fun r => (⟨#[r.2.1, r.2.2], rfl⟩ : Vector _ evalPts))
        polyscale := v
        evalscale := u
        proof := cp.opening }
    Ipa.verifyWith C σ uBase chals c inp

/-- **The run's batched IPA claim at given challenges** — the `inp` inside `kimchiVerifyWith`,
named, so that the extractor can be run at the *same* claim the win event checks. -/
def runInputWith {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField) :
    Ipa.Input C σ.k (nc + 1 + tailRowCount * nc) evalPts :=
  let n := cvk.n
  let publicComm := publicCommitment C σ cvk pub
  let zetaOmega := zeta * cvk.omega
  let zetaN := powPow2 zeta cvk.domainLog2
  let zetaOmegaN := powPow2 zetaOmega cvk.domainLog2
  let zetaM := powPow2 zeta σ.k
  let zetaOmegaM := powPow2 zetaOmega σ.k
  let pubEvals := publicEvalChunks cp n cvk.omega zeta zetaOmega zetaN zetaOmegaN pub
  let pubEval0 := combineAt zetaM pubEvals.zeta.toArray
  let e := cp.linEvals zetaM zetaOmegaM
  let shifts : Fin permCols → C.ScalarField := fun i => cvk.shifts[i]
  let ftEval0 := Kimchi.Protocol.Linearization.ftEval0 n cvk.zkRows cvk.omega shifts
    cvk.endo (mdsOfParams C.frParams) alpha beta gamma zeta pubEval0 e
  let zkpmZ := Kimchi.Protocol.Linearization.zkpmEval n cvk.zkRows cvk.omega zeta
  let pScalar := Kimchi.Protocol.Linearization.permScalar beta gamma alpha zkpmZ e
  let fComm := cvk.sigmaComm[6].map (fun P => pScalar.val • P)
  let ftComm := Ipa.combineCommitments C zetaM fComm.toArray
    - (zetaN - 1).val • Ipa.combineCommitments C zetaM cp.tComm
  let stream : Vector (C.Point × C.ScalarField × C.ScalarField) (nc + 1 + tailRowCount * nc) :=
    (Vector.ofFn fun cc : Fin nc =>
        (publicComm[cc], pubEvals.zeta[cc], pubEvals.zetaOmega[cc]))
      ++ (⟨#[(ftComm, ftEval0, cp.ftEval1)], rfl⟩
          : Vector (C.Point × C.ScalarField × C.ScalarField) 1)
      ++ (tailRowsOf C cvk cp).flatten
  { commitments := stream.map (·.1)
    xs := ⟨#[zeta, zetaOmega], rfl⟩
    evals := stream.map (fun r => (⟨#[r.2.1, r.2.2], rfl⟩ : Vector _ evalPts))
    polyscale := v
    evalscale := u
    proof := cp.opening }

/-- The challenge-generic verifier *is* the size guard plus `Ipa.verifyWith` at that claim.
Definitional — the split only names the boundary. -/
theorem kimchiVerifyWith_eq_verifyWith {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField) (uBase : C.Point)
    (chals : Vector C.ScalarField σ.k) (c : C.ScalarField) :
    kimchiVerifyWith σ cvk cp pub beta gamma alpha zeta v u uBase chals c
      = (if cvk.lagrangeBasis.size < pub.size || cvk.n < pub.size then false
          else Ipa.verifyWith C σ uBase chals c
            (runInputWith σ cvk cp pub beta gamma alpha zeta v u)) := rfl

/-! ### 1b. Fiat–Shamir faithfulness

The generic verifier above is only worth stating if the deployed one *is* it, at challenges
that are transcript reads. A statement of the shape `∃ β γ α ζ v u U c⃗ c, kimchiVerify =
kimchiVerifyWith …` carries no content — it is satisfied by any construction agreeing at one
point, and says nothing about where the challenges came from. What follows names them.

The kimchi schedule threads two sponges and then continues the first one *warm*:

* the **fq sponge** absorbs the key digest, the public-input commitment chunks and the
  witness chunks, squeezes `β`, `γ` (128-bit casts), absorbs `z_comm` and squeezes `α`,
  absorbs `t_comm` and squeezes `ζ` (both endo-expanded). Its state at that moment is the
  **warm state** `s⋆` (`warmState`), and `fqDigest` of `s⋆` is what the second sponge eats;
* the **fr sponge** absorbs that digest, `ft(ζω)`, the public evaluation chunk vectors and
  every column's `ζ`/`ζω` chunk vectors, and squeezes `v` then `u`;
* the **opening** runs on the fq sponge continued from `s⋆`, which is exactly
  `Bulletproof.Ipa.Forking.spongeFSFrom C s⋆` (`kimchiOpeningFS`).

The six pre-opening reads are `Kimchi.Verifier.Forking.poseidonO` / `poseidonOFr` at the six
transcribed prefixes; the three opening reads are `kimchiOpeningFS`'s two squeezes at
`preT` / `preU i` / `preC` of the claim assembled from those six. -/

/-- **The warm state, as a read of the transcript.** The fq interpreter folds a prefix through
the deployed sponge carrying a `(state, last challenge)` pair; `Forking.poseidonO` projects the
*value* at each prefix. This is the *state* component at the `ζ` prefix — the sponge the
deployed verifier hands the opening check, obtained as a transcript read rather than as a
projection of the deployed schedule (`warmState_eq` is the bridge). -/
private def warmState {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) : Poseidon.FqSponge.S C.base :=
  ((Forking.KimchiTranscriptElt.preZeta cvk cp publicComm).foldl
    Forking.step (Poseidon.FqSponge.init, 0)).1

/-- The warm state read off the transcript is the deployed post-`ζ` sponge state. Same fold and
same argument as the four value-side bridges (`Forking.poseidonO_pre*`); only the projection
differs — `foldl_step_fst` says the state component ignores the running challenge. -/
private theorem warmState_eq {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    warmState cvk cp publicComm = (fqOracles C cvk cp publicComm).warm := by
  rw [warmState, Forking.KimchiTranscriptElt.preZeta, Forking.KimchiTranscriptElt.preAlpha,
    Forking.KimchiTranscriptElt.preGamma, Forking.KimchiTranscriptElt.preBeta]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, Forking.step,
    Forking.foldl_step_fst, Forking.foldl_absorbInto_preAbsorbs]
  simp only [Forking.KimchiTranscriptElt.absorbInto, List.foldl_map, Vector.foldl_toList,
    Array.foldl_toList, fqOracles]

/-- **The fq digest, as a read of the transcript.** `fq_sponge.clone().digest()` — the value
handed to the fr sponge — computed from `warmState` rather than from `fqOracles`, so that the
fr-side prefixes are functions of the transcript alone. -/
def warmDigest {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) : C.ScalarField :=
  let x := (Poseidon.FqSponge.challengeFq C.sponge (warmState cvk cp publicComm)).1
  if x.val < C.scalar then ((x.val : ℕ) : C.ScalarField) else 0

/-- The transcript-read digest is the deployed one. Immediate from `warmState_eq`. -/
private theorem warmDigest_eq {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) :
    warmDigest cvk cp publicComm = (fqOracles C cvk cp publicComm).digest := by
  rw [warmDigest, warmState_eq]
  rfl

/-- **The warm opening oracles.** The deployed Poseidon Fiat–Shamir source started at the warm
state: its `squeezeBase` at `preT` gives the `U` base, its `squeezeScalar` at `preU i` and
`preC` the round and Schnorr challenges. -/
def kimchiOpeningFS {nc k : ℕ} (cvk : KimchiVK C nc) (cp : KimchiProof C nc k)
    (publicComm : Vector C.Point nc) : Ipa.Forking.FiatShamir C :=
  Ipa.Forking.spongeFSFrom C (warmState cvk cp publicComm)

/-- The deployed verifier *is* the size guard plus `Ipa.verifyFrom` at the warm state, on the
claim `runInputWith` assembles from the deployed challenges. Definitional, the mirror of
`kimchiVerifyWith_eq_verifyWith`; it is the shape the faithfulness proof compares. -/
private theorem kimchiVerify_eq_verifyFrom {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    kimchiVerify C σ cvk cp pub
      = (if cvk.lagrangeBasis.size < pub.size || cvk.n < pub.size then false
        else
          let publicComm := publicCommitment C σ cvk pub
          let o := fqOracles C cvk cp publicComm
          let pubEvals := publicEvalChunks cp cvk.n cvk.omega o.zeta (o.zeta * cvk.omega)
            (powPow2 o.zeta cvk.domainLog2) (powPow2 (o.zeta * cvk.omega) cvk.domainLog2) pub
          let vu := frOracles C cp o.digest pubEvals
          Ipa.verifyFrom C σ o.warm
            (runInputWith σ cvk cp pub o.beta o.gamma o.alpha o.zeta vu.1 vu.2)) := rfl

/-- **FAITHFULNESS OBLIGATION, at named reads.** The deployed verifier is `kimchiVerifyWith` at
challenges *pinned to transcript reads by hypothesis*: `β`, `γ`, `α`, `ζ` are `poseidonO` at
the four fq prefixes, `v`, `u` are `poseidonOFr` at the two fr prefixes (taken at the warm
digest and at the public evaluations the read `ζ` determines), and `U`, `c⃗`, `c` are the warm
opening oracles' reads at the three opening prefixes of the claim built from those six.

Each hypothesis defines its variable in terms of earlier ones, so the system is a chain of
definitions, not a constraint: `kimchiVerify_eq_verifyWith` below is this theorem at its own
solution. The IPA analogue is `Bulletproof.Ipa.Forking.verifyOracle_spongeFSFrom`, which is
what discharges the opening suffix here. -/
theorem kimchiVerify_eq_verifyWith_of_reads {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (publicComm : Vector C.Point nc) (beta gamma alpha zeta v u : C.ScalarField)
    (pubEvals : PointEvaluations (Vector C.ScalarField nc))
    (inp : Ipa.Input C σ.k (nc + 1 + tailRowCount * nc) evalPts)
    (uBase : C.Point) (chals : Vector C.ScalarField σ.k) (c : C.ScalarField)
    (hpc : publicComm = publicCommitment C σ cvk pub)
    (hbeta : beta = Forking.poseidonO
      (Forking.KimchiTranscriptElt.preBeta cvk cp publicComm))
    (hgamma : gamma = Forking.poseidonO
      (Forking.KimchiTranscriptElt.preGamma cvk cp publicComm))
    (halpha : alpha = Forking.poseidonO
      (Forking.KimchiTranscriptElt.preAlpha cvk cp publicComm))
    (hzeta : zeta = Forking.poseidonO
      (Forking.KimchiTranscriptElt.preZeta cvk cp publicComm))
    (hpe : pubEvals = publicEvalChunks cp cvk.n cvk.omega zeta (zeta * cvk.omega)
      (powPow2 zeta cvk.domainLog2) (powPow2 (zeta * cvk.omega) cvk.domainLog2) pub)
    (hv : v = Forking.poseidonOFr
      (Forking.FrTranscriptElt.preV cp (warmDigest cvk cp publicComm) pubEvals))
    (hu : u = Forking.poseidonOFr
      (Forking.FrTranscriptElt.preU cp (warmDigest cvk cp publicComm) pubEvals))
    (hinp : inp = runInputWith σ cvk cp pub beta gamma alpha zeta v u)
    (huBase : uBase = C.toGroup ((kimchiOpeningFS cvk cp publicComm).squeezeBase
      (Ipa.Forking.IpaTranscriptElt.preT inp)))
    (hchals : chals = Vector.ofFn fun i => (kimchiOpeningFS cvk cp publicComm).squeezeScalar
      (Ipa.Forking.IpaTranscriptElt.preU inp i))
    (hc : c = (kimchiOpeningFS cvk cp publicComm).squeezeScalar
      (Ipa.Forking.IpaTranscriptElt.preC inp)) :
    kimchiVerify C σ cvk cp pub
      = kimchiVerifyWith σ cvk cp pub beta gamma alpha zeta v u uBase chals c := by
  subst hpc hbeta hgamma halpha hzeta hpe hv hu hinp huBase hchals hc
  -- (a) the six pre-opening reads become the six deployed squeezes, in schedule order: the
  -- fr prefixes are read at the digest and the evaluations the fq rewrites have just fixed.
  rw [Forking.poseidonO_preBeta, Forking.poseidonO_preGamma, Forking.poseidonO_preAlpha,
    Forking.poseidonO_preZeta, warmDigest_eq, Forking.poseidonOFr_preV,
    Forking.poseidonOFr_preU]
  -- Both sides now assemble the same `runInputWith` claim behind the same guard.
  -- (b) the start state is the deployed warm state.
  rw [kimchiVerify_eq_verifyFrom, kimchiVerifyWith_eq_verifyWith, kimchiOpeningFS,
    warmState_eq]
  congr 1
  -- (c) the warm-start opening bridge, read right-to-left.
  exact (Ipa.Forking.verifyOracle_spongeFSFrom σ _ _).symm

/-- **The public evaluation chunks at the read `ζ`** — the fr sponge absorbs these, so the two
fr-side prefixes are functions of the fq reads through this. -/
def kimchiPubEvals {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    PointEvaluations (Vector C.ScalarField nc) :=
  let zeta := Forking.poseidonO (Forking.KimchiTranscriptElt.preZeta cvk cp
    (publicCommitment C σ cvk pub))
  publicEvalChunks cp cvk.n cvk.omega zeta (zeta * cvk.omega)
    (powPow2 zeta cvk.domainLog2) (powPow2 (zeta * cvk.omega) cvk.domainLog2) pub

/-- **The run's batched IPA claim at the six pre-opening reads** — `runInputWith` fed the four
`poseidonO` reads and the two `poseidonOFr` reads. The three opening prefixes are taken at this
claim, so it is named. -/
private def kimchiRunInput {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    Ipa.Input C σ.k (nc + 1 + tailRowCount * nc) evalPts :=
  let pc := publicCommitment C σ cvk pub
  runInputWith σ cvk cp pub
    (Forking.poseidonO (Forking.KimchiTranscriptElt.preBeta cvk cp pc))
    (Forking.poseidonO (Forking.KimchiTranscriptElt.preGamma cvk cp pc))
    (Forking.poseidonO (Forking.KimchiTranscriptElt.preAlpha cvk cp pc))
    (Forking.poseidonO (Forking.KimchiTranscriptElt.preZeta cvk cp pc))
    (Forking.poseidonOFr (Forking.FrTranscriptElt.preV cp (warmDigest cvk cp pc)
      (kimchiPubEvals σ cvk cp pub)))
    (Forking.poseidonOFr (Forking.FrTranscriptElt.preU cp (warmDigest cvk cp pc)
      (kimchiPubEvals σ cvk cp pub)))

/-- **FAITHFULNESS OBLIGATION.** The deployed verifier is the challenge-generic verifier at the
nine challenges the deployed schedule draws, each written out as an oracle read: `β`, `γ`, `α`,
`ζ` are the sponge-as-oracle `Forking.poseidonO` at the four fq transcript prefixes; `v`, `u`
are `Forking.poseidonOFr` at the two fr prefixes, read at the warm digest and the public
evaluation chunks; `U`, `c⃗` and `c` are the *warm* opening oracles (`kimchiOpeningFS`, the
deployed sponge continued from the post-`ζ` state) at `preT`, `preU i` and `preC` of the claim
`kimchiRunInput` those six assemble.

Without this the knowledge-soundness endpoints below would be about an unrelated construction;
with it they are about the shipped verifier under a random-oracle idealization of the sponge.
The IPA analogue is `Bulletproof.Ipa.Forking.verifyOracle_spongeFS`.

The base slot needs no caveat (an earlier revision carried one here): the game the endpoints
measure evaluates the generic verifier at the same *warm* base this theorem pins —
`KimchiFamily.Wins` feeds `fam.warmBase`, and `Forking/Bridge.lean` records that the two
slots are the same term, closed by `rfl`. The cold-base game, and the ninth `FSFaithful`
field it required, are gone. -/
theorem kimchiVerify_eq_verifyWith {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    kimchiVerify C σ cvk cp pub
      = kimchiVerifyWith σ cvk cp pub
          (Forking.poseidonO (Forking.KimchiTranscriptElt.preBeta cvk cp
            (publicCommitment C σ cvk pub)))
          (Forking.poseidonO (Forking.KimchiTranscriptElt.preGamma cvk cp
            (publicCommitment C σ cvk pub)))
          (Forking.poseidonO (Forking.KimchiTranscriptElt.preAlpha cvk cp
            (publicCommitment C σ cvk pub)))
          (Forking.poseidonO (Forking.KimchiTranscriptElt.preZeta cvk cp
            (publicCommitment C σ cvk pub)))
          (Forking.poseidonOFr (Forking.FrTranscriptElt.preV cp
            (warmDigest cvk cp (publicCommitment C σ cvk pub)) (kimchiPubEvals σ cvk cp pub)))
          (Forking.poseidonOFr (Forking.FrTranscriptElt.preU cp
            (warmDigest cvk cp (publicCommitment C σ cvk pub)) (kimchiPubEvals σ cvk cp pub)))
          (C.toGroup ((kimchiOpeningFS cvk cp (publicCommitment C σ cvk pub)).squeezeBase
            (Ipa.Forking.IpaTranscriptElt.preT (kimchiRunInput σ cvk cp pub))))
          (Vector.ofFn fun i =>
            (kimchiOpeningFS cvk cp (publicCommitment C σ cvk pub)).squeezeScalar
              (Ipa.Forking.IpaTranscriptElt.preU (kimchiRunInput σ cvk cp pub) i))
          ((kimchiOpeningFS cvk cp (publicCommitment C σ cvk pub)).squeezeScalar
            (Ipa.Forking.IpaTranscriptElt.preC (kimchiRunInput σ cvk cp pub))) :=
  kimchiVerify_eq_verifyWith_of_reads σ cvk cp pub (publicCommitment C σ cvk pub)
    _ _ _ _ _ _ (kimchiPubEvals σ cvk cp pub) (kimchiRunInput σ cvk cp pub) _ _ _
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-! ## 2. The oracle domain

`β`/`γ` are squeezed back to back with nothing absorbed between them, and so are `ξ`/`r`;
their absorbed data is identical and only the squeeze index separates them. That is why the
slot tag is load-bearing here, exactly as `IpaNode.idx` is on the IPA side — without it
`PrefixDecode`'s distinctness fails.

Commit-then-challenge holds structurally in kimchi's schedule (`wComm` before `β`, `zComm`
before `α`, `tComm` before `ζ`, the evaluations before `ξ`), which is the property whose
absence would make the game FALSE rather than merely unproved. -/

/-- **The squeeze index.** Six pre-IPA squeezes then the IPA rounds and the Schnorr squeeze, in
schedule order. The analogue of `IpaNode.idx`, and load-bearing for the same reason: `β`/`γ`
are squeezed back to back with nothing absorbed between them (likewise `ξ`/`r`), so their
absorbed data is identical and only the index separates them. Without it `PrefixDecode`'s
distinctness fails. -/
inductive Squeeze (k : ℕ)
  /-- `β` — after the witness commitments. -/
  | beta
  /-- `γ` — immediately after `β`, nothing absorbed between. -/
  | gamma
  /-- `α` — after the permutation commitment. -/
  | alpha
  /-- `ζ` — after the quotient commitment. -/
  | zeta
  /-- `ξ` (fr-side `v`) — after the evaluations. -/
  | polyscale
  /-- `r` (fr-side `u`) — immediately after `ξ`. -/
  | evalscale
  /-- IPA round `i`'s challenge. -/
  | ipaRound (i : Fin k)
  /-- The Schnorr squeeze. -/
  | schnorr
  deriving DecidableEq

instance {k : ℕ} : Fintype (Squeeze k) := by
  classical
  exact Fintype.ofEquiv (Unit ⊕ Unit ⊕ Unit ⊕ Unit ⊕ Unit ⊕ Unit ⊕ Fin k ⊕ Unit)
    { toFun := fun x => match x with
        | .inl _ => .beta | .inr (.inl _) => .gamma | .inr (.inr (.inl _)) => .alpha
        | .inr (.inr (.inr (.inl _))) => .zeta
        | .inr (.inr (.inr (.inr (.inl _)))) => .polyscale
        | .inr (.inr (.inr (.inr (.inr (.inl _))))) => .evalscale
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))) => .ipaRound i
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr _)))))) => .schnorr
      invFun := fun t => match t with
        | .beta => .inl () | .gamma => .inr (.inl ()) | .alpha => .inr (.inr (.inl ()))
        | .zeta => .inr (.inr (.inr (.inl ())))
        | .polyscale => .inr (.inr (.inr (.inr (.inl ()))))
        | .evalscale => .inr (.inr (.inr (.inr (.inr (.inl ())))))
        | .ipaRound i => .inr (.inr (.inr (.inr (.inr (.inr (.inl i))))))
        | .schnorr => .inr (.inr (.inr (.inr (.inr (.inr (.inr ()))))))
      left_inv := by rintro (_|_|_|_|_|_|_|_) <;> rfl
      right_inv := by rintro (_|_|_|_|_|_|i|_) <;> rfl }

/-- **One column family's chunked evaluations**, at both evaluation points. Named rather than
written inline so that instance search takes one step per `EvalsView` field: the five-field
product of bare `Fin _ → Fin _ → Fin _ → _` exceeds `synthInstance.maxSize`. -/
private def ColEvals (C : Ipa.CommitmentCurve) (nc : ℕ) : Type :=
  Fin evalPts → Fin nc → C.ScalarField

instance instFintypeColEvals {C : Ipa.CommitmentCurve} {nc : ℕ} : Fintype (ColEvals C nc) :=
  inferInstanceAs (Fintype (Fin evalPts → Fin nc → C.ScalarField))

instance instDecidableEqColEvals {C : Ipa.CommitmentCurve} {nc : ℕ} :
    DecidableEq (ColEvals C nc) :=
  inferInstanceAs (DecidableEq (Fin evalPts → Fin nc → C.ScalarField))

/-- **The claimed evaluations, as a `Fintype`-able view.** The fr-sponge absorbs the public
chunk vectors and then, per column family, the `ζ`-chunk vector and the `ζω`-chunk vector
(`frOracles`, `Verifier/Kimchi.lean`) — all of it before `ξ` is squeezed. The node must record
it, because the claim `(P, b, v)` the opening argument runs against is built from these
evaluations. `ProofEvaluations (Vector _ nc)` is not a `Fintype` (`Vector` is not), so the view
holds the same data as functions off `Fin`, exactly as `PreIpaData.publicComm` does for the
commitments.

The four families and their counts are `tailRowsOf`'s regions:
`litRowCount + wCols + coeffCols + sigmaRows = tailRowCount`. -/
private structure EvalsView (C : Ipa.CommitmentCurve) (nc : ℕ) where
  /-- The public evaluation chunks: `some` when the proof carries them, `none` under the
  barycentric fallback, where they are determined by `ζ` and the public input. -/
  pub : Option (ColEvals C nc)
  /-- The seven single-column rows: `z`, then the six selectors, in absorb order. -/
  lit : Fin litRowCount → ColEvals C nc
  /-- The witness columns. -/
  w : Fin wCols → ColEvals C nc
  /-- The coefficient columns. -/
  coefficients : Fin coeffCols → ColEvals C nc
  /-- The six evaluated σ columns. -/
  s : Fin sigmaRows → ColEvals C nc
  deriving DecidableEq

/-- `EvalsView` as a product, for the `Fintype` transport. -/
private def evalsViewEquiv (C : Ipa.CommitmentCurve) (nc : ℕ) :
    (Option (ColEvals C nc) × (Fin litRowCount → ColEvals C nc) ×
        (Fin wCols → ColEvals C nc) × (Fin coeffCols → ColEvals C nc) ×
        (Fin sigmaRows → ColEvals C nc)) ≃ EvalsView C nc where
  toFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
  invFun t := (t.pub, t.lit, t.w, t.coefficients, t.s)
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeEvalsView {C : Ipa.CommitmentCurve} {nc : ℕ} : Fintype (EvalsView C nc) :=
  Fintype.ofEquiv _ (evalsViewEquiv C nc)

/-- One column family's `(ζ, ζω)` chunk pair, as the view. -/
private def pointView {nc : ℕ} (pe : PointEvaluations (Vector C.ScalarField nc)) : ColEvals C nc :=
  fun pt c => if pt = 0 then pe.zeta[c] else pe.zetaOmega[c]

/-- The proof's evaluations as the node's view of them, in the fr-sponge's absorb order. -/
private def evalsViewOf {nc k : ℕ} (cp : KimchiProof C nc k) : EvalsView C nc where
  pub := match cp.pubEvals with
    | .carried pe => some (pointView pe)
    | .barycentric _ => none
  lit := fun r => pointView
    ((![cp.evals.z, cp.evals.genericSelector, cp.evals.poseidonSelector,
        cp.evals.completeAddSelector, cp.evals.mulSelector, cp.evals.emulSelector,
        cp.evals.endomulScalarSelector] : Fin litRowCount → _) r)
  w := fun i => pointView cp.evals.w[i]
  coefficients := fun i => pointView cp.evals.coefficients[i]
  s := fun i => pointView cp.evals.s[i]

/-- **The pre-IPA absorbed data.** Split out from the node so instance search stays within
budget, and because the split is the real one: this is everything the fq/fr sponges absorb
before the opening argument begins. -/
structure PreIpaData (C : Ipa.CommitmentCurve) (nc : ℕ) where
  /-- The verifying-key digest, absorbed first. -/
  digest : C.ScalarField
  /-- The public commitment, absorbed before `β`. -/
  publicComm : Fin nc → C.Point
  /-- The witness-column commitments, absorbed before `β`. -/
  wComm : Fin wCols → Fin nc → C.Point
  /-- The permutation commitment: absorbed before `α`, so `none` at `β`/`γ`. -/
  zComm : Option (Fin nc → C.Point)
  /-- The quotient chunks: absorbed before `ζ`, so `none` earlier. Indexed by the carried bound
  `tComm.size ≤ 7 * nc` rather than an `Array`, which is not a `Fintype`. -/
  tComm : Option (Fin (7 * nc) → Option C.Point)
  /-- `ft(ζω)`: absorbed fr-side before `ξ`, so `none` earlier. -/
  ftEval1 : Option C.ScalarField
  /-- The claimed evaluations: absorbed fr-side before `ξ`, so `none` earlier. They are what
  makes the node determine the claim the opening argument runs against. -/
  evals : Option (EvalsView C nc)
  deriving DecidableEq

/-- `PreIpaData` as a product, for the `Fintype` transport. -/
private def preIpaDataEquiv (C : Ipa.CommitmentCurve) (nc : ℕ) :
    (C.ScalarField × (Fin nc → C.Point) × (Fin wCols → Fin nc → C.Point) ×
        Option (Fin nc → C.Point) × Option (Fin (7 * nc) → Option C.Point) ×
        Option C.ScalarField × Option (EvalsView C nc)) ≃ PreIpaData C nc where
  toFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2⟩
  invFun t := (t.digest, t.publicComm, t.wComm, t.zComm, t.tComm, t.ftEval1, t.evals)
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypePreIpaData {C : Ipa.CommitmentCurve} {nc : ℕ} :
    Fintype (PreIpaData C nc) :=
  Fintype.ofEquiv _ (preIpaDataEquiv C nc)

/-- **A node of the kimchi transcript** — the data the sponge has absorbed when a challenge is
squeezed, together with the index of that squeeze.

Modelled on `Bulletproof.Ipa.Forking.IpaNode`: one structure whose components are
`Option`-gated by how far the schedule has run, exactly as `IpaNode.lr` is `some` at rounds
`≤ idx` and `none` after. That is what makes commit-then-challenge expressible — each squeeze's
node carries precisely what preceded it. -/
structure KimchiNode (C : Ipa.CommitmentCurve) (nc k : ℕ) where
  /-- Which squeeze this node is read at. -/
  idx : Squeeze k
  /-- Everything absorbed before the opening argument. -/
  pre : PreIpaData C nc
  /-- The IPA cross-terms: `some` at rounds `≤ idx`, `none` afterwards. -/
  lr : Fin k → Option (C.Point × C.Point)
  /-- The Schnorr commitment `δ`, absorbed only at the Schnorr node. -/
  delta : Option C.Point
  /-- The folded generator `sg` — *not* absorbed by the deployed sponge, carried for the same
  reason `IpaNode.sg` is (see `Deployed.lean`'s preamble and `sg_determined_of_verifyWith`). -/
  sg : Option C.Point
  deriving DecidableEq

section Nodes

variable {nc k : ℕ}

/-- The node as a product, hand-written for the same reason `ipaNodeEquivProd` is: `deriving
Fintype` does not fire through the curve bundle. -/
private def kimchiNodeEquivProd (C : Ipa.CommitmentCurve) (nc k : ℕ) :
    (Squeeze k × PreIpaData C nc × (Fin k → Option (C.Point × C.Point)) ×
        Option C.Point × Option C.Point) ≃ KimchiNode C nc k where
  toFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
  invFun t := (t.idx, t.pre, t.lr, t.delta, t.sg)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The measure space exists** — the analogue of `instFintypeIpaNode`. -/
instance instFintypeKimchiNode : Fintype (KimchiNode C nc k) :=
  Fintype.ofEquiv _ (kimchiNodeEquivProd C nc k)

/-- **The expansion map per squeeze.** `β`/`γ` are the raw 128-bit value cast into the field;
every other squeeze is endo-expanded. The analogue of `Deployed.expandPre`, indexed because
kimchi uses two maps where the IPA uses one. -/
def squeezeExpand (C : Ipa.CommitmentCurve) : Squeeze k → Prechallenge → C.ScalarField
  | .beta | .gamma => fun q => ((q : ℕ) : C.ScalarField)
  | _ => expandPre C

/-- The node at squeeze `s`: the fields absorbed by then are `some`, the rest `none`. The
direct analogue of `Deployed.nodeU`/`nodeC`, whose `lr` is `some` at rounds `≤ idx` and `none`
after. -/
def nodeAt (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
    (cp : KimchiProof C nc k) (s : Squeeze k) : KimchiNode C nc k where
  idx := s
  pre :=
    { digest := digest
      publicComm := publicComm
      wComm := fun col j => cp.wComm[col][j]
      zComm := match s with
        | .beta | .gamma => none
        | _ => some (fun j => cp.zComm[j])
      tComm := match s with
        | .beta | .gamma | .alpha => none
        | _ => some (fun j => cp.tComm[(j : ℕ)]?)
      ftEval1 := match s with
        | .beta | .gamma | .alpha | .zeta => none
        | _ => some cp.ftEval1
      evals := match s with
        | .beta | .gamma | .alpha | .zeta => none
        | _ => some (evalsViewOf cp) }
  lr := match s with
    | .ipaRound i => fun j => if (j : ℕ) ≤ (i : ℕ) then some cp.opening.lr[j] else none
    | .schnorr => fun j => some cp.opening.lr[j]
    | _ => fun _ => none
  delta := match s with
    | .schnorr => some cp.opening.delta
    | _ => none
  sg := match s with
    | .schnorr => some cp.opening.sg
    | _ => none

/-- **The deployed prefixes**: which node each squeeze is read at. The analogue of
`Deployed.nodes`, and the object the abstract game's `prefixes` argument wants. -/
def kimchiNodes (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
    (cp : KimchiProof C nc k) : Squeeze k → KimchiNode C nc k :=
  nodeAt digest publicComm cp

/-- The round decoder: at an `ipaRound i` node the cross-terms are present, so round `i`'s pair
is read straight off. The analogue of `Deployed.nodeRound`. -/
private def kimchiRound (t : KimchiNode C nc k) : C.Point × C.Point :=
  match t.idx with
  | .ipaRound i => (t.lr i).getD (0, 0)
  | _ => (0, 0)

/-- The final decoder: the Schnorr node carries `δ` and `sg`. The analogue of
`Deployed.nodeFinal`. -/
private def kimchiFinal (t : KimchiNode C nc k) : C.Point × C.Point :=
  (t.delta.getD 0, t.sg.getD 0)

/-- **The absorbing squeeze of a flat stream row**. The squeeze at whose
node the group element sitting at a given flat position has already been absorbed into the
transcript:

* the public block (flat positions `< nc`) is part of the verifier-computed public
  commitment, present at every node, so `β`;
* the derived `ft` row (flat position `nc`) is recomputed by the verifier from the quotient
  chunks and the key, both present no later than `ζ`, so `ζ`;
* tail row `0` is the permutation accumulator `z`, first absorbed at `α`;
* every other tail row — the six selectors, the fifteen witness columns, the fifteen
  coefficient columns and the six σ columns — is absorbed by `β` (the witness commitments are
  absorbed just before `β`; the key rows are part of the absorbed digest and are therefore
  present at every node).

This is the index map `hrepPrefix` uses to say *at which node* a row's AGM representation must
already be fixed. Project-local: it is layout data about `Kimchi.Verifier`'s flat stream, and
has no Mathlib analogue. -/
private def absorbedBy {nc k : ℕ} (i : Fin (nc + 1 + tailRowCount * nc)) : Squeeze k :=
  if (i : ℕ) < nc then Squeeze.beta
  else if (i : ℕ) = nc then Squeeze.zeta
  else if ((i : ℕ) - (nc + 1)) / nc = 0 then Squeeze.alpha
  else Squeeze.beta

/-- `absorbedBy` at the permutation-accumulator row (tail row `0`): `α`, the first squeeze at
whose node `zComm` is present. -/
private theorem absorbedBy_streamPos_zRow (c : Fin nc) :
    absorbedBy (k := k) (streamPos nc zRow c) = Squeeze.alpha := by
  have hval : (streamPos nc zRow c : ℕ) = nc + 1 + (c : ℕ) := by
    show (if (1 : ℕ) < 1 then (c : ℕ) else nc + 1 + (1 - 1) * nc + (c : ℕ)) = _
    rw [if_neg (by omega)]
    omega
  have hdiv : (nc + 1 + (c : ℕ) - (nc + 1)) / nc = 0 := by
    rw [show nc + 1 + (c : ℕ) - (nc + 1) = (c : ℕ) by omega]
    exact Nat.div_eq_of_lt c.isLt
  have hne : ¬ nc + 1 + (c : ℕ) = nc := by omega
  have hnlt : ¬ nc + 1 + (c : ℕ) < nc := by omega
  rw [absorbedBy, hval, if_neg hnlt, if_neg hne, if_pos hdiv]

/-- `absorbedBy` at every tail row from the selectors on — the six selectors, the fifteen
witness columns, the fifteen coefficient columns and the six σ columns: `β`. The witness
commitments are absorbed immediately before `β` is squeezed, and the key rows are part of the
absorbed digest, hence present at every node. -/
private theorem absorbedBy_streamPos_of_two_le (hnc : 0 < nc) (i : Fin batchRows)
    (hi : 2 ≤ (i : ℕ)) (c : Fin nc) :
    absorbedBy (k := k) (streamPos nc i c) = Squeeze.beta := by
  have hval : (streamPos nc i c : ℕ) = nc + 1 + ((i : ℕ) - 1) * nc + (c : ℕ) := by
    show (if (i : ℕ) < 1 then (c : ℕ) else nc + 1 + ((i : ℕ) - 1) * nc + (c : ℕ)) = _
    rw [if_neg (by omega)]
  have hsub : nc + 1 + ((i : ℕ) - 1) * nc + (c : ℕ) - (nc + 1)
      = nc * ((i : ℕ) - 1) + (c : ℕ) := by
    rw [Nat.mul_comm]
    omega
  have hdiv : (nc + 1 + ((i : ℕ) - 1) * nc + (c : ℕ) - (nc + 1)) / nc ≠ 0 := by
    rw [hsub, Nat.mul_add_div hnc, Nat.div_eq_of_lt c.isLt]
    omega
  have hge : nc ≤ nc + 1 + ((i : ℕ) - 1) * nc + (c : ℕ) := by omega
  have hne : ¬ nc + 1 + ((i : ℕ) - 1) * nc + (c : ℕ) = nc := by omega
  have hnlt : ¬ nc + 1 + ((i : ℕ) - 1) * nc + (c : ℕ) < nc := Nat.not_lt.mpr hge
  rw [absorbedBy, hval, if_neg hnlt, if_neg hne, if_neg hdiv]

end Nodes

/-! ### The IPA extraction, inside the kimchi transcript

`Bulletproof.Forking.kimchiExtract` is generic in the oracle domain `T`, the alphabet `Pre` and
the proof type `Pf`. So it instantiates at `T := KimchiNode C nc σ.k`,
`Pf := KimchiProof C nc σ.k` directly — this is the reuse claim, made concrete rather than
asserted.

Everything is stated at `σ.k` rather than an independent `k`, following `Deployed.lean`: the
alternative drags `▸` transports through every signature. -/

section IpaInside

variable {nc : ℕ} [Module C.ScalarField C.Point]

/-- The IPA squeezes as prefixes into the kimchi transcript: round `j` for `j < σ.k`, then the
Schnorr squeeze. The analogue of `Deployed.nodes`, restricted to the opening argument. -/
private def ipaPrefixes (σ : SRS C.Point) (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
    (cp : KimchiProof C nc σ.k) : Fin (σ.k + 1) → KimchiNode C nc σ.k :=
  fun j => kimchiNodes digest publicComm cp
    (if h : (j : ℕ) < σ.k then .ipaRound ⟨(j : ℕ), h⟩ else .schnorr)

/-- **OBLIGATION: commit-then-challenge at the kimchi prefixes.** The analogue of
`Deployed.decodesFromPrefixes_nodes`, and the property whose absence would make the game FALSE
rather than merely unproved. The `Option`-gating of `KimchiNode` exists to make it provable: at
`ipaRound i` the cross-terms are `some` exactly for rounds `≤ i`, and at `schnorr` the node
carries `δ` and `sg`.

Note the direction it certifies: that each prefix node carries ENOUGH to decode its round,
never that it carries no more. A node carrying the whole proof satisfies this too. -/
private def kimchiDecodesFromPrefixes (σ : SRS C.Point)
    (digest : C.ScalarField) (publicComm : Fin nc → C.Point) :
    Bulletproof.Forking.DecodesFromPrefixes σ
      (fun cp : KimchiProof C nc σ.k => Bulletproof.Ipa.Forking.toOpening cp.opening)
      (ipaPrefixes σ digest publicComm) where
  round := kimchiRound
  final := kimchiFinal
  round_eq := by
    intro cp j
    simp [ipaPrefixes, kimchiNodes, nodeAt, kimchiRound, Bulletproof.Ipa.Forking.toOpening]
  final_eq := by
    intro cp
    simp [ipaPrefixes, kimchiNodes, nodeAt, kimchiFinal, Bulletproof.Ipa.Forking.toOpening]

/-- **The IPA extraction inside the kimchi game** — `kimchiExtract` at the kimchi oracle
domain. That this elaborates at all is the reuse result: the abstract game layer needs no
change to serve a transcript that is not the IPA's own. -/
private def kimchiIpaExtract (σ : SRS C.Point)
    (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
    (b : Fin (2 ^ σ.k) → C.ScalarField) (v : C.ScalarField) (P : C.Point)
    (pg : Fin (2 ^ σ.k) → C.ScalarField) (pw : C.ScalarField)
    (hP : P = commitGen σ.g pg + pw • σ.h)
    (A : Zcash.Snark.OracleComp (KimchiNode C nc σ.k) Prechallenge (KimchiProof C nc σ.k))
    (O : KimchiNode C nc σ.k → Prechallenge)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (σ.k + 1)) :
    Option (Bulletproof.Forking.OpeningOrBreak σ P b v) :=
  Bulletproof.Forking.kimchiExtract σ b v P pg pw hP (expandPre C) A
    (fun cp => Bulletproof.Ipa.Forking.toOpening cp.opening)
    (ipaPrefixes σ digest publicComm)
    (kimchiDecodesFromPrefixes σ digest publicComm) O coins

end IpaInside

/-! ## 3. The family

The run's challenges are read off the table at the run's own nodes, so the claim
`(P, b, v)` the opening argument runs against is the one the win event checks. -/

section Game

variable [Module C.ScalarField C.Point]

/-- The challenge the oracle table supplies at squeeze `s` of this run's transcript. -/
def reads {nc k : ℕ} (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
    (cp : KimchiProof C nc k) (O : KimchiNode C nc k → Prechallenge) (s : Squeeze k) :
    C.ScalarField :=
  squeezeExpand C s (O (kimchiNodes digest publicComm cp s))

/-- The run's IPA claim at the table's challenges. -/
def runClaim {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc) (pub : Array C.ScalarField)
    (digest : C.ScalarField) (cp : KimchiProof C nc σ.k)
    (O : KimchiNode C nc σ.k → Prechallenge) :
    Ipa.Input C σ.k (nc + 1 + tailRowCount * nc) evalPts :=
  runInputWith σ cvk cp pub
    (reads digest (fun c => (publicCommitment C σ cvk pub)[c]) cp O Squeeze.beta)
    (reads digest (fun c => (publicCommitment C σ cvk pub)[c]) cp O Squeeze.gamma)
    (reads digest (fun c => (publicCommitment C σ cvk pub)[c]) cp O Squeeze.alpha)
    (reads digest (fun c => (publicCommitment C σ cvk pub)[c]) cp O Squeeze.zeta)
    (reads digest (fun c => (publicCommitment C σ cvk pub)[c]) cp O Squeeze.polyscale)
    (reads digest (fun c => (publicCommitment C σ cvk pub)[c]) cp O Squeeze.evalscale)

/-- **The warm opening base at a run**. The deployed verifier does not derive
the `U` base of the opening argument from a cold sponge: it continues the fq sponge from the
*warm* state — the state reached after the whole pre-opening absorb schedule, i.e. the state at
which `ζ` is squeezed — and squeezes the base there, at the `preT` prefix of the claim the run
opens. This is that group element, as a function of the emitted proof and the oracle table:
`toGroup` of `kimchiOpeningFS`'s base squeeze at `preT (runClaim …)`.

It is the map the family's runs are checked at, and it is *not* a function of the claimed value
alone, which is why it needs base stability rather than the
older factors-through-the-claim hypothesis. Mirrors nothing directly; it is to the base what
`runClaim` (just above) is to the claim, and is written in the same table-reading style. -/
def warmBase {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc) (pub : Array C.ScalarField)
    (digest : C.ScalarField) (cp : KimchiProof C nc σ.k)
    (O : KimchiNode C nc σ.k → Prechallenge) : C.Point :=
  C.toGroup ((kimchiOpeningFS cvk cp (publicCommitment C σ cvk pub)).squeezeBase
    (IpaTranscriptElt.preT (runClaim σ cvk pub digest cp O)))

/-- **The oracle table** the adversary and the extractor share. Ironwood's `Coins`
(ironwood's `Forking/Adversary/Algebraic.lean:857`) carries the recursive fork tape
alongside; here that tape stays a
parameter, which makes the bound hold for every complete tape rather than on average. -/
abbrev Coins (C : Ipa.CommitmentCurve) (nc k : ℕ) : Type := KimchiNode C nc k → Prechallenge

/-- **A basis-indexed kimchi adversary family** — the analogue of `DeployedFamily`.

Beyond an adversary and its query bound it carries (i) the circuit `idx` and its correspondence
to the presented verifying key, so the extracted witness satisfies *the circuit the verifier
checked*, and (ii) the AGM representations `aRef`/`ρRef` of the run's flat commitment stream
and `aT`/`ρT` of the quotient chunks — the same data `kimchiVesta_run_sound_algebraic_ft` takes
as hypotheses, here supplied by the family because we are in the algebraic group model. They
are indexed by the oracle table as well as by the basis: kimchi's claim is adversary output, so
it is table-dependent, unlike `DeployedFamily.claim`. -/
structure KimchiFamily (C : Ipa.CommitmentCurve) [Module C.ScalarField C.Point]
    (nc k n : ℕ) [NeZero n] where
  /-- The verifying key presented at each basis. -/
  cvk : (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) → KimchiVK C nc
  /-- The public input at each basis. -/
  pub : (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) → Array C.ScalarField
  /-- The absorbed key digest, as a transcript label. Free family data, and harmless as
  such: the bound is ∀-families, and the bridge self-polices — a family whose label
  diverges from `VerifierIndex::digest()` makes `FSFaithful` unsatisfiable rather than
  silently applying (external-audit B-5). -/
  digest : (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) → C.ScalarField
  /-- The circuit the key is a key *for*. -/
  idx : Index C.ScalarField n
  /-- The bounded-query algebraic adversary at each basis. -/
  adversary : (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) →
    Zcash.Snark.OracleComp (KimchiNode C nc k) Prechallenge (KimchiProof C nc k)
  /-- The query bound shared by the whole family. -/
  Q : ℕ
  /-- Every basis's adversary respects it. -/
  queryBound : ∀ basis, (adversary basis).QueryBound Q
  /-- Chunking is nontrivial. -/
  hnc : 0 < nc
  /-- Production chunking: the flat stream covers the domain. -/
  hkn : nc * 2 ^ k = n
  /-- The presented key's domain is the circuit's. -/
  hn : ∀ basis, (cvk basis).n = n
  /-- **The key is the circuit's key** — what ties the conclusion to the verifier. -/
  hvk : ∀ basis, (cvk basis).Corresponds (srsOfBasis k basis) idx
  /-- The public input has the circuit's arity. -/
  hpub : ∀ basis, (pub basis).size = idx.publicCount
  /-- The quotient commitment is non-empty. Not algebraic-group data: this RESTRICTS the
  adversary, and is required by `run_sound_algebraic_ft`. -/
  htpos : ∀ basis O, 0 < ((adversary basis).run O).tComm.size
  /-- AGM: the SRS-basis coefficients of every commitment in the run's flat IPA stream. -/
  aRef : (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) →
    (O : KimchiNode C nc k → Prechallenge) →
    Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ k) → C.ScalarField
  /-- AGM: the matching blinding coefficients. -/
  ρRef : (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) →
    (O : KimchiNode C nc k → Prechallenge) →
    Fin (nc + 1 + tailRowCount * nc) → C.ScalarField
  /-- The representations are representations of the run's own stream. -/
  hrep : ∀ basis O i,
    commit (srsOfBasis k basis) (aRef basis O i) (ρRef basis O i)
      = (runClaim (srsOfBasis k basis) (cvk basis) (pub basis) (digest basis)
          ((adversary basis).run O) O).commitmentFn i
  /-- AGM: the coefficients of the quotient chunks, which sit outside the batched stream. -/
  aT : (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) →
    (O : KimchiNode C nc k → Prechallenge) →
    Fin ((adversary basis).run O).tComm.size → Fin (2 ^ k) → C.ScalarField
  /-- AGM: the matching quotient blinders. -/
  ρT : (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) →
    (O : KimchiNode C nc k → Prechallenge) →
    Fin ((adversary basis).run O).tComm.size → C.ScalarField
  /-- The quotient representations are representations of the run's own chunks. -/
  hTC : ∀ basis O (j : Fin ((adversary basis).run O).tComm.size),
    commit (srsOfBasis k basis) (aT basis O j) (ρT basis O j)
      = ((adversary basis).run O).tComm[j]
  /-- **AGM faithfulness on the flat stream**: the coefficient
  vector and blinder the family declares for a stream row are a function of the transcript
  prefix at the node where that row was absorbed (`absorbedBy`), not of the whole oracle table.

  This is what "algebraic adversary" *means* — in the algebraic group model the representation
  is observed at the moment the group element is emitted — and without it the family may choose
  its representation after seeing the very challenge an exclusion set is about, which destroys
  the blindness the adaptive Schwartz–Zippel charge needs. It is a field rather than a
  hypothesis of the endpoint because the endpoint's statement is frozen; it narrows the family
  class to exactly the families the algebraic group model admits. One honest boundary of
  that class (external-audit B-6): a family whose representations depend on answers to
  OFF-RUN oracle cells — cells its own transcript never reads — while emitting the same
  commitments is excluded; that is the emission-time reading of AGM-in-the-ROM, and it is
  the narrowing this field performs. -/
  hrepPrefix : ∀ basis O O' (i : Fin (nc + 1 + tailRowCount * nc)),
    kimchiNodes (digest basis)
        (fun c => (publicCommitment C (srsOfBasis k basis) (cvk basis) (pub basis))[c])
        ((adversary basis).run O) (absorbedBy i)
      = kimchiNodes (digest basis)
        (fun c => (publicCommitment C (srsOfBasis k basis) (cvk basis) (pub basis))[c])
        ((adversary basis).run O') (absorbedBy i) →
    aRef basis O i = aRef basis O' i ∧ ρRef basis O i = ρRef basis O' i
  /-- **AGM faithfulness on the quotient chunks**: same contract for `aT`/`ρT`, whose absorbing
  squeeze is `ζ` (the quotient commitment is absorbed immediately before `ζ` is squeezed).

  Stated with two independently-typed chunk indices related by `(j : ℕ) = (j' : ℕ)` because the
  index type `Fin ((adversary basis).run O).tComm.size` depends on the table; at equal nodes the
  two runs' quotient commitments agree, so the two index types have the same cardinality, but
  saying so definitionally would require a transport in the statement. -/
  hTPrefix : ∀ basis O O' (j : Fin ((adversary basis).run O).tComm.size)
      (j' : Fin ((adversary basis).run O').tComm.size), (j : ℕ) = (j' : ℕ) →
    kimchiNodes (digest basis)
        (fun c => (publicCommitment C (srsOfBasis k basis) (cvk basis) (pub basis))[c])
        ((adversary basis).run O) Squeeze.zeta
      = kimchiNodes (digest basis)
        (fun c => (publicCommitment C (srsOfBasis k basis) (cvk basis) (pub basis))[c])
        ((adversary basis).run O') Squeeze.zeta →
    aT basis O j = aT basis O' j' ∧ ρT basis O j = ρT basis O' j'

namespace KimchiFamily

variable {nc k n : ℕ} [NeZero n] (fam : KimchiFamily C nc k n)

/-- The proof the adversary emits at a basis and a table. -/
def proofOf (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    KimchiProof C nc k :=
  (fam.adversary basis).run O

/-- The public commitment chunks presented at a basis. -/
def publicComm (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) : Fin nc → C.Point :=
  fun c => (publicCommitment C (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis))[c]

/-- The run's IPA claim at a basis and a table. -/
def claim (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    Ipa.Input C k (nc + 1 + tailRowCount * nc) evalPts :=
  runClaim (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis) (fam.digest basis)
    (fam.proofOf basis O) O

/-- **The family's warm opening base** at a basis and a table: `warmBase` at the family's own
SRS, verifying key, public input and digest, on the proof the adversary emits. Mirrors
`KimchiFamily.claim` just above, one field at a time, with `runClaim` replaced by `warmBase`. -/
def warmBase (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    C.Point :=
  _root_.Kimchi.Verifier.KnowledgeSoundness.warmBase (srsOfBasis k basis) (fam.cvk basis)
    (fam.pub basis) (fam.digest basis) (fam.proofOf basis O) O

/-- The SRS the opening argument runs against: the sampled basis with the transcript-derived
IPA base. Matching `deployedExtract`, whose `U` override this copies — except that the override
point is the WARM base `fam.warmBase basis O`, the one the deployed kimchi verifier actually
squeezes from the post-`ζ` sponge state, not the cold `uBaseOf` of the standalone opening. -/
private def runSrs (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    SRS C.Point :=
  { srsOfBasis k basis with U := fam.warmBase basis O }

/-- **The deployed win**: the executable challenge-generic verifier accepts, with *every*
challenge read off the table at the run's own nodes — the pre-IPA six, the `k` round challenges
and the Schnorr challenge — and with the opening base the WARM one, `fam.warmBase basis O`.
The analogue of `Deployed.wireWins`.

The base slot is where this parts company with the standalone opening. `Deployed.wireWins` feeds
`uBaseOf C (Ipa.cipOf claim)`, the base squeezed from a sponge started at `FqSponge.init`, and
that is correct there: for the standalone IPA the opening *is* the whole protocol, so its sponge
really does start cold. Inside kimchi the opening is reached only after the key digest, the
public commitment chunks, the witness, permutation and quotient chunks have been absorbed, and
the deployed verifier squeezes its base from THAT state. `fam.warmBase basis O` is that point
(`KimchiFamily.warmBase` just above), so with it in this slot `Bridge.kimchiVerify_eq_gameArgs`
needs no base-agreement hypothesis: the two sides are the same term. -/
def Wins (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) : Prop :=
  kimchiVerifyWith (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
      (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.beta)
      (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.gamma)
      (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.alpha)
      (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.zeta)
      (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O
        Squeeze.polyscale)
      (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O
        Squeeze.evalscale)
      (fam.warmBase basis O)
      (Vector.ofFn fun i : Fin k =>
        reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O
          (Squeeze.ipaRound i))
      (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.schnorr)
    = true

/-- The run's transcript node at each squeeze — `kimchiNodes` at the family's own digest,
public commitment and emitted proof. The index the AGM-faithfulness fields are stated over. -/
private def nodesOf (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    Squeeze k → KimchiNode C nc k :=
  kimchiNodes (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O)

/-- **AGM faithfulness, in the form a Schwartz–Zippel charge consumes** — the representation
half of the exclusion sets' node-determinacy: a stream row's coefficient vector and blinder
are functions of the run's node at that row's absorbing squeeze, so an exclusion set built from
them at a node strictly *later* than that squeeze does not read the oracle at its own node.

The `absorbedBy_streamPos_*` lemmas identify that squeeze for the row families the proof
visits. -/
private theorem repPrefix_of_absorbedBy (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O O' : Coins C nc k) (i : Fin (nc + 1 + tailRowCount * nc)) {s : Squeeze k}
    (hs : absorbedBy i = s) (hnode : fam.nodesOf basis O s = fam.nodesOf basis O' s) :
    fam.aRef basis O i = fam.aRef basis O' i ∧ fam.ρRef basis O i = fam.ρRef basis O' i := by
  refine fam.hrepPrefix basis O O' i ?_
  rw [hs]
  exact hnode

/-- The quotient-chunk half of `repPrefix_of_absorbedBy`: `aT`/`ρT` are functions of the run's
`ζ` node, the node at which the quotient commitment has been absorbed. -/
private theorem tPrefix_of_zetaNode (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O O' : Coins C nc k) (j : Fin ((fam.adversary basis).run O).tComm.size)
    (j' : Fin ((fam.adversary basis).run O').tComm.size) (hj : (j : ℕ) = (j' : ℕ))
    (hnode : fam.nodesOf basis O Squeeze.zeta = fam.nodesOf basis O' Squeeze.zeta) :
    fam.aT basis O j = fam.aT basis O' j' ∧ fam.ρT basis O j = fam.ρT basis O' j' :=
  fam.hTPrefix basis O O' j j' hj hnode

/-! ### The AGM representation of the combined commitment -/

/-- The polyscale-combination of the family's per-commitment coefficient vectors. -/
private def pgOf (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    Fin (2 ^ k) → C.ScalarField :=
  fun j => ∑ i : Fin (nc + 1 + tailRowCount * nc),
    (fam.claim basis O).polyscale ^ (i : ℕ) * fam.aRef basis O i j

/-- The polyscale-combination of the family's per-commitment blinders. -/
private def pwOf (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    C.ScalarField :=
  ∑ i : Fin (nc + 1 + tailRowCount * nc),
    (fam.claim basis O).polyscale ^ (i : ℕ) * fam.ρRef basis O i

/-- **Per-commitment representations give the combined one** — pure linearity from `hrep`, and
the reason a `KimchiFamily` needs no `pg`/`pw`/`hP` fields of its own: they are projections.

The proof is `Finset.sum_comm` under `commitGen`. -/
private theorem hPOf (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    combinedCommitment (fam.claim basis O).polyscale (fam.claim basis O).commitmentFn
      = commitGen (fam.runSrs basis O).g (fam.pgOf basis O)
        + fam.pwOf basis O • (fam.runSrs basis O).h := by
  have hc : ∀ i, (fam.claim basis O).commitmentFn i
      = commitGen (srsOfBasis k basis).g (fam.aRef basis O i)
        + fam.ρRef basis O i • (srsOfBasis k basis).h := by
    intro i
    exact (fam.hrep basis O i).symm
  show combinedCommitment (fam.claim basis O).polyscale (fam.claim basis O).commitmentFn
      = commitGen (srsOfBasis k basis).g (fam.pgOf basis O)
        + fam.pwOf basis O • (srsOfBasis k basis).h
  simp only [combinedCommitment, hc, pgOf, pwOf, commitGen, smul_add, Finset.smul_sum,
    smul_smul, Finset.sum_add_distrib, Finset.sum_smul]
  rw [Finset.sum_comm]

end KimchiFamily

/-! ## 10. The verifying-key representation channel

`Verifier/Reduction/Soundness.lean` spends its binding hypothesis, irreducibly, on pinning the
chunk representation of the commitments *fixed by the verifying key* — the six σ rows, the
fifteen coefficient rows, the six selector rows and the public row — to the honest chunk
windows of the presented circuit's own polynomials. At the sampled basis
`Zcash.Snark.scalarBasis B s` a coefficient vector's commitment is
`(∑ l, s l * a l + ρ * s blind) • B`, so *every* vector represents *every* group element: a
family may declare, at a verifying-key row, the honest chunk of a **different** circuit whose
polynomials happen to commit to the same group elements, emit an honest proof for that
circuit, and open the perturbed polyscale combination. The key/circuit correspondence still
holds (it constrains group elements, which are unchanged), the verifier accepts, and
`attempt`'s coordinate test succeeds — so no relation is emitted, yet the assembled table
satisfies the *other* circuit. That is arm (4), unbounded by summand (IV).

**The repair is in the extractor itself, on its left branch.** A family whose verifying-key
representations are not the circuit's own has, by `vkRelation`, *produced* a discrete-log
relation among the sampled generators; the extractor returns that, on the break branch, rather
than a representation table it already knows cannot satisfy the presented circuit. This section
therefore sits above `attempt` — the whole point of its position in the file — and builds what
the gate needs: the honesty predicates (decidable, so the extractor can branch on them), the
relations a mismatch computes, and the two break selectors `vkBreak`/`ftBreak` the extractor
actually calls. The `ft` row gets the identical treatment: it is a *derived* commitment, and its
representation is exactly as unconstrained at the sampled basis as the key rows'.

### The two group-side halves, and why they are not assumed

Both `vkRelation` and `ftRelation` need the *group-side* half of the story: that the run's claim
carries, at the offending position, the honest chunk commitment (resp. the verifier's own `ft`
construction). Those facts are *consequences* of the family's `hvk` and the flat-stream layout —
`vkCommHonest_of_wins` and `ftCommHonest` prove them here — but they are not available inside a
`def`, because the public row's case additionally needs the run's acceptance and a curve-specific
`.val`-scalar collapse. So the break selectors ask for the group-side half *at the row they
fire on*, and a left payload consequently certifies "no row is broken"; a consumer holding
`Wins` turns that into key-honesty outright (`attempt_inl_keyHonest_of_wins`). -/

section VkChannel

/-! ### The verifying-key rows -/

/-- **The verifying-key batch rows**, as one index type: the public row, the six selector
rows, the fifteen coefficient rows and the six σ rows. These are exactly the rows whose
chunk representation `kimchiProof_sound_of_openings_of_vkrep` pins with binding. -/
private inductive VkRow where
  /-- The public row. -/
  | pub : VkRow
  /-- The `j`-th selector row, in `selGate` order. -/
  | sel (j : Fin selCount) : VkRow
  /-- The `c`-th coefficient row. -/
  | coeff (c : Fin coeffCols) : VkRow
  /-- The `i`-th σ row (first six columns only). -/
  | sigma (i : Fin sigmaRows) : VkRow

/-- The abstract batch row a verifying-key row sits at. -/
private def VkRow.batchRow : VkRow → Fin batchRows
  | .pub => pubRow
  | .sel j => selRow j
  | .coeff c => cRow c
  | .sigma i => sRow i

/-- **A commitment collision is a discrete-log relation** (binding-free): two representations
of the same group element differ by a relation among `[σ.g, σ.h]`.

Kept local — and `private` — because it is the three-line algebraic core of
`Reduction/Soundness`'s `dlRelation_of_chunk_rep_ne`, and this section must not wait on that
lane to state its own break branch. -/
private theorem dlRelation_of_commit_eq {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (σ : SRS G) (a b : Fin (2 ^ σ.k) → F) (ρ ρb : F)
    (h : commit σ a ρ = commit σ b ρb) : DLRelation σ (a - b) (ρ - ρb) := by
  have h0 : DLRelation σ (a - b) (ρ - ρb) ↔ commitₗ σ ((a, ρ) - (b, ρb)) = 0 := Iff.rfl
  rw [h0, map_sub]
  exact sub_eq_zero_of_eq h

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ} [NeZero n]

/-- The circuit polynomial a verifying-key row is the chunked commitment of: the σ, coefficient
and selector interpolants at their rows, and the **negated** public interpolant at the public
row (kimchi commits to `−pubPoly`, `publicCommitment_corresponds`). -/
private noncomputable def vkRowPoly (idx : Index F n) (pub : Array F) : VkRow → Polynomial F
  | .pub => -(idx.pubPoly (pubView idx pub))
  | .sel j => idx.selectorPoly (selGate j)
  | .coeff c => idx.coeffPoly c
  | .sigma i => idx.sigmaPoly (sigmaPermCol i)

/-- The blinder the honest chunk commitment of a verifying-key row carries: the selectors and
the public commitment are masked with the fixed unit blinder (`mask_custom`), the σ and
coefficient columns are unblinded. -/
private def vkRowBlinder : VkRow → F
  | .pub => 1
  | .sel _ => 1
  | .coeff _ => 0
  | .sigma _ => 0

/-- **The permutation scalar `runInputWith` computes**, named. The `let pScalar := …` line of
`runInputWith` verbatim, with the four fq-side squeezes handed in; `runPScalar` is this at the
sponge's own values. Named here because the `ft` row's honest coefficient window mentions it,
and the knowledge-soundness game's claim is `runInputWith`, not `runInput`. -/
private def pScalarWith {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (beta gamma alpha zeta : C.ScalarField) : C.ScalarField :=
  Kimchi.Protocol.Linearization.permScalar beta gamma alpha
    (Kimchi.Protocol.Linearization.zkpmEval cvk.n cvk.zkRows cvk.omega zeta)
    (cp.linEvals (powPow2 zeta σ.k) (powPow2 (zeta * cvk.omega) σ.k))

omit [Module C.ScalarField C.Point] in
/-- **The layout bridge at the game's own claim**: the challenge-generic claim's commitment
column reads, at the stream position of abstract batch row `i` and chunk `c`, exactly the
abstract batch's entry there.

`Capstone/Reflection.lean`'s `commitmentFn_streamPosAt` says this at `runInput`, the run's *own*
sponge-driven claim; the game's claim is `runInputWith` at the oracle table's challenges. The
two flat streams differ in one slot only — the derived `ft` row at flat position `nc` — which
no batch position reads, and that is exactly the freedom `batchC_eq_flat_gen` was stated
with. -/
private theorem commitmentFn_streamPos_with {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField) (i : Fin batchRows) (c : Fin nc) :
    (runInputWith σ cvk cp pub beta gamma alpha zeta v u).commitmentFn (streamPos nc i c)
      = batchC (fun (col : Fin wCols) (c : Fin nc) => (cp.wComm[col])[c])
          (fun c => cp.zComm[c])
          (fun c => (publicCommitment C σ cvk pub)[c]) cvk.comms i c := by
  show ((_ : Vector (C.Point × C.ScalarField × C.ScalarField) (nc + 1 + tailRowCount * nc)).map
      (·.1))[(streamPos nc i c : ℕ)]'((streamPos nc i c).isLt) = _
  rw [Vector.getElem_map]
  exact (batchC_eq_flat_gen _ (fun _ => rfl) _ i c).symm

omit [Module C.ScalarField C.Point] in
/-- The verifier's squaring ladder computes the power. Project-local: the same two-line
induction is `private` in `Capstone/Reflection.lean`. -/
private theorem powPow2_eq' {F : Type*} [Field F] (x : F) (j : ℕ) :
    powPow2 x j = x ^ 2 ^ j := by
  induction j with
  | zero => simp [powPow2]
  | succ m ih =>
    have hstep : powPow2 x (m + 1) = powPow2 x m * powPow2 x m := by
      simp [powPow2, List.range_succ]
    rw [hstep, ih, ← pow_add, pow_succ, Nat.mul_comm, Nat.two_mul]

omit [Module C.ScalarField C.Point] in
/-- **The derived `ft` row at its own flat position, at the game's own claim.** The `ft` slot
is the one place where `runInputWith` and the sponge-driven `runStreamP` differ, so this read
is done here rather than borrowed from `commitmentFn_ftPos`. -/
private theorem commitmentFn_ftPos_with {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField) :
    (runInputWith σ cvk cp pub beta gamma alpha zeta v u).commitmentFn
        ⟨nc, by omega⟩
      = Ipa.combineCommitments C (powPow2 zeta σ.k)
          ((cvk.sigmaComm[6]).map
            (fun P => (pScalarWith σ cvk cp beta gamma alpha zeta).val • P)).toArray
        - (powPow2 zeta cvk.domainLog2 - 1).val
            • Ipa.combineCommitments C (powPow2 zeta σ.k) cp.tComm := by
  show ((_ : Vector (C.Point × C.ScalarField × C.ScalarField) (nc + 1 + tailRowCount * nc)).map
      (·.1))[(nc : ℕ)]'(by omega) = _
  rw [Vector.getElem_map, Vector.getElem_append, dif_pos (show nc < nc + 1 by omega),
    Vector.getElem_append, dif_neg (show ¬ nc < nc by omega)]
  simp [pScalarWith]

/-! ### The two halves of key-honesty -/

namespace KimchiFamily

variable {nc k : ℕ} (fam : KimchiFamily C nc k n)

/-- The flat position of the derived `ft` row: immediately after the public block's `nc`
chunks. Named because three declarations below index `aRef`/`ρRef` there. -/
private def ftPos (nc : ℕ) : Fin (nc + 1 + tailRowCount * nc) := ⟨nc, by omega⟩

/-- The challenge the oracle table hands *this* run at squeeze `s` — `reads` at the family's
own digest, public commitment and emitted proof. The six pre-IPA values of `fam.claim` are
exactly these. -/
private def readsOf (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (s : Squeeze k) : C.ScalarField :=
  reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O s

/-- **Honest verifying-key representations**. At a basis and a table, the
family's AGM coefficient vector at every verifying-key stream position is the honest chunk
window of the presented circuit's own polynomial.

This is the predicate the repaired `ipaAttempt` branches on, which is why it is a plain
`∀`-conjunction over finite index types rather than an existential or a quotient: it is
decidable. -/
private def VkRepHonest (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    Prop :=
  ∀ (r : VkRow) (c : Fin nc),
    fam.aRef basis O (streamPos nc r.batchRow c)
      = chunkCoeffs (2 ^ k) (vkRowPoly fam.idx (fam.pub basis) r) (c : ℕ)

/-- **Honest verifying-key commitments** — the group-side half of key-honesty: the run's claim
carries, at every verifying-key stream position, the honest chunk commitment of the circuit's
own polynomial, at that row's fixed blinder.

Unlike `VkRepHonest` this is *not* adversary-chosen data: it follows from the family's `hvk`
together with the flat-stream layout. It is a hypothesis here only because that layout bridge
is `private` to the reflection layer; see this section's preamble. -/
private def VkCommHonest (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    Prop :=
  ∀ (r : VkRow) (c : Fin nc),
    (fam.claim basis O).commitmentFn (streamPos nc r.batchRow c)
      = commit (srsOfBasis k basis)
          (chunkCoeffs (2 ^ k) (vkRowPoly fam.idx (fam.pub basis) r) (c : ℕ))
          (vkRowBlinder r)

/-- **The group-side half of key-honesty is a theorem at the three key row families**,
the public row carried as a hypothesis.

`VkCommHonest` is not adversary-chosen data: at the σ, coefficient and selector rows it is the
family's `hvk` (key/circuit correspondence) read through the flat-stream layout, and nothing
else is needed. The public row is different in kind — it is not a key entry but is recomputed
by the verifier from the key's Lagrange basis — so its case additionally needs the run's
acceptance (for the Lagrange-basis size), the public-input arity and the `.val`-scalar
collapse, exactly as `Capstone/Reflection.lean`'s `commitmentFn_streamPos_pubRow_eq_commit`
does. That bridge is `private` at the moment of writing, so the public row enters here as the
hypothesis `hpubRow`; a consumer holding `Wins` supplies it. -/
private theorem vkCommHonest_of_pubRow (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k)
    (hpubRow : ∀ c : Fin nc,
      (fam.claim basis O).commitmentFn (streamPos nc pubRow c)
        = commit (srsOfBasis k basis)
            (chunkCoeffs (2 ^ k)
              (-(fam.idx.pubPoly (pubView fam.idx (fam.pub basis)))) (c : ℕ)) 1) :
    fam.VkCommHonest basis O := by
  have hbr := commitmentFn_streamPos_with (srsOfBasis k basis) (fam.cvk basis)
    (fam.proofOf basis O) (fam.pub basis)
    (fam.readsOf basis O Squeeze.beta) (fam.readsOf basis O Squeeze.gamma)
    (fam.readsOf basis O Squeeze.alpha) (fam.readsOf basis O Squeeze.zeta)
    (fam.readsOf basis O Squeeze.polyscale) (fam.readsOf basis O Squeeze.evalscale)
  intro r c
  cases r with
  | pub => exact hpubRow c
  | sel j =>
      exact ((hbr (selRow j) c).trans
        (batchC_selRow_of_corresponds (srsOfBasis k basis) (fam.hvk basis).1 _ _ _ j c)).trans
          (commitPolyMaskedChunk_as_commit _ _ (c : ℕ))
  | coeff cc =>
      exact ((hbr (cRow cc) c).trans
        (batchC_cRow_of_corresponds (srsOfBasis k basis) (fam.hvk basis).1 _ _ _ cc c)).trans
          (commitPolyChunk_eq_commit _ _ (c : ℕ))
  | sigma i =>
      exact ((hbr (sRow i) c).trans
        (batchC_sRow_of_corresponds (srsOfBasis k basis) (fam.hvk basis).1 _ _ _ i c)).trans
          (commitPolyChunk_eq_commit _ _ (c : ℕ))

/-- **A winning run has a big enough Lagrange basis.** The challenge-generic verifier's first
act is the size guard `cvk.lagrangeBasis.size < pub.size || n < pub.size`, so acceptance
delivers the inequality `publicCommitment_corresponds` needs. -/
private theorem le_lagrangeBasis_size_of_wins (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) (h : fam.Wins basis O) :
    (fam.pub basis).size ≤ (fam.cvk basis).lagrangeBasis.size := by
  by_contra hlt
  rw [KimchiFamily.Wins, kimchiVerifyWith,
    if_pos (by simp [Nat.lt_of_not_le hlt])] at h
  exact Bool.noConfusion h

/-- **The group-side half of key-honesty, outright, on a winning run.**
The public row's hypothesis of `vkCommHonest_of_pubRow` is
discharged from `Capstone/Reflection.lean`'s `publicCommitment_corresponds`: the family's `hvk`
supplies the Lagrange chunk pin, `hpub` the public-input arity, and the run's own acceptance the
Lagrange-basis size. `hsmul` — the `.val`-scalar collapse — stays a parameter because it is
curve-specific, exactly as it is in `commitmentFn_streamPos_pubRow_eq_commit` (whose
orientation is the opposite one; the two are interchanged by `Eq.symm`). -/
private theorem vkCommHonest_of_wins (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k)
    (hsmul : ∀ (a : C.ScalarField) (P : C.Point), a • P = a.val • P)
    (hwin : fam.Wins basis O) : fam.VkCommHonest basis O := by
  refine fam.vkCommHonest_of_pubRow basis O fun c => ?_
  refine ((commitmentFn_streamPos_with (srsOfBasis k basis) (fam.cvk basis)
    (fam.proofOf basis O) (fam.pub basis)
    (fam.readsOf basis O Squeeze.beta) (fam.readsOf basis O Squeeze.gamma)
    (fam.readsOf basis O Squeeze.alpha) (fam.readsOf basis O Squeeze.zeta)
    (fam.readsOf basis O Squeeze.polyscale) (fam.readsOf basis O Squeeze.evalscale)
    pubRow c).trans ?_).trans (commitPolyMaskedChunk_as_commit _ _ (c : ℕ))
  refine (congrFun (batchC_pubRow (fun (col : Fin wCols) (c : Fin nc) =>
      ((fam.proofOf basis O).wComm[col])[c])
    (fun c => (fam.proofOf basis O).zComm[c])
    (fun c => (publicCommitment C (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis))[c])
    (fam.cvk basis).comms) c).trans ?_
  exact publicCommitment_corresponds C (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis)
    fam.idx (fun a P => (hsmul a P).symm) (fam.hvk basis).2.2.2.2.2.2
    (fam.le_lagrangeBasis_size_of_wins basis O hwin) (fam.hpub basis) c

/-! ### The break branch a key-dishonest representation computes -/

/-- **The relation computed at one offending verifying-key row** — the payload the repaired
`ipaAttempt` returns on its right branch.

Both representations of that row's group element are in hand: the family's own, by `hrep`, and
the honest chunk window, by `hcomm`. Their difference is a discrete-log relation among
`[σ.g, σ.h]`, injected into the run's augmented basis with coefficient `0` at the
transcript-derived slot `u` — which is what routes it to `relationFinder`'s `restrictToSetup`
branch, i.e. to arm (2), rather than to the residual.

The coefficients are explicit terms, not an existential: the extractor has to *emit* this
witness, so an existence statement would be useless to it. -/
private noncomputable def vkRelation (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k)
    (r : VkRow) (c : Fin nc)
    (hcomm : (fam.claim basis O).commitmentFn (streamPos nc r.batchRow c)
      = commit (srsOfBasis k basis)
          (chunkCoeffs (2 ^ k) (vkRowPoly fam.idx (fam.pub basis) r) (c : ℕ)) (vkRowBlinder r))
    (hne : fam.aRef basis O (streamPos nc r.batchRow c)
      ≠ chunkCoeffs (2 ^ k) (vkRowPoly fam.idx (fam.pub basis) r) (c : ℕ)) :
    Zcash.Snark.AlgebraicRelationWitness (F := C.ScalarField)
      (Zcash.Snark.augmentedBasis (fam.runSrs basis O).g (fam.runSrs basis O).U
        (fam.runSrs basis O).h) where
  coeffs := Zcash.Snark.augmentedCoeffs
    (fam.aRef basis O (streamPos nc r.batchRow c)
      - chunkCoeffs (2 ^ k) (vkRowPoly fam.idx (fam.pub basis) r) (c : ℕ)) 0
    (fam.ρRef basis O (streamPos nc r.batchRow c) - vkRowBlinder r)
  nontrivial := fun hzero =>
    sub_ne_zero_of_ne hne (funext fun i => congrFun hzero (Sum.inl i))
  relation := by
    rw [Zcash.Snark.representationEval_augmentedBasis]
    have h := dlRelation_of_commit_eq (srsOfBasis k basis)
      (fam.aRef basis O (streamPos nc r.batchRow c))
      (chunkCoeffs (2 ^ k) (vkRowPoly fam.idx (fam.pub basis) r) (c : ℕ))
      (fam.ρRef basis O (streamPos nc r.batchRow c)) (vkRowBlinder r)
      ((fam.hrep basis O (streamPos nc r.batchRow c)).trans hcomm)
    simpa using h

/-! ### The `ft` row: the same hole, and the same gate

The derived `ft` commitment sits at flat position `nc`, between the public block and the tail
rows. It is not a verifying-key row, but its representation is just as unconstrained at the
sampled basis: `run_sound_algebraic_at_of_vkrep`'s `hftRep` pins `aRef ⟨nc, _⟩` to the
`pScalar`-scaled `σ₆` chunk combination minus the quotient-chunk combination, and a family may
declare anything it likes there. The break is `Capstone/Algebraic.lean`'s
`ft_dlRelation_of_chunks_ne`, injected into the augmented basis with coefficient `0` at `u`
exactly as `vkRelation` is. -/

/-- The honest coefficient window of the derived `ft` row, at the family's own challenges:
`run_sound_algebraic_at_of_vkrep`'s `hftRep` right-hand side with `runOracles`' squeezes replaced
by the table's values and `runPScalar` by `pScalarWith`. -/
private noncomputable def ftHonestCoeffs (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) : Fin (2 ^ k) → C.ScalarField :=
  pScalarWith (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O)
      (fam.readsOf basis O Squeeze.beta) (fam.readsOf basis O Squeeze.gamma)
      (fam.readsOf basis O Squeeze.alpha) (fam.readsOf basis O Squeeze.zeta)
    • ∑ c : Fin nc, (fam.readsOf basis O Squeeze.zeta ^ 2 ^ k) ^ (c : ℕ)
        • chunkCoeffs (2 ^ k) (fam.idx.sigmaPoly 6) (c : ℕ)
  - (fam.readsOf basis O Squeeze.zeta ^ n - 1)
      • ∑ j : Fin (fam.proofOf basis O).tComm.size,
          (fam.readsOf basis O Squeeze.zeta ^ 2 ^ k) ^ (j : ℕ) • fam.aT basis O j

/-- The blinder that goes with `ftHonestCoeffs`: the quotient chunks are the only blinded
contributors to the derived `ft` commitment, since the `σ₆` chunk commitments are unblinded
fixed key columns. -/
private def ftHonestBlinder (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) : C.ScalarField :=
  -((fam.readsOf basis O Squeeze.zeta ^ n - 1)
    • ∑ j : Fin (fam.proofOf basis O).tComm.size,
        (fam.readsOf basis O Squeeze.zeta ^ 2 ^ k) ^ (j : ℕ) • fam.ρT basis O j)

/-- **Honest `ft` commitment** — the group-side half at the derived `ft` row: the run's claim
carries, at flat position `nc`, the verifier's own construction of the `ft` commitment
(`runFtComm`), expanded as the two `ζ^{2^k}`-chunk combinations that
`ft_dlRelation_of_chunks_ne` consumes.

The `ft`-row analogue of `VkCommHonest`, and like it *not* adversary-chosen: it follows from
the family's key/circuit correspondence together with the flat-stream layout. It is a named
predicate here because the extractor may not assume it (see the break-selector preamble). -/
private def FtCommHonest (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    Prop :=
  (fam.claim basis O).commitmentFn (ftPos nc)
    = pScalarWith (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O)
          (fam.readsOf basis O Squeeze.beta) (fam.readsOf basis O Squeeze.gamma)
          (fam.readsOf basis O Squeeze.alpha) (fam.readsOf basis O Squeeze.zeta)
        • ∑ c : Fin nc, (fam.readsOf basis O Squeeze.zeta ^ 2 ^ k) ^ (c : ℕ)
            • commitPolyChunk (srsOfBasis k basis) (fam.idx.sigmaPoly 6) (c : ℕ)
      - (fam.readsOf basis O Squeeze.zeta ^ n - 1)
          • ∑ j : Fin (fam.proofOf basis O).tComm.size,
              (fam.readsOf basis O Squeeze.zeta ^ 2 ^ k) ^ (j : ℕ)
                • (fam.proofOf basis O).tComm[j]

/-- **Honest `ft` representation**: the family's coefficient vector at the derived `ft` row is
the combination the verifier's own construction of that commitment forces. The `ft`-row
analogue of `VkRepHonest`, and the second half of the extractor's key gate. -/
private def FtRepHonest (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    Prop :=
  fam.aRef basis O (ftPos nc) = fam.ftHonestCoeffs basis O

/-- **`ft`-honesty is decidable** — one equality of vectors over a field with decidable
equality. `noncomputable` because Lagrange interpolation is. -/
noncomputable instance instDecidableFtRepHonest
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    Decidable (fam.FtRepHonest basis O) := by
  unfold FtRepHonest
  infer_instance

/-- **The relation an `ft`-dishonest representation computes** — the `ft`-row twin of
`vkRelation`. `hcomm` is the group-side half (the run's claim really does carry the verifier's
constructed `ft` commitment at flat position `nc`, expanded as the two chunk combinations);
`hne` is the coefficient mismatch. Their difference is `ft_dlRelation_of_chunks_ne`'s
discrete-log relation, injected into the augmented basis with coefficient `0` at `u`. -/
private noncomputable def ftRelation (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k)
    (hcomm : fam.FtCommHonest basis O)
    (hne : fam.aRef basis O (ftPos nc) ≠ fam.ftHonestCoeffs basis O) :
    Zcash.Snark.AlgebraicRelationWitness (F := C.ScalarField)
      (Zcash.Snark.augmentedBasis (fam.runSrs basis O).g (fam.runSrs basis O).U
        (fam.runSrs basis O).h) where
  coeffs := Zcash.Snark.augmentedCoeffs
    (fam.aRef basis O (ftPos nc) - fam.ftHonestCoeffs basis O) 0
    (fam.ρRef basis O (ftPos nc) - fam.ftHonestBlinder basis O)
  nontrivial := fun hzero =>
    sub_ne_zero_of_ne hne (funext fun i => congrFun hzero (Sum.inl i))
  relation := by
    rw [Zcash.Snark.representationEval_augmentedBasis]
    have h := ft_dlRelation_of_chunks_ne (srsOfBasis k basis) (fam.idx.sigmaPoly 6)
      (fun c : Fin nc => commitPolyChunk (srsOfBasis k basis) (fam.idx.sigmaPoly 6) (c : ℕ))
      (fun _ => rfl)
      (fun j : Fin (fam.proofOf basis O).tComm.size => (fam.proofOf basis O).tComm[j])
      (fam.aT basis O) (fam.ρT basis O) (fam.hTC basis O)
      (pScalarWith (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O)
        (fam.readsOf basis O Squeeze.beta) (fam.readsOf basis O Squeeze.gamma)
        (fam.readsOf basis O Squeeze.alpha) (fam.readsOf basis O Squeeze.zeta))
      (fam.readsOf basis O Squeeze.zeta) n
      (fam.aRef basis O (ftPos nc)) (fam.ρRef basis O (ftPos nc))
      (fam.ftHonestCoeffs basis O) (fam.ftHonestBlinder basis O) rfl rfl
      ((fam.hrep basis O (ftPos nc)).trans hcomm)
    simpa using h.1

/-- **The group-side half at the `ft` row is a theorem** — the `ft`-row companion of
`vkCommHonest_of_wins`, and unlike it needing no acceptance hypothesis: the derived `ft`
commitment is built by the verifier out of the key's seventh σ column and the proof's own
quotient chunks, so the family's `hvk` and `hn` suffice.

The proof transcribes `Capstone/Reflection.lean`'s ft-commitment computation at handed-in
challenges: the two executable running-power
combinations become `combinedCommitment`s, the squaring ladders become the powers `ζ^{2^k}` and
`ζ^n`, and the key's `σ₆` chunks become the circuit's own by the correspondence. `hsmul` — the
`.val`-scalar collapse — stays a parameter because it is curve-specific. -/
private theorem ftCommHonest
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (hsmul : ∀ (a : C.ScalarField) (P : C.Point), a • P = a.val • P) :
    fam.FtCommHonest basis O := by
  have hzM : powPow2 (fam.readsOf basis O Squeeze.zeta) (srsOfBasis k basis).k
      = fam.readsOf basis O Squeeze.zeta ^ 2 ^ k := powPow2_eq' _ _
  have hzN : powPow2 (fam.readsOf basis O Squeeze.zeta) (fam.cvk basis).domainLog2
      = fam.readsOf basis O Squeeze.zeta ^ n := by
    rw [powPow2_eq']
    exact congrArg (fun m => fam.readsOf basis O Squeeze.zeta ^ m) (fam.hn basis)
  have hs6 : ∀ c : Fin nc, ((fam.cvk basis).sigmaComm[6])[c]
      = commitPolyChunk (srsOfBasis k basis) (fam.idx.sigmaPoly 6) (c : ℕ) := fun c =>
    congrFun (congrFun (congrArg IndexComms.sigma (fam.hvk basis).1) 6) c
  show (fam.claim basis O).commitmentFn (ftPos nc) = _
  rw [show (fam.claim basis O).commitmentFn (ftPos nc) = _ from
      commitmentFn_ftPos_with (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O)
        (fam.pub basis) (fam.readsOf basis O Squeeze.beta) (fam.readsOf basis O Squeeze.gamma)
        (fam.readsOf basis O Squeeze.alpha) (fam.readsOf basis O Squeeze.zeta)
        (fam.readsOf basis O Squeeze.polyscale) (fam.readsOf basis O Squeeze.evalscale),
    Bulletproof.combineCommitments_eq hsmul, Bulletproof.combineCommitments_eq hsmul,
    ← hsmul, hzM, hzN]
  congr 1
  · rw [combinedCommitment, Finset.smul_sum]
    have hmapsz : ((((fam.cvk basis).sigmaComm[6]).map
        (fun P => (pScalarWith (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O)
          (fam.readsOf basis O Squeeze.beta) (fam.readsOf basis O Squeeze.gamma)
          (fam.readsOf basis O Squeeze.alpha)
          (fam.readsOf basis O Squeeze.zeta)).val • P)).toArray).size = nc := by
      simp
    refine Fintype.sum_equiv (finCongr hmapsz) _ _ fun i => ?_
    simp only [finCongr_apply, Fin.val_cast, Fin.getElem_fin, Vector.getElem_toArray,
      Vector.getElem_map]
    rw [← hsmul, ← mul_smul, ← mul_smul, mul_comm]
    exact congrArg _ (hs6 ⟨(i : ℕ), by simpa using i.isLt⟩)

/-! ### The two break selectors the extractor branches on

The extractor may not assume the group-side halves of key-honesty: at an arbitrary
`(basis, O)` they are consequences of the family's `hvk` and the flat-stream layout, but the
public row's case additionally needs the run's acceptance, so they are not available inside a
`def`. The selectors below therefore ask for *both* halves at once — a row is `Broken` when the
run's claim really does carry the honest chunk commitment there **and** the family's declared
coefficient vector is not the honest window — and the extractor branches on that. A left
payload consequently certifies "no row is broken", from which a consumer holding the group-side
facts recovers key-honesty outright (`vkRepHonest_of_no_break`). -/

/-- A verifying-key row at which the family's declaration is both refutable (the group-side
half holds there) and refuted (the coefficient vector is not the honest window). -/
private def VkBroken (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (rc : VkRow × Fin nc) : Prop :=
  ((fam.claim basis O).commitmentFn (streamPos nc rc.1.batchRow rc.2)
      = commit (srsOfBasis k basis)
          (chunkCoeffs (2 ^ k) (vkRowPoly fam.idx (fam.pub basis) rc.1) (rc.2 : ℕ))
          (vkRowBlinder rc.1))
    ∧ fam.aRef basis O (streamPos nc rc.1.batchRow rc.2)
        ≠ chunkCoeffs (2 ^ k) (vkRowPoly fam.idx (fam.pub basis) rc.1) (rc.2 : ℕ)

/-- The verifying-key break the extractor emits: the computed difference relation at *a*
broken row, or `none` when no row is broken. `noncomputable` because the honest chunk window
is defined by Lagrange interpolation; the choice of row is over the finite type
`VkRow × Fin nc`. -/
private noncomputable def vkBreak (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) :
    Option (Zcash.Snark.AlgebraicRelationWitness (F := C.ScalarField)
      (Zcash.Snark.augmentedBasis (fam.runSrs basis O).g (fam.runSrs basis O).U
        (fam.runSrs basis O).h)) :=
  letI : Decidable (∃ rc, fam.VkBroken basis O rc) := Classical.propDecidable _
  if h : ∃ rc, fam.VkBroken basis O rc then
    some (fam.vkRelation basis O h.choose.1 h.choose.2 h.choose_spec.1 h.choose_spec.2)
  else none

/-- The `ft`-row analogue of `VkBroken`. -/
private def FtBroken (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    Prop :=
  fam.FtCommHonest basis O ∧ fam.aRef basis O (ftPos nc) ≠ fam.ftHonestCoeffs basis O

/-- The `ft`-row break the extractor emits, the twin of `vkBreak`. -/
private noncomputable def ftBreak (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) :
    Option (Zcash.Snark.AlgebraicRelationWitness (F := C.ScalarField)
      (Zcash.Snark.augmentedBasis (fam.runSrs basis O).g (fam.runSrs basis O).U
        (fam.runSrs basis O).h)) :=
  letI : Decidable (fam.FtBroken basis O) := Classical.propDecidable _
  if h : fam.FtBroken basis O then some (fam.ftRelation basis O h.1 h.2) else none

/-- **A no-break verdict plus the group-side facts *is* key-honesty** — the direction the arm-(4)
consumer needs. `vkBreak = none` says no row is *both* group-honest and rep-dishonest; supply
group-honesty at every row (`VkCommHonest`, a consequence of `hvk` and the layout) and
rep-honesty at every row follows. -/
private theorem vkRepHonest_of_no_break (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) (hcomm : fam.VkCommHonest basis O)
    (h : fam.vkBreak basis O = none) : fam.VkRepHonest basis O := by
  intro r c
  by_contra hne
  have hex : ∃ rc, fam.VkBroken basis O rc := ⟨(r, c), hcomm r c, hne⟩
  rw [vkBreak, dif_pos hex] at h
  exact absurd h (by simp)

/-- The `ft`-row twin of `vkRepHonest_of_no_break`. -/
private theorem ftRepHonest_of_no_break (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k)
    (hcomm : fam.FtCommHonest basis O)
    (h : fam.ftBreak basis O = none) : fam.FtRepHonest basis O := by
  by_contra hne
  rw [ftBreak, dif_pos (show fam.FtBroken basis O from ⟨hcomm, hne⟩)] at h
  exact absurd h (by simp)

end KimchiFamily

end VkChannel

namespace KimchiFamily

variable {nc k n : ℕ} [NeZero n] (fam : KimchiFamily C nc k n)

/-! ### The extractor -/

/-- **The IPA forking extraction inside the kimchi transcript**, at the run's own claim. -/
private def ipaAttempt (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    Option (OpeningOrBreak (fam.runSrs basis O)
      (combinedCommitment (fam.claim basis O).polyscale (fam.claim basis O).commitmentFn)
      (combinedEvalVector (2 ^ k) (fam.claim basis O).evalscale (fam.claim basis O).pointFn)
      (Ipa.cipOf (fam.claim basis O))) :=
  kimchiIpaExtract (fam.runSrs basis O) (fam.digest basis) (fam.publicComm basis)
    (combinedEvalVector (2 ^ k) (fam.claim basis O).evalscale (fam.claim basis O).pointFn)
    (Ipa.cipOf (fam.claim basis O))
    (combinedCommitment (fam.claim basis O).polyscale (fam.claim basis O).commitmentFn)
    (fam.pgOf basis O) (fam.pwOf basis O) (fam.hPOf basis O)
    (fam.adversary basis) O coins

/-- **The key break**: the computed discrete-log relation the family's own declaration yields
when it is not the presented circuit's — the verifying-key relation if some key row is broken,
otherwise the `ft` relation if that row is, otherwise nothing.

`Option.orElse` and not a disjunction because the extractor must *emit* the witness. -/
private noncomputable def keyBreak (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) :
    Option (Zcash.Snark.AlgebraicRelationWitness (F := C.ScalarField)
      (Zcash.Snark.augmentedBasis (fam.runSrs basis O).g (fam.runSrs basis O).U
        (fam.runSrs basis O).h)) :=
  (fam.vkBreak basis O).orElse fun _ => fam.ftBreak basis O

/-- No key break means neither channel fired — the form the honesty recovery consumes. -/
private theorem keyBreak_eq_none_iff (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) :
    fam.keyBreak basis O = none ↔
      fam.vkBreak basis O = none ∧ fam.ftBreak basis O = none := by
  unfold keyBreak
  cases fam.vkBreak basis O <;> simp [Option.orElse]

/-- **The extractor, key-gated.** Total and data-valued on the left: an accepted IPA opening of
the run's combined commitment certifies the family's own AGM representation, which *is* the
extracted witness in the algebraic group model — *provided* that representation really is the
presented circuit's at the verifying-key rows and at the derived `ft` row. Where it is not, the
family has itself handed us a discrete-log relation among the sampled generators (`keyBreak`),
and the extractor returns *that* instead, on the break branch; a break coming up from the IPA
layer is passed through as before.

The gate moves the measured event in the sanctioned direction and only in that direction:
`ExtractsWitness` demands a *left* payload, so replacing a left payload by a right one can only
grow `¬ ExtractsWitness`. `Wins` does not mention the extractor; `attempt … = none` still holds
exactly when the IPA layer returned nothing, so arm (1) is untouched; and the emitted relations
have coefficient `0` at the transcript-derived base, so they flow into the `ε`-priced
arm (2) and not into the residual.

`noncomputable` because the honest chunk window is defined by Lagrange interpolation. That is a
status change with no mathematical content: the layer whose computability CI checks is the IPA
opening extractor underneath, which is untouched.

Nothing here is a `Prop`. That is deliberate: every proof obligation lives in the measured
event below, so no unfinished proof can make the endpoint trivially true — it can only
enlarge the failure set. -/
noncomputable def attempt (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    Option ((Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ k) → C.ScalarField) ⊕'
      Zcash.Snark.AlgebraicRelationWitness (F := C.ScalarField)
        (Zcash.Snark.augmentedBasis (fam.runSrs basis O).g (fam.runSrs basis O).U
          (fam.runSrs basis O).h)) :=
  match fam.ipaAttempt basis O coins with
  | none => none
  | some (PSum.inr rel) => some (PSum.inr rel)
  | some (PSum.inl _) =>
      match fam.keyBreak basis O with
      | some rel => some (PSum.inr rel)
      | none => some (PSum.inl (fam.aRef basis O))

/-- **The extractor produced a satisfying witness** — the analogue of `HasOpening`, with the
semantic content stated here rather than smuggled into the returned type: the returned
coefficient table, assembled by `runWTab`, satisfies the circuit the key corresponds to. -/
def ExtractsWitness (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) : Prop :=
  ∃ a, fam.attempt basis O coins = some (PSum.inl a) ∧
    Satisfies fam.idx (pubView fam.idx (fam.pub basis))
      (runWTab (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
        fam.idx a)

/-! ### The discrete-log charge -/

/-- **The break branch as a relation finder over the setup-only basis** — the copy of
`Bulletproof.Ipa.Forking.relationFinder` at `fam.attempt`. `noncomputable` only because the
key-gated `attempt` is. -/
noncomputable def relationFinder (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    (bs : SetupIndex (2 ^ k) → C.Point) → Coins C nc k →
      Option (Zcash.Snark.AlgebraicRelationWitness (F := C.ScalarField) bs) :=
  fun bs O =>
    match fam.attempt (augOfSetup bs) O coins with
    | none => none
    | some (PSum.inl _) => none
    | some (PSum.inr rel) =>
        if hu : rel.coeffs Zcash.Snark.AugmentedIndex.u = 0 then
          some (setupBasis_srsOfBasis_augOfSetup_override bs
            (fam.warmBase (augOfSetup bs) O) ▸ restrictToSetup rel hu)
        else none

/-- **The residual**: a break that touches the transcript-derived base computes its discrete
log. The copy of `Bulletproof.Ipa.Forking.derivedULog`. `noncomputable` only because the
key-gated `attempt` is.

The base whose discrete log is computed is the WARM one, `fam.warmBase … O`, matching the base
the game is now played at; the body is base-agnostic and carries over unchanged. So
`DerivedUDLAdvantageLE` below, and with it `DiscreteLogRelationHardFor`, prices breaks that
touch the warm post-`ζ` base rather than the cold `uBaseOf` one. The endpoint text is unchanged;
what it assumes hard is the point the deployed verifier actually uses. -/
noncomputable def derivedULog (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (s : SetupIndex (2 ^ k) → C.ScalarField) (O : Coins C nc k) :
    Option (Zcash.Snark.DiscreteLogRepresentation (F := C.ScalarField) B
      (fam.warmBase (augOfSetup (Zcash.Snark.scalarBasis B s)) O)) :=
  match fam.attempt (augOfSetup (Zcash.Snark.scalarBasis B s)) O coins with
  | none => none
  | some (PSum.inl _) => none
  | some (PSum.inr rel) =>
      if hu : rel.coeffs Zcash.Snark.AugmentedIndex.u = 0 then none
      else
        some (Zcash.Snark.discreteLogOfBasis_of_relation B _
          (Zcash.Snark.augmentedCoeffs (fun i => s (SetupIndex.gen i)) 0 (s SetupIndex.blind))
          Zcash.Snark.AugmentedIndex.u rel
          (by
            rintro (i | j) hi
            · rfl
            · fin_cases j
              · exact absurd rfl hi
              · rfl)
          hu)

/-- **The derived-`U` discrete-log assumption** — the residual's price, stated openly. -/
def DerivedUDLAdvantageLE (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) (bound : ℝ≥0∞) : Prop :=
  (PMF.uniformOfFintype ((SetupIndex (2 ^ k) → C.ScalarField) × Coins _ nc k)).toOuterMeasure
      {q | (fam.derivedULog B coins q.1 q.2).isSome} ≤ bound

/-- **The extractor's call count** — the analogue of `DeployedFamily.attemptRuns`. -/
def attemptRuns (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) : ℕ :=
  Bulletproof.Forking.kimchiExtractRuns (fam.runSrs basis O)
    (combinedEvalVector (2 ^ k) (fam.claim basis O).evalscale (fam.claim basis O).pointFn)
    (Ipa.cipOf (fam.claim basis O))
    (combinedCommitment (fam.claim basis O).polyscale (fam.claim basis O).commitmentFn)
    (expandPre C) (fam.adversary basis)
    (fun cp => Bulletproof.Ipa.Forking.toOpening cp.opening)
    (ipaPrefixes (fam.runSrs basis O) (fam.digest basis) (fam.publicComm basis))
    (kimchiDecodesFromPrefixes (fam.runSrs basis O) (fam.digest basis) (fam.publicComm basis))
    O coins

/-- **The extractor makes at most `R` calls on average** — the analogue of
`DeployedFamily.ReductionEfficient`. -/
def ReductionEfficient (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (R : ℕ) : Prop :=
  ∀ basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point,
    ∑ O : Coins C nc k, fam.attemptRuns basis O coins ≤ R * Fintype.card (Coins C nc k)

/-- **Discrete log is hard for this family against `R`-call reductions** — the analogue of
`DeployedFamily.DiscreteLogRelationHardFor`, and what pins `ε` and `δ`. `ε` is a genuine
reduction to textbook discrete log; `δ` is the residual event's own measure, which is why the
two are named separately. -/
def DiscreteLogRelationHardFor (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) (R : ℕ) (ε δ : ℝ≥0∞) : Prop :=
  fam.ReductionEfficient coins R →
    Zcash.Snark.TextbookDLWithCoinsAdvantageLE B (fam.relationFinder coins) ε ∧
      fam.DerivedUDLAdvantageLE B coins δ

end KimchiFamily

end Game

/-! ## 4. The Schwartz–Zippel budget

Not a free parameter: the number of 128-bit prechallenges that can put one of the run's own
six field challenges inside an exclusion set. `β`, `γ` cost `7·(n − zkRows)` each
(`RunBounds`), `α` costs `n·(gateAlphaCount + permAlphaCount − 1)`, `ζ` costs
`degreeBound n` plus the two boundary points `1` and `ω^(n−zkRows)`, and the fr-side `ξ`, `r`
cost `card_badXiOf_le ≤ 2·(m − 1)` and `card_badROf_le ≤ 1` at
`m = nc + 1 + tailRowCount·nc`. Each challenge is an injective expansion of a uniform
prechallenge, so a bad set of size `c` is hit with probability at most `c / 2¹²⁸` — for a
challenge fixed in advance. These exclusion sets are NOT fixed in advance: they are functions
of the adversary's own `aRef`, and the challenge is read at the run's own node, so the event is
adaptive and carries a query factor. Ironwood charges `(Q + 1)/|F|` for a bad set of size ONE
of exactly this shape (`fsAdvantageFull_zero_slice_le`, `Forking/Adversary/Adaptive.lean:37`:
"the extra query reads that challenge from the output's own prefix"), which is the same reason
the query-loss summand carries `(Q + k + 1)`. The budget is therefore charged at `(Q + 1)`
per unit. -/

/-- The Schwartz–Zippel budget of a run: the total exclusion-set cardinality. -/
def szBudget (nc n zkRows : ℕ) : ℕ :=
  2 * (7 * (n - zkRows))
    + n * (Index.gateAlphaCount + Index.permAlphaCount - 1)
    + Index.degreeBound n + 2
    + 2 * (nc + 1 + tailRowCount * nc - 1) + 1

/-- **The `ζ` boundary exclusion set**: the two points `RunGuardImpAt` excludes on top of the
Schwartz–Zippel set `Protocol.soundBadZ` — the vanishing point `1` of the domain polynomial and
the zero-knowledge boundary `ω^(n − zkRows)`. They are the `+ 2` of `szBudget`.

The easiest case of node-determinacy, and the reason it is worth naming: this set
reads neither the family's AGM representations, nor the run's commitments, nor any earlier
challenge — it is a function of the circuit alone. So it is a *constant* function of the node
at which `ζ` is read, hence trivially blind there, and the adaptive Schwartz–Zippel charge
applies to it with no faithfulness hypothesis at all. -/
private def zetaBoundaryBad {n : ℕ} (idx : Index C.ScalarField n) :
    Finset C.ScalarField :=
  {1, idx.omega ^ (n - idx.zkRows)}

/-- Avoiding the boundary set *is* `RunGuardImpAt`'s two `ζ` side conditions. -/
private theorem not_mem_zetaBoundaryBad_iff {n : ℕ} (idx : Index C.ScalarField n)
    (z : C.ScalarField) :
    z ∉ zetaBoundaryBad idx ↔ z ≠ 1 ∧ z ≠ idx.omega ^ (n - idx.zkRows) := by
  simp [zetaBoundaryBad, not_or]

/-- The boundary set costs at most the `2` `szBudget` allots it. -/
private theorem card_zetaBoundaryBad_le {n : ℕ} (idx : Index C.ScalarField n) :
    (zetaBoundaryBad idx).card ≤ 2 := by
  refine le_trans (Finset.card_insert_le _ _) ?_
  simp

/-! ## 5. THE TOP-LEVEL STATEMENT, per curve

The two endpoints — `vesta_kimchi_knowledge_sound` and `pallas_kimchi_knowledge_sound` — are
stated and proved at the END of this file (section 17), after the machinery their proofs
consume: the four-way cover (section 9), the presence summand (section 15) and the algebraic
summand (section 16). Their statements are unchanged; what changed in moving them is that they
are theorems rather than open goals. -/

/-! ## 6. THE ACCEPTANCE TEST — per-curve instantiation

A statement generic in the curve, whose hypotheses are never discharged and which has no
per-curve corollary, is the shape that concealed `hU` in
`Bulletproof/Forking/KnowledgeSoundness.lean`: the proof was correct and the hypothesis had no
witnesses at either deployed curve, so the theorem had no instances. Nothing here is promoted
until it instantiates.

These are `example`s rather than named results: they exist to make the elaborator confirm that
every instance resolves at the real curves, not to be consumed. -/

section PerCurve

open Bulletproof

/-- Vesta: the challenge-generic verifier instantiates at the deployed curve. -/
example {nc : ℕ} (σ : SRS IpaVesta.Point) (cvk : KimchiVK IpaVesta.curve nc)
    (cp : KimchiProof IpaVesta.curve nc σ.k) (pub : Array IpaVesta.curve.ScalarField)
    (beta gamma alpha zeta v u : IpaVesta.curve.ScalarField) (uBase : IpaVesta.Point)
    (chals : Vector IpaVesta.curve.ScalarField σ.k) (c : IpaVesta.curve.ScalarField) : Bool :=
  kimchiVerifyWith σ cvk cp pub beta gamma alpha zeta v u uBase chals c

/-- Vesta: the oracle domain is a `Fintype` at the deployed curve, so
`PMF.uniformOfFintype` over its tables exists — the measure the statement is stated against. -/
example (nc k : ℕ) : Fintype (KimchiNode IpaVesta.curve nc k) := inferInstance

/-- Pallas: likewise. -/
example (nc k : ℕ) : Fintype (KimchiNode IpaPallas.curve nc k) := inferInstance

/-- Vesta: the extractor is a total function at the deployed curve, and its left payload is
data — the property that keeps an unfinished proof from making the bound free. `noncomputable`
since the key gate reads the Lagrange-interpolated honest chunk windows; the layer whose
computability CI checks is the IPA opening extractor underneath. -/
noncomputable example {nc k n : ℕ} [NeZero n] (fam : KimchiFamily IpaVesta.curve nc k n)
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → IpaVesta.Point) (O : Coins IpaVesta.curve nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    Option ((Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ k) → IpaVesta.curve.ScalarField) ⊕'
      Zcash.Snark.AlgebraicRelationWitness (F := IpaVesta.curve.ScalarField)
        (Zcash.Snark.augmentedBasis (fam.runSrs basis O).g (fam.runSrs basis O).U
          (fam.runSrs basis O).h)) :=
  fam.attempt basis O coins

/-- Pallas: likewise. -/
noncomputable example {nc k n : ℕ} [NeZero n] (fam : KimchiFamily IpaPallas.curve nc k n)
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → IpaPallas.Point) (O : Coins IpaPallas.curve nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    Option ((Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ k) → IpaPallas.curve.ScalarField) ⊕'
      Zcash.Snark.AlgebraicRelationWitness (F := IpaPallas.curve.ScalarField)
        (Zcash.Snark.augmentedBasis (fam.runSrs basis O).g (fam.runSrs basis O).U
          (fam.runSrs basis O).h)) :=
  fam.attempt basis O coins

end PerCurve

/-! ## 7. What had to hold before this was worth proving

Both conditions are now met.

* **`kimchiDecodesFromPrefixes` had to be discharged**, since it returns data: leaving it open
  would have made `attempt`'s payload carry `sorryAx`. Commit-then-challenge is structurally
  true of the kimchi schedule, and the `Option`-gating exists to make it provable. It is
  discharged above.
* **Anti-vacuity.** The accepting set had to be shown non-empty, or the bound would be a
  statement about nothing. `Kimchi.Verifier.Forking.honestKimchiFamily_wins` and
  `honestKimchiFamily_failure_set` (`Forking/Honest.lean`) show it, and both are roots of
  `scripts/check_axioms.lean`.

What does **not** need to hold, and is settled in section 8 below: the worry that `attempt`
silently discards the comparison `a = fam.pgOf basis O` at a basis where binding is false. That
comparison is made one layer down, inside ironwood's `deployed_forking_tree`, and the
extraction chain surfaces it.
-/

/-! ## 8. The comparison the extractor does *not* discard

`attempt` (above) reads, on its un-broken left branch,
`| none => some (PSum.inl (fam.aRef basis O))`: it drops the opening `(a, ρ)` the forking
extraction returned and hands back the family's own representation table. Read at that line
alone it looks as though the equality `a = fam.pgOf basis O` — the step
`eval_pins_of_opening` (`Verifier/Capstone/Algebraic.lean`) spends its `hbind` on — is neither
tested nor charged, and since the basis this game samples is `augOfSetup (scalarBasis B s)`,
where every generator is a multiple of `B`, `hbind` is not available to supply it (see
`exists_ne_zero_kernel_scalarBasis` at the end of this section, which refutes it outright).

**It is tested — one layer down.** Ironwood's `deployed_forking_tree`
(ironwood's `Forking/Extractor.lean:179`) returns its left branch only through

```
if hcoord : a = aDep ∧ (z * v) = (z * vDep) ∧ blind = blindDep then PSum.inl … else PSum.inr …
```

with `aDep`/`blindDep` the AGM representation handed in — here `fam.pgOf`/`fam.pwOf`. A returned
opening whose coefficients differ from the presented representation is emitted as a
`NontrivialRelation`, i.e. as a break, which `relationFinder`/`derivedULog` then charge to `ε`
or `δ`. So the `inl` branch is *only* reachable when the discarded opening is exactly
`(fam.pgOf basis O, fam.pwOf basis O)`, and discarding it loses nothing.

That is what this section proves, bottom up: `deployed_forking_tree` (private), then
`kimchiOpeningOrBreak`, `kimchiExtract`, `ipaAttempt`, and finally `attempt` itself. The
headline is the pinning corollary `attempt_inl_pins`: whenever the extractor returns a
left payload, the polyscale combination of the family's own `aRef`/`ρRef` is an accepted opening
of the run's combined commitment — which is precisely `eval_pins_of_opening`'s Step B, delivered
**without binding**. The two `_eq_none_of_attempt_inl` results record the other half of the
accounting: on that branch neither discrete-log finder fires, so nothing there is double
charged.

Everything here is about *existing* definitions; nothing in `attempt`, `Wins` or
`ExtractsWitness` is touched. -/

section DiscardedComparison

variable [Module C.ScalarField C.Point]
variable {F G' : Type*} [Field F] [AddCommGroup G'] [Module F G']

/-- The coefficient vector `ipa_extractV` computes is a function of `(g, b, t)` alone: the
commitment `P` and the value `v` it is checked against enter only through the accept proof, and
proofs are irrelevant. Needed because `kimchiOpeningOrBreak` re-extracts from the tree that
`deployed_forking_tree` already extracted from, at a propositionally — not syntactically — equal
`(P, v)`. -/
private theorem ipa_extractV_fst_congr {d : ℕ} (g : Fin (2 ^ d) → G') (b : Fin (2 ^ d) → F)
    {P P' : G'} {v v' : F} (t : Zcash.Snark.IpaTreeV F G' d)
    (h : Zcash.Snark.IpaAcceptV g b P v t) (h' : Zcash.Snark.IpaAcceptV g b P' v' t)
    (hP : P = P') (hv : v = v') :
    (Zcash.Snark.ipa_extractV g b P v t h).1
      = (Zcash.Snark.ipa_extractV g b P' v' t h').1 := by
  subst hP; subst hv; rfl

/-- **The left branch of `deployed_forking_tree` pins the extracted coefficients.** If the
forking tree resolves to an accepting deployed tree rather than to a relation, then the
coefficient vector recovered from that tree is *the presented representation* `aDep` — this is
the `hcoord` test in the definition's body, exposed. Its statement's `hcl` is the clean-accept
proof the caller re-derives; by `ipa_extractV_fst_congr` the choice of proof is immaterial. -/
private theorem deployed_forking_tree_inl_fst [DecidableEq F] [DecidableEq G'] {U W : G'} {z : F}
    (hz : z ≠ 0) {d : ℕ} (g : Fin (2 ^ d) → G') (b : Fin (2 ^ d) → F) (aDep : Fin (2 ^ d) → F)
    (vDep blindDep : F) (cert : Zcash.Snark.DForkCert F G' d)
    (hv : Zcash.Snark.DeployedForkValid g b U W z
      (Zcash.Snark.commitGen g aDep + (z * vDep) • U + blindDep • W) cert)
    {y : Σ' (blind : F) (t : Zcash.Snark.DeployedIpaTreeV F G' d),
        Zcash.Snark.DeployedIpaAcceptV g b U W z (Zcash.Snark.commitGen g aDep) vDep blind t}
    (h : Zcash.Snark.deployed_forking_tree hz g b aDep vDep blindDep cert hv = PSum.inl y)
    (hcl : Zcash.Snark.IpaAcceptV g b (Zcash.Snark.commitGen g aDep) vDep
      (Zcash.Snark.projTree y.2.1)) :
    (Zcash.Snark.ipa_extractV g b (Zcash.Snark.commitGen g aDep) vDep
      (Zcash.Snark.projTree y.2.1) hcl).1 = aDep := by
  unfold Zcash.Snark.deployed_forking_tree at h
  split at h
  rename_i x P v blind t ha hw heq
  split at h
  · rename_i hclean
    split at h
    · rename_i a hPa hva heq2
      split at h
      · rename_i hcoord
        injection h with h'
        subst h'
        obtain ⟨hac, hvc, -⟩ := hcoord
        have hP : Zcash.Snark.commitGen g aDep = P := by rw [← hac, hPa]
        have hvv : vDep = v := (mul_left_cancel₀ hz hvc).symm
        have hcong := ipa_extractV_fst_congr g b (Zcash.Snark.projTree t) hcl hclean hP hvv
        refine hcong.trans ?_
        rw [heq2]
        exact hac
      · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **The opening `kimchiOpeningOrBreak` returns is the presented AGM representation.** Both
components: the coefficient vector is `pg` and the blinder is `pw`. The blinder is immediate
from the definition (`.inl ⟨a, pw, _⟩`); the coefficient vector is
`deployed_forking_tree_inl_fst` transported through the second extraction. -/
private theorem kimchiOpeningOrBreak_inl_fst [DecidableEq F] [DecidableEq G'] (σ : SRS G')
    (b : Fin (2 ^ σ.k) → F) (v : F) (P : G')
    (pg : Fin (2 ^ σ.k) → F) (pw : F) (hP : P = commitGen σ.g pg + pw • σ.h)
    (cert : KimchiForkCert F G' σ.k) (hv : KimchiForkValid σ.U σ.h v σ.g b P cert)
    {x : Σ' (a : Fin (2 ^ σ.k) → F) (ρ : F), openingRelationB σ P b v a ρ}
    (h : kimchiOpeningOrBreak σ b v P pg pw hP cert hv = PSum.inl x) :
    x.1 = pg ∧ x.2.1 = pw := by
  unfold kimchiOpeningOrBreak at h
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · rename_i _ blind t hacc heq
    split at h
    · exact absurd h (by simp)
    · rename_i hclean _
      have key : (Zcash.Snark.ipa_extractV σ.g b (Zcash.Snark.commitGen σ.g pg) v
          (Zcash.Snark.projTree t) hclean).1 = pg :=
        deployed_forking_tree_inl_fst one_ne_zero σ.g b pg v pw cert.toDFork _ heq hclean
      split at h
      rename_i a hPa hva heq2
      injection h with h'
      subst h'
      refine ⟨?_, rfl⟩
      show a = pg
      rw [← key, heq2]

/-- **The extraction game's left payload is the presented AGM representation.** The same
statement one layer up: `kimchiExtract` only wraps `kimchiOpeningOrBreak` in the fork's
`Option`/validity guard, neither of which touches `(pg, pw)`. -/
private theorem kimchiExtract_inl_fst {T Pre Pf : Type*} [DecidableEq F] [DecidableEq G']
    [DecidableEq T] [Zero Pre] [DecidableEq Pre]
    (σ : SRS G') (b : Fin (2 ^ σ.k) → F) (v : F) (P : G')
    (pg : Fin (2 ^ σ.k) → F) (pw : F) (hP : P = commitGen σ.g pg + pw • σ.h)
    (expand : Pre → F) (A : Zcash.Snark.OracleComp T Pre Pf)
    (proofOf : Pf → OpeningProof F G' σ.k) (prefixes : Pf → Fin (σ.k + 1) → T)
    (dec : DecodesFromPrefixes σ proofOf prefixes)
    (O : T → Pre) (coins : Zcash.Snark.RecursiveForkCoins Pre (σ.k + 1))
    {x : Σ' (a : Fin (2 ^ σ.k) → F) (ρ : F), openingRelationB σ P b v a ρ}
    (h : kimchiExtract σ b v P pg pw hP expand A proofOf prefixes dec O coins
        = some (PSum.inl x)) :
    x.1 = pg ∧ x.2.1 = pw := by
  unfold kimchiExtract at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact kimchiOpeningOrBreak_inl_fst σ b v P pg pw hP _ _ (Option.some.inj h)
    · exact absurd h (by simp)

namespace KimchiFamily

variable {nc k n : ℕ} [NeZero n] (fam : KimchiFamily C nc k n)

/-- **The kimchi-transcript extraction returns the family's own combination.** `ipaAttempt` is
`kimchiExtract` at `(fam.pgOf basis O, fam.pwOf basis O)`, so its left payload is that pair. -/
private theorem ipaAttempt_inl_fst
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (x : Σ' (a : Fin (2 ^ k) → C.ScalarField) (ρ : C.ScalarField),
      openingRelationB (fam.runSrs basis O)
        (combinedCommitment (fam.claim basis O).polyscale (fam.claim basis O).commitmentFn)
        (combinedEvalVector (2 ^ k) (fam.claim basis O).evalscale (fam.claim basis O).pointFn)
        (Ipa.cipOf (fam.claim basis O)) a ρ)
    (h : fam.ipaAttempt basis O coins = some (PSum.inl x)) :
    x.1 = fam.pgOf basis O ∧ x.2.1 = fam.pwOf basis O := by
  unfold KimchiFamily.ipaAttempt kimchiIpaExtract at h
  exact kimchiExtract_inl_fst _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

/-- **The discarded comparison holds anyway.** When `attempt` returns a left payload it is the
family's representation table `aRef` (definitional), and — the content — the polyscale
combination `(pgOf, pwOf)` of that table satisfies the opening relation for the run's combined
commitment. This is the hypothesis `eval_pins_of_opening` derives from `hbind` at its Step B,
here supplied by the extractor's own coefficient test instead. -/
private theorem attempt_inl_pins
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (a : Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ k) → C.ScalarField)
    (h : fam.attempt basis O coins = some (PSum.inl a)) :
    a = fam.aRef basis O ∧
      openingRelationB (fam.runSrs basis O)
        (combinedCommitment (fam.claim basis O).polyscale (fam.claim basis O).commitmentFn)
        (combinedEvalVector (2 ^ k) (fam.claim basis O).evalscale (fam.claim basis O).pointFn)
        (Ipa.cipOf (fam.claim basis O)) (fam.pgOf basis O) (fam.pwOf basis O) := by
  unfold KimchiFamily.attempt at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · rename_i x heq
    obtain ⟨hg, hw⟩ := fam.ipaAttempt_inl_fst basis O coins x heq
    split at h
    · exact absurd h (by simp)
    · exact ⟨by simpa using h.symm, hg ▸ hw ▸ x.2.2⟩

/-- **A left payload certifies that neither break channel fired.** The definitional half of the
gate: the extractor reaches `PSum.inl` only through the `keyBreak = none` branch. -/
private theorem attempt_inl_noBreak
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (a : Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ k) → C.ScalarField)
    (h : fam.attempt basis O coins = some (PSum.inl a)) :
    fam.vkBreak basis O = none ∧ fam.ftBreak basis O = none := by
  rw [← fam.keyBreak_eq_none_iff]
  unfold KimchiFamily.attempt at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · assumption

/-- **A left payload certifies key-honesty**. This is the one
new fact the arm-(4) split needs, and the reason the four-way cover no longer has to carry
key-honesty as an added conjunct: under the gated extractor, arm (4) *implies* it.

The two group-side halves are hypotheses here for the reason recorded in the break-selector
preamble — they are consequences of the family's `hvk` and the flat-stream layout, but the
public row's case additionally needs the run's acceptance, so a consumer that has `Wins` in
hand supplies them; the extractor itself may not. -/
private theorem attempt_inl_keyHonest
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (a : Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ k) → C.ScalarField)
    (h : fam.attempt basis O coins = some (PSum.inl a))
    (hvkc : fam.VkCommHonest basis O) (hftc : fam.FtCommHonest basis O) :
    fam.VkRepHonest basis O ∧ fam.FtRepHonest basis O := by
  obtain ⟨hv, hf⟩ := fam.attempt_inl_noBreak basis O coins a h
  exact ⟨fam.vkRepHonest_of_no_break basis O hvkc hv,
    fam.ftRepHonest_of_no_break basis O hftc hf⟩

/-- **A left payload on a winning run certifies key-honesty, outright** — the packaged form of
`attempt_inl_keyHonest`, with both group-side halves discharged: `vkCommHonest_of_wins` from the
family's `hvk`, `hpub` and the run's own acceptance, and `ftCommHonest` from `hvk` and `hn`.
Only the curve-specific `.val`-scalar collapse remains a parameter. -/
private theorem attempt_inl_keyHonest_of_wins
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (a : Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ k) → C.ScalarField)
    (h : fam.attempt basis O coins = some (PSum.inl a))
    (hsmul : ∀ (a : C.ScalarField) (P : C.Point), a • P = a.val • P)
    (hwin : fam.Wins basis O) :
    fam.VkRepHonest basis O ∧ fam.FtRepHonest basis O :=
  fam.attempt_inl_keyHonest basis O coins a h (fam.vkCommHonest_of_wins basis O hsmul hwin)
    (fam.ftCommHonest basis O hsmul)

/-- `pgOf` written as a `Pi`-level ξ-combination, the shape `eval_pins_of_opening`'s
`∑ i, ξ ^ i • aw₀ i` uses. Pointwise the two differ only by `Finset.sum_apply`. -/
private theorem pgOf_eq_sum_smul (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) :
    fam.pgOf basis O
      = ∑ i : Fin (nc + 1 + tailRowCount * nc),
          (fam.claim basis O).polyscale ^ (i : ℕ) • fam.aRef basis O i := by
  funext j
  simp [KimchiFamily.pgOf, Finset.sum_apply]

end KimchiFamily

/-! ### Anti-vacuity of the left branch

`kimchiOpeningOrBreak_inl_fst` would be true of an unreachable branch, so it is worth recording
that the branch is reached. The witness is not carried here — kernel reduction of
`kimchiOpeningOrBreak` at a `ZMod 7` fixture gets stuck (the `Decidable` instance behind
`hcoord` does not reduce), which is exactly why the existing check `#eval`s instead. The
executable witness lives in `bulletproof-pcs/scripts/check_extractor_computes.lean` (case (3)):
at `σ = ⟨0, ![3], 5, 2⟩`, `pg = ![4]`, `pw = 1` and the honest depth-0 Schnorr fork, the
extractor returns `PSum.inl` with payload `(4, 1)` — the presented representation, as the
theorem above says it must be. `bulletproof-pcs/scripts/check_extractor_computes.sh` is
CI-wired. -/


/-- **Every commitment at the sampled basis is a multiple of the one point `B`.** At
`augOfSetup (scalarBasis B s)` generator `i` is `s (gen i) • B`, so the commitment map collapses
to the linear functional `d ↦ ∑ i, d i * s (gen i)` followed by `· • B`. -/
private theorem commitGen_srsOfBasis_scalarBasis {k : ℕ} (B : C.Point)
    (s : SetupIndex (2 ^ k) → C.ScalarField) (d : Fin (2 ^ k) → C.ScalarField) :
    commitGen (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B s))).g d
      = (∑ i, d i * s (SetupIndex.gen i)) • B := by
  simp only [commitGen, Finset.sum_smul, mul_smul]
  rfl

/-- A linear functional on `Fin m → F` with `m ≥ 2` has a nonzero kernel vector, by hand: the
antisymmetric combination of two coordinates, or a single coordinate when the first vanishes. -/
private lemma exists_ne_zero_sum_mul_eq_zero {m : ℕ} (hm : 2 ≤ m) (c : Fin m → F) :
    ∃ d : Fin m → F, d ≠ 0 ∧ ∑ i, d i * c i = 0 := by
  have h0 : (0 : ℕ) < m := by omega
  have h1 : (1 : ℕ) < m := by omega
  set i0 : Fin m := ⟨0, h0⟩ with hi0
  set i1 : Fin m := ⟨1, h1⟩ with hi1
  have hne : i1 ≠ i0 := by simp [hi0, hi1, Fin.ext_iff]
  have hsum : ∀ (j : Fin m) (t : F), ∑ i, (if i = j then t else 0) * c i = t * c j := by
    intro j t
    simp [ite_mul, Finset.sum_ite_eq']
  by_cases hc : c i0 = 0
  · refine ⟨fun i => if i = i0 then 1 else 0, ?_, ?_⟩
    · intro hd
      have := congrFun hd i0
      simp at this
    · rw [hsum i0 1, hc, mul_zero]
  · refine ⟨fun i => (if i = i0 then c i1 else 0) - (if i = i1 then c i0 else 0), ?_, ?_⟩
    · intro hd
      have := congrFun hd i1
      simp [hne, hc] at this
    · simp only [sub_mul, Finset.sum_sub_distrib, hsum]
      ring

/-- **The sampled basis is maximally non-binding.** At `augOfSetup (scalarBasis B s)` every
generator is a multiple of the single point `B`, so for `k ≥ 1` the commitment map has a
nonzero kernel vector: `hbind` is refutable there, exactly as this module's preamble says. -/
theorem exists_ne_zero_kernel_scalarBasis {k : ℕ} (hk : 1 ≤ k) (B : C.Point)
    (s : SetupIndex (2 ^ k) → C.ScalarField) :
    ∃ d : Fin (2 ^ k) → C.ScalarField, d ≠ 0 ∧
      commitGen (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B s))).g d = 0 := by
  have hm : 2 ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨d, hd, hsum⟩ := exists_ne_zero_sum_mul_eq_zero hm (fun i => s (SetupIndex.gen i))
  exact ⟨d, hd, by rw [commitGen_srsOfBasis_scalarBasis, hsum, zero_smul]⟩
end DiscardedComparison

/-! ## 9. The four-way cover, and the two discrete-log summands

`ExtractsWitness` can fail for exactly four reasons, and the endpoint's four summands charge
them one for one. This section carries the set-theoretic skeleton — a pure case analysis on
`attempt`'s return value, with no arithmetic anywhere in it — together with the two summands
that are available today: the relation set, priced by textbook discrete log through ironwood's
index-generic fixed-slot reduction, and the residual, priced by its own assumption.

It is the kimchi transcription of `Bulletproof.Ipa.Forking.three_way_cover`,
`relation_summand` and `residual_summand`, which the definitions of section 3 were written to
mirror. The one structural difference is the extra arm: the IPA's `HasOpening` asks only that
the extractor took the `PSum.inl` branch, so its `inl` case closes by `absurd`, whereas
`ExtractsWitness` additionally demands `Satisfies`, so a left payload whose assembled table
fails the circuit survives as arm (4).

Arms (2) and (3) are closed here, outright, as summands (II) and (III) of
`vesta_kimchi_knowledge_sound`. Arm (1) is closed in section 15 (the claim-adaptive
extraction game) and arm (4) in section 16 (the adaptive Schwartz–Zippel charge), so the cover's
four arms are now all priced. Arm (4) is disjoint from arms (2) and (3) — the relation
finder and the derived log return `none` whenever the attempt lands left — so nothing is
charged twice.

Arm (4) carries the win conjunct. `arm4_hits_badChallenge` needs it — key-honesty is a
consequence of the extractor's gate on *winning* runs only — and the cover has `hacc : Wins` in
hand at exactly that branch. Narrowing the arm leaves the measured event (the conclusion of
`wins_notExtracts_measure_le_of_arms`) untouched and makes its `hAlgebraic` hypothesis a bound
on a SMALLER set, so the corollary is strictly stronger, not weaker.
-/

section Cover

variable [Module C.ScalarField C.Point]
variable {nc k n : ℕ} [NeZero n] (fam : KimchiFamily C nc k n)

namespace KimchiFamily

/-- **Arm (1): accepting runs on which the extractor produced nothing at all.** The *presence*
failure — the branch `attempt … = none`, which says nothing about which `PSum` side a
successful run would have taken. The copy of
`Bulletproof.Ipa.Forking.DeployedFamily.acceptExtractionFailure`. -/
def acceptExtractionFailure (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) : Set (Coins C nc k) :=
  {O | fam.Wins basis O ∧ fam.attempt basis O coins = none}

/-- **Arm (3): the residual event** — the extractor returned a break *touching the
transcript-derived base* `U`. Such a break is not a relation among the sampled setup
generators, so the fixed-slot discrete-log reduction cannot see it; it is charged to `δ`
instead. The copy of `Bulletproof.Ipa.Forking.TouchesU` at `KimchiFamily.attempt`. -/
def TouchesU (bs : SetupIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) : Prop :=
  ∃ rel, fam.attempt (augOfSetup bs) O coins = some (PSum.inr rel) ∧
    rel.coeffs Zcash.Snark.AugmentedIndex.u ≠ 0

/-- **Arm (4): the extractor opened, but the assembled table does not satisfy the circuit.**
`ExtractsWitness` with its semantic conjunct negated. This is the arm with no counterpart on
the IPA side, whose `HasOpening` asks for the branch alone; it is where the algebraic
run-soundness root has to deliver. -/
private def OpenedUnsatisfying (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) : Prop :=
  ∃ a, fam.attempt basis O coins = some (PSum.inl a) ∧
    ¬ Satisfies fam.idx (pubView fam.idx (fam.pub basis))
      (runWTab (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
        fam.idx a)

/-- **Arm (4) carries key-honesty**. This is what the gated
extractor buys and what summand (IV) needs: at every point of the opened-but-unsatisfying arm
of a winning run, the family's verifying-key representations *are* the presented circuit's
honest chunk windows and its `ft` representation *is* the combination the verifier's own
construction forces — i.e. exactly `run_sound_algebraic_at_of_vkrep`'s four `h*Rep` hypotheses and
its `hftRep`.

The cover itself (`four_way_cover`) is unchanged: no extra conjunct was added to arm (4),
because under the gate the arm *implies* key-honesty rather than needing it assumed. -/
private theorem keyHonest_of_openedUnsatisfying
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hsmul : ∀ (a : C.ScalarField) (P : C.Point), a • P = a.val • P)
    (hwin : fam.Wins basis O) (h : fam.OpenedUnsatisfying basis O coins) :
    fam.VkRepHonest basis O ∧ fam.FtRepHonest basis O := by
  obtain ⟨a, ha, -⟩ := h
  exact fam.attempt_inl_keyHonest_of_wins basis O coins a ha hsmul hwin

/-- **The residual event is exactly the derived-base log finder's support.** Both sides match
on `attempt`: `none` and a left payload give `none`, and a break gives `some` precisely when its
`u` coefficient is nonzero. So `DerivedUDLAdvantageLE` bounds arm (3) and nothing else. The copy
of `Bulletproof.Ipa.Forking.derivedULog_isSome_iff`. -/
theorem derivedULog_isSome_iff (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (s : SetupIndex (2 ^ k) → C.ScalarField) (O : Coins C nc k) :
    (fam.derivedULog B coins s O).isSome ↔
      fam.TouchesU (Zcash.Snark.scalarBasis B s) O coins := by
  classical
  constructor
  · intro h
    by_cases hsome :
        (fam.attempt (augOfSetup (Zcash.Snark.scalarBasis B s)) O coins).isSome
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
      cases x with
      | inl o => simp [KimchiFamily.derivedULog, hx] at h
      | inr rel =>
        by_cases hu : rel.coeffs Zcash.Snark.AugmentedIndex.u = 0
        · simp [KimchiFamily.derivedULog, hx] at h
          exact absurd hu h
        · exact ⟨rel, hx, hu⟩
    · rw [Option.not_isSome_iff_eq_none] at hsome
      simp [KimchiFamily.derivedULog, hsome] at h
  · rintro ⟨rel, hx, hu⟩
    simp only [KimchiFamily.derivedULog, hx, dif_neg hu, Option.isSome_some]

/-- **The four-way cover.** A run that wins while the extractor fails to hand back a satisfying
witness fell into one of four arms: it produced nothing at all (arm (1), the presence rung); it
produced a relation among the sampled setup generators (arm (2), charged to `ε`); it produced a
break touching the transcript-derived base (arm (3), the residual, charged to `δ`); or it
produced a left payload whose assembled table fails the circuit (arm (4), the algebraic rung).

Pure case analysis on `attempt`'s return value — no arithmetic, no cryptographic hypothesis.
The kimchi analogue of `Bulletproof.Ipa.Forking.three_way_cover`, whose `inl` case closes by
contradiction because its `HasOpening` carries no semantic conjunct.

Arm (4) carries the win conjunct, which the cover's own `hacc` supplies for free at that branch.
It is there because `arm4_hits_badChallenge` needs it: under the extractor's key gate a point of
the arm *carries* key-honesty (`keyHonest_of_openedUnsatisfying`), but only on a winning run.
The narrowing shrinks the fourth arm, so the cover — and every bound derived from it — is
strictly stronger than with the bare `OpenedUnsatisfying`. -/
private theorem four_way_cover (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    {q : (SetupIndex (2 ^ k) → C.ScalarField) × Coins C nc k |
        fam.Wins (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 ∧
          ¬ fam.ExtractsWitness (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      ⊆ {q | q.2 ∈ fam.acceptExtractionFailure
              (augOfSetup (Zcash.Snark.scalarBasis B q.1)) coins}
        ∪ (↑(Zcash.Snark.relSetWithCoins B (fam.relationFinder coins)) :
            Set ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C nc k))
        ∪ {q | fam.TouchesU (Zcash.Snark.scalarBasis B q.1) q.2 coins}
        ∪ {q | fam.Wins (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 ∧
              fam.OpenedUnsatisfying
                (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins} := by
  classical
  intro q hq
  obtain ⟨hacc, hnoext⟩ := hq
  by_cases hsome :
      (fam.attempt (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins).isSome
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
    cases x with
    | inl a =>
      exact Or.inr ⟨hacc, a, hx, fun hs => hnoext ⟨a, hx, hs⟩⟩
    | inr rel =>
      by_cases hu : rel.coeffs Zcash.Snark.AugmentedIndex.u = 0
      · refine Or.inl (Or.inl (Or.inr ?_))
        simp only [Finset.mem_coe, Zcash.Snark.relSetWithCoins, Finset.mem_filter,
          Finset.mem_univ, true_and]
        show (fam.relationFinder coins (Zcash.Snark.scalarBasis B q.1) q.2).isSome = true
        simp only [KimchiFamily.relationFinder, hx, dif_pos hu, Option.isSome_some]
      · exact Or.inl (Or.inr ⟨rel, hx, hu⟩)
  · exact Or.inl (Or.inl (Or.inl ⟨hacc, Option.not_isSome_iff_eq_none.mp hsome⟩))

/-- **Summand (II) — one upstream call.** `Zcash.Snark.relationWithCoins_prob_le_of_textbookDL`
(ironwood, `AGM/ProbabilityCoins.lean`) is index-generic, so it applies at
`ι := SetupIndex (2 ^ k)` with no change; `card_setupIndex` turns its `Fintype.card` factor into
the `2 ^ k + 1` the endpoint states. One slot cheaper than the full augmented basis, because
`U` is not sampled. -/
theorem relation_summand (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) {ε : ℝ≥0∞}
    (hDL : Zcash.Snark.TextbookDLWithCoinsAdvantageLE B (fam.relationFinder coins) ε) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C nc k)).toOuterMeasure
        (Zcash.Snark.relSetWithCoins B (fam.relationFinder coins))
      ≤ ((2 ^ k + 1 : ℕ) : ℝ≥0∞) * ε := by
  have h :=
    Zcash.Snark.relationWithCoins_prob_le_of_textbookDL B (fam.relationFinder coins) hDL
  rwa [card_setupIndex] at h

/-- **Summand (III) — the residual, by its own assumption.** `DerivedUDLAdvantageLE` is stated
at the derived-base log finder's support, and `derivedULog_isSome_iff` says that support *is*
arm (3), so the bound transfers by rewriting the set. -/
theorem residual_summand (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) {δ : ℝ≥0∞}
    (hU : fam.DerivedUDLAdvantageLE B coins δ) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C nc k)).toOuterMeasure
        {q | fam.TouchesU (Zcash.Snark.scalarBasis B q.1) q.2 coins}
      ≤ δ := by
  have hset : {q : (SetupIndex (2 ^ k) → C.ScalarField) × Coins C nc k |
        fam.TouchesU (Zcash.Snark.scalarBasis B q.1) q.2 coins}
      = {q | (fam.derivedULog B coins q.1 q.2).isSome} := by
    ext q
    exact (fam.derivedULog_isSome_iff B coins q.1 q.2).symm
  rw [hset]
  exact hU

/-- **The endpoint, reduced to its two cryptographically-priced arms.** Given a bound on the
presence arm (1) and a bound on the winning opened-but-unsatisfying arm (4), the measure of
`Wins ∧ ¬ ExtractsWitness` is at most those two plus `(2 ^ k + 1) · ε + δ`: `four_way_cover`,
monotonicity, and subadditivity three times.

This is the shape `vesta_kimchi_knowledge_sound` and its Pallas twin consume — instantiate
`bPresence := (Q + k + 1) · 3 / 2 ¹²⁸` (section 15) and
`bAlgebraic := (Q + 1) · szBudget / 2 ¹²⁸` (section 16) and the endpoint is exactly this.

`hAlgebraic` bounds the arm WITH its win conjunct, matching `four_way_cover`; that is a smaller
set than bare `OpenedUnsatisfying`, so the hypothesis is weaker and this corollary is
correspondingly stronger. -/
private theorem wins_notExtracts_measure_le_of_arms (B : C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) {R : ℕ}
    {ε δ bPresence bAlgebraic : ℝ≥0∞}
    (hHard : fam.DiscreteLogRelationHardFor B coins R ε δ)
    (hEff : fam.ReductionEfficient coins R)
    (hPresence : (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C nc k)).toOuterMeasure
        {q | q.2 ∈ fam.acceptExtractionFailure
          (augOfSetup (Zcash.Snark.scalarBasis B q.1)) coins} ≤ bPresence)
    (hAlgebraic : (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C nc k)).toOuterMeasure
        {q | fam.Wins (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 ∧
          fam.OpenedUnsatisfying (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
          ≤ bAlgebraic) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C nc k)).toOuterMeasure
        {q | fam.Wins (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 ∧
          ¬ fam.ExtractsWitness (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      ≤ bPresence + ((2 ^ k + 1 : ℕ) : ℝ≥0∞) * ε + δ + bAlgebraic := by
  obtain ⟨hDL, hU⟩ := hHard hEff
  refine le_trans (MeasureTheory.measure_mono (fam.four_way_cover B coins)) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add ?_ hAlgebraic)
  refine le_trans (MeasureTheory.measure_union_le _ _)
    (add_le_add ?_ (fam.residual_summand B coins hU))
  exact le_trans (MeasureTheory.measure_union_le _ _)
    (add_le_add hPresence (fam.relation_summand B coins hDL))

end KimchiFamily

end Cover


/-! ### Claim stability at the kimchi transcript

`Bulletproof.Forking.claimStable_of_preData` reduces stability of a claim map to three
transcript facts. Two of them are pure schedule bookkeeping and are discharged here, once and
for all: the opening-round nodes all carry the same fully-absorbed pre-opening payload
(`preDataOf_eq_of_ipaPrefixes_eq`), and the six pre-opening nodes are never opening-round nodes
(`preNodeOf_ne_ipaPrefixes`), by the squeeze index alone. What is left — and it is the whole
remaining content — is that the claim *factors* through that payload. -/

section ClaimStability

variable {nc k : ℕ}

/-- The six pre-opening squeezes, in schedule order: `β`, `γ`, `α`, `ζ`, `ξ`, `r`. -/
private def preSqueeze : Fin preIpaChals → Squeeze k :=
  ![.beta, .gamma, .alpha, .zeta, .polyscale, .evalscale]

/-- **The run's pre-opening absorbed data** — the `pre` payload every opening-round node
carries, read off the `ξ` node where every `Option` field is already `some`. -/
def preDataOf (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
    (cp : KimchiProof C nc k) : PreIpaData C nc :=
  (nodeAt digest publicComm cp Squeeze.polyscale).pre

/-- **The node at a pre-opening squeeze, rebuilt from the fully-absorbed pre-opening data** by
re-gating the `Option` fields to the schedule. This is what makes the six challenge-reading
nodes a function of the pre-opening data alone, as `claimStable_of_preData` requires. -/
private def preNodeOf (d : PreIpaData C nc) (s : Squeeze k) : KimchiNode C nc k where
  idx := s
  pre :=
    { digest := d.digest
      publicComm := d.publicComm
      wComm := d.wComm
      zComm := match s with
        | .beta | .gamma => none
        | _ => d.zComm
      tComm := match s with
        | .beta | .gamma | .alpha => none
        | _ => d.tComm
      ftEval1 := match s with
        | .beta | .gamma | .alpha | .zeta => none
        | _ => d.ftEval1
      evals := match s with
        | .beta | .gamma | .alpha | .zeta => none
        | _ => d.evals }
  lr := fun _ => none
  delta := none
  sg := none

/-- **Rebuilding is exact at the six pre-opening squeezes**: nothing absorbed after the
opening begins is visible at them, so re-gating the `ξ`-node payload returns the run's own
node. Definitional at each squeeze. -/
private theorem preNodeOf_preDataOf (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
    (cp : KimchiProof C nc k) (i : Fin preIpaChals) :
    preNodeOf (preDataOf digest publicComm cp) (preSqueeze i)
      = kimchiNodes digest publicComm cp (preSqueeze i) := by
  fin_cases i <;> rfl

/-- **Every opening-round node carries the run's pre-opening data.** The `hdet` half of
`claimStable_of_preData` at this transcript: `nodeAt` gates its `Option` fields only against
the four earliest squeezes, so `ipaRound _` and `schnorr` alike carry the `ξ`-node payload. -/
private theorem preDataOf_eq_of_ipaPrefixes_eq (σ : SRS C.Point) (digest : C.ScalarField)
    (publicComm : Fin nc → C.Point) (cp cp' : KimchiProof C nc σ.k) (j : Fin (σ.k + 1))
    (h : ipaPrefixes σ digest publicComm cp j = ipaPrefixes σ digest publicComm cp' j) :
    preDataOf digest publicComm cp = preDataOf digest publicComm cp' := by
  have hp := congrArg KimchiNode.pre h
  unfold ipaPrefixes kimchiNodes at hp
  split at hp <;> exact hp

/-- **A pre-opening node is never an opening-round node.** The `hdisj` half of
`claimStable_of_preData` at this transcript — and it is decided by the squeeze index alone, not
by the absorbed data, which is exactly why the six `β…r` nodes survive reprogramming at an IPA
round. -/
private theorem preNodeOf_ne_ipaPrefixes (σ : SRS C.Point) (digest : C.ScalarField)
    (publicComm : Fin nc → C.Point) (d : PreIpaData C nc) (cp : KimchiProof C nc σ.k)
    (i : Fin preIpaChals) (j : Fin (σ.k + 1)) :
    preNodeOf d (preSqueeze i) ≠ ipaPrefixes σ digest publicComm cp j := by
  intro h
  have hidx := congrArg KimchiNode.idx h
  unfold ipaPrefixes kimchiNodes nodeAt preNodeOf preSqueeze at hidx
  split_ifs at hidx <;> fin_cases i <;> simp_all

/-- **The kimchi discharge skeleton for claim stability**: a claim map that factors through the
run's pre-opening data and the six pre-opening challenges is stable for the IPA prefixes.

This is `Bulletproof.Forking.claimStable_of_preData` with both transcript-specific hypotheses
already discharged, so a consumer supplies only the factorization `hκ`. -/
private theorem claimStable_of_preDataFactors {ClaimData : Type*} (σ : SRS C.Point)
    (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
    (A : Zcash.Snark.OracleComp (KimchiNode C nc σ.k) Prechallenge (KimchiProof C nc σ.k))
    (κ : KimchiProof C nc σ.k → (KimchiNode C nc σ.k → Prechallenge) → ClaimData)
    (claimOf : PreIpaData C nc → (Fin preIpaChals → Prechallenge) → ClaimData)
    (hκ : ∀ p O, κ p O = claimOf (preDataOf digest publicComm p)
      (fun i => O (kimchiNodes digest publicComm p (preSqueeze i)))) :
    Bulletproof.Forking.ClaimStable A (ipaPrefixes σ digest publicComm) κ :=
  Bulletproof.Forking.claimStable_of_preData A (ipaPrefixes σ digest publicComm)
    (preDataOf digest publicComm) (fun d i => preNodeOf d (preSqueeze i)) claimOf
    (fun p O => (hκ p O).trans (congrArg (claimOf (preDataOf digest publicComm p))
      (funext fun i => congrArg O (preNodeOf_preDataOf digest publicComm p i).symm)))
    (fun j p p' h => preDataOf_eq_of_ipaPrefixes_eq σ digest publicComm p p' j h)
    (fun j p i => preNodeOf_ne_ipaPrefixes σ digest publicComm _ p i j)

/-- **The run's claim as a function of the proof and the six pre-opening challenges alone** —
`runInputWith` with the challenges supplied as a `Fin preIpaChals`-indexed tuple, each
expanded by its own squeeze's map. -/
private def kimchiClaimOf (σ : SRS C.Point) (cvk : KimchiVK C nc) (pub : Array C.ScalarField)
    (cp : KimchiProof C nc σ.k) (ch : Fin preIpaChals → Prechallenge) :
    Ipa.Input C σ.k (nc + 1 + tailRowCount * nc) evalPts :=
  runInputWith σ cvk cp pub
    (squeezeExpand C (Squeeze.beta : Squeeze σ.k) (ch 0))
    (squeezeExpand C (Squeeze.gamma : Squeeze σ.k) (ch 1))
    (squeezeExpand C (Squeeze.alpha : Squeeze σ.k) (ch 2))
    (squeezeExpand C (Squeeze.zeta : Squeeze σ.k) (ch 3))
    (squeezeExpand C (Squeeze.polyscale : Squeeze σ.k) (ch 4))
    (squeezeExpand C (Squeeze.evalscale : Squeeze σ.k) (ch 5))

/-- **The claim reads exactly the six pre-opening nodes** — definitional, and it is the `hκ` of
`claimStable_of_preDataFactors` up to one remaining step: `kimchiClaimOf σ cvk pub cp ch` must
be shown to depend on `cp` only through `preDataOf digest publicComm cp`.

That last step is *false* for the whole `Ipa.Input` — its `proof` field is `cp.opening`, which
no pre-opening node carries — and true for the game's claim triple
`(combinedEvalVector …, cipOf …, combinedCommitment …)`, which reads only the commitment and
evaluation streams. Establishing it is what section 11 below does, and it needs the
faithfulness of `evalsViewOf` (a `PointEvaluations` is recovered from its `pointView`) together
with the recovery of `cp.tComm` from the node's `Fin (7 * nc) → Option _` view. -/
private theorem runClaim_eq_kimchiClaimOf (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) (digest : C.ScalarField) (cp : KimchiProof C nc σ.k)
    (O : KimchiNode C nc σ.k → Prechallenge) :
    runClaim σ cvk pub digest cp O
      = kimchiClaimOf σ cvk pub cp (fun i =>
          O (kimchiNodes digest (fun c => (publicCommitment C σ cvk pub)[c]) cp
            (preSqueeze i))) := rfl

end ClaimStability

/-! ## 11. The claim triple factors through the pre-opening data

`claimStable_of_preDataFactors` (in "Claim stability at the kimchi
transcript") leaves exactly one obligation for the kimchi transcript: that the claim map
*factors* through the run's pre-opening payload. That obligation is discharged here, and with it
the last ingredient of arm (1)'s measure bound —
`Bulletproof.Forking.kimchiExtract_failure_measure_le_of_stable` takes `ClaimStable` as a
hypothesis and this is the kimchi instance of it.

**The retarget.** The obligation is *false* for the whole `Ipa.Input`: `runInputWith` sets
`proof := cp.opening`, and no pre-opening node carries the opening — the `j = 0` prefix node
carries only `lr[0]`. It is true for the triple the adaptive win condition actually reads,
`(combinedEvalVector …, Ipa.cipOf …, combinedCommitment …)`, which is `Bulletproof.Forking.WinsAt`'s
`κ`. So the claim map is retargeted at that triple, and the factorization is proved there.

**How the factorization is proved.** Not by chasing the arithmetic of `runInputWith`, which
reads its `cp` through a dozen intermediate lets, but by showing that the pre-opening payload
*determines the proof up to its opening*: `kimchiProof_eq_of_preData_eq` recovers every field of a
`KimchiProof` but `opening` from `preDataOf`, after which the triple equality is `rfl`. Three
structural facts carry that recovery — the evaluation views are faithful (`pointView_inj`,
`evals_eq_of_evalsViewOf_eq`, `pubEvals_eq_of_evalsViewOf_eq`), the quotient array is recovered
from its `Fin (7 * nc)`-indexed `getElem?` view under the carried size bound, and the commitment
vectors are recovered by `Vector.ext`. -/

section ClaimTriple

variable {nc k : ℕ}

/-- **A `(ζ, ζω)` pair is recovered from its transcript view.** `pointView` reads the two chunk
vectors off the two evaluation points, and `evalPts = 2` with `0 ≠ 1`, so nothing is lost. This
is the base case of "the evaluation families are faithful to their views". -/
private theorem pointView_inj {pe pe' : PointEvaluations (Vector C.ScalarField nc)}
    (h : pointView (C := C) pe = pointView pe') : pe = pe' := by
  have h0 : ∀ c : Fin nc, pe.zeta[c] = pe'.zeta[c] := by
    intro c
    have := congrFun (congrFun h 0) c
    simpa [pointView] using this
  have h1 : ∀ c : Fin nc, pe.zetaOmega[c] = pe'.zetaOmega[c] := by
    intro c
    have := congrFun (congrFun h 1) c
    simpa [pointView] using this
  cases pe; cases pe'
  simp only [PointEvaluations.mk.injEq]
  exact ⟨Vector.ext fun i hi => h0 ⟨i, hi⟩, Vector.ext fun i hi => h1 ⟨i, hi⟩⟩

/-- **The public-evaluation source is recovered from the node's view of it.** The `carried`
branch by `pointView_inj`; the `barycentric` branch because its payload is a proof of `nc = 1`,
hence proof-irrelevant — which is exactly why discarding it in `evalsViewOf` costs nothing. -/
private theorem pubEvals_eq_of_evalsViewOf_eq {cp cp' : KimchiProof C nc k}
    (h : evalsViewOf cp = evalsViewOf cp') : cp.pubEvals = cp'.pubEvals := by
  have hp := congrArg EvalsView.pub h
  simp only [evalsViewOf] at hp
  rcases hcp : cp.pubEvals with pe | hn <;> rcases hcp' : cp'.pubEvals with pe' | hn' <;>
    rw [hcp, hcp'] at hp <;> simp only at hp
  all_goals first
    | rfl
    | exact congrArg _ (pointView_inj (Option.some.inj hp))
    | exact absurd hp (by simp)

/-- **The claimed evaluations are recovered from the node's view of them.** `EvalsView` records
all forty-three families — the seven single-column rows in `lit`, then `w`, `coefficients` and
`s` — so `ProofEvaluations` is reassembled field by field, each through `pointView_inj`. -/
private theorem evals_eq_of_evalsViewOf_eq {cp cp' : KimchiProof C nc k}
    (h : evalsViewOf cp = evalsViewOf cp') : cp.evals = cp'.evals := by
  have hlit := congrArg EvalsView.lit h
  have hw := congrArg EvalsView.w h
  have hc := congrArg EvalsView.coefficients h
  have hs := congrArg EvalsView.s h
  simp only [evalsViewOf] at hlit hw hc hs
  have h0 : cp.evals.z = cp'.evals.z := pointView_inj (congrFun hlit 0)
  have h1 : cp.evals.genericSelector = cp'.evals.genericSelector :=
    pointView_inj (congrFun hlit 1)
  have h2 : cp.evals.poseidonSelector = cp'.evals.poseidonSelector :=
    pointView_inj (congrFun hlit 2)
  have h3 : cp.evals.completeAddSelector = cp'.evals.completeAddSelector :=
    pointView_inj (congrFun hlit 3)
  have h4 : cp.evals.mulSelector = cp'.evals.mulSelector := pointView_inj (congrFun hlit 4)
  have h5 : cp.evals.emulSelector = cp'.evals.emulSelector := pointView_inj (congrFun hlit 5)
  have h6 : cp.evals.endomulScalarSelector = cp'.evals.endomulScalarSelector :=
    pointView_inj (congrFun hlit 6)
  have hwv : cp.evals.w = cp'.evals.w :=
    Vector.ext fun i hi => pointView_inj (congrFun hw ⟨i, hi⟩)
  have hcv : cp.evals.coefficients = cp'.evals.coefficients :=
    Vector.ext fun i hi => pointView_inj (congrFun hc ⟨i, hi⟩)
  have hsv : cp.evals.s = cp'.evals.s :=
    Vector.ext fun i hi => pointView_inj (congrFun hs ⟨i, hi⟩)
  show (⟨cp.evals.w, cp.evals.z, cp.evals.s, cp.evals.coefficients, cp.evals.genericSelector,
      cp.evals.poseidonSelector, cp.evals.completeAddSelector, cp.evals.mulSelector,
      cp.evals.emulSelector, cp.evals.endomulScalarSelector⟩ :
      ProofEvaluations (Vector C.ScalarField nc))
    = ⟨cp'.evals.w, cp'.evals.z, cp'.evals.s, cp'.evals.coefficients, cp'.evals.genericSelector,
      cp'.evals.poseidonSelector, cp'.evals.completeAddSelector, cp'.evals.mulSelector,
      cp'.evals.emulSelector, cp'.evals.endomulScalarSelector⟩
  rw [h0, h1, h2, h3, h4, h5, h6, hwv, hcv, hsv]

/-- **The pre-opening payload determines the proof up to its opening.** Everything the node
absorbs before the opening argument — the witness and permutation commitments, the quotient
chunks, `ft(ζω)` and the evaluations — reconstructs the corresponding `KimchiProof` field, so two
proofs with the same payload differ at most in `opening`.

The quotient step is the only one that is not a plain `ext`: the node holds `tComm` as a
`Fin (7 * nc)`-indexed family of `getElem?` reads, and the array is recovered from it because
`tComm_le` bounds both sizes by `7 * nc`, so every out-of-range read is `none` on both sides. -/
private theorem kimchiProof_eq_of_preData_eq
    (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
    (cp cp' : KimchiProof C nc k)
    (h : preDataOf digest publicComm cp = preDataOf digest publicComm cp') :
    cp = { cp' with opening := cp.opening } := by
  have hw := congrArg PreIpaData.wComm h
  have hz := congrArg PreIpaData.zComm h
  have ht := congrArg PreIpaData.tComm h
  have hf := congrArg PreIpaData.ftEval1 h
  have he := congrArg PreIpaData.evals h
  simp only [preDataOf, nodeAt, Option.some.injEq] at hw hz ht hf he
  have hwc : cp.wComm = cp'.wComm :=
    Vector.ext fun i hi => Vector.ext fun j hj => congrFun (congrFun hw ⟨i, hi⟩) ⟨j, hj⟩
  have hzc : cp.zComm = cp'.zComm := Vector.ext fun j hj => congrFun hz ⟨j, hj⟩
  have htc : cp.tComm = cp'.tComm := by
    refine Array.ext_getElem? fun i => ?_
    by_cases hi : i < 7 * nc
    · exact congrFun ht ⟨i, hi⟩
    · have h1 := cp.tComm_le
      have h2 := cp'.tComm_le
      rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
  have hev : cp.evals = cp'.evals := evals_eq_of_evalsViewOf_eq he
  have hpe : cp.pubEvals = cp'.pubEvals := pubEvals_eq_of_evalsViewOf_eq he
  cases cp with | mk wc zc tc tle ev pv fe op =>
  cases cp' with | mk wc' zc' tc' tle' ev' pv' fe' op' =>
  simp only at hwc hzc htc hf hev hpe
  subst hwc; subst hzc; subst htc; subst hf; subst hev; subst hpe
  rfl

variable [Module C.ScalarField C.Point]

/-- **The claim triple** `(b, v, P)` the adaptive win condition reads: the combined evaluation
vector, the combined inner product, and the polyscale combination of the commitments. Exactly
the shape of `Bulletproof.Forking.WinsAt`'s claim map, and deliberately *not* the whole
`Ipa.Input` — the opening is what makes the full input unstable. -/
private def claimTriple {m : ℕ} (inp : Ipa.Input C k m evalPts) :
    (Fin (2 ^ k) → C.ScalarField) × C.ScalarField × C.Point :=
  (combinedEvalVector (2 ^ k) inp.evalscale inp.pointFn, Ipa.cipOf inp,
    combinedCommitment inp.polyscale inp.commitmentFn)

/-- **The triple factors through the pre-opening data**. Two
runs with the same pre-opening payload, at the same six challenges, give the same combined
evaluation vector, the same inner-product claim and the same combined commitment.

Once `kimchiProof_eq_of_preData_eq` has pushed the two proofs into the shape
`cp = { cp' with opening := _ }`, the three components are definitionally equal: none of
`Input.commitmentFn`, `Input.pointFn`, `Input.evalFn` reads `Input.proof`. -/
private theorem triple_eq_of_preData_eq (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) (digest : C.ScalarField) (cp cp' : KimchiProof C nc σ.k)
    (beta gamma alpha zeta v u : C.ScalarField)
    (h : preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp
      = preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp') :
    claimTriple (runInputWith σ cvk cp pub beta gamma alpha zeta v u)
      = claimTriple (runInputWith σ cvk cp' pub beta gamma alpha zeta v u) := by
  obtain ⟨o, ho⟩ : ∃ o, cp = { cp' with opening := o } :=
    ⟨cp.opening, kimchiProof_eq_of_preData_eq _ _ cp cp' h⟩
  subst ho
  rfl

/-- **The triple as a function of the pre-opening payload alone** — the `claimOf` that
`claimStable_of_preDataFactors` asks for. Total by a classical case split on whether the payload
is realized by some proof at all; on the realized branch the choice of realizer does not matter,
which is `triple_eq_of_preData_eq`. Unrealized payloads never arise from a run, so their value is
arbitrary. -/
private noncomputable def preClaimTriple (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) (digest : C.ScalarField)
    (d : PreIpaData C nc) (ch : Fin preIpaChals → Prechallenge) :
    (Fin (2 ^ σ.k) → C.ScalarField) × C.ScalarField × C.Point :=
  letI := Classical.propDecidable
    (∃ cp : KimchiProof C nc σ.k,
      preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp = d)
  if h : ∃ cp : KimchiProof C nc σ.k,
      preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp = d then
    claimTriple (kimchiClaimOf σ cvk pub h.choose ch)
  else (0, 0, 0)

/-- **The factorization, at a realized payload**: the run's own triple is what `preClaimTriple`
returns at the run's payload. This is the `hκ` of `claimStable_of_preDataFactors`. -/
private theorem claimTriple_kimchiClaimOf_eq_preClaimTriple (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) (digest : C.ScalarField) (cp : KimchiProof C nc σ.k)
    (ch : Fin preIpaChals → Prechallenge) :
    claimTriple (kimchiClaimOf σ cvk pub cp ch)
      = preClaimTriple σ cvk pub digest
          (preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp) ch := by
  have hex : ∃ cp' : KimchiProof C nc σ.k,
      preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp'
        = preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp := ⟨cp, rfl⟩
  rw [preClaimTriple, dif_pos hex]
  exact triple_eq_of_preData_eq σ cvk pub digest _ cp _ _ _ _ _ _ hex.choose_spec |>.symm

/-- **The claim triple is stable at the kimchi transcript**, for any adversary against the
transcript of `σ`, `cvk`, `pub`, `digest`. `claimStable_of_preDataFactors` supplies the two
schedule facts; the factorization is `claimTriple_kimchiClaimOf_eq_preClaimTriple`. -/
private theorem claimStable_claimTriple (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) (digest : C.ScalarField)
    (A : Zcash.Snark.OracleComp (KimchiNode C nc σ.k) Prechallenge (KimchiProof C nc σ.k)) :
    Bulletproof.Forking.ClaimStable A
      (ipaPrefixes σ digest (fun c => (publicCommitment C σ cvk pub)[c]))
      (fun cp O => claimTriple (runClaim σ cvk pub digest cp O)) :=
  claimStable_of_preDataFactors σ digest (fun c => (publicCommitment C σ cvk pub)[c]) A
    (fun cp O => claimTriple (runClaim σ cvk pub digest cp O))
    (preClaimTriple σ cvk pub digest)
    (fun p O => by
      show claimTriple (runClaim σ cvk pub digest p O) = _
      rw [runClaim_eq_kimchiClaimOf]
      exact claimTriple_kimchiClaimOf_eq_preClaimTriple σ cvk pub digest p _)

/-- **Arm (1)'s last ingredient**: at every basis, the family's own
claim map — proof and table to the triple `(b, v, P)` the win condition reads — is stable under
the fork's reprogrammings. `Bulletproof.Forking.kimchiExtract_failure_measure_le_of_stable` takes
exactly this as its `hstable`, so the presence arm's bound now waits on nothing else here. -/
private theorem KimchiFamily.claimStable_runClaimTriple {n : ℕ} [NeZero n]
    (fam : KimchiFamily C nc k n) (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) :
    Bulletproof.Forking.ClaimStable (fam.adversary basis)
      (ipaPrefixes (srsOfBasis k basis) (fam.digest basis) (fam.publicComm basis))
      (fun cp O => claimTriple (runClaim (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis)
        (fam.digest basis) cp O)) :=
  claimStable_claimTriple (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis)
    (fam.digest basis) (fam.adversary basis)

end ClaimTriple

/-! ## 11b. The warm opening base factors through the pre-opening data

The section above discharges claim stability for the triple the win condition reads. The
deployed *base* needs the same treatment, and gets it by the same argument at a group-valued map
instead of a triple-valued one: `claimStable_of_preDataFactors` is stated for an arbitrary
`ClaimData`, and base stability *is* claim stability at `ClaimData := C.Point`
(`Bulletproof.Forking.BaseStable` is a plain `def` alias), so the skeleton's output is already
the statement wanted, with no transport.

The single fact that carries the discharge is the one section 11 already proves:
`kimchiProof_eq_of_preData_eq`, the pre-opening payload determines the proof up to its
`opening`. Both halves of the warm base are then determined, because neither reads `opening` —
the warm state is folded from the pre-`ζ` absorb schedule (`preZeta` reads `digest`, the public
commitment, `wComm`, `zComm` and `tComm`, and nothing else), and the `preT` prefix is a function
of the claimed value, which is the middle component of the claim triple. -/

section WarmBase

variable {nc k : ℕ}

/-- **The `U`-base prefix reads the claim only through its value**.
`preT inp` is the two-element list `[frScalar (shiftScalar (cipOf inp)), sqBase]`, so it is
literally a function of `cipOf inp`; in particular it does not read the opening proof, which is
what distinguishes it from the round and Schnorr prefixes.

Deliberately kept local rather than pushed into `Bulletproof/Forking/Transcript.lean`: it is a
one-step `congrArg` that only this discharge needs. -/
private theorem preT_eq_of_cipOf_eq {j m p : ℕ} (inp inp' : Ipa.Input C j m p)
    (h : Ipa.cipOf inp = Ipa.cipOf inp') :
    IpaTranscriptElt.preT inp = IpaTranscriptElt.preT inp' := by
  simp only [IpaTranscriptElt.preT, IpaTranscriptElt.preTAbsorbs, h]

/-- **The warm state is determined by the pre-opening payload.**
The warm state is the fold of the fq sponge along the
pre-`ζ` absorb list — the key digest, the public commitment chunks, the witness commitments, the
permutation commitment and the quotient chunks — none of which is the opening. So equal payloads
force the two proofs into the same shape and the two folds have the same input.

Mirrors `triple_eq_of_preData_eq` (section 11) verbatim: the same `kimchiProof_eq_of_preData_eq`
rewrite, the same `subst`, and the same `rfl`. -/
private theorem warmState_eq_of_preData_eq (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) (digest : C.ScalarField) (cp cp' : KimchiProof C nc σ.k)
    (h : preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp
      = preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp') :
    warmState cvk cp (publicCommitment C σ cvk pub)
      = warmState cvk cp' (publicCommitment C σ cvk pub) := by
  obtain ⟨o, ho⟩ : ∃ o, cp = { cp' with opening := o } :=
    ⟨cp.opening, kimchiProof_eq_of_preData_eq _ _ cp cp' h⟩
  subst ho
  rfl

variable [Module C.ScalarField C.Point]

/-- **The warm base as a function of the proof and the six pre-opening challenges alone**
(payload-and-challenges form): `warmBase` with the table replaced by a
`Fin preIpaChals`-indexed tuple of prechallenges, each expanded by its own squeeze's map.

Mirrors `kimchiClaimOf` (`§ Claim stability at the kimchi transcript`) exactly — same six
arguments, same expansion — and stands
to `warmBase` as `kimchiClaimOf` stands to `runClaim`. -/
def kimchiWarmBase (σ : SRS C.Point) (cvk : KimchiVK C nc) (pub : Array C.ScalarField)
    (cp : KimchiProof C nc σ.k) (ch : Fin preIpaChals → Prechallenge) : C.Point :=
  C.toGroup ((kimchiOpeningFS cvk cp (publicCommitment C σ cvk pub)).squeezeBase
    (IpaTranscriptElt.preT (kimchiClaimOf σ cvk pub cp ch)))

omit [Module C.ScalarField C.Point] in
/-- **The warm base reads exactly the six pre-opening nodes** — the run form is the
challenge-tuple form at the table's answers at the run's own six pre-opening nodes. Definitional,
and the exact mirror of `runClaim_eq_kimchiClaimOf` (same section), which is `rfl` for the same
reason: the base is built from the run's claim and the claim already reads only those six. -/
theorem warmBase_eq_kimchiWarmBase (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) (digest : C.ScalarField) (cp : KimchiProof C nc σ.k)
    (O : KimchiNode C nc σ.k → Prechallenge) :
    warmBase σ cvk pub digest cp O
      = kimchiWarmBase σ cvk pub cp (fun i =>
          O (kimchiNodes digest (fun c => (publicCommitment C σ cvk pub)[c]) cp
            (preSqueeze i))) := rfl

/-- **The warm base is determined by the payload and the six challenges.**
The base is `toGroup` of one squeeze, so it suffices to equate the
squeeze's two arguments: the source is `spongeFSFrom` of the warm state, equal by
`warmState_eq_of_preData_eq`; the prefix is `preT` of the run's claim, and the two claims have
the same value because that value is the middle component of the claim triple, which
`triple_eq_of_preData_eq` already equates — so `preT_eq_of_cipOf_eq` equates the prefixes.

Mirrors the *use* of `triple_eq_of_preData_eq` rather than its proof: no second `subst` is
needed, because both halves are already available as lemmas. -/
theorem kimchiWarmBase_eq_of_preData_eq (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) (digest : C.ScalarField) (cp cp' : KimchiProof C nc σ.k)
    (ch : Fin preIpaChals → Prechallenge)
    (h : preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp
      = preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp') :
    kimchiWarmBase σ cvk pub cp ch = kimchiWarmBase σ cvk pub cp' ch := by
  have hstate := warmState_eq_of_preData_eq σ cvk pub digest cp cp' h
  have htriple := triple_eq_of_preData_eq σ cvk pub digest cp cp'
    (squeezeExpand C (Squeeze.beta : Squeeze σ.k) (ch 0))
    (squeezeExpand C (Squeeze.gamma : Squeeze σ.k) (ch 1))
    (squeezeExpand C (Squeeze.alpha : Squeeze σ.k) (ch 2))
    (squeezeExpand C (Squeeze.zeta : Squeeze σ.k) (ch 3))
    (squeezeExpand C (Squeeze.polyscale : Squeeze σ.k) (ch 4))
    (squeezeExpand C (Squeeze.evalscale : Squeeze σ.k) (ch 5)) h
  have hcip : Ipa.cipOf (kimchiClaimOf σ cvk pub cp ch)
      = Ipa.cipOf (kimchiClaimOf σ cvk pub cp' ch) := congrArg (fun t => t.2.1) htriple
  rw [kimchiWarmBase, kimchiWarmBase, kimchiOpeningFS, kimchiOpeningFS, hstate,
    preT_eq_of_cipOf_eq _ _ hcip]

/-- **The warm base as a function of the pre-opening payload alone** — the
`claimOf` that `claimStable_of_preDataFactors` asks for, at `ClaimData := C.Point`. Total by a
classical case split on whether the payload is realized by some proof at all; on the realized
branch the choice of realizer does not matter, which is `kimchiWarmBase_eq_of_preData_eq`.
Unrealized payloads never arise from a run, so their value is immaterial.

Mirrors `preClaimTriple` (section 11) exactly, with `0` in place of `(0, 0, 0)`. -/
private noncomputable def preWarmBase (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) (digest : C.ScalarField)
    (d : PreIpaData C nc) (ch : Fin preIpaChals → Prechallenge) : C.Point :=
  letI := Classical.propDecidable
    (∃ cp : KimchiProof C nc σ.k,
      preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp = d)
  if h : ∃ cp : KimchiProof C nc σ.k,
      preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp = d then
    kimchiWarmBase σ cvk pub h.choose ch
  else 0

/-- **The factorization, at a realized payload**: the run's own warm
base is what `preWarmBase` returns at the run's payload. This is the `hκ` of
`claimStable_of_preDataFactors`.

Mirrors `claimTriple_kimchiClaimOf_eq_preClaimTriple` (section 11) line for line: the payload is
realized by the run itself, so the defining case split takes its first branch, and
`kimchiWarmBase_eq_of_preData_eq` at `hex.choose_spec` equates the chosen realizer's value with
the run's. -/
private theorem kimchiWarmBase_eq_preWarmBase (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) (digest : C.ScalarField) (cp : KimchiProof C nc σ.k)
    (ch : Fin preIpaChals → Prechallenge) :
    kimchiWarmBase σ cvk pub cp ch
      = preWarmBase σ cvk pub digest
          (preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp) ch := by
  have hex : ∃ cp' : KimchiProof C nc σ.k,
      preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp'
        = preDataOf digest (fun c => (publicCommitment C σ cvk pub)[c]) cp := ⟨cp, rfl⟩
  rw [preWarmBase, dif_pos hex]
  exact kimchiWarmBase_eq_of_preData_eq σ cvk pub digest _ cp ch hex.choose_spec |>.symm

/-- **The deployed warm base is base-stable**, for any adversary against
the transcript of `σ`, `cvk`, `pub`, `digest`. `claimStable_of_preDataFactors` supplies the two
schedule facts; the factorization is `warmBase_eq_kimchiWarmBase` followed by
`kimchiWarmBase_eq_preWarmBase`.

Mirrors `claimStable_claimTriple` (section 11), with the skeleton instantiated at
`ClaimData := C.Point` instead of the triple type. No transport into `BaseStable` is needed or
wanted: that predicate is a `def` alias of `ClaimStable` at the group
(`Bulletproof/Forking/Game.lean`), so the skeleton's output already *is* this statement. -/
private theorem baseStable_warmBase (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (pub : Array C.ScalarField) (digest : C.ScalarField)
    (A : Zcash.Snark.OracleComp (KimchiNode C nc σ.k) Prechallenge (KimchiProof C nc σ.k)) :
    Bulletproof.Forking.BaseStable A
      (ipaPrefixes σ digest (fun c => (publicCommitment C σ cvk pub)[c]))
      (fun cp O => warmBase σ cvk pub digest cp O) :=
  claimStable_of_preDataFactors σ digest (fun c => (publicCommitment C σ cvk pub)[c]) A
    (fun cp O => warmBase σ cvk pub digest cp O)
    (preWarmBase σ cvk pub digest)
    (fun p O => by
      show warmBase σ cvk pub digest p O = _
      rw [warmBase_eq_kimchiWarmBase]
      exact kimchiWarmBase_eq_preWarmBase σ cvk pub digest p _)

/-- **The base hypothesis of the family's measure bound** (family form):
at every basis, the family's own warm base map is stable under the fork's reprogrammings.
`Bulletproof.Forking.kimchiExtract_failure_measure_prod_le_of_stableBase` takes exactly this as
its `hbase`, at `uOf s := fun _ O => fam.warmBase basis O`, so the map is written in that
shape — ignoring the proof argument and reading the run's own proof through `fam.warmBase` —
rather than in the proof-taking shape of the generic theorem above.

The two shapes agree only up to `KimchiFamily.warmBase`'s own unfolding, and unifying them
*under the binder* sends the elaborator into the sponge fold, so the step is taken after
`intro`, where the comparison is between two closed terms with the same head. Mirrors
`KimchiFamily.claimStable_runClaimTriple` (section 11): the generic theorem at the family's own
SRS, verifying key, public input, digest and adversary. -/
private theorem KimchiFamily.baseStable_warmBase {n : ℕ} [NeZero n]
    (fam : KimchiFamily C nc k n) (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) :
    Bulletproof.Forking.BaseStable (fam.adversary basis)
      (ipaPrefixes (srsOfBasis k basis) (fam.digest basis) (fam.publicComm basis))
      (fun _ O => fam.warmBase basis O) := by
  intro j O u h
  exact _root_.Kimchi.Verifier.KnowledgeSoundness.baseStable_warmBase (srsOfBasis k basis)
    (fam.cvk basis) (fam.pub basis) (fam.digest basis) (fam.adversary basis) j O u h

end WarmBase

/-! ## 12. Arm (4): the algebraic containment

Arm (4) is the arm with no counterpart on the IPA side: the extractor *did* open, but the
table it assembles fails the circuit. The plan for arm (4) is that such a point
carries an accepted opening whose coefficients are the family's own, and key-honest
representations (the extractor's gate); the challenge-generic run-soundness root then converts
those into satisfaction of the assembled table PROVIDED eight scalar side conditions hold. So a
point of arm (4) violates one of them, each a membership of one of the run's own challenges in
a counted exclusion set. -/

section Arm4

variable [Module C.ScalarField C.Point]

namespace KimchiFamily

variable {nc k n : ℕ} [NeZero n] (fam : KimchiFamily C nc k n)

/-- **Pins, or a bad opening-argument challenge**. On a run at which the
extractor returns a left payload, either every claimed evaluation of the run's batched claim is
the inner product of that row's declared coefficient vector with the evaluation vector at that
point, or the run's polyscale challenge lies in the `ξ` exclusion set, or its evalscale
challenge lies in the `r` exclusion set.

The accepted opening and the coefficient equality both come from `attempt_inl_pins`; the
combined inner product the opening is checked against is the claim's own, so
`eval_pins_of_opening_of_eq` applies off the two
exclusion sets. No binding hypothesis appears anywhere in the ancestry. -/
private theorem pins_or_badChallenge_of_attempt_inl
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (a : Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ k) → C.ScalarField)
    (h : fam.attempt basis O coins = some (PSum.inl a)) :
    (∀ (i : Fin (nc + 1 + tailRowCount * nc)) (j : Fin evalPts),
        (fam.claim basis O).evalFn i j
          = innerProduct (fam.aRef basis O i)
              (evalVector (2 ^ k) ((fam.claim basis O).pointFn j)))
      ∨ (fam.claim basis O).polyscale
          ∈ badXiOf (fam.runSrs basis O) (fam.aRef basis O) (fam.claim basis O).pointFn
              (fam.claim basis O).evalFn
      ∨ (fam.claim basis O).evalscale
          ∈ badROf (fam.runSrs basis O) (fam.aRef basis O) (fam.claim basis O).pointFn
              (fam.claim basis O).evalFn (fam.claim basis O).polyscale := by
  classical
  by_cases hξ : (fam.claim basis O).polyscale
      ∈ badXiOf (fam.runSrs basis O) (fam.aRef basis O) (fam.claim basis O).pointFn
          (fam.claim basis O).evalFn
  · exact Or.inr (Or.inl hξ)
  by_cases hr : (fam.claim basis O).evalscale
      ∈ badROf (fam.runSrs basis O) (fam.aRef basis O) (fam.claim basis O).pointFn
          (fam.claim basis O).evalFn (fam.claim basis O).polyscale
  · exact Or.inr (Or.inr hr)
  refine Or.inl ?_
  obtain ⟨-, hopen⟩ := fam.attempt_inl_pins basis O coins a h
  exact eval_pins_of_opening_of_eq (fam.runSrs basis O) (fam.claim basis O).commitmentFn
    (fam.claim basis O).pointFn (fam.aRef basis O) (fam.claim basis O).evalFn _ _ hξ hr
    (fam.pgOf basis O) (fam.pwOf basis O) hopen (fam.pgOf_eq_sum_smul basis O)

/-- **Arm (4) is contained in seven bad-challenge events**. Every point of
the opened-but-unsatisfying arm on a winning run satisfies at least one of: the run's `β` lies
in the `β` Schwartz–Zippel set, its `γ` in the `γ` set, its `α` in the `α` set, its `ζ` in the
`ζ` set at the run's own assembled quotient, its `ζ` in the two-element boundary set, its
polyscale in the `ξ` set, or its evalscale in the `r` set.

The route is the blueprint's: `pins_or_badChallenge_of_attempt_inl` gives the two fr-side
disjuncts or the per-row evaluation pins; `keyHonest_of_openedUnsatisfying` gives the five
representation hypotheses; the family's `hrep` gives the commitment representations; then
`run_sound_algebraic_at_of_vkrep` at the run's own six challenges yields `RunGuardImpAt`, whose
conclusion the arm's own conjunct denies — so one of its six guards fails, and the last two of
those are `zetaBoundaryBad`. -/
private theorem arm4_hits_badChallenge
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hsmul : ∀ (a : C.ScalarField) (P : C.Point), a • P = a.val • P)
    (hwin : fam.Wins basis O) (harm : fam.OpenedUnsatisfying basis O coins) :
    fam.readsOf basis O Squeeze.beta
        ∈ Protocol.soundBadB fam.idx
            (runW (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
              (fam.aRef basis O))
      ∨ fam.readsOf basis O Squeeze.gamma
          ∈ Protocol.soundBadG fam.idx
              (runW (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
                (fam.aRef basis O))
              (fam.readsOf basis O Squeeze.beta)
      ∨ fam.readsOf basis O Squeeze.alpha
          ∈ Protocol.soundBadA fam.idx (pubView fam.idx (fam.pub basis))
              (runW (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
                (fam.aRef basis O))
              (runZ (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
                (fam.aRef basis O))
              (fam.readsOf basis O Squeeze.beta) (fam.readsOf basis O Squeeze.gamma)
      ∨ fam.readsOf basis O Squeeze.zeta
          ∈ Protocol.soundBadZ fam.idx (pubView fam.idx (fam.pub basis))
              (runW (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
                (fam.aRef basis O))
              (runZ (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
                (fam.aRef basis O))
              (fam.readsOf basis O Squeeze.beta) (fam.readsOf basis O Squeeze.gamma)
              (fam.readsOf basis O Squeeze.alpha)
              (ftChunkAssembly k (fam.proofOf basis O).tComm.size (fam.aT basis O))
      ∨ fam.readsOf basis O Squeeze.zeta ∈ zetaBoundaryBad fam.idx
      ∨ (fam.claim basis O).polyscale
          ∈ badXiOf (fam.runSrs basis O) (fam.aRef basis O) (fam.claim basis O).pointFn
              (fam.claim basis O).evalFn
      ∨ (fam.claim basis O).evalscale
          ∈ badROf (fam.runSrs basis O) (fam.aRef basis O) (fam.claim basis O).pointFn
              (fam.claim basis O).evalFn (fam.claim basis O).polyscale := by
  classical
  obtain ⟨hvkh, hfth⟩ := fam.keyHonest_of_openedUnsatisfying basis O coins hsmul hwin harm
  obtain ⟨a, ha, hnsat⟩ := harm
  obtain ⟨haeq, -⟩ := fam.attempt_inl_pins basis O coins a ha
  subst haeq
  rcases fam.pins_or_badChallenge_of_attempt_inl basis O coins _ ha with hpins | hxi | hr
  · -- The main branch: the pins hold, so the algebraic root applies at the run's challenges.
    obtain ⟨-, himp⟩ :=
      run_sound_algebraic_at_of_vkrep (srsOfBasis k basis) (fam.cvk basis)
        (fam.proofOf basis O) (fam.pub basis) fam.idx
        (fam.readsOf basis O Squeeze.beta) (fam.readsOf basis O Squeeze.gamma)
        (fam.readsOf basis O Squeeze.alpha) (fam.readsOf basis O Squeeze.zeta)
        (fam.readsOf basis O Squeeze.polyscale) (fam.readsOf basis O Squeeze.evalscale)
        fam.hnc fam.hkn (fam.hn basis) (fam.hvk basis) (fam.htpos basis O)
        (fam.aRef basis O) (fam.ρRef basis O) (fam.hrep basis O) (fam.aT basis O) hpins
        (fun i c => hvkh (VkRow.sigma i) c) (fun cc c => hvkh (VkRow.coeff cc) c)
        (fun jj c => hvkh (VkRow.sel jj) c) (fun c => hvkh VkRow.pub c)
        (fun i hi => by
          have hie : i = ftPos nc := Fin.ext hi
          subst hie
          exact hfth)
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨hB, hG, hA, hZ, hbd, -, -⟩ := hcon
    obtain ⟨hz1, hzb⟩ := (not_mem_zetaBoundaryBad_iff fam.idx _).mp hbd
    exact hnsat (himp hB hG hA hZ hz1 hzb)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hxi)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr)))))

end KimchiFamily

end Arm4

/-! ## 13. Arm (1): a deployed win is an abstract win at the claim triple

The presence arm is priced by the adaptive game, whose win event is
`Bulletproof.Forking.WinsAt` — the abstract acceptance predicate at the claim map's own triple.
The kimchi win event is the executable `kimchiVerifyWith` at the table's challenges. This
section is the bridge to the abstract win, `winsAt_of_wins`.

`Bulletproof.Ipa.Forking.wireWins_iff_wins` (`Deployed.lean`) is the exact pattern, and the step
it factors through — `verifyWith_iff_verifierAcceptsAt` — is now public in that (protected)
file, so it is imported and called rather than restated. What remains project-local is only the
node bookkeeping: the kimchi transcript names the opening-argument squeezes by a `Squeeze` tag
while `ipaPrefixes` names them by a `dite`, and the two spellings have to be matched. -/

section WinBridge

variable [Module C.ScalarField C.Point]

/-! ### The IPA squeezes read the same nodes on both sides

`ipaPrefixes` selects the node by a `dite` on `(j : ℕ) < σ.k`; `reads` names the same node by
its `Squeeze` tag. The two agree, and the expansion map agrees too — `squeezeExpand` is
`expandPre` at every squeeze except `β` and `γ`. -/

namespace KimchiFamily

variable {nc k n : ℕ} [NeZero n] (fam : KimchiFamily C nc k n)

/-- **A deployed win is an abstract win at the claim triple**. If the
challenge-generic kimchi verifier accepts a run at the table's own challenges, then the abstract
opening-argument win predicate holds at the run's setup — the sampled setup with base the
group-map image of the run's combined inner product — for the claim triple of the run's batched
claim.

The deployed win is the size guard together with `Ipa.verifyWith` at the run's claim
(`kimchiVerifyWith_eq_verifyWith`); a `true` result forces the guard's else branch. Those
equations are the abstract acceptance predicate at the same base by
`verifyWith_iff_verifierAcceptsAt`, whose only side condition is the curve's `.val`-scalar
collapse. The round and Schnorr challenges match because both sides read the table at the same
nodes through the same expansion, and the evaluation slot matches because
`claimTriple`'s three components are literally `verifyWith_iff_verifierAcceptsAt`'s. -/
private theorem winsAt_of_wins
    (hsmul : ∀ (z : C.ScalarField) (P : C.Point), z • P = z.val • P)
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (hwin : fam.Wins basis O) :
    Bulletproof.Forking.WinsAt (fam.runSrs basis O) (expandPre C)
      (fun cp => toOpening cp.opening)
      (ipaPrefixes (srsOfBasis k basis) (fam.digest basis) (fam.publicComm basis))
      (fun cp O' => claimTriple (runClaim (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis)
        (fam.digest basis) cp O'))
      O (fam.proofOf basis O) := by
  -- (1) the size guard is off, so the win is `Ipa.verifyWith` at the run's own claim
  have hv : Ipa.verifyWith C (srsOfBasis k basis) (fam.warmBase basis O)
      (Vector.ofFn fun i : Fin k => fam.readsOf basis O (Squeeze.ipaRound i))
      (fam.readsOf basis O Squeeze.schnorr) (fam.claim basis O) = true := by
    have h := hwin
    unfold KimchiFamily.Wins at h
    rw [kimchiVerifyWith_eq_verifyWith] at h
    split at h
    · exact absurd h (by simp)
    · exact h
  -- (2) the wire-to-algebra bridge, at the transcript-derived base
  have hacc := (verifyWith_iff_verifierAcceptsAt hsmul (srsOfBasis k basis)
    (fam.warmBase basis O)
    (Vector.ofFn fun i : Fin k => fam.readsOf basis O (Squeeze.ipaRound i))
    (fam.readsOf basis O Squeeze.schnorr) (fam.claim basis O)).mp hv
  -- (3) both sides read the table at the same nodes
  have hu : (fun i : Fin k =>
        (Vector.ofFn fun j : Fin k => fam.readsOf basis O (Squeeze.ipaRound j))[i])
      = fun i : Fin k => expandPre C
          (O (ipaPrefixes (srsOfBasis k basis) (fam.digest basis) (fam.publicComm basis)
            (fam.proofOf basis O) i.castSucc)) := by
    funext i
    simp [ipaPrefixes, KimchiFamily.readsOf, reads, squeezeExpand]
  have hc : fam.readsOf basis O Squeeze.schnorr
      = expandPre C (O (ipaPrefixes (srsOfBasis k basis) (fam.digest basis)
          (fam.publicComm basis) (fam.proofOf basis O) (Fin.last k))) := by
    simp [ipaPrefixes, KimchiFamily.readsOf, reads, squeezeExpand]
  -- (4) restate the two node identities at the goal's own index type — the abstract game reads
  -- `Fin (fam.runSrs basis O).k`, the twin `Fin (srsOfBasis k basis).k`, and the two are
  -- definitionally `Fin k`; `have` closes that gap where `rw` cannot.
  have hu' : (fun i : Fin (fam.runSrs basis O).k =>
        (Vector.ofFn fun j : Fin k => fam.readsOf basis O (Squeeze.ipaRound j))[i])
      = fun i : Fin (fam.runSrs basis O).k => expandPre C
          (O (ipaPrefixes (srsOfBasis k basis) (fam.digest basis) (fam.publicComm basis)
            (fam.proofOf basis O) i.castSucc)) := hu
  have hc' : fam.readsOf basis O Squeeze.schnorr
      = expandPre C (O (ipaPrefixes (srsOfBasis k basis) (fam.digest basis)
          (fam.publicComm basis) (fam.proofOf basis O)
          (Fin.last (fam.runSrs basis O).k))) := hc
  show VerifierAcceptsAt (fam.runSrs basis O) (toOpening (fam.proofOf basis O).opening)
      (combinedCommitment (fam.claim basis O).polyscale (fam.claim basis O).commitmentFn)
      (innerProduct
        (bPolyCoefficients fun i : Fin (fam.runSrs basis O).k => expandPre C
          (O (ipaPrefixes (srsOfBasis k basis) (fam.digest basis) (fam.publicComm basis)
            (fam.proofOf basis O) i.castSucc)))
        (combinedEvalVector (2 ^ k) (fam.claim basis O).evalscale (fam.claim basis O).pointFn))
      (Ipa.cipOf (fam.claim basis O))
      (expandPre C (O (ipaPrefixes (srsOfBasis k basis) (fam.digest basis)
        (fam.publicComm basis) (fam.proofOf basis O) (Fin.last (fam.runSrs basis O).k))))
      (fun i : Fin (fam.runSrs basis O).k => expandPre C
        (O (ipaPrefixes (srsOfBasis k basis) (fam.digest basis) (fam.publicComm basis)
          (fam.proofOf basis O) i.castSucc)))
  rw [← hu', ← hc']
  exact hacc

end KimchiFamily

end WinBridge

/-! ## 14. The transcript node machinery the charge consumes

Node-determinacy says every exclusion set of arm (4) is a function of the run's node
at a *strictly earlier* squeeze. Feeding that into
`Bulletproof.Forking.adaptive_badSet_ofPrefix_union_expand_measure_le` — whose `pre` argument is
a retraction `ι → κ → T → T` on nodes and whose `hpre` demands that it move every guarded node —
needs one further piece, and it is the only genuinely new mathematics on that path: a retraction
taking the node at a squeeze to the node at any strictly earlier squeeze OF THE SAME RUN,
together with the fact that the two are distinct.

Both are consequences of the shape of `KimchiNode`. A node records the digest, the public
commitment chunks, the emitted proof's group data with everything absorbed after its own squeeze
gated to `none`, and its own squeeze tag. Re-gating those optional fields to an earlier squeeze
therefore reconstructs the earlier node exactly; and the tag component alone
already distinguishes the two (`regate_ne`), so distinctness needs no
injectivity assumption about the encoding — which is what makes this cheap where the IPA side
had to reason about `sg`. -/

section Regate

variable {nc k : ℕ}

/-- **The position of a squeeze in the deployed absorb schedule**: `β`, `γ`, `α`, `ζ`, `ξ`, `r`,
then the opening rounds in order, then the Schnorr squeeze. Project-local: it is schedule data
about `Kimchi.Verifier`'s sponge and has no Mathlib analogue. Phrased as a rank into `ℕ` rather
than as an inductive relation so that the re-gating case splits close by `omega`. -/
private def squeezeRank : Squeeze k → ℕ
  | .beta => 0
  | .gamma => 1
  | .alpha => 2
  | .zeta => 3
  | .polyscale => 4
  | .evalscale => 5
  | .ipaRound i => 6 + (i : ℕ)
  | .schnorr => 6 + k

/-- **Re-gating a node to another squeeze**. Keep the digest, the public
commitment chunks and the witness commitments — those are present at every node — and re-gate
each remaining optional field exactly as `nodeAt` gates it: the permutation commitment is absent
at `β`/`γ`, the quotient chunks also at `α`, the `ft(ζω)` value and the evaluations also at `ζ`,
the cross-terms are kept only up to the target round, and `δ`/`sg` only at the Schnorr squeeze.
Finally set the tag to the target.

This is the retraction `adaptive_badSet_ofPrefix_union_expand_measure_le` asks for; it is a left
inverse of the schedule only on nodes that really are a run's, which is all the
charge needs, since it is only ever applied to `nodeAt _ _ _ _`. -/
private def regate (t : KimchiNode C nc k) (s : Squeeze k) : KimchiNode C nc k where
  idx := s
  pre :=
    { digest := t.pre.digest
      publicComm := t.pre.publicComm
      wComm := t.pre.wComm
      zComm := match s with
        | .beta | .gamma => none
        | _ => t.pre.zComm
      tComm := match s with
        | .beta | .gamma | .alpha => none
        | _ => t.pre.tComm
      ftEval1 := match s with
        | .beta | .gamma | .alpha | .zeta => none
        | _ => t.pre.ftEval1
      evals := match s with
        | .beta | .gamma | .alpha | .zeta => none
        | _ => t.pre.evals }
  lr := match s with
    | .ipaRound i => fun j => if (j : ℕ) ≤ (i : ℕ) then t.lr j else none
    | .schnorr => t.lr
    | _ => fun _ => none
  delta := match s with
    | .schnorr => t.delta
    | _ => none
  sg := match s with
    | .schnorr => t.sg
    | _ => none

/-- **Re-gating to a different squeeze moves the node** — the `hpre` hypothesis of
`adaptive_badSet_ofPrefix_union_expand_measure_le`, whose guard is exactly the tag condition
assumed here. The tag component alone separates the two, so no injectivity assumption about the
rest of the encoding is needed. -/
private theorem regate_ne (t : KimchiNode C nc k) {s : Squeeze k} (h : t.idx ≠ s) :
    regate t s ≠ t := by
  intro he
  apply h
  have hx : (regate t s).idx = t.idx := by rw [he]
  exact hx.symm

/-- **Re-gating is the earlier node of the same run**, in the non-strict form the prefix decoder
consumes: for any run and any two squeezes with `rank s' ≤ rank s`, re-gating the run's node at
`s` to `s'` gives the run's node at `s'`. At `s' = s` this says the retraction fixes the node it
is already at, which is what `PrefixDecode.chainAt_prefixes` needs at its diagonal.

Case check over the pair of tags: the node at a squeeze is defined by exactly the gating the
retraction performs, so every pre-opening field matches on the nose. The only non-definitional
case is round against round, where the retraction truncates a longer cross-term prefix to a
shorter one — and `i ≤ i'` is exactly what the schedule order supplies. -/
private theorem regate_nodeAt_le (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
    (cp : KimchiProof C nc k) {s s' : Squeeze k} (h : squeezeRank s' ≤ squeezeRank s) :
    regate (nodeAt digest publicComm cp s) s' = nodeAt digest publicComm cp s' := by
  cases s' with
  | beta => rfl
  | gamma => rfl
  | alpha => cases s <;> first | rfl | (exact absurd h (by simp only [squeezeRank]; omega))
  | zeta => cases s <;> first | rfl | (exact absurd h (by simp only [squeezeRank]; omega))
  | polyscale => cases s <;> first | rfl | (exact absurd h (by simp only [squeezeRank]; omega))
  | evalscale => cases s <;> first | rfl | (exact absurd h (by simp only [squeezeRank]; omega))
  | schnorr => cases s <;> first | rfl | (exact absurd h (by simp only [squeezeRank]; omega))
  | ipaRound i =>
    cases s with
    | ipaRound i' =>
      have hii : (i : ℕ) ≤ (i' : ℕ) := by simp only [squeezeRank] at h; omega
      simp only [regate, nodeAt, KimchiNode.mk.injEq, true_and, and_true]
      funext j
      by_cases hj : (j : ℕ) ≤ (i : ℕ)
      · simp only [if_pos hj, if_pos (hj.trans hii)]
      · simp only [if_neg hj]
    | schnorr => rfl
    | _ => exact absurd h (by simp only [squeezeRank]; omega)

/-! ### The prefix decoder the adaptive charge asks for

`Zcash.Snark.PrefixDecode` is the ironwood interface a run's transcript prefixes must meet
before either adaptive bound applies: a round index, a retraction to an earlier round, and the
two agreement laws plus distinctness. `regate` supplies the retraction and
`regate_nodeAt_le`/`regate_ne` the laws, so the whole structure is assembled below with no new
mathematics. It is the direct analogue of `Bulletproof.Forking.Deployed.prefixDecode_nodes`,
whose `chainAt` is the same field-truncation written inline. -/

/-- The squeeze the opening argument's index `j` names: round `j` while `j < k`, then the
Schnorr squeeze at `j = k`. Exactly the tag `ipaPrefixes` selects. -/
private def ipaSqueeze (j : Fin (k + 1)) : Squeeze k :=
  if h : (j : ℕ) < k then .ipaRound ⟨(j : ℕ), h⟩ else .schnorr

/-- The opening argument's squeezes are the last `k + 1` of the schedule, in order. -/
private theorem squeezeRank_ipaSqueeze (j : Fin (k + 1)) :
    squeezeRank (ipaSqueeze j) = 6 + (j : ℕ) := by
  unfold ipaSqueeze
  by_cases h : (j : ℕ) < k
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]
    have := j.isLt
    simp only [squeezeRank]
    omega

/-- **The opening-argument round a node belongs to** — the `roundOf` of the prefix decoder.
Pre-opening nodes are given round `0`; they are never reached, since `chainAt_ne` is only ever
applied at a node whose round is positive. -/
private def kimchiRoundOf (t : KimchiNode C nc k) : ℕ :=
  match t.idx with
  | .ipaRound i => (i : ℕ)
  | .schnorr => k
  | _ => 0

/-- The IPA prefix at index `j` is the run's node at `ipaSqueeze j` — the two spellings of the
same `dite`, named so the decoder's obligations can be rewritten into `nodeAt` form. -/
private theorem ipaPrefixes_eq_nodeAt (σ : SRS C.Point) (digest : C.ScalarField)
    (publicComm : Fin nc → C.Point) (cp : KimchiProof C nc σ.k) (j : Fin (σ.k + 1)) :
    ipaPrefixes σ digest publicComm cp j = nodeAt digest publicComm cp (ipaSqueeze j) := rfl

/-- **The kimchi prefixes decode** — the `PrefixDecode` witness the adaptive bounds take as
their `D`. The round of a node is the index of its own squeeze, the chain of a node is `regate`
at the target squeeze, the two agreement laws are `regate_nodeAt_le` (through
`squeezeRank_ipaSqueeze`), and distinctness is `regate_ne`, i.e. the tag component alone.

This is what makes the structured `KimchiNode` pay off, exactly as `IpaNode.idx` does on the IPA
side: no injectivity assumption about a transcript encoding is needed anywhere. -/
private def kimchiPrefixDecode (σ : SRS C.Point) (digest : C.ScalarField)
    (publicComm : Fin nc → C.Point) :
    Zcash.Snark.PrefixDecode (KimchiNode C nc σ.k) (σ.k + 1)
      (ipaPrefixes σ digest publicComm) where
  roundOf := kimchiRoundOf
  chainAt t j := regate t (ipaSqueeze j)
  roundOf_prefixes := by
    intro p j
    rw [ipaPrefixes_eq_nodeAt]
    show kimchiRoundOf (nodeAt digest publicComm p (ipaSqueeze j)) = (j : ℕ)
    unfold ipaSqueeze kimchiRoundOf
    by_cases h : (j : ℕ) < σ.k
    · rw [dif_pos h]; rfl
    · rw [dif_neg h]
      show σ.k = (j : ℕ)
      have := j.isLt
      omega
  chainAt_prefixes := by
    intro p j i hij
    rw [ipaPrefixes_eq_nodeAt, ipaPrefixes_eq_nodeAt]
    refine regate_nodeAt_le digest publicComm p ?_
    rw [squeezeRank_ipaSqueeze, squeezeRank_ipaSqueeze]
    omega
  chainAt_ne := by
    intro t i hlt
    refine regate_ne t ?_
    intro he
    simp only [kimchiRoundOf, he, ipaSqueeze] at hlt
    by_cases h : (i : ℕ) < σ.k
    · rw [dif_pos h] at hlt
      have h2 : (i : ℕ) < (i : ℕ) := hlt
      omega
    · rw [dif_neg h] at hlt
      exact h hlt

/-! ### Agreement at a node propagates backwards along the schedule

`repPrefix_of_absorbedBy` and `tPrefix_of_zetaNode` take node agreement at the row's OWN
absorbing squeeze, while a Schwartz–Zippel charge has agreement at the (later) squeeze whose
challenge the exclusion set is about. The retraction closes that gap in one rewrite, and the two
corollaries below are the form node-determinacy will consume for every row
family. -/

section RegateFamily

variable [Module C.ScalarField C.Point]

namespace KimchiFamily

variable {n : ℕ} [NeZero n] (fam : KimchiFamily C nc k n)

/-- **Two runs that agree at a node agree at every earlier node.** The node at `s'` is the
retraction of the node at `s` (`regate_nodeAt_le`), and the retraction is a function. -/
private theorem nodesOf_eq_of_rank_le (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O O' : Coins C nc k) {s s' : Squeeze k} (h : squeezeRank s' ≤ squeezeRank s)
    (hnode : fam.nodesOf basis O s = fam.nodesOf basis O' s) :
    fam.nodesOf basis O s' = fam.nodesOf basis O' s' := by
  have h1 : fam.nodesOf basis O s' = regate (fam.nodesOf basis O s) s' :=
    (regate_nodeAt_le _ _ _ h).symm
  have h2 : fam.nodesOf basis O' s' = regate (fam.nodesOf basis O' s) s' :=
    (regate_nodeAt_le _ _ _ h).symm
  rw [h1, h2, hnode]

/-- **AGM faithfulness read at a later node**: a stream row's coefficient vector and blinder agree
between two runs as soon as the runs agree at ANY node at or after the row's absorbing squeeze. -/
private theorem repPrefix_of_rank_le (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O O' : Coins C nc k) (i : Fin (nc + 1 + tailRowCount * nc)) {s : Squeeze k}
    (h : squeezeRank (absorbedBy (k := k) i) ≤ squeezeRank s)
    (hnode : fam.nodesOf basis O s = fam.nodesOf basis O' s) :
    fam.aRef basis O i = fam.aRef basis O' i ∧ fam.ρRef basis O i = fam.ρRef basis O' i :=
  fam.repPrefix_of_absorbedBy basis O O' i rfl
    (fam.nodesOf_eq_of_rank_le basis O O' h hnode)

/-- The quotient-chunk twin of `repPrefix_of_rank_le`: `aT`/`ρT` agree as soon as the two runs
agree at any node at or after `ζ`. -/
private theorem tPrefix_of_rank_le (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O O' : Coins C nc k) (j : Fin ((fam.adversary basis).run O).tComm.size)
    (j' : Fin ((fam.adversary basis).run O').tComm.size) (hj : (j : ℕ) = (j' : ℕ))
    {s : Squeeze k} (h : squeezeRank (Squeeze.zeta : Squeeze k) ≤ squeezeRank s)
    (hnode : fam.nodesOf basis O s = fam.nodesOf basis O' s) :
    fam.aT basis O j = fam.aT basis O' j' ∧ fam.ρT basis O j = fam.ρT basis O' j' :=
  fam.tPrefix_of_zetaNode basis O O' j j' hj (fam.nodesOf_eq_of_rank_le basis O O' h hnode)

end KimchiFamily

end RegateFamily

end Regate

/-! ## 15. Arm (1): the presence summand

With the varying-base tower of `Bulletproof/Forking/Game.lean` in place, arm (1) is assembly.
`kimchiExtract_failure_measure_prod_le_of_stableBase` prices, over the joint measure on (setup
index, oracle table) pairs, the event "the run wins at its own setup and the extractor returns
nothing"; the presence arm is contained in it by `winsAt_of_wins` on the win conjunct and by
`ipaAttempt_eq_none_of_attempt` on the failure conjunct.

One instantiation choice is worth recording, because it is what makes the assembly go through at
all. The abstract bound's `hrep` obligation is universally quantified over the proof argument
`p`, while a `KimchiFamily` supplies an algebraic-group representation only for the proof its OWN
adversary emitted. The resolution is to instantiate the claim map `κ` at the run's own proof —
`fun _ O => claimTriple (runClaim … (A.run O) O)`, ignoring `p`. That is not a weakening: `κ` is
only ever applied at `p = A.run O` (in `WinsAt`, in `ClaimStable` and in the measured event
alike), so the p-ignoring map is *definitionally* the map at every point either statement reads,
while `hrep` and `huOf` become the family's `hPOf` and `rfl` at every `p`. -/

section Presence

variable [Module C.ScalarField C.Point]

namespace KimchiFamily

variable {nc k n : ℕ} [NeZero n] (fam : KimchiFamily C nc k n)

/-- **The key gate does not create presence failures.** `attempt` returns `none` exactly when the
IPA layer did, so arm (1) is the IPA layer's own presence event — the fact the gate's docstring
records as "arm (1) is untouched", here proved. -/
private theorem ipaAttempt_eq_none_of_attempt
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (h : fam.attempt basis O coins = none) :
    fam.ipaAttempt basis O coins = none := by
  classical
  rw [attempt] at h
  cases hi : fam.ipaAttempt basis O coins with
  | none => rfl
  | some x =>
    rw [hi] at h
    cases x with
    | inl a => cases hk : fam.keyBreak basis O <;> rw [hk] at h <;> simp at h
    | inr r => simp at h

/-- **The presence summand**: the measure of arm (1) over the joint
uniform sampling of the setup index and the oracle table is at most
`(Q + k + 1) · 3 / |Prechallenge|`.

`kimchiExtract_failure_measure_prod_le_of_stableBase` at the sampled setups
`srsOfBasis k (augOfSetup (scalarBasis B s))`, with the claim map the run's claim triple, the
base map the run's WARM base `fam.warmBase`, the representation map the family's
polyscale-combined coefficient vector and blinder, and the prechallenge alphabet. Its hypotheses
are the two curve facts about the expansion (supplied), the family's query bound, commit-then-
challenge (`kimchiDecodesFromPrefixes`) and distinct chronological prefixes
(`kimchiPrefixDecode`), completeness of the fork tape (supplied), base stability
(`KimchiFamily.baseStable_warmBase`) and claim stability (`claimStable_runClaimTriple`). The
containment is `winsAt_of_wins` and `ipaAttempt_eq_none_of_attempt`.

The base-stable form rather than the `_of_stableU` one is what the warm base needs: `_of_stableU`
asks that the base factor through the claimed value, which the warm base does NOT do — it is
squeezed from the post-`ζ` sponge state, a function of the whole pre-opening payload. What it
does satisfy is the weaker `BaseStable`, and that is exactly `_of_stableBase`'s `hbase`.

The two expansion facts are hypotheses rather than instances because `expandPre` is injective and
nonvanishing per curve (`expandPre_vesta_injective` and its three siblings), not generically. -/
private theorem acceptExtractionFailure_measure_prod_le
    (hsmul : ∀ (z : C.ScalarField) (P : C.Point), z • P = z.val • P)
    (hexp_inj : Function.Injective (expandPre C))
    (hexp_ne : ∀ q : Prechallenge, expandPre C q ≠ 0)
    (B : C.Point) (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hcoins : coins.Complete) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C nc k)).toOuterMeasure
        {q | q.2 ∈ fam.acceptExtractionFailure
          (augOfSetup (Zcash.Snark.scalarBasis B q.1)) coins}
      ≤ (fam.Q + k + 1) * (3 / Fintype.card Prechallenge) := by
  classical
  refine le_trans (MeasureTheory.measure_mono ?_)
    (kimchiExtract_failure_measure_prod_le_of_stableBase
      (S := SetupIndex (2 ^ k) → C.ScalarField)
      (fun s => srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B s)))
      (fun s _ O => claimTriple
        (runClaim (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B s)))
          (fam.cvk (augOfSetup (Zcash.Snark.scalarBasis B s)))
          (fam.pub (augOfSetup (Zcash.Snark.scalarBasis B s)))
          (fam.digest (augOfSetup (Zcash.Snark.scalarBasis B s)))
          ((fam.adversary (augOfSetup (Zcash.Snark.scalarBasis B s))).run O) O))
      (fun s _ O => (fam.pgOf (augOfSetup (Zcash.Snark.scalarBasis B s)) O,
        fam.pwOf (augOfSetup (Zcash.Snark.scalarBasis B s)) O))
      (fun s _ O => fam.hPOf (augOfSetup (Zcash.Snark.scalarBasis B s)) O)
      (fun s _ O => fam.warmBase (augOfSetup (Zcash.Snark.scalarBasis B s)) O)
      (expandPre C) hexp_inj hexp_ne
      (fun s => fam.adversary (augOfSetup (Zcash.Snark.scalarBasis B s)))
      (fun s => fam.queryBound (augOfSetup (Zcash.Snark.scalarBasis B s)))
      (fun _ cp => Bulletproof.Ipa.Forking.toOpening cp.opening)
      (fun s => ipaPrefixes (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B s)))
        (fam.digest (augOfSetup (Zcash.Snark.scalarBasis B s)))
        (fam.publicComm (augOfSetup (Zcash.Snark.scalarBasis B s))))
      (fun s => kimchiDecodesFromPrefixes
        (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B s)))
        (fam.digest (augOfSetup (Zcash.Snark.scalarBasis B s)))
        (fam.publicComm (augOfSetup (Zcash.Snark.scalarBasis B s))))
      (fun s => kimchiPrefixDecode (srsOfBasis k (augOfSetup (Zcash.Snark.scalarBasis B s)))
        (fam.digest (augOfSetup (Zcash.Snark.scalarBasis B s)))
        (fam.publicComm (augOfSetup (Zcash.Snark.scalarBasis B s))))
      (fun s => fam.baseStable_warmBase (augOfSetup (Zcash.Snark.scalarBasis B s)))
      (fun s => fam.claimStable_runClaimTriple (augOfSetup (Zcash.Snark.scalarBasis B s)))
      (fun _ => coins) (fun _ => hcoins) (k := k) (fun _ => le_rfl))
  rintro ⟨s, O⟩ ⟨hwin, hnone⟩
  exact ⟨fam.winsAt_of_wins hsmul _ O hwin,
    fam.ipaAttempt_eq_none_of_attempt _ O coins hnone⟩

end KimchiFamily

end Presence

/-! ## 16. Arm (4): the algebraic summand

The last open arm. `arm4_hits_badChallenge` (section 12) contains arm (4) in a seven-fold
disjunction of bad-challenge memberships; this section prices that union.

The charge is `Bulletproof.Forking.adaptive_badSet_ofPrefix_union_expand_measure_le`, whose
exclusion sets are functions of a *transcript node* together with the oracle's answers at
strictly earlier nodes. The seven sets of arm (4) are instead written as functions of the whole
oracle table — they are built from the adversary's own representations — so the two have to be
reconciled. That reconciliation is the mathematical content of the section, and it splits in
two:

* **the sets are node-determined** (`szBadRun_agree`): two tables whose runs share the node at
  the guarded squeeze, and whose oracle answers agree at the retracted earlier nodes, give the
  *same* seven sets. This is what says the adversary cannot pick its exclusion set after seeing
  the challenge the set is about;
* **the agreement form of the charge**
  (`adaptive_badSet_ofPrefix_union_expand_measure_le_of_agree`): a choice
  function turns a table-indexed family satisfying that agreement law into the node-indexed
  family the abstract bound wants, and at any given table the two events are literally the same
  set.

Everything else is bookkeeping: the index set is `Fin szSets`, the node selector reads the
run's node at that index's squeeze, the retraction is `regate` (section 14), and the
per-index budgets sum to `szBudget` by construction. -/

section Arm4Measure

/-! ### The squeeze expansions are injective

`adaptive_badSet_ofPrefix_union_expand_measure_le` reads each prechallenge into the scalar field
through its own map and needs every one of them injective. Off `β`/`γ` that is the endomorphism
expansion, injective per curve (`expandPre_vesta_injective` and its Pallas twin); at `β`/`γ` it
is the plain cast of a natural number below `2 ^ 128`, which is injective because both Pasta
scalar fields have far more than `2 ^ 128` elements. -/

/-- **The prechallenge cast is injective into any field with at least `2 ^ 128` elements.**

Project-local: `Prechallenge` is `Bulletproof`'s own `Fin (2 ^ 128)` and `C.ScalarField` is
`ZMod C.scalar`, so this is `ZMod.natCast_eq_natCast_iff'` plus `Nat.mod_eq_of_lt` at both
sides — but the composite is used once per curve and is worth naming. -/
private theorem natCast_prechallenge_injective {m : ℕ} (hm : 2 ^ 128 ≤ m) :
    Function.Injective (fun q : Prechallenge => ((q : ℕ) : ZMod m)) := by
  intro a b h
  have ha : (a : ℕ) < m := lt_of_lt_of_le a.isLt hm
  have hb : (b : ℕ) < m := lt_of_lt_of_le b.isLt hm
  refine Fin.ext ?_
  have h' := (ZMod.natCast_eq_natCast_iff' (a : ℕ) (b : ℕ) m).mp h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'

/-- **Every squeeze expansion is injective**. `squeezeExpand` is
the plain cast at `β`/`γ` and `expandPre` everywhere else, so injectivity of the two constituent
maps is exactly what the statement needs; both are supplied per curve, neither holds generically,
which is why they are hypotheses. -/
private theorem squeezeExpand_injective {k : ℕ} (C : Ipa.CommitmentCurve)
    (hcast : Function.Injective (fun q : Prechallenge => ((q : ℕ) : C.ScalarField)))
    (hexp : Function.Injective (expandPre C)) (s : Squeeze k) :
    Function.Injective (squeezeExpand C s) := by
  cases s with
  | beta => exact hcast
  | gamma => exact hcast
  | _ => exact hexp

/-! ### The quotient chunk array is fixed by the `ζ` node -/

/-- **Two proofs with the same `ζ` node carry the same quotient chunks.**
The `ζ` node records `tComm` as a total function on `Fin (7 · nc)`
returning the optional array entry there, and the wire invariant `tComm_le` bounds both arrays'
sizes by `7 · nc`, so every out-of-range read is `none` on both sides and `Array.ext_getElem?`
closes.

This is the `htc` step of `kimchiProof_eq_of_preData_eq` extracted so that it is available at
`ζ`, where `ftEval1`/`evals` are still `none` and that lemma does not apply. -/
private theorem tComm_eq_of_zetaNode {nc k : ℕ} (digest : C.ScalarField)
    (publicComm : Fin nc → C.Point) (cp cp' : KimchiProof C nc k)
    (h : nodeAt digest publicComm cp (Squeeze.zeta : Squeeze k)
      = nodeAt digest publicComm cp' Squeeze.zeta) :
    cp.tComm = cp'.tComm := by
  have ht := congrArg (fun t => t.pre.tComm) h
  simp only [nodeAt, Option.some.injEq] at ht
  refine Array.ext_getElem? fun i => ?_
  by_cases hi : i < 7 * nc
  · exact congrFun ht ⟨i, hi⟩
  · rw [Array.getElem?_eq_none (by have := cp.tComm_le; omega),
      Array.getElem?_eq_none (by have := cp'.tComm_le; omega)]

/-! ### Locality of the assembled objects

The seven exclusion sets are built from `runW`, `runZ`, `ftChunkAssembly`, `badXiOf` and
`badROf`. Each of the five reads strictly less than its argument list suggests, and saying so is
what lets two runs that agree only at an early node be shown to produce the same set. The
statements below are exactly the reads that matter:

* `runW`/`runZ` mention the emitted proof only in the TYPE of their coefficient argument (the
  flat arity `(runInput C σ cvk cp pub).commitments.size` is reducibly `nc + 1 + tailRowCount·nc`,
  independent of `cp`), so two runs with different proofs but agreeing coefficient vectors at the
  witness and accumulator stream positions assemble the same polynomials;
* `ftChunkAssembly` is a function of the chunk count and the chunk coefficient vectors;
* `badXiOf`/`badROf` read the SRS only through `σ.k`, so overriding the transcript-derived base
  `U` — which `runSrs` does, per run — leaves them unchanged. -/

section Locality

/-- **`runW` is local to the witness stream positions**. The two proofs are
allowed to differ: the coefficient argument's type mentions the proof, but only through a flat
arity that does not depend on it. -/
private theorem runW_congr_of_agree {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp cp' : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (aRef aRef' : Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ σ.k) → C.ScalarField)
    (h : ∀ (col : Fin wCols) (c : Fin nc),
      aRef (streamPos nc (wRow col) c) = aRef' (streamPos nc (wRow col) c)) :
    runW σ cvk cp pub aRef = runW σ cvk cp' pub aRef' := by
  funext col
  exact congrArg (assembledRow σ.k nc) (funext fun c => h col c)

/-- **`runZ` is local to the accumulator stream position** — the `runW_congr_of_agree` twin. -/
private theorem runZ_congr_of_agree {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp cp' : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (aRef aRef' : Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ σ.k) → C.ScalarField)
    (h : ∀ c : Fin nc, aRef (streamPos nc zRow c) = aRef' (streamPos nc zRow c)) :
    runZ σ cvk cp pub aRef = runZ σ cvk cp' pub aRef' :=
  congrArg (assembledRow σ.k nc) (funext h)

/-- **The assembled quotient is a function of the chunk count and the chunk vectors.**
Stated with two independently-typed chunk index families related by
equal underlying naturals, which is the shape the run-agreement argument produces. -/
private theorem ftChunkAssembly_congr_of_agree {F : Type*} [Field F] (k : ℕ) {nt nt' : ℕ}
    (aT : Fin nt → Fin (2 ^ k) → F) (aT' : Fin nt' → Fin (2 ^ k) → F) (hn : nt = nt')
    (h : ∀ (j : Fin nt) (j' : Fin nt'), (j : ℕ) = (j' : ℕ) → aT j = aT' j') :
    ftChunkAssembly k nt aT = ftChunkAssembly k nt' aT' := by
  subst hn
  exact congrArg (ftChunkAssembly k nt) (funext fun j => h j j rfl)

/-- **`badXiOf` does not read the transcript-derived base**.
Definitional: the set reads the SRS only through `σ.k`, which a `U`-override preserves. -/
private theorem badXiOf_setBase {G : Type*} (σ : SRS G) (u : G) {m : ℕ}
    (aw₀ : Fin m → Fin (2 ^ σ.k) → C.ScalarField) (x : Fin evalPts → C.ScalarField)
    (E : Fin m → Fin evalPts → C.ScalarField) :
    badXiOf ({σ with U := u}) aw₀ x E = badXiOf σ aw₀ x E := rfl

/-- **`badROf` does not read the transcript-derived base** — the `badXiOf_setBase` twin. -/
private theorem badROf_setBase {G : Type*} (σ : SRS G) (u : G) {m : ℕ}
    (aw₀ : Fin m → Fin (2 ^ σ.k) → C.ScalarField) (x : Fin evalPts → C.ScalarField)
    (E : Fin m → Fin evalPts → C.ScalarField) (ξ : C.ScalarField) :
    badROf ({σ with U := u}) aw₀ x E ξ = badROf σ aw₀ x E ξ := rfl

/-- **The claim's evaluation points and claimed evaluations do not read the opening.** Two runs
whose proofs agree away from `opening`, at the same four fq-side challenges, present the same
`pointFn` and the same `evalFn` — the two components `badXiOf` and `badROf` read. The fr-side
`v`/`u` are free because neither component reads them. -/
private theorem runInputWith_pointFn_evalFn_congr {nc : ℕ} (σ : SRS C.Point)
    (cvk : KimchiVK C nc) (pub : Array C.ScalarField) (cp cp' : KimchiProof C nc σ.k)
    (beta gamma alpha zeta v u v' u' : C.ScalarField) (o : Ipa.Proof C σ.k)
    (hcp : cp = { cp' with opening := o }) :
    (runInputWith σ cvk cp pub beta gamma alpha zeta v u).pointFn
        = (runInputWith σ cvk cp' pub beta gamma alpha zeta v' u').pointFn
      ∧ (runInputWith σ cvk cp pub beta gamma alpha zeta v u).evalFn
        = (runInputWith σ cvk cp' pub beta gamma alpha zeta v' u').evalFn := by
  subst hcp
  exact ⟨rfl, rfl⟩

/-- The batched claim's polyscale slot is the handed-in `v`. Definitional, but named: reaching it
through `runInputWith`'s `let`-chain by unification alone is what makes an `isDefEq` at that
projection blow the recursion budget. -/
private theorem runInputWith_polyscale {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField) :
    (runInputWith σ cvk cp pub beta gamma alpha zeta v u).polyscale = v := rfl

/-- The batched claim's evalscale slot is the handed-in `u` — the `runInputWith_polyscale`
twin, named for the same reason. -/
private theorem runInputWith_evalscale {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField) :
    (runInputWith σ cvk cp pub beta gamma alpha zeta v u).evalscale = u := rfl

end Locality

/-! ### The seven exclusion sets, as a family indexed by `Fin szSets`

`adaptive_badSet_ofPrefix_union_expand_measure_le` prices a union over a finite index set, so the
seven disjuncts of `arm4_hits_badChallenge` are repackaged as a `Fin szSets`-indexed family
of finite sets together with a per-index budget. The budgets are the seven per-squeeze cardinality
bounds, so their total is `szBudget` on the nose. -/

section BadRun

variable [Module C.ScalarField C.Point]

/-- **The squeeze each of the seven exclusion sets guards**: `β`, `γ`, `α`, `ζ` for the four
Schwartz–Zippel sets, `ζ` again for the boundary set, then the fr-side `ξ` and `r`. -/
private def szSqueeze {k : ℕ} : Fin szSets → Squeeze k :=
  ![Squeeze.beta, Squeeze.gamma, Squeeze.alpha, Squeeze.zeta, Squeeze.zeta,
    Squeeze.polyscale, Squeeze.evalscale]

/-- **The per-index budget** of the seven exclusion sets, in the order `szSqueeze` names
them. -/
private def szCard (nc n zkRows : ℕ) : Fin szSets → ℕ :=
  ![7 * (n - zkRows), 7 * (n - zkRows),
    n * (Index.gateAlphaCount + Index.permAlphaCount - 1), Index.degreeBound n, 2,
    2 * (nc + 1 + tailRowCount * nc - 1), 1]

/-- **The budgets sum to the Schwartz–Zippel budget.** `szBudget` was *defined* as this sum;
`Fin.sum_univ_seven` unfolds the sum and `omega` does the regrouping (the two `β`/`γ` terms are
collected into the `2 *` of the budget). -/
private theorem szCard_sum (nc n zkRows : ℕ) :
    ∑ i : Fin szSets, szCard nc n zkRows i = szBudget nc n zkRows := by
  have h : ∑ i : Fin szSets, szCard nc n zkRows i
      = 7 * (n - zkRows) + 7 * (n - zkRows)
        + n * (Index.gateAlphaCount + Index.permAlphaCount - 1) + Index.degreeBound n + 2
        + 2 * (nc + 1 + tailRowCount * nc - 1) + 1 := by
    rw [Fin.sum_univ_seven]
    rfl
  rw [h]
  unfold szBudget
  omega

namespace KimchiFamily

variable {nc k n : ℕ} [NeZero n] (fam : KimchiFamily C nc k n)

/-- **The seven exclusion sets of arm (4), at the run**. Exactly the seven
sets named in `arm4_hits_badChallenge`, evaluated at the run the table produces: the `β`, `γ`,
`α` and `ζ` Schwartz–Zippel sets of the run's assembled columns, accumulator and quotient, the
two-point `ζ` boundary set, and the run's own `ξ` and `r` sets. -/
private noncomputable def szBadRun (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) : Fin szSets → Finset C.ScalarField :=
  ![Protocol.soundBadB fam.idx
      (runW (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
        (fam.aRef basis O)),
    Protocol.soundBadG fam.idx
      (runW (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
        (fam.aRef basis O))
      (fam.readsOf basis O Squeeze.beta),
    Protocol.soundBadA fam.idx (pubView fam.idx (fam.pub basis))
      (runW (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
        (fam.aRef basis O))
      (runZ (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
        (fam.aRef basis O))
      (fam.readsOf basis O Squeeze.beta) (fam.readsOf basis O Squeeze.gamma),
    Protocol.soundBadZ fam.idx (pubView fam.idx (fam.pub basis))
      (runW (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
        (fam.aRef basis O))
      (runZ (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
        (fam.aRef basis O))
      (fam.readsOf basis O Squeeze.beta) (fam.readsOf basis O Squeeze.gamma)
      (fam.readsOf basis O Squeeze.alpha)
      (ftChunkAssembly k (fam.proofOf basis O).tComm.size (fam.aT basis O)),
    zetaBoundaryBad fam.idx,
    badXiOf (fam.runSrs basis O) (fam.aRef basis O) (fam.claim basis O).pointFn
      (fam.claim basis O).evalFn,
    badROf (fam.runSrs basis O) (fam.aRef basis O) (fam.claim basis O).pointFn
      (fam.claim basis O).evalFn (fam.claim basis O).polyscale]

/-- **Each exclusion set costs its budget term, on *every* table** —
winning or not, opened or not. This is why `runBounds_of_chunking` was isolated: the adaptive
charge must bound the sets on tables at which nothing was extracted, where the run-soundness
root's hypothesis stack is unavailable. The `ζ` bound is instantiated at the run's own assembled
quotient by `runBounds_zeta_at_assembly`, the boundary set costs `2` by inspection, and the two
fr-side sets are the opening argument's own counting bounds at the flat arity. -/
private theorem szBadRun_card_le (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) (i : Fin szSets) :
    (fam.szBadRun basis O i).card ≤ szCard nc n fam.idx.zkRows i := by
  have hb : RunBounds (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O)
      (fam.pub basis) fam.idx (fam.aRef basis O) :=
    runBounds_of_chunking (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O)
      (fam.pub basis) fam.idx fam.hnc fam.hkn (fam.aRef basis O)
  fin_cases i
  · exact hb.1
  · exact hb.2.1 _
  · exact hb.2.2.1 _ _
  · exact runBounds_zeta_at_assembly (srsOfBasis k basis) (fam.cvk basis)
      (fam.proofOf basis O) (fam.pub basis) fam.idx (fam.aRef basis O) (fam.aT basis O)
      fam.hkn (fam.htpos basis O) hb _ _ _
  · exact card_zetaBoundaryBad_le fam.idx
  · exact card_badXiOf_le _ _ _ _
  · exact card_badROf_le _ _ _ _ _

end KimchiFamily

/-! ### The index bookkeeping the charge consumes

The node selector reads the run's node at the guarded squeeze; the guard is "this is a
pre-opening node", phrased as a bound on the squeeze rank; and the retraction sends a node to
the run's node at an earlier pre-opening squeeze. The retraction's first branch — which sends a
node to its own Schnorr re-gating when the requested squeeze is the node's own — exists only so
that distinctness holds for *every* `j`, including the degenerate one naming `t`'s own squeeze;
the exclusion set at that index never reads that coordinate. -/

/-- **Every flat stream row is absorbed by `ζ`.** `absorbedBy` returns `β`, `ζ` or `α`, of ranks
`0`, `3` and `2`, so no row's absorbing squeeze is later than `ζ` — which is what makes the two
fr-side exclusion sets (read at `ξ` and `r`, of ranks `4` and `5`) blind to the challenge they
guard. -/
private theorem squeezeRank_absorbedBy_le_three {nc k : ℕ}
    (r : Fin (nc + 1 + tailRowCount * nc)) :
    squeezeRank (absorbedBy (k := k) r) ≤ 3 := by
  unfold absorbedBy
  split_ifs <;> simp [squeezeRank]

/-- **The retraction to an earlier pre-opening node**, at the schedule. At a node
whose own squeeze is `s`, coordinate `j` names the run's node at `preSqueeze j` whenever that
squeeze is STRICTLY earlier in the schedule; otherwise the retraction falls back on the Schnorr
re-gating, which is never the node itself, so `hpre`'s distinctness holds at every coordinate.

The fallback exists only for the degenerate coordinates — the one naming `t`'s own squeeze, and
the ones naming later squeezes — which the exclusion set at that index never reads.

The index `i` of the exclusion set does not appear: the retraction is the same at all seven
sets, so carrying `i` would be an unused argument. -/
private def szPre {nc k : ℕ} (j : Fin preIpaChals) (t : KimchiNode C nc k) : KimchiNode C nc k :=
  if squeezeRank (preSqueeze j : Squeeze k) < squeezeRank t.idx then regate t (preSqueeze j)
  else regate t Squeeze.schnorr

omit [Module C.ScalarField C.Point] in
/-- **The retraction moves every guarded node** — `hpre` of
`adaptive_badSet_ofPrefix_union_expand_measure_le`. The tag component alone separates the two
(`regate_ne`): on the strict branch the ranks would have to coincide, and on the fallback branch
the guard rules out the Schnorr squeeze. -/
private theorem szPre_ne
    {nc k : ℕ} (t : KimchiNode C nc k) (ht : squeezeRank t.idx < 6) (j : Fin preIpaChals) :
    szPre j t ≠ t := by
  unfold szPre
  split
  · next hlt =>
    refine regate_ne t ?_
    intro he
    rw [he] at hlt
    omega
  · refine regate_ne t ?_
    intro he
    rw [he] at ht
    simp only [squeezeRank] at ht
    omega

omit [Module C.ScalarField C.Point] in
/-- **Every guarded squeeze is a pre-opening one** — `hnode`. The seven exclusion sets are read
at `β`, `γ`, `α`, `ζ`, `ζ`, `ξ`, `r`, whose ranks are `0`–`5`. -/
private theorem squeezeRank_szSqueeze_lt_six {k : ℕ} (i : Fin szSets) :
    squeezeRank (szSqueeze (k := k) i) < 6 := by
  fin_cases i
  · show (0 : ℕ) < 6; omega
  · show (1 : ℕ) < 6; omega
  · show (2 : ℕ) < 6; omega
  · show (3 : ℕ) < 6; omega
  · show (3 : ℕ) < 6; omega
  · show (4 : ℕ) < 6; omega
  · show (5 : ℕ) < 6; omega

namespace KimchiFamily

variable {nc k n : ℕ} [NeZero n] (fam : KimchiFamily C nc k n)

/-- **The transcript node at which the `i`-th exclusion set's challenge is read** — the run's own
node at `szSqueeze i`. -/
private def szNode (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (i : Fin szSets)
    (cp : KimchiProof C nc k) : KimchiNode C nc k :=
  nodeAt (fam.digest basis) (fam.publicComm basis) cp (szSqueeze i)

/-! #### What two runs sharing a node share

Each of the five assembled objects the exclusion sets read is recovered from data absorbed no
later than its own squeeze, so node agreement at a squeeze of at least that rank forces the
object. The five statements below are exactly the five reads. -/

/-- Witness-row coefficient vectors agree between two runs agreeing at ANY node: every witness
row is absorbed at `β`, of rank `0`. -/
private theorem aRef_wRow_eq (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O O' : Coins C nc k) {s : Squeeze k}
    (hnode : fam.nodesOf basis O s = fam.nodesOf basis O' s) (col : Fin wCols) (c : Fin nc) :
    fam.aRef basis O (streamPos nc (wRow col) c)
      = fam.aRef basis O' (streamPos nc (wRow col) c) := by
  refine (fam.repPrefix_of_rank_le basis O O' (streamPos nc (wRow col) c) ?_ hnode).1
  rw [absorbedBy_streamPos_of_two_le fam.hnc (wRow col) (by show 2 ≤ 8 + (col : ℕ); omega) c]
  exact Nat.zero_le _

/-- The assembled witness columns agree between two runs agreeing at any node. -/
private theorem runW_eq_of_node (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O O' : Coins C nc k) {s : Squeeze k}
    (hnode : fam.nodesOf basis O s = fam.nodesOf basis O' s) :
    runW (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
        (fam.aRef basis O)
      = runW (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O') (fam.pub basis)
        (fam.aRef basis O') :=
  runW_congr_of_agree _ _ _ _ _ _ _ (fam.aRef_wRow_eq basis O O' hnode)

/-- The assembled accumulator agrees between two runs agreeing at a node of rank at least `α`'s:
the accumulator row is absorbed at `α`. -/
private theorem runZ_eq_of_node (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O O' : Coins C nc k) {s : Squeeze k} (h2 : 2 ≤ squeezeRank s)
    (hnode : fam.nodesOf basis O s = fam.nodesOf basis O' s) :
    runZ (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O) (fam.pub basis)
        (fam.aRef basis O)
      = runZ (srsOfBasis k basis) (fam.cvk basis) (fam.proofOf basis O') (fam.pub basis)
        (fam.aRef basis O') :=
  runZ_congr_of_agree _ _ _ _ _ _ _ fun c =>
    (fam.repPrefix_of_rank_le basis O O' (streamPos nc zRow c)
      (by rw [absorbedBy_streamPos_zRow]; exact h2) hnode).1

/-- The quotient chunk arrays agree between two runs agreeing at a node of rank at least `ζ`'s —
`tComm_eq_of_zetaNode` after propagating the agreement back to the `ζ` node. -/
private theorem tComm_eq_of_node (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O O' : Coins C nc k) {s : Squeeze k} (h3 : 3 ≤ squeezeRank s)
    (hnode : fam.nodesOf basis O s = fam.nodesOf basis O' s) :
    (fam.proofOf basis O).tComm = (fam.proofOf basis O').tComm :=
  tComm_eq_of_zetaNode (fam.digest basis) (fam.publicComm basis) _ _
    (fam.nodesOf_eq_of_rank_le basis O O' (s' := Squeeze.zeta) h3 hnode)

/-- The assembled quotient polynomial agrees between two runs agreeing at a node of rank at least
`ζ`'s: the chunk count is fixed by `tComm_eq_of_node` and the chunk coefficient vectors by AGM
faithfulness at `ζ`. -/
private theorem ftAssembly_eq_of_node (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O O' : Coins C nc k) {s : Squeeze k} (h3 : 3 ≤ squeezeRank s)
    (hnode : fam.nodesOf basis O s = fam.nodesOf basis O' s) :
    ftChunkAssembly k (fam.proofOf basis O).tComm.size (fam.aT basis O)
      = ftChunkAssembly k (fam.proofOf basis O').tComm.size (fam.aT basis O') := by
  refine ftChunkAssembly_congr_of_agree k _ _
    (congrArg Array.size (fam.tComm_eq_of_node basis O O' h3 hnode)) fun j j' hj => ?_
  exact (fam.tPrefix_of_rank_le basis O O' j j' hj h3 hnode).1

/-- Two runs agreeing at a node of rank at least `ξ`'s emit the same proof up to its opening —
`kimchiProof_eq_of_preData_eq` at the `ξ` node, whose payload is the pre-opening data. -/
private theorem proofOf_eq_of_node (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O O' : Coins C nc k) {s : Squeeze k} (h4 : 4 ≤ squeezeRank s)
    (hnode : fam.nodesOf basis O s = fam.nodesOf basis O' s) :
    fam.proofOf basis O
      = { fam.proofOf basis O' with opening := (fam.proofOf basis O).opening } :=
  kimchiProof_eq_of_preData_eq (fam.digest basis) (fam.publicComm basis) _ _
    (congrArg KimchiNode.pre
      (fam.nodesOf_eq_of_rank_le basis O O' (s' := Squeeze.polyscale) h4 hnode))

/-- The run's batched claim reads the polyscale challenge at the run's own `ξ` node. -/
private theorem claim_polyscale (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) :
    (fam.claim basis O).polyscale = fam.readsOf basis O Squeeze.polyscale := by
  have h : fam.claim basis O = runInputWith (srsOfBasis k basis) (fam.cvk basis)
      (fam.proofOf basis O) (fam.pub basis)
      (fam.readsOf basis O Squeeze.beta) (fam.readsOf basis O Squeeze.gamma)
      (fam.readsOf basis O Squeeze.alpha) (fam.readsOf basis O Squeeze.zeta)
      (fam.readsOf basis O Squeeze.polyscale) (fam.readsOf basis O Squeeze.evalscale) := rfl
  rw [h, runInputWith_polyscale]

/-- The run's batched claim reads the evalscale challenge at the run's own `r` node. -/
private theorem claim_evalscale (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) :
    (fam.claim basis O).evalscale = fam.readsOf basis O Squeeze.evalscale := by
  have h : fam.claim basis O = runInputWith (srsOfBasis k basis) (fam.cvk basis)
      (fam.proofOf basis O) (fam.pub basis)
      (fam.readsOf basis O Squeeze.beta) (fam.readsOf basis O Squeeze.gamma)
      (fam.readsOf basis O Squeeze.alpha) (fam.readsOf basis O Squeeze.zeta)
      (fam.readsOf basis O Squeeze.polyscale) (fam.readsOf basis O Squeeze.evalscale) := rfl
  rw [h, runInputWith_evalscale]

/-- `badXiOf` at the run's own SRS is `badXiOf` at the sampled one: the set reads the SRS only
through `σ.k`, which the per-run `U`-override preserves. -/
private theorem badXiOf_runSrs (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) {m : ℕ} (aw₀ : Fin m → Fin (2 ^ k) → C.ScalarField)
    (x : Fin evalPts → C.ScalarField) (E : Fin m → Fin evalPts → C.ScalarField) :
    badXiOf (fam.runSrs basis O) aw₀ x E = badXiOf (srsOfBasis k basis) aw₀ x E :=
  badXiOf_setBase (srsOfBasis k basis) _ aw₀ x E

/-- The `badROf` twin of `badXiOf_runSrs`. -/
private theorem badROf_runSrs (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O : Coins C nc k) {m : ℕ} (aw₀ : Fin m → Fin (2 ^ k) → C.ScalarField)
    (x : Fin evalPts → C.ScalarField) (E : Fin m → Fin evalPts → C.ScalarField)
    (ξ : C.ScalarField) :
    badROf (fam.runSrs basis O) aw₀ x E ξ = badROf (srsOfBasis k basis) aw₀ x E ξ :=
  badROf_setBase (srsOfBasis k basis) _ aw₀ x E ξ

/-- **A retracted coordinate answers the two runs' common earlier challenge.** At a strictly
earlier pre-opening squeeze the retraction lands on the run's own node there (`regate_nodeAt_le`),
so the hypothesis that the two tables agree at the retracted node says exactly that the two runs
read the same challenge at that squeeze. -/
private theorem readsOf_eq_of_ans (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O O' : Coins C nc k) (s : Squeeze k) (j : Fin preIpaChals)
    (hrank : squeezeRank (preSqueeze j : Squeeze k) < squeezeRank s)
    (hans : O (szPre j (fam.nodesOf basis O s)) = O' (szPre j (fam.nodesOf basis O' s))) :
    fam.readsOf basis O (preSqueeze j) = fam.readsOf basis O' (preSqueeze j) := by
  have hO : ∀ P : Coins C nc k,
      szPre j (fam.nodesOf basis P s) = fam.nodesOf basis P (preSqueeze j) := by
    intro P
    show (if squeezeRank (preSqueeze j : Squeeze k) < squeezeRank s
        then regate (fam.nodesOf basis P s) (preSqueeze j)
        else regate (fam.nodesOf basis P s) Squeeze.schnorr)
      = fam.nodesOf basis P (preSqueeze j)
    rw [if_pos hrank]
    exact regate_nodeAt_le (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis P)
      (le_of_lt hrank)
  rw [hO O, hO O'] at hans
  exact congrArg (squeezeExpand C (preSqueeze j)) hans

/-- **The batched claim's evaluation points and claimed evaluations are fixed by the `ξ` node
and the four fq-side challenges.** These are the two components `badXiOf` and `badROf` read; the
opening — the one part of the emitted proof the `ξ` node does not fix — appears in neither. -/
private theorem claim_pointFn_evalFn_eq (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O O' : Coins C nc k) {s : Squeeze k} (h4 : 4 ≤ squeezeRank s)
    (hnode : fam.nodesOf basis O s = fam.nodesOf basis O' s)
    (hb : fam.readsOf basis O Squeeze.beta = fam.readsOf basis O' Squeeze.beta)
    (hg : fam.readsOf basis O Squeeze.gamma = fam.readsOf basis O' Squeeze.gamma)
    (ha : fam.readsOf basis O Squeeze.alpha = fam.readsOf basis O' Squeeze.alpha)
    (hz : fam.readsOf basis O Squeeze.zeta = fam.readsOf basis O' Squeeze.zeta) :
    (fam.claim basis O).pointFn = (fam.claim basis O').pointFn
      ∧ (fam.claim basis O).evalFn = (fam.claim basis O').evalFn := by
  have hO : fam.claim basis O = runInputWith (srsOfBasis k basis) (fam.cvk basis)
      (fam.proofOf basis O) (fam.pub basis)
      (fam.readsOf basis O Squeeze.beta) (fam.readsOf basis O Squeeze.gamma)
      (fam.readsOf basis O Squeeze.alpha) (fam.readsOf basis O Squeeze.zeta)
      (fam.readsOf basis O Squeeze.polyscale) (fam.readsOf basis O Squeeze.evalscale) := rfl
  have hO' : fam.claim basis O' = runInputWith (srsOfBasis k basis) (fam.cvk basis)
      (fam.proofOf basis O') (fam.pub basis)
      (fam.readsOf basis O' Squeeze.beta) (fam.readsOf basis O' Squeeze.gamma)
      (fam.readsOf basis O' Squeeze.alpha) (fam.readsOf basis O' Squeeze.zeta)
      (fam.readsOf basis O' Squeeze.polyscale) (fam.readsOf basis O' Squeeze.evalscale) := rfl
  rw [hO, hO', hb, hg, ha, hz]
  exact runInputWith_pointFn_evalFn_congr (srsOfBasis k basis) (fam.cvk basis) (fam.pub basis)
    (fam.proofOf basis O) (fam.proofOf basis O') _ _ _ _ _ _ _ _ _
    (fam.proofOf_eq_of_node basis O O' h4 hnode)

/-- **The `ξ` exclusion set is fixed by the `ξ` node and the four fq-side challenges.** It reads
every flat row's coefficient vector — all absorbed by `ζ` — the claim's evaluation points and its
claimed evaluations, and the SRS only through `σ.k`. -/
private theorem badXiOf_eq_of_node (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O O' : Coins C nc k) {s : Squeeze k} (h4 : 4 ≤ squeezeRank s)
    (hnode : fam.nodesOf basis O s = fam.nodesOf basis O' s)
    (hb : fam.readsOf basis O Squeeze.beta = fam.readsOf basis O' Squeeze.beta)
    (hg : fam.readsOf basis O Squeeze.gamma = fam.readsOf basis O' Squeeze.gamma)
    (ha : fam.readsOf basis O Squeeze.alpha = fam.readsOf basis O' Squeeze.alpha)
    (hz : fam.readsOf basis O Squeeze.zeta = fam.readsOf basis O' Squeeze.zeta) :
    badXiOf (fam.runSrs basis O) (fam.aRef basis O) (fam.claim basis O).pointFn
        (fam.claim basis O).evalFn
      = badXiOf (fam.runSrs basis O') (fam.aRef basis O') (fam.claim basis O').pointFn
        (fam.claim basis O').evalFn := by
  have hpe := fam.claim_pointFn_evalFn_eq basis O O' h4 hnode hb hg ha hz
  have haR : fam.aRef basis O = fam.aRef basis O' := funext fun r =>
    (fam.repPrefix_of_rank_le basis O O' r
      (le_trans (squeezeRank_absorbedBy_le_three r)
        (le_trans (show (3 : ℕ) ≤ 4 by omega) h4)) hnode).1
  rw [fam.badXiOf_runSrs basis O, fam.badXiOf_runSrs basis O', haR, hpe.1, hpe.2]

/-- **The `r` exclusion set is fixed by the `r` node and the five earlier challenges** — the
`badXiOf_eq_of_node` twin, with the polyscale challenge as the extra datum. -/
private theorem badROf_eq_of_node (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (O O' : Coins C nc k) {s : Squeeze k} (h4 : 4 ≤ squeezeRank s)
    (hnode : fam.nodesOf basis O s = fam.nodesOf basis O' s)
    (hb : fam.readsOf basis O Squeeze.beta = fam.readsOf basis O' Squeeze.beta)
    (hg : fam.readsOf basis O Squeeze.gamma = fam.readsOf basis O' Squeeze.gamma)
    (ha : fam.readsOf basis O Squeeze.alpha = fam.readsOf basis O' Squeeze.alpha)
    (hz : fam.readsOf basis O Squeeze.zeta = fam.readsOf basis O' Squeeze.zeta)
    (hx : fam.readsOf basis O Squeeze.polyscale = fam.readsOf basis O' Squeeze.polyscale) :
    badROf (fam.runSrs basis O) (fam.aRef basis O) (fam.claim basis O).pointFn
        (fam.claim basis O).evalFn (fam.claim basis O).polyscale
      = badROf (fam.runSrs basis O') (fam.aRef basis O') (fam.claim basis O').pointFn
        (fam.claim basis O').evalFn (fam.claim basis O').polyscale := by
  have hpe := fam.claim_pointFn_evalFn_eq basis O O' h4 hnode hb hg ha hz
  have haR : fam.aRef basis O = fam.aRef basis O' := funext fun r =>
    (fam.repPrefix_of_rank_le basis O O' r
      (le_trans (squeezeRank_absorbedBy_le_three r)
        (le_trans (show (3 : ℕ) ≤ 4 by omega) h4)) hnode).1
  have hxi : (fam.claim basis O).polyscale = (fam.claim basis O').polyscale :=
    (fam.claim_polyscale basis O).trans (hx.trans (fam.claim_polyscale basis O').symm)
  rw [fam.badROf_runSrs basis O, fam.badROf_runSrs basis O', haR, hpe.1, hpe.2, hxi]

/-- **The exclusion sets are node-determined** — the mathematical
content of summand (IV). Two tables whose runs share the node at the `i`-th guarded squeeze, and
whose oracle answers agree at every strictly-earlier retracted node, produce the *same* `i`-th
exclusion set. It says the adversary cannot choose its exclusion set after seeing the challenge
that the set is about.

The seven cases follow the schedule. `β` and `γ` read only the assembled witness columns, whose
rows are absorbed at `β`; `α` adds the accumulator, absorbed at `α`; `ζ` adds the assembled
quotient, whose chunk count and chunk vectors are fixed at `ζ`; the boundary set is a function of
the circuit alone; and `ξ`, `r` read every flat row (all absorbed by `ζ`) together with the
batched claim's evaluation points and claimed evaluations, which the `ξ` node fixes up to the
opening — a component neither set touches. Every earlier challenge a set names is supplied by the
retracted coordinate at that squeeze. -/
private theorem szBadRun_agree (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (i : Fin szSets)
    (O O' : Coins C nc k)
    (hnode : fam.szNode basis i (fam.proofOf basis O)
      = fam.szNode basis i (fam.proofOf basis O'))
    (hans : ∀ j : Fin preIpaChals, O (szPre j (fam.szNode basis i (fam.proofOf basis O)))
      = O' (szPre j (fam.szNode basis i (fam.proofOf basis O')))) :
    fam.szBadRun basis O i = fam.szBadRun basis O' i := by
  fin_cases i
  · -- `β`: the assembled witness columns only.
    have hn : fam.nodesOf basis O Squeeze.beta = fam.nodesOf basis O' Squeeze.beta := hnode
    show Protocol.soundBadB fam.idx _ = Protocol.soundBadB fam.idx _
    exact congrArg _ (fam.runW_eq_of_node basis O O' hn)
  · -- `γ`: the same, plus the `β` challenge.
    have hn : fam.nodesOf basis O Squeeze.gamma = fam.nodesOf basis O' Squeeze.gamma := hnode
    have hb : fam.readsOf basis O Squeeze.beta = fam.readsOf basis O' Squeeze.beta :=
      fam.readsOf_eq_of_ans basis O O' Squeeze.gamma 0 (by show (0 : ℕ) < 1; omega) (hans 0)
    have hW := fam.runW_eq_of_node basis O O' hn
    show Protocol.soundBadG fam.idx _ _ = Protocol.soundBadG fam.idx _ _
    rw [hW, hb]
  · -- `α`: adds the assembled accumulator and the `γ` challenge.
    have hn : fam.nodesOf basis O Squeeze.alpha = fam.nodesOf basis O' Squeeze.alpha := hnode
    have hb : fam.readsOf basis O Squeeze.beta = fam.readsOf basis O' Squeeze.beta :=
      fam.readsOf_eq_of_ans basis O O' Squeeze.alpha 0 (by show (0 : ℕ) < 2; omega) (hans 0)
    have hg : fam.readsOf basis O Squeeze.gamma = fam.readsOf basis O' Squeeze.gamma :=
      fam.readsOf_eq_of_ans basis O O' Squeeze.alpha 1 (by show (1 : ℕ) < 2; omega) (hans 1)
    have hW := fam.runW_eq_of_node basis O O' hn
    have hZ := fam.runZ_eq_of_node basis O O' (s := Squeeze.alpha) (by show (2 : ℕ) ≤ 2; omega) hn
    show Protocol.soundBadA fam.idx _ _ _ _ _ = Protocol.soundBadA fam.idx _ _ _ _ _
    rw [hW, hZ, hb, hg]
  · -- `ζ`: adds the assembled quotient and the `α` challenge.
    have hn : fam.nodesOf basis O Squeeze.zeta = fam.nodesOf basis O' Squeeze.zeta := hnode
    have hb : fam.readsOf basis O Squeeze.beta = fam.readsOf basis O' Squeeze.beta :=
      fam.readsOf_eq_of_ans basis O O' Squeeze.zeta 0 (by show (0 : ℕ) < 3; omega) (hans 0)
    have hg : fam.readsOf basis O Squeeze.gamma = fam.readsOf basis O' Squeeze.gamma :=
      fam.readsOf_eq_of_ans basis O O' Squeeze.zeta 1 (by show (1 : ℕ) < 3; omega) (hans 1)
    have ha : fam.readsOf basis O Squeeze.alpha = fam.readsOf basis O' Squeeze.alpha :=
      fam.readsOf_eq_of_ans basis O O' Squeeze.zeta 2 (by show (2 : ℕ) < 3; omega) (hans 2)
    have hW := fam.runW_eq_of_node basis O O' hn
    have hZ := fam.runZ_eq_of_node basis O O' (s := Squeeze.zeta) (by show (2 : ℕ) ≤ 3; omega) hn
    have hT :=
      fam.ftAssembly_eq_of_node basis O O' (s := Squeeze.zeta) (by show (3 : ℕ) ≤ 3; omega) hn
    show Protocol.soundBadZ fam.idx _ _ _ _ _ _ _ = Protocol.soundBadZ fam.idx _ _ _ _ _ _ _
    rw [hW, hZ, hb, hg, ha, hT]
  · -- the `ζ` boundary set: a function of the circuit alone.
    exact (rfl : zetaBoundaryBad fam.idx = zetaBoundaryBad fam.idx)
  · -- `ξ`: every flat row, and the claim's points and claimed evaluations.
    have hn : fam.nodesOf basis O Squeeze.polyscale
        = fam.nodesOf basis O' Squeeze.polyscale := hnode
    have hb : fam.readsOf basis O Squeeze.beta = fam.readsOf basis O' Squeeze.beta :=
      fam.readsOf_eq_of_ans basis O O' Squeeze.polyscale 0 (by show (0 : ℕ) < 4; omega) (hans 0)
    have hg : fam.readsOf basis O Squeeze.gamma = fam.readsOf basis O' Squeeze.gamma :=
      fam.readsOf_eq_of_ans basis O O' Squeeze.polyscale 1 (by show (1 : ℕ) < 4; omega) (hans 1)
    have ha : fam.readsOf basis O Squeeze.alpha = fam.readsOf basis O' Squeeze.alpha :=
      fam.readsOf_eq_of_ans basis O O' Squeeze.polyscale 2 (by show (2 : ℕ) < 4; omega) (hans 2)
    have hz : fam.readsOf basis O Squeeze.zeta = fam.readsOf basis O' Squeeze.zeta :=
      fam.readsOf_eq_of_ans basis O O' Squeeze.polyscale 3 (by show (3 : ℕ) < 4; omega) (hans 3)
    exact fam.badXiOf_eq_of_node basis O O' (s := Squeeze.polyscale)
      (by show (4 : ℕ) ≤ 4; omega) hn hb hg ha hz
  · -- `r`: the same data, plus the `ξ` challenge.
    have hn : fam.nodesOf basis O Squeeze.evalscale
        = fam.nodesOf basis O' Squeeze.evalscale := hnode
    have hb : fam.readsOf basis O Squeeze.beta = fam.readsOf basis O' Squeeze.beta :=
      fam.readsOf_eq_of_ans basis O O' Squeeze.evalscale 0 (by show (0 : ℕ) < 5; omega) (hans 0)
    have hg : fam.readsOf basis O Squeeze.gamma = fam.readsOf basis O' Squeeze.gamma :=
      fam.readsOf_eq_of_ans basis O O' Squeeze.evalscale 1 (by show (1 : ℕ) < 5; omega) (hans 1)
    have ha : fam.readsOf basis O Squeeze.alpha = fam.readsOf basis O' Squeeze.alpha :=
      fam.readsOf_eq_of_ans basis O O' Squeeze.evalscale 2 (by show (2 : ℕ) < 5; omega) (hans 2)
    have hz : fam.readsOf basis O Squeeze.zeta = fam.readsOf basis O' Squeeze.zeta :=
      fam.readsOf_eq_of_ans basis O O' Squeeze.evalscale 3 (by show (3 : ℕ) < 5; omega) (hans 3)
    have hx : fam.readsOf basis O Squeeze.polyscale
        = fam.readsOf basis O' Squeeze.polyscale :=
      fam.readsOf_eq_of_ans basis O O' Squeeze.evalscale 4 (by show (4 : ℕ) < 5; omega) (hans 4)
    exact fam.badROf_eq_of_node basis O O' (s := Squeeze.evalscale)
      (by show (4 : ℕ) ≤ 5; omega) hn hb hg ha hz hx

/-! ### Arm (4)'s measure

The pieces assemble. `arm4_hits_badChallenge` puts every point of the arm into the union event;
`szBadRun_agree` and `szBadRun_card_le` are the agreement law and the budgets; the retraction and
guard are `szPre`/`szPre_ne` and `squeezeRank_szSqueeze_lt_six`; the expansions are injective by
`squeezeExpand_injective`. `measure_prod_le_of_forall_fibre` carries the per-basis bound to the
joint measure, since the bound does not mention the basis. -/

/-- **Arm (4)'s measure at a fixed basis.** `arm4_hits_badChallenge` puts every point of the arm
into the seven-fold union event; the agreement-form union charge then prices it at one query
factor times the total budget. -/
private theorem openedUnsatisfying_measure_le
    (hsmul : ∀ (z : C.ScalarField) (P : C.Point), z • P = z.val • P)
    (hcast : Function.Injective (fun q : Prechallenge => ((q : ℕ) : C.ScalarField)))
    (hexp : Function.Injective (expandPre C))
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    (PMF.uniformOfFintype (Coins C nc k)).toOuterMeasure
        {O | fam.Wins basis O ∧ fam.OpenedUnsatisfying basis O coins}
      ≤ ((fam.Q + 1 : ℕ) : ℝ≥0∞)
        * ((szBudget nc n fam.idx.zkRows : ℝ≥0∞) / (2 ^ 128 : ℕ)) := by
  classical
  have hcharge :=
    Bulletproof.Forking.adaptive_badSet_ofPrefix_union_expand_measure_le_of_agree
      (fam.adversary basis) (fam.queryBound basis) (fam.szNode basis)
      (fun t => squeezeRank t.idx < 6) (fun i _ => squeezeRank_szSqueeze_lt_six i)
      (fun _ j t => szPre j t) (fun _ t ht j => szPre_ne t ht j)
      (fun i => squeezeExpand C (szSqueeze (k := k) i))
      (fun i => squeezeExpand_injective C hcast hexp (szSqueeze (k := k) i))
      (fun i O => fam.szBadRun basis O i)
      (fun i O O' hn ha => fam.szBadRun_agree basis i O O' hn ha)
      (szCard nc n fam.idx.zkRows) (fun i O => fam.szBadRun_card_le basis O i)
  rw [szCard_sum, card_prechallenge] at hcharge
  refine le_trans (MeasureTheory.measure_mono ?_) hcharge
  rintro O ⟨hwin, harm⟩
  rcases fam.arm4_hits_badChallenge basis O coins hsmul hwin harm with
    h | h | h | h | h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩
  · exact ⟨3, h⟩
  · exact ⟨4, h⟩
  · rw [fam.claim_polyscale basis O] at h
    exact ⟨5, h⟩
  · rw [fam.claim_evalscale basis O] at h
    exact ⟨6, h⟩

/-- **The algebraic summand**: over the joint uniform measure on
(setup index, oracle table) pairs, arm (4) — the winning runs on which the extractor opened but
the assembled table does not satisfy the circuit — has measure at most
`(Q + 1) · szBudget / 2¹²⁸`.

The bound at a fixed basis does not mention the basis, so `measure_prod_le_of_forall_fibre`
carries it to the joint measure. The two curve facts about the expansions are hypotheses rather
than instances for the same reason they are in `acceptExtractionFailure_measure_prod_le`:
`expandPre` is injective per curve, and the `β`/`γ` cast is injective only because the scalar
field is bigger than `2 ¹²⁸`. -/
private theorem openedUnsatisfying_measure_prod_le
    (hsmul : ∀ (z : C.ScalarField) (P : C.Point), z • P = z.val • P)
    (hcast : Function.Injective (fun q : Prechallenge => ((q : ℕ) : C.ScalarField)))
    (hexp : Function.Injective (expandPre C))
    (B : C.Point) (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → C.ScalarField) × Coins C nc k)).toOuterMeasure
        {q | fam.Wins (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 ∧
          fam.OpenedUnsatisfying (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      ≤ ((fam.Q + 1 : ℕ) : ℝ≥0∞)
        * ((szBudget nc n fam.idx.zkRows : ℝ≥0∞) / (2 ^ 128 : ℕ)) :=
  measure_prod_le_of_forall_fibre
    (fun s O => fam.Wins (augOfSetup (Zcash.Snark.scalarBasis B s)) O ∧
      fam.OpenedUnsatisfying (augOfSetup (Zcash.Snark.scalarBasis B s)) O coins)
    fun s => fam.openedUnsatisfying_measure_le hsmul hcast hexp
      (augOfSetup (Zcash.Snark.scalarBasis B s)) coins

end KimchiFamily

end BadRun

end Arm4Measure

/-! ## 17. THE TOP-LEVEL STATEMENT, per curve — stated and proved

Everything the two endpoints consume is now above them: `wins_notExtracts_measure_le_of_arms`
(section 9) reduces each to two measure bounds, `acceptExtractionFailure_measure_prod_le`
(section 15) supplies the first and `openedUnsatisfying_measure_prod_le` (section 16) the second.
What is discharged per curve is only the arithmetic of the curve: `hsmul` by
`Pasta.vesta_smul_val` / `Pasta.pallas_smul_val`, the endo expansion's injectivity and
non-vanishing by `expandPre_{vesta,pallas}_{injective,ne_zero}`, and the `β`/`γ` cast's
injectivity by `natCast_prechallenge_injective` at the Pasta scalar modulus, which is far above
`2 ¹²⁸`. -/

/-- **Vesta: the deployed kimchi verifier is knowledge-sound, in the random-oracle model and
the algebraic group model.**

For a family of `Q`-query algebraic adversaries against the executable kimchi verifier, over a
uniformly sampled setup basis and a uniform challenge table: the probability that the verifier
accepts while the extractor fails to hand back a witness table satisfying the circuit the
verifying key corresponds to is at most

`(Q + k + 1)·3/2¹²⁸  +  (2ᵏ + 1)·ε  +  δ  +  (Q + 1)·szBudget/2¹²⁸`.

Four summands, four sources: the forking extraction returns nothing (query loss,
unconditional); it returns a relation among the sampled setup generators (`ε`, textbook
discrete log); it returns a relation touching the transcript-derived base (`δ`, the residual —
an assumption about a slice of the conclusion, not a reduction); or it returns an opening but
the run's own Fiat–Shamir challenges land in an exclusion set (`szBudget`).

**What the bound rests on.** Two cryptographic assumptions, both hypotheses: `hHard`, which
prices the two discrete-log arms, and the fork tape's completeness. `hEff` fixes which
reductions `hHard` is taken against; the extractor's cost is not bounded by any theorem in
this development (external-audit E-1), so `ε` is assumed for the finder rather than derived
from a time bound. Everything else is proved:
the presence arm by the claim-adaptive extraction game, and the algebraic arm by the
Fiat–Shamir-axiom-free run-soundness root together with the adaptive Schwartz–Zippel charge.
The narrowing of the family class is `KimchiFamily`'s own `hrepPrefix`/`hTPrefix` — algebraic
faithfulness, i.e. that a commitment's declared representation is fixed when the commitment is
absorbed — which is what the algebraic group model means and what
`KimchiFamily.szBadRun_agree` consumes.

**Scope.** "The deployed verifier" here means the modeled fragment (see the module
preamble): basic gate set, `nc · 2^k = n` (no sub-SRS keys — the deployed o1js/Mina default
is outside), no lookups, no optional gates, no recursion, no optional-gate/lookup evaluation
fields, non-empty quotient commitment. Mina/pickles proofs are outside on four axes.

`#print axioms` on this theorem: the three standard axioms plus CompElliptic's certified
`native_decide` witnesses for the Pasta curve constants — no `sorryAx`, and no Fiat–Shamir
axiom of any kind. -/
theorem vesta_kimchi_knowledge_sound {nc k n : ℕ} [NeZero n]
    (B : IpaVesta.Point) (fam : KimchiFamily IpaVesta.curve nc k n)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hcoins : coins.Complete) {R : ℕ} {ε δ : ℝ≥0∞}
    (hHard : fam.DiscreteLogRelationHardFor B coins R ε δ)
    (hEff : fam.ReductionEfficient coins R) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → IpaVesta.curve.ScalarField) × Coins _ nc k)).toOuterMeasure
        {q | fam.Wins (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 ∧
          ¬ fam.ExtractsWitness (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      ≤ (fam.Q + k + 1) * (3 / (2 ^ 128 : ℕ))
        + ((2 ^ k + 1 : ℕ) : ℝ≥0∞) * ε + δ
        + ((fam.Q + 1 : ℕ) : ℝ≥0∞) * ((szBudget nc n fam.idx.zkRows : ℝ≥0∞) / (2 ^ 128 : ℕ)) := by
  have hpres := fam.acceptExtractionFailure_measure_prod_le Pasta.vesta_smul_val
    expandPre_vesta_injective expandPre_vesta_ne_zero B coins hcoins
  rw [card_prechallenge] at hpres
  exact fam.wins_notExtracts_measure_le_of_arms B coins hHard hEff hpres
    (fam.openedUnsatisfying_measure_prod_le Pasta.vesta_smul_val
      (natCast_prechallenge_injective (by decide)) expandPre_vesta_injective B coins)

/-- **Pallas: the deployed kimchi verifier is knowledge-sound.** The Pallas-side twin of
`vesta_kimchi_knowledge_sound`, over `Fq`/`IpaPallas`; same shape, same four summands, same
axiom footprint, same modeled-fragment scope (see the Vesta endpoint's docstring and the
module preamble). Every step of the argument is curve-generic; only the four per-curve facts
about the expansions and the scalar action are re-discharged. -/
theorem pallas_kimchi_knowledge_sound {nc k n : ℕ} [NeZero n]
    (B : IpaPallas.Point) (fam : KimchiFamily IpaPallas.curve nc k n)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (hcoins : coins.Complete) {R : ℕ} {ε δ : ℝ≥0∞}
    (hHard : fam.DiscreteLogRelationHardFor B coins R ε δ)
    (hEff : fam.ReductionEfficient coins R) :
    (PMF.uniformOfFintype
        ((SetupIndex (2 ^ k) → IpaPallas.curve.ScalarField) × Coins _ nc k)).toOuterMeasure
        {q | fam.Wins (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 ∧
          ¬ fam.ExtractsWitness (augOfSetup (Zcash.Snark.scalarBasis B q.1)) q.2 coins}
      ≤ (fam.Q + k + 1) * (3 / (2 ^ 128 : ℕ))
        + ((2 ^ k + 1 : ℕ) : ℝ≥0∞) * ε + δ
        + ((fam.Q + 1 : ℕ) : ℝ≥0∞) * ((szBudget nc n fam.idx.zkRows : ℝ≥0∞) / (2 ^ 128 : ℕ)) := by
  have hpres := fam.acceptExtractionFailure_measure_prod_le Pasta.pallas_smul_val
    expandPre_pallas_injective expandPre_pallas_ne_zero B coins hcoins
  rw [card_prechallenge] at hpres
  exact fam.wins_notExtracts_measure_le_of_arms B coins hHard hEff hpres
    (fam.openedUnsatisfying_measure_prod_le Pasta.pallas_smul_val
      (natCast_prechallenge_injective (by decide)) expandPre_pallas_injective B coins)

end Kimchi.Verifier.KnowledgeSoundness
