import Kimchi.Verifier.Capstone.Reflection
import Bulletproof.Forking.KnowledgeSoundness

/-!
# Kimchi verifier knowledge soundness — the STATEMENT

This module expresses, and does not prove, the kimchi-level analogue of
`Bulletproof.Ipa.Forking.ipa{Vesta,Pallas}_knowledge_sound`: over a uniformly sampled setup
basis and a uniform challenge table, the executable kimchi verifier accepts while the
extractor fails to hand back a satisfying witness table only with small probability.

What the theorem buys is the retirement of `kimchi_fiat_shamir_{vesta,pallas}`. Those axioms
assert an accepted IPA opening of the run's combined commitment outright; here that opening is
*extracted*, by the forking argument the IPA capstone already runs, and the cost of extraction
failure is charged to discrete log.

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

`kimchiProof_sound_of_openings` (`Verifier/Reduction/Soundness.lean`) carries
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

/-- The challenge-generic verifier IS the size guard plus `Ipa.verifyWith` at that claim.
Definitional — the split only names the boundary. -/
theorem kimchiVerifyWith_eq_verifyWith {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField)
    (beta gamma alpha zeta v u : C.ScalarField) (uBase : C.Point)
    (chals : Vector C.ScalarField σ.k) (c : C.ScalarField) :
    kimchiVerifyWith σ cvk cp pub beta gamma alpha zeta v u uBase chals c
      = (if cvk.lagrangeBasis.size < pub.size || cvk.n < pub.size then false
          else Ipa.verifyWith C σ uBase chals c
            (runInputWith σ cvk cp pub beta gamma alpha zeta v u)) := rfl

/-- **FAITHFULNESS OBLIGATION.** The deployed verifier is `kimchiVerifyWith` at the challenges
the sponge derives. Without this the statement below is about an unrelated construction; with
it, it is about the shipped verifier under a random-oracle idealization of the sponge. The IPA
analogue is `Bulletproof.Forking.verifyOracle_spongeFS`. -/
theorem kimchiVerify_eq_verifyWith {nc : ℕ} (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (cp : KimchiProof C nc σ.k) (pub : Array C.ScalarField) :
    ∃ (beta gamma alpha zeta v u : C.ScalarField) (uBase : C.Point)
      (chals : Vector C.ScalarField σ.k) (c : C.ScalarField),
      kimchiVerify C σ cvk cp pub
        = kimchiVerifyWith σ cvk cp pub beta gamma alpha zeta v u uBase chals c := by
  sorry

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
def ColEvals (C : Ipa.CommitmentCurve) (nc : ℕ) : Type :=
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
structure EvalsView (C : Ipa.CommitmentCurve) (nc : ℕ) where
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
def evalsViewEquiv (C : Ipa.CommitmentCurve) (nc : ℕ) :
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
def pointView {nc : ℕ} (pe : PointEvaluations (Vector C.ScalarField nc)) : ColEvals C nc :=
  fun pt c => if pt = 0 then pe.zeta[c] else pe.zetaOmega[c]

/-- The proof's evaluations as the node's view of them, in the fr-sponge's absorb order. -/
def evalsViewOf {nc k : ℕ} (cp : KimchiProof C nc k) : EvalsView C nc where
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
def preIpaDataEquiv (C : Ipa.CommitmentCurve) (nc : ℕ) :
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
  /-- The folded generator `sg` — NOT absorbed by the deployed sponge, carried for the same
  reason `IpaNode.sg` is (see `Deployed.lean`'s preamble and `sg_determined_of_verifyWith`). -/
  sg : Option C.Point
  deriving DecidableEq

section Nodes

variable {nc k : ℕ}

/-- The node as a product, hand-written for the same reason `ipaNodeEquivProd` is: `deriving
Fintype` does not fire through the curve bundle. -/
def kimchiNodeEquivProd (C : Ipa.CommitmentCurve) (nc k : ℕ) :
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
def kimchiRound (t : KimchiNode C nc k) : C.Point × C.Point :=
  match t.idx with
  | .ipaRound i => (t.lr i).getD (0, 0)
  | _ => (0, 0)

/-- The final decoder: the Schnorr node carries `δ` and `sg`. The analogue of
`Deployed.nodeFinal`. -/
def kimchiFinal (t : KimchiNode C nc k) : C.Point × C.Point :=
  (t.delta.getD 0, t.sg.getD 0)

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
def ipaPrefixes (σ : SRS C.Point) (digest : C.ScalarField) (publicComm : Fin nc → C.Point)
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
def kimchiDecodesFromPrefixes (σ : SRS C.Point)
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
def kimchiIpaExtract (σ : SRS C.Point)
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

/-- **The oracle table** the adversary and the extractor share. Ironwood's `Coins`
(`Algebraic.lean:857`) carries the recursive fork tape alongside; here that tape stays a
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
  /-- The absorbed key digest, as a transcript label. -/
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

/-- The SRS the opening argument runs against: the sampled basis with the transcript-derived
IPA base. Matching `deployedExtract`, whose `U` override this copies. -/
def runSrs (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    SRS C.Point :=
  { srsOfBasis k basis with U := uBaseOf C (Ipa.cipOf (fam.claim basis O)) }

/-- **The deployed win**: the executable challenge-generic verifier accepts, with *every*
challenge read off the table at the run's own nodes — the pre-IPA six, the `k` round challenges
and the Schnorr challenge. The analogue of `Deployed.wireWins`. -/
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
      (uBaseOf C (Ipa.cipOf (fam.claim basis O)))
      (Vector.ofFn fun i : Fin k =>
        reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O
          (Squeeze.ipaRound i))
      (reads (fam.digest basis) (fam.publicComm basis) (fam.proofOf basis O) O Squeeze.schnorr)
    = true

/-! ### The AGM representation of the combined commitment -/

/-- The polyscale-combination of the family's per-commitment coefficient vectors. -/
def pgOf (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    Fin (2 ^ k) → C.ScalarField :=
  fun j => ∑ i : Fin (nc + 1 + tailRowCount * nc),
    (fam.claim basis O).polyscale ^ (i : ℕ) * fam.aRef basis O i j

/-- The polyscale-combination of the family's per-commitment blinders. -/
def pwOf (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
    C.ScalarField :=
  ∑ i : Fin (nc + 1 + tailRowCount * nc),
    (fam.claim basis O).polyscale ^ (i : ℕ) * fam.ρRef basis O i

/-- **Per-commitment representations give the combined one** — pure linearity from `hrep`, and
the reason a `KimchiFamily` needs no `pg`/`pw`/`hP` fields of its own: they are projections.

The proof is `Finset.sum_comm` under `commitGen`. -/
theorem hPOf (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k) :
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

/-! ### The extractor -/

/-- **The IPA forking extraction inside the kimchi transcript**, at the run's own claim. -/
def ipaAttempt (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
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

/-- **The extractor.** Total, computable, and data-valued on the left: an accepted IPA opening
of the run's combined commitment certifies the family's own AGM representation, which *is* the
extracted witness in the algebraic group model; a break is passed through.

Nothing here is a `Prop`. That is deliberate: every proof obligation lives in the measured
event below, so no unfinished proof can make the endpoint trivially true — it can only
enlarge the failure set. -/
def attempt (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → C.Point) (O : Coins C nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    Option ((Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ k) → C.ScalarField) ⊕'
      Zcash.Snark.AlgebraicRelationWitness (F := C.ScalarField)
        (Zcash.Snark.augmentedBasis (fam.runSrs basis O).g (fam.runSrs basis O).U
          (fam.runSrs basis O).h)) :=
  match fam.ipaAttempt basis O coins with
  | none => none
  | some (PSum.inr rel) => some (PSum.inr rel)
  | some (PSum.inl _) => some (PSum.inl (fam.aRef basis O))

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
`Bulletproof.Ipa.Forking.relationFinder` at `fam.attempt`. -/
def relationFinder (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    (bs : SetupIndex (2 ^ k) → C.Point) → Coins C nc k →
      Option (Zcash.Snark.AlgebraicRelationWitness (F := C.ScalarField) bs) :=
  fun bs O =>
    match fam.attempt (augOfSetup bs) O coins with
    | none => none
    | some (PSum.inl _) => none
    | some (PSum.inr rel) =>
        if hu : rel.coeffs Zcash.Snark.AugmentedIndex.u = 0 then
          some (setupBasis_srsOfBasis_augOfSetup_override bs
            (uBaseOf C (Ipa.cipOf (fam.claim (augOfSetup bs) O))) ▸ restrictToSetup rel hu)
        else none

/-- **The residual**: a break that touches the transcript-derived base computes its discrete
log. The copy of `Bulletproof.Ipa.Forking.derivedULog`. -/
def derivedULog (B : C.Point) (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1))
    (s : SetupIndex (2 ^ k) → C.ScalarField) (O : Coins C nc k) :
    Option (Zcash.Snark.DiscreteLogRepresentation (F := C.ScalarField) B
      (uBaseOf C (Ipa.cipOf (fam.claim (augOfSetup (Zcash.Snark.scalarBasis B s)) O)))) :=
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
of exactly this shape (`fsAdvantageFull_zero_slice_le`, `Forking/Adversary/Adaptive.lean:36`:
"the extra query reads that challenge from the output's own prefix"), which is the same reason
the query-loss summand carries `(Q + k + 1)`. The budget is therefore charged at `(Q + 1)`
per unit. -/

/-- The Schwartz–Zippel budget of a run: the total exclusion-set cardinality. -/
def szBudget (nc n zkRows : ℕ) : ℕ :=
  2 * (7 * (n - zkRows))
    + n * (Index.gateAlphaCount + Index.permAlphaCount - 1)
    + Index.degreeBound n + 2
    + 2 * (nc + 1 + tailRowCount * nc - 1) + 1

/-! ## 5. THE TOP-LEVEL STATEMENT, per curve -/

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

**What remains open** (and is what the open proof stands for): the AGM-side obligation that an
accepted opening plus the representations force `runWTab` to satisfy the circuit off the
exclusion sets — `run_sound_algebraic_ft` with the Fiat–Shamir axiom replaced by the extracted
opening, and with the binding sites returning relations rather than assuming they do not exist;
and the claim-adaptivity generalization of `kimchiExtract_failure_measure_le`, whose `(P, b, v)`
are fixed parameters while kimchi's claim is adversary output. -/
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
  sorry

/-- **Pallas: the deployed kimchi verifier is knowledge-sound.** The Pallas-side twin of
`vesta_kimchi_knowledge_sound`, over `Fq`/`IpaPallas`; same shape, same four summands. -/
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
  sorry

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

/-- Vesta: the extractor is a total computable function at the deployed curve, and its left
payload is data — the property that keeps an unfinished proof from making the bound free. -/
example {nc k n : ℕ} [NeZero n] (fam : KimchiFamily IpaVesta.curve nc k n)
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → IpaVesta.Point) (O : Coins IpaVesta.curve nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    Option ((Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ k) → IpaVesta.curve.ScalarField) ⊕'
      Zcash.Snark.AlgebraicRelationWitness (F := IpaVesta.curve.ScalarField)
        (Zcash.Snark.augmentedBasis (fam.runSrs basis O).g (fam.runSrs basis O).U
          (fam.runSrs basis O).h)) :=
  fam.attempt basis O coins

/-- Pallas: likewise. -/
example {nc k n : ℕ} [NeZero n] (fam : KimchiFamily IpaPallas.curve nc k n)
    (basis : Zcash.Snark.AugmentedIndex (2 ^ k) → IpaPallas.Point) (O : Coins IpaPallas.curve nc k)
    (coins : Zcash.Snark.RecursiveForkCoins Prechallenge (k + 1)) :
    Option ((Fin (nc + 1 + tailRowCount * nc) → Fin (2 ^ k) → IpaPallas.curve.ScalarField) ⊕'
      Zcash.Snark.AlgebraicRelationWitness (F := IpaPallas.curve.ScalarField)
        (Zcash.Snark.augmentedBasis (fam.runSrs basis O).g (fam.runSrs basis O).U
          (fam.runSrs basis O).h)) :=
  fam.attempt basis O coins

end PerCurve

/-! ## 7. What must hold before this is worth proving

* **`kimchiDecodesFromPrefixes` must be discharged.** It returns data, so leaving it open
  makes `attempt` compute with `sorryAx`. Commit-then-challenge is structurally true of the
  kimchi schedule; the `Option`-gating exists to make it provable.
* **The claim-adaptivity generalization.** `Bulletproof.Forking.kimchiExtract_failure_measure_le`
  fixes `(P, b, v)`; kimchi's claim is adversary output. Ironwood's forking layer already
  carries the mechanism — `recursiveAlgebraicForkFrom_realizes` takes an oracle-taking `win`
  together with `stable`/`stable_update` — which `Bulletproof/Forking/Game.lean` currently
  instantiates at the trivially-true predicate.
* **Anti-vacuity.** The accepting set must be shown non-empty, the analogue of
  `Bulletproof.Ipa.Forking.honestFamily_failure_set`, or the bound is a statement about
  nothing.
-/

end Kimchi.Verifier.KnowledgeSoundness
