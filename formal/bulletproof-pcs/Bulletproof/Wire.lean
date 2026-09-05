import CompElliptic.Curves.Pasta
import Pasta.Shifted
import Poseidon.GroupMap
import Bulletproof.Protocol

/-!
# The executable kimchi IPA verifier, over checked records

The batched IPA opening verifier of kimchi (`SRS::verify`, proof-systems
`poly-commitment/src/ipa.rs`), composed as one executable function over a *checked* claim:
the per-polynomial commitments, evaluation points and claimed evaluations, the combination
scalars, and the opening proof, against a separately supplied SRS (`Bulletproof.SRS`).

Everything transcript-derived — the `U` base, the round challenges, the Schnorr challenge —
is recomputed here through the sponge layer of the `poseidon` package; nothing is taken as
input that the wire protocol does not carry. In particular the abstract SRS's randomisation
base `σ.U` is never read: the deployed protocol derives `U` from the transcript, and relating
the derived base to the abstract one is exactly the Fiat–Shamir assumption's junction.

## The checked records carry their shape in their types

`Proof C k` pins the round count (`lr` is a `Vector` of length `k`, the SRS's `σ.k`), and
`Input C k m p` pins the batch shape: `m` rows, `p` evaluation points, and the
claimed-evaluation matrix a `Vector` of `Vector`s. Every read of the verifier, and of every
statement over it, is total — a checked input cannot hold a ragged claim.

The raw serde records (`Wire.Proof`, `Wire.Input`, every payload a `Vec`) live in the `Wire`
namespace below with their `check` parses. Those parses state this verifier's totality
requirements — the round count, and `evals` square against the commitments and points — as a
total parse, so the parse *is* the proof. Clients compose check-then-verify.

Production's `SRS::verify` carries no such explicit guards; its `Vec` payloads feed the
transcript and the batched MSM equations as they are. An oversized `lr` panics, and an
undersized `lr` whose claim is committed over the SRS prefix is accepted. The round-count pin
here is therefore a declared modeling *strengthening* rather than the transcription of a
production check (external-audit W-F3). In the kimchi composition, exploiting that corner
against a `Corresponds`-satisfying key requires a discrete-log break, so the endpoint
exposure is priced.

## The curve bundle

Generic over a single `CommitmentCurve` bundle — the Lean analogue of the Rust
`G: CommitmentCurve` associated types: the base and scalar cardinalities with their primality
facts, the sponge spec, the curve `E`, and the map-to-curve. The bundle carries *facts*, not
structures: the field structures are the canonical `ZMod` instances synthesized from
primality, so the executable and abstract layers cannot disagree on any field operation.
Points are the library's `SWPoint E` (`Point`), so the group structure is inherited — `+`/`0`
and the binary-nsmul scalar action from CompElliptic's `AddCommGroup` instance, point
equality from its `DecidableEq`.

The scalar side reuses the `Bulletproof` definitions (`bPoly`, `bPolyCoefficients`,
`combinedB`, `combinedInnerProduct`) at the concrete scalar field. Scalars act on points as
`z.val • _`, the ℕ-action of the group; `Bulletproof.Reflection` relates this verifier to the
`Prop`-level `BatchAccepts`.

The absorbed-scalar encoding (`shift_scalar`) is selected by the modulus comparison from the
cardinalities — the `Shifted_value` Type1 register when the scalar modulus is below the base
modulus, the Type2 shift otherwise — at the scalar-modulus bit size `Nat.size scalar` (the
Rust `MODULUS_BIT_SIZE`).

## What `verify` checks

The two acceptance equations, at the derived challenges:

* Schnorr: `c • Q + δ = z1 • sg + (z1 · b0) • U + z2 • H`, with
  `Q = P + v • U + ∑ (uⱼ⁻¹ • Lⱼ + uⱼ • Rⱼ)`, `P` the polyscale combination of the
  commitments, `v` the combined inner product, and `b0` the evalscale combination of `bPoly`;
* `sg`-correctness: `sg = ⟨bPolyCoefficients chal, g⟩`.

`IpaVesta` and `IpaPallas` instantiate the two Pasta curves. Both are validated against
production prover/verifier fixtures by `scripts/check_ipa_fixture.lean`, which parses the
wire records and composes check-then-verify.
-/

namespace Bulletproof.Ipa

open CompElliptic.CurveForms.ShortWeierstrass
open Poseidon Poseidon.FqSponge Bulletproof

/-- The per-curve data of the verifier, bundled as a single index — base and scalar
cardinalities with their primality facts, the Fq-sponge spec, the curve, and the
map-to-curve. Carrying facts rather than field structures makes every field operation
resolve to the canonical `ZMod` instances on both the executable and abstract sides. -/
structure CommitmentCurve where
  /-- The base-field cardinality; the field itself is the canonical `ZMod base`. -/
  base : ℕ
  /-- The scalar-field cardinality; the field itself is the canonical `ZMod scalar`. -/
  scalar : ℕ
  [primeBase : Fact (Nat.Prime base)]
  [primeScalar : Fact (Nat.Prime scalar)]
  /-- The Fq-sponge spec driving the verifier's Fiat–Shamir transcript. -/
  sponge : FqSponge.Spec base scalar
  /-- The scalar-side Poseidon parameters — production's `G::sponge_params()`,
  curve-determined like the fq-sponge spec. Not read by the IPA opening verifier
  itself; carried on the bundle for the consumers that run a scalar-side (fr-)sponge
  over the same curve (kimchi's `frOracles`), the way production types the table on
  the curve rather than on any wire record. -/
  frParams : Params (ZMod scalar)
  /-- The curve, in short-Weierstrass form over the base field. -/
  E : SWCurve (ZMod base)
  /-- The map-to-curve deriving the transcript `U` base from a squeezed field element. -/
  toGroup : ZMod base → SWPoint E

attribute [instance] CommitmentCurve.primeBase CommitmentCurve.primeScalar

/-- The base field — the canonical `ZMod` at the base cardinality. -/
abbrev CommitmentCurve.BaseField (C : CommitmentCurve) := ZMod C.base

/-- The scalar field — the canonical `ZMod` at the scalar cardinality. -/
abbrev CommitmentCurve.ScalarField (C : CommitmentCurve) := ZMod C.scalar

/-- The point type — the library's proof-carrying `SWPoint`, with its group structure. -/
abbrev CommitmentCurve.Point (C : CommitmentCurve) := SWPoint C.E

variable (C : CommitmentCurve)

/-- Multi-scalar multiplication `∑ i, aᵢ • gᵢ` — the group-side mirror of
`Bulletproof.commitGen`, with the scalars acting through `val`. -/
def msm {n : ℕ} (g : Fin n → C.Point) (a : Fin n → C.ScalarField) : C.Point :=
  ∑ i, (a i).val • g i

/-- An IPA opening proof at round count `k` — the checked form of the wire
`OpeningProof` (`ipa.rs`): the round count is the SRS's `σ.k`, pinned by the parse. -/
structure Proof (C : CommitmentCurve) (k : ℕ) where
  /-- The per-round `(L, R)` commitment pairs — a `Vector` at the checked round count `k`. -/
  lr : Vector (C.Point × C.Point) k
  /-- The Schnorr commitment `δ`. -/
  delta : C.Point
  /-- The Schnorr response scalar acting on `sg` and the `U` base. -/
  z1 : C.ScalarField
  /-- The Schnorr response scalar acting on the blinding base `H`. -/
  z2 : C.ScalarField
  /-- The challenge-folded commitment base, checked against `⟨bPolyCoefficients chal, g⟩`. -/
  sg : C.Point

/-- A batched opening claim at its shape — round count `k`, `m` rows, `p` evaluation
points: the per-polynomial commitments (one segment each), the evaluation points, the
claimed evaluation matrix (`evals[i][j]` = polynomial `i` at point `j`), the
combination scalars, and the proof. Every read is total. -/
structure Input (C : CommitmentCurve) (k m p : ℕ) where
  /-- The per-polynomial commitments, one segment each — the `m` rows of the claim. -/
  commitments : Vector C.Point m
  /-- The `p` evaluation points. -/
  xs : Vector C.ScalarField p
  /-- The claimed evaluation matrix: `evals[i][j]` = polynomial `i` at point `j`. -/
  evals : Vector (Vector C.ScalarField p) m
  /-- The polynomial-combination scalar `ξ`. -/
  polyscale : C.ScalarField
  /-- The evaluation-point-combination scalar `r`. -/
  evalscale : C.ScalarField
  /-- The opening proof, at the checked round count `k`. -/
  proof : Proof C k

variable {k m p : ℕ}

/-- The commitments as the `Fin`-indexed function of the abstract claim. -/
def Input.commitmentFn {C : CommitmentCurve} (inp : Input C k m p) :
    Fin m → C.Point :=
  fun i => inp.commitments[i]

/-- The evaluation points as the `Fin`-indexed function of the abstract claim. -/
def Input.pointFn {C : CommitmentCurve} (inp : Input C k m p) :
    Fin p → C.ScalarField :=
  fun j => inp.xs[j]

/-- The claimed evaluation matrix as the indexed function of the abstract claim. -/
def Input.evalFn {C : CommitmentCurve} (inp : Input C k m p) :
    Fin m → Fin p → C.ScalarField :=
  fun i j => (inp.evals[i])[j]

/-- The combined inner product of the claimed evaluations
(`Bulletproof.combinedInnerProduct` at the checked matrix). -/
def cipOf {C : CommitmentCurve} (inp : Input C k m p) : C.ScalarField :=
  combinedInnerProduct inp.polyscale inp.evalscale inp.evalFn

/-- The polyscale combination `∑ i, ξ^i • Cᵢ` of the commitments — the group-side mirror
of `Bulletproof.combinedCommitment`, by a running power. -/
def combineCommitments (ξ : C.ScalarField) (cs : Array C.Point) : C.Point :=
  (cs.foldl (fun (acc : C.Point × C.ScalarField) P => (acc.1 + acc.2.val • P, acc.2 * ξ))
    (0, 1)).1

/-- The transcript encoding of an absorbed scalar (`shift_scalar`,
`poly-commitment/src/commitment.rs`): the `Shifted_value` register form at the
scalar-modulus bit size `Nat.size scalar` (the Rust `MODULUS_BIT_SIZE`) — Type1
(`(x − 2ᵇ − 1)/2`) when the scalar modulus is below the base modulus, the Type2 shift
(`x − 2ᵇ`) otherwise. The branch is the Rust `n1 < n2`, decided from the cardinalities. -/
def shiftScalar (x : C.ScalarField) : C.ScalarField :=
  if C.scalar < C.base then Pasta.Shifted.shiftType1 (Nat.size C.scalar) x
  else Pasta.Shifted.shiftType2 (Nat.size C.scalar) x

/-- One round of the challenge fold: absorb `L` and `R`, squeeze one challenge, push it. -/
private def roundStep (acc : Array C.ScalarField × FqSponge.S C.base) (LR : C.Point × C.Point) :
    Array C.ScalarField × FqSponge.S C.base :=
  let us := squeezeChallenge C.sponge (absorbG C.sponge (absorbG C.sponge acc.2 LR.1) LR.2)
  (acc.1.push us.1, us.2)

/-- The per-round challenge fold (the round loop of `SRS::verify`): absorb `L` and `R`,
squeeze one challenge, threading the sponge state — one push per `(L, R)` pair. The
array-level engine of `roundChallenges`; the fold state is concrete data. -/
def roundChallengesAux (s : FqSponge.S C.base) (lr : Array (C.Point × C.Point)) :
    Array C.ScalarField × FqSponge.S C.base :=
  lr.foldl (roundStep C) (#[], s)

/-- A left fold that pushes exactly one element per step grows the array by the list
length. -/
private theorem foldl_fst_size {S γ α : Type*} (step : (Array γ × S) → α → (Array γ × S))
    (hstep : ∀ acc a, (step acc a).1.size = acc.1.size + 1)
    (l : List α) (init : Array γ × S) :
    (l.foldl step init).1.size = init.1.size + l.length := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih, hstep, List.length_cons]
    omega

/-- The fold squeezes exactly one round challenge per `(L, R)` pair. -/
theorem roundChallengesAux_size (s : FqSponge.S C.base) (lr : Array (C.Point × C.Point)) :
    (roundChallengesAux C s lr).1.size = lr.size := by
  unfold roundChallengesAux
  rw [← Array.foldl_toList, foldl_fst_size]
  · simp
  · intro acc a
    simp [roundStep, Array.size_push]

/-- The round challenges of a checked proof, from a given sponge state: the challenge
vector — sized by construction, one challenge per round — and the post-fold sponge
state. -/
def roundChallenges (s : FqSponge.S C.base) {k : ℕ} (lr : Vector (C.Point × C.Point) k) :
    Vector C.ScalarField k × FqSponge.S C.base :=
  let r := roundChallengesAux C s lr.toArray
  (⟨r.1, (roundChallengesAux_size C s lr.toArray).trans lr.size_toArray⟩, r.2)

/-- The verifier's Fiat–Shamir schedule from a given initial sponge state `s₀`
(`SRS::verify`, with the sponge supplied by the caller — kimchi hands the warm post-`ζ`
fq-sponge state here, `BatchEvaluationProof { sponge: fq_sponge, .. }`): absorb the
shifted combined inner product; squeeze and map the `U` base; per round absorb `L`, `R`
and squeeze a challenge; absorb `δ` and squeeze the Schnorr challenge. The round
challenges come back as a `Vector` at the checked round count, so every downstream read
is total. -/
def transcriptFrom (s₀ : FqSponge.S C.base) (inp : Input C k m p) :
    C.Point × Vector C.ScalarField k × C.ScalarField :=
  let s := absorbFr C.sponge s₀ (shiftScalar C (cipOf inp))
  let (t, s) := challengeFq C.sponge s
  let uBase := C.toGroup t
  let (chals, s) := roundChallenges C s inp.proof.lr
  let s := absorbG C.sponge s inp.proof.delta
  let (c, _) := squeezeChallenge C.sponge s
  (uBase, chals, c)

/-- The standalone verifier's Fiat–Shamir schedule: `transcriptFrom` at the fresh
sponge `FqSponge.init` — the cold start. -/
def transcript (inp : Input C k m p) :
    C.Point × Vector C.ScalarField k × C.ScalarField :=
  transcriptFrom C FqSponge.init inp


/-- The acceptance decision from a given initial sponge state `s₀`, against a library
SRS: derive the transcript (from `s₀` — kimchi's warm start hands the post-`ζ`
fq-sponge state, verifier.rs:1184–1193), combine the claim, and check the Schnorr and
`sg`-correctness equations. The claim's shape is carried by its type (round count
`σ.k`), so there are no runtime guards — rejecting ragged input is the wire parse's
job. `σ.U` is never read — the deployed `U` is transcript-derived. -/
def verifyWith (σ : SRS C.Point) (uBase : C.Point) (chals : Vector C.ScalarField σ.k)
    (c : C.ScalarField) (inp : Input C σ.k m p) : Bool :=
  let chal : Fin σ.k → C.ScalarField := fun i => chals[i]
  let b0 := combinedB chal inp.evalscale inp.pointFn
  let v := cipOf inp
  let P := combineCommitments C inp.polyscale inp.commitments.toArray
  let Q := (inp.proof.lr.toArray.zip chals.toArray).foldl
    (fun acc (LRu : (C.Point × C.Point) × C.ScalarField) =>
      acc + (LRu.2⁻¹.val • LRu.1.1 + LRu.2.val • LRu.1.2))
    (P + v.val • uBase)
  let schnorr := decide (c.val • Q + inp.proof.delta
    = inp.proof.z1.val • inp.proof.sg + (inp.proof.z1 * b0).val • uBase
        + inp.proof.z2.val • σ.h)
  let sgOk := decide (inp.proof.sg = msm C σ.g (bPolyCoefficients chal))
  schnorr && sgOk

/-- The opening acceptance at the deployed Fiat–Shamir schedule: `verifyWith` fed the
transcript `transcriptFrom` derives by continuing the warm sponge. Definitionally the
former body, so every existing statement about `verifyFrom` is unchanged; the split only
names the boundary between the *derivation* (`transcriptFrom`) and the *algebra*
(`verifyWith`), so an alternative challenge source can be supplied without touching either. -/
def verifyFrom (σ : SRS C.Point) (s₀ : FqSponge.S C.base) (inp : Input C σ.k m p) :
    Bool :=
  let (uBase, chals, c) := transcriptFrom C s₀ inp
  verifyWith C σ uBase chals c inp

/-- The standalone acceptance decision: `verifyFrom` at the fresh sponge
`FqSponge.init` — the cold start, validated against the production opening fixtures. -/
def verify (σ : SRS C.Point) (inp : Input C σ.k m p) : Bool :=
  verifyFrom C σ FqSponge.init inp


/-! ## The prechallenge level

`transcriptFrom` factored to the raw squeezes of the automaton, the form a circuit
implementation of `check_bulletproof` is read against: `ipaSqueezes` is the schedule on
`Poseidon.State`, `ipaPrechallenges` its 128-bit packings, and
`transcriptFrom_eq_ipaPrechallenges` identifies `transcriptFrom`'s outputs with their
map-to-curve and endo-expansions. `schnorrAt` names the Schnorr equation at given advice,
`verifyWith_eq` splits `verifyWith` into it and the `sg`-correctness equation. -/

/-- The absorbed limbs of a scalar (`absorbFr`'s branch made explicit): one limb when the
scalar modulus is below the base modulus, the high bits then the low bit otherwise. -/
def scalarLimbs (x : C.ScalarField) : List C.BaseField :=
  if C.scalar < C.base then [((x.val : ℕ) : C.BaseField)]
  else [((x.val / 2 : ℕ) : C.BaseField), ((x.val % 2 : ℕ) : C.BaseField)]

/-- `absorbFr` absorbs `scalarLimbs`. -/
private theorem absorbFr_eq (s : FqSponge.S C.base) (x : C.ScalarField) :
    absorbFr C.sponge s x = absorbFq C.sponge s (scalarLimbs C x) := by
  unfold absorbFr scalarLimbs
  split <;> rfl

/-- One round of the raw schedule: absorb `L` then `R`, squeeze, append the raw element. -/
def ipaRound {F : Type*} [Field F] (p : Poseidon.Params F)
    (acc : List F × Poseidon.State F) (q : (F × F) × (F × F)) : List F × Poseidon.State F :=
  let sq := Poseidon.squeeze p
    (Poseidon.absorb p (Poseidon.absorb p acc.2 [q.1.1, q.1.2]) [q.2.1, q.2.2])
  (acc.1 ++ [sq.1], sq.2)

/-- The round fold's challenges accumulate onto the prefix; its state does not depend on
it. -/
theorem ipaRound_foldl {F : Type*} [Field F] (p : Poseidon.Params F) :
    ∀ (l : List ((F × F) × (F × F))) (acc : List F) (s : Poseidon.State F),
      l.foldl (ipaRound p) (acc, s)
        = (acc ++ (l.foldl (ipaRound p) ([], s)).1, (l.foldl (ipaRound p) ([], s)).2)
  | [], _, _ => by simp
  | q :: l, acc, s => by
    simp only [List.foldl_cons, ipaRound, List.nil_append]
    generalize Poseidon.squeeze p (Poseidon.absorb p (Poseidon.absorb p s [q.1.1, q.1.2])
      [q.2.1, q.2.2]) = sq
    rw [ipaRound_foldl p l (acc ++ [sq.1]) sq.2, ipaRound_foldl p l [sq.1] sq.2]
    simp [List.append_assoc]

/-- The raw squeezed elements of the opening transcript from a warm state (`transcriptFrom`
from `⟨s₀, []⟩`): the `U` base's preimage `t`, one element per `(L, R)` pair, and `c`'s.
Points enter as coordinate pairs, the scalar as its limbs. -/
def ipaSqueezes {F : Type*} [Field F] (p : Poseidon.Params F) (s₀ : Poseidon.State F)
    (cipLimbs : List F) (lr : List ((F × F) × (F × F))) (delta : F × F) : F × List F × F :=
  let sqT := Poseidon.squeeze p (Poseidon.absorb p s₀ cipLimbs)
  let r := lr.foldl (ipaRound p) ([], sqT.2)
  (sqT.1, r.1, (Poseidon.squeeze p (Poseidon.absorb p r.2 [delta.1, delta.2])).1)

/-- The 128-bit prechallenges of the opening transcript: `t` raw, each round's and `c`'s
squeeze mod `2^128` (`challengeNat`). `transcriptFrom` is their map-to-curve and
endo-expansions (`transcriptFrom_eq_ipaPrechallenges`). -/
def ipaPrechallenges {p : ℕ} [Field (ZMod p)] (params : Poseidon.Params (ZMod p))
    (s₀ : Poseidon.State (ZMod p)) (cipLimbs : List (ZMod p))
    (lr : List ((ZMod p × ZMod p) × (ZMod p × ZMod p))) (delta : ZMod p × ZMod p) :
    ZMod p × List ℕ × ℕ :=
  let r := ipaSqueezes params s₀ cipLimbs lr delta
  (r.1, r.2.1.map (·.val % 2 ^ 128), r.2.2.val % 2 ^ 128)

/-- A pair of points as coordinate pairs. -/
private def coordsPair (q : C.Point × C.Point) :
    (C.BaseField × C.BaseField) × (C.BaseField × C.BaseField) :=
  ((q.1.x, q.1.y), (q.2.x, q.2.y))

/-- The endo-expanded packing of a raw squeeze. -/
private def expandRaw (x : C.BaseField) : C.ScalarField :=
  endoExpand C.sponge.lam (x.val % 2 ^ 128)

/-- The round fold from an empty limb buffer is `ipaRound` on the automaton, its
challenges the expanded packings of the raw elements. -/
private theorem foldl_rounds (l : List (C.Point × C.Point)) (acc : List C.BaseField)
    (st : Poseidon.State C.BaseField) :
    l.foldl (roundStep C) ((acc.map (expandRaw C)).toArray, ⟨st, []⟩)
      = let r := (l.map (coordsPair C)).foldl (ipaRound C.sponge.params) (acc, st)
        ((r.1.map (expandRaw C)).toArray, ⟨r.2, []⟩) := by
  induction l generalizing acc st with
  | nil => rfl
  | cons q l ih =>
    simp only [List.foldl_cons, List.map_cons, roundStep, absorbG, absorbFq,
      squeezeChallenge_fresh, List.push_toArray, ipaRound, coordsPair]
    generalize Poseidon.squeeze C.sponge.params (Poseidon.absorb C.sponge.params
      (Poseidon.absorb C.sponge.params st [q.1.x, q.1.y]) [q.2.x, q.2.y]) = sq
    have h := ih (acc ++ [sq.1]) sq.2
    simp only [List.map_append, List.map_singleton, expandRaw] at h
    exact h

/-- `transcriptFrom` from a warm state with an empty limb buffer, through
`ipaPrechallenges`: the `U` base is the map-to-curve of `t`, the round challenges and `c`
the endo-expansions of the packed squeezes. -/
theorem transcriptFrom_eq_ipaPrechallenges (st : Poseidon.State C.BaseField)
    (inp : Input C k m p) :
    let r := ipaPrechallenges C.sponge.params st (scalarLimbs C (shiftScalar C (cipOf inp)))
      (inp.proof.lr.toList.map (coordsPair C)) (inp.proof.delta.x, inp.proof.delta.y)
    (transcriptFrom C ⟨st, []⟩ inp).1 = C.toGroup r.1 ∧
    (transcriptFrom C ⟨st, []⟩ inp).2.1.toList = r.2.1.map (endoExpand C.sponge.lam) ∧
    (transcriptFrom C ⟨st, []⟩ inp).2.2 = endoExpand C.sponge.lam r.2.2 := by
  dsimp only
  unfold transcriptFrom
  rw [absorbFr_eq]
  simp only [absorbFq, challengeFq]
  generalize hs : Poseidon.squeeze C.sponge.params
    (Poseidon.absorb C.sponge.params st (scalarLimbs C (shiftScalar C (cipOf inp)))) = sqT
  have h1 : (roundChallenges C ⟨sqT.2, []⟩ inp.proof.lr).1.toArray
      = (roundChallengesAux C ⟨sqT.2, []⟩ inp.proof.lr.toArray).1 := rfl
  have h2 : (roundChallenges C ⟨sqT.2, []⟩ inp.proof.lr).2
      = (roundChallengesAux C ⟨sqT.2, []⟩ inp.proof.lr.toArray).2 := rfl
  have hf := foldl_rounds C inp.proof.lr.toArray.toList [] sqT.2
  simp only [List.map_nil] at hf
  rw [roundChallengesAux, ← Array.foldl_toList, hf] at h1 h2
  have hl : inp.proof.lr.toArray.toList = inp.proof.lr.toList := rfl
  rw [hl] at h1 h2
  rcases hrc : roundChallenges C ⟨sqT.2, []⟩ inp.proof.lr with ⟨chals, s⟩
  rw [hrc] at h1 h2
  subst h2
  unfold ipaPrechallenges ipaSqueezes
  rw [hs]
  refine ⟨rfl, ?_, ?_⟩
  · show chals.toArray.toList = _
    rw [h1]
    simp only [List.map_map, Function.comp_def]
    unfold expandRaw
    rfl
  · simp only [absorbG, absorbFq, squeezeChallenge_fresh]

/-- The Schnorr equation of the opening at given advice: `verifyWith`'s first conjunct
with the combined inner product `cip` and the challenge-polynomial evaluation `b` as
parameters, and `P` the combined commitment. -/
def schnorrAt (σ : SRS C.Point) (uBase : C.Point) (chals : Vector C.ScalarField k)
    (c cip b : C.ScalarField) (P : C.Point) (pr : Proof C k) : Prop :=
  let Q := (pr.lr.toArray.zip chals.toArray).foldl
    (fun acc (LRu : (C.Point × C.Point) × C.ScalarField) =>
      acc + (LRu.2⁻¹.val • LRu.1.1 + LRu.2.val • LRu.1.2))
    (P + cip.val • uBase)
  c.val • Q + pr.delta = pr.z1.val • pr.sg + (pr.z1 * b).val • uBase + pr.z2.val • σ.h

/-- `verifyWith` is `schnorrAt` at the verifier's own `cipOf`, `combinedB` and combined
commitment, together with the `sg`-correctness equation. -/
theorem verifyWith_eq (σ : SRS C.Point) (uBase : C.Point) (chals : Vector C.ScalarField σ.k)
    (c : C.ScalarField) (inp : Input C σ.k m p) :
    verifyWith C σ uBase chals c inp = true ↔
      schnorrAt C σ uBase chals c (cipOf inp)
          (combinedB (fun i => chals[i]) inp.evalscale inp.pointFn)
          (combineCommitments C inp.polyscale inp.commitments.toArray) inp.proof ∧
        inp.proof.sg = msm C σ.g (bPolyCoefficients fun i => chals[i]) := by
  simp [verifyWith, schnorrAt]

end Bulletproof.Ipa

/-! ## The wire boundary: serde records and the check parse -/

namespace Bulletproof.Ipa.Wire

variable {C : CommitmentCurve}

/-- The wire opening proof (`OpeningProof`, ipa.rs): `lr` is a `Vec` — its length is
the SRS's round count, pinned by `check`. -/
structure Proof (C : CommitmentCurve) where
  /-- The per-round `(L, R)` pairs — a `Vec`; its length is pinned to the round count
  by `check`. -/
  lr : Array (C.Point × C.Point)
  /-- The Schnorr commitment `δ`. -/
  delta : C.Point
  /-- The Schnorr response scalar acting on `sg` and the `U` base. -/
  z1 : C.ScalarField
  /-- The Schnorr response scalar acting on the blinding base `H`. -/
  z2 : C.ScalarField
  /-- The challenge-folded commitment base. -/
  sg : C.Point

/-- The wire batched claim (`BatchEvaluationProof`): every payload a `Vec`. -/
structure Input (C : CommitmentCurve) where
  /-- The per-polynomial commitments. -/
  commitments : Array C.Point
  /-- The evaluation points. -/
  xs : Array C.ScalarField
  /-- The claimed evaluation matrix (`evals[i][j]` = polynomial `i` at point `j`);
  squareness against the commitments and points is `check`'s guard. -/
  evals : Array (Array C.ScalarField)
  /-- The polynomial-combination scalar `ξ`. -/
  polyscale : C.ScalarField
  /-- The evaluation-point-combination scalar `r`. -/
  evalscale : C.ScalarField
  /-- The wire opening proof. -/
  proof : Proof C

/-- Parse a wire proof at round count `k` — the checked verifier's `lr`-length
requirement as a total parse. -/
def Proof.check (k : ℕ) (w : Proof C) : Option (Ipa.Proof C k) :=
  if h : w.lr.size = k then
    some { lr := ⟨w.lr, h⟩, delta := w.delta, z1 := w.z1, z2 := w.z2, sg := w.sg }
  else none

/-- Parse a wire claim at its announced shape — the checked verifier's dimension
requirements (`evals` square against the commitments and points, the proof at round
count `k`) as a total parse into the checked input. -/
def Input.check (k : ℕ) (w : Input C) :
    Option (Ipa.Input C k w.commitments.size w.xs.size) := do
  let proof ← w.proof.check k
  let evals ← w.evals.mapM fun e =>
    if h : e.size = w.xs.size then some (⟨e, h⟩ : Vector C.ScalarField w.xs.size)
    else none
  if hm : evals.size = w.commitments.size then
    some { commitments := ⟨w.commitments, rfl⟩, xs := ⟨w.xs, rfl⟩
           evals := ⟨evals, hm⟩
           polyscale := w.polyscale, evalscale := w.evalscale, proof := proof }
  else none

end Bulletproof.Ipa.Wire

/-! ## The Pasta instantiations -/

namespace Bulletproof.IpaVesta

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta Poseidon Bulletproof

/-- The Vesta bundle. The scalar modulus is below the base modulus, so scalars absorb in
Type1 form. The scalar field is `Fp`, so `G::sponge_params()` is the `fp_kimchi`
table. -/
abbrev curve : Ipa.CommitmentCurve where
  base := PALLAS_SCALAR_CARD
  scalar := PALLAS_BASE_CARD
  sponge := FqVesta.spec
  frParams := fpParams
  E := Vesta.curve
  toGroup := GroupMapVesta.toGroup

/-- The Vesta point type. -/
abbrev Point := Ipa.CommitmentCurve.Point curve

end Bulletproof.IpaVesta

namespace Bulletproof.IpaPallas

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta Poseidon Bulletproof

/-- The Pallas bundle. The scalar modulus is above the base modulus, so scalars absorb in
Type2 form (selected by the cardinalities). The scalar field is `Fq`, so
`G::sponge_params()` is the `fq_kimchi` table. -/
abbrev curve : Ipa.CommitmentCurve where
  base := PALLAS_BASE_CARD
  scalar := PALLAS_SCALAR_CARD
  sponge := FqPallas.spec
  frParams := fqParams
  E := Pallas.curve
  toGroup := GroupMapPallas.toGroup

/-- The Pallas point type. -/
abbrev Point := Ipa.CommitmentCurve.Point curve

end Bulletproof.IpaPallas
