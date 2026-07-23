import CompElliptic.Curves.Pasta
import Pasta.Shifted
import Poseidon.GroupMap
import Bulletproof.Protocol

/-!
# The executable kimchi IPA verifier, over checked records

The batched IPA opening verifier of kimchi (`SRS::verify`, proof-systems
`poly-commitment/src/ipa.rs`), composed as one executable function over the CHECKED
claim: the per-polynomial commitments, evaluation points and claimed evaluations, the
combination scalars, and the opening proof, against a separately supplied SRS
(`Bulletproof.SRS`). Everything
transcript-derived — the `U` base, the round challenges, the Schnorr challenge — is
recomputed here through the sponge layer (the `poseidon` package); nothing is taken as
input that the wire protocol does not carry. In particular the abstract SRS's
randomisation base `σ.U` is never read: the deployed protocol derives `U` from the
transcript, and relating the derived base to the abstract one is exactly the
Fiat-Shamir assumption's junction.

**The checked records carry their shape in their types.** `Proof C k` pins the round
count (`lr` is a `Vector` of length `k` — the SRS's `σ.k`); `Input C k m p` pins the
batch shape (`m` rows, `p` evaluation points, the claimed-evaluation matrix a
`Vector` of `Vector`s). Every read of the verifier and of every statement over it is
total; a checked input cannot hold a ragged claim. The raw serde records
(`Wire.Proof`, `Wire.Input` — every payload a `Vec`) live in the `Wire` namespace
below with their `check` parses, which are the verifier's own dimension guards
(round count, `evals` square against the commitments and points) factored as a total
parse — the parse IS the proof. Clients compose check-then-verify; rejecting ragged
input is the same observable behavior as the guards' `false` returns.

Generic over a single `CommitmentCurve` bundle — the Lean analogue of the Rust
`G: CommitmentCurve` associated types: the base and scalar cardinalities with their
primality facts, the sponge spec, the curve `E`, and the map-to-curve. The bundle
carries *facts*, not structures: the field structures are the canonical `ZMod`
instances synthesized from primality, so the executable and abstract layers cannot
disagree on any field operation. Points are the library's `SWPoint E` (`Point`), so
the group structure is inherited: `+`/`0` and the binary-nsmul scalar action from
CompElliptic's `AddCommGroup` instance, point equality from its `DecidableEq`.

The scalar side reuses the `Bulletproof` definitions (`bPoly`,
`bPolyCoefficients`, `combinedB`, `combinedInnerProduct`) at the concrete scalar
field. Scalars act on points as `z.val • _` (the ℕ-action of the group);
`Reflection.lean` relates this verifier to the `Prop`-level `BatchAccepts`.

The absorbed-scalar encoding (`shift_scalar`) is selected by the modulus comparison
from the cardinalities — the `Shifted_value` Type1 register when the scalar modulus is
below the base modulus, the Type2 shift otherwise — at the scalar-modulus bit size
`Nat.size scalar` (the Rust `MODULUS_BIT_SIZE`).

`verify` checks the two acceptance equations at the derived challenges:

* Schnorr: `c • Q + δ = z1 • sg + (z1 · b0) • U + z2 • H`,
  with `Q = P + v • U + ∑ (uⱼ⁻¹ • Lⱼ + uⱼ • Rⱼ)`, `P` the polyscale combination of the
  commitments, `v` the combined inner product, `b0` the evalscale combination of
  `bPoly`;
* `sg`-correctness: `sg = ⟨bPolyCoefficients chal, g⟩`.

`IpaVesta` and `IpaPallas` instantiate the two Pasta curves; both are validated
against production prover/verifier fixtures by `scripts/check_ipa_fixture.lean`
(which parses the wire records and composes check-then-verify).

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
  /-- The Fq-sponge spec driving the verifier's Fiat-Shamir transcript. -/
  sponge : FqSponge.Spec base scalar
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

/-- The per-round challenge fold (the round loop of `SRS::verify`): absorb `L` and `R`,
squeeze one challenge, threading the sponge state — one push per `(L, R)` pair. The
array-level engine of `roundChallenges`; the fold state is concrete data. -/
def roundChallengesAux (s : FqSponge.S C.base) (lr : Array (C.Point × C.Point)) :
    Array C.ScalarField × FqSponge.S C.base :=
  lr.foldl
    (fun (acc : Array C.ScalarField × FqSponge.S C.base) LR =>
      let s := absorbG C.sponge (absorbG C.sponge acc.2 LR.1) LR.2
      let (u, s) := squeezeChallenge C.sponge s
      (acc.1.push u, s))
    (#[], s)

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
  simp only [roundChallengesAux]
  rw [← Array.foldl_toList, foldl_fst_size]
  · simp
  · intro acc a
    simp [Array.size_push]

/-- The round challenges of a checked proof, from a given sponge state: the challenge
vector — sized by construction, one challenge per round — and the post-fold sponge
state. -/
def roundChallenges (s : FqSponge.S C.base) {k : ℕ} (lr : Vector (C.Point × C.Point) k) :
    Vector C.ScalarField k × FqSponge.S C.base :=
  let r := roundChallengesAux C s lr.toArray
  (⟨r.1, (roundChallengesAux_size C s lr.toArray).trans lr.size_toArray⟩, r.2)

/-- The verifier's Fiat-Shamir schedule (`SRS::verify`): absorb the shifted combined inner
product; squeeze and map the `U` base; per round absorb `L`, `R` and squeeze a challenge;
absorb `δ` and squeeze the Schnorr challenge. The round challenges come back as a
`Vector` at the checked round count, so every downstream read is total. -/
def transcript (inp : Input C k m p) :
    C.Point × Vector C.ScalarField k × C.ScalarField :=
  let s := absorbFr C.sponge FqSponge.init (shiftScalar C (cipOf inp))
  let (t, s) := challengeFq C.sponge s
  let uBase := C.toGroup t
  let (chals, s) := roundChallenges C s inp.proof.lr
  let s := absorbG C.sponge s inp.proof.delta
  let (c, _) := squeezeChallenge C.sponge s
  (uBase, chals, c)

/-- A batched claim at given combination scalars — the checked input the grid rows of
the soundness statements range over. The curve is implicit (inferred from the
commitment vector). -/
def mkInput {C : CommitmentCurve} {k m p : ℕ} (commitments : Vector C.Point m)
    (xs : Vector C.ScalarField p) (evals : Vector (Vector C.ScalarField p) m)
    (ξ r : C.ScalarField) (proof : Proof C k) : Input C k m p :=
  { commitments := commitments, xs := xs, evals := evals
    polyscale := ξ, evalscale := r, proof := proof }

/-- The acceptance decision, against a library SRS: derive the transcript, combine the
claim, and check the Schnorr and `sg`-correctness equations. The claim's shape is
carried by its type (round count `σ.k`), so there are no runtime guards — rejecting
ragged input is the wire parse's job. `σ.U` is never read — the deployed `U` is
transcript-derived. -/
def verify (σ : SRS C.Point) (inp : Input C σ.k m p) : Bool :=
  let (uBase, chals, c) := transcript C inp
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

/-- Parse a wire proof at round count `k` — the verifier's `lr`-length guard as a
total parse. -/
def Proof.check (k : ℕ) (w : Proof C) : Option (Ipa.Proof C k) :=
  if h : w.lr.size = k then
    some { lr := ⟨w.lr, h⟩, delta := w.delta, z1 := w.z1, z2 := w.z2, sg := w.sg }
  else none

/-- Parse a wire claim at its announced shape — the verifier's dimension guards
(`evals` square against the commitments and points, the proof at round count `k`) as
a total parse into the checked input. -/
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
Type1 form. -/
abbrev curve : Ipa.CommitmentCurve where
  base := PALLAS_SCALAR_CARD
  scalar := PALLAS_BASE_CARD
  sponge := FqVesta.spec
  E := Vesta.curve
  toGroup := GroupMapVesta.toGroup

/-- The Vesta point type. -/
abbrev Point := Ipa.CommitmentCurve.Point curve

/-- The checked opening proof at round count `k`, over Vesta. -/
abbrev Proof (k : ℕ) := Ipa.Proof curve k

/-- The checked batched claim over Vesta. -/
abbrev Input (k m p : ℕ) := Ipa.Input curve k m p

/-- The wire (serde) opening proof over Vesta. -/
abbrev WireProof := Ipa.Wire.Proof curve

/-- The wire (serde) batched claim over Vesta. -/
abbrev WireInput := Ipa.Wire.Input curve

/-- `Ipa.verify` at the Vesta bundle. -/
def verify (σ : Bulletproof.SRS Point) {m p : ℕ} : Input σ.k m p → Bool :=
  Ipa.verify curve σ

end Bulletproof.IpaVesta

namespace Bulletproof.IpaPallas

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta Poseidon Bulletproof

/-- The Pallas bundle. The scalar modulus is above the base modulus, so scalars absorb in
Type2 form (selected by the cardinalities). -/
abbrev curve : Ipa.CommitmentCurve where
  base := PALLAS_BASE_CARD
  scalar := PALLAS_SCALAR_CARD
  sponge := FqPallas.spec
  E := Pallas.curve
  toGroup := GroupMapPallas.toGroup

/-- The Pallas point type. -/
abbrev Point := Ipa.CommitmentCurve.Point curve

/-- The checked opening proof at round count `k`, over Pallas. -/
abbrev Proof (k : ℕ) := Ipa.Proof curve k

/-- The checked batched claim over Pallas. -/
abbrev Input (k m p : ℕ) := Ipa.Input curve k m p

/-- The wire (serde) opening proof over Pallas. -/
abbrev WireProof := Ipa.Wire.Proof curve

/-- The wire (serde) batched claim over Pallas. -/
abbrev WireInput := Ipa.Wire.Input curve

/-- `Ipa.verify` at the Pallas bundle. -/
def verify (σ : Bulletproof.SRS Point) {m p : ℕ} : Input σ.k m p → Bool :=
  Ipa.verify curve σ

end Bulletproof.IpaPallas
