import CompElliptic.Curves.Pasta
import Pasta.Shifted
import Poseidon.GroupMap
import Bulletproof.Protocol

/-!
# The executable kimchi IPA verifier

The batched IPA opening verifier of kimchi (`SRS::verify`, proof-systems
`poly-commitment/src/ipa.rs`), composed as one executable function over exactly the wire
data: the per-polynomial commitments, evaluation points and claimed evaluations, the
combination scalars, and the opening proof, against a separately supplied SRS
(`Bulletproof.SRS`). Everything
transcript-derived — the `U` base, the round challenges, the Schnorr challenge — is
recomputed here through the sponge layer (the `poseidon` package); nothing is taken as input that
the wire protocol does not carry. In particular the abstract SRS's randomisation base
`σ.U` is never read: the deployed protocol derives `U` from the transcript, and relating
the derived base to the abstract one is exactly the Fiat-Shamir assumption's junction.

Generic over a single `CommitmentCurve` bundle — the Lean analogue of the Rust
`G: CommitmentCurve` associated types: the base and scalar cardinalities with their
primality facts, the sponge spec, the curve `E`, and the map-to-curve. The bundle carries
*facts*, not structures: the field structures are the canonical `ZMod` instances
synthesized from primality, so the executable and abstract layers cannot disagree on any
field operation. Points are the library's `SWPoint E` (`Point`), so the group
structure is inherited: `+`/`0` and the binary-nsmul scalar action from CompElliptic's
`AddCommGroup` instance, point equality from its `DecidableEq`. `Proof`, `Input`, and
`verify` are indexed by the bundle, so a proof's type names its curve.

The scalar side reuses the `Bulletproof` definitions (`bPoly`,
`bPolyCoefficients`, `combinedB`, `combinedInnerProduct`) at the concrete scalar field.
Scalars act on points as `z.val • _` (the ℕ-action of the group); `Reflection.lean`
relates this verifier to the `Prop`-level `BatchAccepts`.

The absorbed-scalar encoding (`shift_scalar`) is selected by the modulus comparison from
the cardinalities — the `Shifted_value` Type1 register when the scalar modulus is below
the base modulus, the Type2 shift otherwise — at the scalar-modulus bit size
`Nat.size scalar` (the Rust `MODULUS_BIT_SIZE`).

`verify` checks the two acceptance equations at the derived challenges:

* Schnorr: `c • Q + δ = z1 • sg + (z1 · b0) • U + z2 • H`,
  with `Q = P + v • U + ∑ (uⱼ⁻¹ • Lⱼ + uⱼ • Rⱼ)`, `P` the polyscale combination of the
  commitments, `v` the combined inner product, `b0` the evalscale combination of `bPoly`;
* `sg`-correctness: `sg = ⟨bPolyCoefficients chal, g⟩`.

`IpaVesta` and `IpaPallas` instantiate the two Pasta curves; both are validated against
production prover/verifier fixtures by `scripts/check_ipa_fixture.lean`.

-/

namespace Bulletproof.Ipa

open CompElliptic.CurveForms.ShortWeierstrass
open Poseidon Poseidon.FqSponge Bulletproof

/-- The per-curve data of the verifier, bundled as a single index — base and scalar
cardinalities with their primality facts, the Fq-sponge spec, the curve, and the
map-to-curve. Carrying facts rather than field structures makes every field operation
resolve to the canonical `ZMod` instances on both the executable and abstract sides. -/
structure CommitmentCurve where
  base : ℕ
  scalar : ℕ
  [primeBase : Fact (Nat.Prime base)]
  [primeScalar : Fact (Nat.Prime scalar)]
  sponge : FqSponge.Spec base scalar
  E : SWCurve (ZMod base)
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

/-- An IPA opening proof — the wire fields of `OpeningProof` (`ipa.rs`). -/
structure Proof (C : CommitmentCurve) where
  lr : Array (C.Point × C.Point)
  delta : C.Point
  z1 : C.ScalarField
  z2 : C.ScalarField
  sg : C.Point

/-- A batched opening claim, uncombined — the verifier's wire input: the per-polynomial
commitments (one segment each), the evaluation points, the claimed evaluation matrix
(`evals[i][j]` = polynomial `i` at point `j`), the combination scalars, and the proof. -/
structure Input (C : CommitmentCurve) where
  commitments : Array C.Point
  xs : Array C.ScalarField
  evals : Array (Array C.ScalarField)
  polyscale : C.ScalarField
  evalscale : C.ScalarField
  proof : Proof C

/-- The commitments as the `Fin`-indexed function of the abstract claim. -/
def Input.commitmentFn {C : CommitmentCurve} (inp : Input C) :
    Fin inp.commitments.size → C.Point :=
  fun i => inp.commitments[i]

/-- The evaluation points as the `Fin`-indexed function of the abstract claim. -/
def Input.pointFn {C : CommitmentCurve} (inp : Input C) :
    Fin inp.xs.size → C.ScalarField :=
  fun j => inp.xs[j]

/-- The claimed evaluation matrix as the indexed function of the abstract claim. The
`evals` array is ragged, so this is where the unchecked indexing of the wire form lives —
once, behind a name used identically on both sides of every statement. -/
def Input.evalFn {C : CommitmentCurve} (inp : Input C) :
    Fin inp.commitments.size → Fin inp.xs.size → C.ScalarField :=
  fun i j => (inp.evals[i.val]!)[j.val]!

/-- The combined inner product of the claimed evaluations
(`Bulletproof.combinedInnerProduct` at the wire arrays). -/
def cipOf {C : CommitmentCurve} (inp : Input C) : C.ScalarField :=
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

/-- The verifier's Fiat-Shamir schedule (`SRS::verify`): absorb the shifted combined inner
product; squeeze and map the `U` base; per round absorb `L`, `R` and squeeze a challenge;
absorb `δ` and squeeze the Schnorr challenge. -/
def transcript (inp : Input C) : C.Point × Array C.ScalarField × C.ScalarField :=
  let s := absorbFr C.sponge FqSponge.init (shiftScalar C (cipOf inp))
  let (t, s) := challengeFq C.sponge s
  let uBase := C.toGroup t
  let (chals, s) := inp.proof.lr.foldl
    (fun (acc : Array C.ScalarField × FqSponge.S C.base) LR =>
      let s := absorbG C.sponge (absorbG C.sponge acc.2 LR.1) LR.2
      let (u, s) := squeezeChallenge C.sponge s
      (acc.1.push u, s))
    (#[], s)
  let s := absorbG C.sponge s inp.proof.delta
  let (c, _) := squeezeChallenge C.sponge s
  (uBase, chals, c)

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

/-- The transcript squeezes exactly one round challenge per `(L, R)` pair. -/
private theorem transcript_chals_size (inp : Input C) :
    (transcript C inp).2.1.size = inp.proof.lr.size := by
  simp only [transcript]
  rw [← Array.foldl_toList, foldl_fst_size]
  · simp
  · intro acc a
    simp [Array.size_push]

/-- The derived round challenges as the `Fin`-indexed function the abstract layer
consumes, under the shape fact. -/
def transcriptChallenges (inp : Input C) {k : ℕ}
    (hk : (transcript C inp).2.1.size = k) : Fin k → C.ScalarField :=
  fun i => (transcript C inp).2.1[i.val]'(by omega)

/-- A batched claim at given combination scalars — the wire input the grid rows of the
soundness statements range over. -/
def mkInput (commitments : Array C.Point) (xs : Array C.ScalarField)
    (evals : Array (Array C.ScalarField)) (ξ r : C.ScalarField) (proof : Proof C) :
    Input C :=
  { commitments := commitments, xs := xs, evals := evals
    polyscale := ξ, evalscale := r, proof := proof }

/-- The acceptance decision, against a library SRS: derive the transcript, combine the
claim, and check the Schnorr and `sg`-correctness equations. Shape guards (round count
`σ.k`, evaluation matrix dimensions) reject malformed inputs. `σ.U` is never read — the
deployed `U` is transcript-derived. -/
def verify (σ : SRS C.Point) (inp : Input C) : Bool :=
  if inp.proof.lr.size != σ.k || inp.evals.size != inp.commitments.size
      || inp.evals.any (·.size != inp.xs.size) then
    false
  else
    let (uBase, chals, c) := transcript C inp
    let chal : Fin σ.k → C.ScalarField := fun i => chals[i.val]!
    let b0 := combinedB chal inp.evalscale (fun j : Fin inp.xs.size => inp.xs[j.val]!)
    let v := cipOf inp
    let P := combineCommitments C inp.polyscale inp.commitments
    let Q := (inp.proof.lr.zip chals).foldl
      (fun acc (LRu : (C.Point × C.Point) × C.ScalarField) =>
        acc + (LRu.2⁻¹.val • LRu.1.1 + LRu.2.val • LRu.1.2))
      (P + v.val • uBase)
    let schnorr := decide (c.val • Q + inp.proof.delta
      = inp.proof.z1.val • inp.proof.sg + (inp.proof.z1 * b0).val • uBase
          + inp.proof.z2.val • σ.h)
    let sgOk := decide (inp.proof.sg = msm C σ.g (bPolyCoefficients chal))
    schnorr && sgOk

/-- An accepting run has the announced round count. -/
theorem verify_shape (σ : SRS C.Point) (inp : Input C)
    (hv : verify C σ inp = true) : inp.proof.lr.size = σ.k := by
  unfold verify at hv
  split at hv
  · simp at hv
  · rename_i hguard
    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hguard
    exact hguard.1.1

/-- The round-challenge count of an accepting run, in the form `transcriptChallenges`
consumes. -/
theorem transcript_size_of_verify (σ : SRS C.Point) (inp : Input C)
    (hv : verify C σ inp = true) : (transcript C inp).2.1.size = σ.k :=
  (transcript_chals_size C inp).trans (verify_shape C σ inp hv)

end Bulletproof.Ipa

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

abbrev Point := Ipa.CommitmentCurve.Point curve
abbrev Proof := Ipa.Proof curve
abbrev Input := Ipa.Input curve

def verify : Bulletproof.SRS Point → Input → Bool := Ipa.verify curve

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

abbrev Point := Ipa.CommitmentCurve.Point curve
abbrev Proof := Ipa.Proof curve
abbrev Input := Ipa.Input curve

def verify : Bulletproof.SRS Point → Input → Bool := Ipa.verify curve

end Bulletproof.IpaPallas
