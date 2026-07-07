import CompElliptic.Curves.Pasta
import Kimchi.Shifted
import Kimchi.Sponge.GroupMap
import Kimchi.Commitment.IPA.Batch

/-!
# The executable kimchi IPA verifier

The batched IPA opening verifier of kimchi (`SRS::verify`, proof-systems
`poly-commitment/src/ipa.rs`), composed as one executable function over exactly the wire
data: the per-polynomial commitments, evaluation points and claimed evaluations, the
combination scalars, and the opening proof, against a separately supplied SRS
(`Kimchi.Commitment.IPA.SRS`, as everywhere in the library). Everything
transcript-derived — the `U` base, the round challenges, the Schnorr challenge — is
recomputed here through the sponge layer (`Kimchi/Sponge`); nothing is taken as input that
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

The scalar side reuses the `Kimchi.Commitment.IPA` definitions (`bPoly`,
`bPolyCoefficients`, `combinedB`, `combinedInnerProduct`) at the concrete scalar field.
Scalars act on points as `z.val • _` (the ℕ-action of the group): the `C.ScalarField`-module
structure on `Point` is the reflection concern relating this verifier to the `Prop`-level
`BatchAccepts`, not stated here.

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

## Contents

* `CommitmentCurve`, `Point` — the curve bundle and the inherited point type.
* `Proof`, `Input` — the wire data, indexed by the curve.
* `shiftScalar` — the absorbed-scalar encoding, selected from the cardinalities.
* `transcript` — the Fiat-Shamir schedule: `(U, chal, c)` from the wire data.
* `verify` — the acceptance decision, against a library `SRS`.
* `IpaVesta`, `IpaPallas` — the Pasta instantiations.
-/

namespace Kimchi.Verifier.Ipa

open CompElliptic.CurveForms.ShortWeierstrass
open Kimchi.Sponge Kimchi.Sponge.FqSponge Kimchi.Commitment.IPA

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
`Kimchi.Commitment.IPA.commitGen`, with the scalars acting through `val`. -/
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
commitments (one chunk each), the evaluation points, the claimed evaluation matrix
(`evals[i][j]` = polynomial `i` at point `j`), the combination scalars, and the proof. -/
structure Input (C : CommitmentCurve) where
  commitments : Array C.Point
  xs : Array C.ScalarField
  evals : Array (Array C.ScalarField)
  polyscale : C.ScalarField
  evalscale : C.ScalarField
  proof : Proof C

/-- The combined inner product of the claimed evaluations
(`Kimchi.Commitment.IPA.combinedInnerProduct` at the wire arrays). -/
def cipOf {C : CommitmentCurve} (inp : Input C) : C.ScalarField :=
  combinedInnerProduct inp.polyscale inp.evalscale
    (fun (i : Fin inp.commitments.size) (j : Fin inp.xs.size) => (inp.evals[i.val]!)[j.val]!)

/-- The polyscale combination `∑ i, ξ^i • Cᵢ` of the commitments — the group-side mirror
of `Kimchi.Commitment.IPA.combinedCommitment`, by a running power. -/
def combineCommitments (ξ : C.ScalarField) (cs : Array C.Point) : C.Point :=
  (cs.foldl (fun (acc : C.Point × C.ScalarField) P => (acc.1 + acc.2.val • P, acc.2 * ξ))
    (0, 1)).1

/-- The transcript encoding of an absorbed scalar (`shift_scalar`,
`poly-commitment/src/commitment.rs`): the `Shifted_value` register form at the
scalar-modulus bit size `Nat.size scalar` (the Rust `MODULUS_BIT_SIZE`) — Type1
(`(x − 2ᵇ − 1)/2`) when the scalar modulus is below the base modulus, the Type2 shift
(`x − 2ᵇ`) otherwise. The branch is the Rust `n1 < n2`, decided from the cardinalities. -/
def shiftScalar (x : C.ScalarField) : C.ScalarField :=
  if C.scalar < C.base then Kimchi.Shifted.shiftType1 (Nat.size C.scalar) x
  else Kimchi.Shifted.shiftType2 (Nat.size C.scalar) x

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

end Kimchi.Verifier.Ipa

/-! ## The Pasta instantiations -/

namespace Kimchi.Verifier.IpaVesta

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta Kimchi.Sponge Kimchi.Verifier

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

def verify : Kimchi.Commitment.IPA.SRS Point → Input → Bool := Ipa.verify curve

end Kimchi.Verifier.IpaVesta

namespace Kimchi.Verifier.IpaPallas

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta Kimchi.Sponge Kimchi.Verifier

/-- The Pallas bundle. The scalar modulus is above the base modulus, so scalars absorb in
Type2 form — selected by the cardinalities, not restated here. -/
abbrev curve : Ipa.CommitmentCurve where
  base := PALLAS_BASE_CARD
  scalar := PALLAS_SCALAR_CARD
  sponge := FqPallas.spec
  E := Pallas.curve
  toGroup := GroupMapPallas.toGroup

abbrev Point := Ipa.CommitmentCurve.Point curve
abbrev Proof := Ipa.Proof curve
abbrev Input := Ipa.Input curve

def verify : Kimchi.Commitment.IPA.SRS Point → Input → Bool := Ipa.verify curve

end Kimchi.Verifier.IpaPallas
