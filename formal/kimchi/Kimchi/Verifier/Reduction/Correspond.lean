import Kimchi.Columns
import Kimchi.Index.Aggregate
import Bulletproof.Protocol
import Kimchi.Verifier.Kimchi

/-!
# The verifier key–index correspondence

A verifier key is a tuple of commitments to a circuit's fixed columns. Soundness
concludes about a *named* circuit, so the fact that the key commits precisely that
circuit — implicit in an implementation, where one pipeline produces both — has to be
stated as a proposition.

`indexerOf` is the honest indexer: the commitments a circuit's own interpolants
determine, per chunk. `VKCorresponds` says a key lies in its image. A key so produced
satisfies it definitionally; an externally supplied key satisfies it exactly when its
committed columns agree, which is a checkable condition.

The abstract layer (`IndexComms`, `indexerOf`, `VKCorresponds`) is stated over an
abstract module with an SRS, matching the commitment layer it composes with. The
checked layer (`KimchiVK.comms`, `KimchiVK.Corresponds`) reads a checked wire key onto
it: `comms` is the total committed-column view, and `Corresponds` bundles the
per-chunk `VKCorresponds` with the scalar-side pins and the Lagrange pin — the full
key–index hypothesis the capstones consume, adjudicated numerically by
`check_vk_correspond`.
-/

open Bulletproof

namespace Kimchi.Verifier

open Polynomial Kimchi.Lift Kimchi.Index Bulletproof

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G] {n : ℕ}

/-- Unblinded commitment to a polynomial: the multi-scalar multiplication of its
coefficient vector against the SRS generators. Coefficients at or above the SRS width
are not read; key columns are interpolants of smaller degree. -/
noncomputable def commitPoly (σ : SRS G) (p : Polynomial F) : G :=
  commitGen σ.g (fun i => p.coeff i)

/-- A verifier key's committed columns: one commitment per fixed column family — the
seven permutation columns, the fifteen coefficient columns, and the six gate
selectors. -/
structure IndexComms (G : Type*) where
  /-- One commitment per permutation column (`permCols`). -/
  sigma : Fin permCols → G
  /-- One commitment per coefficient column (`coeffCols`). -/
  coefficients : Fin coeffCols → G
  /-- The generic selector's commitment. -/
  generic : G
  /-- The poseidon selector's commitment. -/
  poseidon : G
  /-- The completeAdd selector's commitment. -/
  completeAdd : G
  /-- The varBaseMul selector's commitment. -/
  varBaseMul : G
  /-- The endoMul selector's commitment. -/
  endoMul : G
  /-- The endoScalar selector's commitment. -/
  endoScalar : G

/-- Commitment carrying a fixed unit blinder. Selector columns are committed this way
while the permutation and coefficient columns are unblinded — an asymmetry inherited
from the reference implementation. -/
noncomputable def commitPolyMasked (σ : SRS G) (p : Polynomial F) : G :=
  commitPoly σ p + σ.h

/-! ## The chunked indexer -/

/-- Chunk `c` of the unblinded commitment of `p`: the commitment of its `c`-th
width-`2^σ.k` coefficient window (`PolyComm.chunks`). -/
noncomputable def commitPolyChunk (σ : SRS G) (p : Polynomial F) (c : ℕ) : G :=
  commitPoly σ (chunkPoly (2 ^ σ.k) p c)

/-- The fixed-unit-blinder chunk commitment: selectors (and the public commitment) are
masked with the all-ones blinder, per chunk (`mask_custom`, ipa.rs:497–514). -/
noncomputable def commitPolyMaskedChunk (σ : SRS G) (p : Polynomial F) (c : ℕ) : G :=
  commitPolyChunk σ p c + σ.h

/-- The honest chunked indexer: the verifier key a circuit determines at chunk count
`nc` — the per-chunk commitments of its own interpolants (the parent `IndexComms` at
the carrier `Fin nc → G`), selectors carrying the per-chunk fixed blinder. -/
noncomputable def indexerOf (σ : SRS G) (nc : ℕ) (idx : Index F n) :
    IndexComms (Fin nc → G) where
  sigma i c := commitPolyChunk σ (idx.sigmaPoly i) (c : ℕ)
  coefficients cc c := commitPolyChunk σ (idx.coeffPoly cc) (c : ℕ)
  generic c := commitPolyMaskedChunk σ (idx.selectorPoly .generic) (c : ℕ)
  poseidon c := commitPolyMaskedChunk σ (idx.selectorPoly .poseidon) (c : ℕ)
  completeAdd c := commitPolyMaskedChunk σ (idx.selectorPoly .completeAdd) (c : ℕ)
  varBaseMul c := commitPolyMaskedChunk σ (idx.selectorPoly .varBaseMul) (c : ℕ)
  endoMul c := commitPolyMaskedChunk σ (idx.selectorPoly .endoMul) (c : ℕ)
  endoScalar c := commitPolyMaskedChunk σ (idx.selectorPoly .endoScalar) (c : ℕ)

/-- The chunked key–index correspondence: the committed chunk columns are the circuit's
own. -/
def VKCorresponds (σ : SRS G) (nc : ℕ) (comms : IndexComms (Fin nc → G))
    (idx : Index F n) : Prop :=
  comms = indexerOf σ nc idx

/-! ## The checked key's view and correspondence -/

/-- The committed-column view of a checked verifier key: the `IndexComms` over
per-chunk carriers (`Fin nc → C.Point`) the reduction speaks about — every read
total. The glue between the checked wire and the abstract capstones. -/
def KimchiVK.comms {C : Ipa.CommitmentCurve} {nc : ℕ}
    (cvk : KimchiVK C nc) : IndexComms (Fin nc → C.Point) where
  sigma i c := (cvk.sigmaComm[i])[c]
  coefficients cc c := (cvk.coefficientsComm[cc])[c]
  generic c := cvk.genericComm[c]
  poseidon c := cvk.poseidonComm[c]
  completeAdd c := cvk.completeAddComm[c]
  varBaseMul c := cvk.mulComm[c]
  endoMul c := cvk.emulComm[c]
  endoScalar c := cvk.endomulScalarComm[c]

/-- **The checked key–index correspondence**: the committed chunk columns are the
circuit's own (`VKCorresponds`, through the total `comms` view), the scalar-side
parameters match (the domain generator, the zero-knowledge row count, the shifts, the
`ft_eval0` endo coefficient, and the Poseidon MDS — read off the curve's fr-sponge
table), AND the Lagrange-basis chunk commitments over the public region are the basis
polynomials' own chunk commitments. The Lagrange pin is what binds the proof-carried
public evaluations (the public batch row) to the circuit's public input: the verifier
COMPUTES the public commitment from these key entries. Adjudicated numerically, per
chunk, by `check_vk_correspond`. -/
def KimchiVK.Corresponds {C : Ipa.CommitmentCurve}
    [Module C.ScalarField C.Point] {nc : ℕ} {n : ℕ}
    (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (idx : Index C.ScalarField n) : Prop :=
  VKCorresponds σ nc cvk.comms idx
    ∧ cvk.omega = idx.omega
    ∧ cvk.zkRows = idx.zkRows
    ∧ (fun i : Fin permCols => cvk.shifts[i]) = idx.shifts
    ∧ cvk.endo = idx.endoBase
    ∧ mdsOfParams C.frParams = idx.mds
    ∧ ∀ (j : Fin n), (j : ℕ) < idx.publicCount →
        ∀ (hj : (j : ℕ) < cvk.lagrangeBasis.size) (c : Fin nc),
          (cvk.lagrangeBasis[(j : ℕ)]'hj)[c]
            = commitPolyChunk σ
                (columnPoly idx.omega (Kimchi.Permutation.rowIndicator j)) (c : ℕ)

end Kimchi.Verifier
