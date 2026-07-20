import Kimchi.Index.Aggregate
import Bulletproof.Protocol

/-!
# The verifier key–index correspondence

A verifier key is a tuple of commitments to a circuit's fixed columns. Soundness
concludes about a *named* circuit, so the fact that the key commits precisely that
circuit — implicit in an implementation, where one pipeline produces both — has to be
stated as a proposition.

`indexerOf` is the honest indexer: the commitments a circuit's own interpolants
determine. `VKCorresponds` says a key lies in its image. A key so produced satisfies it
definitionally; an externally supplied key satisfies it exactly when its committed
columns agree, which is a checkable condition.

Everything is stated over an abstract module with an SRS, matching the commitment layer
it composes with.
-/

open Bulletproof

namespace Kimchi.Protocol

open Polynomial Kimchi.Quotient Kimchi.Index Bulletproof

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
  sigma : Fin 7 → G
  coefficients : Fin 15 → G
  generic : G
  poseidon : G
  completeAdd : G
  varBaseMul : G
  endoMul : G
  endoScalar : G

/-- Commitment carrying a fixed unit blinder. Selector columns are committed this way
while the permutation and coefficient columns are unblinded — an asymmetry inherited
from the reference implementation. -/
noncomputable def commitPolyMasked (σ : SRS G) (p : Polynomial F) : G :=
  commitPoly σ p + σ.h

/-- The honest indexer: the verifier key a circuit determines — the commitments of its
own interpolants, selectors carrying the fixed blinder. -/
noncomputable def indexerOf (σ : SRS G) (idx : Index F n) : IndexComms G where
  sigma i := commitPoly σ (idx.sigmaPoly i)
  coefficients c := commitPoly σ (idx.coeffPoly c)
  generic := commitPolyMasked σ (idx.selectorPoly .generic)
  poseidon := commitPolyMasked σ (idx.selectorPoly .poseidon)
  completeAdd := commitPolyMasked σ (idx.selectorPoly .completeAdd)
  varBaseMul := commitPolyMasked σ (idx.selectorPoly .varBaseMul)
  endoMul := commitPolyMasked σ (idx.selectorPoly .endoMul)
  endoScalar := commitPolyMasked σ (idx.selectorPoly .endoScalar)

/-- The key–index correspondence: the committed columns are the circuit's own, i.e. the
key lies in the image of the indexer. Soundness carries it as a hypothesis. -/
def VKCorresponds (σ : SRS G) (comms : IndexComms G) (idx : Index F n) : Prop :=
  comms = indexerOf σ idx

end Kimchi.Protocol
