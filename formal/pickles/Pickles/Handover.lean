import Pickles.TwoHalves

/-!
# The accumulator handover along a chain of proofs

Pickles never checks a proof's deferred `sg` equation (`SgOk`) on the proof itself: the proof's
`(sg, round challenges)` becomes an old accumulator of the next proof on the same curve, whose
batch opening checks it (`accOk`). Each capstone gives its proof `kimchiVerify` from `SgOk`.
This module composes those along a chain in which each proof carries its predecessor's
obligation (`carry`).

## Main results

* `chain_kimchiVerify_iff`: in a carried chain, every proof verifies exactly when every
  carried accumulator passes `accOk`, the last proof's own `SgOk` being given.

## Implementation notes

The chain is deterministic: nothing here says that a proof's acceptance certifies the
accumulators it carries. The first opening equation can be solved for any old `sg`, so that
implication is cryptographic and stays out of the tree; the theorem reduces verification to
exactly the `accOk` checks.
-/

namespace Pickles

open Kimchi.Verifier Bulletproof Bulletproof.Ipa

variable {C : KimchiCurve}

/-- **A carried chain verifies exactly when its carried accumulators pass the deferred
check.** Each proof's capstone gives it `kimchiVerify` from its `SgOk`, `carry` makes a proof's
`SgOk` the next proof's `accOk`, and the last proof's `SgOk` is given. -/
theorem chain_kimchiVerify_iff {m : ℕ} (σ : SRS C.Point) {nc : Fin (m + 1) → ℕ}
    (cvk : (k : Fin (m + 1)) → KimchiVK C (nc k))
    (P : (k : Fin (m + 1)) → KimchiProof C (nc k) σ.k)
    (pub : Fin (m + 1) → Array C.ScalarField)
    -- each proof's capstone
    (hcap : ∀ k, Guards C (cvk k) (P k) (pub k) →
      SgOk σ (cvk k) (P k) (pub k) → kimchiVerify C σ (cvk k) (P k) (pub k) = true)
    (hg : ∀ k, Guards C (cvk k) (P k) (pub k))
    -- each proof carries its predecessor's obligation as its old accumulator `j k`
    (j : (k : Fin m) → Fin (P k.succ).olds.size)
    (hcarry : ∀ k : Fin m,
      carry σ (cvk k.castSucc) (P k.castSucc) (pub k.castSucc) (P k.succ) (j k) = true)
    -- the last proof's deferred equation, checked out of circuit
    (hlast : SgOk σ (cvk (Fin.last m)) (P (Fin.last m)) (pub (Fin.last m))) :
    (∀ k, kimchiVerify C σ (cvk k) (P k) (pub k) = true) ↔
      ∀ k : Fin m, accOk σ (P k.succ).olds[j k] = true := by
  constructor
  · intro hv k
    exact (sgOk_iff_accOk_of_carry σ _ _ _ _ _ (hcarry k)).mp
      (sgOk_of_kimchiVerify σ _ _ _ (hv k.castSucc))
  · intro hacc k
    refine hcap k (hg k) ?_
    induction k using Fin.lastCases with
    | last => exact hlast
    | cast k => exact (sgOk_iff_accOk_of_carry σ _ _ _ _ _ (hcarry k)).mpr (hacc k)

end Pickles
