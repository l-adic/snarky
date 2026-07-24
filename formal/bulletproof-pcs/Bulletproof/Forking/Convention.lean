import Bulletproof.Soundness
import Zcash.Snark.Soundness.IpaSoundness

/-!
# Reconciling the two IPA fold conventions

`zcash/ironwood` formalizes the same recursive IPA, but folds the generators the other way:

```
Bulletproof.foldHalves v u = loHalf v + u  • hiHalf v      -- kimchi
Zcash.Snark.foldGens   g u = loHalf g + u⁻¹ • hiHalf g     -- halo2
```

Both acceptance predicates update the commitment by `P + u⁻¹ • L + u • R`, so this is *not* a
naming difference: `Bulletproof.IpaAcceptV` and `Zcash.Snark.IpaAcceptV` are different predicates,
and neither can be substituted for the other. Reusing ironwood's extraction, AGM and forking
machinery at kimchi's parameters therefore goes through the transport proved here.

## Which convention is kimchi's

Kimchi's, i.e. ours. The verifier checks `sg = ⟨bPolyCoefficients chal, g⟩` (`Wire.lean`), and
`bPolyCoefficients chal m = ∏ j, if testBit m j then chal (Fin.rev j) else 1` is the coefficient
vector obtained by folding the generators with the *high half scaled by the challenge* — the
`foldHalves` convention. `Protocol.lean` records the same asymmetry on the polynomial side:
`bPoly = ∏ (1 + u · X ^ 2 ^ i)`, the linear form, not the symmetric `∏ (u⁻¹ + u · X ^ 2 ^ i)`.

## The transport

Substituting `u := w⁻¹` into ironwood's fold gives ours, and carries the commitment update to
`P + w • L + w⁻¹ • R` — which is ours with the two cross-terms exchanged. So an accepting tree in
our convention is an accepting tree in theirs, at inverted challenges and with `L`/`R` (and
`Lv`/`Rv`) swapped. `toZcash` performs exactly that rewiring; the tree is otherwise unchanged.
-/

namespace Bulletproof.Forking

open Bulletproof

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Rewire a kimchi-convention transcript tree into ironwood's convention: invert every round
challenge and exchange the two cross-terms at each node. Leaves are unchanged. -/
def toZcash : {d : ℕ} → IpaTreeV F G d → Zcash.Snark.IpaTreeV F G d
  | 0, .leaf c => .leaf c
  | _ + 1, .node L R Lv Rv u₁ u₂ u₃ t₁ t₂ t₃ =>
      .node R L Rv Lv u₁⁻¹ u₂⁻¹ u₃⁻¹ (toZcash t₁) (toZcash t₂) (toZcash t₃)

/-- Our generator fold at `u` is ironwood's at `u⁻¹`. -/
theorem foldGens_inv {M : Type*} [AddCommGroup M] [Module F M] {k : ℕ}
    (v : Fin (2 ^ (k + 1)) → M) (u : F) :
    Zcash.Snark.foldGens (F := F) v u⁻¹ = foldHalves v u := by
  simp only [Zcash.Snark.foldGens, foldHalves, inv_inv]
  rfl

/-- **The transport.** An accepting tree in kimchi's convention is an accepting tree in
ironwood's, after `toZcash`. This is what lets `Zcash.Snark.ipa_extractV` and the AGM/forking
stack run on kimchi transcripts. -/
theorem zcash_ipaAcceptV_toZcash : {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) →
    (P : G) → (v : F) → (t : IpaTreeV F G d) → IpaAcceptV g b P v t →
    Zcash.Snark.IpaAcceptV g b P v (toZcash t)
  | 0, _, _, _, _, .leaf _, h => h
  | _ + 1, g, b, P, v, .node L R Lv Rv u₁ u₂ u₃ t₁ t₂ t₃, h => by
      obtain ⟨h12, h13, h23, hu₁, hu₂, hu₃, ha₁, ha₂, ha₃⟩ := h
      refine ⟨fun hc => h12 (inv_inj.mp hc), fun hc => h13 (inv_inj.mp hc),
        fun hc => h23 (inv_inj.mp hc), inv_ne_zero hu₁, inv_ne_zero hu₂, inv_ne_zero hu₃,
        ?_, ?_, ?_⟩
      · rw [foldGens_inv, foldGens_inv, inv_inv,
          show P + u₁ • R + u₁⁻¹ • L = P + u₁⁻¹ • L + u₁ • R from by abel,
          show v + u₁ • Rv + u₁⁻¹ • Lv = v + u₁⁻¹ • Lv + u₁ • Rv from by abel]
        exact zcash_ipaAcceptV_toZcash _ _ _ _ t₁ ha₁
      · rw [foldGens_inv, foldGens_inv, inv_inv,
          show P + u₂ • R + u₂⁻¹ • L = P + u₂⁻¹ • L + u₂ • R from by abel,
          show v + u₂ • Rv + u₂⁻¹ • Lv = v + u₂⁻¹ • Lv + u₂ • Rv from by abel]
        exact zcash_ipaAcceptV_toZcash _ _ _ _ t₂ ha₂
      · rw [foldGens_inv, foldGens_inv, inv_inv,
          show P + u₃ • R + u₃⁻¹ • L = P + u₃⁻¹ • L + u₃ • R from by abel,
          show v + u₃ • Rv + u₃⁻¹ • Lv = v + u₃⁻¹ • Lv + u₃ • Rv from by abel]
        exact zcash_ipaAcceptV_toZcash _ _ _ _ t₃ ha₃

/-- **Data-valued extraction at kimchi's convention**, by running ironwood's computable
`ipa_extractV` through the transport. The witness is returned as data (`Σ'`), not asserted to
exist — which is the whole point, since the existential form is free at the deployed
instantiation (`Forking.Extraction.ipa_knowledge_soundness_conclusion_free`).

This is the reuse the transport exists to enable: no extraction is reproved here. -/
def ipaExtract {d : ℕ} (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → F) (P : G) (v : F)
    (t : IpaTreeV F G d) (h : IpaAcceptV g b P v t) :
    Σ' a : Fin (2 ^ d) → F, commitGen g a = P ∧ commitGen b a = v :=
  Zcash.Snark.ipa_extractV g b P v (toZcash t) (zcash_ipaAcceptV_toZcash g b P v t h)

end Bulletproof.Forking
