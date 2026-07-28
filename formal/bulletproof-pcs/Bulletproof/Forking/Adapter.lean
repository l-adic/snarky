import Bulletproof.Forking.Convention

/-!
# Our SRS and opening relation, as ironwood's

`Bulletproof.SRS` and `Zcash.Snark.URS` are the same structure field-for-field — our blinding base
`h` is their `w`, our IPA randomisation base `U` is their `u` — so the two are interconvertible by
a pair of mutually inverse `def`s, with both round-trips true by structure eta.

The one real difference is blinding. Our `commit σ a r = ⟨a, σ.g⟩ + r • σ.h` carries the blinder as
an argument; ironwood's `commit urs a = ⟨a, urs.g⟩` is unblinded, with blinding carried in the `w`
slot of its deployed layer. So our blinded opening relation is theirs *at the de-blinded
commitment* `P - ρ • σ.h`, which is the reconciliation proved here.

Together with `Bulletproof.Forking.Convention` this is everything needed to run ironwood's
extraction on kimchi data: `openingOfAcceptV` produces a witness for our own
`openingRelationB`, as data, with no extraction reproved on our side.
-/

namespace Bulletproof.Forking

open Bulletproof

/-! ## The structure correspondence

Neither structure carries algebraic data, so this part needs no instances on `F`. -/

section Structure

variable {G : Type*}

/-- Our SRS read as ironwood's URS: `h ↦ w`, `U ↦ u`. -/
private def ursOf (σ : SRS G) : Zcash.Snark.URS G := ⟨σ.k, σ.g, σ.h, σ.U⟩

/-- Ironwood's URS read as our SRS: `w ↦ h`, `u ↦ U`. -/
def srsOf (urs : Zcash.Snark.URS G) : SRS G := ⟨urs.k, urs.g, urs.w, urs.u⟩

@[simp] theorem ursOf_k (σ : SRS G) : (ursOf σ).k = σ.k := rfl

@[simp] theorem ursOf_g (σ : SRS G) : (ursOf σ).g = σ.g := rfl

private theorem srsOf_ursOf (σ : SRS G) : srsOf (ursOf σ) = σ := rfl

private theorem ursOf_srsOf (urs : Zcash.Snark.URS G) : ursOf (srsOf urs) = urs := rfl

end Structure

/-! ## The commitment and the opening relation -/

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Our blinded commitment is ironwood's unblinded one plus the blinding term. -/
private theorem commit_eq_zcash (σ : SRS G) (a : Fin (2 ^ σ.k) → F) (r : F) :
    commit σ a r = Zcash.Snark.commit (ursOf σ) a + r • σ.h := rfl

/-- Our blinded opening relation is ironwood's `IpaRelation` at the de-blinded commitment. -/
private theorem openingRelationB_iff_zcash (σ : SRS G) (P : G) (b : Fin (2 ^ σ.k) → F) (v : F)
    (a : Fin (2 ^ σ.k) → F) (ρ : F) :
    openingRelationB σ P b v a ρ ↔ Zcash.Snark.IpaRelation (ursOf σ) (P - ρ • σ.h) b v a := by
  constructor
  · rintro ⟨hP, hv⟩
    rw [commit_eq_zcash] at hP
    exact ⟨eq_sub_of_add_eq hP, hv.symm⟩
  · rintro ⟨hP, hv⟩
    refine ⟨?_, hv.symm⟩
    rw [commit_eq_zcash, hP]
    abel

/-- **The composite.** A kimchi accepting transcript tree yields, as data, a witness for our own
blinded opening relation. The extraction is ironwood's `ipa_extractV`, reached through the
fold-convention transport; nothing is reproved here. -/
def openingOfAcceptV (σ : SRS G) (P : G) (b : Fin (2 ^ σ.k) → F) (v ρ : F)
    (t : IpaTreeV F G σ.k) (h : IpaAcceptV σ.g b (P - ρ • σ.h) v t) :
    Σ' a : Fin (2 ^ σ.k) → F, openingRelationB σ P b v a ρ :=
  let e := ipaExtract σ.g b (P - ρ • σ.h) v t h
  ⟨e.1, (openingRelationB_iff_zcash σ P b v e.1 ρ).mpr ⟨e.2.1, e.2.2⟩⟩

end Bulletproof.Forking
