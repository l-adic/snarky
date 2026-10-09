import PicklesFixture.ImportedIndices

/-!
# Self-consistent wrong-key regressions

Change a commitment and recompute the verifier-index digest. The resulting key passes its
ordinary checks, but fails against the same certified index at the changed column and chunk.
Both step and wrap paths exercise the actual derivation checker, independently of a proof cache.
-/

namespace PicklesFixture.Application

open Pickles Pickles.Application Bulletproof Kimchi.Verifier

/-- Another wellformed key, with its first permutation commitment changed and digest updated. -/
private def alteredKey {C : Ipa.KimchiCurve} {nc : Nat} (σ : SRS C.Point) (K : Key C nc) :
    Except String (Key C nc) :=
  let old := K.cvk.sigmaComm[0]
  let changed := old.set 0 (old[0]'K.cvk.nc_pos + σ.h) K.cvk.nc_pos
  let vk := { K.cvk with sigmaComm := K.cvk.sigmaComm.set 0 changed }
  let vk := { vk with digest := vk.indexDigest }
  match Key.check vk with
  | none => .error "the changed key with recomputed digest failed its ordinary key checks"
  | some key => .ok key

private def requireColumn {α : Type} (name : String) : Except KeyFailure α → IO Unit
  | .error (.commitment ⟨col, chunk⟩) =>
    if col.val = 0 && chunk = 0 then
      IO.println s!"✓ {name}: self-consistent wrong key rejected at sigma 0, chunk 0"
    else throw (IO.userError s!"{name}: wrong key rejected at column {col.val}, chunk {chunk}")
  | .error f => throw (IO.userError s!"{name}: wrong key rejected before comparison: {f.describe}")
  | .ok _ => throw (IO.userError s!"{name}: self-consistent wrong key was accepted")

/-- Ordinary key validity does not allow another circuit's commitments to certify. -/
def rejectWrongKeys (name : String) (A : ImportedApplication) (r : Certification A) : IO Unit := do
  let C := A.assembled.circuits A.setup (fun _ => none)
  let b : A.shape.Branch := ⟨0, A.shape.branches_pos⟩
  let step ← IO.ofExcept (alteredKey C.setup.stepSrs.σ C.wiring.backend.stepKeys[b])
  requireColumn s!"{name} step 0" (← IO.lazyPure fun _ =>
    checkKey? pastaShapeVesta C.setup.stepSrs.σ (r.cert.indices.step b) step (A.shape.slots b))
  let wrap ← IO.ofExcept (alteredKey C.setup.wrapSrs.σ C.wiring.backend.wrapKey)
  requireColumn s!"{name} wrap" (← IO.lazyPure fun _ =>
    checkKey? pastaShapePallas C.setup.wrapSrs.σ r.cert.indices.wrap wrap MaxProofsVerified)

end PicklesFixture.Application
