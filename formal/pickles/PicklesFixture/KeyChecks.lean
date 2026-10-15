import PicklesFixture.Certification

/-!
# Self-consistent wrong-key regressions

Change a commitment and recompute the verifier-index digest. The resulting key passes its
ordinary checks, but fails against the same certified index at the changed column and chunk.
Both step and wrap paths exercise the actual derivation checker, independently of a proof cache.
-/

namespace PicklesFixture.Application

open Pickles Pickles.Application Bulletproof Kimchi.Verifier
open scoped Kimchi

-- Every changed commitment column and chunk is reported at its exact location.
example :
    let columns : Vector (Vector Nat 2) (permCols + coeffCols + selectorCols) :=
      Vector.ofFn fun col => #v[2 * col.val, 2 * col.val + 1]
    (List.finRange (permCols + coeffCols + selectorCols)).all (fun col =>
      (List.finRange 2).all fun chunk =>
        match compareColumns? columns
            (columns.set col.val ((columns[col]).set chunk.val (columns[col][chunk] + 1))) with
        | some diff => diff.column == col && diff.chunk == chunk.val
        | none => false) = true := by
  decide +kernel

/-- Another wellformed key, with its first permutation commitment changed and digest updated. -/
private def alteredKey {C : Ipa.KimchiCurve} {nc : Nat} (σ : SRS C.Point) (K : KimchiVK C nc) :
    Except String (KimchiVK C nc) :=
  let old := K.sigmaComm[0]
  let changed := old.set 0 (old[0]'K.nc_pos + σ.h) K.nc_pos
  let vk := { Kimchi.Fixture.keyToWire K with
    sigmaComm := (K.sigmaComm.set 0 changed).map Vector.toArray }
  let digest := (Poseidon.squeeze C.sponge.params
    (indexStateOfCommitments C (K.sigmaComm.set 0 changed) K.coefficientsComm
      K.genericComm K.poseidonComm K.completeAddComm K.mulComm K.emulComm
      K.endomulScalarComm)).1
  match ({ vk with digest }).check nc with
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
def rejectWrongKeys (name : String) (A : ImportedApplication)
    (cert : ApplicationCertified (A.assembled.circuits A.setup (fun _ => none))) : IO Unit := do
  let C := A.assembled.circuits A.setup (fun _ => none)
  let b : A.shape.Branch := ⟨0, A.shape.branches_pos⟩
  let step ← IO.ofExcept (alteredKey C.setup.stepSrs C.wiring.backend.stepKeys[b])
  requireColumn s!"{name} step 0" (← IO.lazyPure fun _ =>
    checkKey? C.setup.stepSrs (cert.indices.step b) step (A.shape.slots b))
  let wrap ← IO.ofExcept (alteredKey C.setup.wrapSrs C.wiring.backend.wrapKey)
  requireColumn s!"{name} wrap" (← IO.lazyPure fun _ =>
    checkKey? C.setup.wrapSrs cert.indices.wrap wrap MaxProofsVerified)

end PicklesFixture.Application
