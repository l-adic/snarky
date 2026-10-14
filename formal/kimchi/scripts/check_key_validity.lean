import KimchiFixture.Kimchi

/-!
Focused wire-key regressions: accept production keys at one and two chunks on both curves,
then reject malformed dimensions, curve constants, domain metadata and commitment digests.
No proof verification or index commitment derivation is run here.

Run from `formal/`: `lake env lean --run kimchi/scripts/check_key_validity.lean`.
-/

open Lean Bulletproof Kimchi.Verifier

private def checkKey (C : Ipa.KimchiCurve) (nc : Nat) (path : String) : IO Unit := do
  let raw ← IO.FS.readFile path
  let vk ← IO.ofExcept (Json.parse raw >>= Kimchi.Fixture.parseVK C)
  let some checked := vk.check nc
    | throw (IO.userError s!"{path}: valid key rejected")
  unless (Kimchi.Fixture.keyToWire checked).check nc |>.isSome do
    throw (IO.userError s!"{path}: checked key lost data on the wire")
  unless (vk.check 0).isNone do
    throw (IO.userError s!"{path}: zero chunks accepted")
  let corruptions : Array (String × Wire.KimchiVK C) := #[
    ("ragged commitment", { vk with sigmaComm := vk.sigmaComm.set 0 vk.sigmaComm[0].pop }),
    ("oversized public input", { vk with publicCount := 2 ^ vk.domainLog2 + 1 }),
    ("endomorphism coefficient", { vk with endo := vk.endo + 1 }),
    ("zero-knowledge count", { vk with zkRows := vk.zkRows + 1 }),
    ("domain too small for zero-knowledge rows", { vk with
      domainLog2 := 0, omega := domainGenerator C 0, publicCount := 0 }),
    ("domain beyond two-adicity", { vk with
      domainLog2 := C.twoAdicity + 1, omega := domainGenerator C (C.twoAdicity + 1) }),
    ("domain generator", { vk with omega := vk.omega + 1 }),
    ("permutation shifts", { vk with shifts := vk.shifts.set 0 (vk.shifts[0] + 1) }),
    ("commitment digest", { vk with digest := vk.digest + 1 })]
  for (label, bad) in corruptions do
    unless (bad.check nc).isNone do
      throw (IO.userError s!"{path}: accepted invalid {label}")
  IO.println s!"✓ {path}: accepted valid key; rejected {corruptions.size + 1} invalid keys"

def main : IO Unit := do
  checkKey IpaVesta.curve 1 "kimchi/fixtures/kimchi_proof_vesta.json"
  checkKey IpaVesta.curve 2 "kimchi/fixtures/kimchi_proof_vesta_nc2.json"
  checkKey IpaPallas.curve 2 "kimchi/fixtures/kimchi_proof_pallas_nc2.json"
  checkKey IpaPallas.curve 1 "kimchi/fixtures/kimchi_proof_pallas_pickles.json"
