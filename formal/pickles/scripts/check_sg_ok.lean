import Pickles.TwoHalves
import KimchiFixture.Kimchi
import Kimchi.Verifier.Wire
import Lean.Data.Json

/-!
# The deferred `sg` obligation against a deployed wrap proof

`Pickles.SgOk` is the one conjunct of `verifyWith` that the per-proof checkpoint
(`Pickles.twoHalves_kimchiVerify`) carries as a hypothesis rather than discharging: no circuit
computes it, because pickles defers it. A chain only ever terminates after a wrap, so it is the
out-of-circuit verifier of the final wrap proof that checks it, and this driver runs that check
in the form the verifier would — `Pickles.sgOk`, the decidable form of `SgOk`.

The fixture is `kimchi_proof_pallas_pickles.json`, a deployed pickles wrap proof (OCaml through
the Rust prover, `simple_chain`'s second wrap) with its two old accumulators, at the wrap domain
`2^14` below the `2^15` Tock SRS. It is the same artifact
`kimchi/scripts/check_kimchi_verifier.lean` runs the whole verifier on.

Three assertions, the last two of which keep the first from adjudicating vacuously:

* the proof verifies and `sgOk` accepts it;
* bumping the opening's `sg` flips it — the left-hand side is live;
* bumping `ft_eval1` flips it. This is the informative control: an evaluation feeds the
  fr-transcript, which fixes the round challenges, which fix the `bPolyCoefficients` the
  right-hand side commits to. Without it a passing check could be comparing `sg` to itself.

Run: `KIMCHI_FIXTURES_DIR=kimchi/fixtures lake env lean --run pickles/scripts/check_sg_ok.lean`
from `formal/`, or bare from this package. The opening MSM over `2^14` points dominates the
runtime.
-/

open Lean FixtureKit Bulletproof Bulletproof.Fixture Kimchi.Verifier Pickles

/-- The commitment curve of a wrap proof. -/
abbrev CP := IpaPallas.curve

/-- The fixture's records: the SRS at the dumped `max_poly_size`, the wire key, the wire proof
and the public input. -/
def parseFixture (raw : String) :
    Except String (SRS CP.Point × Wire.KimchiVK CP × Wire.KimchiProof CP ×
      Array CP.ScalarField) := do
  let j ← Json.parse raw
  let vk ← Kimchi.Fixture.parseVK CP j
  let mps ← match (← (← j.getObjVal? "max_poly_size").getStr?).toNat? with
    | some v => pure v
    | none => throw "field max_poly_size is not a numeral"
  let σ ← parseSRSAt CP (Nat.log2 mps) j
  let proof ← Kimchi.Fixture.parseKimchiProof CP j
  let pub ← parseArrOf (parseZMod (n := CP.scalar)) (← j.getObjVal? "public")
  return (σ, vk, proof, pub)

def main : IO Unit := do
  let dir := (← IO.getEnv "KIMCHI_FIXTURES_DIR").getD "../kimchi/fixtures"
  let path := s!"{dir}/kimchi_proof_pallas_pickles.json"
  match parseFixture (← IO.FS.readFile path) with
  | .error e => throw (IO.userError s!"{path}: fixture parse error: {e}")
  | .ok (σ, vk, proof, pub) =>
    let nc := Wire.runNc CP σ vk
    if h : nc = 1 then
      -- `SgOk` is stated at one chunk, which is production's wrap regime.
      let check (p : Wire.KimchiProof CP) : Option (Bool × Bool) :=
        match (h ▸ vk.check nc : Option (KimchiVK CP 1)),
              (h ▸ p.check nc σ.k : Option (KimchiProof CP 1 σ.k)) with
        | some cvk, some cp => some (kimchiVerify CP σ cvk cp pub, sgOk σ cvk cp pub)
        | _, _ => none
      let some (verified, accepted) := check proof
        | throw (IO.userError s!"{path}: the fixture's own records failed to parse")
      IO.println s!"{path} (nc = {nc}, k = {σ.k}, \
        {proof.prevChallenges.size} accumulators):"
      IO.println s!"  {if verified then "✓" else "✗"} kimchiVerify accepts"
      IO.println s!"  {if accepted then "✓" else "✗"} sgOk accepts"
      -- The corruptions must flip `sgOk`, or the acceptance above says nothing.
      let bumped (name : String) (p : Wire.KimchiProof CP) : IO Bool := do
        let some (_, ok) := check p
          | throw (IO.userError s!"{path}: the {name} mutant failed to parse")
        IO.println s!"  {if !ok then "✓ REJECT" else "✗ ACCEPT (VACUOUS)"}: {name}"
        return !ok
      let sgFlips ← bumped "bumped opening sg"
        { proof with opening := { proof.opening with sg := proof.opening.sg + σ.h } }
      let ftFlips ← bumped "bumped ft_eval1 (moves the transcript's round challenges)"
        { proof with ftEval1 := proof.ftEval1 + 1 }
      unless verified && accepted && sgFlips && ftFlips do
        throw (IO.userError s!"{path}: deferred sg obligation check FAILED")
      IO.println "✓ the deferred sg obligation holds on a deployed pickles wrap proof, and \
        fails when the opening or the transcript is disturbed"
    else
      throw (IO.userError s!"{path}: expected a one-chunk proof, got nc = {nc}")
