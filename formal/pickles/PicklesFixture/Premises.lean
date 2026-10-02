import Pickles.Verify
import Pickles.PublicInputCommit
import PicklesFixture.Constants

/-!
# The capstones' constant premises

What the handover theorems (`wrapStep_kimchiVerify`, `stepWrap_kimchiVerify`) assume of a main
circuit's constants beyond their keys and the tables' shape, decided on a dump's constants with no
multi-scalar multiplication: the blinding bases are the SRSs', and every key's index points, every
Lagrange base and every slot's correction sum are finite.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi CompElliptic.Fields.Pasta

/-- What `wrapStep_kimchiVerify` assumes of a wrap main's constants beyond its keys and the
tables' shape, decided with no MSM: `h` is the step SRS's blinding base (`hh`), every step
key's index points are finite (`hnz`), and every base is (`havoidS`, by
`Key.avoids_lagrangeRelations_iff`). The bases are upstream's commitments, which the dump's
harness checks against the keys. -/
def wrapMainHyps {nc bp m : ℕ} (k : WrapMainConsts nc)
    (tables : Vector (Vector (Vector XhatWrapCurve.Point nc) m) (bp + 1))
    (h : XhatWrapCurve.Point) :
    Except String Unit := do
  unless decide (k.h = h) do throw "h is not the step SRS's blinding base"
  unless k.keys.all fun key => key.comms.indexPoints.all fun P => decide (P ≠ 0) do
    throw "a step key has an index point at the identity"
  unless tables.all fun t => t.all fun Ps => Ps.all fun P => decide (P ≠ 0) do
    throw "a Lagrange base is the identity"

/-- The wrap statement decoded from zero cells. -/
def zeroWrapStatement :
    Pickles.WrapStatement Pickles.StepIPARounds (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) :=
  CircuitType.fieldsToVar (F := Fp)
    (val := Pickles.WrapStatement Pickles.StepIPARounds Fp Bool (Type1 Fp))
    (Vector.replicate _ (.const 0))

/-- What `stepWrap_kimchiVerify` assumes of a step main's constants beyond its keys, decided
with no MSM: `h` is the wrap SRS's blinding base, the dummy `sg` is finite (`hdummySg`), and
each slot's table fits its key's domain (`Fits`' size clause) and has every base and their
correction sum finite, which is the SRS avoiding the slot's step relations
(`avoids_stepRelationsAt_iff`). The correction sum reads the packing's kinds only, so any
statement of the slot's type stands for all (`zeroWrapStatement`). The bases are upstream's
commitments, which the dump's harness checks against the keys. -/
def stepMainHyps {n ncs : ℕ} (k : StepMainConsts n ncs) (h : XhatStepCurve.Point) :
    Except String Unit := do
  unless decide (k.h = h) do throw "h is not the wrap SRS's blinding base"
  unless decide (dummyWrapSgPt ≠ 0) do throw "the dummy sg is the identity"
  let packed := zeroWrapStatement.packed
  for s in k.slots.toList do
    let bases := s.lagrange.toList
    unless bases.length ≤ s.key.n do
      throw s!"{bases.length} Lagrange bases overflow the domain 2^{s.key.domainLog2}"
    unless bases.all fun Ps => decide (Ps[0] ≠ 0) do throw "a Lagrange base is the identity"
    unless decide
        (Pickles.corrSumPt (C := Bulletproof.IpaPallas.curve) packed.toList bases 0 ≠ 0) do
      throw "a slot's correction sum is the identity"

end PicklesFixture
