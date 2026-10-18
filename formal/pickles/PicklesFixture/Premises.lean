import Pickles.Verify
import Pickles.PublicInputCommit
import PicklesFixture.Constants

/-!
# The capstones' constant premises

What `wrapStep_kimchiVerify` assumes of a wrap main's constants beyond its keys and the tables'
shape, decided on a dump's constants with no multi-scalar multiplication: the blinding base is the
step SRS's, and every step key's index points and every Lagrange base are finite.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi CompElliptic.Fields.Pasta

/-- What `wrapStep_kimchiVerify` assumes of a wrap main's constants beyond its keys and the
tables' shape, decided with no MSM: `h` is the step SRS's blinding base (`hh`), every step
key's index points are finite (`hnz`), and every base is (`havoidS`, by
`KimchiVK.avoids_lagrangeRelations_iff`). The bases are upstream's commitments, which the dump's
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

end PicklesFixture
