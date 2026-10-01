import PicklesFixture.Layout
import PicklesFixture.Satisfies
import PicklesFixture.Fop
import PicklesFixture.Group
import PicklesFixture.Constants
import PicklesFixture.Rules

/-!
# The pickles circuit harnesses the drivers share

The dump comparison (`formal/scripts/check_cs.lean`), the premise check
(`formal/scripts/check_premises.lean`) and the satisfiability check lay out the same
production dumps and call the same library gadgets on them. What they share lives here: the
input layouts, the production constants, the dumps' constants, the transcribed rules and the
gadget harnesses.

Kept out of the `Pickles` library, as the kimchi fixture library is kept out of `Kimchi`:
checking against recorded data is not part of the development.
-/
