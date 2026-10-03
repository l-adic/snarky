import PicklesFixture.Layout
import PicklesFixture.Satisfies
import PicklesFixture.Verdicts
import PicklesFixture.Fop
import PicklesFixture.Group
import PicklesFixture.Constants
import PicklesFixture.Compare
import PicklesFixture.Premises
import PicklesFixture.Proofs
import PicklesFixture.Advice
import PicklesFixture.Rule
import PicklesFixture.Application
import PicklesFixture.ApplicationWiring
import PicklesFixture.ApplicationRun

/-!
# The pickles circuit harnesses the drivers share

The dump comparison (`formal/scripts/check_cs.lean`), the tag-dump check
(`formal/scripts/check_tags.lean`) and the satisfiability check lay out the same production
dumps and call the same library gadgets on them. What they share lives here: the input
layouts, the production constants, the dumps' constants, the replayed rules, the main
circuits' advice off the proof cache, the comparison, the constant premises, the verdicts on
cached proofs and the gadget harnesses.

Kept out of the `Pickles` library, as the kimchi fixture library is kept out of `Kimchi`:
checking against recorded data is not part of the development.
-/
