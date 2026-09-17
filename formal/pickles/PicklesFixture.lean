import PicklesFixture.Layout
import PicklesFixture.Fop
import PicklesFixture.FopInput

/-!
# The pickles circuit harnesses the drivers share

The dump comparison (`formal/scripts/check_cs.lean`) and the satisfiability check lay out
the same production dumps and call the same library gadgets on them. What they share lives
here: the input layouts, the production constants, and the gadget harnesses.

Kept out of the `Pickles` library, as `KimchiFixture` is kept out of `Kimchi` — checking
against recorded data is not part of the development.
-/
