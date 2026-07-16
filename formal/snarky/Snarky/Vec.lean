/-!
# Vector utilities

Kernel-reduction-friendly replacements for core `Vector` operations. Everything in this
library is validated by `decide`, which reduces terms in the kernel — and several core
`Vector` functions go through `Array.mapM`, whose loop is compiled by *well-founded
recursion* and is therefore opaque to kernel reduction: a single such call anywhere in an
executable path silently wedges every downstream `decide`. The replacements here take the
`List` route instead (structural recursion, reduces by iota), converting through
`Vector.toList` with a `simp` length witness.
-/

namespace Snarky

/-- A List-backed `Vector.map` (core's runs through `Array.mapM` — well-founded recursion,
opaque to the kernel; `List.map` is structural, so this version reduces under `decide`). -/
def mapVec (f : α → β) (v : Vector α n) : Vector β n :=
  ⟨⟨v.toList.map f⟩, by simp⟩

end Snarky
