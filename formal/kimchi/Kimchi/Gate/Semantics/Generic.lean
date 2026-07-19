import Kimchi.Gate.Generic

/-! # Generic gate semantics: soundness and completeness of the executable checker. -/

namespace Kimchi.Gate

variable {F : Type*} [Field F]

/-- **Soundness:** a row accepted by the executable checker satisfies both constraints.
    (The gate is a decidable predicate, so soundness is one direction of `ok_iff`; the
    other is `complete`.) -/
theorem Generic.sound [DecidableEq F] (g : Generic F) : g.ok = true → g.Holds := g.ok_iff.mp

/-- **Completeness:** a row satisfying both constraints is accepted by the executable
    checker. (The converse direction of `ok_iff`.) -/
theorem Generic.complete [DecidableEq F] (g : Generic F) : g.Holds → g.ok = true := g.ok_iff.mpr

end Kimchi.Gate
