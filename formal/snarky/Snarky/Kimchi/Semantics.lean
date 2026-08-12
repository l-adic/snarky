import Snarky.Kimchi.Constraint
import Snarky.Backend.WP
import Kimchi.Gate.AddComplete

/-!
# The kimchi constraint semantics

The valuation-level reading of `KimchiConstraint` — the layer gadget laws are stated
against, with no rows, reduction, or wiring in sight. `.basic` reads as the reference
`Basic` semantics, so the one `LawfulBasicSystem` instance below transfers every
backend-generic base gadget law to this backend. `.addComplete` reads as the verified
gate's own predicate at the payload's operand values (`AddComplete.read`, one field
per gate column). `.pad` reads vacuously (a padding row asserts nothing), as do the
gate payloads with no landed gadget: the reading is deliberately per-constructor, and
a vacuous case marks a constructor outside the landed gadget surface.
-/

namespace Snarky.Kimchi

open Snarky

variable {F : Type} [CommRing F] [DecidableEq F]

/-- The payload's operand values under a valuation, as the verified gate's witness
record — one field per gate column, in the gate's column order. -/
def AddComplete.read (V : Valuation F) (c : AddComplete F) :
    Kimchi.Gate.AddComplete.Witness F where
  x1 := c.p1.x.val V
  y1 := c.p1.y.val V
  x2 := c.p2.x.val V
  y2 := c.p2.y.val V
  x3 := c.p3.x.val V
  y3 := c.p3.y.val V
  inf := c.inf.val V
  sameX := c.sameX.val V
  s := c.s.val V
  infZ := c.infZ.val V
  x21Inv := c.x21Inv.val V

/-- The constraint-level semantics: `.basic` is the reference reading, `.addComplete`
the verified gate's predicate at the operand values, and the rest vacuous (module
docstring). -/
def KimchiConstraint.Holds (V : Valuation F) : KimchiConstraint F → Prop
  | .basic con => ConstraintHolds.Holds V con
  | .addComplete c => Kimchi.Gate.AddComplete.Holds (AddComplete.read V c)
  | .poseidon _ => True
  | .varBaseMul _ => True
  | .endoScalar _ => True
  | .endoMul _ => True
  | .pad _ => True

/-- The semantic reading, packaged for the triple machinery. -/
instance KimchiConstraint.instConstraintHolds :
    ConstraintHolds F (KimchiConstraint F) :=
  ⟨KimchiConstraint.Holds⟩

/-- The backend is lawful: `.basic` embeds the reference constraints verbatim, so
each law is `Basic`'s own. -/
instance KimchiConstraint.instLawfulBasicSystem :
    LawfulBasicSystem F (KimchiConstraint F) where
  holds_equal V a b h := LawfulBasicSystem.holds_equal (c := Basic F) V a b h
  holds_r1cs V l r o h := LawfulBasicSystem.holds_r1cs (c := Basic F) V l r o h
  holds_square V a sq h := LawfulBasicSystem.holds_square (c := Basic F) V a sq h
  holds_boolean V x h := LawfulBasicSystem.holds_boolean (c := Basic F) V x h

end Snarky.Kimchi
