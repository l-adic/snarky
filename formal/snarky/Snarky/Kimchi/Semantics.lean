import Snarky.Kimchi.Constraint
import Snarky.Backend.WP
import Kimchi.Gate.AddComplete

/-!
# The kimchi constraint semantics

The two readings of `KimchiConstraint` — the layer gadget laws are stated against,
with no rows, reduction, or wiring in sight. The soundness side reads a constraint at
a total valuation (`Holds`); the prover side checks it on the prover's partial table
(`check`). In both, `.basic` is the reference `Basic` reading — so the
`LawfulBasicSystem` and `LawfulChecker` instances below transfer every backend-generic
base gadget law, sound and complete, to this backend — and `.addComplete` is the
verified gate's own predicate/`ok` at the payload's operand values (`read`/`eval`, one
field per gate column; a value missing from the table rejects). `.pad` reads
vacuously (a padding row asserts nothing), as do the gate payloads with no landed
gadget: the reading is deliberately per-constructor, and a vacuous case marks a
constructor outside the landed gadget surface.
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

/-- The payload's operand values on the prover's partial table, as the gate's witness
record — `read` at an `Assignments`, failing where a value is missing. -/
def AddComplete.eval (env : Assignments F) (c : AddComplete F) :
    Except EvalError (Kimchi.Gate.AddComplete.Witness F) := do
  let x1 ← c.p1.x.eval env
  let y1 ← c.p1.y.eval env
  let x2 ← c.p2.x.eval env
  let y2 ← c.p2.y.eval env
  let x3 ← c.p3.x.eval env
  let y3 ← c.p3.y.eval env
  let inf ← c.inf.eval env
  let sameX ← c.sameX.eval env
  let s ← c.s.eval env
  let infZ ← c.infZ.eval env
  let x21Inv ← c.x21Inv.eval env
  return { x1, y1, x2, y2, x3, y3, inf, sameX, s, infZ, x21Inv }

/-- The prover-side check: `.basic` is the reference check, `.addComplete` the gate's
`ok` at the evaluated payload, and the rest vacuous (module docstring). -/
def KimchiConstraint.check (con : KimchiConstraint F) (env : Assignments F) : Bool :=
  match con with
  | .basic b => Basic.holds b env
  | .addComplete c =>
    match AddComplete.eval env c with
    | .ok w => Kimchi.Gate.AddComplete.ok w
    | .error _ => false
  | .poseidon _ => true
  | .varBaseMul _ => true
  | .endoScalar _ => true
  | .endoMul _ => true
  | .pad _ => true

/-- The prover-side check, packaged for the completeness machinery. -/
instance KimchiConstraint.instChecker : Checker F (KimchiConstraint F) :=
  ⟨KimchiConstraint.check⟩

/-- The backend checker is lawful: `.basic` embeds the reference constraints
verbatim, so each law is `Basic`'s own. -/
instance KimchiConstraint.instLawfulChecker :
    LawfulChecker F (KimchiConstraint F) where
  check_equal env a b v h1 h2 :=
    LawfulChecker.check_equal (c := Basic F) env a b v h1 h2
  check_r1cs env l r o x y z hl hr ho hm :=
    LawfulChecker.check_r1cs (c := Basic F) env l r o x y z hl hr ho hm
  check_square env a sq x z ha hs hm :=
    LawfulChecker.check_square (c := Basic F) env a sq x z ha hs hm
  check_boolean env a v ha hb :=
    LawfulChecker.check_boolean (c := Basic F) env a v ha hb

/-- The kimchi prover carrier: the checking reading at the kimchi backend. -/
abbrev KimchiProverC (F : Type) := Prover (KimchiConstraint F)

/-- The kimchi constraint vocabulary, as a class over the carrier. NOT a backend
seam: kimchi is the terminal constraint layer, and the two instances below — the sum
itself and its prover tag — are the only two that will ever exist. The class exists
because a completeness triple must elaborate the gadget body at the prover tag, so
the gadget definitions are polymorphic between exactly these two carriers. One
method per landed gadget law. -/
class KimchiSystem (F c : Type) where
  /-- Embed a complete-addition payload. -/
  addComplete : AddComplete F → c
  /-- Embed a Poseidon block payload. -/
  poseidon : PoseidonConstraint F → c

instance : KimchiSystem F (KimchiConstraint F) := ⟨.addComplete, .poseidon⟩

instance [inst : KimchiSystem F c] : KimchiSystem F (Prover c) := inst

end Snarky.Kimchi
