import Snarky.Kimchi.Constraint
import Snarky.Backend.WP
import Kimchi.Gate.AddComplete
import Kimchi.Gate.Poseidon

/-!
# The kimchi constraint semantics

The two readings of `KimchiConstraint` — the layer gadget laws are stated against,
with no rows, reduction, or wiring in sight. The soundness side reads a constraint at
a total valuation (`Holds`); the prover side checks it on the prover's partial table
(`check`). In both, `.basic` is the reference `Basic` reading — so the
`LawfulBasicSystem` and `LawfulChecker` instances below transfer every backend-generic
base gadget law, sound and complete, to this backend — and the landed gate payloads
read as the verified gates' own predicates/`ok` at the payload's operand values: one
witness record for `.addComplete` (`read`/`eval`, one field per gate column), a chain
of five-round windows over the state list for `.poseidon` (`chainHolds`/`chainOk` at
the payload's parameter data; a value missing from the table rejects). `.pad` reads
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

/-- The payload's MDS rows as the gate's matrix record. -/
def Poseidon.mdsOf (m : (F × F × F) × (F × F × F) × (F × F × F)) :
    Kimchi.Gate.Poseidon.Mds F :=
  { m00 := m.1.1, m01 := m.1.2.1, m02 := m.1.2.2,
    m10 := m.2.1.1, m11 := m.2.1.2.1, m12 := m.2.1.2.2,
    m20 := m.2.2.1, m21 := m.2.2.2.1, m22 := m.2.2.2.2 }

/-- Window `k`'s five constant triples off the payload's table (rounds `5k … 5k+4`,
the offsets the reducer writes into row `k`'s coefficient cells). -/
def Poseidon.rcRow (rc : List (F × F × F)) (k : ℕ) : Fin 5 → F × F × F :=
  fun j => rc.getD (5 * k + j.1) (0, 0, 0)

/-- The payload's state values under a valuation, in round order. -/
def Poseidon.read (V : Valuation F) (c : PoseidonConstraint F) : List (F × F × F) :=
  c.state.map fun t => (t.1.val V, t.2.1.val V, t.2.2.val V)

/-- The chain reading of a state list: one gate window per five states from position
`5k`, each window's sixth state opening the next — the wire layout's next-row read,
value-level, so the chain's links are shared list elements. Off the deployed
`11·5 + 1` shape, partial tails assert nothing, matching the reducer's row
fallbacks. -/
def Poseidon.chainHolds (M : Kimchi.Gate.Poseidon.Mds F) (rc : List (F × F × F)) :
    ℕ → List (F × F × F) → Prop
  | k, s0 :: s1 :: s2 :: s3 :: s4 :: rest =>
    match rest with
    | s5 :: _ =>
      Kimchi.Gate.Poseidon.Holds M (rcRow rc k) ⟨s0, s1, s2, s3, s4, s5⟩ ∧
        chainHolds M rc (k + 1) rest
    | [] => True
  | _, _ => True

/-- The constraint-level semantics: `.basic` is the reference reading, the landed gate
payloads the verified gates' predicates at the operand values, and the rest vacuous
(module docstring). -/
def KimchiConstraint.Holds (V : Valuation F) : KimchiConstraint F → Prop
  | .basic con => ConstraintHolds.Holds V con
  | .addComplete c => Kimchi.Gate.AddComplete.Holds (AddComplete.read V c)
  | .poseidon c => Poseidon.chainHolds (Poseidon.mdsOf c.mds) c.rc 0 (Poseidon.read V c)
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

/-- The payload's state values on the prover's partial table, failing where a value
is missing. -/
def Poseidon.evalStates (env : Assignments F) :
    List (FVar F × FVar F × FVar F) → Except EvalError (List (F × F × F))
  | [] => .ok []
  | t :: ts => do
    let a ← t.1.eval env
    let b ← t.2.1.eval env
    let c ← t.2.2.eval env
    let rest ← evalStates env ts
    return (a, b, c) :: rest

/-- The decidable mirror of `chainHolds`: the gate's `ok` per window. -/
def Poseidon.chainOk (M : Kimchi.Gate.Poseidon.Mds F) (rc : List (F × F × F)) :
    ℕ → List (F × F × F) → Bool
  | k, s0 :: s1 :: s2 :: s3 :: s4 :: rest =>
    match rest with
    | s5 :: _ =>
      Kimchi.Gate.Poseidon.ok M (rcRow rc k) ⟨s0, s1, s2, s3, s4, s5⟩ &&
        chainOk M rc (k + 1) rest
    | [] => true
  | _, _ => true

/-- The prover-side check: `.basic` is the reference check, the landed gate payloads
the gates' `ok` at the evaluated values, and the rest vacuous (module docstring). -/
def KimchiConstraint.check (con : KimchiConstraint F) (env : Assignments F) : Bool :=
  match con with
  | .basic b => Basic.holds b env
  | .addComplete c =>
    match AddComplete.eval env c with
    | .ok w => Kimchi.Gate.AddComplete.ok w
    | .error _ => false
  | .poseidon c =>
    match Poseidon.evalStates env c.state with
    | .ok vs => Poseidon.chainOk (Poseidon.mdsOf c.mds) c.rc 0 vs
    | .error _ => false
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
