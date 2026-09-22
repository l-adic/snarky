import Snarky.Kimchi.Constraint
import Snarky.WP
import Kimchi.Gate.AddComplete
import Kimchi.Gate.Poseidon
import Kimchi.Gate.EndoScalar
import Kimchi.Gate.EndoMul

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
the payload's parameter data), one witness record per round for `.endoScalar` and for
`.varBaseMul` (the scale round carries all 26 gate cells itself, output accumulator
and register included, so no successor read is needed), a successor chain over the
round list for `.endoMul` (each round's output cells read from the NEXT round's
`p`/`nAcc`, the last from the payload finals — the two-row gate's next-row read,
value-level); a value missing from the table rejects. `.pad` reads vacuously (a
padding row asserts nothing): the reading is deliberately per-constructor, and a
vacuous case marks a constructor outside the landed gadget surface.
-/

namespace Snarky.Kimchi

open Snarky

-- `Field` rather than `CommRing`: the EndoScalar gate's crumb-interpolation
-- polynomials carry inverse-of-small-integer coefficients.
variable {F : Type} [Field F] [DecidableEq F]

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

/-- The payload round's operand values under a valuation, as the verified gate's
witness record — one field per gate cell, the crumbs in index order. -/
def EndoScalarRound.read (V : Valuation F) (r : EndoScalarRound F) :
    Kimchi.Gate.EndoScalar.Witness F where
  a0 := r.a0.val V
  b0 := r.b0.val V
  n0 := r.n0.val V
  a8 := r.a8.val V
  b8 := r.b8.val V
  n8 := r.n8.val V
  crumbs := r.xs.toList.map (·.val V)

/-- The scale round's operand values under a valuation, as the verified gate's
witness record — one field per gate cell; the round carries its own output
accumulator and register, so the reading is self-contained. -/
def ScaleRound.read (V : Valuation F) (r : ScaleRound F) :
    Kimchi.Gate.VarBaseMul.Witness F where
  xT := r.base.x.val V
  yT := r.base.y.val V
  x0 := r.acc0.x.val V
  y0 := r.acc0.y.val V
  x1 := r.acc1.x.val V
  y1 := r.acc1.y.val V
  x2 := r.acc2.x.val V
  y2 := r.acc2.y.val V
  x3 := r.acc3.x.val V
  y3 := r.acc3.y.val V
  x4 := r.acc4.x.val V
  y4 := r.acc4.y.val V
  x5 := r.acc5.x.val V
  y5 := r.acc5.y.val V
  n := r.nPrev.val V
  nPrime := r.nNext.val V
  b0 := r.bit0.val V
  b1 := r.bit1.val V
  b2 := r.bit2.val V
  b3 := r.bit3.val V
  b4 := r.bit4.val V
  s0 := r.slope0.val V
  s1 := r.slope1.val V
  s2 := r.slope2.val V
  s3 := r.slope3.val V
  s4 := r.slope4.val V

/-- The payload round's operand values under a valuation, as the verified gate's
witness record — one field per gate cell, with the output cells `xS`/`yS`/`nPrime`
supplied by the caller: the gate is two-row, and a round's outputs live in its
successor's cells (the next round's `p`/`nAcc`, or the payload finals). -/
def EndoMulRound.readWith (V : Valuation F) (r : EndoMulRound F) (xS yS nPrime : F) :
    Kimchi.Gate.EndoMul.Witness F where
  xT := r.t.x.val V
  yT := r.t.y.val V
  xP := r.p.x.val V
  yP := r.p.y.val V
  n := r.nAcc.val V
  nPrime := nPrime
  b1 := r.bit0.val V
  b2 := r.bit1.val V
  b3 := r.bit2.val V
  b4 := r.bit3.val V
  s1 := r.s1.val V
  xR := r.r.x.val V
  yR := r.r.y.val V
  s3 := r.s3.val V
  xS := xS
  yS := yS
  inv := r.inv.val V

/-- The successor-chain reading of the round list: the gate per round at the
payload's endo coefficient, each round's output cells read from the NEXT round's
`p`/`nAcc` values and the last round's from the finals `fin` — the wire layout's
next-row read, value-level, so the chain's links are shared round fields. -/
def EndoMul.chainHolds (V : Valuation F) (endo : F) (fin : F × F × F) :
    List (EndoMulRound F) → Prop
  | [] => True
  | [r] =>
    Kimchi.Gate.EndoMul.Holds endo (EndoMulRound.readWith V r fin.1 fin.2.1 fin.2.2)
  | r :: r' :: rest =>
    Kimchi.Gate.EndoMul.Holds endo
      (EndoMulRound.readWith V r (r'.p.x.val V) (r'.p.y.val V) (r'.nAcc.val V)) ∧
      chainHolds V endo fin (r' :: rest)

/-- The constraint-level semantics: `.basic` is the reference reading, the landed gate
payloads the verified gates' predicates at the operand values, and the rest vacuous
(module docstring). -/
def KimchiConstraint.Holds (V : Valuation F) : KimchiConstraint F → Prop
  | .basic con => ConstraintHolds.Holds V con
  | .addComplete c => Kimchi.Gate.AddComplete.Holds (AddComplete.read V c)
  | .poseidon c => Poseidon.chainHolds (Poseidon.mdsOf c.mds) c.rc 0 (Poseidon.read V c)
  | .endoScalar rounds => ∀ r ∈ rounds, Kimchi.Gate.EndoScalar.Holds (EndoScalarRound.read V r)
  | .varBaseMul rounds =>
    ∀ r ∈ rounds, Kimchi.Gate.VarBaseMul.Holds (ScaleRound.read V r)
  | .endoMul c =>
    EndoMul.chainHolds V c.endo (c.s.x.val V, c.s.y.val V, c.nAcc.val V) c.state
  | .pad _ => True

/-- The semantic reading, packaged for the triple machinery. -/
instance KimchiConstraint.instConstraintHolds :
    ConstraintHolds F (KimchiConstraint F) :=
  ⟨KimchiConstraint.Holds⟩

/-- The backend is lawful: `.basic` embeds the reference constraints verbatim, so
each law is `Basic`'s own. -/
instance KimchiConstraint.instLawfulBasicSystem :
    LawfulBasicSystem F (KimchiConstraint F) where
  holds_equal V a b := LawfulBasicSystem.holds_equal (c := Basic F) V a b
  holds_r1cs V l r o := LawfulBasicSystem.holds_r1cs (c := Basic F) V l r o
  holds_square V a sq := LawfulBasicSystem.holds_square (c := Basic F) V a sq
  holds_boolean V x := LawfulBasicSystem.holds_boolean (c := Basic F) V x

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
  /-- Embed a challenge-decomposition payload. -/
  endoScalar : EndoScalar F → c
  /-- Embed an endomorphism-multiplication payload. -/
  endoMul : EndoMul F → c
  /-- Embed a variable-base scalar-multiplication payload. -/
  varBaseMul : VarBaseMul F → c

instance : KimchiSystem F (KimchiConstraint F) :=
  ⟨.addComplete, .poseidon, .endoScalar, .endoMul, .varBaseMul⟩

instance [inst : KimchiSystem F c] {V : Valuation F} :
    KimchiSystem F (Builder V c) := inst

end Snarky.Kimchi
