import Snarky.Kimchi.Constraint
import Snarky.Backend.WP
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

/-- The payload round's operand values on the prover's partial table, failing where
a value is missing. -/
def EndoScalarRound.eval (env : Assignments F) (r : EndoScalarRound F) :
    Except EvalError (Kimchi.Gate.EndoScalar.Witness F) := do
  let a0 ← r.a0.eval env
  let b0 ← r.b0.eval env
  let n0 ← r.n0.eval env
  let a8 ← r.a8.eval env
  let b8 ← r.b8.eval env
  let n8 ← r.n8.eval env
  let crumbs ← r.xs.toList.mapM (·.eval env)
  return { a0, b0, n0, a8, b8, n8, crumbs }

/-- The scale round's operand values on the prover's partial table, failing where
a value is missing. -/
def ScaleRound.eval (env : Assignments F) (r : ScaleRound F) :
    Except EvalError (Kimchi.Gate.VarBaseMul.Witness F) := do
  let xT ← r.base.x.eval env
  let yT ← r.base.y.eval env
  let x0 ← r.acc0.x.eval env
  let y0 ← r.acc0.y.eval env
  let x1 ← r.acc1.x.eval env
  let y1 ← r.acc1.y.eval env
  let x2 ← r.acc2.x.eval env
  let y2 ← r.acc2.y.eval env
  let x3 ← r.acc3.x.eval env
  let y3 ← r.acc3.y.eval env
  let x4 ← r.acc4.x.eval env
  let y4 ← r.acc4.y.eval env
  let x5 ← r.acc5.x.eval env
  let y5 ← r.acc5.y.eval env
  let n ← r.nPrev.eval env
  let nPrime ← r.nNext.eval env
  let b0 ← r.bit0.eval env
  let b1 ← r.bit1.eval env
  let b2 ← r.bit2.eval env
  let b3 ← r.bit3.eval env
  let b4 ← r.bit4.eval env
  let s0 ← r.slope0.eval env
  let s1 ← r.slope1.eval env
  let s2 ← r.slope2.eval env
  let s3 ← r.slope3.eval env
  let s4 ← r.slope4.eval env
  return { xT, yT, x0, y0, x1, y1, x2, y2, x3, y3, x4, y4, x5, y5,
           n, nPrime, b0, b1, b2, b3, b4, s0, s1, s2, s3, s4 }

/-- The payload round's operand values on the prover's partial table, with the
output cells `xS`/`yS`/`nPrime` supplied by the caller (`readWith` at an
`Assignments`); failing where a value is missing. -/
def EndoMulRound.evalWith (env : Assignments F) (r : EndoMulRound F)
    (xS yS nPrime : F) : Except EvalError (Kimchi.Gate.EndoMul.Witness F) := do
  let xT ← r.t.x.eval env
  let yT ← r.t.y.eval env
  let xP ← r.p.x.eval env
  let yP ← r.p.y.eval env
  let n ← r.nAcc.eval env
  let b1 ← r.bit0.eval env
  let b2 ← r.bit1.eval env
  let b3 ← r.bit2.eval env
  let b4 ← r.bit3.eval env
  let s1 ← r.s1.eval env
  let xR ← r.r.x.eval env
  let yR ← r.r.y.eval env
  let s3 ← r.s3.eval env
  let inv ← r.inv.eval env
  return { xT, yT, xP, yP, n, nPrime, b1, b2, b3, b4, s1, xR, yR, s3, xS, yS, inv }

/-- The decidable mirror of `chainHolds`: the gate's `ok` per round on the evaluated
values, the successor reads evaluated on the same table; a value missing from the
table rejects. -/
def EndoMul.chainOk (env : Assignments F) (endo : F) (fin : F × F × F) :
    List (EndoMulRound F) → Bool
  | [] => true
  | [r] =>
    match EndoMulRound.evalWith env r fin.1 fin.2.1 fin.2.2 with
    | .ok w => Kimchi.Gate.EndoMul.ok endo w
    | .error _ => false
  | r :: r' :: rest =>
    (match r'.p.x.eval env, r'.p.y.eval env, r'.nAcc.eval env with
      | .ok xS, .ok yS, .ok nPrime =>
        match EndoMulRound.evalWith env r xS yS nPrime with
        | .ok w => Kimchi.Gate.EndoMul.ok endo w
        | .error _ => false
      | _, _, _ => false) &&
    chainOk env endo fin (r' :: rest)

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
  | .endoScalar rounds =>
    rounds.all fun r =>
      match EndoScalarRound.eval env r with
      | .ok w => Kimchi.Gate.EndoScalar.ok w
      | .error _ => false
  | .varBaseMul rounds =>
    rounds.all fun r =>
      match ScaleRound.eval env r with
      | .ok w => Kimchi.Gate.VarBaseMul.ok w
      | .error _ => false
  | .endoMul c =>
    match c.s.x.eval env, c.s.y.eval env, c.nAcc.eval env with
    | .ok xs, .ok ys, .ok n => EndoMul.chainOk env c.endo (xs, ys, n) c.state
    | _, _, _ => false
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
  /-- Embed a challenge-decomposition payload. -/
  endoScalar : EndoScalar F → c
  /-- Embed an endomorphism-multiplication payload. -/
  endoMul : EndoMul F → c
  /-- Embed a variable-base scalar-multiplication payload. -/
  varBaseMul : VarBaseMul F → c

instance : KimchiSystem F (KimchiConstraint F) :=
  ⟨.addComplete, .poseidon, .endoScalar, .endoMul, .varBaseMul⟩

instance [inst : KimchiSystem F c] : KimchiSystem F (Prover c) := inst

end Snarky.Kimchi
