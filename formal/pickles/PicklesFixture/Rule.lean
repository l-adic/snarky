import Lean.Data.Json
import FixtureKit.Parse
import Pickles.StepMain
import PicklesFixture.Layout

/-!
# A rule replayed from its dump

A tag dump carries each branch's rule as data: the operations its body ran, in order, each an
allocation of fresh variables or a constraint as emitted, before the kimchi reduction, over the
rule's local variable ids, with its outputs as expressions over the same ids. Local ids
`0 … inputSize - 1` are the input's cells, and each allocation takes the next ids. Replaying the
operations rebuilds the rule as a circuit, which `Pickles.stepMain` takes like any other: the
capstones hold for every rule, so the replay is as good as a transcription.

## Main definitions

* `PicklesFixture.RuleDump`, `PicklesFixture.RuleDump.ofJson`: a rule's dump and its reader,
  which checks every local id is in scope where it is read.
* `PicklesFixture.replayRule`: the rule as a circuit.
-/

namespace PicklesFixture

open Lean Snarky Snarky.Kimchi CompElliptic.Fields.Pasta

/-- One operation of a rule's body, over its local variable ids. -/
inductive RuleOp where
  /-- Allocate `n` fresh variables. -/
  | alloc (n : ℕ)
  /-- Emit a Kimchi constraint over local variable expressions. -/
  | constrain (c : KimchiConstraint Fp)

/-- A rule's body as dumped: its input's size, its operations in order, and per slot the
previous statement's cells and the must-verify flag, then its public output. -/
structure RuleDump where
  /-- The number of input cells, the local ids below it. -/
  inputSize : ℕ
  /-- The operations, in the order the body ran them. -/
  ops : List RuleOp
  /-- Per slot: the previous statement's cells and whether the slot must verify. -/
  prevs : Array (Array (FVar Fp) × FVar Fp)
  /-- The public output's cells. -/
  publicOutput : Array (FVar Fp)

/-- An expression's local ids, read through `env`. -/
def substLocal (env : Array (FVar Fp)) : FVar Fp → FVar Fp
  | .var v => env.getD v (.const 0)
  | .const c => .const c
  | .add a b => .add (substLocal env a) (substLocal env b)
  | .scale k x => .scale k (substLocal env x)

/-- Whether every local id of an expression is below `n`. -/
def scopedBelow (n : ℕ) : FVar Fp → Bool
  | .var v => v < n
  | .const _ => true
  | .add a b => scopedBelow n a && scopedBelow n b
  | .scale _ x => scopedBelow n x

/-- An expression of a rule dump: `{var}`, `{const}`, `{add: [a, b]}` or `{scale: {k, x}}`. -/
partial def parseLocal (j : Json) : Except String (FVar Fp) := do
  if let .ok v := j.getObjVal? "var" then return .var (← v.getNat?)
  if let .ok c := j.getObjVal? "const" then return .const (← FixtureKit.parseZMod c)
  if let .ok ab := j.getObjVal? "add" then
    let #[a, b] ← ab.getArr? | throw "add: expected two operands"
    return .add (← parseLocal a) (← parseLocal b)
  if let .ok s := j.getObjVal? "scale" then
    return .scale (← FixtureKit.parseZMod (← s.getObjVal? "k")) (← parseLocal (← s.getObjVal? "x"))
  throw s!"not a rule expression: {j.compress.take 80}"

/-- Two operands, as `[a, b]`. -/
private def parseTwo (j : Json) : Except String (FVar Fp × FVar Fp) := do
  let #[a, b] ← j.getArr? | throw "expected two operands"
  return (← parseLocal a, ← parseLocal b)

/-- A basic constraint of a rule dump. -/
def parseBasic (b : Json) : Except String (Basic Fp) := do
  if let .ok r := b.getObjVal? "r1cs" then
    return .r1cs (← parseLocal (← r.getObjVal? "left")) (← parseLocal (← r.getObjVal? "right"))
      (← parseLocal (← r.getObjVal? "output"))
  if let .ok e := b.getObjVal? "equal" then
    let (x, y) ← parseTwo e
    return .equal x y
  if let .ok s := b.getObjVal? "square" then
    let (x, y) ← parseTwo s
    return .square x y
  if let .ok x := b.getObjVal? "boolean" then return .boolean (← parseLocal x)
  throw s!"not a basic constraint: {b.compress.take 80}"

private def localVector (n : Nat) (j : Json) : Except String (Vector (FVar Fp) n) := do
  let xs ← FixtureKit.parseArrOf parseLocal j
  if h : xs.size = n then return ⟨xs, h⟩ else throw s!"expected {n} rule cells, got {xs.size}"

private def localPoint (j : Json) : Except String (AffinePoint (FVar Fp)) := do
  return ⟨← parseLocal (← j.getObjVal? "x"), ← parseLocal (← j.getObjVal? "y")⟩

private def localField (j : Json) (key : String) := j.getObjVal? key >>= parseLocal

private def parseScaleRound (j : Json) : Except String (ScaleRound Fp) := do
  let #[a0, a1, a2, a3, a4, a5] ← (← j.getObjVal? "accs").getArr?
    | throw "a variable-base round needs six accumulator points"
  let bits ← localVector 5 (← j.getObjVal? "bits")
  let slopes ← localVector 5 (← j.getObjVal? "slopes")
  return { acc0 := ← localPoint a0, acc1 := ← localPoint a1, acc2 := ← localPoint a2
           acc3 := ← localPoint a3, acc4 := ← localPoint a4, acc5 := ← localPoint a5
           bit0 := bits[0], bit1 := bits[1], bit2 := bits[2], bit3 := bits[3], bit4 := bits[4]
           slope0 := slopes[0], slope1 := slopes[1], slope2 := slopes[2]
           slope3 := slopes[3], slope4 := slopes[4]
           nPrev := ← localField j "nPrev", nNext := ← localField j "nNext"
           base := ← localPoint (← j.getObjVal? "base") }

private def parseEndoRound (j : Json) : Except String (EndoMulRound Fp) := do
  let bits ← localVector 4 (← j.getObjVal? "bits")
  return { t := ← localPoint (← j.getObjVal? "t"), p := ← localPoint (← j.getObjVal? "p")
           r := ← localPoint (← j.getObjVal? "r"), s := ← localPoint (← j.getObjVal? "s")
           s1 := ← localField j "s1", s3 := ← localField j "s3"
           nAcc := ← localField j "nAcc", nAccNext := ← localField j "nAccNext"
           bit0 := bits[0], bit1 := bits[1], bit2 := bits[2], bit3 := bits[3]
           inv := ← localField j "inv" }

private def parseConstraint (c : Json) : Except String (KimchiConstraint Fp) := do
  if let .ok b := c.getObjVal? "basic" then return .basic (← parseBasic b)
  if let .ok p := c.getObjVal? "pad" then return .pad (← localVector 7 p)
  if let .ok a := c.getObjVal? "addComplete" then
    return .addComplete {
      p1 := ← localPoint (← a.getObjVal? "p1"), p2 := ← localPoint (← a.getObjVal? "p2")
      p3 := ← localPoint (← a.getObjVal? "p3"), inf := ← localField a "inf"
      sameX := ← localField a "sameX", s := ← localField a "s"
      infZ := ← localField a "infZ", x21Inv := ← localField a "x21Inv" }
  if let .ok p := c.getObjVal? "poseidon" then
    let states ← (← p.getObjVal? "state").getArr? >>= (·.mapM (localVector 3))
    unless states.size = 56 do throw "a Poseidon block needs 56 states"
    return .poseidon {
      mds := Poseidon.fpParams.mds, rc := Poseidon.fpParams.roundConstants.toList
      state := states.toList.map fun (s : Vector (FVar Fp) 3) => (s[0], s[1], s[2]) }
  if let .ok rs := c.getObjVal? "varBaseMul" then
    return .varBaseMul (← rs.getArr? >>= (·.toList.mapM parseScaleRound))
  if let .ok rs := c.getObjVal? "endoScalar" then
    return .endoScalar (← rs.getArr? >>= (·.toList.mapM fun r => do
      return { n0 := ← localField r "n0", n8 := ← localField r "n8"
               a0 := ← localField r "a0", a8 := ← localField r "a8"
               b0 := ← localField r "b0", b8 := ← localField r "b8"
               xs := ← localVector 8 (← r.getObjVal? "xs") }))
  if let .ok e := c.getObjVal? "endoMul" then
    let state ← (← e.getObjVal? "state").getArr? >>= (·.toList.mapM parseEndoRound)
    unless !state.isEmpty do throw "an endomorphism multiplication needs a round"
    return .endoMul {
      state, s := ← localPoint (← e.getObjVal? "s")
      nAcc := ← localField e "nAcc", endo := Bulletproof.IpaPallas.curve.endo.coeff }
  throw s!"unsupported rule constraint: {c.compress.take 80}"

/-- An allocation or a constraint in the exported Kimchi vocabulary. -/
def parseOp (j : Json) : Except String RuleOp := do
  if let .ok n := j.getObjVal? "alloc" then return .alloc (← n.getNat?)
  return .constrain (← parseConstraint (← j.getObjVal? "constraint"))

private def traverseConstraint {m : Type → Type} [Monad m]
    (f : FVar Fp → m (FVar Fp)) : KimchiConstraint Fp → m (KimchiConstraint Fp)
  | .basic b => .basic <$> (match b with
    | .r1cs l r o => return .r1cs (← f l) (← f r) (← f o)
    | .equal a b => return .equal (← f a) (← f b)
    | .square a b => return .square (← f a) (← f b)
    | .boolean a => return .boolean (← f a))
  | .pad xs => .pad <$> xs.mapM f
  | .poseidon p => do
    return .poseidon { p with state := ← p.state.mapM fun (a, b, c) =>
      return (← f a, ← f b, ← f c) }
  | .addComplete p => do
    return .addComplete {
      p1 := ← pt p.p1,
      p2 := ← pt p.p2,
      p3 := ← pt p.p3,
      inf := ← f p.inf,
      sameX := ← f p.sameX,
      s := ← f p.s,
      infZ := ← f p.infZ,
      x21Inv := ← f p.x21Inv }
  | .varBaseMul rs => do
    return .varBaseMul (← rs.mapM fun p => do
      return {
        acc0 := ← pt p.acc0,
        acc1 := ← pt p.acc1,
        acc2 := ← pt p.acc2,
        acc3 := ← pt p.acc3,
        acc4 := ← pt p.acc4,
        acc5 := ← pt p.acc5,
        bit0 := ← f p.bit0,
        bit1 := ← f p.bit1,
        bit2 := ← f p.bit2,
        bit3 := ← f p.bit3,
        bit4 := ← f p.bit4,
        slope0 := ← f p.slope0,
        slope1 := ← f p.slope1,
        slope2 := ← f p.slope2,
        slope3 := ← f p.slope3,
        slope4 := ← f p.slope4,
        nPrev := ← f p.nPrev,
        nNext := ← f p.nNext,
        base := ← pt p.base })
  | .endoScalar rs => do
    return .endoScalar (← rs.mapM fun p => do
      return {
        n0 := ← f p.n0,
        n8 := ← f p.n8,
        a0 := ← f p.a0,
        a8 := ← f p.a8,
        b0 := ← f p.b0,
        b8 := ← f p.b8,
        xs := ← p.xs.mapM f })
  | .endoMul e => do
    let state ← e.state.mapM fun p => do
      return {
        t := ← pt p.t,
        p := ← pt p.p,
        r := ← pt p.r,
        s := ← pt p.s,
        s1 := ← f p.s1,
        s3 := ← f p.s3,
        nAcc := ← f p.nAcc,
        nAccNext := ← f p.nAccNext,
        bit0 := ← f p.bit0,
        bit1 := ← f p.bit1,
        bit2 := ← f p.bit2,
        bit3 := ← f p.bit3,
        inv := ← f p.inv }
    return .endoMul { e with state, s := ← pt e.s, nAcc := ← f e.nAcc }
  where
  pt (p : AffinePoint (FVar Fp)) : m (AffinePoint (FVar Fp)) := do
    return ⟨← f p.x, ← f p.y⟩

private def substConstraint (env : Array (FVar Fp)) (c : KimchiConstraint Fp) :=
  Id.run (traverseConstraint (m := Id) (fun x => pure (substLocal env x)) c)

private def scopedConstraint (n : Nat) (c : KimchiConstraint Fp) : Bool :=
  (traverseConstraint (m := Option) (fun x => if scopedBelow n x then some x else none) c).isSome

/-- The number of local ids in scope after `ops`, starting from `n`, when every constraint reads
only ids already in scope. -/
def scopeAfter : ℕ → List RuleOp → Option ℕ
  | n, [] => some n
  | n, .alloc m :: ops => scopeAfter (n + m) ops
  | n, .constrain c :: ops => if scopedConstraint n c then scopeAfter n ops else none

/-- A rule's dump, read and checked: every constraint reads only ids allocated before it, and
the outputs only ids the body allocated. -/
def RuleDump.ofJson (j : Json) : Except String RuleDump := do
  let inputSize ← (← j.getObjVal? "inputSize").getNat?
  let ops ← (← j.getObjVal? "ops").getArr? >>= (·.mapM parseOp)
  let prevs ← (← j.getObjVal? "prevs").getArr? >>= (·.mapM fun p => do
    return (← FixtureKit.parseArrOf parseLocal (← p.getObjVal? "statement"),
      ← parseLocal (← p.getObjVal? "mustVerify")))
  let publicOutput ← FixtureKit.parseArrOf parseLocal (← j.getObjVal? "publicOutput")
  let some n := scopeAfter inputSize ops.toList
    | throw "a rule constraint reads a variable before it is allocated"
  unless prevs.all (fun (s, m) => s.all (scopedBelow n) && scopedBelow n m) &&
      publicOutput.all (scopedBelow n) do
    throw "a rule output reads a variable the rule did not allocate"
  return { inputSize, ops := ops.toList, prevs, publicOutput }

/-- The number of variables a rule's body allocates. -/
def RuleDump.allocated (d : RuleDump) : ℕ :=
  d.ops.foldl (fun n op => match op with | .alloc m => n + m | _ => n) 0

/-- Replay `ops`, the local ids read through `env`, which each allocation extends with its
fresh variables; the result is the final `env`. An allocation's advice is the witness's values
from `off` on, the allocations so far having taken those before it; with no witness it is
inert. -/
def replayOps (vals : Option (Array Fp)) : List RuleOp → ℕ → Array (FVar Fp) →
    CircuitM Fp C (Array (FVar Fp))
  | [], _, env => .pure env
  | .alloc n :: ops, off, env =>
    .existsOp n
      (match vals with
        | none => AsProver.throw "advice"
        | some vs =>
          if h : off + n ≤ vs.size then
            pure (Vector.ofFn fun i : Fin n => vs[off + i.val]'(by omega))
          else AsProver.throw s!"rule witness: allocation at {off} needs {n} values, \
            but the witness has {vs.size}")
      fun xs => replayOps vals ops (off + n) (env ++ xs.toArray.map .var)
  | .constrain c :: ops, off, env =>
    .addConstraintOp (substConstraint env c) (replayOps vals ops off env)

private theorem build_replayOps_irrel (vals vals' : Option (Array Fp)) (ops : List RuleOp)
    (off : ℕ) (env : Array (FVar Fp)) (nv : ℕ) :
    build (replayOps vals ops off env) nv = build (replayOps vals' ops off env) nv := by
  induction ops generalizing off env nv with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp only [replayOps, build, ih]

/-- A rule's dump as the rule it records: the input's cells are the first local ids, the body's
operations replay in order, and each slot's previous statement, its must-verify flag and the
public output are read through the ids the replay allocated. With a witness `vals` (its
`RuleDump.allocated` values, in order) its allocations take them; without, it compiles only. -/
def replayRule (d : RuleDump) (vals : Option (Array Fp)) (x : Vector (FVar Fp) d.inputSize) :
    CircuitM Fp C (((i : Fin d.prevs.size) → Pickles.PrevStatement d.prevs[i].1.size) ×
      Vector (FVar Fp) d.publicOutput.size) := do
  let env ← replayOps vals d.ops 0 x.toArray
  return (fun i => ⟨⟨d.prevs[i].1.map (substLocal env), by simp⟩,
      .unchecked (substLocal env d.prevs[i].2)⟩,
    ⟨d.publicOutput.map (substLocal env), by simp⟩)

/-- Installing cached rule witnesses preserves its cells, allocation and constraints. -/
theorem build_replayRule_irrel (d : RuleDump) (vals vals' : Option (Array Fp))
    (x : Vector (FVar Fp) d.inputSize) (nv : ℕ) :
    build (replayRule d vals x) nv = build (replayRule d vals' x) nv := by
  simp only [replayRule, build_bind, build_replayOps_irrel vals vals']

end PicklesFixture
