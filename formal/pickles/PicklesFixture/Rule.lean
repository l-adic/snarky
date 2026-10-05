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
  /-- Emit a basic constraint. -/
  | constrain (c : Basic Fp)
  /-- Emit a padding row over seven cells. -/
  | pad (vs : Vector (FVar Fp) 7)

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

/-- A basic constraint's local ids, read through `env`. -/
def substBasic (env : Array (FVar Fp)) : Basic Fp → Basic Fp
  | .r1cs l r o => .r1cs (PicklesFixture.substLocal env l) (PicklesFixture.substLocal env r)
      (PicklesFixture.substLocal env o)
  | .equal a b => .equal (PicklesFixture.substLocal env a) (PicklesFixture.substLocal env b)
  | .square a s => .square (PicklesFixture.substLocal env a) (PicklesFixture.substLocal env s)
  | .boolean x => .boolean (PicklesFixture.substLocal env x)

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

/-- An operation of a rule dump: `{alloc: n}`, or `{constraint: c}` with `c` a basic constraint
or a padding row. A rule emitting any other kind of constraint is refused. -/
def parseOp (j : Json) : Except String RuleOp := do
  if let .ok n := j.getObjVal? "alloc" then return .alloc (← n.getNat?)
  let c ← j.getObjVal? "constraint"
  if let .ok b := c.getObjVal? "basic" then return .constrain (← parseBasic b)
  if let .ok p := c.getObjVal? "pad" then
    let vs ← FixtureKit.parseArrOf parseLocal p
    if h : vs.size = 7 then return .pad ⟨vs, h⟩ else throw s!"a padding row of {vs.size} cells"
  throw s!"a rule constraint other than a basic one or a padding row: {c.compress.take 80}"

/-- Whether every local id a constraint reads is below `n`. -/
def scopedBasicBelow (n : ℕ) : Basic Fp → Bool
  | .r1cs l r o => PicklesFixture.scopedBelow n l && PicklesFixture.scopedBelow n r &&
      PicklesFixture.scopedBelow n o
  | .equal a b => PicklesFixture.scopedBelow n a && PicklesFixture.scopedBelow n b
  | .square a s => PicklesFixture.scopedBelow n a && PicklesFixture.scopedBelow n s
  | .boolean x => PicklesFixture.scopedBelow n x

/-- The number of local ids in scope after `ops`, starting from `n`, when every constraint reads
only ids already in scope. -/
def scopeAfter : ℕ → List RuleOp → Option ℕ
  | n, [] => some n
  | n, .alloc m :: ops => scopeAfter (n + m) ops
  | n, .constrain c :: ops => if scopedBasicBelow n c then scopeAfter n ops else none
  | n, .pad vs :: ops => if vs.all (scopedBelow n) then scopeAfter n ops else none

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
    .addConstraintOp (.basic (substBasic env c)) (replayOps vals ops off env)
  | .pad vs :: ops, off, env =>
    .addConstraintOp (.pad (vs.map (substLocal env))) (replayOps vals ops off env)

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
