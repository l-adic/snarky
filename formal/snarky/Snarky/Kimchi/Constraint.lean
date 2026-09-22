import Snarky.Kimchi.Constraint.GenericPlonk
import Snarky.Kimchi.Constraint.AddComplete
import Snarky.Kimchi.Constraint.EndoScalar
import Snarky.Kimchi.Constraint.VarBaseMul
import Snarky.Kimchi.Constraint.EndoMul
import Snarky.Kimchi.Constraint.Poseidon

/-!
# The kimchi constraint type and its reduction

The backend's constraint sum `KimchiConstraint`, the emitted-gate sum `KimchiGate`
with its row dispatch, the `BasicSystem` instance carrying the DSL's constructors into
that sum, and the one reduction `KimchiConstraint.reduce` taking a constraint to its
gate. Transcribed from packages/snarky-kimchi/src/Snarky/Constraint/Kimchi.purs.

Each arm of the reduction calls its gate's own reducer and wraps the emitted rows in
the matching `KimchiGate` arm. Two arms break that pattern. A `.basic` constraint
emits through the batching queue and so wraps as `.noOp`, carrying no rows of its own;
`.pad` has no gate module behind it, so `reducePad` pins its seven operands here and
emits one degenerate generic row.

The reduction is polymorphic in the reduction monad (`PlonkReductionM`), so the
builder and the prover run it unchanged. It therefore borrows and returns the one
shared variable counter of `Constraint/Reduction.lean`: reduction-internal variables
are numbered between user variables in program order, and that interleaving is fixture
bytes. Run in the prover it tests nothing — a kimchi constraint emits rows, not a
checkable predicate — so nothing here validates a witness.

The Poseidon parameters ride in the constraint payload (see `Constraint/Poseidon.lean`),
so the reduction takes no parameter for them.
-/

namespace Snarky.Kimchi

open Snarky

/-- The kimchi backend's constraint type: the DSL's `Basic` vocabulary, one arm per
modelled gate, and the padding row. -/
inductive KimchiConstraint (F : Type u) where
  /-- A `Basic` constraint, reduced through the generic-gate fan-out. -/
  | basic (c : Basic F)
  /-- A complete-addition constraint. -/
  | addComplete (c : AddComplete F)
  /-- A Poseidon block constraint. -/
  | poseidon (c : PoseidonConstraint F)
  /-- A variable-base scalar-multiplication constraint. -/
  | varBaseMul (c : VarBaseMul F)
  /-- A challenge-decomposition constraint. -/
  | endoScalar (c : EndoScalar F)
  /-- An endomorphism-optimized scalar-multiplication constraint. -/
  | endoMul (c : EndoMul F)
  /-- Pad the circuit by one row: the degenerate generic row of `mkPadRow`, over the
  seven permutable cells. Its use is to push a row count past a domain boundary; no
  Lean circuit constructs it, and it reads vacuously. -/
  | pad (vs : Vector (FVar F) 7)

/-- What one constraint reduces to: the per-gate row carriers, or nothing (a `Basic`
constraint emits through the batching queue instead). -/
inductive KimchiGate (F : Type u) where
  /-- One packed generic row. -/
  | plonk (r : Rows F)
  /-- One complete-addition row. -/
  | addComplete (r : Rows F)
  /-- A Poseidon block's rows. -/
  | poseidon (rs : List (KimchiRow F))
  /-- A scalar multiplication's row pairs. -/
  | varBaseMul (rs : List (KimchiRow F × KimchiRow F))
  /-- A challenge decomposition's rows. -/
  | endoScalar (rs : List (KimchiRow F))
  /-- An endomorphism multiplication's rows. -/
  | endoMul (rs : List (KimchiRow F))
  /-- No direct rows (a reduced `Basic` constraint). -/
  | noOp

/-- Row dispatch: the rows an emitted gate contributes, none for `.noOp`. -/
instance : ToKimchiRows F (KimchiGate F) where
  toKimchiRows
    | .plonk r => toKimchiRows r
    | .addComplete r => toKimchiRows r
    | .poseidon rs => toKimchiRows rs
    | .varBaseMul rs => toKimchiRows rs
    | .endoScalar rs => toKimchiRows rs
    | .endoMul rs => toKimchiRows rs
    | .noOp => []

/-- The DSL's constraint constructors, into the kimchi sum: each lands in `.basic`. -/
instance : BasicSystem F (KimchiConstraint F) where
  r1cs l r o := .basic (.r1cs l r o)
  equal a b := .basic (.equal a b)
  square a c := .basic (.square a c)
  boolean x := .basic (.boolean x)

variable {F : Type} {m : Type → Type}

/-- Pin the padding row's seven operands to variables and wire them into one row. -/
private def reducePad [Add F] [Mul F] [Zero F] [One F] [Neg F] [DecidableEq F]
    [Monad m] [PlonkReductionM F m] (vs : Vector (FVar F) 7) : m (Rows F) := do
  let v0 ← reduceToVariable vs[0]
  let v1 ← reduceToVariable vs[1]
  let v2 ← reduceToVariable vs[2]
  let v3 ← reduceToVariable vs[3]
  let v4 ← reduceToVariable vs[4]
  let v5 ← reduceToVariable vs[5]
  let v6 ← reduceToVariable vs[6]
  pure (mkPadRow ⟨⟨[v0, v1, v2, v3, v4, v5, v6]⟩, by simp⟩)

/-- Reduce a constraint through its gate's reducer and wrap the rows. A `.basic`
constraint emits into the batching queue instead and wraps as `.noOp`. -/
def KimchiConstraint.reduce [Add F] [Mul F] [Sub F] [Zero F] [One F] [Neg F]
    [DecidableEq F] [Monad m] [PlonkReductionM F m] :
    KimchiConstraint F → m (KimchiGate F)
  | .basic c => do
    Snarky.Kimchi.reduce c
    pure .noOp
  | .addComplete c => .addComplete <$> c.reduce
  | .poseidon c => .poseidon <$> c.reduce
  | .varBaseMul c => .varBaseMul <$> VarBaseMul.reduce c
  | .endoScalar c => .endoScalar <$> EndoScalar.reduce c
  | .endoMul c => .endoMul <$> c.reduce
  | .pad vs => .plonk <$> reducePad vs

end Snarky.Kimchi
