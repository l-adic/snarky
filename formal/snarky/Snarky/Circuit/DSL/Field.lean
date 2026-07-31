import Snarky.Circuit.DSL.Monad

/-!
# Field gadgets

Port of `Snarky.Circuit.DSL.Field` (packages/snarky/src/Snarky/Circuit/DSL/Field.purs):
the field comparison and arithmetic gadgets. The centrepiece is `equals` — an equality
*test* returning a `BoolVar` rather than an assertion, via the standard inverse-or-zero
trick — with `sum`, `pow`, and `square` alongside.

Name map (D7; underscores drop): `equals_` → `equals`, `neq_` → `neq`, `sum_` → `sum`,
`pow_` → `pow`, `square_` → `square`. The PS action-lifted `equals` variant rides the
numeric-tower instances and is not ported (D8); `pow`'s exponent is `Nat` (PS `Int`,
never called negative).

Deviations from the PS original (per `formal/docs/snarky-ps-alignment.md`):
- PS witnesses `equals_`'s `{r, zInv}` record through the generic deriving machinery
  (D8, not ported) and retags `r` with a bare `coerce`; here the witness is the pair
  `UnChecked Bool × F` — the typed skip-the-check discipline PS's own `xor_` uses, and
  the `Prod` instances' first Lean consumer. Same one `existsOp` of two variables, same
  order (PS's record rows sort alphabetically: `r`, `zInv`), same absence of `boolean`
  checks — the gadget's two `r1cs` constraints already force booleanity
  (`Snarky.equals_sound`).
- `neq` is `not` after `equals`, as in PS (whose `not` rides the HeytingAlgebra action
  instance, D8); `not` lives in `DSL/Monad`, its PS home.
- The `CircuitType F Bool` instance pins `F : Type 0` (`AsProver` payloads share `F`'s
  universe), so the `BoolVar`-returning gadgets are stated for `Type`-sized fields —
  every concrete field is one.

D9 survey (the `snarky-test-utils` Field spec), in the D12 statement form — gadget laws
are stated against the interpreters, never re-derived over the field alone. Interpreter
theorems cannot live here (this module mirrors the PS layering, below the backend), so
they sit with the other interpreter-spanning theorems in `Snarky.Laws` (D3): the `eq`
rows are `Snarky.equals_sound`/`equals_complete` there, plus the fixed-input `decide`
examples in `Snarky.Example`; the `mul`/`inv`/`div` rows and `square`/`pow` likewise
(`div_sound`/`pow_sound` and their completeness twins are proved compositionally,
through the bind laws). The `sum` row is `sum_eval` below (`sum` is pure — its
evaluation IS its interpreter semantics). The `negate` row is `Circuit/CVar` algebra
under `reduce_eval`; `seal` is the
`DSL/Utils` follow-on (plan §6). The spec's end-to-end shape — compile, solve against
public inputs, compare with the model function — awaits `Backend/Compile` (walk
step 14).

Public results: `sum_eval` (a `roots.txt` entry); `equalsWit`/`equalsCore` are public
only as the named internals the `Snarky.Laws` gadget laws quantify over — not user API.
-/

namespace Snarky

variable {F c : Type u}

/-! ## The gadgets -/

/-- `equals`'s witness computation: the claimed answer bit and the inverse-or-zero.
Public only for the gadget laws in `Snarky.Laws`. -/
def equalsWit {F : Type} [Field F] [DecidableEq F] (z : CVar F) :
    AsProver F (UnChecked Bool × F) := do
  let zv ← AsProver.readCVar z
  pure (if zv = 0 then (⟨true⟩, 0) else (⟨false⟩, zv⁻¹))

/-- `equals`'s witnessing branch, over the precomputed difference `z` — split out so the
gadget laws in `Snarky.Laws` quantify over it uniformly. Public only for those laws. -/
def equalsCore {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (z : CVar F) :
    CircuitM F c (BoolVar F) := do
  let rz ← witness (val := UnChecked Bool × F) (equalsWit z)
  let r := rz.1.val
  addConstraint (BasicSystem.r1cs ↑r z (.const 0))
  addConstraint (BasicSystem.r1cs rz.2 z (CVar.sub_ (.const 1) ↑r))
  pure r

/-- Equality test returning a boolean variable (PS `equals_`). A constant difference
folds to the constant answer. Otherwise, with `z = a − b`: witness the pair `(r, zInv)`
— `r` the claimed answer at `UnChecked Bool`, `zInv` the inverse or zero — and constrain
`r · z = 0` and `zInv · z = 1 − r`. The pair forces `r = (a == b)` — in particular `r`
is boolean (`Snarky.equals_sound`), which is why the witness may skip the `boolean`
check. -/
def equals {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (a b : FVar F) :
    CircuitM F c (BoolVar F) :=
  match CVar.sub_ a b with
  | .const f => pure (.unchecked (.const (if f = 0 then 1 else 0)))
  | z => equalsCore z

/-- Negated equality test (PS `neq_ = not <<< equals_`): the negated `equals` bit. -/
def neq {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c] (a b : FVar F) :
    CircuitM F c (BoolVar F) := do
  let r ← equals a b
  pure (Snarky.not r)

/-- Sum a list of field variables — pure, no constraints (PS `sum_`, which folds an
`Array` the same way): `add_` over the list from `const 0`. -/
def sum [Add F] [Zero F] (xs : List (FVar F)) : FVar F :=
  xs.foldl CVar.add_ (.const 0)

/-- Fuel-indexed body of `pow`, structural on the fuel so the definition kernel-reduces
(`decide`-friendly; PS recurses on `n / 2` directly). The fuel-exhausted branch is
unreachable: `pow` seeds fuel `n`, and the exponent at least halves each step. Public
only for the gadget laws in `Snarky.Laws`. -/
def powGo [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c] :
    Nat → FVar F → Nat → CircuitM F c (FVar F)
  | _, _, 0 => pure (.const 1)
  | _, x, 1 => pure x
  | 0, x, _ => pure x
  | fuel + 1, x, n => do
    let sq ← mul x x
    let y ← powGo fuel sq (n / 2)
    if n % 2 = 0 then pure y else mul x y

/-- `x ^ n` by repeated squaring, in PS `pow_`'s recursion and constraint order: square,
recurse on `n / 2`, and multiply by `x` once more when `n` is odd. On a constant every
step goes through `mul`'s folding, so no constraints are emitted. -/
def pow [Add F] [Mul F] [Zero F] [One F] [DecidableEq F] [BasicSystem F c]
    (x : FVar F) (n : Nat) : CircuitM F c (FVar F) :=
  powGo n x n

/-- `square`'s witness computation: the square of the operand's value. Public only for
the gadget laws in `Snarky.Laws`. -/
def squareWit [Add F] [Mul F] (x : FVar F) : AsProver F F := do
  let xv ← AsProver.readCVar x
  pure (xv * xv)

/-- `square`'s witnessing branch: witness the square, pin it with one `square`
constraint. Split out so the gadget laws in `Snarky.Laws` quantify over it uniformly. -/
def squareCore [Add F] [Mul F] [BasicSystem F c] (x : FVar F) : CircuitM F c (FVar F) := do
  let z ← witness (val := F) (squareWit x)
  addConstraint (BasicSystem.square x z)
  pure z

/-- Square a field variable via the dedicated `square` constraint rather than `r1cs`
(PS `square_`, matching OCaml's `Checked.square`). A constant folds. -/
def square [Add F] [Mul F] [BasicSystem F c] (x : FVar F) : CircuitM F c (FVar F) :=
  match x with
  | .const f => pure (.const (f * f))
  | x => squareCore x

/-! ## The sum law (D9: the sum spec row) -/

private theorem sum_go [AddMonoid F] [Mul F] {env : Assignments F} :
    ∀ {xs : List (CVar F)} {vals : List F} {acc : CVar F} {a : F},
      xs.map (CVar.eval · env) = vals.map .ok → acc.eval env = .ok a →
      (xs.foldl CVar.add_ acc).eval env = .ok (a + vals.sum) := by
  intro xs
  induction xs with
  | nil =>
    intro vals acc a hmap hacc
    cases vals with
    | nil => simpa using hacc
    | cons v vs => cases hmap
  | cons x xs ih =>
    intro vals acc a hmap hacc
    cases vals with
    | nil => cases hmap
    | cons v vs =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hx, hrest⟩ := hmap
      have hstep : (CVar.add_ acc x).eval env = .ok (a + v) := by
        rw [CVar.eval_add_]
        simp only [CVar.eval, hacc, hx]
      simpa [add_assoc] using ih hrest hstep

/-- `sum` evaluates to the sum of its operands' values: if each `xᵢ` evaluates to `vᵢ`
under `env`, the folded expression evaluates to `Σ vᵢ`. -/
theorem sum_eval [AddMonoid F] [Mul F] {env : Assignments F} {xs : List (CVar F)}
    {vals : List F} (h : xs.map (CVar.eval · env) = vals.map .ok) :
    (sum xs).eval env = .ok vals.sum := by
  have h0 : (CVar.const (0 : F)).eval env = .ok 0 := rfl
  simpa [sum] using sum_go h h0

end Snarky
