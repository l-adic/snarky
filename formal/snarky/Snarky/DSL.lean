import Snarky.Circuit.DSL.Assert
import Snarky.Circuit.DSL.Bits
import Snarky.Circuit.DSL.Boolean
import Snarky.Circuit.DSL.Field
import Snarky.Circuit.DSL.Monad

/-!
# The user-facing barrel

Port of `Snarky.Circuit.DSL` (packages/snarky/src/Snarky/Circuit/DSL.purs), the umbrella
module circuit authors import. In PS it is a pure re-export barrel — no definitions, one
curated export list; Lean has no re-export mechanism, so THE BARREL IS THE IMPORT: this
file's import set (`Monad`/`Field`/`Boolean`/`Assert`/`Bits`; `SizedF` and `Utils` are
the plan-§6 follow-ons) is what `import Snarky.DSL` exposes.

Two barrel-semantics deviations, consequences of import-as-export:
- Lean exposes each module's WHOLE surface, where PS curates: PS's list omits
  `allBools` and the `square` constraint method (module-public, not re-exported), and
  everything here named `*Wit`/`*Core`/`*Aux` plus the gadget laws is law machinery, not
  user API — the module docstrings mark it.
- The backend (`build`/`prove` and the interpreter laws) rides in transitively — the
  gadget modules import it for their laws (D3/D12). PS's barrel does not export the
  backend; treat it as the verification surface, not the circuit-authoring one.

## The PS → Lean surface map (D7)

The walk's per-module name maps, consolidated — the lookup table for translating PS
circuit code. Rule of thumb: trailing underscores drop unless a Lean keyword or core
name forces otherwise; `*Generic`/`g*`/`r*` deriving machinery is uniformly non-ported
(D8), returning later as a `deriving` handler if wanted.

| PS | Lean | note |
| --- | --- | --- |
| `Snarky(..)` | `CircuitM` | the deep embedding — THE sanctioned deviation (`DSL/Monad`) |
| `CircuitOps(..)` | `CircuitM` constructors | one constructor per ops-record field |
| `AsProver(..)` | `AsProver` | reader-except stack; advice row dropped (D8) |
| `AsProverCtx(..)`, `liftAdvice`, `runAdvice` | — | the advice row (D8; also `Backend/Advice`) |
| `liftEffectSnarky`, `mkWitnessTable` | — | `Effect` machinery, no pure-embedding analogue |
| `runAsProver` | `AsProver.run` | |
| `throwAsProver` | `AsProver.throw` | |
| `read` | `readVar` | `read` is core's `MonadReader` primitive |
| `readCVar` | `AsProver.readCVar` | |
| `exists` | `witness` | `exists` is a Lean keyword |
| `fresh`, `addConstraint`, `assignVars`, `label` | same | |
| `check` (class `CheckedType`) | `CheckedType.check` | |
| `mul_`, `inv_`, `div_` | `mul`, `inv`, `div` | in `DSL/Monad`, their PS home |
| `not_`, `and_`, `or_` | `not`, `and`, `or` | shadow core's Bool functions; types resolve |
| `equals_`, `neq_`, `sum_`, `pow_`, `square_` | drop `_` | action-lifted `equals` non-ported (D8) |
| `if_` (class `IfThenElse`) | `select` | `if` is a keyword; class name kept |
| `true_`, `false_` | `true_`, `false_` | keywords keep the underscores |
| `xor_`, `any_`, `all_` | `xor`, `any`, `all` | |
| `assert*_` family | drop `_` | impossible constant asserts emit unsatisfiable rows |
| `assertEq`, `isEqual` (class `AssertEqual`) | same | the old transitional `assertEq` retired |
| `allBools` | `allBools` | |
| `unpack_`, `pack_` | `unpack`, `pack` | the width is an explicit `Nat` argument |
| `unpackPure`, `packPure` | same | |
| `PrimeField.toBigInt` | `ToNat.toNat` | the one curve-class fragment ported (`DSL/Bits`) |
| `Variable` + the `CVar` folds (`add_`, …) | same | folds keep `_` (raw-constructor clash) |
| `const_` | — | `CVar.const` is first-class |
| `EvaluationError(..)` | `EvalError` | variants remapped; see `Circuit/CVar` |
| `CircuitType` + methods | same | `sizeInFields` is the type-level `size`; `generic*` D8 |
| `Bool(..)` | `BoolVar` + its doors | D11: `witness` at (`UnChecked`) `Bool`; `BoolVar.unchecked` |
| `F(..)` | — | the value wrapper is unnecessary (class dispatch on `F` itself) |
| `FVar`, `BoolVar`, `UnChecked(..)` | same | |
| `BasicSystem`, `Basic(..)`, its methods | same | Lean also surfaces `square` (not in PS's list) |
| `SizedF` module, `seal` | — | plan-§6 follow-ons (`SizedF` builds on `ToNat`) |
-/
