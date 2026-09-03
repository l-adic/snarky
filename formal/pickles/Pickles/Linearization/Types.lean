/-!
# The linearization token language

The `PolishToken` alphabet of kimchi's linearization, transcribed from
`packages/pickles-linearization-types/src/Pickles/Linearization/Types.purs` — itself the
PureScript image of proof-systems' `kimchi::circuits::expr::PolishToken`. A linearization
is a reverse-Polish program over this alphabet, dumped from Rust into
`packages/pickles-codegen/rust/output/{pallas,vesta}_scalar_field.json` and decoded by
`PicklesFixture.TokenParser`. That JSON is the source of truth: the PureScript
`Pickles.Linearization.{Pallas,Vesta}` modules are generated FROM it, so this transcription
and the PureScript one are siblings rather than parent and child, and a disagreement
between them is detectable.

The stream is a **stack machine**, not an expression tree. `Dup`, `Store` and `Load` give
sharing; `SkipIfNot`/`SkipIf` encode a feature-flag conditional as two bounded
sub-sequences, laid out as

  `SkipIfNot f n₁ · e₁ · SkipIf f n₂ · e₂`

where `e₁` is taken when the feature is enabled and `e₂` when it is not. The semantics live
in `Pickles.Linearization.Interpreter`; this module is the alphabet alone.

## Two deviations from the PureScript, both deliberate

`ConstantTerm.literal` carries a `Nat`, where the PureScript carries the raw `"0x…"` string
and defers to a partial `parseHex` inside the environment. Decoding the hex once, at parse
time, keeps the interpreter's constant lookup total and reduces the environment's literal
operation to a `Nat`-cast. The denoted values are identical; only the representation moves
earlier.

Column and slot indices are `Nat` rather than bounded types, mirroring the untyped numbers
in the JSON. Range facts (`Witness` below 15, `Load` inside the store) belong to the
well-formedness predicate over a concrete stream, where they are decidable, rather than to
the alphabet — the deployed interpreter itself tolerates out-of-range indices by
defaulting, and that behaviour must be modelled rather than typed away.
-/

namespace Pickles.Linearization

/-- Which of the two adjacent rows a cell reference reads. -/
inductive CurrOrNext where
  /-- The row the constraint is evaluated at. -/
  | curr
  /-- Its successor, used by the multi-row gates. -/
  | next
  deriving DecidableEq, Repr

/-- A gate's selector column, naming the gate whose selector polynomial is read. Includes
the gates outside the modelled fragment (range check, foreign field, xor, rot): they occur
in the deployed stream, inside feature-flagged branches. -/
inductive GateType where
  /-- The generic gate. -/
  | generic
  /-- The Poseidon permutation gate. -/
  | poseidon
  /-- Complete elliptic-curve addition. -/
  | completeAdd
  /-- Variable-base scalar multiplication. -/
  | varBaseMul
  /-- Endomorphism-based scalar multiplication. -/
  | endoMul
  /-- Endomorphism scalar recoding. -/
  | endoMulScalar
  /-- Range check, first half. -/
  | rangeCheck0
  /-- Range check, second half. -/
  | rangeCheck1
  /-- Foreign-field addition. -/
  | foreignFieldAdd
  /-- Foreign-field multiplication. -/
  | foreignFieldMul
  /-- 16-bit xor. -/
  | xor16
  /-- 64-bit rotation. -/
  | rot64
  deriving DecidableEq, Repr

/-- The lookup families a lookup selector can name. Outside the modelled fragment. -/
inductive LookupPattern where
  /-- The plain lookup pattern. -/
  | lookup
  /-- The xor lookup pattern. -/
  | xor
  /-- The range-check lookup pattern. -/
  | rangeCheck
  /-- The foreign-field-multiplication lookup pattern. -/
  | foreignFieldMul
  deriving DecidableEq, Repr

/-- A column of the evaluation table, as a cell reference names it. -/
inductive Column where
  /-- Witness column `i` (the deployed streams use `i < 15`). -/
  | witness (i : Nat)
  /-- Coefficient column `i` (the deployed streams use `i < 15`). -/
  | coefficient (i : Nat)
  /-- The selector column of gate `g`. -/
  | index (g : GateType)
  /-- Sorted lookup column `i`. -/
  | lookupSorted (i : Nat)
  /-- The lookup aggregation column. -/
  | lookupAggreg
  /-- The lookup table column. -/
  | lookupTable
  /-- The runtime lookup table column. -/
  | lookupRuntimeTable
  /-- The runtime lookup selector column. -/
  | lookupRuntimeSelector
  /-- The selector column of lookup family `p`. -/
  | lookupKindIndex (p : LookupPattern)
  deriving DecidableEq, Repr

/-- A constant the stream can push: a curve/field parameter or a numeric literal. -/
inductive ConstantTerm where
  /-- The endomorphism coefficient of the curve. -/
  | endoCoefficient
  /-- Entry `(row, col)` of the Poseidon MDS matrix. -/
  | mds (row col : Nat)
  /-- A numeric literal, decoded from the JSON's `"0x…"` string (see the preamble). -/
  | literal (value : Nat)
  deriving DecidableEq, Repr

/-- A verifier challenge the stream can push. -/
inductive ChallengeTerm where
  /-- The constraint-aggregation challenge. Always emitted as part of `Expr::Pow(alpha, n)`,
  which is what licenses the interpreter's Alpha+Pow peephole. -/
  | alpha
  /-- The permutation challenge `β`. -/
  | beta
  /-- The permutation challenge `γ`. -/
  | gamma
  /-- The lookup joint combiner. Outside the modelled fragment. -/
  | jointCombiner
  deriving DecidableEq, Repr

/-- An optional-feature predicate, guarding a `SkipIf`/`SkipIfNot` branch. Every flag the
deployed streams use is disabled in the modelled fragment, so every guarded branch is
dead — see the specialization pass in `Pickles.Linearization.Interpreter`. -/
inductive FeatureFlag where
  /-- The range-check-0 gate is enabled. -/
  | rangeCheck0
  /-- The range-check-1 gate is enabled. -/
  | rangeCheck1
  /-- The foreign-field-addition gate is enabled. -/
  | foreignFieldAdd
  /-- The foreign-field-multiplication gate is enabled. -/
  | foreignFieldMul
  /-- The xor gate is enabled. -/
  | xor
  /-- The rotation gate is enabled. -/
  | rot
  /-- Lookup tables are in use. -/
  | lookupTables
  /-- Runtime lookup tables are in use. -/
  | runtimeLookupTables
  /-- Lookup family `p` is in use. -/
  | lookupPattern (p : LookupPattern)
  /-- The lookup table has width `n`. -/
  | tableWidth (n : Nat)
  /-- There are `n` lookups per row. -/
  | lookupsPerRow (n : Nat)
  deriving DecidableEq, Repr

/-- One instruction of a linearization program. -/
inductive PolishToken where
  /-- Push a constant. -/
  | constant (c : ConstantTerm)
  /-- Push a challenge. -/
  | challenge (c : ChallengeTerm)
  /-- Push the evaluation of `col` at `row`. -/
  | cell (col : Column) (row : CurrOrNext)
  /-- Duplicate the top of the stack. -/
  | dup
  /-- Replace the top of the stack by its `n`-th power. -/
  | pow (n : Nat)
  /-- Pop two, push their sum. -/
  | add
  /-- Pop two, push their product. -/
  | mul
  /-- Pop two, push their difference. -/
  | sub
  /-- Push the zero-knowledge/previous-rows vanishing evaluation. -/
  | vanishesOnZeroKnowledgeAndPreviousRows
  /-- Push the unnormalized Lagrange basis at `offset`; `zkRows` selects the shifted
  domain. The offset is signed — the deployed streams use `0` and `-1`. -/
  | unnormalizedLagrangeBasis (zkRows : Bool) (offset : Int)
  /-- Append the top of the stack to the store, keeping it on the stack. -/
  | store
  /-- Push store slot `i`. -/
  | load (i : Nat)
  /-- Skip the next `n` tokens when feature `f` is ENABLED (the else-branch marker). -/
  | skipIf (f : FeatureFlag) (n : Nat)
  /-- Skip the next `n` tokens when feature `f` is DISABLED (the then-branch marker). -/
  | skipIfNot (f : FeatureFlag) (n : Nat)
  deriving DecidableEq, Repr

end Pickles.Linearization
