-- | A step input check and rule body as replayable operations, before
-- | Kimchi reduction. Lean allocates plain input fields and replays both
-- | inside `stepMain`.
-- |
-- | Variables are local to the rule: `Var 0 … Var (inputSize - 1)` are
-- | its input's cells, and each allocation takes the next ids in order.
-- | Advice is never run, as in the builder.
-- |
-- | The step solve captures witness values in that same numbering.
module Pickles.Prove.RuleDump
  ( RuleDump
  , RuleDumpJson(..)
  , RuleOp(..)
  , RulePrev
  , recordRule
  , encodeRuleDump
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.List (List(..))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Traversable (traverse)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Foreign (Foreign)
import JS.BigInt as BigInt
import Pickles.Field (StepField)
import Pickles.Step.Main (RuleOutput, runRuleWithInput)
import Pickles.Step.Slots (EncodedPrev, PrevValues, prevsVector)
import Safe.Coerce (coerce)
import Simple.JSON (class WriteForeign, writeImpl)
import Snarky.Circuit.CVar (CVar(..), EvaluationError(..), Variable(..))
import Snarky.Circuit.DSL (class CircuitType, Basic(..), Bool(..), FVar, sizeInFields, varToFields)
import Snarky.Circuit.DSL.Monad (class CheckedType, AsProver, CircuitOps(..), Snarky(..), throwAsProver)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Curves.Class (toBigInt)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | The input check followed by the rule body, in one local numbering.
type RuleDump =
  { inputSize :: Int
  , ops :: Array RuleOp
  , prevs :: Array RulePrev
  , publicOutput :: Array (FVar StepField)
  }

-- | The rule's wire representation. The rule itself remains the recorder's
-- | typed result; wrapping it selects its custom Simple.JSON encoding.
newtype RuleDumpJson = RuleDumpJson RuleDump

instance WriteForeign RuleDumpJson where
  writeImpl (RuleDumpJson d) = encodeRuleDump d

-- | One slot's previous statement: its cells and its must-verify flag.
type RulePrev =
  { statement :: Array (FVar StepField)
  , mustVerify :: FVar StepField
  }

-- | One operation of the body: an allocation of fresh variables, or a
-- | constraint as emitted.
data RuleOp
  = Alloc Int
  | Constrain (KimchiConstraint StepField)

-- | Record the input check and rule without running advice. Side-loaded
-- | slots are refused because their returned keys are not represented.
recordRule
  :: forall @len @r @inputVal @outputVal prevsSpec inputVar outputVar
   . Reflectable len Int
  => CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => CheckedType StepField (KimchiConstraint StepField) inputVar
  => ( AsProver StepField r (PrevValues prevsSpec)
       -> inputVar
       -> Snarky StepField (KimchiConstraint StepField) r (RuleOutput prevsSpec outputVar)
     )
  -> Effect RuleDump
recordRule rule = do
  let inputSize = sizeInFields (Proxy @StepField) (Proxy @inputVal)
  next <- Ref.new 0
  log <- Ref.new Nil
  let
    record op = Ref.modify_ (Cons op) log
    bump n = Ref.modify' (\c -> { state: c + n, value: c }) next
    alloc n
      | n <= 0 = pure []
      | otherwise = do
          v <- bump n
          record (Alloc n)
          pure (map Variable (Array.range v (v + n - 1)))
    ops = CircuitOps
      { freshOp: do
          v <- bump 1
          record (Alloc 1)
          pure (Variable v)
      , addConstraintOp: record <<< Constrain
      , existsOp: \n _ -> alloc n
      , assignOp: \_ _ -> pure unit
      , pushLabelOp: \_ -> pure unit
      , popLabelOp: pure unit
      }
    Snarky body = runRuleWithInput @inputVal rule
      (throwAsProver (FailedAssertion "a rule dump runs no advice"))
      (throwAsProver (FailedAssertion "a rule dump runs no advice"))
  { output: out } <- body ops
  prevs <- traverse prevOf (Vector.toUnfoldable (prevsVector @len out.prevs))
  emitted <- List.reverse <$> Ref.read log
  -- `inputSize` represents the initial allocation in the replay format.
  -- Zero-sized allocations are omitted by the recorder.
  bodyOps <-
    if inputSize == 0 then pure emitted
    else case emitted of
      Cons (Alloc n) rest | n == inputSize -> pure rest
      _ -> throw "a rule dump expected its input allocation first"
  pure
    { inputSize
    , ops: Array.fromFoldable bodyOps
    , prevs
    , publicOutput: varToFields @StepField @outputVal out.publicOutput
    }
  where
  prevOf :: EncodedPrev -> Effect RulePrev
  prevOf e = case e.verificationKey of
    Nothing -> pure { statement: e.fields, mustVerify: coerce e.proofMustVerify }
    Just _ -> throw "a rule dump covers compiled slots, not a side-loaded slot"

-- | The dump's JSON: field elements as decimal strings, a variable
-- | expression as `{var}`, `{const}`, `{add: [a, b]}` or `{scale: {k, x}}`,
-- | and each constraint under its `KimchiConstraint` arm's name with the
-- | payload's own field names.
encodeRuleDump :: RuleDump -> Foreign
encodeRuleDump d = writeImpl
  { inputSize: d.inputSize
  , ops: map op d.ops
  , prevs: map (\p -> writeImpl { statement: map cvar p.statement, mustVerify: cvar p.mustVerify }) d.prevs
  , publicOutput: map cvar d.publicOutput
  }
  where
  op = case _ of
    Alloc n -> writeImpl { alloc: n }
    Constrain c -> writeImpl { constraint: constraint c }

field :: StepField -> Foreign
field = writeImpl <<< BigInt.toString <<< toBigInt

cvar :: FVar StepField -> Foreign
cvar = case _ of
  Var (Variable v) -> writeImpl { var: v }
  Const c -> writeImpl { const: field c }
  Add a b -> writeImpl { add: [ cvar a, cvar b ] }
  ScalarMul k a -> writeImpl { scale: { k: field k, x: cvar a } }

xy :: { x :: FVar StepField, y :: FVar StepField } -> Foreign
xy p = writeImpl { x: cvar p.x, y: cvar p.y }

point :: AffinePoint (FVar StepField) -> Foreign
point (AffinePoint p) = xy p

cvars :: forall n. Vector.Vector n (FVar StepField) -> Array Foreign
cvars = map cvar <<< Vector.toUnfoldable

constraint :: KimchiConstraint StepField -> Foreign
constraint = case _ of
  KimchiBasic b -> writeImpl { basic: basic b }
  KimchiAddComplete c -> writeImpl
    { addComplete:
        { p1: xy c.p1
        , p2: xy c.p2
        , p3: xy c.p3
        , inf: cvar c.inf
        , sameX: cvar c.sameX
        , s: cvar c.s
        , infZ: cvar c.infZ
        , x21Inv: cvar c.x21Inv
        }
    }
  KimchiPoseidon c -> writeImpl { poseidon: { state: map cvars (Vector.toUnfoldable c.state) :: Array (Array Foreign) } }
  KimchiVarBaseMul rounds -> writeImpl
    { varBaseMul: rounds <#> \r -> writeImpl
        { accs: map point (Vector.toUnfoldable r.accs) :: Array Foreign
        , bits: cvars r.bits
        , slopes: cvars r.slopes
        , nPrev: cvar r.nPrev
        , nNext: cvar r.nNext
        , base: point r.base
        }
    }
  KimchiEndoScalar rounds -> writeImpl
    { endoScalar: rounds <#> \r -> writeImpl
        { n0: cvar r.n0
        , n8: cvar r.n8
        , a0: cvar r.a0
        , a8: cvar r.a8
        , b0: cvar r.b0
        , b8: cvar r.b8
        , xs: cvars r.xs
        }
    }
  KimchiEndoMul c -> writeImpl
    { endoMul:
        { state: NEA.toArray c.state <#> \r -> writeImpl
            { t: point r.t
            , p: point r.p
            , r: point r.r
            , s: point r.s
            , s1: cvar r.s1
            , s3: cvar r.s3
            , nAcc: cvar r.nAcc
            , nAccNext: cvar r.nAccNext
            , bits: cvars r.bits
            , inv: cvar r.inv
            }
        , s: point c.s
        , nAcc: cvar c.nAcc
        }
    }
  KimchiPad vs -> writeImpl { pad: cvars vs }

basic :: Basic StepField -> Foreign
basic = case _ of
  R1CS r -> writeImpl { r1cs: { left: cvar r.left, right: cvar r.right, output: cvar r.output } }
  Equal a b -> writeImpl { equal: [ cvar a, cvar b ] }
  Square a c -> writeImpl { square: [ cvar a, cvar c ] }
  Boolean a -> writeImpl { boolean: cvar a }
