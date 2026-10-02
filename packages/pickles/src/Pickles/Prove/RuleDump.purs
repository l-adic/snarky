-- | A step rule as data: its body run once through a recording
-- | interpreter, which keeps each constraint as the rule emits it,
-- | before the kimchi reduction turns it into gate rows, and each
-- | allocation, in program order. The Lean side rebuilds the rule from
-- | this record and compiles `step_main` around it, so a rule is never
-- | transcribed by hand.
-- |
-- | Variables are local to the rule: `Var 0 … Var (inputSize - 1)` are
-- | its input's cells, and each allocation takes the next ids in order.
-- | Advice is never run, as in the builder.
-- |
-- | At a proof, `ruleWitness` runs the same body with its advice, in the
-- | same numbering, and returns the values its allocations took: what the
-- | replay needs to rebuild the step circuit's witness.
module Pickles.Prove.RuleDump
  ( RuleDump
  , RuleOp(..)
  , RulePrev
  , RuleWitness
  , recordRule
  , ruleWitness
  , encodeRuleDump
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Either (Either(..), either)
import Data.Foldable (for_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.List (List(..))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Foreign (Foreign)
import JS.BigInt as BigInt
import Pickles.Field (StepField)
import Pickles.Step.Main (RuleOutput)
import Pickles.Step.Slots (EncodedPrev, PrevValues, prevsVector)
import Safe.Coerce (coerce)
import Simple.JSON (writeImpl)
import Snarky.Backend.Advice (AdviceHandler)
import Snarky.Backend.Assignments as Assignments
import Snarky.Circuit.CVar (CVar(..), EvaluationError(..), Variable(..))
import Snarky.Circuit.DSL (class CircuitType, Basic(..), Bool(..), FVar, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Circuit.DSL.Monad (AsProver, CircuitOps(..), Snarky(..), runAsProver, throwAsProver)
import Snarky.Circuit.EvalError (catchEvalError, throwEvalError)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Curves.Class (toBigInt)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | A rule's body as data.
type RuleDump =
  { inputSize :: Int
  , ops :: Array RuleOp
  , prevs :: Array RulePrev
  , publicOutput :: Array (FVar StepField)
  }

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

-- | Run a rule through the recording interpreter. `len` is its slot
-- | count, `inputVal` and `outputVal` its input's and output's value
-- | types. A side-loaded slot carries a key the record has no place
-- | for, so a rule with one is refused.
recordRule
  :: forall @len @r @inputVal @outputVal prevsSpec inputVar outputVar
   . Reflectable len Int
  => CircuitType StepField inputVal inputVar
  => CircuitType StepField outputVal outputVar
  => ( AsProver StepField r (PrevValues prevsSpec)
       -> inputVar
       -> Snarky StepField (KimchiConstraint StepField) r (RuleOutput prevsSpec outputVar)
     )
  -> Effect RuleDump
recordRule rule = do
  let inputSize = sizeInFields (Proxy @StepField) (Proxy @inputVal)
  next <- Ref.new inputSize
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
    input = fieldsToVar @StepField @inputVal
      (if inputSize <= 0 then [] else map (Var <<< Variable) (Array.range 0 (inputSize - 1)))
    Snarky body = rule (throwAsProver (FailedAssertion "a rule dump runs no advice")) input
  out <- body ops
  prevs <- traverse prevOf (Vector.toUnfoldable (prevsVector @len out.prevs))
  emitted <- Ref.read log
  pure
    { inputSize
    , ops: Array.fromFoldable (List.reverse emitted)
    , prevs
    , publicOutput: varToFields @StepField @outputVal out.publicOutput
    }
  where
  prevOf :: EncodedPrev -> Effect RulePrev
  prevOf e = case e.verificationKey of
    Nothing -> pure { statement: e.fields, mustVerify: coerce e.proofMustVerify }
    Just _ -> throw "a rule dump covers compiled slots, not a side-loaded slot"

-- | A rule's witness at one proof: its input's cells and the values of its
-- | allocations, in `recordRule`'s numbering.
type RuleWitness = { input :: Array StepField, values :: Array StepField }

-- | Run a rule with its advice, as the prover does inside `stepMain`, but
-- | alone: the input's cells are the first variables, the advice runs
-- | against them and the rule's earlier allocations, and the rule's
-- | constraints are not emitted, so no reduction variable interleaves with
-- | its own. `prevStates` is the proof's previous statements, as
-- | `stepMain` hands them to the rule.
ruleWitness
  :: forall @inputVal r prevsSpec inputVar outputVar
   . CircuitType StepField inputVal inputVar
  => AdviceHandler r
  -> AsProver StepField r (PrevValues prevsSpec)
  -> inputVal
  -> ( AsProver StepField r (PrevValues prevsSpec)
       -> inputVar
       -> Snarky StepField (KimchiConstraint StepField) r (RuleOutput prevsSpec outputVar)
     )
  -> Effect (Either EvaluationError RuleWitness)
ruleWitness handler prevStates inputValue rule = do
  let
    input = valueToFields @StepField @inputVal inputValue
    inputSize = Array.length input
  assignments <- Assignments.fresh
  forWithIndex_ input \i x -> Assignments.set (Variable i) x assignments
  next <- Ref.new inputSize
  let
    run :: forall a. AsProver StepField r a -> Effect a
    run w = runAsProver handler assignments w >>= either throwEvalError pure
    assign vars fields = for_ (Array.zip vars fields) \(Tuple v x) -> Assignments.set v x assignments
    bump n = Ref.modify' (\c -> { state: c + n, value: c }) next
    ops = CircuitOps
      { freshOp: Variable <$> bump 1
      , addConstraintOp: \_ -> pure unit
      , existsOp: \n w -> do
          fields <- run w
          v <- bump n
          let vars = if n <= 0 then [] else map Variable (Array.range v (v + n - 1))
          assign vars fields
          pure vars
      , assignOp: \vars w -> run w >>= assign vars
      , pushLabelOp: \_ -> pure unit
      , popLabelOp: pure unit
      }
    inputVar = fieldsToVar @StepField @inputVal
      (if inputSize <= 0 then [] else map (Var <<< Variable) (Array.range 0 (inputSize - 1)))
    Snarky body = rule prevStates inputVar
  catchEvalError (body ops) >>= case _ of
    Left e -> pure (Left e)
    Right _ -> do
      end <- Ref.read next
      let
        allocated = if end <= inputSize then [] else Array.range inputSize (end - 1)
      pure case traverse (\v -> Assignments.lookup (Variable v) assignments) allocated of
        Just values -> Right { input, values }
        Nothing -> Left (FailedAssertion "a rule allocation took no value")

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
