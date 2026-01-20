-- | Stack-based interpreter for Polish notation linearization polynomials.
-- | This approach avoids generating large PureScript expressions that
-- | overwhelm the compiler's type checker.
module Pickles.Linearization.Interpreter
  ( evaluate
  , EvalState
  , initialState
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Pickles.Linearization.Env (Env)
import Pickles.Linearization.Types (ChallengeTerm(..), ConstantTerm(..), PolishToken(..))

-- | Evaluation state: stack of values and stored values for Load
type EvalState a =
  { stack :: Array a
  , store :: Array a
  , position :: Int -- Current position in token array
  }

-- | Initial empty state
initialState :: forall a. EvalState a
initialState = { stack: [], store: [], position: 0 }

-- | Evaluate a Polish notation token array with the given environment
evaluate :: forall a. Array PolishToken -> Env a -> a
evaluate tokens env =
  let
    finalState = evalLoop tokens initialState
  in
    -- Result is the top of the stack (or zero if empty)
    fromMaybe (env.field "0x0") (Array.last finalState.stack)
  where
  -- Main evaluation loop
  evalLoop :: Array PolishToken -> EvalState a -> EvalState a
  evalLoop toks state =
    if state.position >= Array.length toks then
      state
    else
      case Array.index toks state.position of
        Nothing -> state
        Just token ->
          let
            newState = evalToken toks token state
          in
            evalLoop toks newState

  -- Evaluate a single token
  evalToken :: Array PolishToken -> PolishToken -> EvalState a -> EvalState a
  evalToken _toks token state = evalTokenInner _toks token state

  -- Inner token evaluation (no tracing)
  evalTokenInner :: Array PolishToken -> PolishToken -> EvalState a -> EvalState a
  evalTokenInner toks token state = case token of
    -- Constants
    Constant term -> push (evalConstant term) (advance state)

    -- Challenges
    Challenge Alpha -> push (env.alphaPow 1) (advance state)
    Challenge Beta -> push env.beta (advance state)
    Challenge Gamma -> push env.gamma (advance state)
    Challenge JointCombiner -> push env.jointCombiner (advance state)

    -- Cell access
    Cell { col, row } ->
      push (env.cell (env.var col row)) (advance state)

    -- Stack operations
    Dup ->
      case Array.last state.stack of
        Just top -> push top (advance state)
        Nothing -> advance state

    -- Arithmetic
    Add ->
      case pop2 state of
        Just { a, b, newState } ->
          push (env.add a b) (advance newState)
        Nothing -> advance state

    Mul ->
      case pop2 state of
        Just { a, b, newState } ->
          push (env.mul a b) (advance newState)
        Nothing -> advance state

    Sub ->
      case pop2 state of
        Just { a, b, newState } ->
          push (env.sub a b) (advance newState)
        Nothing -> advance state

    Pow n ->
      case pop state of
        Just { value, newState } ->
          push (env.pow value n) (advance newState)
        Nothing -> advance state

    -- Store/Load for sharing subexpressions
    Store ->
      case pop state of
        Just { value, newState } ->
          let
            storeState = newState { store = Array.snoc newState.store value }
          in
            push value (advance storeState)
        Nothing -> advance state

    Load n ->
      case Array.index state.store n of
        Just value -> push value (advance state)
        Nothing -> advance state

    -- Special terms
    VanishesOnZeroKnowledgeAndPreviousRows ->
      push env.vanishesOnZeroKnowledgeAndPreviousRows (advance state)

    UnnormalizedLagrangeBasis { zk_rows, offset } ->
      push (env.unnormalizedLagrangeBasis { zkRows: zk_rows, offset }) (advance state)

    -- Conditional execution
    -- SkipIfNot: if feature is NOT enabled, skip count tokens
    --
    -- The expression uses a pattern where each feature has:
    -- - SkipIfNot(feat, N): large block with gate computation
    -- - SkipIfNot(feat, 1): small block with zero constant
    -- - Add: combines results
    --
    -- When disabled (all features treated as disabled for testing):
    -- - Large block (count > 1): skip, DON'T push (the block would produce a value)
    -- - Small block (count <= 1): skip, push zero (provides the "else" value)
    --
    -- IMPORTANT: When skipping, we must NOT evaluate the sub-expression at all
    -- (no side effects like Store operations should occur).
    SkipIfNot flag count ->
      env.ifFeature
        { flag
        , onTrue: \_ ->
            -- Feature enabled: evaluate sub-expression and use result
            let
              subResult = evalSubExpr toks (state.position + 1) count state.store
              newState = state { position = state.position + 1 + count, store = subResult.store }
            in
              push (fromMaybe (env.field "0x0") (Array.last subResult.stack)) newState
        , onFalse: \_ ->
            -- Feature disabled: skip entirely, don't evaluate sub-expression
            let
              newState = state { position = state.position + 1 + count }
            in
              if count <= 1 then push (env.field "0x0") newState -- Small blocks push zero
              else newState -- Large blocks: just skip, don't push
        }

    -- SkipIf: if feature IS enabled, skip count tokens (opposite of SkipIfNot)
    SkipIf flag count ->
      env.ifFeature
        { flag
        , onTrue: \_ ->
            -- Feature enabled: skip entirely, don't evaluate sub-expression
            let
              newState = state { position = state.position + 1 + count }
            in
              if count <= 1 then push (env.field "0x0") newState
              else newState
        , onFalse: \_ ->
            -- Feature disabled: evaluate sub-expression and use result
            let
              subResult = evalSubExpr toks (state.position + 1) count state.store
              newState = state { position = state.position + 1 + count, store = subResult.store }
            in
              push (fromMaybe (env.field "0x0") (Array.last subResult.stack)) newState
        }

  -- Evaluate a sub-expression (for SkipIf/SkipIfNot blocks)
  evalSubExpr :: Array PolishToken -> Int -> Int -> Array a -> EvalState a
  evalSubExpr toks startPos count store =
    let
      subTokens = Array.slice startPos (startPos + count) toks
      initState = { stack: [], store, position: 0 }
    in
      evalLoop subTokens initState

  -- Evaluate a constant term
  evalConstant :: ConstantTerm -> a
  evalConstant = case _ of
    EndoCoefficient -> env.endoCoefficient
    Mds { row, col } -> env.mds { row, col }
    Literal hex -> env.field hex

  -- Stack helpers
  push :: a -> EvalState a -> EvalState a
  push value state = state { stack = Array.snoc state.stack value }

  pop :: EvalState a -> Maybe { value :: a, newState :: EvalState a }
  pop state = do
    { init, last } <- Array.unsnoc state.stack
    pure { value: last, newState: state { stack = init } }

  pop2 :: EvalState a -> Maybe { a :: a, b :: a, newState :: EvalState a }
  pop2 state = do
    { value: b, newState: s1 } <- pop state
    { value: a, newState: s2 } <- pop s1
    pure { a, b, newState: s2 }

  advance :: EvalState a -> EvalState a
  advance state = state { position = state.position + 1 }
