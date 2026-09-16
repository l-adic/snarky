-- | A stack machine over the Polish-notation linearization tables.
-- | The tables are interpreted rather than compiled into PureScript
-- | expressions, which at that size overwhelm the type checker.
module Pickles.Linearization.Interpreter
  ( evaluate
  , evaluateM
  , EvalState
  , initialState
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Pickles.Linearization.Env (Env, EnvM)
import Pickles.Linearization.Types (ChallengeTerm(..), ConstantTerm(..), PolishToken(..))
import Snarky.Circuit.DSL (FVar)

-- | The value stack, the `Store`/`Load` slots, and the token index.
type EvalState a =
  { stack :: Array a
  , store :: Array a
  , position :: Int
  }

initialState :: forall a. EvalState a
initialState = { stack: [], store: [], position: 0 }

-- | The value `tokens` leaves on top of the stack under `env`, or
-- | zero if it leaves none.
evaluate :: forall a. Array PolishToken -> Env a -> a
evaluate tokens env =
  let
    finalState = evalLoop tokens (Array.length tokens) initialState
  in
    fromMaybe (env.field "0x0") (Array.last finalState.stack)
  where
  evalLoop :: Array PolishToken -> Int -> EvalState a -> EvalState a
  evalLoop toks endPos state =
    if state.position >= endPos then
      state
    else
      case Array.index toks state.position of
        Nothing -> state
        Just token ->
          let
            newState = evalToken toks token state
          in
            evalLoop toks endPos newState

  evalToken :: Array PolishToken -> PolishToken -> EvalState a -> EvalState a
  evalToken toks token state = case token of
    Constant term -> push (evalConstant term) (advance state)

    -- No `Alpha`+`Pow` peephole here: with no constraints to save,
    -- the separate `Pow` case is enough.
    Challenge Alpha -> push (env.alphaPow 1) (advance state)
    Challenge Beta -> push env.beta (advance state)
    Challenge Gamma -> push env.gamma (advance state)
    Challenge JointCombiner -> push env.jointCombiner (advance state)

    Cell { col, row } ->
      push (env.cell (env.var col row)) (advance state)

    Dup ->
      case Array.last state.stack of
        Just top -> push top (advance state)
        Nothing -> advance state

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

    -- `Store`/`Load` carry the subexpressions the token stream shares.
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

    VanishesOnZeroKnowledgeAndPreviousRows ->
      push env.vanishesOnZeroKnowledgeAndPreviousRows (advance state)

    UnnormalizedLagrangeBasis { zk_rows, offset } ->
      push (env.unnormalizedLagrangeBasis { zkRows: zk_rows, offset }) (advance state)

    -- A feature-gated subexpression is encoded as the pair
    --   SkipIfNot(flag, len_e1) [e1] SkipIf(flag, len_e2) [e2]
    -- so each branch is a bounded sub-sequence, run for its
    -- top-of-stack value and selected by `ifFeature`.
    SkipIfNot flag countTrue ->
      let
        trueEnd = state.position + 1 + countTrue
        countFalse = case Array.index toks trueEnd of
          Just (SkipIf _ c) -> c
          _ -> 0
        falseEnd = trueEnd + 1 + countFalse
        extractTop s = fromMaybe (env.field "0x0") (Array.last s.stack)
        result = env.ifFeature
          { flag
          , onTrue: \_ ->
              extractTop (evalLoop toks trueEnd (state { position = state.position + 1 }))
          , onFalse: \_ ->
              extractTop (evalLoop toks falseEnd (state { position = trueEnd + 1 }))
          }
      in
        push result (state { position = falseEnd })

    -- `SkipIf` is consumed by the `SkipIfNot` handler above.
    SkipIf _ count ->
      state { position = state.position + 1 + count }

  evalConstant = case _ of
    EndoCoefficient -> env.endoCoefficient
    Mds { row, col } -> env.mds { row, col }
    Literal hex -> env.field hex

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

-- | `EvalState` plus a slot for `zeta^n - 1`, which is computed
-- | part-way through evaluation rather than up front.
type EvalStateM a =
  { stack :: Array a
  , store :: Array a
  , position :: Int
  , zetaCache :: Maybe a -- ^ filled by the first `UnnormalizedLagrangeBasis`
  }

-- | `evaluate` in a constraint-emitting monad. The stack holds
-- | evaluated `FVar`s, so a `Load` reuses a value rather than
-- | re-emitting the constraints that produced it. `Mul`, `Pow` and the
-- | Lagrange basis emit constraints; `Add` and `Sub` are free.
evaluateM
  :: forall f n
   . Monad n
  => Array PolishToken
  -> EnvM f n
  -> n (FVar f)
evaluateM tokens env = do
  let initState = { stack: [], store: [], position: 0, zetaCache: Nothing } :: EvalStateM (FVar f)
  finalState <- evalLoopM tokens (Array.length tokens) initState
  pure $ fromMaybe (env.field "0x0") (Array.last finalState.stack)
  where
  evalLoopM :: Array PolishToken -> Int -> EvalStateM (FVar f) -> n (EvalStateM (FVar f))
  evalLoopM toks endPos state =
    if state.position >= endPos then
      pure state
    else
      case Array.index toks state.position of
        Nothing -> pure state
        Just token -> do
          newState <- evalTokenM toks token state
          evalLoopM toks endPos newState

  evalTokenM :: Array PolishToken -> PolishToken -> EvalStateM (FVar f) -> n (EvalStateM (FVar f))
  evalTokenM toks token state = case token of
    Constant term -> pure $ push (evalConstantM term) (advance state)

    -- Every `Challenge Alpha` in the generated tables is immediately
    -- followed by a `Pow`, so the pair is read as one table lookup and
    -- the `alphaPow 1` fallback never fires.
    Challenge Alpha ->
      case Array.index toks (state.position + 1) of
        Just (Pow n) ->
          pure $ push (env.alphaPow n) (state { position = state.position + 2 })
        _ ->
          pure $ push (env.alphaPow 1) (advance state)
    Challenge Beta -> pure $ push env.beta (advance state)
    Challenge Gamma -> pure $ push env.gamma (advance state)
    Challenge JointCombiner -> pure $ push env.jointCombiner (advance state)

    Cell { col, row } ->
      pure $ push (env.cell (env.var col row)) (advance state)

    Dup ->
      case Array.last state.stack of
        Just top -> pure $ push top (advance state)
        Nothing -> pure $ advance state

    Add ->
      case pop2' state of
        Just { a, b, newState } ->
          pure $ push (env.add a b) (advance newState)
        Nothing -> pure $ advance state

    Mul ->
      case pop2' state of
        Just { a, b, newState } -> do
          result <- env.mul a b
          pure $ push result (advance newState)
        Nothing -> pure $ advance state

    Sub ->
      case pop2' state of
        Just { a, b, newState } ->
          pure $ push (env.sub a b) (advance newState)
        Nothing -> pure $ advance state

    Pow n ->
      case pop' state of
        Just { value, newState } -> do
          result <- env.pow value n
          pure $ push result (advance newState)
        Nothing -> pure $ advance state

    Store ->
      case pop' state of
        Just { value, newState } ->
          let
            storeState = newState { store = Array.snoc newState.store value }
          in
            pure $ push value (advance storeState)
        Nothing -> pure $ advance state

    -- `Load` returns the stored `FVar`, emitting nothing.
    Load n ->
      case Array.index state.store n of
        Just value -> pure $ push value (advance state)
        Nothing -> pure $ advance state

    VanishesOnZeroKnowledgeAndPreviousRows ->
      pure $ push env.vanishesOnZeroKnowledgeAndPreviousRows (advance state)

    -- `zeta^n - 1` is computed at the first basis term, so its
    -- constraints land there rather than at the start of the stream.
    UnnormalizedLagrangeBasis { zk_rows, offset } ->
      case state.zetaCache of
        Just cached -> do
          result <- env.lagrangeBasis cached { zkRows: zk_rows, offset }
          pure $ push result (advance state)
        Nothing -> do
          zetaToNMinus1 <- env.computeZetaToNMinus1
          result <- env.lagrangeBasis zetaToNMinus1 { zkRows: zk_rows, offset }
          pure $ push result (advance (state { zetaCache = Just zetaToNMinus1 }))

    -- A feature-gated subexpression is encoded as the pair
    --   SkipIfNot(flag, len_e1) [e1] SkipIf(flag, len_e2) [e2]
    -- so each branch is a bounded sub-sequence, run for its
    -- top-of-stack value and selected by `ifFeature`.
    SkipIfNot flag countTrue -> do
      let
        trueEnd = state.position + 1 + countTrue
        countFalse = case Array.index toks trueEnd of
          Just (SkipIf _ c) -> c
          _ -> 0
        falseEnd = trueEnd + 1 + countFalse
        extractTop s = fromMaybe (env.field "0x0") (Array.last s.stack)
      result <- env.ifFeature
        { flag
        , onTrue: \_ -> do
            s <- evalLoopM toks trueEnd (state { position = state.position + 1 })
            pure $ extractTop s
        , onFalse: \_ -> do
            s <- evalLoopM toks falseEnd (state { position = trueEnd + 1 })
            pure $ extractTop s
        }
      pure $ push result (state { position = falseEnd })

    -- `SkipIf` is consumed by the `SkipIfNot` handler above.
    SkipIf _ count ->
      pure $ state { position = state.position + 1 + count }

  evalConstantM = case _ of
    EndoCoefficient -> env.endoCoefficient
    Mds { row, col } -> env.mds { row, col }
    Literal hex -> env.field hex

  push :: FVar f -> EvalStateM (FVar f) -> EvalStateM (FVar f)
  push value state = state { stack = Array.snoc state.stack value }

  pop' :: EvalStateM (FVar f) -> Maybe { value :: FVar f, newState :: EvalStateM (FVar f) }
  pop' state = do
    { init, last } <- Array.unsnoc state.stack
    pure { value: last, newState: state { stack = init } }

  pop2' :: EvalStateM (FVar f) -> Maybe { a :: FVar f, b :: FVar f, newState :: EvalStateM (FVar f) }
  pop2' state = do
    { value: b, newState: s1 } <- pop' state
    { value: a, newState: s2 } <- pop' s1
    pure { a, b, newState: s2 }

  advance :: EvalStateM (FVar f) -> EvalStateM (FVar f)
  advance state = state { position = state.position + 1 }
