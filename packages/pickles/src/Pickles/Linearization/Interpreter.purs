-- | Stack-based interpreter for Polish notation linearization polynomials.
-- | This approach avoids generating large PureScript expressions that
-- | overwhelm the compiler's type checker.
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

-- | Monadic evaluation state: extends EvalState with a lazy cache for zeta^n-1.
-- | The cache matches OCaml's `lazy (domain#vanishing_polynomial zeta)` binding
-- | (plonk_checks.ml:280), which is forced on first UnnormalizedLagrangeBasis call.
type EvalStateM a =
  { stack :: Array a
  , store :: Array a
  , position :: Int
  , zetaCache :: Maybe a -- ^ Memoized zeta^n-1, computed on first UnnormalizedLagrangeBasis
  }

-- | Monadic interpreter for Polish notation linearization polynomials.
-- | Unlike `evaluate`, this runs in the Snarky monad with FVar stack values.
-- | Key differences:
-- | - Stack holds already-evaluated FVar values (not monadic actions)
-- | - Store saves FVar values; Load retrieves them without re-execution
-- | - Peephole: Challenge Alpha + Pow N → alphaPow(N) pure lookup
-- | - Mul/Pow/UnnormalizedLagrangeBasis are monadic (create R1CS constraints)
-- | - Add/Sub are pure CVar operations (no constraints)
-- | - Lazy zeta^n-1: computed on first UnnormalizedLagrangeBasis, cached for reuse
evaluateM
  :: forall f n
   . Monad n
  => Array PolishToken
  -> EnvM f n
  -> n (FVar f)
evaluateM tokens env = do
  let initState = { stack: [], store: [], position: 0, zetaCache: Nothing } :: EvalStateM (FVar f)
  finalState <- evalLoopM tokens initState
  pure $ fromMaybe (env.field "0x0") (Array.last finalState.stack)
  where
  -- Main evaluation loop (monadic)
  evalLoopM :: Array PolishToken -> EvalStateM (FVar f) -> n (EvalStateM (FVar f))
  evalLoopM toks state =
    if state.position >= Array.length toks then
      pure state
    else
      case Array.index toks state.position of
        Nothing -> pure state
        Just token -> do
          newState <- evalTokenM toks token state
          evalLoopM toks newState

  -- Evaluate a single token (monadic)
  evalTokenM :: Array PolishToken -> PolishToken -> EvalStateM (FVar f) -> n (EvalStateM (FVar f))
  evalTokenM toks token state = case token of
    -- Constants (pure)
    Constant term -> pure $ push (evalConstantM term) (advance state)

    -- Challenges
    -- Peephole optimization: Challenge Alpha followed by Pow N → alphaPow(N) lookup
    Challenge Alpha ->
      case Array.index toks (state.position + 1) of
        Just (Pow n) ->
          -- Consume both tokens, push precomputed alpha^n
          pure $ push (env.alphaPow n) (state { position = state.position + 2 })
        _ ->
          -- Standalone Challenge Alpha (no Pow following) → alpha^1
          pure $ push (env.alphaPow 1) (advance state)
    Challenge Beta -> pure $ push env.beta (advance state)
    Challenge Gamma -> pure $ push env.gamma (advance state)
    Challenge JointCombiner -> pure $ push env.jointCombiner (advance state)

    -- Cell access (pure)
    Cell { col, row } ->
      pure $ push (env.cell (env.var col row)) (advance state)

    -- Stack operations (pure)
    Dup ->
      case Array.last state.stack of
        Just top -> pure $ push top (advance state)
        Nothing -> pure $ advance state

    -- Arithmetic
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

    -- Store/Load for sharing subexpressions
    -- Store saves the already-evaluated FVar value.
    Store ->
      case pop' state of
        Just { value, newState } ->
          let
            storeState = newState { store = Array.snoc newState.store value }
          in
            pure $ push value (advance storeState)
        Nothing -> pure $ advance state

    -- Load retrieves the saved FVar value (no re-execution!)
    Load n ->
      case Array.index state.store n of
        Just value -> pure $ push value (advance state)
        Nothing -> pure $ advance state

    -- Special terms
    VanishesOnZeroKnowledgeAndPreviousRows ->
      pure $ push env.vanishesOnZeroKnowledgeAndPreviousRows (advance state)

    -- Lazy zeta^n-1: compute on first use, cache for subsequent calls.
    -- Matches OCaml's Lazy.force zeta_to_n_minus_1 in unnormalized_lagrange_basis.
    UnnormalizedLagrangeBasis { zk_rows, offset } ->
      case state.zetaCache of
        Just cached -> do
          result <- env.lagrangeBasis cached { zkRows: zk_rows, offset }
          pure $ push result (advance state)
        Nothing -> do
          zetaToNMinus1 <- env.computeZetaToNMinus1
          result <- env.lagrangeBasis zetaToNMinus1 { zkRows: zk_rows, offset }
          pure $ push result (advance (state { zetaCache = Just zetaToNMinus1 }))

    -- Conditional execution (features always disabled)
    SkipIfNot flag count ->
      env.ifFeature
        { flag
        , onTrue: \_ -> do
            subResult <- evalSubExprM toks (state.position + 1) count state.store state.zetaCache
            let newState = state { position = state.position + 1 + count, store = subResult.store, zetaCache = subResult.zetaCache }
            pure $ push (fromMaybe (env.field "0x0") (Array.last subResult.stack)) newState
        , onFalse: \_ ->
            let
              newState = state { position = state.position + 1 + count }
            in
              if count <= 1 then pure $ push (env.field "0x0") newState
              else pure newState
        }

    SkipIf flag count ->
      env.ifFeature
        { flag
        , onTrue: \_ ->
            let
              newState = state { position = state.position + 1 + count }
            in
              if count <= 1 then pure $ push (env.field "0x0") newState
              else pure newState
        , onFalse: \_ -> do
            subResult <- evalSubExprM toks (state.position + 1) count state.store state.zetaCache
            let newState = state { position = state.position + 1 + count, store = subResult.store, zetaCache = subResult.zetaCache }
            pure $ push (fromMaybe (env.field "0x0") (Array.last subResult.stack)) newState
        }

  -- Evaluate a sub-expression (for SkipIf/SkipIfNot blocks)
  evalSubExprM :: Array PolishToken -> Int -> Int -> Array (FVar f) -> Maybe (FVar f) -> n (EvalStateM (FVar f))
  evalSubExprM toks startPos count store zetaCache =
    let
      subTokens = Array.slice startPos (startPos + count) toks
      initState = { stack: [], store, position: 0, zetaCache }
    in
      evalLoopM subTokens initState

  -- Evaluate a constant term (pure)
  evalConstantM :: ConstantTerm -> FVar f
  evalConstantM = case _ of
    EndoCoefficient -> env.endoCoefficient
    Mds { row, col } -> env.mds { row, col }
    Literal hex -> env.field hex

  -- Stack helpers
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
