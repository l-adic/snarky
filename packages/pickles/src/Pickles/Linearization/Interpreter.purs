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
  evalToken _toks token state = case token of
    -- Constants
    Constant term -> push (evalConstant term) (advance state)

    -- Challenges
    -- Note: this pure interpreter does not do the Alpha+Pow peephole
    -- because over concrete fields, alphaPow is just a lookup and the
    -- separate Pow case handles exponentiation. The peephole matters
    -- in evaluateM where it avoids generating unnecessary constraints.
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

    -- Conditional: SkipIfNot — if feature is NOT enabled, skip count tokens.
    -- Used for the true branch of IfFeature(feat, e1, e2):
    --   SkipIfNot(feat, len_e1) [e1 tokens] SkipIf(feat, len_e2) [e2 tokens]
    -- When enabled, e1 evaluates inline; when disabled, e1 is skipped.
    SkipIfNot flag count ->
      env.ifFeature
        { flag
        , onTrue: \_ -> advance state
        , onFalse: \_ -> state { position = state.position + 1 + count }
        }

    -- Conditional: SkipIf — if feature IS enabled, skip count tokens.
    -- Used for the false branch of IfFeature(feat, e1, e2):
    --   SkipIfNot(feat, len_e1) [e1 tokens] SkipIf(feat, len_e2) [e2 tokens]
    -- When enabled, e2 is skipped; when disabled, e2 evaluates inline.
    SkipIf flag count ->
      env.ifFeature
        { flag
        , onTrue: \_ -> state { position = state.position + 1 + count }
        , onFalse: \_ -> advance state
        }

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
    -- Peephole: Challenge Alpha is always followed by Pow N in the
    -- generated token streams (Rust's to_polish only emits Alpha as
    -- part of Expr::Pow(alpha, n)). The fallback to alphaPow 1 is
    -- defensive and never fires in practice.
    Challenge Alpha ->
      case Array.index toks (state.position + 1) of
        Just (Pow n) ->
          pure $ push (env.alphaPow n) (state { position = state.position + 2 })
        _ ->
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

    -- Conditional: SkipIfNot — if feature is NOT enabled, skip count tokens.
    SkipIfNot flag count ->
      env.ifFeature
        { flag
        , onTrue: \_ -> pure $ advance state
        , onFalse: \_ -> pure $ state { position = state.position + 1 + count }
        }

    -- Conditional: SkipIf — if feature IS enabled, skip count tokens.
    SkipIf flag count ->
      env.ifFeature
        { flag
        , onTrue: \_ -> pure $ state { position = state.position + 1 + count }
        , onFalse: \_ -> pure $ advance state
        }

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
