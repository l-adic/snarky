module Snarky.Constraint.Kimchi.Reduction
  ( Rows
  , addEqualsConstraint
  , addGenericPlonkConstraint
  , class PlonkReductionM
  , createInternalVariable
  , finalizeGateQueue
  , mkRawGeneric7Row
  , reduceAffineExpression
  , reduceAsBuilder
  , reduceAsProver
  , reduceToVariable
  ) where

import Prelude

import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.List (reverse) as List
import Data.List.NonEmpty (fromFoldable)
import Data.List.Types (List(..), NonEmptyList(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, over, un)
import Data.NonEmpty (NonEmpty(..))
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Data.UnionFind as UF
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Exception.Unsafe (unsafeThrow)
import Record as Record
import Snarky.Circuit.CVar (AffineExpression(..), CVar, evalAffineExpression, incrementVariable, reduceToAffineExpression)
import Snarky.Circuit.DSL (EvaluationError(..), Variable)
import Snarky.Constraint.Kimchi.Types (class ToKimchiRows, AuxState(..), GateKind(..), GenericPlonkConstraint, KimchiRow)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

class (Monad m, PrimeField f) <= PlonkReductionM m f | m -> f where
  createInternalVariable
    :: AffineExpression f
    -> m Variable
  addGenericPlonkConstraint
    :: GenericPlonkConstraint f
    -> m Unit
  addEqualsConstraint
    :: { cl :: f
       , vl :: Maybe Variable
       , cr :: f
       , vr :: Maybe Variable
       }
    -> m Unit

-- return a * x where a \in f and x is a variable.
reduceAffineExpression
  :: forall f m
   . PlonkReductionM m f
  => AffineExpression f
  -> m (Tuple (Maybe Variable) f)
reduceAffineExpression (AffineExpression { constant, terms }) = case fromFoldable terms of
  Nothing -> pure $ Tuple Nothing (fromMaybe zero constant)
  Just (NonEmptyList (NonEmpty head tail)) -> case tail of
    Nil -> case constant of
      Nothing -> pure $ lmap Just head
      Just c
        | c == zero -> pure $ lmap Just head
        | otherwise -> do
            vo <- createInternalVariable $ AffineExpression { constant, terms: [ head ] }
            let Tuple vl cl = head
            addGenericPlonkConstraint { vl: Just vl, cl, vr: Nothing, cr: zero, vo: Just vo, co: -one, m: zero, c }
            pure $ Tuple (Just vo) one
    Cons first rest -> do
      -- 2+ terms: head saved for final gate, tail right-recursively reduced.
      -- Matches OCaml's reduce_lincom + completely_reduce.
      Tuple rx rs <- completelyReduce first rest
      let Tuple lx ls = head
      vo <- createInternalVariable $ AffineExpression { constant, terms: [ Tuple lx ls, Tuple rx rs ] }
      addGenericPlonkConstraint { cl: ls, vl: Just lx, cr: rs, vr: Just rx, co: -one, vo: Just vo, m: zero, c: fromMaybe zero constant }
      pure $ Tuple (Just vo) one
  where
  -- Right recursion matching OCaml's completely_reduce.
  -- Reduces a list of (variable, coefficient) terms into a single variable.
  completelyReduce :: Tuple Variable f -> List (Tuple Variable f) -> m (Tuple Variable f)
  completelyReduce single Nil = pure single
  completelyReduce (Tuple lx ls) (Cons next rest') = do
    Tuple rx rs <- completelyReduce next rest'
    vo <- createInternalVariable $ AffineExpression { constant: Nothing, terms: [ Tuple lx ls, Tuple rx rs ] }
    addGenericPlonkConstraint { cl: ls, vl: Just lx, cr: rs, vr: Just rx, co: -one, vo: Just vo, m: zero, c: zero }
    pure $ Tuple vo one

reduceToVariable
  :: forall f m
   . PlonkReductionM m f
  => CVar f Variable
  -> m Variable
reduceToVariable var = do
  Tuple mvar c <- reduceAffineExpression $ reduceToAffineExpression var
  case mvar of
    Nothing -> do
      vl <- createInternalVariable $ AffineExpression { constant: Just c, terms: mempty }
      addEqualsConstraint { cl: one, vl: Just vl, cr: c, vr: Nothing }
      pure vl
    -- result is c * v
    Just v ->
      if c == one then pure v
      else do
        c_times_v <- createInternalVariable $ AffineExpression { constant: zero, terms: [ Tuple v c ] }
        -- c * v - c_times_v = 0
        addGenericPlonkConstraint { cl: c, vl: Just v, cr: zero, vr: Nothing, co: -one, vo: Just c_times_v, m: zero, c: zero }
        pure c_times_v

newtype Rows f = Rows (KimchiRow f)

instance ToKimchiRows f (Rows f) where
  toKimchiRows (Rows as) = Array.singleton as

mkRawGeneric7Row :: forall f. Vector.Vector 7 Variable -> Rows f
mkRawGeneric7Row vs =
  let
    paddedVars :: Vector.Vector 15 (Maybe Variable)
    paddedVars = map Just vs `Vector.append` Vector.generate (const Nothing)
  in
    Rows { kind: GenericPlonkGate, variables: paddedVars, coeffs: [] }

reduceAsBuilder
  :: forall f a r
   . PrimeField f
  => { nextVariable :: Variable
     , aux :: AuxState f
     | r
     }
  -> (forall m. PlonkReductionM m f => m a)
  -> Tuple
       a
       { nextVariable :: Variable
       , constraints :: Array (Rows f)
       , aux :: AuxState f
       }
reduceAsBuilder { nextVariable, aux } m =
  let
    initState = { nextVariable, constraints: mempty, aux }
    Tuple a s = un PlonkBuilder m initState
  in
    Tuple a
      ( Record.set (Proxy @"constraints")
          (map Rows (Array.fromFoldable (List.reverse s.constraints)))
          s
      )

reduceAsProver
  :: forall f a
   . PrimeField f
  => { nextVariable :: Variable
     , assignments :: Map Variable f
     }
  -> (forall m. PlonkReductionM m f => m a)
  -> Either
       EvaluationError
       ( Tuple
           a
           { nextVariable :: Variable
           , assignments :: Map Variable f
           }
       )
reduceAsProver s m = un PlonkProver m s

--------------------------------------------------------------------------------

-- `constraints` is accumulated as a reversed `List` (newest first):
-- `Cons` is O(1) with tail sharing, vs `Array.snoc`'s O(n) full
-- `slice()` copy → O(n²) over a reduction. Materialised forward
-- exactly once in `reduceAsBuilder` (O(m)).
type BuilderReductionState f =
  { constraints :: List (KimchiRow f)
  , nextVariable :: Variable
  , aux :: AuxState f
  }

-- | Hand-rolled pure state monad (replaces `State` from `transformers`).
-- | Reductions are per-constraint (a handful of binds), so plain
-- | function-composition binds are fine — no stack-safety machinery needed.
newtype PlonkBuilder f a = PlonkBuilder (BuilderReductionState f -> Tuple a (BuilderReductionState f))

derive instance Newtype (PlonkBuilder f a) _

instance Functor (PlonkBuilder f) where
  map f (PlonkBuilder g) = PlonkBuilder \s -> let Tuple a s' = g s in Tuple (f a) s'

instance Apply (PlonkBuilder f) where
  apply = ap

instance Applicative (PlonkBuilder f) where
  pure a = PlonkBuilder \s -> Tuple a s

instance Bind (PlonkBuilder f) where
  bind (PlonkBuilder g) f = PlonkBuilder \s ->
    let
      Tuple a s' = g s
    in
      un PlonkBuilder (f a) s'

instance Monad (PlonkBuilder f)

getsB :: forall f a. (BuilderReductionState f -> a) -> PlonkBuilder f a
getsB f = PlonkBuilder \s -> Tuple (f s) s

modifyB_ :: forall f. (BuilderReductionState f -> BuilderReductionState f) -> PlonkBuilder f Unit
modifyB_ f = PlonkBuilder \s -> Tuple unit (f s)

constraintToCoeffs
  :: forall f
   . PrimeField f
  => GenericPlonkConstraint f
  -> Array f
constraintToCoeffs gate =
  [ gate.cl, gate.cr, gate.co, gate.m, gate.c ]

finalizeGateQueue
  :: forall f r
   . PrimeField f
  => { queuedGenericGate :: Maybe (GenericPlonkConstraint f)
     | r
     }
  -> Maybe (Rows f)
finalizeGateQueue { queuedGenericGate } =
  map
    ( \gate ->
        let
          variables = gate.vl :< gate.vr :< gate.vo :< Vector.generate (const Nothing)
        in
          Rows { kind: GenericPlonkGate, coeffs: constraintToCoeffs gate, variables }

    )
    queuedGenericGate

-- Handle gate batching and wire placement for GenericPlonk gates
handleGateBatching
  :: forall f
   . PrimeField f
  => GenericPlonkConstraint f
  -> PlonkBuilder f (Maybe (KimchiRow f))
handleGateBatching newGate = do
  mqueued <- getsB (\{ aux: AuxState aux } -> aux.queuedGenericGate)
  case mqueued of
    Nothing -> do
      -- No queued gate, store this one for batching
      modifyB_ \s -> s
        { aux = over AuxState
            _ { queuedGenericGate = Just newGate }
            (s.aux)
        }

      pure Nothing
    Just queuedGate -> do
      -- clear the queue
      modifyB_ \s -> s
        { aux = over AuxState
            _ { queuedGenericGate = Nothing }
            (s.aux)
        }
      pure $ Just $ emitDoubleGateRow queuedGate newGate
  where
  -- OCaml puts the NEW gate first and the QUEUED gate second
  emitDoubleGateRow queued new_ =
    let
      vars = new_.vl :< new_.vr :< new_.vo :< queued.vl :< queued.vr :< queued.vo :< Vector.generate (const Nothing)
      coeffs = constraintToCoeffs new_ <> constraintToCoeffs queued

    in
      { kind: GenericPlonkGate, coeffs, variables: vars }

-- | Wire-state union-find ops for the builder, over the pure
-- | `Data.UnionFind` API.
findB :: forall f. Variable -> PlonkBuilder f Variable
findB x = do
  uf <- getsB (\{ aux: AuxState aux } -> aux.wireState.unionFind)
  let Tuple a uf' = UF.find x uf
  modifyB_ \s -> s
    { aux = over AuxState
        ( \st -> st
            { wireState = st.wireState
                { unionFind = uf'
                }
            }
        )
        s.aux
    }
  pure a

unionB :: forall f. Variable -> Variable -> PlonkBuilder f Unit
unionB x y = do
  uf <- getsB (\{ aux: AuxState aux } -> aux.wireState.unionFind)
  modifyB_ \s -> s
    { aux = over AuxState
        ( \st -> st
            { wireState = st.wireState
                { unionFind = UF.union x y uf
                }
            }
        )
        s.aux
    }

instance PrimeField f => PlonkReductionM (PlonkBuilder f) f where
  addGenericPlonkConstraint c = do
    mconstraint <- handleGateBatching c
    case mconstraint of
      Nothing -> pure unit
      Just c' -> modifyB_ \s ->
        s { constraints = Cons c' s.constraints }
  createInternalVariable _ = do
    nextVariable <- getsB _.nextVariable
    void $ findB nextVariable
    modifyB_ \s -> s
      { nextVariable = incrementVariable nextVariable
      , aux = over AuxState
          ( \st -> st
              { wireState = st.wireState
                  { internalVariables = Set.insert nextVariable st.wireState.internalVariables
                  }
              }
          )
          s.aux
      }
    pure nextVariable
  addEqualsConstraint c
    | c.cl == zero && c.cr == zero = pure unit
    | Just l <- c.vl, Just r <- c.vr, c.cl == c.cr = unionB l r
    -- Two-variable case: cl * l = cr * r where cl /= cr.
    -- OCaml only emits a generic constraint here — it does NOT touch cached_constants.
    -- Caching would be incorrect: l and r are not constants, they are variables
    -- related by l = (cr/cl) * r. Storing them in cachedConstants would corrupt
    -- later constant deduplication.
    | Just l <- c.vl, Just r <- c.vr =
        addGenericPlonkConstraint
          { vl: Just l
          , cl: c.cl
          , vr: Just r
          , cr: -c.cr
          , co: zero
          , vo: Nothing
          , m: zero
          , c: zero
          }
    | Just l <- c.vl, Nothing <- c.vr, c.cl /= zero = do
        ws <- getsB (\{ aux: AuxState aux } -> aux.wireState)
        let constVal = c.cr / c.cl
        case Map.lookup constVal ws.cachedConstants of
          Just cached -> unionB l cached
          Nothing -> do
            addGenericPlonkConstraint
              { vl: Just l
              , cl: c.cl
              , vr: Nothing
              , cr: zero
              , co: zero
              , vo: Nothing
              , m: zero
              , c: -c.cr
              }
            modifyB_ \s -> s
              { aux = over AuxState
                  ( \st -> st
                      { wireState = st.wireState
                          { cachedConstants = Map.insert constVal l st.wireState.cachedConstants
                          }
                      }
                  )
                  s.aux
              }
    | Just l <- c.vl, Nothing <- c.vr =
        addGenericPlonkConstraint { vl: Nothing, cl: zero, vr: Nothing, cr: zero, co: zero, vo: Nothing, m: zero, c: c.cr }
    | Nothing <- c.vl, Just r <- c.vr, c.cr /= zero = do
        ws <- getsB (\{ aux: AuxState aux } -> aux.wireState)
        let constVal = c.cl / c.cr
        case Map.lookup constVal ws.cachedConstants of
          Just cached -> unionB r cached
          Nothing -> do
            addGenericPlonkConstraint
              { vl: Nothing
              , cl: zero
              , vr: Just r
              , cr: c.cr
              , co: zero
              , vo: Nothing
              , m: zero
              , c: -c.cl
              }
            modifyB_ \s -> s
              { aux = over AuxState
                  ( \st -> st
                      { wireState = st.wireState { cachedConstants = Map.insert constVal r st.wireState.cachedConstants }
                      }
                  )
                  s.aux
              }
    | Nothing <- c.vl, Just r <- c.vr =
        addGenericPlonkConstraint { vl: Nothing, cl: zero, vr: Nothing, cr: zero, co: zero, vo: Nothing, m: zero, c: c.cl }
    | Nothing <- c.vl, Nothing <- c.vr, c.cl == c.cr = pure unit
    | otherwise = unsafeThrow $ "Contradiction: " <> show c.cl <> " ≠ " <> show c.cr

type ProverReductionState f =
  { nextVariable :: Variable
  , assignments :: Map Variable f
  }

-- | Hand-rolled fused state + error monad (replaces
-- | `ExceptT EvaluationError (State …)` from `transformers`).
newtype PlonkProver f a = PlonkProver (ProverReductionState f -> Either EvaluationError (Tuple a (ProverReductionState f)))

derive instance Newtype (PlonkProver f a) _

instance Functor (PlonkProver f) where
  map f (PlonkProver g) = PlonkProver \s -> g s <#> \(Tuple a s') -> Tuple (f a) s'

instance Apply (PlonkProver f) where
  apply = ap

instance Applicative (PlonkProver f) where
  pure a = PlonkProver \s -> Right (Tuple a s)

instance Bind (PlonkProver f) where
  bind (PlonkProver g) f = PlonkProver \s -> case g s of
    Left e -> Left e
    Right (Tuple a s') -> un PlonkProver (f a) s'

instance Monad (PlonkProver f)

instance (PrimeField f) => PlonkReductionM (PlonkProver f) f where
  addGenericPlonkConstraint _ = pure unit
  createInternalVariable e = PlonkProver \s ->
    let
      _lookup v = case Map.lookup v s.assignments of
        Nothing -> Left $ MissingVariable v
        Just a -> Right a
    in
      evalAffineExpression e _lookup <#> \a ->
        Tuple s.nextVariable
          { nextVariable: incrementVariable s.nextVariable
          , assignments: Map.insert s.nextVariable a s.assignments
          }
  addEqualsConstraint _ = pure unit