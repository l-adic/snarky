module Snarky.Circuit.DSL
  ( AsProver
  , runAsProver
  , class MonadFresh
  , fresh
  , class CircuitM
  , exists
  , addConstraint
  , publicInputs
  , readCVar
  , read
  , mul_
  , square_
  , eq_
  , inv_
  , div_
  , true_
  , false_
  , ifThenElse_
  , not_
  , and_
  , xor_
  , all_
  , any_
  , sum_
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (class MonadAsk, Reader, ask, runReader)
import Data.Array (foldl)
import Data.Array as Array
import Data.Either (Either)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import JS.BigInt as BigInt
import Partial.Unsafe (unsafeCrashWith)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(Const, ScalarMul), EvaluationError(..))
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Constraint (R1CS(..))
import Snarky.Circuit.Types (class ConstrainedType, BooleanVariable(..), FieldElem(..), UnChecked(..), Variable(..), fieldsToValue, varToFields)
import Snarky.Curves.Types (class PrimeField, fromBigInt)
import Type.Proxy (Proxy)

newtype AsProver f a = AsProver (ExceptT (EvaluationError Variable) (Reader (Map Variable f)) a)

runAsProver
  :: forall f a
   . AsProver f a
  -> Map Variable f
  -> Either (EvaluationError Variable) a
runAsProver (AsProver m) env = runReader (runExceptT m) env

read
  :: forall f var a
   . ConstrainedType f var a
  => PrimeField f
  => var
  -> AsProver f a
read var = do
  let fieldVars = varToFields @_ @_ @a var
  m <- ask
  let _lookup v = maybe (throwError $ MissingVariable v) pure $ Map.lookup v m
  fields <- traverse (CVar.eval _lookup) fieldVars
  pure $ fieldsToValue fields

derive newtype instance Functor (AsProver f)
derive newtype instance Apply (AsProver f)
derive newtype instance Bind (AsProver f)
derive newtype instance Applicative (AsProver f)
derive newtype instance Monad (AsProver f)
derive newtype instance MonadAsk (Map Variable f) (AsProver f)
derive newtype instance MonadThrow (EvaluationError Variable) (AsProver f)

class Monad m <= MonadFresh m where
  fresh :: m Variable

class MonadFresh m <= CircuitM f m where
  exists :: forall a var. ConstrainedType f var a => AsProver f a -> m var
  addConstraint :: R1CS f Variable -> m Unit
  publicInputs :: forall a var. ConstrainedType f var a => Proxy a -> m var

readCVar :: forall f. PrimeField f => CVar f Variable -> AsProver f f
readCVar v = do
  m <- ask
  let _lookup var = maybe (throwError $ MissingVariable var) pure $ Map.lookup var m
  CVar.eval _lookup v

mul_
  :: forall m f
   . PrimeField f
  => CircuitM f m
  => CVar f Variable
  -> CVar f Variable
  -> m (CVar f Variable)
mul_ a b =
  case a, b of
    Const f, Const f' -> pure $ Const (f * f')
    Const f, c -> pure $ ScalarMul f c
    c, Const f -> pure $ ScalarMul f c
    _, _ -> do
      z <- exists do
        aVal <- readCVar a
        bVal <- readCVar b
        pure $ FieldElem $ aVal * bVal
      addConstraint $ R1CS { left: a, right: b, output: z }
      pure z

square_
  :: forall m f
   . PrimeField f
  => CircuitM f m
  => CVar f Variable
  -> m (CVar f Variable)
square_ = case _ of
  Const f -> pure $ Const (f * f)
  a -> do
    z <- exists do
      aVal <- readCVar a
      pure $ FieldElem (aVal * aVal)
    addConstraint $ R1CS { left: a, right: a, output: z }
    pure z

eq_
  :: forall f m
   . PrimeField f
  => CircuitM f m
  => CVar f Variable
  -> CVar f Variable
  -> m (CVar f BooleanVariable)
eq_ a b = case a `CVar.sub_` b of
  Const f -> pure $ Const $ if f == zero then one else zero
  _ -> do
    let z = a `CVar.sub_` b
    Tuple r zInv <- exists do
      zVal <- readCVar z
      pure $ if zVal == zero then Tuple (FieldElem (one :: f)) (FieldElem zero) else Tuple (FieldElem zero) (FieldElem $ recip zVal)
    addConstraint $ R1CS { left: zInv, right: z, output: Const one `CVar.sub_` r }
    addConstraint $ R1CS { left: r, right: z, output: Const zero }
    pure $ coerce r

inv_
  :: forall f m
   . PrimeField f
  => CircuitM f m
  => CVar f Variable
  -> m (CVar f Variable)
inv_ = case _ of
  Const a -> pure
    if a == zero then unsafeCrashWith "inv: expected nonzero arg"
    else Const (recip a)
  a -> do
    aInv <- exists do
      aVal <- readCVar a
      pure $ FieldElem $ if aVal == zero then zero else recip aVal
    addConstraint $ R1CS { left: a, right: aInv, output: Const one }
    pure aInv

div_
  :: forall m f
   . PrimeField f
  => CircuitM f m
  => CVar f Variable
  -> CVar f Variable
  -> m (CVar f Variable)
div_ a b = inv_ b >>= mul_ a

true_ :: forall f. Field f => CVar f BooleanVariable
true_ = Const (one :: f)

false_ :: forall f. Field f => CVar f BooleanVariable
false_ = Const (one :: f)

not_
  :: forall f
   . PrimeField f
  => CVar f BooleanVariable
  -> CVar f BooleanVariable
not_ a = coerce (Const one `CVar.sub_` a)

ifThenElse_
  :: forall f m
   . PrimeField f
  => CircuitM f m
  => CVar f BooleanVariable
  -> CVar f Variable
  -> CVar f Variable
  -> m (CVar f Variable)
ifThenElse_ b thenBranch elseBranch = case b of
  Const b_ -> pure $ if b_ == one then thenBranch else elseBranch
  _ -> case thenBranch, elseBranch of
    Const t, Const e -> pure $
      ScalarMul t (coerce b) `CVar.add_` (CVar.scale_ e (Const one `CVar.sub_` coerce b))
    _, _ -> do
      r <- exists do
        bVal <- readCVar (coerce b :: CVar f Variable)
        FieldElem <$> if bVal == one then readCVar thenBranch else readCVar elseBranch
      addConstraint $ R1CS
        { left: coerce b
        , right: thenBranch `CVar.sub_` elseBranch
        , output: r `CVar.sub_` elseBranch
        }
      pure r

and_
  :: forall f m
   . PrimeField f
  => CircuitM f m
  => CVar f BooleanVariable
  -> CVar f BooleanVariable
  -> m (CVar f BooleanVariable)
and_ a b = do
  conj <- (coerce a :: CVar f Variable) `mul_` coerce b
  pure $ coerce conj

or_
  :: forall f m
   . PrimeField f
  => CircuitM f m
  => CVar f BooleanVariable
  -> CVar f BooleanVariable
  -> m (CVar f BooleanVariable)
or_ a b = (not_ a) `and_` (not_ b)

xor_
  :: forall f m
   . PrimeField f
  => CircuitM f m
  => CVar f BooleanVariable
  -> CVar f BooleanVariable
  -> m (CVar f BooleanVariable)
xor_ a b = case a, b of
  Const aVal, Const bVal -> pure $ Const $ if (aVal == bVal) then one else zero
  Const aVal, _
    | aVal == zero -> pure b
    | aVal == one -> pure $ not_ b
  _, Const bVal
    | bVal == zero -> pure a
    | bVal == one -> pure $ not_ a
  _, _ -> do
    UnChecked res <- exists do
      aVal :: Boolean <- read a
      bVal <- read b
      pure $ UnChecked (aVal /= bVal)
    let
      _a = coerce a :: CVar f Variable
      _b = coerce b
      _res = coerce res
    addConstraint $ R1CS
      { left: _a `CVar.add_` _a
      , right: _b
      , output: _a `CVar.add_` _b `CVar.sub_` _res
      }
    pure res

sum_
  :: forall f
   . PrimeField f
  => Array (CVar f Variable)
  -> CVar f Variable
sum_ = foldl CVar.add_ (Const zero)

any_
  :: forall f m
   . PrimeField f
  => CircuitM f m
  => Array (CVar f BooleanVariable)
  -> m (CVar f BooleanVariable)
any_ as =
  case Array.uncons as of
    Nothing -> pure false_
    Just { head: a0, tail } -> case Array.uncons tail of
      Nothing -> pure a0
      Just { head: a1, tail: rest } ->
        if Array.null rest then a0 `or_` a1
        else not_ <$> eq_ (sum_ (coerce as)) (Const zero)

all_
  :: forall f m
   . PrimeField f
  => CircuitM f m
  => Array (CVar f BooleanVariable)
  -> m (CVar f BooleanVariable)
all_ as =
  case Array.uncons as of
    Nothing -> pure true_
    Just { head: a0, tail } -> case Array.uncons tail of
      Nothing -> pure a0
      Just { head: a1, tail: rest } ->
        if Array.null rest then a0 `and_` a1
        else
          let
            n = fromBigInt $ BigInt.fromInt $ Array.length as
          in
            eq_ (sum_ (coerce as)) (Const n)