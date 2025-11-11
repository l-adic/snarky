module Snarky.Circuit.DSL
  ( AsProverT
  , AsProver
  , addConstraint
  , all_
  , and_
  , any_
  , class CircuitM
  , class MonadFresh
  , const_
  , div_
  , eq_
  , exists
  , false_
  , fresh
  , ifThenElse_
  , inv_
  , mul_
  , not_
  , or_
  , publicInputs
  , read
  , readCVar
  , runAsProver
  , runAsProverT
  , square_
  , sum_
  , true_
  , xor_
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow)
import Control.Monad.Except (class MonadTrans, ExceptT, lift, runExceptT, throwError)
import Control.Monad.Reader (class MonadAsk, ReaderT, ask, runReaderT)
import Data.Array (foldl)
import Data.Array as Array
import Data.Either (Either)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (un)
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

newtype AsProverT f m a = AsProverT (ExceptT (EvaluationError Variable) (ReaderT (Map Variable f) m) a)

runAsProverT
  :: forall f a m
   . Monad m
  => AsProverT f m a
  -> Map Variable f
  -> m (Either (EvaluationError Variable) a)
runAsProverT (AsProverT m) env = runReaderT (runExceptT m) env

type AsProver f = AsProverT f Identity

runAsProver
  :: forall f a
   . AsProver f a
  -> Map Variable f
  -> Either (EvaluationError Variable) a
runAsProver m e = un Identity $ runAsProverT m e

read
  :: forall f var a m
   . ConstrainedType f var a
  => PrimeField f
  => Monad m
  => var
  -> AsProverT f m a
read var = do
  let fieldVars = varToFields @_ @_ @a var
  m <- ask
  let _lookup v = maybe (throwError $ MissingVariable v) pure $ Map.lookup v m
  fields <- traverse (CVar.eval _lookup) fieldVars
  pure $ fieldsToValue fields

derive newtype instance Functor m => Functor (AsProverT f m)
derive newtype instance Monad m => Apply (AsProverT f m)
derive newtype instance Monad m => Bind (AsProverT f m)
derive newtype instance Monad m => Applicative (AsProverT f m)
derive newtype instance Monad m => Monad (AsProverT f m)
derive newtype instance Monad m => MonadAsk (Map Variable f) (AsProverT f m)
derive newtype instance Monad m => MonadThrow (EvaluationError Variable) (AsProverT f m)

instance MonadTrans (AsProverT f) where
  lift m = AsProverT $ lift $ lift m

class Monad m <= MonadFresh m where
  fresh :: m Variable

class (Monad n, MonadFresh m, PrimeField f) <= CircuitM f m n | m -> n where
  exists :: forall a var. ConstrainedType f var a => AsProverT f n a -> m var
  addConstraint :: R1CS f Variable -> m Unit
  publicInputs :: forall a var. ConstrainedType f var a => Proxy a -> m var

readCVar :: forall f m. PrimeField f => Monad m => CVar f Variable -> AsProverT f m f
readCVar v = do
  m <- ask
  let _lookup var = maybe (throwError $ MissingVariable var) pure $ Map.lookup var m
  CVar.eval _lookup v

mul_
  :: forall f m n
   . CircuitM f m n
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
  :: forall m f n
   . CircuitM f m n
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
  :: forall f m n
   . CircuitM f m n
  => CVar f Variable
  -> CVar f Variable
  -> m (CVar f BooleanVariable)
eq_ a b = case a `CVar.sub_` b of
  Const f -> pure $ Const $ if f == zero then one else zero
  _ -> do
    let z = a `CVar.sub_` b
    Tuple r zInv <- exists do
      zVal <- readCVar z
      pure $
        if zVal == zero then Tuple (FieldElem (one :: f)) (FieldElem zero)
        else Tuple (FieldElem zero) (FieldElem $ recip zVal)
    addConstraint $ R1CS { left: zInv, right: z, output: Const one `CVar.sub_` r }
    addConstraint $ R1CS { left: r, right: z, output: Const zero }
    pure $ coerce r

inv_
  :: forall f m n
   . CircuitM f m n
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

const_ :: forall f. PrimeField f => f -> CVar f Variable
const_ = Const

div_
  :: forall m f n
   . CircuitM f m n
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
  :: forall f m n
   . CircuitM f m n
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
  :: forall f m n
   . CircuitM f m n
  => CVar f BooleanVariable
  -> CVar f BooleanVariable
  -> m (CVar f BooleanVariable)
and_ a b = do
  conj <- mul_ (coerce a :: CVar f Variable) (coerce b)
  pure $ coerce conj

or_
  :: forall f m n
   . CircuitM f m n
  => CVar f BooleanVariable
  -> CVar f BooleanVariable
  -> m (CVar f BooleanVariable)
or_ a b = not_ <$> (not_ a) `and_` (not_ b)

xor_
  :: forall f m n
   . CircuitM f m n
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
  :: forall f m n
   . CircuitM f m n
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
  :: forall f m n
   . CircuitM f m n
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