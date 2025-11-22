module Snarky.Circuit.DSL.Monad
  ( AsProver
  , AsProverT
  , Snarky(..)
  , addConstraint
  , class CircuitM
  , class MonadFresh
  , exists
  , fresh
  , read
  , readCVar
  , runAsProver
  , runAsProverT
  , runSnarky
  , throwAsProver
  , not_
  , or_
  , and_
  , inv_
  , mul_
  , div_
  ) where

import Prelude

import Control.Apply (lift2)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Trans.Class (class MonadTrans, lift)
import Data.Either (Either)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (maybe)
import Data.Newtype (un)
import Data.Traversable (traverse)
import Partial.Unsafe (unsafeCrashWith)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(..), EvaluationError(..), add_, const_, sub_)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Constraint.Class (class R1CSSystem, r1cs)
import Snarky.Circuit.Types (class CheckedType, class CircuitType, Bool(..), F(..), Variable, fieldsToValue, varToFields)
import Snarky.Curves.Class (class PrimeField)

newtype AsProverT f m a = AsProverT (ExceptT (EvaluationError f Variable) (ReaderT (Map Variable f) m) a)

runAsProverT
  :: forall f a m
   . Monad m
  => AsProverT f m a
  -> Map Variable f
  -> m (Either (EvaluationError f Variable) a)
runAsProverT (AsProverT m) env = runReaderT (runExceptT m) env

type AsProver f = AsProverT f Identity

runAsProver
  :: forall f a
   . AsProver f a
  -> Map Variable f
  -> Either (EvaluationError f Variable) a
runAsProver m e = un Identity $ runAsProverT m e

readCVar :: forall f m. PrimeField f => Monad m => CVar f Variable -> AsProverT f m f
readCVar v = AsProverT do
  m <- ask
  let _lookup var = maybe (throwError $ MissingVariable var) pure $ Map.lookup var m
  CVar.eval _lookup v

read
  :: forall f var a m
   . CircuitType f a var
  => PrimeField f
  => Monad m
  => var
  -> AsProverT f m a
read var = AsProverT do
  let fieldVars = varToFields @f @a var
  m <- ask
  let _lookup v = maybe (throwError $ MissingVariable v) pure $ Map.lookup v m
  fields <- traverse (CVar.eval _lookup) fieldVars
  pure $ fieldsToValue fields

derive newtype instance Functor m => Functor (AsProverT f m)
derive newtype instance Monad m => Apply (AsProverT f m)
derive newtype instance Monad m => Bind (AsProverT f m)
derive newtype instance Monad m => Applicative (AsProverT f m)
derive newtype instance Monad m => Monad (AsProverT f m)

instance MonadTrans (AsProverT f) where
  lift m = AsProverT $ lift $ lift m

class Monad m <= MonadFresh m where
  fresh :: m Variable

newtype Snarky :: ((Type -> Type) -> (Type -> Type)) -> (Type -> Type) -> Type -> Type
newtype Snarky t m a = Snarky (t m a)

derive newtype instance (Functor (t m)) => Functor (Snarky t m)
derive newtype instance (Apply (t m)) => Apply (Snarky t m)
derive newtype instance (Applicative (t m)) => Applicative (Snarky t m)
derive newtype instance (Bind (t m)) => Bind (Snarky t m)
derive newtype instance (Monad (t m)) => Monad (Snarky t m)
derive newtype instance (MonadFresh (t m)) => MonadFresh (Snarky t m)
derive newtype instance (MonadTrans t) => MonadTrans (Snarky t)

runSnarky :: forall t m a. Snarky t m a -> t m a
runSnarky (Snarky m) = m

class (Monad m, MonadFresh (t m), PrimeField f, R1CSSystem (CVar f Variable) c) <= CircuitM f c t m | t -> c f, c -> f where
  exists :: forall a var. CheckedType var c => CircuitType f a var => AsProverT f m a -> Snarky t m var
  addConstraint :: c -> Snarky t m Unit

throwAsProver :: forall f m a. Monad m => EvaluationError f Variable -> AsProverT f m a
throwAsProver = AsProverT <<< throwError

instance (CircuitM f c t m) => Semigroup (Snarky t m (CVar f Variable)) where
  append a b = lift2 (<>) a b

instance (CircuitM f c t m) => Monoid (Snarky t m (CVar f Variable)) where
  mempty = pure mempty

instance (CircuitM f c t m) => Semiring (Snarky t m (CVar f Variable)) where
  one = pure $ const_ one
  zero = pure $ const_ zero
  add a b = lift2 add_ a b
  mul a b = join $ lift2 mul_ a b

instance (CircuitM f c t m) => Ring (Snarky t m (CVar f Variable)) where
  sub a b = sub_ <$> a <*> b

instance (CircuitM f c t m) => CommutativeRing (Snarky t m (CVar f Variable))

instance (CircuitM f c t m) => DivisionRing (Snarky t m (CVar f Variable)) where
  recip a = a >>= inv_

instance (CircuitM f c t m) => EuclideanRing (Snarky t m (CVar f Variable)) where
  degree _ = 1
  div a b = join $ lift2 div_ a b
  mod _ _ = pure $ const_ zero

instance (CircuitM f c t m) => HeytingAlgebra (Snarky t m (CVar f (Bool Variable))) where
  tt = pure $ const_ (one :: f)
  ff = pure $ const_ (zero :: f)
  not a = not_ <$> a
  conj a b = join $ lift2 and_ a b
  disj a b = join $ lift2 or_ a b
  implies a b = not a || b

not_
  :: forall f
   . PrimeField f
  => CVar f (Bool Variable)
  -> CVar f (Bool Variable)
not_ a = const_ one `CVar.sub_` a

or_
  :: forall f c t m
   . CircuitM f c t m
  => CVar f (Bool Variable)
  -> CVar f (Bool Variable)
  -> Snarky t m (CVar f (Bool Variable))
or_ a b = not_ <$> (not_ a) `and_` (not_ b)

and_
  :: forall f c t m
   . CircuitM f c t m
  => CVar f (Bool Variable)
  -> CVar f (Bool Variable)
  -> Snarky t m (CVar f (Bool Variable))
and_ a b = do
  coerce <$> mul_ (coerce a :: CVar f Variable) (coerce b)

inv_
  :: forall f c t m
   . CircuitM f c t m
  => CVar f Variable
  -> Snarky t m (CVar f Variable)
inv_ = case _ of
  Const a -> pure
    if a == zero then unsafeCrashWith "inv: expected nonzero arg"
    else Const (recip a)
  a -> do
    aInv <- exists do
      aVal <- readCVar a
      if aVal == zero then throwAsProver $ DivisionByZero { numerator: Const one, denominator: a }
      else pure $ F $ if aVal == zero then zero else recip aVal
    addConstraint $ r1cs { left: a, right: aInv, output: Const one }
    pure aInv

mul_
  :: forall f c t m
   . CircuitM f c t m
  => CVar f Variable
  -> CVar f Variable
  -> Snarky t m (CVar f Variable)
mul_ a b =
  case a, b of
    Const f, Const f' -> pure $ Const (f * f')
    Const f, c -> pure $ ScalarMul f c
    c, Const f -> pure $ ScalarMul f c
    _, _ -> do
      z <- exists do
        aVal <- readCVar a
        bVal <- readCVar b
        pure $ F $ aVal * bVal
      addConstraint $ r1cs { left: a, right: b, output: z }
      pure z

div_
  :: forall f c t m
   . CircuitM f c t m
  => CVar f Variable
  -> CVar f Variable
  -> Snarky t m (CVar f Variable)
div_ a b = mul_ a =<< inv_ b