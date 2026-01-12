module Snarky.Circuit.DSL.Monad
  ( AsProver
  , AsProverT
  , Snarky(..)
  , class ConstraintM
  , addConstraint'
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
import Data.HeytingAlgebra (ff, implies, tt)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (un)
import Data.Traversable (traverse)
import Partial.Unsafe (unsafeCrashWith)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(..), EvaluationError(..), Variable, add_, const_, sub_)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Types (class CheckedType, class CircuitType, Bool(..), BoolVar, F(..), FVar, fieldsToValue, varToFields)
import Snarky.Constraint.Basic (class BasicSystem, r1cs)
import Snarky.Curves.Class (class PrimeField)

class ConstraintM t c where
  addConstraint' :: forall m. Monad m => c -> t m Unit

addConstraint :: forall f c t m. CircuitM f c t m => c -> Snarky c t m Unit
addConstraint c = Snarky $ addConstraint' c

--------------------------------------------------------------------------------
newtype AsProverT f m a = AsProverT (ExceptT EvaluationError (ReaderT (Map Variable f) m) a)

runAsProverT
  :: forall f a m
   . Monad m
  => AsProverT f m a
  -> Map Variable f
  -> m (Either EvaluationError a)
runAsProverT (AsProverT m) env = runReaderT (runExceptT m) env

type AsProver f = AsProverT f Identity

runAsProver
  :: forall f a
   . AsProver f a
  -> Map Variable f
  -> Either EvaluationError a
runAsProver m e = un Identity $ runAsProverT m e

readCVar :: forall f m. PrimeField f => Monad m => FVar f -> AsProverT f m (F f)
readCVar v = AsProverT do
  m <- ask
  let _lookup var = maybe (throwError $ MissingVariable var) pure $ Map.lookup var m
  F <$> CVar.eval _lookup v

read
  :: forall f var @a m
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

instance (Monad m, Semigroup a) => Semigroup (AsProverT f m a) where
  append a b = lift2 (<>) a b

instance (Monad m, Monoid a) => Monoid (AsProverT f m a) where
  mempty = pure mempty

instance (Monad m, Semiring a) => Semiring (AsProverT f m a) where
  one = pure one
  zero = pure zero
  add = lift2 add
  mul = lift2 mul

instance (Monad m, Ring a) => Ring (AsProverT f m a) where
  sub = lift2 sub

instance (Monad m, CommutativeRing a) => CommutativeRing (AsProverT f m a)

instance (Monad m, DivisionRing a) => DivisionRing (AsProverT f m a) where
  recip = map recip

instance (Monad m, EuclideanRing a) => EuclideanRing (AsProverT f m a) where
  degree _ = 1
  div = lift2 div
  mod _ _ = pure zero

instance (Monad m) => HeytingAlgebra (AsProverT f m Boolean) where
  tt = pure tt
  ff = pure ff
  not = map not
  conj = lift2 conj
  disj = lift2 disj
  implies = lift2 implies

--------------------------------------------------------------------------------

class Monad m <= MonadFresh m where
  fresh :: m Variable

newtype Snarky :: Type -> ((Type -> Type) -> (Type -> Type)) -> (Type -> Type) -> Type -> Type
newtype Snarky c t m a = Snarky (t m a)

derive newtype instance (Functor (t m)) => Functor (Snarky c t m)
derive newtype instance (Apply (t m)) => Apply (Snarky c t m)
derive newtype instance (Applicative (t m)) => Applicative (Snarky c t m)
derive newtype instance (Bind (t m)) => Bind (Snarky c t m)
derive newtype instance (Monad (t m)) => Monad (Snarky c t m)
derive newtype instance (MonadFresh (t m)) => MonadFresh (Snarky c t m)
derive newtype instance (MonadTrans t) => MonadTrans (Snarky c t)

runSnarky :: forall c t m a. Snarky c t m a -> t m a
runSnarky (Snarky m) = m

class (Monad m, MonadFresh (t m), BasicSystem f c, ConstraintM t c) <= CircuitM f c t m | t -> f, c -> f where
  exists :: forall a var. CheckedType var c => CircuitType f a var => AsProverT f m a -> Snarky c t m var

throwAsProver :: forall f m a. Monad m => EvaluationError -> AsProverT f m a
throwAsProver = AsProverT <<< throwError

--------------------------------------------------------------------------------

instance (CircuitM f c t m) => Semigroup (Snarky c t m (FVar f)) where
  append a b = lift2 (<>) a b

instance (CircuitM f c t m) => Monoid (Snarky c t m (FVar f)) where
  mempty = pure mempty

instance (CircuitM f c t m) => Semiring (Snarky c t m (FVar f)) where
  one = pure $ const_ one
  zero = pure $ const_ zero
  add a b = lift2 add_ a b
  mul a b = join $ lift2 mul_ a b

instance (CircuitM f c t m) => Ring (Snarky c t m (FVar f)) where
  sub a b = sub_ <$> a <*> b

instance (CircuitM f c t m) => CommutativeRing (Snarky c t m (FVar f))

instance (CircuitM f c t m) => DivisionRing (Snarky c t m (FVar f)) where
  recip a = a >>= inv_

instance (CircuitM f c t m) => EuclideanRing (Snarky c t m (FVar f)) where
  degree _ = 1
  div a b = join $ lift2 div_ a b
  mod _ _ = pure $ const_ zero

instance (CircuitM f c t m) => HeytingAlgebra (Snarky c t m (BoolVar f)) where
  tt = pure $ const_ (one :: f)
  ff = pure $ const_ (zero :: f)
  not a = not_ <$> a
  conj a b = join $ lift2 and_ a b
  disj a b = join $ lift2 or_ a b
  implies a b = not a || b

not_
  :: forall f
   . PrimeField f
  => BoolVar f
  -> BoolVar f
not_ a = const_ one `CVar.sub_` a

or_
  :: forall f c t m
   . CircuitM f c t m
  => BoolVar f
  -> BoolVar f
  -> Snarky c t m (BoolVar f)
or_ a b = not_ <$> (not_ a) `and_` (not_ b)

and_
  :: forall f c t m
   . CircuitM f c t m
  => BoolVar f
  -> BoolVar f
  -> Snarky c t m (BoolVar f)
and_ a b = do
  coerce <$> mul_ (coerce a :: FVar f) (coerce b)

inv_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> Snarky c t m (FVar f)
inv_ = case _ of
  Const a -> pure
    if a == zero then unsafeCrashWith "inv: expected nonzero arg"
    else Const (recip a)
  a -> do
    aInv <- exists do
      aVal <- readCVar a
      if aVal == zero then throwAsProver $
        DivisionByZero
          { context: "inv"
          , expression: Nothing
          }
      else pure $ if aVal == zero then zero else recip aVal
    addConstraint $ r1cs { left: a, right: aInv, output: Const one }
    pure aInv

mul_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> FVar f
  -> Snarky c t m (FVar f)
mul_ a b =
  case a, b of
    Const f, Const f' -> pure $ Const (f * f')
    Const f, c -> pure $ ScalarMul f c
    c, Const f -> pure $ ScalarMul f c
    _, _ -> do
      z <- exists do
        aVal <- readCVar a
        bVal <- readCVar b
        pure $ aVal * bVal
      addConstraint $ r1cs { left: a, right: b, output: z }
      pure z

div_
  :: forall f c t m
   . CircuitM f c t m
  => FVar f
  -> FVar f
  -> Snarky c t m (FVar f)
div_ a b = mul_ a =<< inv_ b