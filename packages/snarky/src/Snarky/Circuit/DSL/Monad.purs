-- | The circuit monad and core DSL operations.
-- |
-- | This module provides the `Snarky` monad for building circuits and the
-- | `AsProverT` monad for witness computation during proving.
-- |
-- | ## Circuit Construction
-- |
-- | The `Snarky c t m a` monad is where circuits are built:
-- |
-- | ```purescript
-- | -- Multiply two field elements (introduces R1CS constraint)
-- | multiply :: forall f c t m. CircuitM f c t m => FVar f -> FVar f -> Snarky c t m (FVar f)
-- | multiply a b = mul_ a b
-- | ```
-- |
-- | ## Witness Computation
-- |
-- | The `exists` function introduces new variables with prover-side computation:
-- |
-- | ```purescript
-- | -- Compute inverse with witness
-- | inverse :: forall f c t m. CircuitM f c t m => FVar f -> Snarky c t m (FVar f)
-- | inverse a = do
-- |   aInv <- exists (recip <$> readCVar a)  -- Prover computes 1/a
-- |   addConstraint $ r1cs { left: a, right: aInv, output: const_ one }
-- |   pure aInv
-- | ```
-- |
-- | ## Key Operations
-- |
-- | - `exists`: Introduce witness variable with prover computation
-- | - `addConstraint`: Add constraint to the circuit
-- | - `mul_`, `div_`, `inv_`: Field arithmetic (create constraints)
-- | - `and_`, `or_`, `not_`: Boolean logic
-- | - `read`, `readCVar`: Evaluate variables in prover context
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
  --
  , class CheckedType
  , check
  , genericCheck
  --
  , class GCheckedType
  , gCheck
  , class RCheckedType
  , rCheck
  , class WithLabel
  , withLabel
  , label
  ) where

import Prelude

import Control.Apply (lift2)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Trans.Class (class MonadTrans, lift)
import Data.Either (Either)
import Data.Generic.Rep (class Generic, Argument(..), Constructor(..), NoArguments, Product(..), from)
import Data.HeytingAlgebra (ff, implies, tt)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, un, unwrap, wrap)
import Data.Symbol (class IsSymbol)
import Data.Traversable (traverse, traverse_)
import Data.Tuple (Tuple)
import Data.Vector (Vector)
import Effect.Exception.Unsafe (unsafeThrow)
import Prim.Row as Row
import Prim.RowList (class RowToList)
import Prim.RowList as RL
import Record as Record
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(..), EvaluationError(..), Variable, add_, const_, sub_)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Types (class CircuitType, Bool(..), BoolVar, F(..), FVar, UnChecked, fieldsToValue, varToFields)
import Snarky.Constraint.Basic (class BasicSystem, boolean, r1cs)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

class ConstraintM t c where
  addConstraint' :: forall m. Monad m => c -> t m Unit

addConstraint :: forall f c t m. CircuitM f c t m => c -> Snarky c t m Unit
addConstraint c = Snarky $ addConstraint' c

--------------------------------------------------------------------------------

-- | Prover-side computation monad. Runs with access to variable assignments,
-- | used as the argument to `exists` to compute witness values.
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

-- | The circuit-building monad.
-- |
-- | Type parameters:
-- | - `c`: Constraint type (e.g., `Basic f` or backend-specific)
-- | - `t`: Monad transformer injected by the backend (e.g., `CircuitBuilderT` or `ProverT`)
-- | - `m`: Base monad
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

-- | The main circuit monad type class. Backends implement this to provide
-- | `exists`, which introduces witness variables with prover-side computation.
-- | The functional dependencies ensure the field type is determined by either
-- | the transformer `t` or the constraint type `c`.
class (Monad m, MonadFresh (t m), BasicSystem f c, ConstraintM t c, WithLabel t) <= CircuitM f c t m | t -> f, c -> f where
  exists :: forall a var. CircuitType f a var => CheckedType f c var => ConstraintM t c => AsProverT f m a -> Snarky c t m var

throwAsProver :: forall f m a. Monad m => EvaluationError -> AsProverT f m a
throwAsProver = AsProverT <<< throwError

--------------------------------------------------------------------------------

instance (CircuitM f c t m) => Semigroup (Snarky c t m (FVar f)) where
  append a b = lift2 (<>) a b

else instance (Semigroup (Snarky c t m a), Newtype s a, Functor (Snarky c t m)) => Semigroup (Snarky c t m s) where
  append x y = map wrap (append (map unwrap x) (map unwrap y))

instance (CircuitM f c t m) => Monoid (Snarky c t m (FVar f)) where
  mempty = pure mempty

else instance (Monoid (Snarky c t m a), Newtype s a, Functor (Snarky c t m), Semigroup (Snarky c t m s)) => Monoid (Snarky c t m s) where
  mempty = map wrap mempty

instance (CircuitM f c t m) => Semiring (Snarky c t m (FVar f)) where
  one = pure $ const_ one
  zero = pure $ const_ zero
  add a b = lift2 add_ a b
  mul a b = join $ lift2 mul_ a b

else instance (Semiring (Snarky c t m a), Newtype s a, Functor (Snarky c t m)) => Semiring (Snarky c t m s) where
  one = map wrap one
  zero = map wrap zero
  add x y = map wrap (add (map unwrap x) (map unwrap y))
  mul x y = map wrap (mul (map unwrap x) (map unwrap y))

instance (CircuitM f c t m) => Ring (Snarky c t m (FVar f)) where
  sub a b = sub_ <$> a <*> b

else instance (Ring (Snarky c t m a), Newtype s a, Functor (Snarky c t m), Semiring (Snarky c t m s)) => Ring (Snarky c t m s) where
  sub x y = map wrap (sub (map unwrap x) (map unwrap y))

instance (CircuitM f c t m) => CommutativeRing (Snarky c t m (FVar f))

else instance (CommutativeRing (Snarky c t m a), Newtype s a, Ring (Snarky c t m s)) => CommutativeRing (Snarky c t m s)

instance (CircuitM f c t m) => DivisionRing (Snarky c t m (FVar f)) where
  recip a = a >>= inv_

else instance (DivisionRing (Snarky c t m a), Newtype s a, Functor (Snarky c t m), Ring (Snarky c t m s)) => DivisionRing (Snarky c t m s) where
  recip x = map wrap (recip (map unwrap x))

instance (CircuitM f c t m) => EuclideanRing (Snarky c t m (FVar f)) where
  degree _ = 1
  div a b = join $ lift2 div_ a b
  mod _ _ = pure $ const_ zero

else instance (EuclideanRing (Snarky c t m a), Newtype s a, Functor (Snarky c t m), CommutativeRing (Snarky c t m s)) => EuclideanRing (Snarky c t m s) where
  degree _ = 1
  div x y = map wrap (div (map unwrap x) (map unwrap y))
  mod x y = map wrap (mod (map unwrap x) (map unwrap y))

instance (CircuitM f c t m) => HeytingAlgebra (Snarky c t m (BoolVar f)) where
  tt = pure $ const_ (one :: f)
  ff = pure $ const_ (zero :: f)
  not a = not_ <$> a
  conj a b = join $ lift2 and_ a b
  disj a b = join $ lift2 or_ a b
  implies a b = not a || b

else instance (HeytingAlgebra (Snarky c t m a), Newtype s a, Functor (Snarky c t m)) => HeytingAlgebra (Snarky c t m s) where
  tt = map wrap tt
  ff = map wrap ff
  not x = map wrap (not (map unwrap x))
  conj x y = map wrap (conj (map unwrap x) (map unwrap y))
  disj x y = map wrap (disj (map unwrap x) (map unwrap y))
  implies x y = map wrap (implies (map unwrap x) (map unwrap y))

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
    if a == zero then unsafeThrow "inv: expected nonzero arg"
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

--------------------------------------------------------------------------------

-- | Defines what constraints are added when a variable type is introduced via `exists`.
-- | For example, `BoolVar` adds a boolean constraint; `FVar` adds nothing.
-- | Use `UnChecked` wrapper to skip checks when constraints are guaranteed elsewhere.
class CheckedType f c var | c -> f, var -> f where
  check
    :: forall t m
     . CircuitM f c t m
    => var
    -> Snarky c t m Unit

instance CheckedType f c Unit where
  check _ = pure mempty

instance CheckedType f c (FVar f) where
  check _ = pure mempty

instance BasicSystem f c => CheckedType f c (BoolVar f) where
  check var = Snarky $ addConstraint' @_ @c $ boolean (coerce var :: FVar f)

instance (CheckedType f c avar, CheckedType f c bvar) => CheckedType f c (Tuple avar bvar) where
  check = genericCheck

instance CheckedType f c (UnChecked var) where
  check _ = pure mempty

instance CheckedType f c var => CheckedType f c (Vector n var) where
  check var = traverse_ check var

instance (RowToList var rlvar, RCheckedType f c rlvar var) => CheckedType f c (Record var) where
  check x = rCheck (Proxy @rlvar) x

class GCheckedType f c var | c -> f, var -> f where
  gCheck
    :: forall t m
     . CircuitM f c t m
    => var
    -> Snarky c t m Unit

instance GCheckedType f c NoArguments where
  gCheck _ = pure mempty

instance CheckedType f c a => GCheckedType f c (Argument a) where
  gCheck (Argument a) = check a

instance (GCheckedType f c avar, GCheckedType f c bvar) => GCheckedType f c (Product avar bvar) where
  gCheck (Product a b) = lift2 (<>) (gCheck a) (gCheck b)

instance GCheckedType f c var => GCheckedType f c (Constructor name var) where
  gCheck (Constructor a) = gCheck a

genericCheck
  :: forall var rep f c t m
   . Generic var rep
  => CircuitM f c t m
  => GCheckedType f c rep
  => var
  -> Snarky c t m Unit
genericCheck var = gCheck $ from var

class RCheckedType :: forall k. Type -> Type -> k -> Row Type -> Constraint
class RCheckedType f c rlvar var | rlvar -> var where
  rCheck
    :: forall t m
     . CircuitM f c t m
    => Proxy rlvar
    -> Record var
    -> Snarky c t m Unit

instance RCheckedType f c RL.Nil () where
  rCheck _ _ = pure mempty

instance
  ( IsSymbol s
  , Row.Cons s avar restvars vars
  , Row.Lacks s restvars
  , CheckedType f c avar
  , RCheckedType f c tailvars restvars
  ) =>
  RCheckedType f c (RL.Cons s avar tailvars) vars where
  rCheck _ r = do
    afs <- check $ Record.get (Proxy @s) r
    asfs <- rCheck (Proxy @tailvars) $ Record.delete (Proxy @s) r
    pure $ afs <> asfs

--------------------------------------------------------------------------------

-- | Label a block of circuit code for debugging. When the debugger catches an
-- | error inside a labeled block, it wraps it with `WithContext`.
-- | No-op for ProverT and CircuitBuilderT.
class WithLabel :: forall k. ((Type -> Type) -> k -> Type) -> Constraint
class WithLabel t where
  withLabel :: forall m a. Monad m => String -> t m a -> t m a

label :: forall c t m a. WithLabel t => Monad m => String -> Snarky c t m a -> Snarky c t m a
label s (Snarky a) = Snarky (withLabel s a)
