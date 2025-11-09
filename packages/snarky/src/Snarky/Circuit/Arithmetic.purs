module Snarky.Circuit.Constraint where

import Prelude

import Control.Monad.Reader (class MonadAsk, Reader, ask)
import Control.Monad.State (class MonadState, class MonadTrans, StateT, evalStateT)
import Data.Array (foldMap, foldl, uncons)
import Data.Array as Array
import Data.Bifunctor (class Bifunctor)
import Data.Foldable (class Foldable, foldM)
import Data.Maybe (Maybe(..), fromJust)
import Data.Monoid.Conj (Conj(..))
import Data.Newtype (class Newtype, un)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Safe.Coerce (coerce)
import Snarky.Circuit.Affine (AffineCircuit(..), subtract)
import Snarky.Circuit.Affine as AffineCircuit
import Type.Proxy (Proxy(..))

data Gate f i
  = R1CS
      { left :: AffineCircuit f i
      , right :: AffineCircuit f i
      , output :: AffineCircuit f i
      }
  | BooleanGate (AffineCircuit f i)

derive instance Functor (Gate f)
derive instance Foldable (Gate f)
derive instance Traversable (Gate f)
derive instance Bifunctor Gate

-- | Evaluate a single gate
eval
  :: forall f i vars
   . Field f
  => Eq f
  => Show f
  => Show i
  => (i -> vars -> Maybe f)
  -> vars
  -> Gate f i
  -> Boolean
eval lookup vars gate =
  case gate of
    R1CS { left, right, output } ->
      let
        lval = AffineCircuit.eval lookup vars left
        rval = AffineCircuit.eval lookup vars right
        oval = AffineCircuit.eval lookup vars output
      in
        lval * rval == oval
    BooleanGate i ->
      let
        inp = AffineCircuit.eval lookup vars i
      in
        inp == zero || inp == one

newtype ArithCircuit f i = ArithCircuit (Array (Gate f i))

-- | Evaluate an arithmetic circuit on a given environment containing
-- the inputs. Outputs the entire environment (outputs, intermediate
-- values and inputs).
evalArithCircuit
  :: forall i f vars
   . Field f
  => Eq f
  => Show f
  => Show i
  => (i -> vars -> Maybe f)
  -> ArithCircuit f i
  -> vars
  -> Boolean
evalArithCircuit _lookupVar (ArithCircuit gates) vars =
  un Conj $ foldMap (Conj <<< eval _lookupVar vars) gates

type CircuitEnv f =
  { nextVar :: Int
  , constraints :: Array (Gate f Variable)
  }

data ProverError
  = MissingVariable Variable
  | EvaluationException String

newtype Variable = Variable Int

derive newtype instance Eq Variable
derive newtype instance Show Variable
derive newtype instance Ord Variable

newtype BooleanVariable = BooleanVariable Variable

derive newtype instance Eq BooleanVariable
derive newtype instance Show BooleanVariable
derive newtype instance Ord BooleanVariable
derive instance Newtype BooleanVariable _

newtype CircuitT f m a = CircuitT (StateT (CircuitEnv f) m a)

derive newtype instance Functor m => Functor (CircuitT f m)
derive newtype instance Monad m => Apply (CircuitT f m)
derive newtype instance Monad m => Bind (CircuitT f m)
derive newtype instance Monad m => Applicative (CircuitT f m)
derive newtype instance Monad m => Monad (CircuitT f m)
derive newtype instance Monad m => MonadState (CircuitEnv f) (CircuitT f m)
derive newtype instance MonadTrans (CircuitT f)

runCircuitT :: forall f m a. Functor m => CircuitEnv f -> CircuitT f m a -> m a
runCircuitT env (CircuitT t) = evalStateT t env

class ConstrainedType f var a where
  valueToFields :: a -> Array f
  fieldsToValue :: Array f -> a
  varToFields :: var -> Array (AffineCircuit f Variable)
  fieldsToVar :: Array (AffineCircuit f Variable) -> var
  sizeInFields :: Proxy a -> Int
  check :: var -> Array (Gate f Variable)

newtype AsProver f a = AsProver (Reader (AffineCircuit f Variable -> f) a)

derive newtype instance Functor (AsProver f)
derive newtype instance Apply (AsProver f)
derive newtype instance Bind (AsProver f)
derive newtype instance Applicative (AsProver f)
derive newtype instance Monad (AsProver f)
derive newtype instance MonadAsk (AffineCircuit f Variable -> f) (AsProver f)

readVar :: forall f. AffineCircuit f Variable -> AsProver f f
readVar v = do
  lookup <- ask
  pure $ lookup v

read
  :: forall f var a
   . ConstrainedType f var a
  => var
  -> AsProver f a
read var = do
  let fieldVars = varToFields @f @var @a var
  fields <- traverse readVar fieldVars
  pure $ fieldsToValue @f @var @a fields

class (Monad m) <= CircuitBuilderM f m where
  exists :: forall a var. (ConstrainedType f var a => AsProver f a) -> m var
  addConstraint :: Gate f Variable -> m Unit

instance ConstrainedType f (AffineCircuit f Variable) f where
  valueToFields = Array.singleton
  fieldsToValue a = unsafePartial fromJust $ Array.head a
  varToFields = Array.singleton
  fieldsToVar a = unsafePartial fromJust $ Array.head a
  sizeInFields _ = 1
  check _ = mempty

instance (ConstrainedType f avar a, ConstrainedType f bvar b) => ConstrainedType f (Tuple avar bvar) (Tuple a b) where
  valueToFields (Tuple a b) = valueToFields @f @avar @a a <> valueToFields @f @bvar @b b
  fieldsToValue fs =
    let
      { before: as, after: bs } = Array.splitAt (sizeInFields @f @avar (Proxy @a)) fs
    in
      Tuple (fieldsToValue @f @avar @a as) (fieldsToValue @f @bvar @b bs)
  varToFields (Tuple av bv) = varToFields @f @avar @a av <> varToFields @f @bvar @b bv
  fieldsToVar vs =
    let
      { before: avs, after: bvs } = Array.splitAt (sizeInFields @f @avar (Proxy @a)) vs
    in
      Tuple (fieldsToVar @f @avar @a avs) (fieldsToVar @f @bvar @b bvs)
  sizeInFields _ = sizeInFields @f @avar @a (Proxy @a) + sizeInFields @f @bvar @b (Proxy @b)
  check (Tuple a b) = check @f @avar @a a <> check @f @bvar @b b

mul_
  :: forall m f
   . Field f
  => CircuitBuilderM f m
  => AffineCircuit f Variable
  -> AffineCircuit f Variable
  -> m (AffineCircuit f Variable)
mul_ a b =
  case a, b of
    Const f, Const f' -> pure $ Const (f * f')
    Const f, c -> pure $ ScalarMul f c
    c, Const f -> pure $ ScalarMul f c
    _, _ -> do
      z <- exists $ (*) <$> (readVar a) <*> (readVar b)
      addConstraint $ R1CS { left: a, right: b, output: z }
      pure z

eq_
  :: forall f m
   . Field f
  => Eq f
  => CircuitBuilderM f m
  => AffineCircuit f Variable
  -> AffineCircuit f Variable
  -> m (AffineCircuit f BooleanVariable)
eq_ a b = case a `subtract` b of
  Const f -> pure $ Const $ if f == zero then one else zero
  _ -> do
    let z = a `subtract` b
    Tuple r zInv <- exists do
      zVal <- readVar z
      pure $ if zVal == zero then Tuple (one :: f) zero else Tuple zero (recip zVal)
    addConstraint $ R1CS { left: zInv, right: z, output: Const one `subtract` r }
    addConstraint $ R1CS { left: r, right: z, output: Const zero }
    pure $ coerce r

inv_
  :: forall f m
   . Field f
  => Eq f
  => CircuitBuilderM f m
  => AffineCircuit f Variable
  -> m (AffineCircuit f Variable)
inv_ = case _ of
  Const a -> pure
    if a == zero then unsafeCrashWith "inv: expected nonzero arg"
    else Const (recip a)
  a -> do
    aInv <- exists
      ( readVar a $> \aVal ->
          if aVal == zero @f then zero else recip aVal
      )
    addConstraint $ R1CS { left: a, right: aInv, output: Const one }
    pure aInv

div_
  :: forall m f
   . Field f
  => Eq f
  => CircuitBuilderM f m
  => AffineCircuit f Variable
  -> AffineCircuit f Variable
  -> m (AffineCircuit f Variable)
div_ a b = inv_ b >>= mul_ a

instance (Eq f, Field f) => ConstrainedType f (AffineCircuit f BooleanVariable) Boolean where
  valueToFields b = Array.singleton $ if b then one @f else zero
  fieldsToValue a =
    let
      b = unsafePartial fromJust $ Array.head a
    in
      b == one
  varToFields var = Array.singleton $ coerce var
  fieldsToVar a = coerce $ unsafePartial fromJust $ Array.head a
  sizeInFields _ = 1
  check var = Array.singleton $ BooleanGate (coerce var)

newtype UnChecked var = UnChecked var

derive instance Newtype (UnChecked var) _

unchecked :: forall f var. AffineCircuit f (UnChecked var) -> AffineCircuit f var
unchecked = coerce

true_ :: forall f. Field f => AffineCircuit f BooleanVariable
true_ = Const (one :: f)

false_ :: forall f. Field f => AffineCircuit f BooleanVariable
false_ = Const (one :: f)

not_
  :: forall f
   . Field f
  => Eq f
  => AffineCircuit f BooleanVariable
  -> AffineCircuit f BooleanVariable
not_ a = coerce (Const one `subtract` a)

ifThenElse_
  :: forall f m
   . Field f
  => Eq f
  => CircuitBuilderM f m
  => AffineCircuit f BooleanVariable
  -> AffineCircuit f Variable
  -> AffineCircuit f Variable
  -> m (AffineCircuit f Variable)
ifThenElse_ b thenBranch elseBranch = case b of
  Const b_ -> pure $ if b_ == one then thenBranch else elseBranch
  _ -> case thenBranch, elseBranch of
    Const t, Const e -> pure $
      ScalarMul t (coerce b) `Add` (ScalarMul e (Const one `subtract` coerce b))
    _, _ -> do
      r <- exists
        ( readVar (coerce b :: AffineCircuit f Variable) $> \bVal ->
            if bVal == one @f then thenBranch else elseBranch
        )
      addConstraint $ R1CS
        { left: coerce b
        , right: thenBranch `subtract` elseBranch
        , output: r `subtract` elseBranch
        }
      pure r

and_
  :: forall f m
   . Field f
  => Eq f
  => CircuitBuilderM f m
  => AffineCircuit f BooleanVariable
  -> AffineCircuit f BooleanVariable
  -> m (AffineCircuit f BooleanVariable)
and_ a b = do
  conj <- (coerce a :: AffineCircuit f Variable) `mul_` coerce b
  pure $ coerce conj

or_
  :: forall f m
   . Field f
  => Eq f
  => CircuitBuilderM f m
  => AffineCircuit f BooleanVariable
  -> AffineCircuit f BooleanVariable
  -> m (AffineCircuit f BooleanVariable)
or_ a b = (not_ a) `and_` (not_ b)

instance ConstrainedType f var a => ConstrainedType f (UnChecked var) a where
  valueToFields b = valueToFields @f @var @a b
  fieldsToValue a = fieldsToValue @f @var @a a
  varToFields (UnChecked var) = varToFields @f @var @a var
  fieldsToVar a = UnChecked $ fieldsToVar @f @var @a a
  sizeInFields _ = sizeInFields @f @var @a (Proxy @a)
  check _ = mempty

xor_
  :: forall f m
   . Field f
  => Eq f
  => CircuitBuilderM f m
  => AffineCircuit f BooleanVariable
  -> AffineCircuit f BooleanVariable
  -> m (AffineCircuit f BooleanVariable)
xor_ a b = case a, b of
  Const aVal, Const bVal -> pure $ Const $ if (aVal == bVal) then one else zero
  Const aVal, _
    | aVal == zero -> pure b
    | aVal == one -> pure $ not_ b
  _, Const bVal
    | bVal == zero -> pure a
    | bVal == one -> pure $ not_ a
  _, _ -> do
    res <- unchecked <$> exists @f @m
      ( do
          aVal :: Boolean <- read a
          bVal <- read b
          pure (aVal /= bVal)
      )
    let
      _a = coerce a :: AffineCircuit f Variable
      _b = coerce b
      _res = coerce res
    addConstraint $ R1CS
      { left: _a `Add` _a
      , right: _b
      , output: _a `Add` _b `subtract` _res
      }
    pure res

sum_
  :: forall f
   . Field f
  => Array (AffineCircuit f Variable)
  -> AffineCircuit f Variable
sum_ = foldl Add (Const zero)

any_
  :: forall f m
   . Field f
  => Eq f
  => CircuitBuilderM f m
  => Array (AffineCircuit f BooleanVariable)
  -> m (AffineCircuit f BooleanVariable)
any_ as =
  case Array.uncons as of
    Nothing -> pure false_
    Just { head: a0, tail } -> case Array.uncons tail of
      Nothing -> pure a0
      Just { a1, tail: rest } ->
        if Array.null rest then a0 `or_` a1
        else not_ <$> eq_ (sum_ (coerce as)) (Const zero)

all_
  :: forall f m
   . Field f
  => Eq f
  => CircuitBuilderM f m
  => Array (AffineCircuit f BooleanVariable)
  -> m (AffineCircuit f BooleanVariable)
all_ as =
  case Array.uncons as of
    Nothing -> pure true_
    Just { head: a0, tail } -> case Array.uncons tail of
      Nothing -> pure a0
      Just { head: a1, tail: rest } ->
        if Array.null rest then a0 `and_` a1
        else eq_ (sum_ (coerce as)) (Const $ Array.length as)