-- | The circuit monad and core DSL operations, in DIRECT (final-tagless)
-- | style: a `Snarky` computation is a function from an interpreter's
-- | operations record (`CircuitOps`) straight to `Effect`, and an
-- | `AsProver` witness computation is a function from the prover context
-- | (assignments + advice handler) to `Effect`. Nothing is reified — a
-- | bind is a closure, an op is a record-field call. The TWO interpreters
-- | (the constraint builder, `Snarky.Backend.Builder`, and the witness
-- | prover, `Snarky.Backend.Prover`) are just two ways of constructing a
-- | `CircuitOps` record.
-- |
-- | ## Advice
-- |
-- | The open row `r` types the ADVICE an application serves to witness
-- | computations (a ledger oracle, …). Advice operations remain encoded as
-- | `Run r` values (cheap — they are rare); `liftAdvice` interprets them
-- | against the `AdviceHandler r` carried in the prover context.
-- |
-- | ## Errors
-- |
-- | Witness/constraint failures abort the whole interpretation via tagged
-- | JS exceptions (`Snarky.Circuit.EvalError`), recovered as
-- | `Either EvaluationError` only at interpreter boundaries. Throw-only —
-- | there is no user-facing catch, matching the old EXCEPT-row semantics.
-- |
-- | ## The `exists` encoding
-- |
-- | `exists` is monomorphized at the call site: the `CircuitType` dictionary
-- | projects the witness to `Array f` and rebuilds the variable bundle, so
-- | the ops-record payload is plain data — a size and a witness computation
-- | returning fields. The builder's ops ignore the witness computation; the
-- | prover's run it.
module Snarky.Circuit.DSL.Monad
  ( AsProver(..)
  , AsProverCtx(..)
  , liftAdvice
  , runAdvice
  , CircuitOps(..)
  , Snarky(..)
  , assignVars
  , addConstraint
  , exists
  , fresh
  , read
  , readCVar
  , runAsProver
  , liftEffectAsProver
  , liftEffectSnarky
  , mkWitnessTable
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
  , label
  ) where

import Prelude

import Control.Apply (lift2)
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Array as Array
import Data.Const (Const)
import Data.Either (Either(..))
import Data.Functor.Product (Product(..)) as FP
import Data.Generic.Rep (class Generic, Argument(..), Constructor(..), NoArguments, Product(..), from)
import Data.HeytingAlgebra (ff, implies, tt)
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Symbol (class IsSymbol)
import Data.Traversable (traverse, traverse_)
import Data.Tuple (Tuple)
import Data.Vector (Vector)
import Effect (Effect)
import Effect.Exception.Unsafe (unsafeThrow)
import Effect.Ref as Ref
import Prim.Row as Row
import Prim.RowList (class RowToList)
import Prim.RowList as RL
import Record as Record
import Run (Run)
import Run as Run
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (AdviceHandler(..))
import Snarky.Backend.Assignments (Assignments)
import Snarky.Backend.Assignments as Assignments
import Snarky.Circuit.CVar (CVar(..), EvaluationError(..), Variable, add_, const_, sub_)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.EvalError (throwEvalError)
import Snarky.Circuit.EvalError as EvalError
import Snarky.Circuit.Types (class CircuitType, Bool(..), BoolVar, F(..), FVar, NoInput, NoOutput, UnChecked, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Constraint.Basic (class BasicSystem, boolean, r1cs)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Witness (prover-side) computations

-- | What a witness computation runs against: the (mutable) assignment
-- | store it reads variables from, and the application's advice handler.
newtype AsProverCtx :: Type -> Row (Type -> Type) -> Type
newtype AsProverCtx f r = AsProverCtx
  { assignments :: Assignments f
  , advice :: AdviceHandler r
  }

-- | Prover-side computation: a direct reader of the prover context over
-- | `Effect`. Used as the argument to `exists` to compute witness values.
-- | A newtype so it can carry the lifted numeric/boolean instances below
-- | (witness blocks compute with `*`, `/`, `&&` over `readCVar` results).
newtype AsProver :: Type -> Row (Type -> Type) -> Type -> Type
newtype AsProver f r a = AsProver (AsProverCtx f r -> Effect a)

instance Functor (AsProver f r) where
  map f (AsProver g) = AsProver \ctx -> map f (g ctx)

instance Apply (AsProver f r) where
  apply (AsProver mf) (AsProver ma) = AsProver \ctx -> apply (mf ctx) (ma ctx)

instance Applicative (AsProver f r) where
  pure a = AsProver \_ -> pure a

instance Bind (AsProver f r) where
  bind (AsProver g) k = AsProver \ctx -> g ctx >>= \a -> case k a of AsProver h -> h ctx

instance Monad (AsProver f r)

instance MonadRec (AsProver f r) where
  tailRecM k a0 = AsProver \ctx -> tailRecM (\a -> case k a of AsProver g -> g ctx) a0

-- | Lift an advice computation (the open tail `r`) into a witness
-- | computation: interpret its (tiny) `Run` encoding against the context's
-- | handler. Advice ops are rare, so their `Run` reification is noise.
liftAdvice :: forall f r a. Run r a -> AsProver f r a
liftAdvice run = AsProver \(AsProverCtx ctx) -> runAdvice ctx.advice run

-- | Interpret a pure-advice `Run` program against a handler, directly in
-- | `Effect`.
runAdvice :: forall r a. AdviceHandler r -> Run r a -> Effect a
runAdvice (AdviceHandler h) = tailRecM \m -> case Run.peel m of
  Right a -> pure (Done a)
  Left v -> Loop <$> h v

instance (Semigroup a) => Semigroup (AsProver f r a) where
  append a b = lift2 (<>) a b

instance (Monoid a) => Monoid (AsProver f r a) where
  mempty = pure mempty

instance (Semiring a) => Semiring (AsProver f r a) where
  one = pure one
  zero = pure zero
  add = lift2 add
  mul = lift2 mul

instance (Ring a) => Ring (AsProver f r a) where
  sub = lift2 sub

instance (CommutativeRing a) => CommutativeRing (AsProver f r a)

instance (DivisionRing a) => DivisionRing (AsProver f r a) where
  recip = map recip

instance (EuclideanRing a) => EuclideanRing (AsProver f r a) where
  degree _ = 1
  div = lift2 div
  mod _ _ = pure zero

instance HeytingAlgebra (AsProver f r Boolean) where
  tt = pure tt
  ff = pure ff
  not = map not
  conj = lift2 conj
  disj = lift2 disj
  implies = lift2 implies

-- | Run a witness computation against an assignment map and advice
-- | handler, recovering a thrown `EvaluationError` at this boundary.
runAsProver
  :: forall f r a
   . AdviceHandler r
  -> Assignments f
  -> AsProver f r a
  -> Effect (Either EvaluationError a)
runAsProver advice assignments (AsProver g) =
  EvalError.catchEvalError (g (AsProverCtx { assignments, advice }))

readCVar :: forall f r. PrimeField f => FVar f -> AsProver f r (F f)
readCVar v = AsProver \(AsProverCtx ctx) -> do
  let _lookup var = maybe (throwEvalError $ MissingVariable var) pure $ Assignments.lookup var ctx.assignments
  F <$> CVar.eval _lookup v

read
  :: forall f var @a r
   . CircuitType f a var
  => PrimeField f
  => var
  -> AsProver f r a
read var = AsProver \(AsProverCtx ctx) -> do
  let fieldVars = varToFields @f @a var
  let _lookup v = maybe (throwEvalError $ MissingVariable v) pure $ Assignments.lookup v ctx.assignments
  fields <- traverse (CVar.eval _lookup) fieldVars
  pure $ fieldsToValue fields

throwAsProver :: forall f r a. EvaluationError -> AsProver f r a
throwAsProver e = AsProver \_ -> throwEvalError e

--------------------------------------------------------------------------------
-- The circuit monad

-- | The operations record an interpreter supplies: how each circuit op
-- | executes. The builder's ops collect constraints and ignore witness
-- | computations; the prover's run witnesses against the live assignments.
-- | A newtype so it can be stored and passed without rank-2 trouble; built
-- | once per compile/solve, so its cost is nothing.
newtype CircuitOps :: Type -> Type -> Row (Type -> Type) -> Type
newtype CircuitOps f c r = CircuitOps
  { freshOp :: Effect Variable
  , addConstraintOp :: c -> Effect Unit
  , existsOp :: Int -> AsProver f r (Array f) -> Effect (Array Variable)
  , assignOp :: Array Variable -> AsProver f r (Array f) -> Effect Unit
  , pushLabelOp :: String -> Effect Unit
  , popLabelOp :: Effect Unit
  }

-- | The circuit-building monad: a direct reader of the interpreter's ops
-- | over `Effect`. A bind is a closure; an op is a record-field call.
newtype Snarky :: Type -> Type -> Row (Type -> Type) -> Type -> Type
newtype Snarky f c r a = Snarky (CircuitOps f c r -> Effect a)

instance Functor (Snarky f c r) where
  map f (Snarky g) = Snarky \ops -> map f (g ops)

instance Apply (Snarky f c r) where
  apply (Snarky mf) (Snarky ma) = Snarky \ops -> apply (mf ops) (ma ops)

instance Applicative (Snarky f c r) where
  pure a = Snarky \_ -> pure a

instance Bind (Snarky f c r) where
  bind (Snarky g) k = Snarky \ops -> g ops >>= \a -> case k a of Snarky h -> h ops

instance Monad (Snarky f c r)

instance MonadRec (Snarky f c r) where
  tailRecM k a0 = Snarky \ops -> tailRecM (\a -> case k a of Snarky g -> g ops) a0

-- | Run an `Effect` inside a witness computation.
liftEffectAsProver :: forall f r a. Effect a -> AsProver f r a
liftEffectAsProver eff = AsProver \_ -> eff

-- | Lift an effect into the circuit monad. Runs under BOTH interpreters --
-- | builder and prover -- so use only for interpretation-neutral setup
-- | (e.g. allocating a fresh memo `Ref` for witness computations to share).
liftEffectSnarky :: forall f c r a. Effect a -> Snarky f c r a
liftEffectSnarky eff = Snarky \_ -> eff

-- | A lazily-computed, memoized witness table shared by many `exists`
-- | bodies: the FIRST body to run computes the whole table (e.g. a batched
-- | scalar-mul witness chain), the rest pay a `Ref` read plus an array
-- | index. The memo is allocated per gadget invocation, so solver closures
-- | reused across runs never share state; the builder discards exists
-- | bodies, so under compilation only the inert `Ref` allocation runs and
-- | the emitted circuit is untouched.
mkWitnessTable
  :: forall f c r a
   . String
  -> AsProver f r (Array a)
  -> Snarky f c r (Int -> AsProver f r a)
mkWitnessTable name compute = do
  memo <- liftEffectSnarky (Ref.new Nothing)
  pure \i -> do
    table <- liftEffectAsProver (Ref.read memo) >>= case _ of
      Just t -> pure t
      Nothing -> do
        t <- compute
        liftEffectAsProver (Ref.write (Just t) memo)
        pure t
    maybe (throwAsProver (FailedAssertion (name <> ": witness table index out of bounds"))) pure
      (Array.index table i)

-- | Allocate a fresh circuit variable.
fresh :: forall f c r. Snarky f c r Variable
fresh = Snarky \(CircuitOps ops) -> ops.freshOp

-- | Add a constraint to the circuit.
addConstraint :: forall f c r. c -> Snarky f c r Unit
addConstraint c = Snarky \(CircuitOps ops) -> ops.addConstraintOp c

-- | Bind already-allocated variables to witness-computed values (prover
-- | only; the builder ignores it). Used by the solver to back-fill the
-- | public-output slots.
assignVars :: forall f c r. Array Variable -> AsProver f r (Array f) -> Snarky f c r Unit
assignVars vars w = Snarky \(CircuitOps ops) -> ops.assignOp vars w

-- | Introduce witness variables with a prover-side computation. The builder
-- | interpreter allocates variables and ignores the computation; the prover
-- | interpreter runs it against the current assignments and records the
-- | results. Type-specific `check` constraints are added either way.
exists
  :: forall f c r a var
   . CircuitType f a var
  => CheckedType f c var
  => AsProver f r a
  -> Snarky f c r var
exists w = do
  let n = sizeInFields (Proxy @f) (Proxy @a)
  vars <- Snarky \(CircuitOps ops) -> ops.existsOp n (map valueToFields w)
  let v = fieldsToVar @f @a (map Var vars)
  check v
  pure v

-- | Label a block of circuit code for debugging: constraints emitted inside
-- | carry the label context, and prover errors (in debug mode) are wrapped
-- | with it.
label :: forall f c r a. String -> Snarky f c r a -> Snarky f c r a
label s (Snarky m) = Snarky \ops@(CircuitOps o) -> do
  o.pushLabelOp s
  a <- m ops
  o.popLabelOp
  pure a

--------------------------------------------------------------------------------

instance (PrimeField f, BasicSystem f c) => Semigroup (Snarky f c r (FVar f)) where
  append a b = lift2 (<>) a b

else instance (Semigroup (Snarky f c r a), Newtype s a, Functor (Snarky f c r)) => Semigroup (Snarky f c r s) where
  append x y = map wrap (append (map unwrap x) (map unwrap y))

instance (PrimeField f, BasicSystem f c) => Monoid (Snarky f c r (FVar f)) where
  mempty = pure mempty

else instance (Monoid (Snarky f c r a), Newtype s a, Functor (Snarky f c r), Semigroup (Snarky f c r s)) => Monoid (Snarky f c r s) where
  mempty = map wrap mempty

instance (PrimeField f, BasicSystem f c) => Semiring (Snarky f c r (FVar f)) where
  one = pure $ const_ one
  zero = pure $ const_ zero
  add a b = lift2 add_ a b
  mul a b = join $ lift2 mul_ a b

else instance (Semiring (Snarky f c r a), Newtype s a, Functor (Snarky f c r)) => Semiring (Snarky f c r s) where
  one = map wrap one
  zero = map wrap zero
  add x y = map wrap (add (map unwrap x) (map unwrap y))
  mul x y = map wrap (mul (map unwrap x) (map unwrap y))

instance (PrimeField f, BasicSystem f c) => Ring (Snarky f c r (FVar f)) where
  sub a b = sub_ <$> a <*> b

else instance (Ring (Snarky f c r a), Newtype s a, Functor (Snarky f c r), Semiring (Snarky f c r s)) => Ring (Snarky f c r s) where
  sub x y = map wrap (sub (map unwrap x) (map unwrap y))

instance (PrimeField f, BasicSystem f c) => CommutativeRing (Snarky f c r (FVar f))

else instance (CommutativeRing (Snarky f c r a), Newtype s a, Ring (Snarky f c r s)) => CommutativeRing (Snarky f c r s)

instance (PrimeField f, BasicSystem f c) => DivisionRing (Snarky f c r (FVar f)) where
  recip a = a >>= inv_

else instance (DivisionRing (Snarky f c r a), Newtype s a, Functor (Snarky f c r), Ring (Snarky f c r s)) => DivisionRing (Snarky f c r s) where
  recip x = map wrap (recip (map unwrap x))

instance (PrimeField f, BasicSystem f c) => EuclideanRing (Snarky f c r (FVar f)) where
  degree _ = 1
  div a b = join $ lift2 div_ a b
  mod _ _ = pure $ const_ zero

else instance (EuclideanRing (Snarky f c r a), Newtype s a, Functor (Snarky f c r), CommutativeRing (Snarky f c r s)) => EuclideanRing (Snarky f c r s) where
  degree _ = 1
  div x y = map wrap (div (map unwrap x) (map unwrap y))
  mod x y = map wrap (mod (map unwrap x) (map unwrap y))

instance (PrimeField f, BasicSystem f c) => HeytingAlgebra (Snarky f c r (BoolVar f)) where
  tt = pure $ const_ (one :: f)
  ff = pure $ const_ (zero :: f)
  not a = not_ <$> a
  conj a b = join $ lift2 and_ a b
  disj a b = join $ lift2 or_ a b
  implies a b = not a || b

else instance (HeytingAlgebra (Snarky f c r a), Newtype s a, Functor (Snarky f c r)) => HeytingAlgebra (Snarky f c r s) where
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
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => BoolVar f
  -> BoolVar f
  -> Snarky f c r (BoolVar f)
or_ a b = not_ <$> (not_ a) `and_` (not_ b)

and_
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => BoolVar f
  -> BoolVar f
  -> Snarky f c r (BoolVar f)
and_ a b = do
  coerce <$> mul_ (coerce a :: FVar f) (coerce b)

inv_
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> Snarky f c r (FVar f)
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
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> FVar f
  -> Snarky f c r (FVar f)
mul_ a b =
  case a, b of
    Const f, Const f' -> pure $ Const (f * f')
    Const f, c -> pure $ CVar.scale_ f c
    c, Const f -> pure $ CVar.scale_ f c
    _, _ -> do
      z <- exists do
        aVal <- readCVar a
        bVal <- readCVar b
        pure $ aVal * bVal
      addConstraint $ r1cs { left: a, right: b, output: z }
      pure z

div_
  :: forall f c r
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> FVar f
  -> Snarky f c r (FVar f)
div_ a b = mul_ a =<< inv_ b

--------------------------------------------------------------------------------

-- | Defines what constraints are added when a variable type is introduced via `exists`.
-- | For example, `BoolVar` adds a boolean constraint; `FVar` adds nothing.
-- | Use `UnChecked` wrapper to skip checks when constraints are guaranteed elsewhere.
class CheckedType f c var | c -> f, var -> f where
  check :: forall r. var -> Snarky f c r Unit

instance CheckedType f c Unit where
  check _ = pure unit

instance CheckedType f c NoInput where
  check _ = pure unit

instance CheckedType f c NoOutput where
  check _ = pure unit

instance CheckedType f c (FVar f) where
  check _ = pure unit

instance BasicSystem f c => CheckedType f c (BoolVar f) where
  check var = addConstraint $ boolean (coerce var :: FVar f)

instance (CheckedType f c avar, CheckedType f c bvar) => CheckedType f c (Tuple avar bvar) where
  check = genericCheck

-- | `Const Unit a` has no content to check, regardless of `a`. Used
-- | by higher-kinded slot-list representations (see
-- | `Pickles.Wrap.Slots`).
instance CheckedType f c (Const Unit a) where
  check _ = pure unit

-- | `Product f g a = Product (Tuple (f a) (g a))` checks each factor
-- | recursively, mirroring the Tuple instance one layer up.
instance
  ( CheckedType f c (fc a)
  , CheckedType f c (gc a)
  ) =>
  CheckedType f c (FP.Product fc gc a) where
  check (FP.Product t) = check t

instance CheckedType f c (UnChecked var) where
  check _ = pure unit

instance CheckedType f c var => CheckedType f c (Vector n var) where
  check var = traverse_ check var

instance (RowToList var rlvar, RCheckedType f c rlvar var) => CheckedType f c (Record var) where
  check x = rCheck (Proxy @rlvar) x

class GCheckedType f c var | c -> f, var -> f where
  gCheck :: forall r. var -> Snarky f c r Unit

instance GCheckedType f c NoArguments where
  gCheck _ = pure unit

instance CheckedType f c a => GCheckedType f c (Argument a) where
  gCheck (Argument a) = check a

instance (GCheckedType f c avar, GCheckedType f c bvar) => GCheckedType f c (Product avar bvar) where
  gCheck (Product a b) = gCheck a *> gCheck b

instance GCheckedType f c var => GCheckedType f c (Constructor name var) where
  gCheck (Constructor a) = gCheck a

genericCheck
  :: forall var rep f c r
   . Generic var rep
  => GCheckedType f c rep
  => var
  -> Snarky f c r Unit
genericCheck var = gCheck $ from var

class RCheckedType :: forall k. Type -> Type -> k -> Row Type -> Constraint
class RCheckedType f c rlvar var | rlvar -> var where
  rCheck :: forall r. Proxy rlvar -> Record var -> Snarky f c r Unit

instance RCheckedType f c RL.Nil () where
  rCheck _ _ = pure unit

instance
  ( IsSymbol s
  , Row.Cons s avar restvars vars
  , Row.Lacks s restvars
  , CheckedType f c avar
  , RCheckedType f c tailvars restvars
  ) =>
  RCheckedType f c (RL.Cons s avar tailvars) vars where
  rCheck _ r = do
    check $ Record.get (Proxy @s) r
    rCheck (Proxy @tailvars) $ Record.delete (Proxy @s) r
