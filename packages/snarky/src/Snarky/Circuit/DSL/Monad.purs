-- | The circuit monad and core DSL operations, expressed with
-- | `purescript-run` extensible effects.
-- |
-- | Circuit construction is ONE first-order effect (`CircuitF`) with TWO
-- | interpreters — the constraint builder (`Snarky.Backend.Builder`) and the
-- | witness prover (`Snarky.Backend.Prover`) — replacing the old
-- | `CircuitM f c t m` class over two monad transformers.
-- |
-- | ## The rows
-- |
-- | ```purescript
-- | Snarky f c r a       -- circuit program: Run (circuit :: CircuitF f c r | r) a
-- | AsProver f r a       -- witness program: Run (EXCEPT … + READER … + r) a
-- | ```
-- |
-- | The old "base monad" `m` (the advice monad) is now the OPEN TAIL `r` —
-- | effects the circuit doesn't know about (a ledger oracle, `EFFECT`,
-- | nothing). They are reachable only from witness computations passed to
-- | `exists`, exactly as before.
-- |
-- | ## The `exists` encoding
-- |
-- | `exists` is monomorphized at the call site: the `CircuitType` dictionary
-- | projects the witness to `Array f` and rebuilds the variable bundle, so the
-- | effect payload is plain data — a size, a witness computation returning
-- | fields, and a continuation from the allocated variables. The builder
-- | interpreter discards the witness computation; the prover runs it.
module Snarky.Circuit.DSL.Monad
  ( AsProver(..)
  , ASPROVER
  , liftAdvice
  , liftEffectRow
  , CircuitF(..)
  , CIRCUIT
  , Snarky(..)
  , _circuit
  , liftCircuit
  , runSnarky
  , addConstraint
  , exists
  , fresh
  , read
  , readCVar
  , runAsProver
  , runAsProverPure
  , unAsProver
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
import Control.Monad.Rec.Class (class MonadRec)
import Data.Const (Const)
import Data.Either (Either)
import Data.Functor.Product (Product(..)) as FP
import Data.Generic.Rep (class Generic, Argument(..), Constructor(..), NoArguments, Product(..), from)
import Data.HeytingAlgebra (ff, implies, tt)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Symbol (class IsSymbol)
import Data.Traversable (traverse, traverse_)
import Data.Tuple (Tuple)
import Data.Vector (Vector)
import Effect.Exception.Unsafe (unsafeThrow)
import Prim.Row as Row
import Prim.RowList (class RowToList)
import Prim.RowList as RL
import Record as Record
import Run (EFFECT, Run)
import Run as Run
import Run.Except (EXCEPT)
import Run.Except as Except
import Run.Reader (READER)
import Run.Reader as Reader
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (CVar(..), EvaluationError(..), Variable, add_, const_, sub_)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.Types (class CircuitType, Bool(..), BoolVar, F(..), FVar, NoInput, NoOutput, UnChecked, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Constraint.Basic (class BasicSystem, boolean, r1cs)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------
-- Witness (prover-side) computations

-- | The effects available to a witness computation: evaluation failure,
-- | read access to the current variable assignments, plus whatever advice
-- | effects `r` the application provides.
type ASPROVER f r = EXCEPT EvaluationError + READER (Map Variable f) + r

-- | Prover-side computation. Runs with access to variable assignments,
-- | used as the argument to `exists` to compute witness values. A newtype
-- | over `Run` so it can carry the lifted numeric/boolean instances below
-- | (witness blocks compute with `*`, `/`, `&&` over `readCVar` results).
newtype AsProver :: Type -> Row (Type -> Type) -> Type -> Type
newtype AsProver f r a = AsProver (Run (ASPROVER f r) a)

derive newtype instance Functor (AsProver f r)
derive newtype instance Apply (AsProver f r)
derive newtype instance Applicative (AsProver f r)
derive newtype instance Bind (AsProver f r)
derive newtype instance Monad (AsProver f r)
derive newtype instance MonadRec (AsProver f r)

-- | Widen an open row by the EFFECT label (for orchestration code running
-- | solvers, whose results are `Run r`, inside `Run (EFFECT + r)`). Safe for
-- | the same reason `Run.expand` is (a `Run r` program can never produce an
-- | effect outside `r`); spelled with a coercion because the `Union` solver
-- | cannot align two open tails.
liftEffectRow :: forall r a. Run r a -> Run (EFFECT + r) a
liftEffectRow = unsafeCoerce

-- | Lift an advice computation (the open tail `r`) into a witness
-- | computation. Replaces the old `MonadTrans (AsProverT f)` instance; the
-- | row widening is safe for the same reason `Run.expand` is (a `Run r`
-- | program can never produce an effect outside `r`), and is spelled with a
-- | coercion because the `Union` solver cannot align two open tails.
liftAdvice :: forall f r a. Run r a -> AsProver f r a
liftAdvice = AsProver <<< (unsafeCoerce :: Run r a -> Run (ASPROVER f r) a)

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

-- | Interpret a witness computation against an assignment map, leaving the
-- | advice effects `r` to the caller.
runAsProver
  :: forall f r a
   . Map Variable f
  -> AsProver f r a
  -> Run r (Either EvaluationError a)
runAsProver env (AsProver m) = Except.runExcept (Reader.runReader env m)

-- | Interpret a CLOSED witness computation (no advice effects) purely.
runAsProverPure
  :: forall f a
   . AsProver f () a
  -> Map Variable f
  -> Either EvaluationError a
runAsProverPure m env = Run.extract (runAsProver env m)

readCVar :: forall f r. PrimeField f => FVar f -> AsProver f r (F f)
readCVar v = AsProver do
  m <- Reader.ask
  let _lookup var = maybe (Except.throw $ MissingVariable var) pure $ Map.lookup var m
  F <$> CVar.eval _lookup v

read
  :: forall f var @a r
   . CircuitType f a var
  => PrimeField f
  => var
  -> AsProver f r a
read var = AsProver do
  let fieldVars = varToFields @f @a var
  m <- Reader.ask
  let _lookup v = maybe (Except.throw $ MissingVariable v) pure $ Map.lookup v m
  fields <- traverse (CVar.eval _lookup) fieldVars
  pure $ fieldsToValue fields

throwAsProver :: forall f r a. EvaluationError -> AsProver f r a
throwAsProver = AsProver <<< Except.throw

--------------------------------------------------------------------------------
-- The circuit effect

-- | The circuit-construction effect. First-order: `Exists` carries the
-- | witness computation already projected to `Array f` (see module doc), so
-- | interpreters never need the value type or its dictionaries.
data CircuitF f c (r :: Row (Type -> Type)) a
  = Fresh (Variable -> a)
  | AddConstraint c a
  | Exists Int (Run (ASPROVER f r) (Array f)) (Array Variable -> a)
  | Assign (Array Variable) (Run (ASPROVER f r) (Array f)) a
  | PushLabel String a
  | PopLabel a

derive instance Functor (CircuitF f c r)

-- | The circuit row: the `circuit` effect over an open tail of advice
-- | effects `r` (shared with the witness computations inside `Exists`).
type CIRCUIT f c r = (circuit :: CircuitF f c r | r)

_circuit :: Proxy "circuit"
_circuit = Proxy

-- | The circuit-building monad: `Run` over the circuit effect, newtyped to
-- | carry the numeric/boolean instances below (orphan rules forbid them on
-- | `Run` directly). Runtime-free.
newtype Snarky :: Type -> Type -> Row (Type -> Type) -> Type -> Type
newtype Snarky f c r a = Snarky (Run (CIRCUIT f c r) a)

derive newtype instance Functor (Snarky f c r)
derive newtype instance Apply (Snarky f c r)
derive newtype instance Applicative (Snarky f c r)
derive newtype instance Bind (Snarky f c r)
derive newtype instance Monad (Snarky f c r)
derive newtype instance MonadRec (Snarky f c r)

runSnarky :: forall f c r a. Snarky f c r a -> Run (CIRCUIT f c r) a
runSnarky (Snarky m) = m

unAsProver :: forall f r a. AsProver f r a -> Run (ASPROVER f r) a
unAsProver (AsProver m) = m

liftCircuit :: forall f c r a. CircuitF f c r a -> Snarky f c r a
liftCircuit = Snarky <<< Run.lift _circuit

-- | Allocate a fresh circuit variable.
fresh :: forall f c r. Snarky f c r Variable
fresh = liftCircuit (Fresh identity)

-- | Add a constraint to the circuit.
addConstraint :: forall f c r. c -> Snarky f c r Unit
addConstraint c = liftCircuit (AddConstraint c unit)

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
exists (AsProver w) = do
  let n = sizeInFields (Proxy @f) (Proxy @a)
  vars <- liftCircuit (Exists n (map valueToFields w) identity)
  let v = fieldsToVar @f @a (map Var vars)
  check v
  pure v

-- | Label a block of circuit code for debugging: constraints emitted inside
-- | carry the label context, and prover errors (in debug mode) are wrapped
-- | with it.
label :: forall f c r a. String -> Snarky f c r a -> Snarky f c r a
label s (Snarky m) = Snarky do
  Run.lift _circuit (PushLabel s unit)
  a <- m
  Run.lift _circuit (PopLabel unit)
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
