-- | Circuit types as values, so a shape can be chosen at runtime.
-- |
-- | `Snarky.Circuit.DSL.Monad.exists` is type-directed: the variables
-- | it allocates are counted by a `CircuitType` instance, so the shape
-- | must be static. That is what forces the pickles compiler to carry a
-- | type-level slot list even though every quantity it derives from
-- | that list is an ordinary integer. `Typ` reifies the three things
-- | the class supplies — a size, a serialiser, a check — `typOf`
-- | materialises it where the type is still in scope, and `existsTyp`
-- | is `exists` with the dictionary passed by hand.
-- |
-- | ## Why this is not in `snarky`
-- |
-- | It adds no capability; the primitive under `exists` is already
-- | length-directed. What it removes is a static guarantee, that the
-- | circuit-building and witness-generating passes agree on how many
-- | variables to allocate. With a type-level shape they agree by
-- | construction; with a value, only if both read the same value.
-- |
-- | That obligation is dischargeable here and not in general: a slot's
-- | shape comes from the application spec, is fixed when the circuit is
-- | compiled, and is stored on the compile result for the prover to
-- | read back, so there is nowhere for a caller to supply a different
-- | one. Do not export this beyond the pickles compiler, and do not
-- | build a `Typ` from anything a proof carries.
module Pickles.Typ
  ( Typ
  , typOf
  , existsTyp
  , arrayTyp
  , perSlotTyp
  , unitTyp
  , pairTyp
  , transportTyp
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (sum, traverse_)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Exception.Unsafe (unsafeThrow)
import Snarky.Circuit.CVar (CVar(..))
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, AsProver, CircuitOps(..), FVar, Snarky(..), check, fieldsToVar, sizeInFields, valueToFields)
import Type.Proxy (Proxy(..))

-- | A circuit type as a value: how many field elements it occupies, how
-- | to serialise a value into them, how to read variables back out, and
-- | what to constrain about the result.
-- |
-- | `check` is rank-2 in the runner row so that a stored `Typ` can be
-- | used at whatever row the prove call happens to run in.
type Typ :: Type -> Type -> Type -> Type -> Type
type Typ f c val var =
  { size :: Int
  , toFields :: val -> Array f
  , fromVars :: Array (FVar f) -> var
  , check :: forall r. var -> Snarky f c r Unit
  }

-- | Materialise the class dictionary as a value. Call it where the
-- | statement type is still in scope — at rule construction — and store
-- | the result; afterwards the type may be erased.
typOf
  :: forall @f @val @var c
   . CircuitType f val var
  => CheckedType f c var
  => Typ f c val var
typOf =
  { size: sizeInFields (Proxy @f) (Proxy @val)
  , toFields: valueToFields
  , fromVars: fieldsToVar @f @val
  , check
  }

-- | `exists` with the dictionary passed by hand.
-- |
-- | The caller owes one thing: `t.size` must be determined by the
-- | application spec, never by a witness. Allocation happens in both the
-- | building and the proving pass, and a size that differed between them
-- | would silently produce two different circuits.
existsTyp
  :: forall f c val var r
   . Typ f c val var
  -> AsProver f r val
  -> Snarky f c r var
existsTyp t w = do
  vars <- Snarky \(CircuitOps ops) -> ops.existsOp t.size (map fieldsOfDeclaredSize w)
  let v = t.fromVars (map Var vars)
  t.check v
  pure v
  where
  -- `existsOp` allocates `t.size` variables from the type and assigns
  -- them from these fields. Supply fewer and the tail is never
  -- assigned; the solver reports `MissingVariable` at whatever gate
  -- first reads one, arbitrarily far from the mistake and naming a
  -- variable index rather than the shape that was wrong. Supply more
  -- and the surplus is dropped silently. The two numbers meet here and
  -- nowhere else.
  --
  -- Prove-time only: the circuit-building pass discards this action, so
  -- at build time there is no value to disagree with.
  fieldsOfDeclaredSize val =
    let
      fs = t.toFields val
      n = Array.length fs
    in
      if n == t.size then fs
      else unsafeThrow
        $ "existsTyp: the type declares "
            <> show t.size
            <> " field elements but the witness supplied "
            <> show n
            <> ". Allocation follows the type and assignment follows the "
            <> "value, so this would leave variables unassigned."

-- | A fixed-length array of a repeated element type.
arrayTyp :: forall f c val var. Int -> Typ f c val var -> Typ f c (Array val) (Array var)
arrayTyp n elem =
  { size: n * elem.size
  , toFields: \xs -> Array.concatMap elem.toFields xs
  , fromVars: \vars -> map elem.fromVars (chunksOf elem.size vars)
  , check: traverse_ elem.check
  }

-- | One inner array per slot, of the widths given, all sharing an
-- | element type.
-- |
-- | The shape of a rule's previous-proof slot data: one stack of
-- | bulletproof challenges per slot, the stacks of differing widths.
-- | The type-level encoding nests `Vector w`; here the widths are the
-- | argument.
perSlotTyp
  :: forall f c val var
   . Array Int
  -> Typ f c val var
  -> Typ f c (Array (Array val)) (Array (Array var))
perSlotTyp widths elem =
  { size: sum widths * elem.size
  , toFields: Array.concatMap (Array.concatMap elem.toFields)
  , fromVars: split widths
  , check: traverse_ (traverse_ elem.check)
  }
  where
  split ws vars = case Array.uncons ws of
    Nothing -> []
    Just { head: w, tail: ws' } ->
      Array.cons
        (map elem.fromVars (chunksOf elem.size (Array.take (w * elem.size) vars)))
        (split ws' (Array.drop (w * elem.size) vars))

-- | The empty product: no field elements, nothing to constrain.
-- |
-- | Terminates a `pairTyp` chain, the way `Unit` terminates the nested
-- | tuple a `TupleN` is made of. Taken from the class rather than
-- | written out, so the terminator agrees with the instance by
-- | construction rather than by assertion.
unitTyp :: forall f c. Typ f c Unit Unit
unitTyp = typOf

-- | Two shapes in sequence: the left's field elements, then the
-- | right's.
-- |
-- | That is what the generic `CircuitType` instance does for a product,
-- | so a right-nested chain of `pairTyp` ending in `unitTyp` emits,
-- | field for field, what the corresponding `TupleN` instance emits.
-- | The correspondence is the point: it lets a record's `Typ` be
-- | written out by hand and still allocate the identical circuit,
-- | provided the chain lists the fields in the order the `TupleN` did.
-- |
-- | Unlike `unitTyp` this cannot be taken from the class — it combines
-- | two `Typ` values, and the interesting one is `arrayTyp` at a width
-- | known only at runtime. The paragraph above is the obligation that
-- | replaces the instance.
pairTyp
  :: forall f c leftVal leftVar rightVal rightVar
   . Typ f c leftVal leftVar
  -> Typ f c rightVal rightVar
  -> Typ f c (Tuple leftVal rightVal) (Tuple leftVar rightVar)
pairTyp left right =
  { size: left.size + right.size
  , toFields: \(Tuple lv rv) -> left.toFields lv <> right.toFields rv
  , fromVars: \vars ->
      let
        { before, after } = Array.splitAt left.size vars
      in
        Tuple (left.fromVars before) (right.fromVars after)
  , check: \(Tuple la ra) -> left.check la *> right.check ra
  }

-- | Re-present a shape at a different value and variable type, without
-- | touching its layout.
-- |
-- | Three functions rather than two isomorphisms, because a `Typ` never
-- | reads a value back out of field elements. The value type is only
-- | ever consumed, so it needs one direction; the variable type is both
-- | produced by `fromVars` and consumed by `check`, so it needs both.
-- |
-- | Use it to land a `pairTyp` chain on a record: the chain fixes the
-- | field order, and this names the fields.
transportTyp
  :: forall f c val var val' var'
   . (val' -> val)
  -> (var -> var')
  -> (var' -> var)
  -> Typ f c val var
  -> Typ f c val' var'
transportTyp toVal fromVar toVar t =
  { size: t.size
  , toFields: \v -> t.toFields (toVal v)
  , fromVars: \vars -> fromVar (t.fromVars vars)
  , check: \v -> t.check (toVar v)
  }

chunksOf :: forall a. Int -> Array a -> Array (Array a)
chunksOf n xs
  | n <= 0 = []
  | Array.null xs = []
  | otherwise = Array.cons (Array.take n xs) (chunksOf n (Array.drop n xs))
