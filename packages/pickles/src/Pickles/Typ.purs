-- | Circuit types as values, so a shape can be chosen at runtime.
-- |
-- | `Snarky.Circuit.DSL.Monad.exists` is type-directed: the variables it
-- | allocates are counted by a `CircuitType` instance, so the shape must
-- | be known statically. That is what forces the pickles compiler to
-- | carry a type-level slot list even though every quantity it derives
-- | from that list is an ordinary integer.
-- |
-- | The class supplies exactly three things — a size, a serialiser and a
-- | check — and the underlying primitive is already length-directed:
-- |
-- | ```
-- | exists w = do
-- |   let n = sizeInFields (Proxy @f) (Proxy @a)
-- |   vars <- Snarky \(CircuitOps ops) -> ops.existsOp n (map valueToFields w)
-- |   let v = fieldsToVar @f @a (map Var vars)
-- |   check v
-- |   pure v
-- | ```
-- |
-- | So `Typ` is that triple reified, `typOf` materialises it from the
-- | class wherever the type is still in scope, and `existsTyp` is
-- | `exists` with the dictionary passed by hand. This is OCaml pickles'
-- | arrangement: `Typ.t` there is a value carrying `store` / `read` /
-- | `alloc` / `check`, which is why `inductive_rule.ml` can hold a
-- | runtime list of previous-proof slots where this port needs one
-- | type-class instance per shape.
-- |
-- | ## Why this is not in `snarky`
-- |
-- | It adds no capability: `exists` already calls the length-directed
-- | primitive underneath. What it removes is a static guarantee, namely
-- | that the circuit-building pass and the witness-generating pass agree
-- | on how many variables to allocate. With a type-level shape they agree
-- | by construction; with a value they agree only if both read the same
-- | value.
-- |
-- | That obligation is dischargeable in pickles and not in general, so
-- | the primitive lives here. A slot's shape comes from the application
-- | spec, is fixed when the circuit is compiled, and is stored on the
-- | compile result for the prover to read back. A caller cannot supply a
-- | different one because there is nowhere to supply it.
-- |
-- | Do not export this beyond the pickles compiler, and do not build a
-- | `Typ` from anything a proof carries.
module Pickles.Typ
  ( Typ
  , typOf
  , existsTyp
  , arrayTyp
  , perSlotTyp
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (sum, traverse_)
import Data.Maybe (Maybe(..))
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
  vars <- Snarky \(CircuitOps ops) -> ops.existsOp t.size (map t.toFields w)
  let v = t.fromVars (map Var vars)
  t.check v
  pure v

-- | A fixed-length array of a repeated element type.
arrayTyp :: forall f c val var. Int -> Typ f c val var -> Typ f c (Array val) (Array var)
arrayTyp n elem =
  { size: n * elem.size
  , toFields: \xs -> Array.concatMap elem.toFields xs
  , fromVars: \vars -> map elem.fromVars (chunksOf elem.size vars)
  , check: traverse_ elem.check
  }

-- | One inner array per slot, each as wide as that slot's
-- | `max_local_max_proofs_verified`, all sharing an element type.
-- |
-- | This is the shape of a rule's previous-proof slot data: one stack of
-- | bullet-proof challenges per slot, of differing widths. The
-- | type-level encoding is a nested `Product` of `Vector w`; here the
-- | widths are the argument.
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

chunksOf :: forall a. Int -> Array a -> Array (Array a)
chunksOf n xs
  | n <= 0 = []
  | Array.null xs = []
  | otherwise = Array.cons (Array.take n xs) (chunksOf n (Array.drop n xs))
