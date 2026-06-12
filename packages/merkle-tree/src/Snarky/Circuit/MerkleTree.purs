module Snarky.Circuit.MerkleTree
  ( MerkleF(..)
  , MERKLE
  , _merkle
  , getElement
  , getPath
  , setValue
  , get
  , impliedRoot
  , fetchAndUpdate
  , update
  ) where

import Prelude

import Data.Foldable (foldM)
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Hashable (class MerkleHashable, hashLeaf, mergeCircuit)
import Data.MerkleTree.Sized (Address, AddressVar(..), Path(..))
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Poseidon (class PoseidonField)
import Run (Run)
import Run as Run
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, FVar, Snarky, assertEqual_, exists, if_, liftAdvice, read)
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

-- | Merkle-tree advice requests as a `Run` effect (replaces the old
-- | `MerkleRequestM m` advice-monad class). Interpreters answer the
-- | requests against a concrete tree (e.g. a `Ref`-held in-memory tree).
data MerkleF f v (d :: Int) a
  = GetElement (Address d) ({ value :: v, path :: Path d (Digest f) } -> a)
  | GetPath (Address d) (Path d (Digest f) -> a)
  | SetValue (Address d) v a

derive instance Functor (MerkleF f v d)

type MERKLE f v d r = (merkle :: MerkleF f v d | r)

_merkle :: Proxy "merkle"
_merkle = Proxy

getElement :: forall @f @v @d r. Address d -> Run (MERKLE f v d + r) { value :: v, path :: Path d (Digest f) }
getElement a = Run.lift _merkle (GetElement a identity)

getPath :: forall @f @v @d r. Address d -> Run (MERKLE f v d + r) (Path d (Digest f))
getPath a = Run.lift _merkle (GetPath a identity)

setValue :: forall @f @v @d r. Address d -> v -> Run (MERKLE f v d + r) Unit
setValue a v = Run.lift _merkle (SetValue a v unit)

get
  :: forall f d @v var r
   . Reflectable d Int
  => PoseidonField f
  => PrimeField f
  => CircuitType f v var
  => CheckedType f (KimchiConstraint f) var
  => MerkleHashable var (Snarky f (KimchiConstraint f) (MERKLE f v d + r) (Digest (FVar f)))
  => AddressVar d f
  -> Digest (FVar f)
  -> Snarky f (KimchiConstraint f) (MERKLE f v d + r) var
get addr (Digest root) = do
  { value, path } <- exists do
    a <- read addr
    liftAdvice $ getElement @f @v @d a
  h <- hashLeaf $ Just value
  impliedRoot addr h path >>= \(Digest d) ->
    assertEqual_ root d
  pure value

-- | Fetch an element, apply a modification, and update the tree.
-- |
-- | This function:
-- | 1. Witnesses the current element and path
-- | 2. Verifies the old element hashes to the given root
-- | 3. Applies the modification function to get the new element
-- | 4. Updates the underlying tree state via setValue
-- | 5. Computes and returns the new root along with old and new elements
fetchAndUpdate
  :: forall f d @v var r
   . Reflectable d Int
  => PoseidonField f
  => PrimeField f
  => CircuitType f v var
  => CheckedType f (KimchiConstraint f) var
  => MerkleHashable var (Snarky f (KimchiConstraint f) (MERKLE f v d + r) (Digest (FVar f)))
  => AddressVar d f
  -> Digest (FVar f)
  -> (var -> Snarky f (KimchiConstraint f) (MERKLE f v d + r) var)
  -> Snarky f (KimchiConstraint f) (MERKLE f v d + r)
       { root :: Digest (FVar f)
       , old :: var
       , new :: var
       }
fetchAndUpdate addr (Digest root) f = do
  -- Get element and path as witnesses
  { value: prev, path } <- exists do
    a <- read addr
    liftAdvice $ getElement @f @v @d a
  -- Hash old element and verify against root
  prevHash <- hashLeaf $ Just prev
  impliedRoot addr prevHash path >>= \(Digest d) ->
    assertEqual_ root d
  -- Apply modification function
  next <- f prev
  -- Update the tree with the new value
  _ <- exists do
    a <- read addr
    n <- read @v next
    liftAdvice $ setValue @f @v @d a n
  -- Hash new element and compute new root
  nextHash <- hashLeaf $ Just next
  newRoot <- impliedRoot addr nextHash path
  pure { root: newRoot, old: prev, new: next }

-- | Update an element when you already have both old and new values.
-- |
-- | This function:
-- | 1. Witnesses only the path (not the element)
-- | 2. Verifies the old element hashes to the given root
-- | 3. Updates the underlying tree state via setValue
-- | 4. Computes and returns the new root
update
  :: forall f d @v var r
   . Reflectable d Int
  => PoseidonField f
  => PrimeField f
  => CircuitType f v var
  => MerkleHashable var (Snarky f (KimchiConstraint f) (MERKLE f v d + r) (Digest (FVar f)))
  => AddressVar d f
  -> Digest (FVar f)
  -> var
  -> var
  -> Snarky f (KimchiConstraint f) (MERKLE f v d + r) (Digest (FVar f))
update addr (Digest root) prev next = do
  -- Witness only the path
  path <- exists do
    a <- read addr
    liftAdvice $ getPath @f @v @d a
  -- Hash old element and verify against root
  prevHash <- hashLeaf $ Just prev
  impliedRoot addr prevHash path >>= \(Digest d) ->
    assertEqual_ root d
  -- Update the tree with the new value
  _ <- exists do
    a <- read addr
    n <- read @v next
    liftAdvice $ setValue @f @v @d a n
  -- Hash new element and compute new root
  nextHash <- hashLeaf $ Just next
  impliedRoot addr nextHash path

impliedRoot
  :: forall f d r
   . Reflectable d Int
  => PoseidonField f
  => PrimeField f
  => AddressVar d f
  -> Digest (FVar f)
  -> Path d (Digest (FVar f))
  -> Snarky f (KimchiConstraint f) r (Digest (FVar f))
impliedRoot (AddressVar addr) initialHash (Path path) =
  foldM
    ( \(Digest acc) (Tuple b (Digest h)) -> do
        l <- if_ b h acc
        r <- if_ b acc h
        mergeCircuit (Digest l) (Digest r)
    )
    initialHash
    (Vector.zip addr path)