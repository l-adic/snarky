module Snarky.Circuit.MerkleTree
  ( class MerkleRequestM
  , getElement
  , getPath
  , setValue
  , get
  , impliedRoot
  , modify
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Foldable (foldM)
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Hashable (class MerkleHashable)
import Data.MerkleTree.Sized (class Hashable, class MergeHash, Address, AddressVar(..), Path(..), hash, merge)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Partial.Unsafe (unsafeCrashWith)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, assertEqual_, exists, if_, read)
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Circuit.Types (class CheckedType, class CircuitType)

class
  ( Monad m
  , MerkleHashable v (Digest (F f))
  , CircuitType f v var
  , CheckedType var c
  ) <=
  MerkleRequestM m f v var c (d :: Int)
  | v f -> var, c -> f where
  getElement :: Address d -> m { value :: v, path :: Path d (Digest (F f)) }
  getPath :: Address d -> m (Path d (Digest (F f)))
  setValue :: Address d -> v -> m Unit

get
  :: forall t m f c d v vvar
   . Reflectable d Int
  => MerkleRequestM m f v vvar c d
  => Hashable vvar (Digest (FVar f))
  => CircuitM f c t m
  => AddressVar d f
  -> Digest (FVar f)
  -> Snarky c t m vvar
get addr (Digest root) = do
  { value, path } <- exists do
    a <- read addr
    lift $ getElement @m @_ @v @_ @c @d a
  let
    h = hash $ Just value
  impliedRoot addr h path >>= \(Digest d) ->
    assertEqual_ root d
  pure value

modify
  :: forall t m f c d v vvar
   . Reflectable d Int
  => MerkleRequestM m f v vvar c d
  => Hashable vvar (FVar f)
  => CircuitM f c t m
  => AddressVar d f
  -> FVar f
  -> (vvar -> Snarky c t m vvar)
  -> Snarky c t m vvar
modify = unsafeCrashWith ""

impliedRoot
  :: forall t m f c d
   . Reflectable d Int
  => MergeHash (Digest (FVar f))
  => CircuitM f c t m
  => AddressVar d f
  -> Digest (FVar f)
  -> Path d (Digest (FVar f))
  -> Snarky c t m (Digest (FVar f))
impliedRoot (AddressVar addr) hash (Path path) =
  foldM
    ( \(Digest acc) (Tuple b (Digest h)) -> do
        l <- if_ b h acc
        r <- if_ b acc h
        pure $ merge (Digest l) (Digest r)
    )
    hash
    (Vector.zip addr path)