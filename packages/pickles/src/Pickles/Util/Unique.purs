-- | Opaque runtime identity tokens, modeled on Haskell's
-- | `Data.Unique` (`hackage:base/Data.Unique`). Each `newUnique` call
-- | allocates a globally fresh value that compares unequal to every
-- | previous one, and equal only to itself.
-- |
-- | Used by `Pickles.Prove.Compile.Tag` as the routing key — the
-- | prover/verifier identity tied to a single `compile` invocation.
-- | Equality + ordering let it serve as a Map/HashMap key for
-- | downstream registries (mutual-rule families, side-loaded VKs).
module Pickles.Util.Unique
  ( Unique
  , newUnique
  ) where

import Prelude

import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)

newtype Unique = Unique Int

derive newtype instance Eq Unique
derive newtype instance Ord Unique

instance Show Unique where
  show (Unique n) = "Unique#" <> show n

-- | Module-local counter. Allocated lazily once at module load via
-- | `unsafePerformEffect`. Subsequent `newUnique` calls atomically
-- | increment via `Ref.modify`. Sufficient for single-threaded JS;
-- | not safe across workers, but Pickles compiles run in a single
-- | thread.
counter :: Ref Int
counter = unsafePerformEffect (Ref.new 0)

-- | Allocate a fresh `Unique`. Each call returns a value distinct
-- | from every prior return.
newUnique :: Effect Unique
newUnique = Unique <$> Ref.modify (_ + 1) counter
