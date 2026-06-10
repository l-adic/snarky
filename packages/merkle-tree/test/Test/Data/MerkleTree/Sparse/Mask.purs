-- | Property tests for `Data.MerkleTree.Sparse.Mask`: a mask is a *faithful
-- | witness* of a full sparse tree over its touched addresses. Every law
-- | relates the mask back to the full tree it was extracted from.
-- |
-- | The load-bearing laws are `set commutes` (single + double): updating the
-- | mask and updating the full ledger yield the same root — i.e. proving
-- | against the witness equals applying to the real ledger.
module Test.Data.MerkleTree.Sparse.Mask (spec) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Foldable (foldl, for_)
import Data.Int (pow)
import Data.Maybe (Maybe(..), fromJust)
import Data.MerkleTree.Hashable (class Hashable)
import Data.MerkleTree.Sized (Address(..), Path)
import Data.MerkleTree.Sparse (SparseMerkleTree)
import Data.MerkleTree.Sparse as Full
import Data.MerkleTree.Sparse.Mask (SparseLedger)
import Data.MerkleTree.Sparse.Mask as Mask
import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable, reflectType, reifyType)
import Data.Tuple (Tuple(..), fst)
import Data.Vector as Vector
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField)
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (class Arbitrary, arbitrary, quickCheckGen', (===))
import Test.QuickCheck.Gen (Gen, chooseInt, elements, shuffle, suchThat, vectorOf)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy)

-- Depths ≥ 2 so there's room for ≥ 2 distinct touched addresses.
-- Capped at 8: the generator populates up to `2^(d-1)` accounts, so deeper
-- trees would build an impractically large ledger per case.
treeDepths :: Array Int
treeDepths = [ 2, 4, 8 ]

-- The laws are exact mask-vs-full relations, so a modest sample suffices; the
-- depth-8 cases (up to ~2^7 accounts) make a large count needlessly slow.
trials :: Int
trials = 20

--------------------------------------------------------------------------------
-- Generators

-- | A full tree built from known entries, the touched addresses (its populated
-- | slots plus a couple of likely-empty ones), and a `focus` drawn from them.
type Scenario d f =
  { full :: SparseMerkleTree d (Digest f) f
  , touched :: Array (Address d)
  , focus :: Address d
  }

addressOf :: forall d. Int -> Address d
addressOf = Address <<< BigInt.fromInt

genScenario
  :: forall @f d
   . Reflectable d Int
  => PoseidonField f
  => Hashable f f
  => Arbitrary f
  => Proxy d
  -> Gen (Scenario d f)
genScenario pd = do
  let
    d = reflectType pd
    hi = (2 `pow` d) - 1
  -- Populate a random number of accounts strictly less than half the slots
  -- (< 2^(d-1)): the tree is at most half-full, leaving room for a strict subset
  -- to keep some accounts collapsed and a majority of empty slots for creation.
  nEntries <- chooseInt 1 ((2 `pow` (d - 1)) - 1)
  entries <- vectorOf nEntries (Tuple <$> chooseInt 0 hi <*> arbitrary @f)
  let
    -- `Full.set` only fails (Nothing) out of bounds; `chooseInt 0 hi` is always
    -- in bounds, so assert that with `fromJust`.
    full = foldl (\t (Tuple i v) -> unsafePartial (fromJust (Full.set (addressOf i) v t))) Full.empty entries
    populated = Array.nub (map fst entries)
  -- An empty slot for creation coverage — > half the tree is empty, so this
  -- resamples in ~2 tries on average.
  emptyAddr <- chooseInt 0 hi `suchThat` \i -> not (Array.elem i populated)
  -- Touch a STRICT subset of the populated accounts (so the un-touched ones are
  -- collapsed into `Hash` frontier nodes) plus the empty slot.
  kept <- strictSubset populated
  let touchedInts = Array.cons emptyAddr kept
  focus <- elements (unsafePartial (fromJust (NEA.fromArray touchedInts)))
  pure { full, touched: map addressOf touchedInts, focus: addressOf focus }

-- | A non-empty, proper subset of `xs` (drops at least one element when
-- | `length xs ≥ 2`; degenerates to all of `xs` for a singleton).
strictSubset :: forall a. Array a -> Gen (Array a)
strictSubset xs = do
  let n = Array.length xs
  k <- chooseInt 1 (max 1 (n - 1))
  Array.take k <$> shuffle xs

mkMask
  :: forall d f
   . Reflectable d Int
  => PoseidonField f
  => Hashable f f
  => Scenario d f
  -> SparseLedger d (Digest f) Int f
mkMask { full, touched } =
  Mask.fromSubset full (map (\a -> Tuple a (Nothing :: Maybe Int)) touched)

-- | Touched addresses as a non-empty array (always ≥ 1 — the empty slot is
-- | always present).
neTouched :: forall d f. Scenario d f -> NEA.NonEmptyArray (Address d)
neTouched s = unsafePartial (fromJust (NEA.fromArray s.touched))

--------------------------------------------------------------------------------
-- Spec

spec :: Spec Unit
spec = describe "Sparse.Mask faithful-witness laws" do

  it "1. mask root == full root" $ liftEffect $
    for_ treeDepths \depth -> quickCheckGen' trials $ reifyType depth \pd -> do
      s <- genScenario @Vesta.ScalarField pd
      pure $ Mask.merkleRoot (mkMask s) === Full.root s.full

  it "2. get agrees with the full tree on touched addresses" $ liftEffect $
    for_ treeDepths \depth -> quickCheckGen' trials $ reifyType depth \pd -> do
      s <- genScenario @Pallas.ScalarField pd
      pure $ Mask.get s.focus (mkMask s) === Full.get s.full s.focus

  it "3. getPath agrees with the full tree's witness" $ liftEffect $
    for_ treeDepths \depth -> quickCheckGen' trials $ reifyType depth \pd -> do
      s <- genScenario @Vesta.ScalarField pd
      pure $ pathArr (Mask.getPath s.focus (mkMask s)) === pathArr (Full.getWitness s.focus s.full)

  it "4. set commutes: mask update == full ledger update (same root)" $ liftEffect $
    for_ treeDepths \depth -> quickCheckGen' trials $ reifyType depth \pd -> do
      s <- genScenario @Pallas.ScalarField pd
      v <- arbitrary @Pallas.ScalarField
      pure $ Just (Mask.merkleRoot (Mask.set s.focus v (mkMask s)))
        === (Full.root <$> Full.set s.focus v s.full)

  it "5. two sets commute (sender+receiver, overlapping paths)" $ liftEffect $
    for_ treeDepths \depth -> quickCheckGen' trials $ reifyType depth \pd -> do
      s <- genScenario @Vesta.ScalarField pd
      b <- elements (neTouched s)
      va <- arbitrary @Vesta.ScalarField
      vb <- arbitrary @Vesta.ScalarField
      let maskR = Mask.merkleRoot (Mask.set b vb (Mask.set s.focus va (mkMask s)))
      let fullR = Full.root <$> (Full.set s.focus va s.full >>= Full.set b vb)
      pure $ Just maskR === fullR

  it "6. set-get: get after set returns the new value" $ liftEffect $
    for_ treeDepths \depth -> quickCheckGen' trials $ reifyType depth \pd -> do
      s <- genScenario @Pallas.ScalarField pd
      v <- arbitrary @Pallas.ScalarField
      pure $ Mask.get s.focus (Mask.set s.focus v (mkMask s)) === Just v

pathArr :: forall d f. Path d (Digest f) -> Array (Digest f)
pathArr = unwrap >>> Vector.toUnfoldable
