module Snarky.Circuit.Kimchi.VarBaseMul
  ( scaleFast1
  , scaleFast2
  , scaleFast2'
  , splitFieldVar
  , splitField
  , joinField
  , VbmRow
  , computeVbmChain
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Foldable (foldl, traverse_)
import Data.Reflectable (class Reflectable)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import JS.BigInt as BigInt
import Prim.Int (class Add, class Mul)
import Safe.Coerce (coerce)
import Snarky.Circuit.Curves as EllipticCurve
import Snarky.Circuit.DSL (class BasicSystem, BoolVar, EvaluationError, F(..), FVar, Snarky, addConstraint, assertEqual_, const_, exists, if_, label, mkWitnessTable, read, readCVar, throwAsProver, unpackPure)
import Snarky.Circuit.DSL as Bits
import Snarky.Circuit.Kimchi.AddComplete (Finiteness(..), addFast, sealPoint)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Constraint.Kimchi.VarBaseMul (ScaleRound)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromInt, toBigInt)
import Snarky.Data.EllipticCurve (AffinePoint(..), DoubleAddRow, doubleAddChain)
import Snarky.Types.Shifted (Type1(..))
import Type.Proxy (Proxy(..))

-- | Per-bit witness row of `varBaseMul` — exactly the five values the
-- | gadget's `exists` bodies witness for one bit step.
type VbmRow f = DoubleAddRow f

-- | The gadget's entire witness chain via `doubleAddChain` (three field
-- | inversions total instead of two per bit — Montgomery's trick over a
-- | projective walk). Each bit step is `acc' = 2·acc + Q` with
-- | `Q = (xBase, (2·b − 1)·yBase)`. The rows are the same field elements
-- | the sequential per-bit bodies produced, so witnesses stay
-- | byte-identical.
computeVbmChain
  :: forall f
   . PrimeField f
  => { xBase :: f, yBase :: f, acc0 :: AffinePoint f, bits :: Array f }
  -> Either EvaluationError (Array (VbmRow f))
computeVbmChain { xBase, yBase, acc0, bits } =
  doubleAddChain "varBaseMul" acc0
    (map (\b -> AffinePoint { x: xBase, y: yBase * (b + b - one) }) bits)

varBaseMul
  :: forall r n @nChunks @bitsUsed l f
   . FieldSizeInBits f n
  => Add bitsUsed l n
  => Mul 5 nChunks bitsUsed
  => Reflectable bitsUsed Int
  => PrimeField f
  => AffinePoint (FVar f)
  -> Type1 (FVar f)
  -> Snarky f (KimchiConstraint f) r
       { g :: AffinePoint (FVar f)
       , lsbBits :: Vector n (FVar f)
       }
varBaseMul base' (Type1 t) = label "var-base-mul" do
  -- Seal the base point once, matching OCaml's `let base = seal base in` at the top
  -- of scale_fast_unpack. This converts complex CVar expressions to simple variables,
  -- preventing redundant constraints when base is reduced in each VarBaseMul round.
  base <- sealPoint base'
  -- Use F f (field) witnesses, not Boolean — matching OCaml's Field.typ + Boolean.Unsafe.of_cvar.
  -- The VarBaseMul gate itself constrains bits to be boolean, so explicit checks are redundant.
  lsbBits <- exists do
    F vVal <- readCVar t
    pure
      $ map (\b -> if b then one else zero :: F f)
      $
        unpackPure vVal (Proxy @n)
  -- Use addFast CheckFinite to match OCaml's add_fast (default check_finite=true),
  -- where inf = Field.zero (constant). This ensures inf shares the cached constant
  -- variable with nPrev = const_ zero, matching OCaml's permutation wiring.
  { p } <- addFast CheckFinite base base
  let
    -- Take bottom bitsUsed LSB bits, then reverse to MSB-first within range.
    -- Matches OCaml's: List.take num_bits |> Array.of_list_rev_map
    lsbBitsUsed = Vector.take @bitsUsed lsbBits

    msbBitsUsed :: Vector bitsUsed (FVar f)
    msbBitsUsed = coerce $ Vector.reverse lsbBitsUsed

    chunks :: Vector nChunks (Vector 5 (FVar f))
    chunks = Vector.chunks @5 msbBitsUsed
  -- The first per-bit exists body computes the whole batched witness chain
  -- (`computeVbmChain`); the rest index into it. Advice-only: the emitted
  -- circuit is untouched.
  chainAt <- mkWitnessTable "varBaseMul" do
    AffinePoint b0 <- read @(AffinePoint f) base
    acc0 <- read @(AffinePoint f) p
    bitVals :: Array (F f) <- traverse readCVar (Vector.toUnfoldable msbBitsUsed)
    case computeVbmChain { xBase: b0.x, yBase: b0.y, acc0, bits: coerce bitVals } of
      Left e -> throwAsProver e
      Right tbl -> pure (coerce tbl :: Array (VbmRow (F f)))
  Tuple rounds { nAccPrev: nAcc, acc: g } <- mapAccumM
    ( \s bs -> do
        nAcc <- exists do
          nAccPrevVal :: F f <- readCVar s.nAccPrev
          bsVal <- read @(Vector _ _) bs
          pure $ foldl (\a b -> double a + b) nAccPrevVal bsVal
        -- Individual exists per variable to match OCaml's allocation order:
        -- s1, s1_squared, s2, x_res, y_res per bit step
        Tuple accs slopes <- Vector.unzip <<< fst <$> do
          mapAccumM
            ( \i _b -> do
                s1 <- exists (chainAt i <#> _.s1)
                -- s1Sq and s2 are allocated (in this exact order, for OCaml
                -- allocation parity) and assigned, but no constraint row and
                -- no later body reads the variables back.
                _s1Sq <- exists (chainAt i <#> _.s1Sq)
                _s2 <- exists (chainAt i <#> _.s2)
                xRes <- exists (chainAt i <#> _.xRes)
                yRes <- exists (chainAt i <#> _.yRes)
                let a' = AffinePoint { x: xRes, y: yRes }
                pure $ Tuple (Tuple a' s1) (i + 1)
            )
            s.step
            bs
        pure $ Tuple
          ( { accs: s.acc :< accs
            , bits: bs
            , slopes
            , nPrev: s.nAccPrev
            , nNext: nAcc
            , base
            } :: ScaleRound f
          )
          { nAccPrev: nAcc, acc: Vector.last accs, step: s.step + 5 }

    )
    { nAccPrev: const_ zero, acc: p, step: 0 }
    chunks
  addConstraint $ KimchiVarBaseMul $ Vector.toUnfoldable rounds
  assertEqual_ nAcc t
  pure { g, lsbBits }
  where
  double x = x + x

{-
scaleFast1 g a ~ scalarMul (fromShifted a) g

where ~ means that the LHS is a circuit which computes
the pure function on the RHS. This is used when the modulus
of the scalar field is smaller than the modulus of the circuit field.
-}
scaleFast1
  :: forall r n @nChunks @bitsUsed f _l
   . FieldSizeInBits f n
  => Add bitsUsed _l n
  => Mul 5 nChunks bitsUsed
  => Reflectable nChunks Int
  => Reflectable bitsUsed Int
  => PrimeField f
  => AffinePoint (FVar f)
  -> Type1 (FVar f)
  -> Snarky f (KimchiConstraint f) r
       (AffinePoint (FVar f))
scaleFast1 p t = label "scale-fast-1" do
  { g } <- varBaseMul @nChunks @bitsUsed p t
  pure g

{-
scaleFast2 g a ~ scalarMul (fromShifted a) g

where ~ means that the LHS is a circuit which computes
the pure function on the RHS. This is used when the modulus
of the scalar field is larger than the modulus of the circuit field.
-}
scaleFast2
  :: forall r f n @nChunks @sDiv2Bits bitsUsed _l _afterBits
   . FieldSizeInBits f n
  => Add bitsUsed _l n
  => Add sDiv2Bits _afterBits n
  => Mul 5 nChunks bitsUsed
  => Reflectable bitsUsed Int
  => Reflectable sDiv2Bits Int
  => PrimeField f
  => AffinePoint (FVar f)
  -> { sDiv2 :: FVar f, sOdd :: BoolVar f }
  -> Snarky f (KimchiConstraint f) r
       (AffinePoint (FVar f))
scaleFast2 base { sDiv2, sOdd } = label "scale-fast-2" do
  { g, lsbBits } <- varBaseMul @nChunks @bitsUsed base (Type1 sDiv2)
  let { after } = Vector.splitAt @sDiv2Bits lsbBits
  traverse_ (\x -> assertEqual_ x (const_ zero)) after
  if_ sOdd g =<< do
    negBase <- EllipticCurve.negate base
    { p } <- addFast CheckFinite g negBase
    pure p

-- | Split a field element into parity decomposition and constrain it.
-- | Witnesses (sDiv2, sOdd) where s = 2*sDiv2 + sOdd, then asserts the relationship.
splitFieldVar
  :: forall r f c
   . PrimeField f
  => BasicSystem f c
  => FVar f
  -> Snarky f c r ({ sDiv2 :: (FVar f), sOdd :: (BoolVar f) })
splitFieldVar s = label "split-field-var" do
  res@{ sDiv2, sOdd } <- exists do
    F sVal <- readCVar s
    pure $ splitField (F sVal)
  assertEqual_ s =<< do
    pure (const_ $ fromInt 2) * pure sDiv2 + pure (coerce sOdd)
  pure res

splitField :: forall f. PrimeField f => F f -> { sDiv2 :: F f, sOdd :: Boolean }
splitField (F s) =
  let
    sBigInt = toBigInt s
    sOdd = BigInt.odd sBigInt
    sDiv2 = (if sOdd then s - one else s) / fromInt 2
  in
    { sDiv2: F sDiv2, sOdd }

joinField :: forall f. PrimeField f => { sDiv2 :: f, sOdd :: Boolean } -> f
joinField { sDiv2, sOdd } =
  let
    two = fromInt 2
  in
    two * sDiv2 + (if sOdd then one else zero)

{-
scaleFast2' g s ~ [s + 2^n] * g

Like scaleFast2 but takes a raw field element instead of a pre-split Type2.
Splits s into (sDiv2, sOdd) where s = 2*sDiv2 + sOdd (parity decomposition),
constrains the split, then delegates to scaleFast2 which adds the 2^n shift
via varBaseMul. This matches OCaml's scale_fast2'.
-}
scaleFast2'
  :: forall r f n @nChunks @sDiv2Bits bitsUsed _l _afterBits
   . FieldSizeInBits f n
  => Add bitsUsed _l n
  => Add sDiv2Bits _afterBits n
  => Mul 5 nChunks bitsUsed
  => Reflectable bitsUsed Int
  => Reflectable sDiv2Bits Int
  => PrimeField f
  => AffinePoint (FVar f)
  -> FVar f
  -> Snarky f (KimchiConstraint f) r
       (AffinePoint (FVar f))
scaleFast2' base s = label "scale-fast-2-prime" do
  split <- splitFieldVar s
  scaleFast2 @nChunks @sDiv2Bits base split
