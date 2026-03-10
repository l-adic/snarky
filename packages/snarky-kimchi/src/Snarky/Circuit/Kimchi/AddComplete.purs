module Snarky.Circuit.Kimchi.AddComplete where

import Prelude

import Control.Apply (lift2)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, Snarky, UnChecked(..), addConstraint, exists, false_, label, read, readCVar, seal)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Curves.Class (fromInt)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Seal an affine point: reduce each coordinate to a single variable if complex.
sealPoint
  :: forall f c t m
   . CircuitM f c t m
  => AffinePoint (FVar f)
  -> Snarky c t m (AffinePoint (FVar f))
sealPoint p = label "seal_point" do
  -- OCaml's seal = Tuple_lib.Double.map ~f:Utils.seal evaluates y before x
  -- (right-to-left tuple construction), so we must seal y first to match.
  y <- label "seal_y" $ seal p.y
  x <- label "seal_x" $ seal p.x
  pure { x, y }

-- | OCaml: add_fast ?(check_finite = true/false)
-- |   CheckFinite (= true):  inf is constant zero, no witness needed
-- |   DontCheckFinite (= false): inf is a fresh witness variable
data Finiteness = CheckFinite | DontCheckFinite

-- | Complete addition assuming finite inputs.
-- | OCaml: add_fast (uses default check_finite=true)
addComplete
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => AffinePoint (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky (KimchiConstraint f) t m
       { p :: AffinePoint (FVar f)
       , isInfinity :: BoolVar f
       }
addComplete = addFast CheckFinite

-- | Complete addition with explicit finiteness control.
-- | OCaml: add_fast ~check_finite:true/false
addFast
  :: forall f t m
   . CircuitM f (KimchiConstraint f) t m
  => Finiteness
  -> AffinePoint (FVar f)
  -> AffinePoint (FVar f)
  -> Snarky (KimchiConstraint f) t m
       { p :: AffinePoint (FVar f)
       , isInfinity :: BoolVar f
       }
addFast finiteness p1' p2' = label "add_fast" do
  p1 <- sealPoint p1'
  p2 <- sealPoint p2'
  UnChecked sameX <- exists $ UnChecked <$>
    lift2 eq (readCVar p1.x) (readCVar p2.x)
  inf <- case finiteness of
    CheckFinite -> pure false_
    DontCheckFinite -> do
      UnChecked r <- exists $ UnChecked <$> do
        let sameY = lift2 eq (readCVar p1.y) (readCVar p2.y)
        read sameX && not sameY
      pure r
  infZ <- exists $
    lift2 eq (readCVar p1.y) (readCVar p2.y) >>=
      if _ then zero
      else
        read sameX >>=
          if _ then recip (readCVar p2.y - readCVar p1.y)
          else zero
  x21Inv <- exists $
    read sameX >>=
      if _ then zero
      else recip (readCVar p2.x - readCVar p1.x)
  s <- exists $
    read sameX >>=
      if _ then do
        x1 <- readCVar p1.x
        y1 <- readCVar p1.y
        pure $ (fromInt 3 * x1 * x1) / (fromInt 2 * y1)
      else
        (readCVar p2.y - readCVar p1.y) / (readCVar p2.x - readCVar p1.x)
  x3 <- exists
    let
      sVal = readCVar s
    in
      sVal * sVal - (readCVar p1.x + readCVar p2.x)
  y3 <- exists $
    readCVar s * (readCVar p1.x - readCVar x3) - readCVar p1.y
  addConstraint $ KimchiAddComplete
    { p1, p2, sameX: coerce sameX, inf: coerce inf, infZ, x21Inv, s, p3: { x: x3, y: y3 } }
  pure
    { p: { x: x3, y: y3 }
    , isInfinity: inf
    }
