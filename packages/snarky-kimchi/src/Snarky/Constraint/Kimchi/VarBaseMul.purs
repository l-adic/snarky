module Snarky.Constraint.Kimchi.VarBaseMul where

import Snarky.Circuit.Types (FVar)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.Vector (Vector)

type ScaleRound f =
  { accs :: Vector 6 (AffinePoint (FVar f))
  , bits :: Vector 5 (FVar f)
  , slopes :: Vector 5 (FVar f)
  , nPrev :: FVar f
  , nNext :: FVar f
  , base :: AffinePoint (FVar f)
  }

type VarBaseMul f = Array (ScaleRound f)