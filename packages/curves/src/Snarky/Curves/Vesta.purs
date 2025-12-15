module Snarky.Curves.Vesta
  ( ScalarField
  , BaseField
  , G
  ) where

import Snarky.Curves.Pasta (VestaScalarField, VestaBaseField, VestaG)

type ScalarField = VestaScalarField
type BaseField = VestaBaseField
type G = VestaG