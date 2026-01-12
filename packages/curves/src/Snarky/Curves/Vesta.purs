module Snarky.Curves.Vesta
  ( ScalarField
  , BaseField
  , G
  ) where

import Snarky.Curves.Pasta (VestaBaseField, VestaG, VestaScalarField)

type ScalarField = VestaScalarField
type BaseField = VestaBaseField
type G = VestaG

