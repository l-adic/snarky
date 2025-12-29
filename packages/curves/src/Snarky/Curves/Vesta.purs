module Snarky.Curves.Vesta
  ( ScalarField
  , BaseField
  , G
  , endoCoefficient
  ) where

import Snarky.Curves.Pasta (VestaScalarField, VestaBaseField, VestaG, vestaEndoCoefficient)

type ScalarField = VestaScalarField
type BaseField = VestaBaseField
type G = VestaG

endoCoefficient :: ScalarField
endoCoefficient = vestaEndoCoefficient