module Snarky.Curves.Pallas
  ( ScalarField
  , BaseField
  , G
  , endoCoefficient
  ) where

import Snarky.Curves.Pasta (PallasScalarField, PallasBaseField, PallasG, pallasEndoCoefficient)

type ScalarField = PallasScalarField
type BaseField = PallasBaseField
type G = PallasG

endoCoefficient :: ScalarField
endoCoefficient = pallasEndoCoefficient