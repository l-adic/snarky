module Snarky.Curves.Pallas
  ( ScalarField
  , BaseField
  , G
  ) where

import Snarky.Curves.Pasta (PallasBaseField, PallasG, PallasScalarField)

type ScalarField = PallasScalarField
type BaseField = PallasBaseField
type G = PallasG

