module Snarky.Curves.Pallas
  ( ScalarField
  , BaseField
  , G
  ) where

import Snarky.Curves.Pasta (PallasScalarField, PallasBaseField, PallasG)

type ScalarField = PallasScalarField
type BaseField = PallasBaseField
type G = PallasG

