-- | FFI bindings to Rust linearization evaluator for testing
module Pickles.Linearization.FFI
  ( evaluatePallasLinearization
  , evaluateVestaLinearization
  , PallasLinearizationInput
  , VestaLinearizationInput
  , pallasUnnormalizedLagrangeBasis
  , vestaUnnormalizedLagrangeBasis
  , pallasVanishesOnZkAndPreviousRows
  , vestaVanishesOnZkAndPreviousRows
  ) where

import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

-- | Input record for Pallas linearization evaluation
type PallasLinearizationInput =
  { alpha :: Pallas.BaseField
  , beta :: Pallas.BaseField
  , gamma :: Pallas.BaseField
  , jointCombiner :: Pallas.BaseField
  , witnessEvals :: Array Pallas.BaseField
  , coefficientEvals :: Array Pallas.BaseField
  , poseidonIndex :: Array Pallas.BaseField
  , genericIndex :: Array Pallas.BaseField
  , varbasemulIndex :: Array Pallas.BaseField
  , endomulIndex :: Array Pallas.BaseField
  , endomulScalarIndex :: Array Pallas.BaseField
  , completeAddIndex :: Array Pallas.BaseField
  , vanishesOnZk :: Pallas.BaseField
  , zeta :: Pallas.BaseField
  , domainLog2 :: Int
  }

-- | Evaluate Pallas linearization using Rust/Kimchi
foreign import evaluatePallasLinearizationImpl :: PallasLinearizationInput -> Pallas.BaseField

evaluatePallasLinearization :: PallasLinearizationInput -> Pallas.BaseField
evaluatePallasLinearization = evaluatePallasLinearizationImpl

-- | Input record for Vesta linearization evaluation
type VestaLinearizationInput =
  { alpha :: Vesta.BaseField
  , beta :: Vesta.BaseField
  , gamma :: Vesta.BaseField
  , jointCombiner :: Vesta.BaseField
  , witnessEvals :: Array Vesta.BaseField
  , coefficientEvals :: Array Vesta.BaseField
  , poseidonIndex :: Array Vesta.BaseField
  , genericIndex :: Array Vesta.BaseField
  , varbasemulIndex :: Array Vesta.BaseField
  , endomulIndex :: Array Vesta.BaseField
  , endomulScalarIndex :: Array Vesta.BaseField
  , completeAddIndex :: Array Vesta.BaseField
  , vanishesOnZk :: Vesta.BaseField
  , zeta :: Vesta.BaseField
  , domainLog2 :: Int
  }

-- | Evaluate Vesta linearization using Rust/Kimchi
foreign import evaluateVestaLinearizationImpl :: VestaLinearizationInput -> Vesta.BaseField

evaluateVestaLinearization :: VestaLinearizationInput -> Vesta.BaseField
evaluateVestaLinearization = evaluateVestaLinearizationImpl

-- | Compute unnormalized Lagrange basis for Pallas base field
-- | (pt^n - 1) / (pt - ω^i)
foreign import pallasUnnormalizedLagrangeBasisImpl
  :: { domainLog2 :: Int
     , zkRows :: Boolean
     , offset :: Int
     , pt :: Pallas.BaseField
     }
  -> Pallas.BaseField

pallasUnnormalizedLagrangeBasis
  :: { domainLog2 :: Int
     , zkRows :: Boolean
     , offset :: Int
     , pt :: Pallas.BaseField
     }
  -> Pallas.BaseField
pallasUnnormalizedLagrangeBasis = pallasUnnormalizedLagrangeBasisImpl

-- | Compute unnormalized Lagrange basis for Vesta base field
foreign import vestaUnnormalizedLagrangeBasisImpl
  :: { domainLog2 :: Int
     , zkRows :: Boolean
     , offset :: Int
     , pt :: Vesta.BaseField
     }
  -> Vesta.BaseField

vestaUnnormalizedLagrangeBasis
  :: { domainLog2 :: Int
     , zkRows :: Boolean
     , offset :: Int
     , pt :: Vesta.BaseField
     }
  -> Vesta.BaseField
vestaUnnormalizedLagrangeBasis = vestaUnnormalizedLagrangeBasisImpl

-- | Compute vanishes on ZK and previous rows for Pallas base field
-- | ∏_{j=0}^{zkRows} (pt - ω^(n - zkRows - 1 + j))
foreign import pallasVanishesOnZkAndPreviousRowsImpl
  :: { domainLog2 :: Int
     , zkRows :: Int
     , pt :: Pallas.BaseField
     }
  -> Pallas.BaseField

pallasVanishesOnZkAndPreviousRows
  :: { domainLog2 :: Int
     , zkRows :: Int
     , pt :: Pallas.BaseField
     }
  -> Pallas.BaseField
pallasVanishesOnZkAndPreviousRows = pallasVanishesOnZkAndPreviousRowsImpl

-- | Compute vanishes on ZK and previous rows for Vesta base field
foreign import vestaVanishesOnZkAndPreviousRowsImpl
  :: { domainLog2 :: Int
     , zkRows :: Int
     , pt :: Vesta.BaseField
     }
  -> Vesta.BaseField

vestaVanishesOnZkAndPreviousRows
  :: { domainLog2 :: Int
     , zkRows :: Int
     , pt :: Vesta.BaseField
     }
  -> Vesta.BaseField
vestaVanishesOnZkAndPreviousRows = vestaVanishesOnZkAndPreviousRowsImpl
