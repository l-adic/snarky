-- | FFI bindings to Rust linearization evaluator for testing
module Pickles.Linearization.FFI
  ( evaluatePallasLinearization
  , evaluateVestaLinearization
  , evaluatePallasLinearizationPure
  , evaluateVestaLinearizationPure
  , pallasUnnormalizedLagrangeBasis
  , vestaUnnormalizedLagrangeBasis
  , pallasVanishesOnZkAndPreviousRows
  , vestaVanishesOnZkAndPreviousRows
  ) where

import Effect (Effect)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

-- | Evaluate Pallas linearization using Rust/Kimchi
-- | All field elements are passed directly (no hex conversion needed)
foreign import evaluatePallasLinearizationImpl
  :: Pallas.BaseField -- alpha
  -> Pallas.BaseField -- beta
  -> Pallas.BaseField -- gamma
  -> Pallas.BaseField -- jointCombiner
  -> Array Pallas.BaseField -- witnessEvals (flattened: [col0_curr, col0_next, col1_curr, ...])
  -> Array Pallas.BaseField -- coefficientEvals
  -> Array Pallas.BaseField -- poseidonIndex [curr, next]
  -> Array Pallas.BaseField -- genericIndex [curr, next]
  -> Array Pallas.BaseField -- varbasemulIndex [curr, next]
  -> Array Pallas.BaseField -- endomulIndex [curr, next]
  -> Array Pallas.BaseField -- endomulScalarIndex [curr, next]
  -> Array Pallas.BaseField -- completeAddIndex [curr, next]
  -> Pallas.BaseField -- vanishesOnZk
  -> Pallas.BaseField -- zeta
  -> Int -- domainLog2
  -> Effect Pallas.BaseField

-- | Evaluate Vesta linearization using Rust/Kimchi
foreign import evaluateVestaLinearizationImpl
  :: Vesta.BaseField -- alpha
  -> Vesta.BaseField -- beta
  -> Vesta.BaseField -- gamma
  -> Vesta.BaseField -- jointCombiner
  -> Array Vesta.BaseField -- witnessEvals (flattened)
  -> Array Vesta.BaseField -- coefficientEvals
  -> Array Vesta.BaseField -- poseidonIndex [curr, next]
  -> Array Vesta.BaseField -- genericIndex [curr, next]
  -> Array Vesta.BaseField -- varbasemulIndex [curr, next]
  -> Array Vesta.BaseField -- endomulIndex [curr, next]
  -> Array Vesta.BaseField -- endomulScalarIndex [curr, next]
  -> Array Vesta.BaseField -- completeAddIndex [curr, next]
  -> Vesta.BaseField -- vanishesOnZk
  -> Vesta.BaseField -- zeta
  -> Int -- domainLog2
  -> Effect Vesta.BaseField

-- | Wrapper for Pallas linearization evaluation
evaluatePallasLinearization
  :: { alpha :: Pallas.BaseField
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
  -> Effect Pallas.BaseField
evaluatePallasLinearization input =
  evaluatePallasLinearizationImpl
    input.alpha
    input.beta
    input.gamma
    input.jointCombiner
    input.witnessEvals
    input.coefficientEvals
    input.poseidonIndex
    input.genericIndex
    input.varbasemulIndex
    input.endomulIndex
    input.endomulScalarIndex
    input.completeAddIndex
    input.vanishesOnZk
    input.zeta
    input.domainLog2

-- | Wrapper for Vesta linearization evaluation
evaluateVestaLinearization
  :: { alpha :: Vesta.BaseField
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
  -> Effect Vesta.BaseField
evaluateVestaLinearization input =
  evaluateVestaLinearizationImpl
    input.alpha
    input.beta
    input.gamma
    input.jointCombiner
    input.witnessEvals
    input.coefficientEvals
    input.poseidonIndex
    input.genericIndex
    input.varbasemulIndex
    input.endomulIndex
    input.endomulScalarIndex
    input.completeAddIndex
    input.vanishesOnZk
    input.zeta
    input.domainLog2

-- ============================================================================
-- Pure versions (for QuickCheck and other pure contexts)
-- ============================================================================

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

foreign import evaluatePallasLinearizationPureImpl
  :: PallasLinearizationInput -> Pallas.BaseField

evaluatePallasLinearizationPure :: PallasLinearizationInput -> Pallas.BaseField
evaluatePallasLinearizationPure = evaluatePallasLinearizationPureImpl

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

foreign import evaluateVestaLinearizationPureImpl
  :: VestaLinearizationInput -> Vesta.BaseField

evaluateVestaLinearizationPure :: VestaLinearizationInput -> Vesta.BaseField
evaluateVestaLinearizationPure = evaluateVestaLinearizationPureImpl

-- ============================================================================
-- Domain polynomial functions (pure - no Effect needed)
-- ============================================================================

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
