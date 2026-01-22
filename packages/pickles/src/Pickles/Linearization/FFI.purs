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
  , pallasWitnessToEvaluations
  , vestaWitnessToEvaluations
  , pallasGatesToCoefficientEvaluations
  , pallasGatesToSelectorEvaluations
  , vestaGatesToCoefficientEvaluations
  , vestaGatesToSelectorEvaluations
  , pallasProverIndexWitnessEvaluations
  , pallasProverIndexCoefficientEvaluations
  , pallasProverIndexSelectorEvaluations
  , vestaProverIndexWitnessEvaluations
  , vestaProverIndexCoefficientEvaluations
  , vestaProverIndexSelectorEvaluations
  ) where

import Snarky.Backend.Kimchi.Types (Gate, ProverIndex)
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
-- | When zkRows > 0, offsets into the ZK padding region
foreign import pallasUnnormalizedLagrangeBasisImpl
  :: { domainLog2 :: Int
     , zkRows :: Int
     , offset :: Int
     , pt :: Pallas.BaseField
     }
  -> Pallas.BaseField

pallasUnnormalizedLagrangeBasis
  :: { domainLog2 :: Int
     , zkRows :: Int
     , offset :: Int
     , pt :: Pallas.BaseField
     }
  -> Pallas.BaseField
pallasUnnormalizedLagrangeBasis = pallasUnnormalizedLagrangeBasisImpl

-- | Compute unnormalized Lagrange basis for Vesta base field
foreign import vestaUnnormalizedLagrangeBasisImpl
  :: { domainLog2 :: Int
     , zkRows :: Int
     , offset :: Int
     , pt :: Vesta.BaseField
     }
  -> Vesta.BaseField

vestaUnnormalizedLagrangeBasis
  :: { domainLog2 :: Int
     , zkRows :: Int
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

-- | Compute polynomial evaluations from a Pallas witness matrix.
-- | Given 15 witness columns, interpolates each into a polynomial and
-- | evaluates at zeta and zeta*omega.
-- | Returns flattened array: [col0_zeta, col0_zeta_omega, col1_zeta, ...]
foreign import pallasWitnessToEvaluationsImpl
  :: Array (Array Pallas.BaseField)
  -> Pallas.BaseField
  -> Int
  -> Array Pallas.BaseField

pallasWitnessToEvaluations
  :: { witness :: Array (Array Pallas.BaseField)
     , zeta :: Pallas.BaseField
     , domainLog2 :: Int
     }
  -> Array Pallas.BaseField
pallasWitnessToEvaluations { witness, zeta, domainLog2 } =
  pallasWitnessToEvaluationsImpl witness zeta domainLog2

-- | Compute polynomial evaluations from a Vesta witness matrix.
foreign import vestaWitnessToEvaluationsImpl
  :: Array (Array Vesta.BaseField)
  -> Vesta.BaseField
  -> Int
  -> Array Vesta.BaseField

vestaWitnessToEvaluations
  :: { witness :: Array (Array Vesta.BaseField)
     , zeta :: Vesta.BaseField
     , domainLog2 :: Int
     }
  -> Array Vesta.BaseField
vestaWitnessToEvaluations { witness, zeta, domainLog2 } =
  vestaWitnessToEvaluationsImpl witness zeta domainLog2

-- | Compute coefficient polynomial evaluations from Vesta circuit gates.
-- | For Pallas linearization (which verifies Vesta circuits), we need coefficient
-- | evaluations in Fp (= Pallas.BaseField = Vesta.ScalarField).
-- | Note: Vesta gates use Vesta.ScalarField which equals Pallas.BaseField,
-- | so the field types align correctly.
-- | Returns array of 15 coefficient evaluations at zeta.
foreign import pallasGatesToCoefficientEvaluationsImpl
  :: Array (Gate Vesta.ScalarField)
  -> Pallas.BaseField
  -> Int
  -> Array Pallas.BaseField

pallasGatesToCoefficientEvaluations
  :: { gates :: Array (Gate Vesta.ScalarField)
     , zeta :: Pallas.BaseField
     , domainLog2 :: Int
     }
  -> Array Pallas.BaseField
pallasGatesToCoefficientEvaluations { gates, zeta, domainLog2 } =
  pallasGatesToCoefficientEvaluationsImpl gates zeta domainLog2

-- | Compute selector polynomial evaluations from Vesta circuit gates.
-- | Returns flattened array: [poseidon_zeta, poseidon_zeta_omega, generic_zeta, ...]
foreign import pallasGatesToSelectorEvaluationsImpl
  :: Array (Gate Vesta.ScalarField)
  -> Pallas.BaseField
  -> Int
  -> Array Pallas.BaseField

pallasGatesToSelectorEvaluations
  :: { gates :: Array (Gate Vesta.ScalarField)
     , zeta :: Pallas.BaseField
     , domainLog2 :: Int
     }
  -> Array Pallas.BaseField
pallasGatesToSelectorEvaluations { gates, zeta, domainLog2 } =
  pallasGatesToSelectorEvaluationsImpl gates zeta domainLog2

-- | Compute coefficient polynomial evaluations from Pallas circuit gates.
-- | For Vesta linearization (which verifies Pallas circuits).
foreign import vestaGatesToCoefficientEvaluationsImpl
  :: Array (Gate Pallas.ScalarField)
  -> Vesta.BaseField
  -> Int
  -> Array Vesta.BaseField

vestaGatesToCoefficientEvaluations
  :: { gates :: Array (Gate Pallas.ScalarField)
     , zeta :: Vesta.BaseField
     , domainLog2 :: Int
     }
  -> Array Vesta.BaseField
vestaGatesToCoefficientEvaluations { gates, zeta, domainLog2 } =
  vestaGatesToCoefficientEvaluationsImpl gates zeta domainLog2

-- | Compute selector polynomial evaluations from Pallas circuit gates.
foreign import vestaGatesToSelectorEvaluationsImpl
  :: Array (Gate Pallas.ScalarField)
  -> Vesta.BaseField
  -> Int
  -> Array Vesta.BaseField

vestaGatesToSelectorEvaluations
  :: { gates :: Array (Gate Pallas.ScalarField)
     , zeta :: Vesta.BaseField
     , domainLog2 :: Int
     }
  -> Array Vesta.BaseField
vestaGatesToSelectorEvaluations { gates, zeta, domainLog2 } =
  vestaGatesToSelectorEvaluationsImpl gates zeta domainLog2

--------------------------------------------------------------------------------
-- Prover Index evaluation functions (for linearization testing with valid witnesses)
--------------------------------------------------------------------------------

-- | Compute witness polynomial evaluations from a Vesta prover index.
-- | For Pallas linearization (which verifies Vesta circuits).
-- | Returns 30 values: 15 columns × 2 points (zeta, zeta*omega).
foreign import pallasProverIndexWitnessEvaluationsImpl
  :: ProverIndex Vesta.G Vesta.ScalarField
  -> Array (Array Vesta.ScalarField)
  -> Vesta.ScalarField
  -> Array Vesta.ScalarField

pallasProverIndexWitnessEvaluations
  :: { proverIndex :: ProverIndex Vesta.G Vesta.ScalarField
     , witnessColumns :: Array (Array Vesta.ScalarField)
     , zeta :: Vesta.ScalarField
     }
  -> Array Vesta.ScalarField
pallasProverIndexWitnessEvaluations { proverIndex, witnessColumns, zeta } =
  pallasProverIndexWitnessEvaluationsImpl proverIndex witnessColumns zeta

-- | Compute coefficient polynomial evaluations from a Vesta prover index.
-- | Returns 15 coefficient evaluations at zeta.
foreign import pallasProverIndexCoefficientEvaluationsImpl
  :: ProverIndex Vesta.G Vesta.ScalarField
  -> Vesta.ScalarField
  -> Array Vesta.ScalarField

pallasProverIndexCoefficientEvaluations
  :: { proverIndex :: ProverIndex Vesta.G Vesta.ScalarField
     , zeta :: Vesta.ScalarField
     }
  -> Array Vesta.ScalarField
pallasProverIndexCoefficientEvaluations { proverIndex, zeta } =
  pallasProverIndexCoefficientEvaluationsImpl proverIndex zeta

-- | Compute selector polynomial evaluations from a Vesta prover index.
-- | Returns 12 values: 6 gate types × 2 points (zeta, zeta*omega).
foreign import pallasProverIndexSelectorEvaluationsImpl
  :: ProverIndex Vesta.G Vesta.ScalarField
  -> Vesta.ScalarField
  -> Array Vesta.ScalarField

pallasProverIndexSelectorEvaluations
  :: { proverIndex :: ProverIndex Vesta.G Vesta.ScalarField
     , zeta :: Vesta.ScalarField
     }
  -> Array Vesta.ScalarField
pallasProverIndexSelectorEvaluations { proverIndex, zeta } =
  pallasProverIndexSelectorEvaluationsImpl proverIndex zeta

-- | Compute witness polynomial evaluations from a Pallas prover index.
-- | For Vesta linearization (which verifies Pallas circuits).
foreign import vestaProverIndexWitnessEvaluationsImpl
  :: ProverIndex Pallas.G Pallas.ScalarField
  -> Array (Array Pallas.ScalarField)
  -> Pallas.ScalarField
  -> Array Pallas.ScalarField

vestaProverIndexWitnessEvaluations
  :: { proverIndex :: ProverIndex Pallas.G Pallas.ScalarField
     , witnessColumns :: Array (Array Pallas.ScalarField)
     , zeta :: Pallas.ScalarField
     }
  -> Array Pallas.ScalarField
vestaProverIndexWitnessEvaluations { proverIndex, witnessColumns, zeta } =
  vestaProverIndexWitnessEvaluationsImpl proverIndex witnessColumns zeta

-- | Compute coefficient polynomial evaluations from a Pallas prover index.
foreign import vestaProverIndexCoefficientEvaluationsImpl
  :: ProverIndex Pallas.G Pallas.ScalarField
  -> Pallas.ScalarField
  -> Array Pallas.ScalarField

vestaProverIndexCoefficientEvaluations
  :: { proverIndex :: ProverIndex Pallas.G Pallas.ScalarField
     , zeta :: Pallas.ScalarField
     }
  -> Array Pallas.ScalarField
vestaProverIndexCoefficientEvaluations { proverIndex, zeta } =
  vestaProverIndexCoefficientEvaluationsImpl proverIndex zeta

-- | Compute selector polynomial evaluations from a Pallas prover index.
foreign import vestaProverIndexSelectorEvaluationsImpl
  :: ProverIndex Pallas.G Pallas.ScalarField
  -> Pallas.ScalarField
  -> Array Pallas.ScalarField

vestaProverIndexSelectorEvaluations
  :: { proverIndex :: ProverIndex Pallas.G Pallas.ScalarField
     , zeta :: Pallas.ScalarField
     }
  -> Array Pallas.ScalarField
vestaProverIndexSelectorEvaluations { proverIndex, zeta } =
  vestaProverIndexSelectorEvaluationsImpl proverIndex zeta
