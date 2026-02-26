-- | FFI bindings to Rust linearization evaluator for testing.
-- | Exposes a typeclass `LinearizationFFI` with instances for Pallas and Vesta.
module Pickles.Linearization.FFI
  ( class LinearizationFFI
  , evalLinearization
  , unnormalizedLagrangeBasis
  , vanishesOnZkAndPreviousRows
  , domainGenerator
  , domainShifts
  , proverIndexDomainLog2
  , evalWitnessPolys
  , evalCoefficientPolys
  , evalSelectorPolys
  , LinearizationInput
  , PointEval
  ) where

import Data.Vector (Vector)
import Snarky.Backend.Kimchi.Types (ProverIndex)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

-- | Input record for linearization evaluation
type LinearizationInput f =
  { alpha :: f
  , beta :: f
  , gamma :: f
  , jointCombiner :: f
  , witnessEvals :: Vector 15 (PointEval f)
  , coefficientEvals :: Vector 15 f
  , poseidonIndex :: PointEval f
  , genericIndex :: PointEval f
  , varbasemulIndex :: PointEval f
  , endomulIndex :: PointEval f
  , endomulScalarIndex :: PointEval f
  , completeAddIndex :: PointEval f
  , vanishesOnZk :: f
  , zeta :: f
  , domainLog2 :: Int
  }

-- | Polynomial evaluation at two points: zeta and zeta*omega
type PointEval f = { zeta :: f, omegaTimesZeta :: f }

-- | Typeclass encapsulating all linearization FFI operations for a given field.
-- | `f` is the evaluation field, `g` is the curve group of the circuit being verified.
-- | For Pallas linearization (Fp): f = Pallas.BaseField, g = Vesta.G
-- | For Vesta linearization (Fq): f = Vesta.BaseField, g = Pallas.G
class LinearizationFFI f g | f -> g where
  evalLinearization :: LinearizationInput f -> f
  unnormalizedLagrangeBasis :: { domainLog2 :: Int, zkRows :: Int, offset :: Int, pt :: f } -> f
  vanishesOnZkAndPreviousRows :: { domainLog2 :: Int, zkRows :: Int, pt :: f } -> f
  domainGenerator :: Int -> f
  domainShifts :: Int -> Vector 7 f
  proverIndexDomainLog2 :: ProverIndex g f -> Int
  evalWitnessPolys :: ProverIndex g f -> Vector 15 (Array f) -> f -> Vector 15 (PointEval f)
  evalCoefficientPolys :: ProverIndex g f -> f -> Vector 15 f
  evalSelectorPolys :: ProverIndex g f -> f -> Vector 6 (PointEval f)

--------------------------------------------------------------------------------
-- Private foreign imports
--------------------------------------------------------------------------------

foreign import evaluatePallasLinearization :: LinearizationInput Pallas.BaseField -> Pallas.BaseField
foreign import evaluateVestaLinearization :: LinearizationInput Vesta.BaseField -> Vesta.BaseField

foreign import pallasUnnormalizedLagrangeBasis :: { domainLog2 :: Int, zkRows :: Int, offset :: Int, pt :: Pallas.BaseField } -> Pallas.BaseField
foreign import vestaUnnormalizedLagrangeBasis :: { domainLog2 :: Int, zkRows :: Int, offset :: Int, pt :: Vesta.BaseField } -> Vesta.BaseField

foreign import pallasVanishesOnZkAndPreviousRows :: { domainLog2 :: Int, zkRows :: Int, pt :: Pallas.BaseField } -> Pallas.BaseField
foreign import vestaVanishesOnZkAndPreviousRows :: { domainLog2 :: Int, zkRows :: Int, pt :: Vesta.BaseField } -> Vesta.BaseField

foreign import pallasDomainGenerator :: Int -> Pallas.BaseField
foreign import vestaDomainGenerator :: Int -> Vesta.BaseField

foreign import pallasDomainShifts :: Int -> Vector 7 Pallas.BaseField
foreign import vestaDomainShifts :: Int -> Vector 7 Vesta.BaseField

foreign import pallasProverIndexDomainLog2 :: ProverIndex Vesta.G Pallas.BaseField -> Int
foreign import vestaProverIndexDomainLog2 :: ProverIndex Pallas.G Vesta.BaseField -> Int

foreign import pallasProverIndexWitnessEvaluations :: ProverIndex Vesta.G Pallas.BaseField -> Vector 15 (Array Pallas.BaseField) -> Pallas.BaseField -> Vector 15 (PointEval Pallas.BaseField)
foreign import vestaProverIndexWitnessEvaluations :: ProverIndex Pallas.G Vesta.BaseField -> Vector 15 (Array Vesta.BaseField) -> Vesta.BaseField -> Vector 15 (PointEval Vesta.BaseField)

foreign import pallasProverIndexCoefficientEvaluations :: ProverIndex Vesta.G Pallas.BaseField -> Pallas.BaseField -> Vector 15 Pallas.BaseField
foreign import vestaProverIndexCoefficientEvaluations :: ProverIndex Pallas.G Vesta.BaseField -> Vesta.BaseField -> Vector 15 Vesta.BaseField

foreign import pallasProverIndexSelectorEvaluations :: ProverIndex Vesta.G Pallas.BaseField -> Pallas.BaseField -> Vector 6 (PointEval Pallas.BaseField)
foreign import vestaProverIndexSelectorEvaluations :: ProverIndex Pallas.G Vesta.BaseField -> Vesta.BaseField -> Vector 6 (PointEval Vesta.BaseField)

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance LinearizationFFI Pallas.BaseField Vesta.G where
  evalLinearization = evaluatePallasLinearization
  unnormalizedLagrangeBasis = pallasUnnormalizedLagrangeBasis
  vanishesOnZkAndPreviousRows = pallasVanishesOnZkAndPreviousRows
  domainGenerator = pallasDomainGenerator
  domainShifts = pallasDomainShifts
  proverIndexDomainLog2 = pallasProverIndexDomainLog2
  evalWitnessPolys = pallasProverIndexWitnessEvaluations
  evalCoefficientPolys = pallasProverIndexCoefficientEvaluations
  evalSelectorPolys = pallasProverIndexSelectorEvaluations

instance LinearizationFFI Vesta.BaseField Pallas.G where
  evalLinearization = evaluateVestaLinearization
  unnormalizedLagrangeBasis = vestaUnnormalizedLagrangeBasis
  vanishesOnZkAndPreviousRows = vestaVanishesOnZkAndPreviousRows
  domainGenerator = vestaDomainGenerator
  domainShifts = vestaDomainShifts
  proverIndexDomainLog2 = vestaProverIndexDomainLog2
  evalWitnessPolys = vestaProverIndexWitnessEvaluations
  evalCoefficientPolys = vestaProverIndexCoefficientEvaluations
  evalSelectorPolys = vestaProverIndexSelectorEvaluations
