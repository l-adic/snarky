-- | FFI bindings to Rust linearization evaluator for testing.
-- | Exposes a typeclass `LinearizationFFI` with instances for Pallas and Vesta.
module Pickles.Linearization.FFI
  ( class LinearizationFFI
  , evaluateLinearization
  , unnormalizedLagrangeBasis
  , vanishesOnZkAndPreviousRows
  , proverIndexWitnessEvaluations
  , proverIndexCoefficientEvaluations
  , proverIndexSelectorEvaluations
  , LinearizationInput
  , PointEval
  ) where

import Snarky.Backend.Kimchi.Types (ProverIndex)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

-- | Input record for linearization evaluation
type LinearizationInput f =
  { alpha :: f
  , beta :: f
  , gamma :: f
  , jointCombiner :: f
  , witnessEvals :: Array f
  , coefficientEvals :: Array f
  , poseidonIndex :: Array f
  , genericIndex :: Array f
  , varbasemulIndex :: Array f
  , endomulIndex :: Array f
  , endomulScalarIndex :: Array f
  , completeAddIndex :: Array f
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
  evaluateLinearization :: LinearizationInput f -> f
  unnormalizedLagrangeBasis :: { domainLog2 :: Int, zkRows :: Int, offset :: Int, pt :: f } -> f
  vanishesOnZkAndPreviousRows :: { domainLog2 :: Int, zkRows :: Int, pt :: f } -> f
  proverIndexWitnessEvaluations :: { proverIndex :: ProverIndex g f, witnessColumns :: Array (Array f), zeta :: f } -> Array (PointEval f)
  proverIndexCoefficientEvaluations :: { proverIndex :: ProverIndex g f, zeta :: f } -> Array f
  proverIndexSelectorEvaluations :: { proverIndex :: ProverIndex g f, zeta :: f } -> Array (PointEval f)

--------------------------------------------------------------------------------
-- Private foreign imports
--------------------------------------------------------------------------------

foreign import evaluatePallasLinearization :: LinearizationInput Pallas.BaseField -> Pallas.BaseField
foreign import evaluateVestaLinearization :: LinearizationInput Vesta.BaseField -> Vesta.BaseField

foreign import pallasUnnormalizedLagrangeBasis :: { domainLog2 :: Int, zkRows :: Int, offset :: Int, pt :: Pallas.BaseField } -> Pallas.BaseField
foreign import vestaUnnormalizedLagrangeBasis :: { domainLog2 :: Int, zkRows :: Int, offset :: Int, pt :: Vesta.BaseField } -> Vesta.BaseField

foreign import pallasVanishesOnZkAndPreviousRows :: { domainLog2 :: Int, zkRows :: Int, pt :: Pallas.BaseField } -> Pallas.BaseField
foreign import vestaVanishesOnZkAndPreviousRows :: { domainLog2 :: Int, zkRows :: Int, pt :: Vesta.BaseField } -> Vesta.BaseField

foreign import pallasProverIndexWitnessEvaluations :: { proverIndex :: ProverIndex Vesta.G Pallas.BaseField, witnessColumns :: Array (Array Pallas.BaseField), zeta :: Pallas.BaseField } -> Array (PointEval Pallas.BaseField)
foreign import vestaProverIndexWitnessEvaluations :: { proverIndex :: ProverIndex Pallas.G Vesta.BaseField, witnessColumns :: Array (Array Vesta.BaseField), zeta :: Vesta.BaseField } -> Array (PointEval Vesta.BaseField)

foreign import pallasProverIndexCoefficientEvaluations :: { proverIndex :: ProverIndex Vesta.G Pallas.BaseField, zeta :: Pallas.BaseField } -> Array Pallas.BaseField
foreign import vestaProverIndexCoefficientEvaluations :: { proverIndex :: ProverIndex Pallas.G Vesta.BaseField, zeta :: Vesta.BaseField } -> Array Vesta.BaseField

foreign import pallasProverIndexSelectorEvaluations :: { proverIndex :: ProverIndex Vesta.G Pallas.BaseField, zeta :: Pallas.BaseField } -> Array (PointEval Pallas.BaseField)
foreign import vestaProverIndexSelectorEvaluations :: { proverIndex :: ProverIndex Pallas.G Vesta.BaseField, zeta :: Vesta.BaseField } -> Array (PointEval Vesta.BaseField)

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance LinearizationFFI Pallas.BaseField Vesta.G where
  evaluateLinearization = evaluatePallasLinearization
  unnormalizedLagrangeBasis = pallasUnnormalizedLagrangeBasis
  vanishesOnZkAndPreviousRows = pallasVanishesOnZkAndPreviousRows
  proverIndexWitnessEvaluations = pallasProverIndexWitnessEvaluations
  proverIndexCoefficientEvaluations = pallasProverIndexCoefficientEvaluations
  proverIndexSelectorEvaluations = pallasProverIndexSelectorEvaluations

instance LinearizationFFI Vesta.BaseField Pallas.G where
  evaluateLinearization = evaluateVestaLinearization
  unnormalizedLagrangeBasis = vestaUnnormalizedLagrangeBasis
  vanishesOnZkAndPreviousRows = vestaVanishesOnZkAndPreviousRows
  proverIndexWitnessEvaluations = vestaProverIndexWitnessEvaluations
  proverIndexCoefficientEvaluations = vestaProverIndexCoefficientEvaluations
  proverIndexSelectorEvaluations = vestaProverIndexSelectorEvaluations
