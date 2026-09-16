-- | Domain quantities the linearization needs. Only the permutation
-- | shifts cross into JavaScript, because their sampling is
-- | Blake2b-seeded rather than field arithmetic; the rest forward to
-- | `Snarky.Backend.Kimchi.Domain`.
module Pickles.Linearization.FFI
  ( class LinearizationFFI
  , domainGenerator
  , domainShifts
  , unnormalizedLagrangeBasis
  , PointEval
  ) where

import Data.Vector (Vector)
import Snarky.Backend.Kimchi.Domain as Domain
import Snarky.Curves.Class (class TwoAdicField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

-- | A polynomial evaluated at `zeta` and at `zeta*omega`.
type PointEval f = { zeta :: f, omegaTimesZeta :: f }

-- | `f` is the field the verified proof's polynomials are evaluated
-- | in: `Pallas.BaseField` for a wrap proof, `Vesta.BaseField` for a
-- | step proof. Dispatch is by result type.
class TwoAdicField f <= LinearizationFFI f where
  -- | The plonk permutation shifts `k_0..k_6` of the domain.
  domainShifts :: Int -> Vector 7 f

-- | The `2^log2`-th primitive root of unity in `f`.
domainGenerator :: forall @f. TwoAdicField f => Int -> f
domainGenerator = Domain.domainGenerator @f

-- | The unnormalized `i`-th Lagrange basis polynomial at `pt`.
unnormalizedLagrangeBasis
  :: forall @f
   . TwoAdicField f
  => { domainLog2 :: Int, zkRows :: Int, offset :: Int, pt :: f }
  -> f
unnormalizedLagrangeBasis = Domain.unnormalizedLagrangeBasis @f

--------------------------------------------------------------------------------
-- Foreign imports
--------------------------------------------------------------------------------

foreign import pallasDomainShifts :: Int -> Vector 7 Pallas.BaseField
foreign import vestaDomainShifts :: Int -> Vector 7 Vesta.BaseField

--------------------------------------------------------------------------------
-- Instances
--------------------------------------------------------------------------------

instance LinearizationFFI Pallas.BaseField where
  domainShifts = pallasDomainShifts

instance LinearizationFFI Vesta.BaseField where
  domainShifts = vestaDomainShifts
