-- | Single remaining FFI surface: kimchi `Shifts::new(domain)`, which does
-- | Blake2b-seeded deterministic sampling (not pure field arithmetic).
-- |
-- | The other helpers that used to live here — `domainGenerator`,
-- | `unnormalizedLagrangeBasis`, plus the dead `evalLinearization` /
-- | `evalWitnessPolys` / `evalCoefficientPolys` / `evalSelectorPolys` /
-- | `proverIndexDomainLog2` — moved to `Snarky.Backend.Kimchi.Domain` (pure PureScript)
-- | or were removed (no PS consumer) as part of the kimchi-napi migration.
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

-- | Polynomial evaluation at two points: zeta and zeta*omega.
-- |
-- | Used throughout the pickles `PlonkChecks` modules + the Linearization
-- | Interpreter. Kept here as the canonical definition so existing
-- | imports still resolve.
type PointEval f = { zeta :: f, omegaTimesZeta :: f }

-- | `f` is the BASE field of the circuit being verified (witness/eval
-- | field). For Pallas-committed (wrap) circuits f = Pallas.BaseField = Fp;
-- | for Vesta-committed (step) circuits f = Vesta.BaseField = Fq.
-- |
-- | The class is dispatch-by-result-type / by-`pt` — call as e.g.
-- | `domainGenerator log2 :: StepField`.
class TwoAdicField f <= LinearizationFFI f where
  -- | Plonk permutation argument shift coefficients (`k_0..k_6`). Derived
  -- | deterministically from the domain via Blake2b; matches kimchi's
  -- | `Shifts::new`. This stays as FFI because it's not pure field
  -- | arithmetic (the sampling reads bytes from a hash).
  domainShifts :: Int -> Vector 7 f

-- | 2^log2-th primitive root of unity in `f`. Pure PS via `Snarky.Backend.Kimchi.Domain`.
domainGenerator :: forall @f. TwoAdicField f => Int -> f
domainGenerator = Domain.domainGenerator @f

-- | Unnormalized i-th Lagrange basis polynomial. Pure PS via `Snarky.Backend.Kimchi.Domain`.
unnormalizedLagrangeBasis
  :: forall @f
   . TwoAdicField f
  => { domainLog2 :: Int, zkRows :: Int, offset :: Int, pt :: f }
  -> f
unnormalizedLagrangeBasis = Domain.unnormalizedLagrangeBasis @f

--------------------------------------------------------------------------------
-- Foreign imports — only the Blake2b-seeded shifts sampling.
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
