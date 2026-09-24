module Test.Pickles.WrapDomainShiftsSpec (spec) where

import Prelude

import Colog (LoggerT, Message)
import Data.Fin (getFinite)
import Data.Foldable (for_)
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Pickles.Field (WrapField)
import Pickles.Linearization.FFI (domainShifts)
import Pickles.ProofsVerified (allPossibleDomainLog2s, wrapDomainShifts)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | `Pickles.Pseudo.toDomain` emits one shift set whichever wrap domain
-- | it selects; this pins that the three domains share it.
spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.ProofsVerified.wrapDomainShifts" do
  it "is every wrap domain's shift set" \_ -> liftAff do
    for_ allPossibleDomainLog2s \log2 ->
      domainShifts @WrapField (getFinite log2) `shouldEqual` wrapDomainShifts
