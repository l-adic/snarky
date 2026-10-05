module Test.Pickles.EnvironmentDumpSpec (spec) where

import Prelude

import Colog (LoggerT, Message)
import Data.Array as Array
import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Foreign (MultipleErrors)
import Pickles.Dump.Environment (EnvironmentDump, environmentDump)
import Pickles.ProofsVerified (ProofsVerified(..))
import Simple.JSON (readJSON, writeJSON)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Dump.Environment" do
  it "round-trips the shared environment through Simple.JSON" \{ pallasSrs, vestaSrs } -> liftEffect do
    let
      environment = environmentDump { pallasSrs, vestaSrs } N1
      json = writeJSON environment
    case (readJSON json :: Either MultipleErrors EnvironmentDump) of
      Left _ -> throw "environment JSON did not decode"
      Right decoded -> decoded `shouldEqual` environment

  it "retains the distinct one-predecessor unfinalized padding" \{ pallasSrs, vestaSrs } -> liftEffect do
    let { padding } = environmentDump { pallasSrs, vestaSrs } N1
    case padding.unfinalized of
      [ n0, n1, n2 ] -> do
        map _.predecessors padding.unfinalized `shouldEqual` [ 0, 1, 2 ]
        map (Array.length <<< _.fields) padding.unfinalized `shouldEqual` [ 32, 32, 32 ]
        n0.fields `shouldEqual` n2.fields
        (n0.fields == n1.fields) `shouldEqual` false
      _ -> throw "expected padding for predecessor counts zero, one and two"
    Array.length padding.wrapChallenges.raw `shouldEqual` 15
    Array.length padding.wrapChallenges.expanded `shouldEqual` 15
    Array.length padding.stepChallenges.raw `shouldEqual` 16
    Array.length padding.stepChallenges.expanded `shouldEqual` 16
    padding.wrapDomain `shouldEqual` 1
