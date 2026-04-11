module Test.Pickles.Prove.Pure.EvalsOfSplit
  ( spec
  ) where

-- | Unit tests for `Pickles.Prove.Pure.EvalsOfSplit.actualEvaluation`.
-- |
-- | `actualEvaluation rounds pt [a0, a1, ..., a_{n-1}]` computes
-- |
-- |   a0 + ptN · a1 + ptN^2 · a2 + ... + ptN^(n-1) · a_{n-1}
-- |
-- | where `ptN = pt^(2^rounds)`. All expected values below are
-- | hand-computed from that formula.

import Prelude

import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Pickles.Prove.Pure.Common (actualEvaluation)
import Snarky.Curves.Class (fromBigInt)
import Snarky.Curves.Pallas as Pallas
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

type F = Pallas.BaseField

int :: Int -> F
int = fromBigInt <<< BigInt.fromInt

spec :: Spec Unit
spec = describe "Pickles.Prove.Pure.EvalsOfSplit.actualEvaluation" do
  it "returns zero on an empty array" do
    let result = actualEvaluation 0 (int 5) []
    liftEffect $ result `shouldEqual` (int 0)

  it "returns the single chunk unchanged for a 1-element array" do
    -- a0 = 7, pt irrelevant (no higher terms)
    let result = actualEvaluation 0 (int 5) [ int 7 ]
    liftEffect $ result `shouldEqual` (int 7)

  it "rounds=0, pt=3, [1,2] → 1 + 3·2 = 7" do
    -- ptN = 3^(2^0) = 3^1 = 3
    -- result = 1 + 3·2 = 7
    let result = actualEvaluation 0 (int 3) [ int 1, int 2 ]
    liftEffect $ result `shouldEqual` (int 7)

  it "rounds=0, pt=5, [1,2,3] → 1 + 5·2 + 25·3 = 86" do
    -- ptN = 5^1 = 5
    -- result = 1 + 5·2 + 5²·3 = 1 + 10 + 75 = 86
    let result = actualEvaluation 0 (int 5) [ int 1, int 2, int 3 ]
    liftEffect $ result `shouldEqual` (int 86)

  it "rounds=1, pt=2, [1,2] → 1 + 4·2 = 9" do
    -- ptN = 2^(2^1) = 2^2 = 4
    -- result = 1 + 4·2 = 9
    let result = actualEvaluation 1 (int 2) [ int 1, int 2 ]
    liftEffect $ result `shouldEqual` (int 9)

  it "rounds=1, pt=2, [3, 5, 7] → 3 + 4·5 + 16·7 = 135" do
    -- ptN = 2^2 = 4
    -- result = 3 + 4·5 + 16·7 = 3 + 20 + 112 = 135
    let result = actualEvaluation 1 (int 2) [ int 3, int 5, int 7 ]
    liftEffect $ result `shouldEqual` (int 135)

  it "rounds=2, pt=2, [1, 1] → 1 + 16·1 = 17" do
    -- ptN = 2^(2^2) = 2^4 = 16
    -- result = 1 + 16·1 = 17
    let result = actualEvaluation 2 (int 2) [ int 1, int 1 ]
    liftEffect $ result `shouldEqual` (int 17)

  it "rounds=3, pt=2, [0, 1] → 256" do
    -- ptN = 2^(2^3) = 2^8 = 256
    -- result = 0 + 256·1 = 256
    let result = actualEvaluation 3 (int 2) [ int 0, int 1 ]
    liftEffect $ result `shouldEqual` (int 256)
