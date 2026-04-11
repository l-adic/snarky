module Test.Pickles.Prove.Pure.BulletproofB
  ( spec
  ) where

-- | Unit tests for `Pickles.Prove.Pure.BulletproofB.computeBpChalsAndB`.
-- |
-- | These verify the algebraic relationships the function asserts:
-- |
-- |   chals[i] = toFieldPure rawPrechallenges[i] endo
-- |   b = bPoly chals zeta + r · bPoly chals zetaw
-- |
-- | We don't hand-compute the endo expansion results (they depend on
-- | the 128-bit challenge bit decomposition and the endo coefficient);
-- | instead we cross-check against the underlying helpers directly.

import Prelude

import Data.Maybe (fromJust)
import Data.Vector as Vector
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.IPA (bPoly)
import Pickles.Prove.Pure.Common (computeBpChalsAndB)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Curves.Class (fromBigInt)
import Snarky.Curves.Pallas as Pallas
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

type F = Pallas.BaseField

int :: Int -> F
int = fromBigInt <<< BigInt.fromInt

-- | Construct a small SizedF 128 holding an Int-sized value. Crashes
-- | if n >= 2^128, which never happens for small inputs.
mkChal :: Int -> SizedF 128 F
mkChal n = unsafePartial $ fromJust $ SizedF.fromField @128 (int n)

spec :: Spec Unit
spec = describe "Pickles.Prove.Pure.BulletproofB.computeBpChalsAndB" do

  describe "chals expansion" do
    it "each chal equals toFieldPure of the corresponding prechallenge" do
      let
        rawPrechallenges = Vector.cons (mkChal 7) (Vector.cons (mkChal 11) Vector.nil)
        endo = int 3
        result = computeBpChalsAndB
          { rawPrechallenges
          , endo
          , zeta: int 2
          , zetaw: int 4
          , r: int 5
          }
        expectedChal0 = toFieldPure (mkChal 7) endo
        expectedChal1 = toFieldPure (mkChal 11) endo
        expectedChals = Vector.cons expectedChal0 (Vector.cons expectedChal1 Vector.nil)
      liftEffect $ result.chals `shouldEqual` expectedChals

  describe "b combines zeta and zetaw evaluations" do
    it "b = bPoly chals zeta + r · bPoly chals zetaw" do
      let
        rawPrechallenges = Vector.cons (mkChal 7) (Vector.cons (mkChal 11) Vector.nil)
        endo = int 3
        zeta = int 2
        zetaw = int 4
        r = int 5
        result = computeBpChalsAndB
          { rawPrechallenges, endo, zeta, zetaw, r }
        expected =
          let
            bAtZeta = bPoly result.chals zeta
            bAtZetaw = bPoly result.chals zetaw
          in
            bAtZeta + r * bAtZetaw
      liftEffect $ result.b `shouldEqual` expected

  describe "single-challenge degenerate case" do
    it "matches b = bPoly (1-element) zeta + r · bPoly (1-element) zetaw" do
      let
        rawPrechallenges = Vector.cons (mkChal 42) Vector.nil
        endo = int 2
        zeta = int 3
        zetaw = int 6
        r = int 7
        result = computeBpChalsAndB
          { rawPrechallenges, endo, zeta, zetaw, r }
        expected =
          let
            bAtZeta = bPoly result.chals zeta
            bAtZetaw = bPoly result.chals zetaw
          in
            bAtZeta + r * bAtZetaw
      liftEffect $ result.b `shouldEqual` expected
