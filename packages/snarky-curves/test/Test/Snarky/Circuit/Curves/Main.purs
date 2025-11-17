module Test.Snarky.Circuit.Curves.Main where

import Prelude

import Control.Monad.Gen (suchThat)
import Data.Array.NonEmpty as NEA
import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested (Tuple3, tuple3, uncurry3)
import Effect (Effect)
import Snarky.Circuit.Compile (compile, makeSolver)
import Snarky.Circuit.Curves (assertOnCurve, assertEqual)
import Snarky.Circuit.Curves as Curves
import Snarky.Circuit.Curves.Types (AffinePoint(..), CurveParams(..), genAffinePoint)
import Snarky.Circuit.TestUtils (AssertionExpectation(..), ConstraintSystem, assertionSpec', circuitSpec')
import Snarky.Curves.Class (class WeierstrassCurve, curveParams)
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (frequency)
import Test.Spec (Spec, describe, it)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main =
  runSpecAndExitProcess [ consoleReporter ] do
    spec (Proxy @Vesta.G)

spec
  :: forall g f
   . Arbitrary f
  => Arbitrary g
  => Eq f
  => WeierstrassCurve f g
  => Proxy g
  -> Spec Unit
spec pg =
  describe "Snarky.Circuit.Curves" do

    it "assertOnCurve Circuit is Valid" $
      let
        solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry assertOnCurve)
        { constraints } = un Identity $
          compile
            ( Proxy
                @( Tuple
                    (CurveParams f)
                    (AffinePoint f)
                )
            )
            (Proxy @Unit)
            (uncurry assertOnCurve)

        onCurve = do
          p :: AffinePoint f <- genAffinePoint pg
          pure $ Tuple (CurveParams $ curveParams pg) p
        offCurve = do
          let { a, b } = curveParams pg
          x <- arbitrary
          y <- arbitrary `suchThat` \_y -> _y * _y /= x * x * x + a * x + b
          pure $ Tuple (CurveParams $ curveParams pg) (AffinePoint { x, y })

      in
        do
          assertionSpec' constraints solver (const Satisfied) onCurve
          assertionSpec' constraints solver (const Unsatisfied) offCurve

    it "assertEqual Circuit is Valid" $
      let
        solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry assertEqual)
        { constraints } = un Identity $
          compile
            ( Proxy
                @( Tuple
                    (AffinePoint f)
                    (AffinePoint f)
                )
            )
            (Proxy @Unit)
            (uncurry assertEqual)

        same = do
          p :: AffinePoint f <- genAffinePoint pg
          pure $ Tuple p p
        distinct = do
          p1 :: AffinePoint f <- genAffinePoint pg
          p2 <- genAffinePoint pg `suchThat` \p -> p /= p1
          pure $ Tuple p1 p2
      in
        do
          assertionSpec' constraints solver (const Satisfied) same
          assertionSpec' constraints solver (const Unsatisfied) distinct

    it "negate Circuit is Valid" $
      let
        pureNegate :: AffinePoint f -> AffinePoint f
        pureNegate (AffinePoint { x, y }) = AffinePoint { x, y: negate y }
        solver = makeSolver (Proxy @(ConstraintSystem f)) Curves.negate
        { constraints } = un Identity $
          compile
            (Proxy @(AffinePoint f))
            (Proxy @(AffinePoint f))
            Curves.negate
        gen = genAffinePoint pg
      in
        circuitSpec' constraints solver pureNegate gen

    it "lookupSingleBit Circuit is Valid" $
      let
        pureLookupSingleBit :: Tuple3 Boolean (AffinePoint f) (AffinePoint f) -> AffinePoint f
        pureLookupSingleBit = uncurry3 \b p1 p2 -> if b then p2 else p1
        solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry3 Curves.lookupSingleBit)
        { constraints } = un Identity $
          compile
            (Proxy @(Tuple3 Boolean (AffinePoint f) (AffinePoint f)))
            (Proxy @(AffinePoint f))
            (uncurry3 Curves.lookupSingleBit)
        gen = do
          b <- arbitrary
          frequency $ NEA.cons'
            ( Tuple 1.0 do -- Same points (test when selection doesn't matter)
                p <- genAffinePoint pg
                pure $ tuple3 b p p
            )
            [ Tuple 1.0 do -- Different points (test actual selection)
                p1 <- genAffinePoint pg
                p2 <- genAffinePoint pg
                pure $ tuple3 b p1 p2
            ]
      in
        circuitSpec' constraints solver pureLookupSingleBit gen