module Test.Snarky.Circuit.Kimchi.AddComplete where

import Prelude

import Control.Monad.Gen (suchThat)
import Data.Array (catMaybes, mapWithIndex)
import Data.Either (Either(..))
import Data.Identity (Identity)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust)
import Data.Tuple (Tuple(..), uncurry)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Poseidon.Class (class PoseidonField)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, compilePure, makeSolver, runSolver)
import Snarky.Circuit.DSL (class CircuitM, Snarky, const_)
import Snarky.Circuit.DSL as Snarky
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Types (F, FVar)
import Snarky.Constraint.Kimchi (AuxState(..), KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Constraint.Kimchi.Wire (GateKind(..))
import Snarky.Curves.Class (class PrimeField, class WeierstrassCurve)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (Point(..), AffinePoint)
import Snarky.Data.EllipticCurve as EC
import Test.QuickCheck (class Arbitrary, quickCheck')
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Test.Utils.CompleteAdd (placeWitness, verifyVestaCompleteAdd)
import Type.Proxy (Proxy(..))

spec
  :: forall g f
   . PrimeField f
  => PoseidonField f
  => Arbitrary g
  => WeierstrassCurve f g
  => Proxy g
  -> Proxy (KimchiConstraint f)
  -> Spec Unit
spec pg pc =
  describe "Kimchi AddComplete" do

    it "addComplete Circuit is Valid" $ unsafePartial $
      let
        f = uncurry EC.addAffine
        solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry circuit)

        circuit
          :: forall t
           . CircuitM f (KimchiConstraint f) t Identity
          => AffinePoint (FVar f)
          -> AffinePoint (FVar f)
          -> Snarky (KimchiConstraint f) t Identity (Point (FVar f))
        circuit p1 p2 = do
          { isInfinity, p } <- addComplete p1 p2
          x <- Snarky.if_ isInfinity (const_ zero) p.x
          y <- Snarky.if_ isInfinity (const_ one) p.y
          z <- Snarky.if_ isInfinity (const_ zero) (const_ one)
          pure $ Point { x, y, z }
        { constraints } =
          compilePure
            (Proxy @(Tuple (AffinePoint (F f)) (AffinePoint (F f))))
            (Proxy @(Point (F f)))
            pc
            (uncurry circuit)
            Kimchi.initialState

        -- Generate distinct points to avoid division by zero in slope calculation
        -- Avoid x1 = x2
        gen = do
          p1 <- EC.genAffinePoint pg
          p2 <- EC.genAffinePoint pg `suchThat` \p ->
            let
              { x: x1, y: y1 } = p1
              { x: x2, y: y2 } = p
            in
              x1 /= x2 || y1 /= negate y2
          pure $ Tuple p1 p2
        genInverse = do
          p1 <- EC.genAffinePoint pg
          let p2 = p1 { y = -p1.y }
          pure $ Tuple p1 p2

      in
        do
          circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied f) gen
          circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied f) genInverse


spec2 :: Spec Unit
spec2 = do
  describe "" $
    it "addComplete witness validates against Kimchi ground truth" $ unsafePartial $ do
      let
        circuit
          :: forall t
           . CircuitM Pallas.ScalarField (KimchiConstraint Pallas.ScalarField) t Identity
          => AffinePoint (FVar Pallas.ScalarField)
          -> AffinePoint (FVar Pallas.ScalarField)
          -> Snarky (KimchiConstraint Pallas.ScalarField) t Identity (Point (FVar Pallas.ScalarField))
        circuit p1 p2 = do
          { isInfinity, p } <- addComplete p1 p2
          x <- Snarky.if_ isInfinity (const_ zero) p.x
          y <- Snarky.if_ isInfinity (const_ one) p.y
          z <- Snarky.if_ isInfinity (const_ zero) (const_ one)
          pure $ Point { x, y, z }

        { aux : AuxState { wireState: { emittedRows, wireAssignments }} } =
          compilePure
            (Proxy @(Tuple (AffinePoint (F Pallas.ScalarField)) (AffinePoint (F Pallas.ScalarField))))
            (Proxy @(Point (F Pallas.ScalarField)))
            (Proxy @(KimchiConstraint Pallas.ScalarField))
            (uncurry circuit)
            (Kimchi.initialState :: CircuitBuilderState (KimchiGate Pallas.ScalarField) _)

        solver :: 
          Solver 
            (Pallas.ScalarField) 
            (KimchiConstraint Pallas.ScalarField)
            (Tuple (AffinePoint (F Pallas.ScalarField)) (AffinePoint (F Pallas.ScalarField)))
            (Point (F Pallas.ScalarField))
        solver = makeSolver (Proxy @(KimchiConstraint Pallas.ScalarField)) (uncurry circuit)

        gen = do
          p1 <- EC.genAffinePoint (Proxy @Vesta.G)
          p2 <- EC.genAffinePoint (Proxy @Vesta.G) `suchThat` \p ->
            let
              { x: x1, y: y1 } = p1
              { x: x2, y: y2 } = p
            in
              x1 /= x2 || y1 /= negate y2
          pure $ Tuple p1 p2

      liftEffect $ quickCheck' 10 do 
        input <- gen
        let Right (Tuple _ assignment) = runSolver solver input
        let witnessMatrix = placeWitness wireAssignments assignment
        let ecAddRows = catMaybes $
              mapWithIndex 
                ( \i {kind} -> case kind of
                    AddCompleteGate -> Just i
                    _ -> Nothing
                )
                emittedRows
        let witnessRow = map (\col -> fromJust $ Map.lookup (Tuple 0 col) witnessMatrix) ecAddRows
        pure $ verifyVestaCompleteAdd witnessRow