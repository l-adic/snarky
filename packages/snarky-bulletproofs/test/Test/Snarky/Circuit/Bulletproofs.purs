module Test.Snarky.Circuit.Bulletproofs (spec) where

import Prelude

import Control.Monad.Except (mapExceptT, runExceptT, throwError)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Trans.Class (lift)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), snd)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception (error, throw)
import Snarky.Backend.Bulletproof.Gate (makeGates, makeGatesWitness, satisfies, sortR1CS)
import Snarky.Backend.Bulletproof.Types (Circuit, Witness)
import Snarky.Backend.Bulletproof.Class (class Bulletproof, createCrs, createWitness, createCircuit, createStatement, circuitIsSatisfiedBy, createProof, verify)
import Type.Proxy (Proxy(..))
import Snarky.Backend.Compile (SolverT, compile, makeSolver)
import Snarky.Circuit.Curves (assertEqual)
import Snarky.Circuit.Curves as EC
import Snarky.Circuit.DSL (class CircuitM, F, Snarky, FVar, all_, assert_, const_, equals_, exists, mul_, neq_, read)
import Snarky.Constraint.Bulletproofs (R1CS, eval)
import Snarky.Curves.Class (class PrimeField, class WeierstrassCurve, curveParams)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams, double, genAffinePoint)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, randomSample, randomSampleOne, suchThat)
import Test.Snarky.Circuit as CircuitTests
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: Spec Unit
spec = do
  CircuitTests.spec (Proxy @Vesta.BaseField) (Proxy @(R1CS Vesta.BaseField)) eval
  factorsSpec (Proxy @Pallas.G) (Proxy @Pallas.ScalarField) "Pallas"
  factorsSpec (Proxy @Vesta.G) (Proxy @Vesta.ScalarField) "Vesta"

-- Note: Cross-curve dlogSpec tests commented out due to cross-wired field relationships
-- dlogSpec (Proxy @Pasta.PallasG) (Proxy @Pasta.PallasBaseField) (Proxy @Pasta.VestaG) "Pallas"
-- dlogSpec (Proxy @Pasta.VestaG) (Proxy @Pasta.VestaBaseField) (Proxy @Pasta.PallasG) "Vesta"

--------------------------------------------------------------------------------

class Monad m <= FactorM f m where
  factor :: F f -> m { a :: F f, b :: F f }

factorsCircuit
  :: forall t m f c
   . FactorM f m
  => CircuitM f c t m
  => FVar f
  -> Snarky t m Unit
factorsCircuit n = do
  { a, b } <- exists do
    nVal <- read n
    lift $ factor @f nVal
  c1 <- equals_ n =<< mul_ a b
  c2 <- neq_ a (const_ one)
  c3 <- neq_ b (const_ one)
  assert_ =<< all_ [ c1, c2, c3 ]

instance (Arbitrary f, PrimeField f) => FactorM f Gen where
  factor n = do
    a <- arbitrary @(F f) `suchThat` \a ->
      a /= one && a /= n
    let b = n / a
    pure $ { a, b }

instance FactorM f Effect where
  factor _ = do
    throw "unhandled request: Factor"

factorsSpec
  :: forall g f
   . Bulletproof g f
  => PrimeField f
  => Proxy g
  -> Proxy f
  -> String
  -> Spec Unit
factorsSpec (_ :: Proxy g) (_ :: Proxy f) name = describe (name <> " Factors Spec") do

  it (name <> " Bulletproof Prove/Verify Flow") $ liftEffect $ do
    { constraints: cs, publicInputs } <-
      compile
        (Proxy @(F f))
        (Proxy @Unit)
        factorsCircuit
    let
      constraints = sortR1CS cs
      gates = makeGates { publicInputs, constraints }

      solver :: SolverT f (R1CS f) Gen (F f) Unit
      solver = makeSolver (Proxy @(R1CS f)) factorsCircuit

      gen :: Gen (F f)
      gen = arbitrary `suchThat` \a -> a /= zero && a /= one
      solve n = do
        Tuple _ assignments <- solver n
        makeGatesWitness { assignments, constraints, publicInputs }

    k <- randomSampleOne gen
    runExceptT (mapExceptT randomSampleOne $ solve k) >>= case _ of
      Left e -> throwError $ error (show e)
      Right witness -> do
        let
          q = Array.length gates.wl
          n = Array.length witness.al
          m = Array.length publicInputs

        let psSatisfies = satisfies witness gates
        psSatisfies `shouldEqual` true

        let
          rustWitness = (createWitness :: _ -> Witness g) { witness, seed: 12345 }
          rustCircuit = (createCircuit :: _ -> Circuit g) { gates, dimensions: { q, n, m } }
          rustSatisfies = circuitIsSatisfiedBy { circuit: rustCircuit, witness: rustWitness }

        rustSatisfies `shouldEqual` true

        let
          crs = createCrs { size: 256, seed: 42 }
          statement = createStatement { crs, witness: rustWitness }

        let
          proof = createProof
            { crs
            , circuit: rustCircuit
            , witness: rustWitness
            , seed: 54321
            }
          verifyResult = verify
            { crs
            , circuit: rustCircuit
            , statement
            , proof
            }

        verifyResult `shouldEqual` true

--------------------------------------------------------------------------------

class MonadDLog f m where
  getDLog16 :: AffinePoint (F f) -> m (AffinePoint (F f))

newtype Env f = Env (Array (Tuple (AffinePoint (F f)) (AffinePoint (F f))))

instance (PrimeField f) => MonadDLog f (ReaderT (Env f) Effect) where
  getDLog16 p = do
    Env m <- ask
    case Array.find (\(Tuple a _) -> a == p) m of
      Nothing -> throwError $ error ("Missing point " <> show p)
      Just q -> pure $ snd q

instance MonadDLog f Effect where
  getDLog16 _ = do
    throw "unhandled request: getDLog16"

dlog16Circuit
  :: forall f t m
   . CircuitM f (R1CS f) t m
  => MonadDLog f m
  => CurveParams f
  -> AffinePoint (FVar f)
  -> Snarky t m Unit
dlog16Circuit cp p = do
  q <- exists do
    pVal <- read p
    lift $ getDLog16 @f pVal
  let f = EC.double cp
  qToThe16 <- do
    q2 <- f q
    q4 <- f q2
    q8 <- f q4
    f q8
  assertEqual qToThe16 p

dlogSpec
  :: forall g f curve
   . Bulletproof curve f
  => PrimeField f
  => Arbitrary g
  => WeierstrassCurve f g
  => Proxy curve
  -> Proxy f
  -> Proxy g
  -> String
  -> Spec Unit
dlogSpec (_ :: Proxy curve) (_ :: Proxy f) pg name = describe (name <> " DLog Spec") do
  let cp = curveParams pg
  it "dlog Circuit is Valid" $ liftEffect $ do
    { constraints: cs, publicInputs } <-
      compile
        (Proxy @(AffinePoint (F f)))
        (Proxy @Unit)
        (dlog16Circuit cp)
    let
      constraints = sortR1CS cs
      gates = makeGates { publicInputs, constraints }

      solver :: SolverT f (R1CS f) (ReaderT (Env f) Effect) (AffinePoint (F f)) Unit
      solver = makeSolver (Proxy @(R1CS f)) (dlog16Circuit cp)

      gen :: Gen (Tuple (AffinePoint (F f)) (AffinePoint (F f)))
      gen = do
        p <- genAffinePoint pg
        let
          f x =
            let
              x2 = double cp x
              x4 = double cp x2
              x8 = double cp x4
            in
              double cp x8
        pure $ Tuple (f p) p
      solve p = do
        Tuple _ assignments <- solver p
        makeGatesWitness { assignments, constraints, publicInputs }
    kvs <- randomSample gen
    let nat kv m = runReaderT m (Env [ kv ])
    for_ kvs \kv@(Tuple p _) -> do
      runExceptT (mapExceptT (nat kv) $ solve p) >>= case _ of
        Left e -> throwError $ error (show e)
        Right witness -> do
          let
            q = Array.length gates.wl
            n = Array.length witness.al
            m = Array.length publicInputs

          let psSatisfies = satisfies witness gates
          psSatisfies `shouldEqual` true

          let
            rustWitness = (createWitness :: _ -> Witness curve) { witness, seed: 12345 }
            rustCircuit = (createCircuit :: _ -> Circuit curve) { gates, dimensions: { q, n, m } }
            rustSatisfies = circuitIsSatisfiedBy { circuit: rustCircuit, witness: rustWitness }

          rustSatisfies `shouldEqual` true

          let
            crs = createCrs { size: 256, seed: 42 }
            statement = createStatement { crs, witness: rustWitness }

          let
            proof = createProof
              { crs
              , circuit: rustCircuit
              , witness: rustWitness
              , seed: 54321
              }
            verifyResult = verify
              { crs
              , circuit: rustCircuit
              , statement
              , proof
              }

          verifyResult `shouldEqual` true

