module Test.Snarky.Circuit.R1CS (spec) where

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
import Snarky.Backend.Bulletproof.Gate (makeGates, makeWitness, satisfies, sortR1CS, toGates)
import Snarky.Backend.Bulletproof.Pallas as PallasBulletproof
import Snarky.Backend.Bulletproof.Vesta as VestaBulletproof
import Snarky.Backend.Compile (SolverT, compile, makeSolver)
import Snarky.Circuit.Curves (assertEqual)
import Snarky.Circuit.Curves as EC
import Snarky.Circuit.DSL (class CircuitM, F, Snarky, FVar, all_, assert_, const_, equals_, exists, mul_, neq_, read)
import Snarky.Constraint.R1CS (R1CS, eval)
import Snarky.Curves.Class (class PrimeField, class WeierstrassCurve, curveParams)
import Snarky.Curves.Vesta as Vesta
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams, double, genAffinePoint)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, randomSample, randomSampleOne, suchThat)
import Test.Snarky.Circuit as CircuitTests
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = do
  CircuitTests.spec (Proxy @Vesta.BaseField) (Proxy @(R1CS Vesta.BaseField)) eval
  factorsSpec (Proxy @Vesta.BaseField)
  pallasFactorsSpec
  vestaFactorsSpec
  dlogSpec (Proxy @Vesta.G) (Proxy @Vesta.BaseField)

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
  :: forall f
   . PrimeField f
  => Proxy f
  -> Spec Unit
factorsSpec _ = describe "Factors Spec" do

  it "factors Circuit is Valid" $ liftEffect $ do
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
        makeWitness { assignments, constraints, publicInputs }
    ns <- randomSample gen
    for_ ns \n -> do
      runExceptT (mapExceptT randomSampleOne $ solve n) >>= case _ of
        Left e -> throwError $ error (show e)
        Right witness -> satisfies witness gates `shouldEqual` true

pallasFactorsSpec :: Spec Unit
pallasFactorsSpec = describe "Pallas Factors Spec" do

  it "Pallas Bulletproof Prove/Verify Flow" $ liftEffect $ do
    { constraints: cs, publicInputs } <-
      compile
        (Proxy @(F Pallas.ScalarField))
        (Proxy @Unit)
        factorsCircuit
    let
      constraints = sortR1CS cs
      gates = makeGates { publicInputs, constraints }

      solver :: SolverT Pallas.ScalarField (R1CS Pallas.ScalarField) Gen (F Pallas.ScalarField) Unit
      solver = makeSolver (Proxy @(R1CS Pallas.ScalarField)) factorsCircuit

      gen :: Gen (F Pallas.ScalarField)
      gen = arbitrary `suchThat` \a -> a /= zero && a /= one
      solve n = do
        Tuple _ assignments <- solver n
        makeWitness { assignments, constraints, publicInputs }

    k <- randomSampleOne gen
    runExceptT (mapExceptT randomSampleOne $ solve k) >>= case _ of
      Left e -> throwError $ error (show e)
      Right witness -> do
        -- Debug: Print PureScript circuit and witness dimensions
        let
          q = Array.length gates.wl
          n = Array.length witness.al -- number of multiplication gates
          m = Array.length publicInputs
          -- Use sparse format for efficient FFI transfer
          gates' = toGates gates { q, n, m }

        -- Test PureScript implementation
        let psSatisfies = satisfies witness gates
        psSatisfies `shouldEqual` true

        -- Test Rust bulletproof circuit implementation 
        let
          rustWitness = PallasBulletproof.witnessCreate
            { left: witness.al
            , right: witness.ar
            , output: witness.ao
            , v: witness.v
            , seed: 12345
            }
          rustCircuit = PallasBulletproof.circuitCreate gates'
          rustSatisfies = PallasBulletproof.circuitIsSatisfiedBy { circuit: rustCircuit, witness: rustWitness }

        rustSatisfies `shouldEqual` true

        -- Test prove/verify flow
        let
          crs = PallasBulletproof.crsCreate { size: 256, seed: 42 }
          statement = PallasBulletproof.statementCreate { crs, witness: rustWitness }

        let
          proof = PallasBulletproof.prove
            { crs
            , circuit: rustCircuit
            , witness: rustWitness
            , seed: 54321
            }
          verifyResult = PallasBulletproof.verify
            { crs
            , circuit: rustCircuit
            , statement
            , proof
            }

        verifyResult `shouldEqual` true

vestaFactorsSpec :: Spec Unit
vestaFactorsSpec = describe "Vesta Factors Spec" do

  it "Vesta Bulletproof Prove/Verify Flow" $ liftEffect $ do
    { constraints: cs, publicInputs } <-
      compile
        (Proxy @(F Vesta.ScalarField))
        (Proxy @Unit)
        factorsCircuit
    let
      constraints = sortR1CS cs
      gates = makeGates { publicInputs, constraints }

      solver :: SolverT Vesta.ScalarField (R1CS Vesta.ScalarField) Gen (F Vesta.ScalarField) Unit
      solver = makeSolver (Proxy @(R1CS Vesta.ScalarField)) factorsCircuit

      gen :: Gen (F Vesta.ScalarField)
      gen = arbitrary `suchThat` \a -> a /= zero && a /= one
      solve n = do
        Tuple _ assignments <- solver n
        makeWitness { assignments, constraints, publicInputs }

    k <- randomSampleOne gen
    runExceptT (mapExceptT randomSampleOne $ solve k) >>= case _ of
      Left e -> throwError $ error (show e)
      Right witness -> do
        -- Debug: Print PureScript circuit and witness dimensions
        let
          q = Array.length gates.wl
          n = Array.length witness.al -- number of multiplication gates
          m = Array.length publicInputs
          -- Use sparse format for efficient FFI transfer
          gates' = toGates gates { q, n, m }

        -- Test PureScript implementation
        let psSatisfies = satisfies witness gates
        psSatisfies `shouldEqual` true

        -- Test Rust bulletproof circuit implementation 
        let
          rustWitness = VestaBulletproof.witnessCreate
            { left: witness.al
            , right: witness.ar
            , output: witness.ao
            , v: witness.v
            , seed: 12345
            }
          rustCircuit = VestaBulletproof.circuitCreate gates'
          rustSatisfies = VestaBulletproof.circuitIsSatisfiedBy { circuit: rustCircuit, witness: rustWitness }

        rustSatisfies `shouldEqual` true

        -- Test prove/verify flow
        let
          crs = VestaBulletproof.crsCreate { size: 256, seed: 42 }
          statement = VestaBulletproof.statementCreate { crs, witness: rustWitness }

        let
          proof = VestaBulletproof.prove
            { crs
            , circuit: rustCircuit
            , witness: rustWitness
            , seed: 54321
            }
          verifyResult = VestaBulletproof.verify
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
  :: forall f g
   . PrimeField f
  => Arbitrary g
  => WeierstrassCurve f g
  => Proxy g
  -> Proxy f
  -> Spec Unit
dlogSpec pg _ = describe "DLog Spec" do
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
        makeWitness { assignments, constraints, publicInputs }
    kvs <- randomSample gen
    let nat kv m = runReaderT m (Env [ kv ])
    for_ kvs \kv@(Tuple p _) -> do
      runExceptT (mapExceptT (nat kv) $ solve p) >>= case _ of
        Left e -> throwError $ error (show e)
        Right witness -> satisfies witness gates `shouldEqual` true