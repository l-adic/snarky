module Test.Pickles.Linearization where

-- | This module tests the equivalence of the PureScript Kimchi linearization
-- | interpreter against the Rust FFI evaluator.
-- |
-- | The `buildEvalPoint` function uses a `defaultVal` parameter. This parameter
-- | serves as a fallback for any column evaluations that are not explicitly
-- | provided by the test inputs (e.g., `witnessEvals`, `coeffEvals`,
-- | `indexEvals`). For specific lookup-related evaluations, `defaultVal` is
-- | always returned.
-- |
-- | By typically setting `defaultVal` to `zero` (the field's zero element),
-- | this test effectively asserts the equivalence of the linearization
-- | polynomial in a "vanilla" proof system configuration. In this configuration,
-- | features like lookups, which are not explicitly provided or relevant to the
-- | `constantTermTokens` being evaluated, are treated as "off" or "zeroed out".
-- | This is consistent with the Rust FFI evaluator's internal logic, which
-- | treats all feature flags as disabled to match the OCaml implementation.
-- | For example, if the Kimchi linearization in `constantTermTokens` refers to
-- | a lookup column, its value in this test will be zero, as if the lookup
-- | feature were disabled.

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Either (Either(..))
import Data.Fin (Finite(..), unsafeFinite)
import Data.Identity (Identity)
import Data.Int (pow) as Int
import Data.Newtype (unwrap, wrap)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector, (!!))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Class.Console (log)
import Effect.Exception (throw)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Pickles.Linearization.Env (CurrOrNext(..), GateType(..)) as Env
import Pickles.Linearization.Env (Env, EnvM, buildCircuitEnvM, circuitEnv, fieldEnv, precomputeAlphaPowers)
import Pickles.Linearization.FFI (class LinearizationFFI, PointEval, domainGenerator, evalLinearization, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.Linearization.FFI as FFI
import Pickles.Linearization.Interpreter (evaluate, evaluateM)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.Linearization.Types (PolishToken)
import Pickles.Linearization.Vesta as VestaTokens
import Pickles.PlonkChecks.GateConstraints (buildChallenges, buildEvalPoint, parseHex)
import Poseidon (class PoseidonField)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Backend.Kimchi.CircuitJson (CircuitData, circuitToJson, readCircuitJson)
import Snarky.Circuit.CVar (CVar(..), const_)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, mul_, pow_, sub_)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (class HasEndo, class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (arbitrary, quickCheckGen, (===))
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

kimchiTestConfig :: forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)
kimchiTestConfig = { checker: eval, postCondition: Kimchi.postCondition, initState: Kimchi.initialState }

main :: Effect Unit
main =
  runSpecAndExitProcess [ consoleReporter ] do
    spec kimchiTestConfig

-- Standard Kimchi constants
domainLog2 :: Int
domainLog2 = 16

zkRows :: Int
zkRows = 3

-------------------------------------------------------------------------------
-- | Helper functions (test-specific)
-------------------------------------------------------------------------------

-- | Build FFI input from vectors and challenges
buildFFIInput
  :: forall f g r
   . LinearizationFFI f g
  => { witnessEvals :: Vector 15 (PointEval f)
     , coeffEvals :: Vector 15 f
     , indexEvals :: Vector 6 (PointEval f)
     , alpha :: f
     , beta :: f
     , gamma :: f
     , jointCombiner :: f
     , zeta :: f
     | r
     }
  -> FFI.LinearizationInput f
buildFFIInput { witnessEvals, coeffEvals, indexEvals, alpha, beta, gamma, jointCombiner, zeta } =
  let
    index = unsafeFinite @6
  in
    { alpha
    , beta
    , gamma
    , jointCombiner
    , witnessEvals
    , coefficientEvals: coeffEvals
    -- Index order matches Kimchi verifier: Generic, Poseidon, CompleteAdd, VarBaseMul, EndoMul, EndoMulScalar
    -- See kimchi/src/verifier.rs lines 485-490
    , genericIndex: indexEvals !! index 0
    , poseidonIndex: indexEvals !! index 1
    , completeAddIndex: indexEvals !! index 2
    , varbasemulIndex: indexEvals !! index 3
    , endomulIndex: indexEvals !! index 4
    , endomulScalarIndex: indexEvals !! index 5
    , vanishesOnZk: vanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: zeta }
    , zeta
    , domainLog2
    }

-- | Generate a sized vector of arbitrary field elements
genFieldVector :: forall f n. PrimeField f => Reflectable n Int => Proxy n -> Gen (Vector n f)
genFieldVector p = Vector.generator p arbitrary

-------------------------------------------------------------------------------
-- | Parameterized test types and functions
-------------------------------------------------------------------------------

-- | Input record for linearization test, parameterized by element type.
-- | Use as `LinearizationInput (F f)` for values or `LinearizationInput (FVar f)` for circuit variables.
type LinearizationInput a =
  { witnessEvals :: Vector 15 (PointEval a)
  , coeffEvals :: Vector 15 a
  , indexEvals :: Vector 6 (PointEval a)
  , alpha :: a
  , beta :: a
  , gamma :: a
  , jointCombiner :: a
  , vanishesOnZk :: a
  , lagrangeFalse0 :: a
  , lagrangeTrue1 :: a
  }

-- | Circuit that evaluates the linearization polynomial (parameterized)
linearizationCircuit
  :: forall f f' t m
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => Array PolishToken
  -> LinearizationInput (FVar f)
  -> Snarky (KimchiConstraint f) t m (FVar f)
linearizationCircuit tokens input =
  let
    evalPoint = buildEvalPoint
      { witnessEvals: input.witnessEvals
      , coeffEvals: input.coeffEvals
      , indexEvals: input.indexEvals
      , defaultVal: Const zero
      }

    challenges = buildChallenges
      { alpha: input.alpha
      , beta: input.beta
      , gamma: input.gamma
      , jointCombiner: input.jointCombiner
      , vanishesOnZk: input.vanishesOnZk
      , lagrangeFalse0: input.lagrangeFalse0
      , lagrangeTrue1: input.lagrangeTrue1
      }

    env = circuitEnv evalPoint challenges parseHex
  in
    evaluate tokens env

-- | Reference function for field evaluation (parameterized)
linearizationReference
  :: forall f f'
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => Array PolishToken
  -> LinearizationInput (F f)
  -> F f
linearizationReference tokens input' =
  let
    input :: LinearizationInput f
    input = coerce input'

    evalPoint = buildEvalPoint
      { witnessEvals: input.witnessEvals
      , coeffEvals: input.coeffEvals
      , indexEvals: input.indexEvals
      , defaultVal: zero
      }

    challenges = buildChallenges
      { alpha: input.alpha
      , beta: input.beta
      , gamma: input.gamma
      , jointCombiner: input.jointCombiner
      , vanishesOnZk: input.vanishesOnZk
      , lagrangeFalse0: input.lagrangeFalse0
      , lagrangeTrue1: input.lagrangeTrue1
      }

    env = fieldEnv evalPoint challenges parseHex
  in
    coerce $ evaluate tokens env

-- | Generate an arbitrary PointEval
genPointEval :: forall f. PrimeField f => Gen (PointEval f)
genPointEval = do
  zeta <- arbitrary
  omegaTimesZeta <- arbitrary
  pure { zeta, omegaTimesZeta }

-- | Generate arbitrary LinearizationInput using FFI for domain-dependent values
genLinearizationInput
  :: forall f g
   . PrimeField f
  => LinearizationFFI f g
  => Gen (LinearizationInput (F f))
genLinearizationInput = do
  witnessEvals <- Vector.generator (Proxy @15) genPointEval
  coeffEvals <- genFieldVector (Proxy @15)
  indexEvals <- Vector.generator (Proxy @6) genPointEval
  alpha <- arbitrary
  beta <- arbitrary
  gamma <- arbitrary
  jointCombiner <- arbitrary
  zeta :: F f <- arbitrary

  -- Compute domain-dependent values using FFI
  let
    vanishesOnZk = wrap $ vanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: unwrap zeta }
    lagrangeFalse0 = wrap $ unnormalizedLagrangeBasis { domainLog2, zkRows: 0, offset: 0, pt: unwrap zeta }
    lagrangeTrue1 = wrap $ unnormalizedLagrangeBasis { domainLog2, zkRows, offset: -1, pt: unwrap zeta }

  pure
    { witnessEvals
    , coeffEvals
    , indexEvals
    , alpha
    , beta
    , gamma
    , jointCombiner
    , vanishesOnZk
    , lagrangeFalse0
    , lagrangeTrue1
    }

-------------------------------------------------------------------------------
-- | Parameterized test suite
-------------------------------------------------------------------------------

linearizationTests
  :: forall f f' g
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => Kimchi.KimchiVerify f f'
  => LinearizationFFI f g
  => TestConfig f (KimchiGate f) (AuxState f)
  -> Proxy f
  -> Array PolishToken
  -> Spec Unit
linearizationTests cfg _ tokens = do
  it "PureScript interpreter matches Rust evaluator on arbitrary inputs" do
    liftEffect $ quickCheckGen do
      -- Generate arbitrary field elements
      (witnessEvals :: Vector 15 (PointEval f)) <- Vector.generator (Proxy @15) genPointEval
      coeffEvals <- genFieldVector (Proxy @15)
      (indexEvals :: Vector 6 (PointEval f)) <- Vector.generator (Proxy @6) genPointEval
      alpha <- arbitrary
      beta <- arbitrary
      gamma <- arbitrary
      jointCombiner <- arbitrary
      zeta <- arbitrary

      -- Build PureScript structures using FFI for domain values
      let
        vanishesOnZk' = vanishesOnZkAndPreviousRows { domainLog2, zkRows, pt: zeta }
        lagrangeFalse0 = unnormalizedLagrangeBasis { domainLog2, zkRows: 0, offset: 0, pt: zeta }
        lagrangeTrue1 = unnormalizedLagrangeBasis { domainLog2, zkRows, offset: -1, pt: zeta }

      let evalPoint = buildEvalPoint { witnessEvals, coeffEvals, indexEvals, defaultVal: zero }
      let challenges = buildChallenges { alpha, beta, gamma, jointCombiner, vanishesOnZk: vanishesOnZk', lagrangeFalse0, lagrangeTrue1 }
      let env = fieldEnv evalPoint challenges parseHex
      let
        psResult = (evaluate :: Array PolishToken -> Env f -> f)
          tokens
          env

      -- Build FFI input for Rust
      let ffiInput = buildFFIInput { witnessEvals, coeffEvals, indexEvals, alpha, beta, gamma, jointCombiner, zeta }

      -- Call Rust evaluator
      let rustResult = evalLinearization ffiInput

      -- Both should produce the same result
      pure $ psResult === rustResult

  it "Circuit evaluation matches field evaluation" do
    let
      circuit'
        :: forall t
         . CircuitM f (KimchiConstraint f) t Identity
        => LinearizationInput (FVar f)
        -> Snarky (KimchiConstraint f) t Identity (FVar f)
      circuit' = linearizationCircuit tokens
    void $ circuitTest' @f
      cfg
      ( NEA.singleton
          { testFunction: satisfied (linearizationReference tokens)
          , input: QuickCheck 1 (genLinearizationInput :: Gen (LinearizationInput (F f)))
          }
      )
      circuit'

-------------------------------------------------------------------------------
-- | Main spec
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- | Monadic circuit matching OCaml's 90-field input layout
-------------------------------------------------------------------------------

-- | Maximum alpha power appearing in the constant_term tokens.
-- | OCaml precomputes 71 elements (0..70) but only 0..31 are used.
maxAlphaPower :: Int
maxAlphaPower = 70

-- | Circuit that evaluates the linearization polynomial using the monadic
-- | interpreter with compact Store/Load token stream:
-- | - 90 input fields (matching OCaml dump_circuit_impl.ml layout)
-- | - Precomputed alpha powers via successive multiplication
-- | - Domain values computed from zeta (omega constants for lagrange basis)
-- | - Monadic interpreter (evaluateM) with peephole alpha optimization
linearizationCircuitM
  :: forall f f' g t m
   . PrimeField f
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => LinearizationFFI f g
  => Int -- ^ domainLog2
  -> Array PolishToken
  -> Vector 90 (FVar f)
  -> Snarky (KimchiConstraint f) t m (FVar f)
linearizationCircuitM domLog2 tokens inputs = do
  let
    -- Unpack 90 inputs matching OCaml layout:
    -- 0-29: witness evals (15 pairs of (zeta, zetaw))
    -- 30-59: coefficient evals (15 pairs of (zeta, zetaw))
    -- 60-61: z eval (unused in constant_term)
    -- 62-73: s evals (6 pairs, unused in constant_term)
    -- 74-85: selector evals (6 pairs: generic, poseidon, completeadd, vbm, emul, emulscalar)
    -- 86: alpha, 87: beta, 88: gamma, 89: zeta
    at i = inputs !! unsafeFinite i

    -- Witness evals: 15 pairs at indices 0-29
    witnessEval row col =
      let
        base = 2 * (coerce col :: Int)
      in
        case row of
          Env.Curr -> at base
          Env.Next -> at (base + 1)

    -- Coefficient evals: 15 pairs at indices 30-59
    -- OCaml treats coefficients as pairs (zeta, zetaw) but we only use zeta
    coeffEval col = at (30 + 2 * (coerce col :: Int))

    -- Selector evals: 6 pairs at indices 74-85
    -- Order: Generic=0, Poseidon=1, CompleteAdd=2, VarBaseMul=3, EndoMul=4, EndoMulScalar=5
    selectorEval row gt =
      let
        idx = case gt of
          Env.Generic -> 0
          Env.Poseidon -> 1
          Env.CompleteAdd -> 2
          Env.VarBaseMul -> 3
          Env.EndoMul -> 4
          Env.EndoMulScalar -> 5
          _ -> 0 -- Unsupported gates default to generic
        base = 74 + 2 * idx
      in
        case row of
          Env.Curr -> at base
          Env.Next -> at (base + 1)

    alpha = at 86
    beta = at 87
    gamma = at 88
    zeta = at 89

    -- Build eval point using direct lookups
    evalPoint =
      { witness: \row col -> witnessEval row col
      , coefficient: \col -> coeffEval col
      , index: \row gt -> selectorEval row gt
      , lookupAggreg: \_ -> Const zero
      , lookupSorted: \_ _ -> Const zero
      , lookupTable: \_ -> Const zero
      , lookupRuntimeTable: \_ -> Const zero
      , lookupRuntimeSelector: \_ -> Const zero
      , lookupKindIndex: \_ -> Const zero
      }

    -- Domain generator is a constant (from FFI)
    gen = domainGenerator @f domLog2

    -- All omega values are constants (no circuit constraints)
    -- omega^(-1) = 1/gen (constant fold)
    omegaToMinus1 = recip gen
    -- omega^(n - zk_rows - 1) = omega^(n-4) = omega^(-4) since omega^n = 1
    -- = (omega^(-1))^4
    omegaToMinus4 = omegaToMinus1 * omegaToMinus1 * omegaToMinus1 * omegaToMinus1
    -- omega^(n - zk_rows) = omega^(-3)
    omegaToMinus3 = omegaToMinus1 * omegaToMinus1 * omegaToMinus1
    -- omega^(n - zk_rows + 1) = omega^(-2)
    omegaToMinus2 = omegaToMinus1 * omegaToMinus1

    -- Omega constant lookup for unnormalized lagrange basis
    -- Matches OCaml's unnormalized_lagrange_basis omega resolution
    omegaForLagrange { zkRows: zk, offset } =
      if not zk && offset == 0 then one -- omega^0 = 1
      else if zk && offset == (-1) then omegaToMinus4 -- omega^(n - zk_rows - 1)
      else if not zk && offset == 1 then gen -- omega^1
      else if not zk && offset == (-1) then omegaToMinus1 -- omega^(-1)
      else if not zk && offset == (-2) then omegaToMinus2 -- omega^(-2)
      else if zk && offset == 0 then omegaToMinus3 -- omega^(n - zk_rows) = omega^(-zk_rows)
      else one -- fallback (shouldn't happen for constant_term tokens)

  -- 1. Precompute alpha powers (69 R1CS constraints for successive multiplication)
  alphaPowers <- precomputeAlphaPowers maxAlphaPower alpha

  -- 2. Eager zk_polynomial = (zeta - ω⁻¹)(zeta - ω⁻²)(zeta - ω⁻³)
  -- Matches OCaml plonk_checks.ml:272-279
  _zkPoly <- do
    t1 <- mul_ (zeta `sub_` const_ omegaToMinus1) (zeta `sub_` const_ omegaToMinus2)
    mul_ t1 (zeta `sub_` const_ omegaToMinus3)

  -- 3. Eager zeta_to_n_minus_1 = zeta^(2^domainLog2) - 1
  -- Matches OCaml plonk_checks.ml:294 (separate from the lazy binding at :281)
  _eagerZetaToNMinus1 <- do
    zetaToN <- pow_ zeta (Int.pow 2 domLog2)
    pure (zetaToN `sub_` const_ one)

  -- 4. vanishes_on_zero_knowledge_and_previous_rows = 1 (joint_combiner is None)
  let vanishesOnZk = const_ one

  -- 5. Build monadic env
  -- Note: zeta^n-1 is ALSO computed lazily inside the env (computeZetaToNMinus1),
  -- matching OCaml's lazy binding (plonk_checks.ml:281) forced inside
  -- unnormalized_lagrange_basis.
  let
    env :: EnvM f (Snarky (KimchiConstraint f) t m)
    env = buildCircuitEnvM
      alphaPowers
      zeta
      domLog2
      omegaForLagrange
      evalPoint
      vanishesOnZk
      beta
      gamma
      (const_ one) -- jointCombiner (None → 1)
      parseHex

  -- 6. Evaluate tokens using monadic interpreter
  evaluateM tokens env

type V90Pallas = Vector 90 (F Pallas.BaseField)
type V90Vesta = Vector 90 (F Vesta.BaseField)

compileLinearizationTick :: String
compileLinearizationTick = circuitToJson @Pallas.BaseField $
  compilePure
    (Proxy @V90Pallas)
    (Proxy @(F Pallas.BaseField))
    (Proxy @(KimchiConstraint Pallas.BaseField))
    (linearizationCircuitM 16 PallasTokens.constantTermTokens)
    Kimchi.initialState

compileLinearizationTock :: String
compileLinearizationTock = circuitToJson @Vesta.BaseField $
  compilePure
    (Proxy @V90Vesta)
    (Proxy @(F Vesta.BaseField))
    (Proxy @(KimchiConstraint Vesta.BaseField))
    (linearizationCircuitM 15 VestaTokens.constantTermTokens)
    Kimchi.initialState

fixtureDir :: String
fixtureDir = "packages/snarky-kimchi/test/fixtures/"

linearizationTickCircuitComparison :: Spec Unit
linearizationTickCircuitComparison =
  it "linearization_tick_circuit matches OCaml" do
    ocamlJson <- liftEffect do
      buf <- FS.readFile (fixtureDir <> "linearization_tick_circuit.json")
      Buffer.toString UTF8 buf
    let
      ocamlCircuit :: Either _ (CircuitData Pallas.BaseField)
      ocamlCircuit = readCircuitJson ocamlJson

      psCircuit :: Either _ (CircuitData Pallas.BaseField)
      psCircuit = readCircuitJson compileLinearizationTick
    case ocamlCircuit, psCircuit of
      Right ocaml, Right ps -> do
        log $ "OCaml: pi=" <> show ocaml.publicInputSize <> ", gates=" <> show (Array.length ocaml.gates)
        log $ "PS:    pi=" <> show ps.publicInputSize <> ", gates=" <> show (Array.length ps.gates)
        ps.publicInputSize `shouldEqual` ocaml.publicInputSize
        ps.gates `shouldEqual` ocaml.gates
      Left e, _ -> liftEffect $ throw $ "Failed to parse OCaml JSON: " <> show e
      _, Left e -> liftEffect $ throw $ "Failed to parse PureScript JSON: " <> show e

linearizationTockCircuitComparison :: Spec Unit
linearizationTockCircuitComparison =
  it "linearization_tock_circuit matches OCaml" do
    ocamlJson <- liftEffect do
      buf <- FS.readFile (fixtureDir <> "linearization_tock_circuit.json")
      Buffer.toString UTF8 buf
    let
      ocamlCircuit :: Either _ (CircuitData Vesta.BaseField)
      ocamlCircuit = readCircuitJson ocamlJson

      psCircuit :: Either _ (CircuitData Vesta.BaseField)
      psCircuit = readCircuitJson compileLinearizationTock
    case ocamlCircuit, psCircuit of
      Right ocaml, Right ps -> do
        log $ "OCaml: pi=" <> show ocaml.publicInputSize <> ", gates=" <> show (Array.length ocaml.gates)
        log $ "PS:    pi=" <> show ps.publicInputSize <> ", gates=" <> show (Array.length ps.gates)
        ps.publicInputSize `shouldEqual` ocaml.publicInputSize
        ps.gates `shouldEqual` ocaml.gates
      Left e, _ -> liftEffect $ throw $ "Failed to parse OCaml JSON: " <> show e
      _, Left e -> liftEffect $ throw $ "Failed to parse PureScript JSON: " <> show e

spec :: (forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)) -> Spec Unit
spec cfg = describe "Linearization Interpreter" do
  describe "Pallas" do
    linearizationTests cfg (Proxy @Pallas.BaseField) PallasTokens.constantTermTokens
  describe "Vesta" do
    linearizationTests cfg (Proxy @Vesta.BaseField) VestaTokens.constantTermTokens
  describe "Circuit comparison" do
    linearizationTickCircuitComparison
    linearizationTockCircuitComparison
