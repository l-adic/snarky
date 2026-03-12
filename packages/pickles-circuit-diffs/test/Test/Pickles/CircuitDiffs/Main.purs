module Test.Pickles.CircuitDiffs.Main where

import Prelude

import Data.Either (Either(..))
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Pickles.CircuitDiffs.Circuit (Circuit, fromCompiledCircuit, parseCachedConstants, parseCircuitJson)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (F, FVar, exists, mul_)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint, initialState)
import Snarky.Constraint.Kimchi.Types (GateKind)
import Snarky.Curves.Vesta as Vesta
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

type Fp = Vesta.ScalarField

fixtureDir :: String
fixtureDir = "packages/snarky-kimchi/test/fixtures/"

readFixture :: String -> Effect String
readFixture path = do
  buf <- FS.readFile path
  Buffer.toString UTF8 buf

-- | The parts of a circuit that are comparable between OCaml fixtures and PureScript.
-- | OCaml fixtures don't have variables or context, so we strip those.
type ComparableGate f =
  { kind :: GateKind
  , wires :: Array { row :: Int, col :: Int }
  , coeffs :: Array f
  }

type ComparableCircuit f =
  { publicInputSize :: Int
  , gates :: Array (ComparableGate f)
  , cachedConstants :: Array { variable :: Int, value :: f }
  }

comparable :: forall f. Circuit f -> ComparableCircuit f
comparable c =
  { publicInputSize: c.publicInputSize
  , gates: map (\g -> { kind: g.kind, wires: g.wires, coeffs: g.coeffs }) c.gates
  , cachedConstants: c.cachedConstants
  }

--------------------------------------------------------------------------------
-- Circuits

mulCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (FVar Fp)
mulCircuit x = do
  y <- exists (pure (zero :: F Fp))
  mul_ x y

compileMul :: Circuit Fp
compileMul = fromCompiledCircuit $
  compilePure (Proxy @(F Fp)) (Proxy @(F Fp)) (Proxy @(KimchiConstraint Fp)) mulCircuit initialState

--------------------------------------------------------------------------------
-- Test

loadOcamlCircuit :: String -> Effect (Circuit Fp)
loadOcamlCircuit name = do
  circuitJson <- readFixture (fixtureDir <> name <> ".json")
  cachedJson <- readFixture (fixtureDir <> name <> "_cached_constants.json")
  case parseCircuitJson circuitJson, parseCachedConstants cachedJson of
    Right { publicInputSize, gates }, Right cachedConstants ->
      pure { publicInputSize, gates, cachedConstants }
    Left e, _ -> throw $ "Failed to parse circuit JSON: " <> show e
    _, Left e -> throw $ "Failed to parse cached constants: " <> show e

main :: Effect Unit
main = runSpecAndExitProcess [ consoleReporter ] spec

spec :: Spec Unit
spec =
  describe "Circuit comparison" do
    it "mul_circuit matches OCaml" do
      ocaml <- liftEffect $ loadOcamlCircuit "mul_circuit"
      comparable compileMul `shouldEqual` comparable ocaml
