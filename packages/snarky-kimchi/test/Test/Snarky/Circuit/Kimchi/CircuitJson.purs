module Test.Snarky.Circuit.Kimchi.CircuitJson (spec, structuralMatch, debugCompare) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Traversable (sequence_)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console (log)
import Effect.Exception (throw)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Snarky.Backend.Compile (compilePure)
import Snarky.Backend.Kimchi.CircuitJson (CircuitData, circuitToJson, readCircuitJson)
import Snarky.Circuit.DSL (BoolVar, F, FVar, all_, and_, any_, assertEqual_, assertNonZero_, assertNotEqual_, assertSquare_, assert_, div_, equals_, exists, if_, inv_, mul_, or_, unpack_, xor_)
import Snarky.Circuit.DSL.Monad (class CircuitM, Snarky)
import Snarky.Constraint.Kimchi (KimchiConstraint, initialState)
import Snarky.Curves.Class (class SerdeHex)
import Snarky.Curves.Vesta as Vesta
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

type Fp = Vesta.ScalarField

-- Helper to compile a field→field circuit
compileFF
  :: (forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (FVar Fp))
  -> String
compileFF circuit = circuitToJson @Fp $
  compilePure (Proxy @(F Fp)) (Proxy @(F Fp)) (Proxy @(KimchiConstraint Fp)) circuit initialState

-- Helper to compile a field→bool circuit
compileFB
  :: (forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (BoolVar Fp))
  -> String
compileFB circuit = circuitToJson @Fp $
  compilePure (Proxy @(F Fp)) (Proxy @Boolean) (Proxy @(KimchiConstraint Fp)) circuit initialState

-- Helper to compile a field→unit circuit
compileFU
  :: (forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m Unit)
  -> String
compileFU circuit = circuitToJson @Fp $
  compilePure (Proxy @(F Fp)) (Proxy @Unit) (Proxy @(KimchiConstraint Fp)) circuit initialState

-- Helper to compile a bool→bool circuit
compileBB
  :: (forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m (BoolVar Fp))
  -> String
compileBB circuit = circuitToJson @Fp $
  compilePure (Proxy @Boolean) (Proxy @Boolean) (Proxy @(KimchiConstraint Fp)) circuit initialState

-- Helper to compile a bool→unit circuit
compileBU
  :: (forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m Unit)
  -> String
compileBU circuit = circuitToJson @Fp $
  compilePure (Proxy @Boolean) (Proxy @Unit) (Proxy @(KimchiConstraint Fp)) circuit initialState

--------------------------------------------------------------------------------
-- Field arithmetic circuits (input: field, output: field)

mulCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (FVar Fp)
mulCircuit x = do
  y <- exists (pure (zero :: F Fp))
  mul_ x y

invCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (FVar Fp)
invCircuit x = inv_ x

divCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (FVar Fp)
divCircuit x = do
  y <- exists (pure (zero :: F Fp))
  div_ x y

ifCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (FVar Fp)
ifCircuit x = do
  y <- exists (pure (zero :: F Fp))
  b <- exists (pure true)
  if_ b x y

-- Field→Boolean circuit
equalsCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m (BoolVar Fp)
equalsCircuit x = do
  y <- exists (pure (zero :: F Fp))
  equals_ x y

--------------------------------------------------------------------------------
-- Assertion circuits (input: field, output: unit)

assertEqualCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m Unit
assertEqualCircuit x = do
  y <- exists (pure (zero :: F Fp))
  assertEqual_ x y

assertSquareCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m Unit
assertSquareCircuit x = do
  y <- exists (pure (zero :: F Fp))
  assertSquare_ x y

assertNonZeroCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m Unit
assertNonZeroCircuit x = assertNonZero_ x

assertNotEqualCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m Unit
assertNotEqualCircuit x = do
  y <- exists (pure (zero :: F Fp))
  assertNotEqual_ x y

unpackCircuit :: forall c t m. CircuitM Fp c t m => FVar Fp -> Snarky c t m Unit
unpackCircuit x = do
  _ <- unpack_ x (Proxy @254)
  pure unit

--------------------------------------------------------------------------------
-- Boolean circuits (input: bool, output: bool)

boolAndCircuit :: forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m (BoolVar Fp)
boolAndCircuit x = do
  y <- exists (pure true)
  and_ x y

boolOrCircuit :: forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m (BoolVar Fp)
boolOrCircuit x = do
  y <- exists (pure true)
  or_ x y

boolXorCircuit :: forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m (BoolVar Fp)
boolXorCircuit x = do
  y <- exists (pure true)
  xor_ x y

boolAllCircuit :: forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m (BoolVar Fp)
boolAllCircuit x = do
  y <- exists (pure true)
  w <- exists (pure true)
  all_ [ x, y, w ]

boolAnyCircuit :: forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m (BoolVar Fp)
boolAnyCircuit x = do
  y <- exists (pure true)
  w <- exists (pure true)
  any_ [ x, y, w ]

-- Boolean assertion (input: bool, output: unit)
boolAssertCircuit :: forall c t m. CircuitM Fp c t m => BoolVar Fp -> Snarky c t m Unit
boolAssertCircuit x = assert_ x

--------------------------------------------------------------------------------
-- | Load an OCaml JSON file and parse a PureScript JSON string
loadCircuits
  :: forall @f
   . SerdeHex f
  => Eq f
  => Show f
  => String
  -> String
  -> Aff { ocaml :: CircuitData f, ps :: CircuitData f }
loadCircuits ocamlPath psJson = do
  ocamlJson <- liftEffect do
    buf <- FS.readFile ocamlPath
    Buffer.toString UTF8 buf
  let
    ocamlCircuit :: Either _ (CircuitData f)
    ocamlCircuit = readCircuitJson ocamlJson

    psCircuit :: Either _ (CircuitData f)
    psCircuit = readCircuitJson psJson
  case ocamlCircuit, psCircuit of
    Right oc, Right ps -> pure { ocaml: oc, ps }
    Left e, _ -> liftEffect $ throw $ "Failed to parse OCaml JSON: " <> show e
    _, Left e -> liftEffect $ throw $ "Failed to parse PureScript JSON: " <> show e

ocamlDir :: String
ocamlDir = "packages/snarky-kimchi/test/fixtures/"

-- | Exact match: public input size, gate count, gates
exactMatch :: String -> String -> Spec Unit
exactMatch name psJson =
  it (name <> " matches OCaml exactly") do
    c <- loadCircuits @Fp (ocamlDir <> name <> ".json") psJson
    c.ps.publicInputSize `shouldEqual` c.ocaml.publicInputSize
    c.ps.gates `shouldEqual` c.ocaml.gates

-- | Structural match: public input size, gate count, gate kinds
structuralMatch :: String -> String -> Spec Unit
structuralMatch name psJson =
  it (name <> " structurally matches OCaml (pi, gate count, gate kinds)") do
    c <- loadCircuits @Fp (ocamlDir <> name <> ".json") psJson
    c.ps.publicInputSize `shouldEqual` c.ocaml.publicInputSize
    Array.length c.ps.gates `shouldEqual` Array.length c.ocaml.gates
    map _.kind c.ps.gates `shouldEqual` map _.kind c.ocaml.gates

-- | Debug: print both circuits for comparison
debugCompare :: String -> String -> Spec Unit
debugCompare name psJson =
  it (name <> " debug comparison") do
    c <- loadCircuits @Fp (ocamlDir <> name <> ".json") psJson
    log $ "\n=== " <> name <> " ==="
    log $ "OCaml (pi=" <> show c.ocaml.publicInputSize <> ", gates=" <> show (Array.length c.ocaml.gates) <> "):"
    Array.mapWithIndex (\i g -> log $ "  [" <> show i <> "] " <> show g.kind <> " wires=" <> show g.wires <> " coeffs=" <> show g.coeffs) c.ocaml.gates # sequence_
    log $ "PS (pi=" <> show c.ps.publicInputSize <> ", gates=" <> show (Array.length c.ps.gates) <> "):"
    Array.mapWithIndex (\i g -> log $ "  [" <> show i <> "] " <> show g.kind <> " wires=" <> show g.wires <> " coeffs=" <> show g.coeffs) c.ps.gates # sequence_

spec :: Spec Unit
spec =
  describe "CircuitJson comparison" do
    describe "Exact matches" do
      exactMatch "mul_circuit" (compileFF mulCircuit)
      exactMatch "inv_circuit" (compileFF invCircuit)
      exactMatch "assert_equal_circuit" (compileFU assertEqualCircuit)
      exactMatch "assert_non_zero_circuit" (compileFU assertNonZeroCircuit)
      exactMatch "div_circuit" (compileFF divCircuit)
      exactMatch "equals_circuit" (compileFB equalsCircuit)
      exactMatch "if_circuit" (compileFF ifCircuit)
      exactMatch "assert_not_equal_circuit" (compileFU assertNotEqualCircuit)
      exactMatch "bool_and_circuit" (compileBB boolAndCircuit)
      exactMatch "bool_or_circuit" (compileBB boolOrCircuit)
      exactMatch "bool_assert_circuit" (compileBU boolAssertCircuit)
      exactMatch "bool_xor_circuit" (compileBB boolXorCircuit)
      exactMatch "bool_all_circuit" (compileBB boolAllCircuit)
      exactMatch "bool_any_circuit" (compileBB boolAnyCircuit)
      exactMatch "assert_square_circuit" (compileFU assertSquareCircuit)
      exactMatch "unpack_circuit" (compileFU unpackCircuit)
