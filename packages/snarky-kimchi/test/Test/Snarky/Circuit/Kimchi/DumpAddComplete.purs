-- | Dump real compiled circuits together with a satisfying witness into the combined JSON
-- | the Lean verified checker ingests (`formal/Kimchi/Json.lean` → `Kimchi.Circuit.check`).
-- |
-- | "The deployed artifact is the proven artifact": the gate list snarky elaborates and the
-- | witness the solver produces are serialized verbatim (field elements as little-endian
-- | hex), so Lean checks the exact object kimchi proves about. Used to validate the Lean
-- | gate transcriptions — a wrong constraint makes `check` reject the real witness.
-- |
-- | Build then run via node on the compiled output (the spago spec runner trips on the
-- | pickles package's generated modules):
-- |   npx spago test -p snarky-kimchi -- --example "dumps add_complete"   # builds
-- |   node -e "import('./output/Test.Snarky.Circuit.Kimchi.DumpAddComplete/index.js').then(m=>{m.dump();m.dumpPoseidon()})"
module Test.Snarky.Circuit.Kimchi.DumpAddComplete
  ( spec
  , dump
  , dumpPoseidon
  , dumpVarBaseMul
  , dumpEndoMul
  , dumpEndoScalar
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, nil, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Class (liftEffect)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Partial.Unsafe (unsafeCrashWith)
import Simple.JSON (writeJSON)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Builder (CircuitBuilderState, constraintsToArray)
import Snarky.Backend.Compile (Solver, compile, makeSolver, runSolver)
import Snarky.Backend.Kimchi (makeGateData, makeWitness)
import Snarky.Backend.Kimchi.Class (circuitGateGetWires)
import Snarky.Backend.Kimchi.Types (gateWiresGetWire, wireGetCol, wireGetRow)
import Snarky.Circuit.DSL (F(..), FVar, SizedF, Snarky, const_)
import Snarky.Circuit.Kimchi.AddComplete (Finiteness(..), addFast)
import Snarky.Circuit.Kimchi.EndoMul (endo)
import Snarky.Circuit.Kimchi.EndoScalar (toField)
import Snarky.Circuit.Kimchi.Poseidon as PoseidonCircuit
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast1)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState(..), GateKind(..), toKimchiRows)
import Snarky.Curves.Class (class PrimeField, endoScalar, fromInt, generator, toAffine)
import Snarky.Curves.Class (EndoScalar(..)) as Cv
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Snarky.Types.Shifted (Type1(..))
import Test.Spec (Spec, it)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type Fp = Vesta.ScalarField

-- | The dump's `typ` strings, matching the OCaml fixtures / the Lean `kindOf` parser.
gateKindToString :: GateKind -> String
gateKindToString = case _ of
  Zero -> "Zero"
  GenericPlonkGate -> "Generic"
  PoseidonGate -> "Poseidon"
  AddCompleteGate -> "CompleteAdd"
  VarBaseMul -> "VarBaseMul"
  EndoMul -> "EndoMul"
  EndoScalar -> "EndoMulScalar"

-- | Shared: extract the gate list + witness from a compiled circuit and a solved input,
-- | and write the combined JSON.
dumpToFile
  :: forall a b
   . String
  -> CircuitBuilderState (KimchiGate Fp) (AuxState Fp)
  -> Solver Fp (KimchiConstraint Fp) a b
  -> a
  -> Effect Unit
dumpToFile path builtState solver input = do
  gd <- makeGateData @Fp
    { constraints: Array.concatMap (toKimchiRows <<< _.constraint)
        (constraintsToArray builtState.constraints)
    , publicInputs: builtState.publicInputs
    , unionFind: (un AuxState builtState.aux).wireState.unionFind
    }
  runSolver solver input >>= case _ of
    Left e -> unsafeCrashWith ("dump " <> path <> ": solver failed: " <> show e)
    Right (Tuple _out assignments) -> do
      let
        { witness, publicInputs } = makeWitness
          { assignments
          , constraints: map _.variables gd.constraints
          , publicInputs: builtState.publicInputs
          }
        gates = Array.mapWithIndex
          ( \i row ->
              let
                gateWires = circuitGateGetWires (unsafeIdx gd.gates i)
                wires = Array.mapWithIndex
                  ( \j _ ->
                      let
                        w = gateWiresGetWire gateWires j
                      in
                        { row: wireGetRow w, col: wireGetCol w }
                  )
                  (Array.replicate 7 unit)
              in
                { typ: gateKindToString row.kind, wires, coeffs: row.coeffs }
          )
          gd.constraints
        json = writeJSON
          { publicInputSize: gd.publicInputSize
          , gates
          , witness: Vector.toUnfoldable witness :: Array (Array Fp)
          , publicInputs
          }
      FS.writeTextFile UTF8 path json
  where
  unsafeIdx arr i = case Array.index arr i of
    Just x -> x
    Nothing -> unsafeCrashWith "dump: gate index out of range"

--------------------------------------------------------------------------------
-- add_complete (Generic + CompleteAdd)

addCompleteCircuit
  :: forall r
   . PrimeField Fp
  => Tuple (AffinePoint (FVar Fp)) (AffinePoint (FVar Fp))
  -> Snarky Fp (KimchiConstraint Fp) r (AffinePoint (FVar Fp))
addCompleteCircuit (Tuple p1 p2) = _.p <$> addFast DontCheckFinite p1 p2

dump :: Effect Unit
dump = do
  let
    toPt g = case toAffine g of
      Just c -> AffinePoint c
      Nothing -> unsafeCrashWith "DumpAddComplete: unexpected point at infinity"
    p1 = toPt (generator :: Pallas.G)
    p2 = toPt ((generator :: Pallas.G) <> (generator :: Pallas.G))
    input = Tuple p1 p2
  builtState <- compile @Fp noAdvice
    (Proxy @(Tuple (AffinePoint Fp) (AffinePoint Fp)))
    (Proxy @(AffinePoint Fp))
    (Proxy @(KimchiConstraint Fp))
    addCompleteCircuit
  let
    solver
      :: Solver Fp (KimchiConstraint Fp)
           (Tuple (AffinePoint Fp) (AffinePoint Fp))
           (AffinePoint Fp)
    solver = makeSolver (Proxy @(KimchiConstraint Fp)) addCompleteCircuit
  dumpToFile "formal/fixtures/add_complete_step.json" builtState solver input

--------------------------------------------------------------------------------
-- poseidon (Poseidon + Zero/Generic)

dumpPoseidon :: Effect Unit
dumpPoseidon = do
  let
    poseidonCircuit
      :: Vector 3 (FVar Fp) -> Snarky Fp (KimchiConstraint Fp) () (Vector 3 (FVar Fp))
    poseidonCircuit = PoseidonCircuit.poseidon

    input :: Vector 3 (F Fp)
    input = F one :< F (one + one) :< F (one + one + one) :< nil
  builtState <- compile @Fp noAdvice
    (Proxy @(Vector 3 (F Fp)))
    (Proxy @(Vector 3 (F Fp)))
    (Proxy @(KimchiConstraint Fp))
    poseidonCircuit
  let
    solver :: Solver Fp (KimchiConstraint Fp) (Vector 3 (F Fp)) (Vector 3 (F Fp))
    solver = makeSolver (Proxy @(KimchiConstraint Fp)) poseidonCircuit
  dumpToFile "formal/fixtures/poseidon_step.json" builtState solver input

--------------------------------------------------------------------------------
-- varbasemul (VarBaseMul + Zero, plus Generic public rows)

dumpVarBaseMul :: Effect Unit
dumpVarBaseMul = do
  let
    circuit
      :: forall r
       . Tuple (AffinePoint (FVar Fp)) (FVar Fp)
      -> Snarky Fp (KimchiConstraint Fp) r (AffinePoint (FVar Fp))
    circuit (Tuple g scalar) = scaleFast1 @51 g (Type1 scalar)
    toPt h = case toAffine h of
      Just c -> AffinePoint c
      Nothing -> unsafeCrashWith "dumpVarBaseMul: infinity"
    input = Tuple (toPt (generator :: Pallas.G)) (F (fromInt 12345))
  builtState <- compile @Fp noAdvice
    (Proxy @(Tuple (AffinePoint Fp) (F Fp)))
    (Proxy @(AffinePoint Fp))
    (Proxy @(KimchiConstraint Fp))
    circuit
  let
    solver :: Solver Fp (KimchiConstraint Fp) (Tuple (AffinePoint Fp) (F Fp)) (AffinePoint Fp)
    solver = makeSolver (Proxy @(KimchiConstraint Fp)) circuit
  dumpToFile "formal/fixtures/varbasemul_step.json" builtState solver input

--------------------------------------------------------------------------------
-- endomul (EndoMul + Zero, plus Generic public rows)

dumpEndoMul :: Effect Unit
dumpEndoMul = do
  let
    circuit
      :: forall r
       . Tuple (AffinePoint (FVar Fp)) (FVar Fp)
      -> Snarky Fp (KimchiConstraint Fp) r (AffinePoint (FVar Fp))
    circuit (Tuple g scalar) = endo @128 @32 g (unsafeCoerce scalar :: SizedF 128 (FVar Fp))
    toPt h = case toAffine h of
      Just c -> AffinePoint c
      Nothing -> unsafeCrashWith "dumpEndoMul: infinity"
    input = Tuple (toPt (generator :: Pallas.G)) (F (fromInt 12345))
  builtState <- compile @Fp noAdvice
    (Proxy @(Tuple (AffinePoint Fp) (F Fp)))
    (Proxy @(AffinePoint Fp))
    (Proxy @(KimchiConstraint Fp))
    circuit
  let
    solver :: Solver Fp (KimchiConstraint Fp) (Tuple (AffinePoint Fp) (F Fp)) (AffinePoint Fp)
    solver = makeSolver (Proxy @(KimchiConstraint Fp)) circuit
  dumpToFile "formal/fixtures/endomul_step.json" builtState solver input

--------------------------------------------------------------------------------
-- endomul_scalar (EndoMulScalar, plus Generic public rows)

dumpEndoScalar :: Effect Unit
dumpEndoScalar = do
  let
    circuit
      :: forall r
       . FVar Fp
      -> Snarky Fp (KimchiConstraint Fp) r (FVar Fp)
    circuit scalar =
      let
        Cv.EndoScalar es = endoScalar @Vesta.BaseField @Fp
      in
        toField @8 (unsafeCoerce scalar :: SizedF 128 (FVar Fp)) (const_ es)
    input = F (fromInt 12345)
  builtState <- compile @Fp noAdvice
    (Proxy @(F Fp))
    (Proxy @(F Fp))
    (Proxy @(KimchiConstraint Fp))
    circuit
  let
    solver :: Solver Fp (KimchiConstraint Fp) (F Fp) (F Fp)
    solver = makeSolver (Proxy @(KimchiConstraint Fp)) circuit
  dumpToFile "formal/fixtures/endoscalar_step.json" builtState solver input

spec :: Spec Unit
spec = do
  it "dumps add_complete fixture for Lean" $ liftEffect dump
  it "dumps poseidon fixture for Lean" $ liftEffect dumpPoseidon
  it "dumps varbasemul fixture for Lean" $ liftEffect dumpVarBaseMul
  it "dumps endomul fixture for Lean" $ liftEffect dumpEndoMul
  it "dumps endoscalar fixture for Lean" $ liftEffect dumpEndoScalar
