-- | Dump the REAL `ipaFinalCheckCircuit` (the in-circuit IPA final verification) as a
-- | (circuit, witness) JSON fixture for the Lean verified checker — the drift guard for the
-- | deployed verifier's own gate stream. Step-side instantiation (Fp = Vesta.ScalarField,
-- | Pallas points — the same field every other fixture uses).
-- |
-- | The circuit does not assert `success`, so a fabricated (generator-multiple) input yields a
-- | satisfying witness with `success = false` — sufficient for constraint-transcription
-- | validation. A `success = true` fixture requires a real step/wrap proof (SRS + minutes).
-- |
-- | Drive from the repo root:
-- |   node -e "import('./output/Test.Pickles.DumpIpa/index.js').then(m=>m.dumpIpaFinalCheck())"
module Test.Pickles.DumpIpa (dumpIpaFinalCheck) where

import Prelude

import Data.Monoid (power)

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, nil, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Partial.Unsafe (unsafeCrashWith)
import Pickles.IPA (IpaFinalCheckInput, ipaFinalCheckCircuit)
import Pickles.Sponge as Sponge
import Pickles.Step.OtherField (ipaScalarOps) as StepOF
import Simple.JSON (writeJSON)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Builder (CircuitBuilderState, constraintsToArray)
import Snarky.Backend.Compile (Solver, compile, makeSolver, runSolver)
import Snarky.Backend.Kimchi (makeGateData, makeWitness)
import Snarky.Backend.Kimchi.Class (circuitGateGetWires)
import Snarky.Backend.Kimchi.Types (gateWiresGetWire, wireGetCol, wireGetRow)
import Snarky.Circuit.DSL (BoolVar, F(..), FVar, SizedF, Snarky, const_)
import Snarky.Circuit.Kimchi (SplitField(..), Type2(..))
import Snarky.Circuit.Kimchi.GroupMap (groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState(..), GateKind(..), toKimchiRows)
import Snarky.Curves.Class (endoScalar, fromInt, generator, toAffine)
import Snarky.Curves.Class (EndoScalar(..)) as Cv
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

type Fp = Vesta.ScalarField
type SfVal = Type2 (SplitField (F Fp) Boolean)
type SfVar = Type2 (SplitField (FVar Fp) (BoolVar Fp))

-- | The dump's `typ` strings (same table as DumpAddComplete).
gateKindToString :: GateKind -> String
gateKindToString = case _ of
  Zero -> "Zero"
  GenericPlonkGate -> "Generic"
  PoseidonGate -> "Poseidon"
  AddCompleteGate -> "CompleteAdd"
  VarBaseMul -> "VarBaseMul"
  EndoMul -> "EndoMul"
  EndoScalar -> "EndoMulScalar"

-- | Extract gates + witness from a compiled circuit and a solved input; write the JSON.
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

-- | Dump the 2-round IPA final check with fabricated inputs.
dumpIpaFinalCheck :: Effect Unit
dumpIpaFinalCheck = do
  let
    stepEndo = let Cv.EndoScalar e = endoScalar @Vesta.BaseField @Fp in e

    circuit
      :: forall r
       . IpaFinalCheckInput 2 (FVar Fp) SfVar
      -> Snarky Fp (KimchiConstraint Fp) r
           { success :: BoolVar Fp, challenges :: Vector 2 (SizedF 128 (FVar Fp)) }
    circuit input =
      Sponge.evalSpongeM Sponge.initialSpongeCircuit
        (ipaFinalCheckCircuit @Fp @Pallas.G StepOF.ipaScalarOps
          { endo: const_ stepEndo, groupMapParams: groupMapParams (Proxy @Pallas.G) }
          input)

    toPt h = case toAffine h of
      Just c -> AffinePoint c
      Nothing -> unsafeCrashWith "dumpIpaFinalCheck: infinity"
    pt k = toPt (power (generator :: Pallas.G) k)
    sf k = Type2 (SplitField { sDiv2: F (fromInt k), sOdd: false })

    input :: IpaFinalCheckInput 2 Fp SfVal
    input =
      { delta: pt 2
      , sg: pt 3
      , lr: ({ l: pt 4, r: pt 5 } :< { l: pt 6, r: pt 7 } :< nil)
      , z1: sf 11
      , z2: sf 12
      , u: pt 8
      , combinedPolynomial: pt 9
      , combinedInnerProduct: sf 13
      , b: sf 14
      , blindingGenerator: pt 10
      }
  builtState <- compile @Fp noAdvice
    (Proxy @(IpaFinalCheckInput 2 Fp SfVal))
    (Proxy @{ success :: Boolean, challenges :: Vector 2 (SizedF 128 (F Fp)) })
    (Proxy @(KimchiConstraint Fp))
    circuit
  let
    solver
      :: Solver Fp (KimchiConstraint Fp)
           (IpaFinalCheckInput 2 Fp SfVal)
           { success :: Boolean, challenges :: Vector 2 (SizedF 128 (F Fp)) }
    solver = makeSolver (Proxy @(KimchiConstraint Fp)) circuit
  dumpToFile "formal/fixtures/ipa_final_check_step.json" builtState solver input
