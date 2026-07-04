-- | Dump real compiled circuits together with a satisfying witness into the combined JSON
-- | the Lean verified checker ingests (`formal/Kimchi/Json.lean` → `Kimchi.Circuit.check`).
-- |
-- | "The deployed artifact is the proven artifact": the gate list snarky elaborates and the
-- | witness the solver produces are serialized verbatim (field elements as little-endian
-- | hex), so Lean checks the exact object kimchi proves about. Used to validate the Lean
-- | gate transcriptions — a wrong constraint makes `check` reject the real witness.
-- |
-- | This is a generation TOOL, not a test — it writes committed files, so it is NOT wired
-- | into the test spec (that would run with the wrong cwd and pollute the repo). Drive it
-- | from the repo root via `make dump-fixtures`, which compiles this module and then:
-- |   node -e "import('./output/Test.Snarky.Circuit.Kimchi.DumpAddComplete/index.js').then(m=>m.dumpAll())"
module Test.Snarky.Circuit.Kimchi.DumpAddComplete
  ( addCompleteKindsCoeffs
  , stateTProbe
  , stProbeA
  , stProbeB
  , varBaseMulKindsCoeffs
  , dump
  , dumpPoseidon
  , dumpVarBaseMul
  , dumpEndoMul
  , dumpEndoScalar
  , dumpScaleCombine
  , dumpEndoCombine
  , dumpMsm2
  , dumpFiatShamir
  , dumpAll
  ) where

import Prelude

import Data.Array as Array
import Control.Monad.State.Trans (StateT(..), runStateT)
import Data.Either (Either(..))
import Data.Traversable (traverse)
import Data.Maybe (Maybe(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, nil, (:<))
import Data.Vector as Vector
import Effect (Effect)
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
import JS.BigInt as BigInt
import Snarky.Circuit.DSL (F(..), FVar, SizedF, Snarky, add_, assertEqual_, const_, exists, readCVar, scale_)
import Snarky.Circuit.Kimchi.AddComplete (Finiteness(..), addFast)
import Snarky.Circuit.Kimchi.EndoMul (endo)
import Snarky.Circuit.Kimchi.EndoScalar (toField)
import Snarky.Circuit.Kimchi.Poseidon as PoseidonCircuit
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast1)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState(..), GateKind(..), toKimchiRows)
import Snarky.Curves.Class (class PrimeField, endoScalar, fromBigInt, fromInt, generator, toAffine, toBigInt)
import Snarky.Curves.Class (EndoScalar(..)) as Cv
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Snarky.Types.Shifted (Type1(..))
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

-- | Probe A: bare StateT bind chain, no traverse.
stProbeA :: Effect Int
stProbeA = do
  Tuple a s <- runStateT (do
    x <- StateT \s -> pure (Tuple (s + 1) (s + 10))
    y <- StateT \s -> pure (Tuple (s + 2) (s + 20))
    pure (x + y)) 0
  pure (a * 1000 + s)

-- | Probe B: traverse over 2 elements.
stProbeB :: Effect { xs :: Array Int, final :: Int }
stProbeB = do
  Tuple xs final <- runStateT (traverse (\x -> StateT \s -> pure (Tuple (x + s) (s + 1)))
    [ 10, 20 ]) 0
  pure { xs, final }

-- | Minimal semantics probe for the Lean CoreFn interpreter: StateT-over-Effect traversal.
stateTProbe :: Effect { xs :: Array Int, final :: Int }
stateTProbe = do
  Tuple xs final <- runStateT (traverse (\x -> StateT \s -> pure (Tuple (x + s) (s + 1)))
    [ 10, 20, 30, 40, 50 ]) 0
  pure { xs, final }

-- | Entry point for the Lean CoreFn interpreter (formal/CheckCoreFn.lean): the compiled
-- | elaboration of the addComplete circuit, as plain (kind, coeffs) rows. No file IO, no
-- | solver — just what `compile` emits, for cross-validation against the dumped fixture.
addCompleteKindsCoeffs :: Effect (Array { typ :: String, coeffs :: Array Fp })
addCompleteKindsCoeffs = do
  builtState <- compile @Fp noAdvice
    (Proxy @(Tuple (AffinePoint Fp) (AffinePoint Fp)))
    (Proxy @(AffinePoint Fp))
    (Proxy @(KimchiConstraint Fp))
    addCompleteCircuit
  pure $ map (\r -> { typ: gateKindToString r.kind, coeffs: r.coeffs })
    (Array.concatMap (toKimchiRows <<< _.constraint) (constraintsToArray builtState.constraints))

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

-- | Interpreter entry: the scaleFast1 @51 elaboration as (kind, coeffs) rows.
varBaseMulKindsCoeffs :: Effect (Array { typ :: String, coeffs :: Array Fp })
varBaseMulKindsCoeffs = do
  let
    circuit
      :: forall r
       . Tuple (AffinePoint (FVar Fp)) (FVar Fp)
      -> Snarky Fp (KimchiConstraint Fp) r (AffinePoint (FVar Fp))
    circuit (Tuple g scalar) = scaleFast1 @51 g (Type1 scalar)
  builtState <- compile @Fp noAdvice
    (Proxy @(Tuple (AffinePoint Fp) (F Fp)))
    (Proxy @(AffinePoint Fp))
    (Proxy @(KimchiConstraint Fp))
    circuit
  pure $ map (\r -> { typ: gateKindToString r.kind, coeffs: r.coeffs })
    (Array.concatMap (toKimchiRows <<< _.constraint) (constraintsToArray builtState.constraints))

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

--------------------------------------------------------------------------------
-- scale_combine (the IPA MSM term `p' = acc + [s]·T`): VarBaseMul chain → CompleteAdd

-- | `addFast acc (scaleFast1 g s)` — a scalar-mul whose result feeds an add. This is the atomic
-- | multi-scalar-multiplication term of the IPA opening check (wrap_verifier), and the first
-- | dumped circuit exercising genuine gate-output→gate-input dataflow (VarBaseMul result into a
-- | CompleteAdd input), matching Lean `Kimchi.Circuit.VarBaseMul.scaleCombine_sound`.
dumpScaleCombine :: Effect Unit
dumpScaleCombine = do
  let
    circuit
      :: forall r
       . Tuple (Tuple (AffinePoint (FVar Fp)) (FVar Fp)) (AffinePoint (FVar Fp))
      -> Snarky Fp (KimchiConstraint Fp) r (AffinePoint (FVar Fp))
    circuit (Tuple (Tuple g scalar) acc) =
      _.p <$> (addFast DontCheckFinite acc =<< scaleFast1 @51 g (Type1 scalar))
    toPt h = case toAffine h of
      Just c -> AffinePoint c
      Nothing -> unsafeCrashWith "dumpScaleCombine: infinity"
    input =
      Tuple (Tuple (toPt (generator :: Pallas.G)) (F (fromInt 12345)))
        (toPt ((generator :: Pallas.G) <> (generator :: Pallas.G)))
  builtState <- compile @Fp noAdvice
    (Proxy @(Tuple (Tuple (AffinePoint Fp) (F Fp)) (AffinePoint Fp)))
    (Proxy @(AffinePoint Fp))
    (Proxy @(KimchiConstraint Fp))
    circuit
  let
    solver
      :: Solver Fp (KimchiConstraint Fp)
           (Tuple (Tuple (AffinePoint Fp) (F Fp)) (AffinePoint Fp))
           (AffinePoint Fp)
    solver = makeSolver (Proxy @(KimchiConstraint Fp)) circuit
  dumpToFile "formal/fixtures/scale_combine_step.json" builtState solver input

--------------------------------------------------------------------------------
-- endo_combine (the endo MSM term `p' = acc + [s]·T`): EndoMul chain → CompleteAdd

-- | `addFast acc (endo g c)` — the endo scalar-mul's result feeds an add
-- | (`addComplete (endo q c) delta`, Pickles/IPA.purs), matching Lean
-- | `Kimchi.Circuit.EndoMul.endoCombine_sound`.
dumpEndoCombine :: Effect Unit
dumpEndoCombine = do
  let
    circuit
      :: forall r
       . Tuple (Tuple (AffinePoint (FVar Fp)) (FVar Fp)) (AffinePoint (FVar Fp))
      -> Snarky Fp (KimchiConstraint Fp) r (AffinePoint (FVar Fp))
    circuit (Tuple (Tuple g scalar) acc) = do
      q <- endo @128 @32 g (unsafeCoerce scalar :: SizedF 128 (FVar Fp))
      _.p <$> addFast DontCheckFinite acc q
    toPt h = case toAffine h of
      Just c -> AffinePoint c
      Nothing -> unsafeCrashWith "dumpEndoCombine: infinity"
    input =
      Tuple (Tuple (toPt (generator :: Pallas.G)) (F (fromInt 12345)))
        (toPt ((generator :: Pallas.G) <> (generator :: Pallas.G)))
  builtState <- compile @Fp noAdvice
    (Proxy @(Tuple (Tuple (AffinePoint Fp) (F Fp)) (AffinePoint Fp)))
    (Proxy @(AffinePoint Fp))
    (Proxy @(KimchiConstraint Fp))
    circuit
  let
    solver
      :: Solver Fp (KimchiConstraint Fp)
           (Tuple (Tuple (AffinePoint Fp) (F Fp)) (AffinePoint Fp))
           (AffinePoint Fp)
    solver = makeSolver (Proxy @(KimchiConstraint Fp)) circuit
  dumpToFile "formal/fixtures/endo_combine_step.json" builtState solver input

--------------------------------------------------------------------------------
-- msm2 (a 2-term MSM): acc + [s1]·G1 + [s2]·G2 — the scale-combine folded

-- | Two scale-combine terms folded: the core of the verifier's Lagrange/IPA MSM,
-- | matching Lean `Kimchi.Circuit.VarBaseMul.msm_sound` (n = 2).
dumpMsm2 :: Effect Unit
dumpMsm2 = do
  let
    circuit
      :: forall r
       . Tuple (Tuple (Tuple (AffinePoint (FVar Fp)) (FVar Fp))
            (Tuple (AffinePoint (FVar Fp)) (FVar Fp))) (AffinePoint (FVar Fp))
      -> Snarky Fp (KimchiConstraint Fp) r (AffinePoint (FVar Fp))
    circuit (Tuple (Tuple (Tuple g1 s1) (Tuple g2 s2)) acc) = do
      q1 <- scaleFast1 @51 g1 (Type1 s1)
      r1 <- _.p <$> addFast DontCheckFinite acc q1
      q2 <- scaleFast1 @51 g2 (Type1 s2)
      _.p <$> addFast DontCheckFinite r1 q2
    toPt h = case toAffine h of
      Just c -> AffinePoint c
      Nothing -> unsafeCrashWith "dumpMsm2: infinity"
    input =
      Tuple
        (Tuple (Tuple (toPt (generator :: Pallas.G)) (F (fromInt 12345)))
          (Tuple (toPt ((generator :: Pallas.G) <> (generator :: Pallas.G))) (F (fromInt 6789))))
        (toPt ((generator :: Pallas.G) <> (generator :: Pallas.G) <> (generator :: Pallas.G)))
  builtState <- compile @Fp noAdvice
    (Proxy @(Tuple (Tuple (Tuple (AffinePoint Fp) (F Fp)) (Tuple (AffinePoint Fp) (F Fp)))
        (AffinePoint Fp)))
    (Proxy @(AffinePoint Fp))
    (Proxy @(KimchiConstraint Fp))
    circuit
  let
    solver
      :: Solver Fp (KimchiConstraint Fp)
           (Tuple (Tuple (Tuple (AffinePoint Fp) (F Fp)) (Tuple (AffinePoint Fp) (F Fp)))
             (AffinePoint Fp))
           (AffinePoint Fp)
    solver = makeSolver (Proxy @(KimchiConstraint Fp)) circuit
  dumpToFile "formal/fixtures/msm2_step.json" builtState solver input

--------------------------------------------------------------------------------
-- fiat_shamir (Rung 4): Poseidon transcript → challenge split → EndoScalar decode

-- | Squeeze a Poseidon transcript, split the squeezed element as `sq = lo + 2^128·hi`
-- | (the challenge truncation), and endo-decode the 128-bit challenge `lo` via the
-- | EndoMulScalar chain — matching Lean `Kimchi.Circuit.FiatShamir.fiatShamir_sound`.
dumpFiatShamir :: Effect Unit
dumpFiatShamir = do
  let
    p128 = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt 128)

    circuit
      :: forall r
       . Vector 3 (FVar Fp)
      -> Snarky Fp (KimchiConstraint Fp) r (FVar Fp)
    circuit v = do
      out <- PoseidonCircuit.poseidon v
      let
        sq = case Array.index (Vector.toUnfoldable out) 0 of
          Just x -> x
          Nothing -> unsafeCrashWith "dumpFiatShamir: empty state"
      lo <- exists do
        s <- readCVar sq
        pure (F (fromBigInt (toBigInt s `mod` p128)))
      hi <- exists do
        s <- readCVar sq
        pure (F (fromBigInt (toBigInt s `div` p128)))
      assertEqual_ sq (add_ lo (scale_ (fromBigInt p128) hi))
      let Cv.EndoScalar es = endoScalar @Vesta.BaseField @Fp
      -- the high part is also crumb-decomposed (challenge canonicity: hi < 2^128)
      _ <- toField @8 (unsafeCoerce hi :: SizedF 128 (FVar Fp)) (const_ es)
      toField @8 (unsafeCoerce lo :: SizedF 128 (FVar Fp)) (const_ es)

    input :: Vector 3 (F Fp)
    input = F (fromInt 5) :< F (fromInt 6) :< F (fromInt 7) :< nil
  builtState <- compile @Fp noAdvice
    (Proxy @(Vector 3 (F Fp)))
    (Proxy @(F Fp))
    (Proxy @(KimchiConstraint Fp))
    circuit
  let
    solver :: Solver Fp (KimchiConstraint Fp) (Vector 3 (F Fp)) (F Fp)
    solver = makeSolver (Proxy @(KimchiConstraint Fp)) circuit
  dumpToFile "formal/fixtures/fiat_shamir_step.json" builtState solver input

-- | Regenerate every committed fixture. Run from the repo root so the relative
-- | `formal/fixtures/…` paths resolve.
dumpAll :: Effect Unit
dumpAll = do
  dump
  dumpPoseidon
  dumpVarBaseMul
  dumpEndoMul
  dumpEndoScalar
  dumpScaleCombine
  dumpEndoCombine
  dumpMsm2
  dumpFiatShamir
