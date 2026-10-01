module Test.Pickles.CircuitDiffs.Main where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRecM)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Int.Bits as Bits
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import JS.BigInt as BigInt
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Perms (all, mkPerms)
import Node.FS.Sync as FS
import Partial.Unsafe (unsafeCrashWith)
import Pickles.CircuitDiffs.Circuit (ComparableCircuit, parseOcamlFixtures)
import Pickles.CircuitDiffs.PureScript.BCorrect (compileBCorrect, compileBCorrectWrap)
import Pickles.CircuitDiffs.PureScript.BindVk (compileBindVkStep)
import Pickles.CircuitDiffs.PureScript.BulletReduce (compileBulletReduce)
import Pickles.CircuitDiffs.PureScript.BulletReduceOne (compileBulletReduceOne)
import Pickles.CircuitDiffs.PureScript.BulletReduceOneStep (compileBulletReduceOneStep)
import Pickles.CircuitDiffs.PureScript.BulletReduceStep (compileBulletReduceStep)
import Pickles.CircuitDiffs.PureScript.CheckBulletproofStep (compileCheckBulletproofStep)
import Pickles.CircuitDiffs.PureScript.CheckBulletproofWrap (compileCheckBulletproofWrap)
import Pickles.CircuitDiffs.PureScript.Cip (compileCipStep, compileCipWrap)
import Pickles.CircuitDiffs.PureScript.CombinePoly (compileCombinePoly)
import Pickles.CircuitDiffs.PureScript.Common (StepArtifact, WrapArtifact)
import Pickles.Dump.Circuit (Circuit, comparable, fromCompiledCircuit)
import Pickles.Dump.Constants (DerivedKey)
import Pickles.CircuitDiffs.PureScript.ExpandPlonk (compileExpandPlonkStep, compileExpandPlonkWrap)
import Pickles.CircuitDiffs.PureScript.FopStep (compileFopStep)
import Pickles.CircuitDiffs.PureScript.FopStepChunks2 (compileFopStepChunks2)
import Pickles.CircuitDiffs.PureScript.FopWrap (compileFopWrap)
import Pickles.CircuitDiffs.PureScript.FqSpongeTranscript (compileFqSpongeTranscriptStep)
import Pickles.CircuitDiffs.PureScript.FqSpongeTranscriptWrap (compileFqSpongeTranscriptWrap)
import Pickles.CircuitDiffs.PureScript.FtEval0Step (compileFtEval0Step)
import Pickles.CircuitDiffs.PureScript.Ftcomm (compileFtcomm)
import Pickles.CircuitDiffs.PureScript.FtcommStep (compileFtcommStep)
import Pickles.CircuitDiffs.PureScript.FullStepVerifyOne (compileFullStepVerifyOne)
import Pickles.CircuitDiffs.PureScript.FullStepVerifyOneN2 (compileFullStepVerifyOneN2)
import Pickles.CircuitDiffs.PureScript.GroupMap (compileGroupMap)
import Pickles.CircuitDiffs.PureScript.GroupMapStep (compileGroupMapStep)
import Pickles.CircuitDiffs.PureScript.HashMessagesStep (compileHashMessagesStep)
import Pickles.CircuitDiffs.PureScript.HashMessagesWrap (compileHashMessagesWrap)
import Pickles.CircuitDiffs.PureScript.IvpStep (compileIvpStep)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams, compileIvpWrap)
import Pickles.CircuitDiffs.PureScript.LinearizationStep (compileLinearizationStep)
import Pickles.CircuitDiffs.PureScript.LinearizationWrap (compileLinearizationWrap)
import Pickles.CircuitDiffs.PureScript.OtherFieldCheck (compileOtherFieldCheck)
import Pickles.CircuitDiffs.PureScript.PlonkChecksPassed (compilePlonkChecksPassedStep, compilePlonkChecksPassedWrap)
import Pickles.CircuitDiffs.PureScript.Pow2Pow (compilePow2Pow)
import Pickles.CircuitDiffs.PureScript.PseudoCircuits (compileChooseKeyN1Wrap, compileOneHotN17Step, compileOneHotN17Wrap, compileOneHotN1Step, compileOneHotN1Wrap, compileOneHotN3Step, compileOneHotN3Wrap, compilePseudoChooseN1Step, compilePseudoChooseN1Wrap, compilePseudoChooseN3Step, compilePseudoChooseN3Wrap, compilePseudoMaskN17Step, compilePseudoMaskN17Wrap, compilePseudoMaskN1Step, compilePseudoMaskN1Wrap, compilePseudoMaskN3Step, compilePseudoMaskN3Wrap, compilePseudoToDomainWrap, compileSideloadedVkTypStep, compileUtilsOnesVectorN16Step, compileUtilsOnesVectorN16Wrap)
import Pickles.CircuitDiffs.PureScript.SchnorrVerify (compileSchnorrVerify)
import Pickles.CircuitDiffs.PureScript.SpongeChallenges (compileChallengeDigestStep, compileChallengeDigestWrap, compileSpongeAndChallengesStep, compileSpongeAndChallengesWrap)
import Pickles.CircuitDiffs.PureScript.StepMainAddOneReturn (compileStepMainAddOneReturn)
import Pickles.CircuitDiffs.PureScript.StepMainChunks2 (compileStepMainChunks2)
import Pickles.CircuitDiffs.PureScript.StepMainImportTwoPhaseChain (StepMainImportTwoPhaseChainParams, compileStepMainImportTwoPhaseChainWithConstants)
import Pickles.CircuitDiffs.PureScript.StepMainNoRecursionReturn (StepMainNoRecursionReturnParams, compileStepMainNoRecursionReturn)
import Pickles.CircuitDiffs.PureScript.StepMainSideLoadedChild (compileStepMainSideLoadedChild)
import Pickles.CircuitDiffs.PureScript.StepMainSideLoadedMain (compileStepMainSideLoadedMain)
import Pickles.CircuitDiffs.PureScript.StepMainSimpleChain (compileStepMainSimpleChain)
import Pickles.CircuitDiffs.PureScript.StepMainSimpleChainN2 (compileStepMainSimpleChainN2WithConstants)
import Pickles.CircuitDiffs.PureScript.StepMainTreeProofReturn (StepMainTreeProofReturnParams, compileStepMainTreeProofReturnWithConstants)
import Pickles.CircuitDiffs.PureScript.StepMainTwoPhaseChainIncrement (compileStepMainTwoPhaseChainIncrementWithConstants)
import Pickles.CircuitDiffs.PureScript.StepMainTwoPhaseChainMakeZero (compileStepMainTwoPhaseChainMakeZero, compileStepMainTwoPhaseChainMakeZeroWithConstants)
import Pickles.CircuitDiffs.PureScript.StepVerify (compileStepVerify)
import Pickles.CircuitDiffs.PureScript.StepVerifyN2 (compileStepVerifyN2)
import Pickles.CircuitDiffs.PureScript.WrapFinalize (compileWrapFinalizeN2)
import Pickles.CircuitDiffs.PureScript.WrapMain (compileWrapMainN1)
import Pickles.CircuitDiffs.PureScript.WrapMainAddOneReturn (compileWrapMainAddOneReturn)
import Pickles.CircuitDiffs.PureScript.WrapMainChunks2 (compileWrapMainChunks2)
import Pickles.CircuitDiffs.PureScript.WrapMainImportTwoPhaseChain (compileWrapMainImportTwoPhaseChain)
import Pickles.CircuitDiffs.PureScript.WrapMainN2 (compileWrapMainN2)
import Pickles.CircuitDiffs.PureScript.WrapMainSideLoadedMain (compileWrapMainSideLoadedMain)
import Pickles.CircuitDiffs.PureScript.WrapMainTreeProofReturn (compileWrapMainTreeProofReturn)
import Pickles.CircuitDiffs.PureScript.WrapMainTwoPhaseChain (WrapMainTwoPhaseChainParams, compileWrapMainTwoPhaseChain)
import Pickles.CircuitDiffs.PureScript.WrapVerify (compileWrapVerify)
import Pickles.CircuitDiffs.PureScript.WrapVerifyN2 (compileWrapVerifyN2)
import Pickles.CircuitDiffs.PureScript.Xhat (compileXhat)
import Pickles.CircuitDiffs.PureScript.XhatBranches (compileXhatBranches)
import Pickles.CircuitDiffs.PureScript.XhatStep (compileXhatStep)
import Pickles.CircuitDiffs.Types (CircuitComparison, Constants(..))
import Pickles.CircuitDiffs.Types as Dump
import Pickles.PublicInputCommit (LagrangeBaseLookup, mkConstLagrangeBaseLookup)
import Safe.Coerce (coerce)
import Simple.JSON (writeJSON)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Backend.Kimchi.Impl.Pallas (pallasCrsCreate)
import Snarky.Backend.Kimchi.Impl.Vesta (vestaCrsCreate)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (class BasicSystem, class CheckedType, class CircuitType, BoolVar, F(..), FVar, SizedF, addConstraint, all_, and_, any_, assertEqual_, assertNonZero_, assertNotEqual_, assertSquare_, assert_, const_, div_, equals_, exists, if_, inv_, mul_, or_, pow_, unpack_, xor_)
import Snarky.Circuit.DSL.Monad (Snarky)
import Snarky.Circuit.Kimchi.AddComplete (Finiteness(..), addFast)
import Snarky.Circuit.Kimchi.EndoMul (endo)
import Snarky.Circuit.Kimchi.EndoScalar (toField)
import Snarky.Circuit.Kimchi.Poseidon (poseidon)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast1, scaleFast2')
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Curves.Class (class PrimeField, class SerdeHex, EndoScalar(..), endoScalar, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Snarky.Types.Shifted (Type1(..))
import Test.Spec (SpecT, beforeAll_, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess')
import Test.Spec.Runner.Node.Config as Cfg
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type Fp = Vesta.ScalarField
type Fq = Pallas.ScalarField

fixtureDir :: String
fixtureDir = "packages/pickles-circuit-diffs/circuits/ocaml/"

readFixture :: String -> Effect String
readFixture path = do
  buf <- FS.readFile path
  Buffer.toString UTF8 buf

--------------------------------------------------------------------------------
-- SRS FFI

foreign import pallasSrsBlindingGenerator :: CRS VestaG -> AffinePoint Fq
foreign import vestaSrsBlindingGenerator :: CRS PallasG -> AffinePoint Fp

-- Index-based per-commitment lookup, OCaml-parity for
-- `Kimchi_bindings.Protocol.SRS.Fq/Fp.lagrange_commitment`. The per-index
-- variants remove the "numPublic" parameter at call sites — the walk fetches
-- commitments on demand from kimchi's cached basis.
foreign import pallasSrsLagrangeCommitmentAt :: CRS VestaG -> Int -> Int -> AffinePoint Fq
foreign import pallasSrsLagrangeCommitmentChunksAt :: CRS VestaG -> Int -> Int -> Array (AffinePoint Fq)
foreign import vestaSrsLagrangeCommitmentAt :: CRS PallasG -> Int -> Int -> AffinePoint Fp

--------------------------------------------------------------------------------
-- Output directories for serialized comparable circuits

resultsDir :: String
resultsDir = "packages/pickles-circuit-diffs/circuits/results/"

writeComparison :: String -> CircuitComparison -> Effect Unit
writeComparison path c = FS.writeTextFile UTF8 path (writeJSON c)

-- | A circuit and the constants it was compiled with, as its comparison dump carries them.
type Compared f = { circuit :: Circuit f, constants :: Maybe Constants }

-- | A point as its decimal coordinates.
fPoint :: forall f. PrimeField f => AffinePoint (F f) -> Dump.Point
fPoint (AffinePoint { x: F x, y: F y }) = [ BigInt.toString (toBigInt x), BigInt.toString (toBigInt y) ]

-- | A circuit compiled over `srsData`, with its `Xhat` constants: the blinding base and the
-- | first `count` Lagrange bases.
withXhat
  :: forall n f r g
   . PrimeField f
  => Int
  -> { lagrangeAt :: LagrangeBaseLookup n f, blindingH :: AffinePoint (F f) | r }
  -> Circuit g
  -> Compared g
withXhat count srsData circuit =
  { circuit
  , constants: Just $ Xhat
      { h: fPoint srsData.blindingH
      , lagrange: Array.range 0 (count - 1) <#> \i ->
          map fPoint (Vector.toUnfoldable (srsData.lagrangeAt i).constant)
      }
  }

-- | A circuit compiled over per-branch Lagrange tables, with its `XhatBranches` constants:
-- | the blinding base and each branch's first `count` bases.
withXhatBranches
  :: forall branches n r g
   . { lagrangeTable :: Int -> Vector branches (Vector n (AffinePoint (F Fq))), blindingH :: AffinePoint (F Fq) | r }
  -> Int
  -> Circuit g
  -> Compared g
withXhatBranches config count circuit =
  { circuit
  , constants: Just $ XhatBranches
      { h: fPoint config.blindingH
      , lagrange: Array.transpose $ Array.range 0 (count - 1) <#> \i ->
          map (map fPoint <<< Vector.toUnfoldable) (Vector.toUnfoldable (config.lagrangeTable i))
      }
  }

-- | A wrap artifact's circuit, with the constants it bakes in.
withWrapConstants :: WrapArtifact -> Effect (Compared Fq)
withWrapConstants art =
  fromCompiledCircuit art.wrapCs <#> \circuit -> { circuit, constants: Just art.constants }

-- | A step artifact's circuit, with the constants it bakes in.
withStepConstants :: { art :: StepArtifact, constants :: Constants } -> Effect (Compared Fp)
withStepConstants r =
  fromCompiledCircuit r.art.stepCs <#> \circuit -> { circuit, constants: Just r.constants }

-- | `withStepConstants` for a step circuit whose self slots verify against
-- | its tag's wrap key, `wrapArt`'s.
withSelfKey
  :: WrapArtifact
  -> { art :: StepArtifact, constants :: DerivedKey PallasG Fq -> Effect Constants }
  -> Effect (Compared Fp)
withSelfKey wrapArt r = do
  constants <- r.constants wrapArt.wrapKey
  withStepConstants { art: r.art, constants }

-- | The wrap circuits of the tags whose step circuits are dumped: each
-- | `wrap_main_*` fixture of such a tag, and the key its step circuit's
-- | self slots verify against. `simple_chain_n2` and `tree_proof_return`
-- | use `override_wrap_domain:N1`.
simpleChainN2Wrap :: SrsBundle -> Effect WrapArtifact
simpleChainN2Wrap bundle =
  compileWrapMainN2
    { lagrangeAt: mkConstLagrangeBaseLookup \i ->
        Vector.singleton (coerce (pallasSrsLagrangeCommitmentAt bundle.vestaCrs16 15 i))
    , blindingH: coerce $ pallasSrsBlindingGenerator bundle.vestaCrs16
    }
    (stepLagrangeData bundle.pallasCrs15 14)

-- | `tree_proof_return`'s wrap circuit (`simpleChainN2Wrap`). Its step
-- | slots read the No_recursion_return wrap key's basis at 2^13 and its
-- | own at 2^14.
treeProofReturnWrap :: SrsBundle -> Effect WrapArtifact
treeProofReturnWrap bundle =
  compileWrapMainTreeProofReturn
    { lagrangeAt: mkConstLagrangeBaseLookup \i ->
        Vector.singleton (coerce (pallasSrsLagrangeCommitmentAt bundle.vestaCrs16 15 i))
    , blindingH: coerce $ pallasSrsBlindingGenerator bundle.vestaCrs16
    }
    (treeProofReturnParams bundle)

-- | `two_phase_chain`'s wrap circuit (`simpleChainN2Wrap`): two branches,
-- | make_zero and increment, sharing one wrap key.
twoPhaseChainWrap :: SrsBundle -> Effect WrapArtifact
twoPhaseChainWrap bundle = compileWrapMainTwoPhaseChain (twoPhaseChainParams bundle)

-- | `import_two_phase_chain`'s wrap circuit (`simpleChainN2Wrap`). No
-- | OCaml fixture: it is compiled for its key alone.
importTwoPhaseChainWrap :: SrsBundle -> Effect WrapArtifact
importTwoPhaseChainWrap bundle =
  compileWrapMainImportTwoPhaseChain
    { lagrangeAt: mkConstLagrangeBaseLookup \i ->
        Vector.singleton (coerce (pallasSrsLagrangeCommitmentAt bundle.vestaCrs16 15 i))
    , blindingH: coerce $ pallasSrsBlindingGenerator bundle.vestaCrs16
    }
    (importTwoPhaseChainParams bundle)

-- | A step circuit's SRS data: the `srs` Lagrange basis at `2^log2` and its
-- | blinding base.
stepLagrangeData
  :: CRS PallasG
  -> Int
  -> { lagrangeAt :: LagrangeBaseLookup 1 Fp, blindingH :: AffinePoint (F Fp) }
stepLagrangeData srs log2 =
  { lagrangeAt: stepLagrangeAt srs log2
  , blindingH: (coerce $ vestaSrsBlindingGenerator srs) :: AffinePoint (F Fp)
  }

-- | The `srs` Lagrange basis at `2^log2`, as a step circuit reads it.
stepLagrangeAt :: CRS PallasG -> Int -> LagrangeBaseLookup 1 Fp
stepLagrangeAt srs log2 = mkConstLagrangeBaseLookup \i ->
  Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt srs log2 i)) :: AffinePoint (F Fp))

-- | `tree_proof_return`'s step params: slot 0 a No_recursion_return proof,
-- | its wrap circuit compiled from the NRR wrap and step data; slot 1 self.
treeProofReturnParams :: SrsBundle -> StepMainTreeProofReturnParams
treeProofReturnParams bundle =
  { slot0LagrangeAt: stepLagrangeAt bundle.pallasCrs15 13
  , slot1LagrangeAt: stepLagrangeAt bundle.pallasCrs15 14
  , blindingH: (coerce $ vestaSrsBlindingGenerator bundle.pallasCrs15) :: AffinePoint (F Fp)
  , nrrWrapSrsData:
      { lagrangeAt: mkConstLagrangeBaseLookup \i ->
          Vector.singleton (coerce (pallasSrsLagrangeCommitmentAt bundle.vestaCrs16 9 i))
      , blindingH: coerce $ pallasSrsBlindingGenerator bundle.vestaCrs16
      }
  , nrrStepSrsData: stepLagrangeData bundle.pallasCrs15 14
  }

-- | `two_phase_chain`'s wrap params: both branches' step data at 2^14.
twoPhaseChainParams :: SrsBundle -> WrapMainTwoPhaseChainParams
twoPhaseChainParams bundle =
  { vestaSrs: bundle.vestaCrs16
  , blindingH: coerce $ pallasSrsBlindingGenerator bundle.vestaCrs16
  , makeZeroStepSrsData: stepLagrangeData bundle.pallasCrs15 14
  , incrementStepSrsData: stepLagrangeData bundle.pallasCrs15 14
  }

-- | `import_two_phase_chain`'s step params: an External slot over
-- | `two_phase_chain` beside a Self slot, both reading the 2^14 basis.
importTwoPhaseChainParams :: SrsBundle -> StepMainImportTwoPhaseChainParams
importTwoPhaseChainParams bundle =
  { slot0LagrangeAt: stepLagrangeAt bundle.pallasCrs15 14
  , slot1LagrangeAt: stepLagrangeAt bundle.pallasCrs15 14
  , blindingH: (coerce $ vestaSrsBlindingGenerator bundle.pallasCrs15) :: AffinePoint (F Fp)
  , twoPhaseChainSrsData: twoPhaseChainParams bundle
  }

appendManifest :: String -> String -> Effect Unit
appendManifest name status =
  FS.appendTextFile UTF8 (resultsDir <> "manifest.jsonl")
    (writeJSON { name, status } <> "\n")

resetOutputDirs :: Effect Unit
resetOutputDirs = do
  let rmOpts = { force: true, maxRetries: 0, recursive: true, retryDelay: 0 }
  let mkdirOpts = { recursive: true, mode: mkPerms all all all }
  FS.rm' resultsDir rmOpts
  FS.mkdir' resultsDir mkdirOpts

--------------------------------------------------------------------------------
-- Compile helpers (basic circuits, Fp only)

compileFF :: (forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r (FVar Fp)) -> Effect (Circuit Fp)
compileFF circuit = fromCompiledCircuit =<<
  (compile noAdvice (Proxy @(F Fp)) (Proxy @(F Fp)) (Proxy @(KimchiConstraint Fp)) circuit)

compileFB :: (forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r (BoolVar Fp)) -> Effect (Circuit Fp)
compileFB circuit = fromCompiledCircuit =<<
  (compile noAdvice (Proxy @(F Fp)) (Proxy @Boolean) (Proxy @(KimchiConstraint Fp)) circuit)

compileFU :: (forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r Unit) -> Effect (Circuit Fp)
compileFU circuit = fromCompiledCircuit =<<
  (compile noAdvice (Proxy @(F Fp)) (Proxy @Unit) (Proxy @(KimchiConstraint Fp)) circuit)

compileUU :: (forall r. PrimeField Fp => Unit -> Snarky Fp (KimchiConstraint Fp) r Unit) -> Effect (Circuit Fp)
compileUU circuit = fromCompiledCircuit =<<
  (compile noAdvice (Proxy @Unit) (Proxy @Unit) (Proxy @(KimchiConstraint Fp)) circuit)

compileBB :: (forall c r. BasicSystem Fp c => BoolVar Fp -> Snarky Fp c r (BoolVar Fp)) -> Effect (Circuit Fp)
compileBB circuit = fromCompiledCircuit =<<
  (compile noAdvice (Proxy @Boolean) (Proxy @Boolean) (Proxy @(KimchiConstraint Fp)) circuit)

compileBU :: (forall c r. BasicSystem Fp c => BoolVar Fp -> Snarky Fp c r Unit) -> Effect (Circuit Fp)
compileBU circuit = fromCompiledCircuit =<<
  (compile noAdvice (Proxy @Boolean) (Proxy @Unit) (Proxy @(KimchiConstraint Fp)) circuit)

type TwoPoints = Tuple (AffinePoint Fp) (AffinePoint Fp)
type Point = AffinePoint Fp
type PointField = Tuple (AffinePoint Fp) (F Fp)
type V3 = Vector 3 (F Fp)

compilePF
  :: ( forall r
        . PrimeField Fp
       => Tuple (AffinePoint (FVar Fp)) (FVar Fp)
       -> Snarky Fp (KimchiConstraint Fp) r (AffinePoint (FVar Fp))
     )
  -> Effect (Circuit Fp)
compilePF circuit = fromCompiledCircuit =<<
  (compile noAdvice (Proxy @PointField) (Proxy @Point) (Proxy @(KimchiConstraint Fp)) circuit)

--------------------------------------------------------------------------------
-- Field arithmetic circuits

mulCircuit :: forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r (FVar Fp)
mulCircuit x = do
  y <- exists (pure (zero :: F Fp))
  mul_ x y

invCircuit :: forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r (FVar Fp)
invCircuit x = inv_ x

divCircuit :: forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r (FVar Fp)
divCircuit x = do
  -- The divisor's witness must be nonzero for the solver (`inv_` throws
  -- `DivisionByZero`); the constraint system is witness-independent, so the
  -- OCaml byte-comparison is unaffected.
  y <- exists (pure (one :: F Fp))
  div_ x y

ifCircuit :: forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r (FVar Fp)
ifCircuit x = do
  y <- exists (pure (zero :: F Fp))
  b <- exists (pure true)
  if_ b x y

equalsCircuit :: forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r (BoolVar Fp)
equalsCircuit x = do
  y <- exists (pure (zero :: F Fp))
  equals_ x y

pow7Circuit :: forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r (FVar Fp)
pow7Circuit x = pow_ x 7

pow8Circuit :: forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r (FVar Fp)
pow8Circuit x = pow_ x 8

--------------------------------------------------------------------------------
-- Assertion circuits

assertEqualCircuit :: forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r Unit
assertEqualCircuit x = do
  y <- exists (pure (zero :: F Fp))
  assertEqual_ x y

-- | Application body for `dump_two_phase_chain`'s branch 0
-- | (`make_zero`): assert that the public input equals zero. PS
-- | mirror of `app_circuit_two_phase_chain_make_zero` in
-- | `dump_circuit_impl.ml`. Foundational for the multi-branch
-- | trace-diff loop — if PS and OCaml disagree on the gate
-- | sequence for this trivial body, every downstream step_main /
-- | wrap_main / witness comparison is meaningless.
makeZeroAppCircuit :: forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r Unit
makeZeroAppCircuit x = assertEqual_ x (const_ zero)

-- | Application body for `dump_two_phase_chain`'s branch 1
-- | (`increment`): allocate prev as a witness, assert that the
-- | public input equals `prev + 1`. PS mirror of
-- | `app_circuit_two_phase_chain_increment`.
incrementAppCircuit :: forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r Unit
incrementAppCircuit x = do
  prev <- exists (pure (zero :: F Fp))
  assertEqual_ x (CVar.add_ (const_ one) prev)

-- | PS mirror of `app_circuit_chunks2` in `dump_circuit_impl.ml`: fill
-- | 2^16 rows with `Field.mul (fresh_zero) (fresh_zero)` (each R1CS
-- | counts as half a row, so 2^17 + 1 iterations match OCaml's
-- | `for _ = 0 to 1 lsl 17 do`), then a raw 7-wire Generic row with zero
-- | coeffs to bump the 7th permuted column's polynomial degree above
-- | 2^16.
chunks2AppCircuit :: forall r. PrimeField Fp => Unit -> Snarky Fp (KimchiConstraint Fp) r Unit
chunks2AppCircuit _ = do
  let
    freshZero = exists (pure (zero :: F Fp))
    iters = (1 `Bits.shl` 17) + 1
    mulOne = do
      z1 <- freshZero
      z2 <- freshZero
      _ <- mul_ z1 z2
      pure unit
  tailRecM
    ( \i ->
        if i >= iters then pure (Done unit)
        else mulOne *> pure (Loop (i + 1))
    )
    0
  z <- freshZero
  addConstraint $ KimchiPad
    (z :< z :< z :< z :< z :< z :< z :< Vector.nil)

assertSquareCircuit :: forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r Unit
assertSquareCircuit x = do
  y <- exists (pure (zero :: F Fp))
  assertSquare_ x y

assertNonZeroCircuit :: forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r Unit
assertNonZeroCircuit x = assertNonZero_ x

assertNotEqualCircuit :: forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r Unit
assertNotEqualCircuit x = do
  y <- exists (pure (zero :: F Fp))
  assertNotEqual_ x y

unpackCircuit :: forall c r. BasicSystem Fp c => FVar Fp -> Snarky Fp c r Unit
unpackCircuit x = do
  _ <- unpack_ x (Proxy @254)
  pure unit

--------------------------------------------------------------------------------
-- Boolean circuits

boolAndCircuit :: forall c r. BasicSystem Fp c => BoolVar Fp -> Snarky Fp c r (BoolVar Fp)
boolAndCircuit x = do
  y <- exists (pure true)
  and_ x y

boolOrCircuit :: forall c r. BasicSystem Fp c => BoolVar Fp -> Snarky Fp c r (BoolVar Fp)
boolOrCircuit x = do
  y <- exists (pure true)
  or_ x y

boolXorCircuit :: forall c r. BasicSystem Fp c => BoolVar Fp -> Snarky Fp c r (BoolVar Fp)
boolXorCircuit x = do
  y <- exists (pure true)
  xor_ x y

boolAllCircuit :: forall c r. BasicSystem Fp c => BoolVar Fp -> Snarky Fp c r (BoolVar Fp)
boolAllCircuit x = do
  y <- exists (pure true)
  w <- exists (pure true)
  all_ [ x, y, w ]

boolAnyCircuit :: forall c r. BasicSystem Fp c => BoolVar Fp -> Snarky Fp c r (BoolVar Fp)
boolAnyCircuit x = do
  y <- exists (pure true)
  w <- exists (pure true)
  any_ [ x, y, w ]

boolAssertCircuit :: forall c r. BasicSystem Fp c => BoolVar Fp -> Snarky Fp c r Unit
boolAssertCircuit x = assert_ x

--------------------------------------------------------------------------------
-- Kimchi gate circuits

addCompleteCircuit
  :: forall r
   . PrimeField Fp
  => Tuple (AffinePoint (FVar Fp)) (AffinePoint (FVar Fp))
  -> Snarky Fp (KimchiConstraint Fp) r (AffinePoint (FVar Fp))
addCompleteCircuit (Tuple p1 p2) =
  _.p <$> addFast DontCheckFinite p1 p2

endoScalarCircuit
  :: forall r
   . PrimeField Fp
  => FVar Fp
  -> Snarky Fp (KimchiConstraint Fp) r (FVar Fp)
endoScalarCircuit scalar =
  let
    EndoScalar es = endoScalar @Vesta.BaseField @Fp
  in
    toField @8 (unsafeCoerce scalar :: SizedF 128 (FVar Fp)) (const_ es)

varBaseMulCircuit
  :: forall r
   . PrimeField Fp
  => Tuple (AffinePoint (FVar Fp)) (FVar Fp)
  -> Snarky Fp (KimchiConstraint Fp) r (AffinePoint (FVar Fp))
varBaseMulCircuit (Tuple g scalar) =
  scaleFast1 @51 g (Type1 scalar)

endoMulCircuit
  :: forall r
   . PrimeField Fp
  => Tuple (AffinePoint (FVar Fp)) (FVar Fp)
  -> Snarky Fp (KimchiConstraint Fp) r (AffinePoint (FVar Fp))
endoMulCircuit (Tuple g scalar) =
  endo @128 @32 g (unsafeCoerce scalar :: SizedF 128 (FVar Fp))

scaleFast2_128Circuit
  :: forall r
   . PrimeField Fp
  => Tuple (AffinePoint (FVar Fp)) (FVar Fp)
  -> Snarky Fp (KimchiConstraint Fp) r (AffinePoint (FVar Fp))
scaleFast2_128Circuit (Tuple g scalar) =
  scaleFast2' @26 @127 g scalar

poseidonCircuit
  :: forall r
   . PrimeField Fp
  => Vector 3 (FVar Fp)
  -> Snarky Fp (KimchiConstraint Fp) r (Vector 3 (FVar Fp))
poseidonCircuit = poseidon

--------------------------------------------------------------------------------
-- Test infrastructure

loadOcamlCircuit :: forall f. Ord f => SerdeHex f => PrimeField f => String -> Effect (Circuit f)
loadOcamlCircuit name = do
  circuit <- readFixture (fixtureDir <> name <> ".json")
  cachedConstants <- readFixture (fixtureDir <> name <> "_cached_constants.json")
  gateLabels <- readFixture (fixtureDir <> name <> "_gate_labels.jsonl")
  case parseOcamlFixtures { circuit, cachedConstants, gateLabels } of
    Right c -> pure c
    Left e -> throw $ "Failed to parse OCaml fixtures: " <> show e

-- | Strip metadata fields for equality comparison (context and variables are not part of
-- | the constraint system)
stripMetadata :: ComparableCircuit -> ComparableCircuit
stripMetadata c = c
  { gates = map (_ { context = [], variables = Nothing }) c.gates
  , cachedConstants = Array.sort $ map (\cc -> cc { variable = 0 }) c.cachedConstants
  }

exactMatch :: forall f. Ord f => SerdeHex f => PrimeField f => String -> Circuit f -> SpecT Aff Unit Aff Unit
exactMatch name ps = exactMatchEff name (pure ps)

-- | Variant for circuits whose construction is `Effect`-bound (e.g. the
-- | `compileStepMain*` helpers that thread `CircuitBuilderT` state through
-- | a real `Effect` context). Equivalent to `exactMatch` after running the
-- | producing action — provided so call sites don't need an
-- | `unsafePerformEffect` shim at the boundary.
exactMatchEff
  :: forall f
   . Ord f
  => SerdeHex f
  => PrimeField f
  => String
  -> Effect (Circuit f)
  -> SpecT Aff Unit Aff Unit
exactMatchEff name effPs = exactMatchWith name (effPs <#> \circuit -> { circuit, constants: Nothing })

-- | The general form: the produced circuit and the constants it was compiled with, which the
-- | comparison JSON written to `circuits/results/` carries.
exactMatchWith
  :: forall f
   . Ord f
  => SerdeHex f
  => PrimeField f
  => String
  -> Effect (Compared f)
  -> SpecT Aff Unit Aff Unit
exactMatchWith name effPs =
  it (name <> " matches OCaml") do
    { circuit: ps, constants } <- liftEffect effPs
    ocaml <- liftEffect $ (loadOcamlCircuit name :: Effect (Circuit f))
    let psCircuit = comparable ps
    let ocamlCircuit = comparable ocaml
    let psNoCtx = stripMetadata psCircuit
    let ocamlNoCtx = stripMetadata ocamlCircuit
    let status = if psNoCtx == ocamlNoCtx then "match" else "mismatch"
    let comparison = { name, status, purescript: psCircuit, ocaml: ocamlCircuit, constants }
    liftEffect do
      writeComparison (resultsDir <> name <> ".json") comparison
      appendManifest name status
    unless (status == "match") $
      psNoCtx `shouldEqual` ocamlNoCtx

-- | Compile a circuit over its input and output types and compare it.
exactMatchCompiled
  :: forall @a @b avar bvar
   . CircuitType Fp a avar
  => CircuitType Fp b bvar
  => CheckedType Fp (KimchiConstraint Fp) avar
  => String
  -> (forall r. avar -> Snarky Fp (KimchiConstraint Fp) r bvar)
  -> SpecT Aff Unit Aff Unit
exactMatchCompiled name circuit =
  exactMatchEff name $ fromCompiledCircuit
    =<< compile @Fp noAdvice (Proxy @a) (Proxy @b) (Proxy @(KimchiConstraint Fp)) circuit

--------------------------------------------------------------------------------
-- Test spec

-- | The three distinct SRSes the circuit-diff fixtures read constants off
-- | (Lagrange commitments + blinding generators), built directly and threaded
-- | into `spec`. The kimchi URS is a cheap, deterministic hash-to-curve string;
-- | the per-domain bases each read triggers are computed lazily by kimchi.
type SrsBundle =
  { vestaCrs16 :: CRS VestaG
  , pallasCrs16 :: CRS PallasG
  , pallasCrs15 :: CRS PallasG
  }

main :: Effect Unit
main = do
  let
    bundle =
      { vestaCrs16: vestaCrsCreate (1 `Bits.shl` 16)
      , pallasCrs16: pallasCrsCreate (1 `Bits.shl` 16)
      , pallasCrs15: pallasCrsCreate (1 `Bits.shl` 15)
      }
  runSpecAndExitProcess' { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }
    [ consoleReporter ]
    (spec bundle)

spec :: SrsBundle -> SpecT Aff Unit Aff Unit
spec bundle =
  beforeAll_ (liftEffect resetOutputDirs) $
    describe "Circuit comparison" do
      describe "Field arithmetic" do
        exactMatchCompiled @(F Fp) @(F Fp) "mul_step_circuit" mulCircuit
        exactMatchCompiled @(F Fp) @(F Fp) "inv_step_circuit" invCircuit
        exactMatchCompiled @(F Fp) @(F Fp) "div_step_circuit" divCircuit
        exactMatchCompiled @(F Fp) @(F Fp) "if_step_circuit" ifCircuit
        exactMatchCompiled @(F Fp) @Boolean "equals_step_circuit" equalsCircuit
        exactMatchCompiled @(F Fp) @(F Fp) "pow7_step_circuit" pow7Circuit
        exactMatchCompiled @(F Fp) @(F Fp) "pow8_step_circuit" pow8Circuit
      describe "Assertions" do
        exactMatchCompiled @(F Fp) @Unit "assert_equal_step_circuit" assertEqualCircuit
        exactMatchCompiled @(F Fp) @Unit "assert_non_zero_step_circuit" assertNonZeroCircuit
        exactMatchCompiled @(F Fp) @Unit "assert_not_equal_step_circuit" assertNotEqualCircuit
        exactMatchCompiled @(F Fp) @Unit "assert_square_step_circuit" assertSquareCircuit
        exactMatchCompiled @(F Fp) @Unit "unpack_step_circuit" unpackCircuit
      describe "Boolean" do
        exactMatchCompiled @Boolean @Boolean "bool_and_step_circuit" boolAndCircuit
        exactMatchCompiled @Boolean @Boolean "bool_or_step_circuit" boolOrCircuit
        exactMatchCompiled @Boolean @Boolean "bool_xor_step_circuit" boolXorCircuit
        exactMatchCompiled @Boolean @Boolean "bool_all_step_circuit" boolAllCircuit
        exactMatchCompiled @Boolean @Boolean "bool_any_step_circuit" boolAnyCircuit
        exactMatchCompiled @Boolean @Unit "bool_assert_step_circuit" boolAssertCircuit
      describe "Two-phase chain application circuits" do
        -- App-level rule bodies for `dump_two_phase_chain` (the
        -- minimal multi-branch fixture). We byte-compare ONLY the
        -- application bodies — without step_main scaffolding —
        -- because rule-body parity is the foundation: if the user-
        -- written assertions don't compile to the same gates in PS
        -- and OCaml, every downstream comparison (witness, oracles,
        -- deferred values, wrap_main) is rooted in noise. The full
        -- multi-branch step_main diff comes later, once PS supports
        -- multi-branch compile.
        exactMatchCompiled @(F Fp) @Unit "app_circuit_two_phase_chain_make_zero"
          makeZeroAppCircuit
        exactMatchCompiled @(F Fp) @Unit "app_circuit_two_phase_chain_increment"
          incrementAppCircuit
        exactMatchEff "app_circuit_chunks2" (compileUU chunks2AppCircuit)
      describe "Schnorr signature" do
        -- Iteration 1 fixture: zero-seed sponge (matches PS
        -- `Snarky.Circuit.RandomOracle.Sponge` initial state). 5 public
        -- inputs (pk_x, pk_y, r, s, message[0]) + 1 boolean output.
        -- OCaml source: `schnorr_verify_circuit` in
        -- `mina/src/lib/crypto/pickles/dump_circuit_impl.ml`.
        exactMatchEff "schnorr_verify_step_circuit" (fromCompiledCircuit =<< compileSchnorrVerify)
      describe "Kimchi gates" do
        exactMatchCompiled @TwoPoints @Point "add_complete_step_circuit" addCompleteCircuit
        exactMatchCompiled @(F Fp) @(F Fp) "endo_scalar_step_circuit" endoScalarCircuit
        exactMatchCompiled @PointField @Point "var_base_mul_step_circuit" varBaseMulCircuit
        exactMatchCompiled @PointField @Point "endo_mul_step_circuit" endoMulCircuit
        exactMatchEff "scale_fast2_128_step_circuit" (compilePF scaleFast2_128Circuit)
        exactMatchCompiled @V3 @V3 "poseidon_step_circuit" poseidonCircuit
      describe "Pickles Step sub-circuits" do
        exactMatchEff "pow2_pow_step_circuit" (fromCompiledCircuit =<< compilePow2Pow)
        exactMatchEff "b_correct_step_circuit" (fromCompiledCircuit =<< compileBCorrect)
        exactMatchEff "b_correct_wrap_circuit" (fromCompiledCircuit =<< compileBCorrectWrap)
        exactMatchEff "plonk_checks_passed_step_circuit" (fromCompiledCircuit =<< compilePlonkChecksPassedStep)
        exactMatchEff "plonk_checks_passed_wrap_circuit" (fromCompiledCircuit =<< compilePlonkChecksPassedWrap)
        exactMatchEff "expand_plonk_step_circuit" (fromCompiledCircuit =<< compileExpandPlonkStep)
        exactMatchEff "expand_plonk_wrap_circuit" (fromCompiledCircuit =<< compileExpandPlonkWrap)
        exactMatchEff "challenge_digest_step_circuit" (fromCompiledCircuit =<< compileChallengeDigestStep)
        exactMatchEff "challenge_digest_wrap_circuit" (fromCompiledCircuit =<< compileChallengeDigestWrap)
        exactMatchEff "sponge_and_challenges_step_circuit" (fromCompiledCircuit =<< compileSpongeAndChallengesStep)
        exactMatchEff "fq_sponge_transcript_step_circuit" (fromCompiledCircuit =<< compileFqSpongeTranscriptStep)
        exactMatchEff "sponge_and_challenges_wrap_circuit" (fromCompiledCircuit =<< compileSpongeAndChallengesWrap)
        exactMatchEff "fq_sponge_transcript_wrap_circuit" (fromCompiledCircuit =<< compileFqSpongeTranscriptWrap)
        exactMatchEff "hash_messages_for_next_step_proof_circuit" (fromCompiledCircuit =<< compileHashMessagesStep)
        exactMatchEff "finalize_other_proof_step_circuit" (fromCompiledCircuit =<< compileFopStep)
        exactMatchEff "finalize_other_proof_chunks2_step_circuit" (fromCompiledCircuit =<< compileFopStepChunks2)
        exactMatchEff "group_map_step_circuit" (fromCompiledCircuit =<< compileGroupMapStep)
        exactMatchEff "bullet_reduce_one_step_circuit" (fromCompiledCircuit =<< compileBulletReduceOneStep)
        exactMatchEff "bullet_reduce_step_circuit" (fromCompiledCircuit =<< compileBulletReduceStep)
        exactMatchEff "ftcomm_step_circuit" (fromCompiledCircuit =<< compileFtcommStep)
        let
          stepSrs = bundle.pallasCrs16
          stepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt stepSrs 16 i)) :: AffinePoint (F Fp))
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepSrs) :: AffinePoint (F Fp)
            }
        exactMatchWith "xhat_step_circuit" (withXhat 30 stepSrsData <$> (fromCompiledCircuit =<< compileXhatStep stepSrsData))
        exactMatchEff "check_bulletproof_step_circuit" (fromCompiledCircuit =<< compileCheckBulletproofStep stepSrsData.blindingH)
      describe "Pickles Wrap sub-circuits" do
        exactMatchEff "hash_messages_for_next_wrap_proof_circuit" (fromCompiledCircuit =<< compileHashMessagesWrap)
        exactMatchEff "finalize_other_proof_wrap_circuit" (fromCompiledCircuit =<< compileFopWrap)
        exactMatchEff "wrap_finalize_n2_circuit" (fromCompiledCircuit =<< compileWrapFinalizeN2)
        exactMatchEff "group_map_wrap_circuit" (fromCompiledCircuit =<< compileGroupMap)
        exactMatchEff "bullet_reduce_one_wrap_circuit" (fromCompiledCircuit =<< compileBulletReduceOne)
        exactMatchEff "bullet_reduce_wrap_circuit" (fromCompiledCircuit =<< compileBulletReduce)
        exactMatchEff "ftcomm_wrap_circuit" (fromCompiledCircuit =<< compileFtcomm)
        exactMatchEff "combine_poly_wrap_circuit" (fromCompiledCircuit =<< compileCombinePoly)
        let
          srs = bundle.vestaCrs16
          wrapSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton (coerce (pallasSrsLagrangeCommitmentAt srs 16 i))
            , blindingH: coerce $ pallasSrsBlindingGenerator srs
            }
        exactMatchWith "xhat_wrap_circuit" (withXhat 34 wrapSrsData <$> (fromCompiledCircuit =<< compileXhat @1 wrapSrsData))
        -- `x_hat` at two branches, through the wrap circuit's `maskedLagrangeAt`: step
        -- domains `2^16, 2^16` (one shared table) and `2^15, 2^16` (per-branch tables).
        let
          lagrangeOne :: Int -> Int -> Vector 1 (AffinePoint (F Fq))
          lagrangeOne log2 i = Vector.singleton (coerce (pallasSrsLagrangeCommitmentAt srs log2 i))
          sameConfig =
            { domainLog2s: 16 :< 16 :< Vector.nil
            , lagrangeTable: \i -> lagrangeOne 16 i :< lagrangeOne 16 i :< Vector.nil
            , blindingH: wrapSrsData.blindingH
            }
          diffConfig =
            { domainLog2s: 15 :< 16 :< Vector.nil
            , lagrangeTable: \i -> lagrangeOne 15 i :< lagrangeOne 16 i :< Vector.nil
            , blindingH: wrapSrsData.blindingH
            }
        exactMatchWith "xhat_wrap_branches_same_circuit"
          (withXhatBranches sameConfig 34 <$> (fromCompiledCircuit =<< compileXhatBranches sameConfig))
        exactMatchWith "xhat_wrap_branches_diff_circuit"
          (withXhatBranches diffConfig 34 <$> (fromCompiledCircuit =<< compileXhatBranches diffConfig))
        -- `xhat_wrap_circuit` at a 2^17 domain over the same 2^16 SRS: every Lagrange base
        -- is two chunks, and the gadget folds one accumulator per chunk.
        let
          chunks2At :: Int -> Vector 2 (AffinePoint Fq)
          chunks2At i = case Vector.toVector @2 (pallasSrsLagrangeCommitmentChunksAt srs 17 i) of
            Just v -> v
            Nothing -> unsafeCrashWith ("xhat_wrap_chunks2: Lagrange base " <> show i <> " is not two chunks")
          wrapSrsDataChunks2 =
            { lagrangeAt: mkConstLagrangeBaseLookup \i -> (coerce (chunks2At i) :: Vector 2 (AffinePoint (F Fq)))
            , blindingH: wrapSrsData.blindingH
            }
        exactMatchWith "xhat_wrap_chunks2_circuit"
          (withXhat 34 wrapSrsDataChunks2 <$> (fromCompiledCircuit =<< compileXhat @2 wrapSrsDataChunks2))
        exactMatchEff "check_bulletproof_wrap_circuit" (fromCompiledCircuit =<< compileCheckBulletproofWrap wrapSrsData.blindingH)
      describe "IVP" do
        let
          wrapSrs = bundle.vestaCrs16
          wrapSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton (coerce (pallasSrsLagrangeCommitmentAt wrapSrs 16 i))
            , blindingH: coerce $ pallasSrsBlindingGenerator wrapSrs
            }
        exactMatchWith "ivp_wrap_circuit" (withXhat 34 wrapSrsData <$> (fromCompiledCircuit =<< compileIvpWrap wrapSrsData))
        exactMatchWith "wrap_verify_circuit" (withXhat 34 wrapSrsData <$> (fromCompiledCircuit =<< compileWrapVerify wrapSrsData))
        exactMatchEff "wrap_verify_n2_circuit" (fromCompiledCircuit =<< compileWrapVerifyN2 wrapSrsData)
        let
          -- wrap_main_circuit fixture uses domainLog2 = 14 to match the
          -- production Simple_chain N1 wrap compile (verified via OCaml
          -- `compile.wrap_domains.h.log2` trace). The matching change in
          -- dump_circuit_impl.ml passes ~domain_log2:14 to
          -- Wrap_main_for_dump.build, and the PS WrapMain.purs config
          -- pins domainLog2s = 14. The lagrange closure here has to
          -- return commitments at domain size 2^14 to match.
          wrapMainSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton (coerce (pallasSrsLagrangeCommitmentAt wrapSrs 14 i))
            , blindingH: coerce $ pallasSrsBlindingGenerator wrapSrs
            }
          -- N=1 step CS commits over the Vesta SRS at log2=14. The
          -- step shape is the same one `step_main_simple_chain_circuit`
          -- already byte-matches.
          wrapMainN1StepSrs = bundle.pallasCrs15
          wrapMainN1StepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt wrapMainN1StepSrs 14 i)) :: AffinePoint (F Fp))
            , blindingH: (coerce $ vestaSrsBlindingGenerator wrapMainN1StepSrs) :: AffinePoint (F Fp)
            }
        -- N=1 Input mode (Simple_chain). step_widths=[1], padded=[[0];[1]].
        -- `compileWrapMainN1` deterministically computes the step VK by
        -- recompiling the matching step CS and running the kimchi
        -- commitment pipeline (mirrors the wrap_main_n2_circuit fix at
        -- commit `cf352650`).
        exactMatchWith "wrap_main_circuit"
          (withWrapConstants =<< compileWrapMainN1 wrapMainSrsData wrapMainN1StepSrsData)
        -- N=1 side-loaded parent (`Simple_chain` from `dump_side_loaded_main`).
        -- Same shape as `wrap_main_circuit` but the prev slot's bound is
        -- N2 instead of N1: step_widths=[1], padded=[[0];[2]],
        -- domain_log2=14. `compileWrapMainSideLoadedMain` deterministically
        -- computes the step VK by recompiling the matching step CS
        -- (mirrors the wrap_main_n2_circuit fix in commit `cf352650`).
        let
          -- Step SRS data for SideLoadedMain: same shape as
          -- `wrapMainN1StepSrsData` but with the side-loaded
          -- per-domain lagrange tables at log2 ∈ {13, 14, 15}.
          wrapMainSlmStepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt wrapMainN1StepSrs 14 i)) :: AffinePoint (F Fp))
            , sideloadedPerDomainLagrangeAt:
                (\i -> Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt wrapMainN1StepSrs 13 i)) :: AffinePoint (F Fp)))
                  :< (\i -> Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt wrapMainN1StepSrs 14 i)) :: AffinePoint (F Fp)))
                  :< (\i -> Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt wrapMainN1StepSrs 15 i)) :: AffinePoint (F Fp)))
                  :< Vector.nil
            , blindingH: (coerce $ vestaSrsBlindingGenerator wrapMainN1StepSrs) :: AffinePoint (F Fp)
            }
        exactMatchWith "wrap_main_side_loaded_main_circuit"
          (withWrapConstants =<< compileWrapMainSideLoadedMain wrapMainSrsData wrapMainSlmStepSrsData)
        -- N=2 Input mode (Simple_chain_n2). step_widths=[2], padded=[[0;2];[0;2]].
        -- `compileWrapMainN2` deterministically computes the step VK by
        -- recompiling the matching step CS and running the kimchi
        -- commitment pipeline. Needs `stepMainN2StepSrsData` (the same
        -- data used by `step_main_simple_chain_n2_circuit` below).
        --
        -- The wrap-side lagrange basis is at log2=14 (same as
        -- `wrap_main_circuit`): `dump_simple_chain_n2.ml` passes
        -- `~override_wrap_domain:Proofs_verified.N1`, so the wrap
        -- domain is N1 = Pow_2_roots_of_unity 14.
        exactMatchWith "wrap_main_n2_circuit"
          (withWrapConstants =<< simpleChainN2Wrap bundle)
        -- N=0 Input_and_output mode (Add_one_return). step_widths=[0],
        -- padded=[[0];[0]]. First (and only) N=0 wrap fixture — exercises
        -- the wrap verify-one-of-step path with a step proof whose own
        -- public input is just the msgForNextStep digest (no unfinalized
        -- proofs, no msg_wrap entries). Uses domain_log2=13 (step domain
        -- for the N=0 step circuit is 2^9, wrap domain is 2^13 per OCaml
        -- dump_add_one_return's `compile.wrap_domains.h.log2` trace).
        let
          -- Lagrange lookup is for the STEP proof's evaluation domain
          -- (= step circuit's domain log2 = 9 for AOR), NOT the wrap
          -- circuit's domain log2 = 13. Mirrors `wrap_main_circuit`
          -- and `wrap_main_n2_circuit` test setups where the lagrange
          -- log2 matches `domainLog2s` (the step proof's domain).
          wrapMainAddOneReturnSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton (coerce (pallasSrsLagrangeCommitmentAt wrapSrs 9 i))
            , blindingH: coerce $ pallasSrsBlindingGenerator wrapSrs
            }
          -- Step CS params for Add_one_return (mpv=0, no prev proofs).
          -- Lagrange lookup is unused at mpv=0 (perSlotLagrangeAt is
          -- Vector.nil). blindingH and SRS size match the Vesta CRS
          -- the step VK is derived over (deriveStepKey).
          aorStepSrs = bundle.pallasCrs15
          aorStepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt aorStepSrs 14 i)) :: AffinePoint (F Fp))
            , blindingH: (coerce $ vestaSrsBlindingGenerator aorStepSrs) :: AffinePoint (F Fp)
            }
        exactMatchWith "wrap_main_add_one_return_circuit"
          (withWrapConstants =<< compileWrapMainAddOneReturn wrapMainAddOneReturnSrsData aorStepSrsData)
        -- N=0, num_chunks=2 wrap. Same branch/widths/Max_widths layout
        -- as `wrap_main_add_one_return_circuit` but with `stepChunks=2`
        -- at `wrapMainForPrevs`, so the IVP MSM walks 2 chunks per
        -- w/z/t_comm. Step domain log2 = 17 (driven by the chunks2 step
        -- body's 2^17 mul fillers); wrap domain log2 = 14 (= N1
        -- override). Step SRS, lagrange, blindingH match the chunks2
        -- step-only fixture above. Mirrors `dump_chunks2.ml` wrap-side.
        let
          chunks2WrapSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton (coerce (pallasSrsLagrangeCommitmentAt wrapSrs 17 i))
            , blindingH: coerce $ pallasSrsBlindingGenerator wrapSrs
            }
        exactMatchWith "chunks2_wrap_main_circuit"
          (withWrapConstants =<< compileWrapMainChunks2 chunks2WrapSrsData aorStepSrsData)
        -- N=2 Output mode (Tree_proof_return). Single branch with
        -- heterogeneous prev slots [0; 2] (No_recursion_return at
        -- slot 0, self at slot 1). step_widths=[2], padded=[[0];[2]].
        -- TPR step CS has step_domain log2 = 15 (empirically verified
        -- via OC's `branch_data` row 81 R coeff = 4*15 = 60); wrap
        -- circuit uses override_wrap_domain:N1 → wrap domain log2 = 14.
        -- The IVP MSM lagrange lookup is at the STEP domain log2 (15),
        -- matching `domainLog2s` in the WrapMainConfig.
        exactMatchWith "wrap_main_tree_proof_return_circuit"
          (withWrapConstants =<< treeProofReturnWrap bundle)
        -- Multi-branch (2 branches: make_zero + increment) sharing ONE wrap
        -- key. step_widths=[0;1], padded=[[0;0];[0;1]]; per-branch step
        -- domains [9; 14] differ (make_zero is tiny, increment full),
        -- so wrap_main goes through the per-branch dispatch path.
        -- Lagrange lookup is per-branch — needs the wrap SRS directly.
        -- Step VKs are derived per-branch (mirrors the deterministic
        -- VK fix family — wrap_main_circuit, wrap_main_tree_proof_return).
        exactMatchWith "wrap_main_two_phase_chain_circuit"
          (withWrapConstants =<< twoPhaseChainWrap bundle)
        let
          -- OCaml uses SRS.Fq.create (1 lsl 15) and domain Pow_2_roots_of_unity 15
          stepSrs = bundle.pallasCrs15
          stepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt stepSrs 15 i)) :: AffinePoint (F Fp))
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepSrs) :: AffinePoint (F Fp)
            }
        exactMatchWith "ivp_step_circuit" (withXhat 30 stepSrsData <$> (fromCompiledCircuit =<< compileIvpStep stepSrsData))
      describe "Step verify" do
        let
          -- Same SRS as IVP step: OCaml uses SRS.Fq.create (1 lsl 15) and domain 15
          stepVerifySrs = bundle.pallasCrs15
          stepVerifySrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt stepVerifySrs 15 i)) :: AffinePoint (F Fp))
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepVerifySrs) :: AffinePoint (F Fp)
            }
        exactMatchWith "step_verify_circuit"
          (withXhat 30 stepVerifySrsData <$> (fromCompiledCircuit =<< compileStepVerify stepVerifySrsData))
        let
          stepVerifyN2SrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt stepVerifySrs 15 i)) :: AffinePoint (F Fp))
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepVerifySrs) :: AffinePoint (F Fp)
            }
        exactMatchEff "step_verify_n2_circuit" (fromCompiledCircuit =<< compileStepVerifyN2 stepVerifyN2SrsData)
      describe "Full step verify_one" do
        let
          fullStepSrs = bundle.pallasCrs15
          fullStepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt fullStepSrs 14 i)) :: AffinePoint (F Fp))
            , blindingH: (coerce $ vestaSrsBlindingGenerator fullStepSrs) :: AffinePoint (F Fp)
            }
        exactMatchWith "full_step_verify_one_circuit"
          (withXhat 30 fullStepSrsData <$> (fromCompiledCircuit =<< compileFullStepVerifyOne fullStepSrsData))
        let
          fullStepN2SrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt fullStepSrs 14 i)) :: AffinePoint (F Fp))
            , blindingH: (coerce $ vestaSrsBlindingGenerator fullStepSrs) :: AffinePoint (F Fp)
            }
        exactMatchEff "full_step_verify_one_n2_circuit" (fromCompiledCircuit =<< compileFullStepVerifyOneN2 fullStepN2SrsData)
      describe "Typ checks" do
        exactMatchEff "other_field_check_step_circuit" (fromCompiledCircuit =<< compileOtherFieldCheck)
      describe "Step main" do
        let
          -- OCaml uses SRS.Fq.create (1 lsl 15), wrap domain Pow_2_roots_of_unity 14
          stepMainSrs = bundle.pallasCrs15
          stepMainSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 14 i)) :: AffinePoint (F Fp))
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            }
        -- N=1, Input mode. Public input layout is input field only.
        exactMatchEff "step_main_simple_chain_circuit" (fromCompiledCircuit <<< _.stepCs =<< compileStepMainSimpleChain stepMainSrsData)
        let
          stepMainN2SrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 14 i)) :: AffinePoint (F Fp))
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            }
        -- N=2, Input mode. Two prev proofs verified by verify_one.
        exactMatchWith "step_main_simple_chain_n2_circuit" do
          wrapArt <- simpleChainN2Wrap bundle
          withSelfKey wrapArt
            =<< compileStepMainSimpleChainN2WithConstants stepMainN2SrsData
        -- N=0, Input_and_output mode — Add_one_return. No recursion,
        -- no verify_one; the hash_messages_for_next_step_proof absorbs
        -- BOTH input and output fields (OCaml step_main.ml:566-573
        -- Input_and_output branch → `to_field_elements (app_state, ret_var)`).
        exactMatchEff "step_main_add_one_return_circuit" (fromCompiledCircuit <<< _.stepCs =<< compileStepMainAddOneReturn stepMainSrsData)
        -- N=0, Output mode — No_recursion_return. Rule returns
        -- `output = 0` with no input. Exercises the Output-mode branch
        -- of step_main.ml:566-573 (`Output _ -> ret_var`) at N=0: the
        -- hash_messages_for_next_step_proof absorbs ONLY the output
        -- field (no input contribution). Precursor to Tree_proof_return's
        -- proof-level byte-for-byte test, which consumes a real
        -- No_recursion_return proof in slot 0.
        exactMatchEff "step_main_no_recursion_return_circuit" (fromCompiledCircuit <<< _.stepCs =<< compileStepMainNoRecursionReturn stepMainSrsData)
        -- N=0, num_chunks=2, override_wrap_domain=N1 (= log2 14).
        -- Same shape as NRR but with 2^17+1 mul fillers + a 7-wire Raw
        -- Generic gate so the step domain rounds to 2^17 and kimchi's
        -- PCS commits at num_chunks=2. Mirrors `dump_chunks2.exe`.
        -- See `mina/.../dump_chunks2/dump_chunks2.ml`. The CS itself is
        -- not affected by `num_chunks` directly — it's purely a function
        -- of the rule body's gate count — but this fixture is the
        -- byte-equality gate for the chunks2 witness diff loop.
        exactMatchEff "chunks2_step_main_circuit" (fromCompiledCircuit <<< _.stepCs =<< compileStepMainChunks2 stepMainSrsData)
        -- N=2, Output mode, HETEROGENEOUS prevs (No_recursion_return @ N0,
        -- self @ N2). All four layers of heterogeneity wired up:
        -- * per-slot SPPW sizing  (`Slot 0 … /\ Slot 2 … /\ Unit`)
        -- * per-slot FOP domain   (`[13, 14]`)
        -- * per-slot wrap VK      (`[Just no_rec_vk, Nothing]`)
        -- * per-slot lagrange     (`[domain 13 lookup, domain 14 lookup]`).
        let
          lagrangeAtD13 =
            mkConstLagrangeBaseLookup \i ->
              Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 13 i)) :: AffinePoint (F Fp))
          lagrangeAtD14 =
            mkConstLagrangeBaseLookup \i ->
              Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 14 i)) :: AffinePoint (F Fp))
          -- SRS data for compiling NRR's wrap CS up-front, used to
          -- derive slot 0's known wrap key (replacing the prior
          -- 28-copies-of-Pallas-generator placeholder). Mirrors
          -- `wrapMainAddOneReturnSrsData` (NRR is N=0 leaf rule, same
          -- wrap config as AOR — IVP MSM lookup at step domain log2 9).
          tprNrrWrapSrs = bundle.vestaCrs16

          tprNrrWrapSrsData :: IvpWrapParams
          tprNrrWrapSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton (coerce (pallasSrsLagrangeCommitmentAt tprNrrWrapSrs 9 i))
            , blindingH: coerce $ pallasSrsBlindingGenerator tprNrrWrapSrs
            }

          -- NRR step CS SRS data. lagrangeAt is unused at mpv=0
          -- (`compileStepMainNoRecursionReturn` passes Vector.nil for
          -- perSlotLagrangeAt) but still required by the params type.
          -- Same shape as `aorStepSrsData`.
          tprNrrStepSrsData :: StepMainNoRecursionReturnParams
          tprNrrStepSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 14 i)) :: AffinePoint (F Fp))
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            }
          treeProofReturnSrsData =
            { slot0LagrangeAt: lagrangeAtD13
            , slot1LagrangeAt: lagrangeAtD14
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            , nrrWrapSrsData: tprNrrWrapSrsData
            , nrrStepSrsData: tprNrrStepSrsData
            }
        exactMatchWith "step_main_tree_proof_return_circuit" do
          wrapArt <- treeProofReturnWrap bundle
          withSelfKey wrapArt
            =<< compileStepMainTreeProofReturnWithConstants treeProofReturnSrsData
        -- N=2: an External slot over `two_phase_chain` (step domains 9 and
        -- 14) beside a Self slot; both slots read the 2^14 Lagrange basis.
        exactMatchWith "step_main_import_two_phase_chain_circuit" do
          wrapArt <- importTwoPhaseChainWrap bundle
          withSelfKey wrapArt
            =<< compileStepMainImportTwoPhaseChainWithConstants (importTwoPhaseChainParams bundle)
        -- N=1 parent + single side-loaded prev (mpv=N2 upper bound).
        -- The three per-domain lagrange tables sit at log2 ∈ {13, 14,
        -- 15} (= the wrap-domain log2s for `actualWrapDomainSize ∈
        -- {N0, N1, N2}`); the in-circuit dispatch one-hot-muxes among
        -- them. Reference: OCaml `dump_side_loaded_main.ml`.
        let
          lagrangeAtD15 =
            mkConstLagrangeBaseLookup \i ->
              Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 15 i)) :: AffinePoint (F Fp))
          sideLoadedMainSrsData =
            { lagrangeAt: lagrangeAtD14
            , sideloadedPerDomainLagrangeAt:
                ( \i ->
                    Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 13 i)) :: AffinePoint (F Fp))
                )
                  :<
                    ( \i ->
                        Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 14 i)) :: AffinePoint (F Fp))
                    )
                  :<
                    ( \i ->
                        Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 15 i)) :: AffinePoint (F Fp))
                    )
                  :< Vector.nil
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            }
          _ = lagrangeAtD15 -- keep available in case the diff loop wants the LBL form
        -- N=1 parent + side-loaded prev. Current state: −63 Generic.
        -- PS labels in fixture output (`context` field) localize the
        -- deficit to `step6_ivp / ivp_xhat / public-input-commit`
        -- (rows 3993-4085) — PS `InCircuitCorrections` mode vs OCaml
        -- `public_input_commitment_dynamic` (step_verifier.ml:457-512)
        -- emit different specific R1CS Generic counts despite
        -- structurally equivalent math. CompleteAdd, VarBaseMul,
        -- EndoMul, Poseidon counts all match exactly. Sub-targets:
        -- step2_fop −64, step6_ivp −22, +23 PS-extra in misc labels
        -- (sponge_after_index, step8_assert_bp).
        --
        -- Pending until residual is closed.
        --
        -- To run the diff manually:
        --   `npx spago test -p pickles-circuit-diffs -- --example "side_loaded_main"`
        -- after switching `pending'` below back to `exactMatchEff`.
        exactMatchEff "step_main_side_loaded_main_circuit" (fromCompiledCircuit <<< _.stepCs =<< compileStepMainSideLoadedMain sideLoadedMainSrsData)
        -- N=0, Input mode — side-loaded CHILD (No_recursion + dummy_constraints).
        -- The inner rule whose proof gets verified by the side-loaded
        -- parent in `dump_side_loaded_main.ml`. Full body translated:
        -- on-curve `g`, `toFieldChecked' @1`, `scaleFast1 @1 @5` ×2,
        -- `endo @4 @1`, then `Field.Assert.equal self Field.zero`.
        let
          sideLoadedChildSrsData =
            { blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            }
        exactMatchEff "step_main_side_loaded_child_circuit" (fromCompiledCircuit <<< _.stepCs =<< compileStepMainSideLoadedChild sideLoadedChildSrsData)
        -- N=1 Input mode (`increment` branch of two_phase_chain).
        -- Step domain log2 = 14. Body asserts `self_v = prev + 1` (single
        -- R1CS) with `proofMustVerify = true_`. mpvMax=1, mpvPad=0.
        -- The OCaml fixture is one of TWO step CSes the
        -- `dump_two_phase_chain.exe` driver emits (step_0=make_zero,
        -- step_1=increment); both feed into the shared wrap CS via
        -- `choose_key`-style step VK dispatch.
        let
          twoPhaseChainMakeZeroSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 14 i)) :: AffinePoint (F Fp))
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            }
          twoPhaseChainIncrementSrsData =
            { lagrangeAt: mkConstLagrangeBaseLookup \i ->
                Vector.singleton ((coerce (vestaSrsLagrangeCommitmentAt stepMainSrs 14 i)) :: AffinePoint (F Fp))
            , blindingH: (coerce $ vestaSrsBlindingGenerator stepMainSrs) :: AffinePoint (F Fp)
            }
        -- Increment standalone test compiles BOTH branches: make_zero
        -- first to obtain its artifact, then increment with that
        -- artifact (passed as a separate arg, supplying the multi-branch
        -- FOP domain dispatch list's `[makeZero, increment]` head).
        exactMatchWith "step_main_two_phase_chain_increment_circuit" $ do
          makeZeroArt <- compileStepMainTwoPhaseChainMakeZero twoPhaseChainMakeZeroSrsData
          wrapArt <- twoPhaseChainWrap bundle
          withSelfKey wrapArt
            =<< compileStepMainTwoPhaseChainIncrementWithConstants makeZeroArt
              twoPhaseChainIncrementSrsData
        -- N=0 Input mode (`make_zero` branch of two_phase_chain). Rule
        -- has no prevs but the multi-branch wrap is mpv=N1, so the
        -- step PI is 34 entries (mpvPad=1 → 1 front-padded dummy slot).
        -- Step domain log2 = 9. Body asserts `self_v = 0` (single R1CS).
        exactMatchWith "step_main_two_phase_chain_make_zero_circuit"
          ( withStepConstants
              =<< compileStepMainTwoPhaseChainMakeZeroWithConstants twoPhaseChainMakeZeroSrsData
          )
      describe "Linearization" do
        exactMatchEff "linearization_step_circuit" (fromCompiledCircuit =<< compileLinearizationStep)
        exactMatchEff "linearization_wrap_circuit" (fromCompiledCircuit =<< compileLinearizationWrap)
        exactMatchEff "ft_eval0_step_circuit" (fromCompiledCircuit =<< compileFtEval0Step)
      describe "Combined inner product" do
        exactMatchEff "cip_step_circuit" (fromCompiledCircuit =<< compileCipStep)
        exactMatchEff "cip_wrap_circuit" (fromCompiledCircuit =<< compileCipWrap)
      describe "Pseudo module" do
        exactMatchEff "utils_ones_vector_n16_step_circuit" (fromCompiledCircuit =<< compileUtilsOnesVectorN16Step)
        exactMatchEff "utils_ones_vector_n16_wrap_circuit" (fromCompiledCircuit =<< compileUtilsOnesVectorN16Wrap)
        exactMatchEff "one_hot_n1_step_circuit" (fromCompiledCircuit =<< compileOneHotN1Step)
        exactMatchEff "one_hot_n1_wrap_circuit" (fromCompiledCircuit =<< compileOneHotN1Wrap)
        exactMatchEff "one_hot_n17_step_circuit" (fromCompiledCircuit =<< compileOneHotN17Step)
        exactMatchEff "one_hot_n17_wrap_circuit" (fromCompiledCircuit =<< compileOneHotN17Wrap)
        exactMatchEff "one_hot_n3_step_circuit" (fromCompiledCircuit =<< compileOneHotN3Step)
        exactMatchEff "one_hot_n3_wrap_circuit" (fromCompiledCircuit =<< compileOneHotN3Wrap)
        exactMatchEff "pseudo_mask_n1_step_circuit" (fromCompiledCircuit =<< compilePseudoMaskN1Step)
        exactMatchEff "pseudo_mask_n1_wrap_circuit" (fromCompiledCircuit =<< compilePseudoMaskN1Wrap)
        exactMatchEff "pseudo_mask_n3_step_circuit" (fromCompiledCircuit =<< compilePseudoMaskN3Step)
        exactMatchEff "pseudo_mask_n3_wrap_circuit" (fromCompiledCircuit =<< compilePseudoMaskN3Wrap)
        exactMatchEff "pseudo_mask_n17_step_circuit" (fromCompiledCircuit =<< compilePseudoMaskN17Step)
        exactMatchEff "pseudo_mask_n17_wrap_circuit" (fromCompiledCircuit =<< compilePseudoMaskN17Wrap)
        exactMatchEff "pseudo_choose_n1_step_circuit" (fromCompiledCircuit =<< compilePseudoChooseN1Step)
        exactMatchEff "pseudo_choose_n1_wrap_circuit" (fromCompiledCircuit =<< compilePseudoChooseN1Wrap)
        exactMatchEff "pseudo_choose_n3_step_circuit" (fromCompiledCircuit =<< compilePseudoChooseN3Step)
        exactMatchEff "pseudo_choose_n3_wrap_circuit" (fromCompiledCircuit =<< compilePseudoChooseN3Wrap)
        exactMatchEff "pseudo_to_domain_wrap_circuit" (fromCompiledCircuit =<< compilePseudoToDomainWrap)
        exactMatchEff "choose_key_n1_wrap_circuit" (fromCompiledCircuit =<< compileChooseKeyN1Wrap)
        exactMatchEff "sideloaded_vk_typ_step_circuit" (fromCompiledCircuit =<< compileSideloadedVkTypStep)
        exactMatchEff "bind_vk_step_circuit" (fromCompiledCircuit =<< compileBindVkStep)
