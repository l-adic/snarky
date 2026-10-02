-- | Shared plumbing for the PureScript side of the circuit diffs.
-- |
-- | Harness rule: a harness lays out the dump's inputs and calls LIBRARY
-- | circuits on them; it never re-implements a circuit. Every constraint row
-- | must come from a named library gadget (`Pickles.*`, `Snarky.Circuit.Kimchi.*`)
-- | or a DSL primitive applied exactly as the dump applies it, so that a
-- | library change is caught by the fixture rather than absorbed by the
-- | harness. Native constant folding (domain generators, their powers, endo
-- | coefficients) is not circuit logic.
module Pickles.CircuitDiffs.PureScript.Common
  ( CompiledCircuit
  , StepArtifact
  , WrapArtifact
  , mkStepArtifact
  , domainLog2OfCompiled
  , preComputeSelfStepDomainLog2
  , dummyVestaPt
  , dummyPallasPt
  , dummyWrapSg
  , domainLog2
  , stepEndo
  , wrapEndo
  , srsLengthLog2
  , wrapDomainLog2
  , wrapSrsLengthLog2
  , deriveStepKey
  , deriveWrapKey
  ) where

import Prelude

import Data.Array (concatMap)
import Data.Array as Array
import Data.Maybe (fromJust)
import Data.Newtype (un)
import Data.Reflectable (class Reflectable, reflectType)
import Effect (Effect)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Pickles.CircuitDiffs.Types (Constants)
import Pickles.Dump.Constants (DerivedKey)
import Pickles.Field (StepField, WrapField)
import Pickles.VerificationKey (VerificationKey)
import Snarky.Backend.Builder (CircuitBuilderState, constraintsToArray)
import Snarky.Backend.Kimchi (makeConstraintSystemWithPrevChallenges)
import Snarky.Backend.Kimchi.Class (createProverIndex, createVerifierIndex, crsSize)
import Snarky.Backend.Kimchi.Proof (proverIndexDomainLog2)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F(..))
import Snarky.Constraint.Kimchi (KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState(..), KimchiRow, toKimchiRows)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, generator, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..), WeierstrassAffinePoint)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Compiled circuit type
-------------------------------------------------------------------------------

type CompiledCircuit f = CircuitBuilderState (KimchiGate f) (AuxState f)

-------------------------------------------------------------------------------
-- | Dummy points
-------------------------------------------------------------------------------

dummyVestaPt :: AffinePoint (F WrapField)
dummyVestaPt =
  let
    g = unsafePartial $ fromJust $ toAffine (generator :: VestaG)
  in
    AffinePoint { x: F g.x, y: F g.y }

dummyPallasPt :: AffinePoint (F StepField)
dummyPallasPt =
  let
    g = unsafePartial $ fromJust $ toAffine (generator :: PallasG)
  in
    AffinePoint { x: F g.x, y: F g.y }

dummyWrapSg :: AffinePoint StepField
dummyWrapSg = AffinePoint
  { x: fromBigInt $ unsafePartial fromJust $ BigInt.fromString "8063668238751197448664615329057427953229339439010717262869116690340613895496"
  , y: fromBigInt $ unsafePartial fromJust $ BigInt.fromString "2694491010813221541025626495812026140144933943906714931997499229912601205355"
  }

-------------------------------------------------------------------------------
-- | Constants
-------------------------------------------------------------------------------

domainLog2 :: Int
domainLog2 = 16

stepEndo :: StepField
stepEndo = let EndoScalar e = endoScalar @Vesta.BaseField @StepField in e

wrapEndo :: WrapField
wrapEndo = let EndoScalar e = endoScalar @Pallas.BaseField @WrapField in e

srsLengthLog2 :: Int
srsLengthLog2 = 16

wrapDomainLog2 :: Int
wrapDomainLog2 = 15

wrapSrsLengthLog2 :: Int
wrapSrsLengthLog2 = 15

--------------------------------------------------------------------------------
-- VK derivation
--------------------------------------------------------------------------------

-- | Derive a step `VerifierIndex` from a compiled step constraint system,
-- | with its domain.
-- |
-- | Mirrors `Pickles.Prove.Step.stepCompile`'s
-- | `makeConstraintSystemWithPrevChallenges + createProverIndex +
-- | createVerifierIndex` tail. Byte-identical to OCaml's
-- | `Pickles.compile_promise` for the same step CS + SRS.
deriveStepKey
  :: forall @len
   . Reflectable len Int
  => CRS VestaG
  -> CompiledCircuit StepField
  -> Effect (DerivedKey VestaG StepField)
deriveStepKey vestaSrs builtState = do
  let
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) (constraintsToArray builtState.constraints)
  csResult <- makeConstraintSystemWithPrevChallenges @StepField
    { constraints: kimchiRows
    , publicInputs: builtState.publicInputs
    , unionFind: (un AuxState builtState.aux).wireState.unionFind
    , prevChallengesCount: reflectType (Proxy @len)
    , maxPolySize: crsSize vestaSrs
    }
  let
    proverIndex = createProverIndex @StepField @VestaG
      { gates: csResult.gates
      , publicInputSize: csResult.publicInputSize
      , prevChallengesCount: csResult.prevChallengesCount
      , maxPolySize: csResult.maxPolySize
      , crs: vestaSrs
      }
  pure
    { verifierIndex: createVerifierIndex @StepField @VestaG proverIndex
    , domainLog2: proverIndexDomainLog2 proverIndex
    }

-- | Wrap-side analog of `deriveStepKey`. The wrap CS lives in `WrapField`
-- | over Pallas; commitments are Pallas points with coordinates in
-- | `Pallas.BaseField = StepField`, so the resulting key is what a step
-- | circuit consumes when verifying the wrap proof.
deriveWrapKey
  :: forall @len
   . Reflectable len Int
  => CRS PallasG
  -> CompiledCircuit WrapField
  -> Effect (DerivedKey PallasG WrapField)
deriveWrapKey pallasSrs builtState = do
  let
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) (constraintsToArray builtState.constraints)
  csResult <- makeConstraintSystemWithPrevChallenges @WrapField
    { constraints: kimchiRows
    , publicInputs: builtState.publicInputs
    , unionFind: (un AuxState builtState.aux).wireState.unionFind
    , prevChallengesCount: reflectType (Proxy @len)
    , maxPolySize: crsSize pallasSrs
    }
  let
    proverIndex = createProverIndex @WrapField @PallasG
      { gates: csResult.gates
      , publicInputSize: csResult.publicInputSize
      , prevChallengesCount: csResult.prevChallengesCount
      , maxPolySize: csResult.maxPolySize
      , crs: pallasSrs
      }
  pure
    { verifierIndex: createVerifierIndex @WrapField @PallasG proverIndex
    , domainLog2: proverIndexDomainLog2 proverIndex
    }

-------------------------------------------------------------------------------
-- | Compile-result artifacts
-- |
-- | Compile artifacts bundle a `CompiledCircuit` with the most-commonly
-- | needed *derived* fields (domain log2 from row count, wrap VK from
-- | commitments) so downstream compiles consume them as records rather
-- | than re-deriving from scratch.
-- |
-- | This is the test-side analog of OCaml's `Compiled.t` record
-- | (`compile.ml`'s output bundling `step_domains`, `wrap_domains`,
-- | `step_keys`, `wrap_key`). Eliminates the "hardcoded placeholder
-- | values" failure mode that bit several wrap-fixture tests when
-- | OCaml fixtures were regenerated from production drivers.
-------------------------------------------------------------------------------

type StepArtifact =
  { stepCs :: CompiledCircuit StepField
  , stepDomainLog2 :: Int
  }

type WrapArtifact =
  { stepCs :: CompiledCircuit StepField
  , stepDomainLog2 :: Int
  , wrapCs :: CompiledCircuit WrapField
  , wrapVk :: VerificationKey 1 (WeierstrassAffinePoint PallasG (F StepField))
  -- ^ The wrap circuit's own key, whole: a step circuit's slot verifies
  -- its proofs against it.
  , wrapKey :: DerivedKey PallasG WrapField
  , constants :: Constants
  -- ^ The constants the wrap circuit bakes in (`wrapMainConstants`).
  }

-- | Construct a `StepArtifact` from a compiled step CS, deriving the
-- | step domain log2 from the row count.
mkStepArtifact :: CompiledCircuit StepField -> StepArtifact
mkStepArtifact cs =
  { stepCs: cs
  , stepDomainLog2: domainLog2OfCompiled cs
  }

-- | Round up the constraint count to the next power-of-2 log. Mirrors
-- | OCaml's `Fix_domains.domains` row-count → log2 calculation
-- | (`compile.ml`), which sets the kimchi prover-index domain size.
domainLog2OfCompiled :: CompiledCircuit StepField -> Int
domainLog2OfCompiled builtState =
  let
    kimchiRows :: Array (KimchiRow StepField)
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) (constraintsToArray builtState.constraints)
    n = Array.length kimchiRows
  in
    ceilLog2 n
  where
  ceilLog2 :: Int -> Int
  ceilLog2 n
    | n <= 1 = 0
    | otherwise = go 0 1
        where
        go k acc = if acc >= n then k else go (k + 1) (acc * 2)

-- | Shape-pass + extract domain log2. For rules with self-prev slots
-- | whose own step domain log2 must be baked into their own
-- | `WrapMainConfig` — a self-circularity OCaml resolves with
-- | `Fix_domains.domains`' two-pass compile.
-- |
-- | Caller supplies a thunk that compiles the rule with ANY placeholder
-- | self log2 in `perSlotFopDomainLog2s`; we discard the resulting CS
-- | and read only its row count. The placeholder doesn't drift because
-- | it's never compared to anything.
preComputeSelfStepDomainLog2
  :: Effect (CompiledCircuit StepField) -> Effect Int
preComputeSelfStepDomainLog2 shapeCompile =
  domainLog2OfCompiled <$> shapeCompile
