module Pickles.CircuitDiffs.PureScript.StepVerify
  ( StepVerifyInput(..)
  , StepVerifyParams
  , stepVerifyBody
  , compileStepVerify
  ) where

import Prelude

import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (Tuple5, tuple5, uncurry5)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyPallasPt, dummyWrapSg, stepEndo)
import Pickles.CircuitDiffs.PureScript.PerProofWitness (PerProofWitnessInput(..), unfinalizedDeferredValues)
import Pickles.Field (StepField)
import Pickles.IncrementallyVerifyProof (incrementallyVerifyProof, packStatement)
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBaseLookup)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Step.Types (WrapProof(..))
import Pickles.Types (ChunkedCommitment(..), PerProofUnfinalized(..), WrapProofMessages(..), WrapProofOpening(..))
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, BoolVar, F(..), FVar, Snarky, UnChecked(..), assertEq, const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields, if_)
import Snarky.Circuit.Kimchi (SplitField, Type2, groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | Step_verifier.verify circuit — tests the full verify pipeline:
-- |   1. packStatement (Spec.pack equivalent)
-- |   2. incrementallyVerifyProof
-- |   3. Assertions (digest + bp challenges)

type StepVerifyParams =
  { lagrangeAt :: LagrangeBaseLookup 1 StepField
  , blindingH :: AffinePoint (F StepField)
  }

-- | `step_verify{,_n2}_circuit`'s input (OCaml `dump_circuit_impl.ml`) at `w` previous proofs:
-- | the per-proof witness with no application state (its evaluations dead inputs), the
-- | unfinalized proof it is checked against, `is_base_case`, and the two message digests.
newtype StepVerifyInput w f b pt = StepVerifyInput
  { witness :: PerProofWitnessInput Unit w f b pt
  , unfinalized :: PerProofUnfinalized 15 (Type2 (SplitField f b)) f b
  , isBaseCase :: b
  , messagesForNextWrapProof :: f
  , messagesForNextStepProof :: f
  }

-- | The wire order.
type StepVerifyTuple w f b pt =
  Tuple5 (PerProofWitnessInput Unit w f b pt) (PerProofUnfinalized 15 (Type2 (SplitField f b)) f b) b f f

toTuple :: forall w f b pt. StepVerifyInput w f b pt -> StepVerifyTuple w f b pt
toTuple (StepVerifyInput i) =
  tuple5 i.witness i.unfinalized i.isBaseCase i.messagesForNextWrapProof i.messagesForNextStepProof

fromTuple :: forall w f b pt. StepVerifyTuple w f b pt -> StepVerifyInput w f b pt
fromTuple = uncurry5 \witness unfinalized isBaseCase messagesForNextWrapProof messagesForNextStepProof ->
  StepVerifyInput { witness, unfinalized, isBaseCase, messagesForNextWrapProof, messagesForNextStepProof }

instance
  ( Reflectable w Int
  , CircuitType f fa fv
  , CircuitType f ba bv
  , CircuitType f (PerProofWitnessInput Unit w fa ba pa) (PerProofWitnessInput Unit w fv bv pv)
  , CircuitType f (PerProofUnfinalized 15 (Type2 (SplitField fa ba)) fa ba) (PerProofUnfinalized 15 (Type2 (SplitField fv bv)) fv bv)
  ) =>
  CircuitType f (StepVerifyInput w fa ba pa) (StepVerifyInput w fv bv pv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(StepVerifyTuple w fa ba pa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(StepVerifyTuple w fa ba pa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(StepVerifyTuple w fa ba pa)

-- | The circuit over the input with the given `sg_old`: the packed statement, the
-- | incrementally verified wrap proof, the digest asserted unconditionally
-- | (step_verifier.ml:1294), the challenges gated by `is_base_case` (step_verifier.ml:1300-1314).
stepVerifyBody
  :: forall w r
   . StepVerifyParams
  -> Vector 2 (AffinePoint (FVar StepField))
  -> StepVerifyInput w (FVar StepField) (BoolVar StepField) (AffinePoint (FVar StepField))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
stepVerifyBody { lagrangeAt, blindingH } sgOld (StepVerifyInput input) = do
  let
    PerProofWitnessInput witness = input.witness
    WrapProof proof = witness.wrapProof
    WrapProofMessages m = proof.messages
    WrapProofOpening o = proof.opening
    PerProofUnfinalized u = input.unfinalized
    deferredValues = unfinalizedDeferredValues input.unfinalized
    constDummyPt = let AffinePoint { x: F x', y: F y' } = dummyPallasPt in AffinePoint { x: const_ x', y: const_ y' }

    -- packStatement: Spec.pack(to_data(statement))
    publicInput = packStatement
      { proofState:
          { deferredValues: witness.deferredValues
          , spongeDigestBeforeEvaluations: witness.spongeDigest
          , messagesForNextWrapProof: input.messagesForNextWrapProof
          }
      , messagesForNextStepProof: input.messagesForNextStepProof
      }

    ivpParams =
      { curveParams: curveParams (Proxy @PallasG)
      , lagrangeAt
      , blindingH
      , correctionMode: PureCorrections
      , endo: stepEndo
      , groupMapParams: groupMapParams (Proxy @PallasG)
      , useOptSponge: false
      }

    ivpInput =
      { publicInput
      , sgOld
      , sgOldMask: Nothing
      , sigmaCommLast: ChunkedCommitment (Vector.singleton constDummyPt)
      , columnComms:
          { index: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 6 _
          , coeff: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 15 _
          , sigma: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 6 _
          }
      , deferredValues
      , wComm: m.wComm
      , zComm: m.zComm
      , tComm: Vector.concat (coerce m.tComm :: Vector 7 (Vector 1 (AffinePoint (FVar StepField))))
      , opening: { delta: o.delta, sg: o.sg, lr: o.lr, z1: o.z1, z2: o.z2 }
      }

  output <- evalSpongeM initialSpongeCircuit $
    incrementallyVerifyProof @PallasG StepOtherField.ipaScalarOps ivpParams ivpInput Nothing
  assertEq u.spongeDigest output.spongeDigestBeforeEvaluations
  for_ (Vector.zip deferredValues.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) -> do
    c2' <- if_ input.isBaseCase c1 c2
    assertEq c1 c2'

-- | `step_verify_circuit`: no previous proofs; the two `sg_old` the dummy wrap `sg`.
stepVerifyCircuit
  :: forall r
   . StepVerifyParams
  -> UnChecked (StepVerifyInput 0 (FVar StepField) (BoolVar StepField) (AffinePoint (FVar StepField)))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
stepVerifyCircuit params (UnChecked input) =
  let
    constDummySg = AffinePoint { x: const_ (unwrap dummyWrapSg).x, y: const_ (unwrap dummyWrapSg).y }
  in
    stepVerifyBody params (constDummySg :< constDummySg :< Vector.nil) input

compileStepVerify :: StepVerifyParams -> Effect (CompiledCircuit StepField)
compileStepVerify srsData =
  compile noAdvice
    (Proxy @(UnChecked (StepVerifyInput 0 (F StepField) Boolean (AffinePoint StepField))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    (stepVerifyCircuit srsData)
