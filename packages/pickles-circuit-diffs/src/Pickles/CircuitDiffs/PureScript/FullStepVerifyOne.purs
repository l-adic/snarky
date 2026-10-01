module Pickles.CircuitDiffs.PureScript.FullStepVerifyOne
  ( FullStepVerifyOneInput(..)
  , FullStepVerifyOneParams
  , verifyOneInputOf
  , compileFullStepVerifyOne
  ) where

-- | Thin wrapper around Pickles.Step.VerifyOne.verifyOne for circuit diff testing, over the
-- | dump's typed input.

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple4, tuple4, uncurry4)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyPallasPt, dummyWrapSg, stepEndo)
import Pickles.CircuitDiffs.PureScript.PerProofWitness (PerProofWitnessInput(..), unfinalizedDeferredValues)
import Pickles.Constants (zkRowsByDefault)
import Pickles.Field (StepField)
import Pickles.FinalizeOtherProof (DomainMode(..))
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PlonkChecks (singleChunkEvals)
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBaseLookup)
import Pickles.Step.Types (WrapProof(..))
import Pickles.Step.VerifyOne (VerifyOneInput, verifyOne)
import Pickles.Types (AllocEvals(..), ChunkedCommitment(..), PerProofUnfinalized(..), StepIPARounds, WrapIPARounds, WrapProofMessages(..), WrapProofOpening(..), WrapVkChunks)
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, Bool(..), BoolVar, F(..), FVar, Snarky, UnChecked(..), const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (SplitField, Type2, groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

type FullStepVerifyOneParams =
  { lagrangeAt :: LagrangeBaseLookup 1 StepField
  , blindingH :: AffinePoint (F StepField)
  }

-- | `full_step_verify_one{,_n2}_circuit`'s input (OCaml `dump_circuit_impl.ml`) at `w`
-- | previous proofs: the per-proof witness with a one-field application state, the
-- | unfinalized proof, the claimed `messages_for_next_wrap_proof` digest, and `must_verify`.
newtype FullStepVerifyOneInput w f b pt = FullStepVerifyOneInput
  { witness :: PerProofWitnessInput f w f b pt
  , unfinalized :: PerProofUnfinalized 15 (Type2 (SplitField f b)) f b
  , messagesForNextWrapProof :: f
  , mustVerify :: b
  }

-- | The wire order.
type FullStepVerifyOneTuple w f b pt =
  Tuple4 (PerProofWitnessInput f w f b pt) (PerProofUnfinalized 15 (Type2 (SplitField f b)) f b) f b

toTuple :: forall w f b pt. FullStepVerifyOneInput w f b pt -> FullStepVerifyOneTuple w f b pt
toTuple (FullStepVerifyOneInput i) =
  tuple4 i.witness i.unfinalized i.messagesForNextWrapProof i.mustVerify

fromTuple :: forall w f b pt. FullStepVerifyOneTuple w f b pt -> FullStepVerifyOneInput w f b pt
fromTuple = uncurry4 \witness unfinalized messagesForNextWrapProof mustVerify ->
  FullStepVerifyOneInput { witness, unfinalized, messagesForNextWrapProof, mustVerify }

instance
  ( Reflectable w Int
  , CircuitType f fa fv
  , CircuitType f ba bv
  , CircuitType f (PerProofWitnessInput fa w fa ba pa) (PerProofWitnessInput fv w fv bv pv)
  , CircuitType f (PerProofUnfinalized 15 (Type2 (SplitField fa ba)) fa ba) (PerProofUnfinalized 15 (Type2 (SplitField fv bv)) fv bv)
  ) =>
  CircuitType f (FullStepVerifyOneInput w fa ba pa) (FullStepVerifyOneInput w fv bv pv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(FullStepVerifyOneTuple w fa ba pa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(FullStepVerifyOneTuple w fa ba pa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(FullStepVerifyOneTuple w fa ba pa)

-- | `verifyOne`'s input from the dump's, at the given proof mask and `sg_old`, the key the
-- | dummy.
verifyOneInputOf
  :: forall w
   . Vector w (BoolVar StepField)
  -> Vector 2 (AffinePoint (FVar StepField))
  -> FullStepVerifyOneInput w (FVar StepField) (BoolVar StepField) (AffinePoint (FVar StepField))
  -> VerifyOneInput w WrapVkChunks 7 WrapIPARounds StepIPARounds (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (FVar StepField) (BoolVar StepField)
verifyOneInputOf proofMask sgOld (FullStepVerifyOneInput input) =
  let
    PerProofWitnessInput witness = input.witness
    WrapProof proof = witness.wrapProof
    WrapProofMessages m = proof.messages
    WrapProofOpening o = proof.opening
    AllocEvals evals = witness.evals
    PerProofUnfinalized u = input.unfinalized
    dv = witness.deferredValues
    constDummyPt = let AffinePoint { x: F x', y: F y' } = dummyPallasPt in AffinePoint { x: const_ x', y: const_ y' }
  in
    { appStateFields: [ witness.appState ]
    , wComm: m.wComm
    , zComm: m.zComm
    , tComm: Vector.concat (coerce m.tComm :: Vector 7 (Vector 1 (AffinePoint (FVar StepField))))
    , lr: o.lr
    , z1: o.z1
    , z2: o.z2
    , delta: o.delta
    , sg: o.sg
    , proofState:
        { plonk: dv.plonk
        , combinedInnerProduct: dv.combinedInnerProduct
        , b: dv.b
        , xi: dv.xi
        , bulletproofChallenges: dv.bulletproofChallenges
        , spongeDigest: witness.spongeDigest
        }
    , chunkedEvals: singleChunkEvals evals
    , prevChallenges: witness.prevChallenges
    , prevSgs: witness.prevSgs
    , unfinalized:
        { deferredValues: unfinalizedDeferredValues input.unfinalized
        , shouldFinalize: u.shouldFinalize
        , claimedDigest: u.spongeDigest
        }
    , messagesForNextWrapProof: input.messagesForNextWrapProof
    , mustVerify: input.mustVerify
    , branchData:
        { proofsVerifiedMask: map coerce dv.branchData.proofsVerifiedMask
        , domainLog2: dv.branchData.domainLog2
        }
    , proofMask
    , vkComms:
        { sigma: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 6 _
        , sigmaLast: ChunkedCommitment (Vector.singleton constDummyPt)
        , coeff: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 15 _
        , index: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 6 _
        }
    , sgOld
    }

-- | One previous proof: the mask trimmed to its last bit, `sg_old` the dummy wrap `sg` then
-- | the proof's.
fullStepVerifyOneCircuit
  :: forall r
   . FullStepVerifyOneParams
  -> UnChecked (FullStepVerifyOneInput 1 (FVar StepField) (BoolVar StepField) (AffinePoint (FVar StepField)))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
fullStepVerifyOneCircuit { lagrangeAt, blindingH } (UnChecked input@(FullStepVerifyOneInput i)) = do
  let
    PerProofWitnessInput witness = i.witness
    constDummySg = AffinePoint { x: const_ (unwrap dummyWrapSg).x, y: const_ (unwrap dummyWrapSg).y }
    proofMask = Vector.drop @1 witness.deferredValues.branchData.proofsVerifiedMask

    domainLog2 = 16
    fopParams =
      { domains:
          NEA.singleton
            { generator: const_ (LinFFI.domainGenerator @StepField domainLog2)
            , log2: domainLog2
            }
      , shifts: map const_ (LinFFI.domainShifts @StepField domainLog2)
      , srsLengthLog2: 16
      , zkRows: zkRowsByDefault
      , endo: stepEndo
      , linearizationPoly: Linearization.pallas
      , domainMode: KnownDomainsMode
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

  _result <- verifyOne fopParams (verifyOneInputOf proofMask (constDummySg :< witness.prevSgs) input) ivpParams
  pure unit

compileFullStepVerifyOne :: FullStepVerifyOneParams -> Effect (CompiledCircuit StepField)
compileFullStepVerifyOne params =
  compile noAdvice
    (Proxy @(UnChecked (FullStepVerifyOneInput 1 (F StepField) Boolean (AffinePoint StepField))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    (fullStepVerifyOneCircuit params)
