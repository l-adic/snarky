-- | Step circuit combinator for Pickles recursion.
-- |
-- | The Step circuit combines an application circuit with verification of
-- | previous Wrap proofs. It handles both base case (no real proofs) and
-- | recursive cases (verifying previous Wrap proofs).
-- |
-- | Key mechanism: The `shouldFinalize` flag enables bootstrapping. Dummy proofs
-- | have `shouldFinalize = false`, which makes `finalized || not shouldFinalize`
-- | pass regardless of verification result.
-- |
-- | Reference: mina/src/lib/pickles/step_main.ml:274-594
module Pickles.Step.Circuit
  ( -- * Application Circuit Types
    AppCircuit
  , AppCircuitInput
  , AppCircuitOutput
  -- * Step Circuit Types (re-exported from Pickles.Types)
  , module Pickles.Types
  -- * Wrap Statement Public Input
  , WrapStatementPublicInput
  , buildWrapPublicInput
  -- * Step Circuit Combinator
  , stepCircuit
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Reflectable (class Reflectable)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Linearization.FFI (class LinearizationFFI)
import Pickles.ProofWitness (ProofWitness)
import Pickles.Step.Advice (class StepWitnessM, getFopProofStates, getMessages, getMessagesForNextWrapProof, getOpeningProof, getPrevChallenges, getProofWitnesses, getSgOld, getWrapVerifierIndex)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofOutput, FinalizeOtherProofParams, finalizeOtherProofCircuit)
import Pickles.Step.MessageHash (hashMessagesForNextStepProof)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Types (StepInput, StepStatement)
import Pickles.PublicInputCommit (CorrectionMode)
import Pickles.Verify.Types (UnfinalizedProof)
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, FVar, Snarky, assertEq, assert_, const_, exists, label, not_, or_)
import Snarky.Circuit.DSL.SizedF (SizedF, toField, unsafeMkSizedF)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField, fromInt)
import Snarky.Circuit.DSL (F) as DSL
import Snarky.Curves.Vesta as Vesta
import Snarky.Circuit.Kimchi (GroupMapParams)
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)
import Snarky.Types.Shifted (SplitField, Type1(..), Type2)

-------------------------------------------------------------------------------
-- | Application Circuit Types
-------------------------------------------------------------------------------

-- | Input to an application circuit.
-- |
-- | The application receives:
-- | - `appInput`: Its own application-specific input
-- | - `previousProofInputs`: Public inputs from previous proofs (for recursive apps)
-- |
-- | For base case (no recursion), `previousProofInputs` contains dummy values.
type AppCircuitInput n input prevInput =
  { appInput :: input
  , previousProofInputs :: Vector n prevInput
  }

-- | Output from an application circuit.
-- |
-- | The application returns:
-- | - `mustVerify`: Which previous proofs should actually be verified
-- | - `publicOutput`: The application's public output
-- | - `auxiliaryOutput`: Private prover data (not part of public statement)
-- |
-- | For base case, `mustVerify` should be all false.
type AppCircuitOutput n output aux f =
  { mustVerify :: Vector n (BoolVar f)
  , publicOutput :: output
  , auxiliaryOutput :: aux
  }

-- | Type alias for an application circuit in the Step context.
-- |
-- | An application circuit:
-- | 1. Receives its input + previous proof public inputs
-- | 2. Does its application logic (e.g., verify a signature)
-- | 3. Returns which previous proofs to verify + its output
-- |
-- | The Step combinator handles the actual verification of previous proofs.
type AppCircuit n input prevInput output aux f c t m =
  AppCircuitInput n input prevInput
  -> Snarky c t m (AppCircuitOutput n output aux f)

-------------------------------------------------------------------------------
-- | Finalize Other Proof
-------------------------------------------------------------------------------

-- | Finalize another proof's deferred values.
-- |
-- | Wraps `finalizeOtherProofCircuit`. The sponge is handled internally
-- | by `finalizeOtherProofCircuit` (challenge_digest + Fr-sponge).
finalizeOtherProof
  :: forall _d d n f f' g t m r2
   . Add 1 _d d
  => PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => HasEndo f f'
  => CircuitM f (KimchiConstraint f) t m
  => LinearizationFFI f g
  => Reflectable d Int
  => FinalizeOtherProofParams f r2
  -> { mask :: Vector n (BoolVar f)
     , prevChallenges :: Vector n (Vector d (FVar f))
     , domainLog2Var :: FVar f
     }
  -> UnfinalizedProof d (FVar f) (Type1 (FVar f)) (BoolVar f)
  -> ProofWitness (FVar f)
  -> Snarky (KimchiConstraint f) t m (FinalizeOtherProofOutput d f)
finalizeOtherProof params shared unfinalized witness =
  finalizeOtherProofCircuit StepOtherField.fopShiftOps params
    { unfinalized
    , witness
    , mask: shared.mask
    , prevChallenges: shared.prevChallenges
    , domainLog2Var: shared.domainLog2Var
    }

-------------------------------------------------------------------------------
-- | Wrap Statement Public Input (Spec.pack output)
-------------------------------------------------------------------------------

-- | Type alias for the Wrap Statement packed as public input for the Step IVP.
-- |
-- | This matches OCaml's Spec.pack of Types.Wrap.Statement.In_circuit:
-- |   Vec5 FVar:       [cip, b, zetaToSrs, zetaToDom, perm]
-- |   Vec2 SizedF128:  [beta, gamma]
-- |   Vec3 SizedF128:  [alpha, zeta, xi]
-- |   Vec3 FVar:       [spongeDigest, msgWrap, msgStep]
-- |   Vec(ds) SizedF128: bulletproof_challenges (StepIPARounds)
-- |   SizedF10:        branch_data
-- |
-- | Reference: composition_types.ml Per_proof.In_circuit.to_data (line 1212)
type WrapStatementPublicInput ds f =
  Tuple (Vector 5 f)
    ( Tuple (Vector 2 (SizedF 128 f))
        ( Tuple (Vector 3 (SizedF 128 f))
            ( Tuple (Vector 3 f)
                ( Tuple (Vector ds (SizedF 128 f))
                    (SizedF 10 f)
                )
            )
        )
    )

-- | Build the Wrap Statement public input from per-proof data.
-- |
-- | Constructs the Spec.pack tuple from the fopState's deferred values,
-- | message digests, and branch_data.
-- |
-- | branch_data = 4*domainLog2 + mask0 + 2*mask1
-- |   where mask encodes proofs_verified (MaxProofsVerified=2)
-- |
-- | Reference: step_main.ml:70-80, step_verifier.ml:1242-1315
buildWrapPublicInput
  :: forall ds f
   . PrimeField f
  => { fopState :: UnfinalizedProof ds (FVar f) (Type1 (FVar f)) (BoolVar f)
     , messagesForNextWrapProof :: FVar f
     , messagesForNextStepProof :: FVar f
     , domainLog2 :: Int
     , mask0 :: BoolVar f
     , mask1 :: BoolVar f
     }
  -> WrapStatementPublicInput ds (FVar f)
buildWrapPublicInput { fopState, messagesForNextWrapProof, messagesForNextStepProof, domainLog2, mask0, mask1 } =
  let
    dv = fopState.deferredValues
    p = dv.plonk

    -- Unwrap Type1 to get the underlying FVar
    unwrap :: Type1 (FVar f) -> FVar f
    unwrap (Type1 x) = x

    -- Branch_data.pack: 4*domainLog2 + mask0 + 2*mask1
    -- Fits in 10 bits: 4*15 + 1 + 2 = 63 < 1024
    branchData :: SizedF 10 (FVar f)
    branchData =
      let
        four = one + one + one + one
        two = one + one
        m0 :: FVar f
        m0 = coerce mask0
        m1 :: FVar f
        m1 = coerce mask1
      in
        unsafeMkSizedF $ CVar.add_ (CVar.scale_ four (const_ (fromInt domainLog2))) (CVar.add_ m0 (CVar.scale_ two m1))
  in
    Tuple
      -- Vec5 FVar: [cip, b, zetaToSrs, zetaToDom, perm]
      ( unwrap dv.combinedInnerProduct
          :< unwrap dv.b
          :< unwrap p.zetaToSrsLength
          :< unwrap p.zetaToDomainSize
          :< unwrap p.perm
          :< Vector.nil
      )
      ( Tuple
          -- Vec2 SizedF128: [beta, gamma]
          (p.beta :< p.gamma :< Vector.nil)
          ( Tuple
              -- Vec3 SizedF128: [alpha, zeta, xi]
              (p.alpha :< p.zeta :< dv.xi :< Vector.nil)
              ( Tuple
                  -- Vec3 FVar: [spongeDigest, msgWrap, msgStep]
                  ( fopState.spongeDigestBeforeEvaluations
                      :< messagesForNextWrapProof
                      :< messagesForNextStepProof
                      :< Vector.nil
                  )
                  ( Tuple
                      -- Vec(ds) SizedF128: bulletproof_challenges
                      dv.bulletproofChallenges
                      -- SizedF10: branch_data
                      branchData
                  )
              )
          )
      )

-------------------------------------------------------------------------------
-- | Step Circuit Combinator
-------------------------------------------------------------------------------

-- | The Step circuit combinator.
-- |
-- | Takes an application circuit and returns a Step circuit that:
-- | 1. Runs the application circuit
-- | 2. For each previous proof: FOP, hash messages, build statement, verify
-- | 3. Returns a StepStatement for the Wrap circuit
-- |
-- | **Processing (see step_main.ml:274-594, verify_one:17-117):**
-- | 1. Run application circuit -> get `mustVerify` flags
-- | 2. Load private witness data via advisory monad
-- | 3. For each previous proof:
-- |    - Assert `shouldFinalize == mustVerify`
-- |    - Call `finalizeOtherProof` -> `(finalized, challenges)`
-- |    - Hash messages for next Step proof
-- |    - Build Wrap Statement public input
-- |    - Call `incrementallyVerifyProof` (IVP)
-- |    - Assert digest (unconditional) and bp challenges (gated by isBaseCase)
-- |    - Assert `(verified && finalized) || not mustVerify`
-- | 4. Return StepStatement with FOP output challenges
-- |
-- | **For base case (Step0):** All `mustVerify = false`, `isBaseCase = true`,
-- | assertions pass trivially. Pass dummy data via advisory monad.
stepCircuit
  :: forall n _ds @ds _dw dw input prevInput output aux t m r
   . Add 1 _ds ds
  => Add 1 _dw dw
  => CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
  => StepWitnessM n ds dw m Vesta.ScalarField
  => Reflectable n Int
  => Reflectable ds Int
  => Reflectable dw Int
  => FinalizeOtherProofParams Vesta.ScalarField
       ( curveParams :: CurveParams Vesta.ScalarField
       , lagrangeComms :: Array (AffinePoint (DSL.F Vesta.ScalarField))
       , blindingH :: AffinePoint (DSL.F Vesta.ScalarField)
       , groupMapParams :: GroupMapParams Vesta.ScalarField
       , correctionMode :: CorrectionMode
       , useOptSponge :: Boolean
       | r
       )
  -> AppCircuit n input prevInput output aux Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
  -> StepInput n input prevInput ds dw (FVar Vesta.ScalarField) (Type2 (SplitField (FVar Vesta.ScalarField) (BoolVar Vesta.ScalarField))) (BoolVar Vesta.ScalarField)
  -> Snarky (KimchiConstraint Vesta.ScalarField) t m (StepStatement n ds dw (FVar Vesta.ScalarField) (Type2 (SplitField (FVar Vesta.ScalarField) (BoolVar Vesta.ScalarField))) (BoolVar Vesta.ScalarField))
stepCircuit params appCircuit { appInput, previousProofInputs, unfinalizedProofs } = label "step-circuit" do
  -- 1. Run application circuit
  { mustVerify } <- appCircuit { appInput, previousProofInputs }

  -- 2. Request private proof witnesses via advisory monad
  proofWitnesses <- exists $ lift $ getProofWitnesses @_ @ds @dw unit
  prevChallenges <- exists $ lift $ getPrevChallenges @_ @ds @dw unit
  fopProofStates <- exists $ lift $ getFopProofStates @_ @ds @dw unit
  messagesForNextWrapProof <- exists $ lift $ getMessagesForNextWrapProof @_ @ds @dw unit
  wrapVk <- exists $ lift $ getWrapVerifierIndex @n @ds @dw unit
  sgOld <- exists $ lift $ getSgOld @n @ds @dw unit
  -- TODO: used by IVP when wired in
  _messages <- exists $ lift $ getMessages @n @ds @dw unit
  _openingProofs <- exists $ lift $ getOpeningProof @n @ds @dw unit

  let
    shared =
      { mask: mustVerify
      , prevChallenges
      , domainLog2Var: const_ (fromInt params.domainLog2)
      }

  -- 3. For each proof: FOP → (finalized, challenges), assert bootstrapping invariant
  let proofsWithData = Vector.zip (Vector.zip unfinalizedProofs (Vector.zip fopProofStates proofWitnesses)) mustVerify
  allChallenges <- for proofsWithData \(Tuple (Tuple unfinalized (Tuple fopState witness)) mustVerifyFlag) -> do
    let shouldFinalize = unfinalized.shouldFinalize
    assertEq shouldFinalize mustVerifyFlag
    { finalized, challenges } <- finalizeOtherProof params shared fopState witness
    -- TODO: replace with (verified && finalized) || not mustVerify
    -- once IVP is wired in (needs self-consistent dummy data for base case)
    finalizedOrNotRequired <- or_ finalized (not_ shouldFinalize)
    assert_ finalizedOrNotRequired
    pure challenges

  -- 4. Hash messages for next Step proof (uses VK + all proofs' sg + bp challenges)
  let
    hashInput =
      { vkComms:
          { sigma: wrapVk.columnComms.sigma
          , sigmaLast: wrapVk.sigmaCommLast
          , coeff: wrapVk.columnComms.coeff
          , index: wrapVk.columnComms.index
          }
      , proofs: Vector.zipWith
          (\sg chals -> { sg, bpChallenges: map toField chals })
          sgOld
          allChallenges
      }
  messagesForNextStepProof <- hashMessagesForNextStepProof hashInput

  pure
    { proofState: { unfinalizedProofs, messagesForNextStepProof }
    , messagesForNextWrapProof
    }
