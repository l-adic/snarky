-- | Wrap main circuit — the SNARK function for wrapping any step proof.
-- |
-- | Parameterized by:
-- | - @branches: number of step circuit variants (N1 or N2)
-- | - @slot0Width, @slot1Width: max number of previous proofs per slot
-- |   (determines old_bp_chals layout and FOP padding)
-- |
-- | The circuit:
-- | 1. Selects the active branch via one-hot vector
-- | 2. Computes branch_data and asserts it matches the public input
-- | 3. Selects verification key via choose_key
-- | 4. Runs FOP (finalize other proof) for each of the 2 unfinalized proofs
-- | 5. Hashes messages for next wrap proof
-- | 6. Runs the IVP (incrementally verify proof) with Opt sponge
-- |
-- | Reference: mina/src/lib/crypto/pickles/wrap_main.ml
module Pickles.Wrap.Main
  ( WrapMainConfig
  , WrapMainAdvice
  , WrapStatementData
  , UnfinalizedProofData
  , ProofWitnessData
  , OpeningProofData
  , MessagesData
  , wrapMainCircuit
  ) where

import Prelude

import Data.Fin (Finite, unsafeFinite)
import Data.Foldable (foldl)
import Data.Reflectable (class Reflectable)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PackedStatement (PackedStepPublicInput, fromPackedTuple)
import Pickles.Pseudo as Pseudo
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBase)
import Pickles.Sponge (evalSpongeM, spongeFromConstants)
import Pickles.Types (StepIPARounds, WrapField, WrapIPARounds)
import Pickles.VerificationKey (StepVK, chooseKey)
import Pickles.Wrap.FinalizeOtherProof (wrapFinalizeOtherProofCircuit)
import Pickles.Wrap.MessageHash (dummyPaddingSpongeStates, hashMessagesForNextWrapProofCircuit')
import Pickles.Wrap.Verify (wrapVerify)
import Prim.Int (class Add)
import Record as Record
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (add_, scale_) as CVar
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, SizedF, Snarky, add_, and_, assertAny_, assertEqual_, const_, equals_, label, not_)
import Snarky.Circuit.Kimchi (SplitField, Type1, Type2(..), groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (EndoScalar(..), endoScalar) as Curves
import Snarky.Curves.Class (curveParams, fromInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (splitFieldCircuit)
import Type.Proxy (Proxy(..))

-- | Compile-time configuration for wrap_main.
-- | These are fixed for a given circuit compilation (known before constraint generation).
-- |
-- | OCaml equivalents:
-- | - stepWidths: (int, branches) Vector.t
-- | - stepDomains: (Domains.t, branches) Vector.t (we just use domain log2 ints)
-- | - stepKeys: step_keys (we use dummy VKs for now)
-- | - allPossibleLog2s: Wrap_verifier.all_possible_domains
type WrapMainConfig branches =
  { stepWidths :: Vector branches Int
  , domainLog2s :: Vector branches Int
  , stepKeys :: Vector branches (StepVK (FVar WrapField))
  -- ^ VK commitments as circuit variables (from chooseKey mask+seal).
  -- Callers wrap constant points with const_ before passing.
  , lagrangeComms :: Array (LagrangeBase WrapField)
  , blindingH :: AffinePoint (F WrapField)
  , allPossibleDomainLog2s :: Vector 3 (Finite 16)
  -- ^ [13, 14, 15] — the possible wrap domain sizes
  , wrapDomainLog2 :: Int
  -- ^ Domain log2 for pow2pow in FOP (usually 15)
  , wrapSrsLengthLog2 :: Int
  -- ^ SRS length log2 (usually 15)
  }

-- | Per-proof advice data from exists/request.
-- |
-- | In OCaml these come from `exists ~request:(fun () -> Req.*)`.
-- | In the test harness they come from flat input parsing.
-- |
-- | old_bp_chals are pre-padded to Padded_length=N2 by the caller
-- | (matching OCaml's Wrap_hack.Checked.pad_challenges).
-- | slot0Chals/slot1Chals contain the REAL challenge vectors per slot.
-- | The caller is responsible for padding with dummyWrapChals.
type WrapMainAdvice slot0Width slot1Width =
  { whichBranch :: FVar WrapField
  , prevProofState ::
      { unfProof0 :: UnfinalizedProofData
      , unfProof1 :: UnfinalizedProofData
      , prevMsgForNextStep :: FVar WrapField
      }
  , prevStepAccs :: { acc0 :: AffinePoint (FVar WrapField), acc1 :: AffinePoint (FVar WrapField) }
  -- Padded to N2: caller prepends dummies as needed
  , paddedChals0 :: Vector 2 (Vector WrapIPARounds (FVar WrapField))
  , paddedChals1 :: Vector 2 (Vector WrapIPARounds (FVar WrapField))
  -- Real (unpadded) challenges per slot, for message hash
  , slot0Chals :: Vector slot0Width (Vector WrapIPARounds (FVar WrapField))
  , slot1Chals :: Vector slot1Width (Vector WrapIPARounds (FVar WrapField))
  , evals :: { evals0 :: ProofWitnessData, evals1 :: ProofWitnessData }
  , wrapDomainIndices :: { idx0 :: FVar WrapField, idx1 :: FVar WrapField }
  , openingProof :: OpeningProofData
  , messages :: MessagesData
  }

-- | Per-proof deferred values (from prev_proof_state.unfinalized_proofs)
type UnfinalizedProofData =
  { deferredValues ::
      { plonk ::
          { alpha :: SizedF 128 (FVar WrapField)
          , beta :: SizedF 128 (FVar WrapField)
          , gamma :: SizedF 128 (FVar WrapField)
          , zeta :: SizedF 128 (FVar WrapField)
          , zetaToSrsLength :: Type2 (FVar WrapField)
          , zetaToDomainSize :: Type2 (FVar WrapField)
          , perm :: Type2 (FVar WrapField)
          }
      , combinedInnerProduct :: Type2 (FVar WrapField)
      , b :: Type2 (FVar WrapField)
      , xi :: SizedF 128 (FVar WrapField)
      , bulletproofChallenges :: Vector WrapIPARounds (SizedF 128 (FVar WrapField))
      }
  , shouldFinalize :: BoolVar WrapField
  , spongeDigestBeforeEvaluations :: FVar WrapField
  , rawFq :: Vector 5 (FVar WrapField)
  }

-- | Evaluation witness data
type ProofWitnessData =
  { allEvals ::
      { ftEval1 :: FVar WrapField
      , publicEvals :: { zeta :: FVar WrapField, omegaTimesZeta :: FVar WrapField }
      , witnessEvals :: Vector 15 { zeta :: FVar WrapField, omegaTimesZeta :: FVar WrapField }
      , coeffEvals :: Vector 15 { zeta :: FVar WrapField, omegaTimesZeta :: FVar WrapField }
      , zEvals :: { zeta :: FVar WrapField, omegaTimesZeta :: FVar WrapField }
      , sigmaEvals :: Vector 6 { zeta :: FVar WrapField, omegaTimesZeta :: FVar WrapField }
      , indexEvals :: Vector 6 { zeta :: FVar WrapField, omegaTimesZeta :: FVar WrapField }
      }
  }

-- | Opening proof data
type OpeningProofData =
  { lr :: Vector StepIPARounds { l :: AffinePoint (FVar WrapField), r :: AffinePoint (FVar WrapField) }
  , z1 :: Type1 (FVar WrapField)
  , z2 :: Type1 (FVar WrapField)
  , delta :: AffinePoint (FVar WrapField)
  , sg :: AffinePoint (FVar WrapField)
  }

-- | Protocol messages
type MessagesData =
  { wComm :: Vector 15 (AffinePoint (FVar WrapField))
  , zComm :: AffinePoint (FVar WrapField)
  , tComm :: Vector 7 (AffinePoint (FVar WrapField))
  }

-- | WrapStatement public input fields
type WrapStatementData =
  { plonk ::
      { alpha :: SizedF 128 (FVar WrapField)
      , beta :: SizedF 128 (FVar WrapField)
      , gamma :: SizedF 128 (FVar WrapField)
      , zeta :: SizedF 128 (FVar WrapField)
      , perm :: Type1 (FVar WrapField)
      , zetaToSrsLength :: Type1 (FVar WrapField)
      , zetaToDomainSize :: Type1 (FVar WrapField)
      }
  , xi :: SizedF 128 (FVar WrapField)
  , combinedInnerProduct :: Type1 (FVar WrapField)
  , b :: Type1 (FVar WrapField)
  , branchData :: FVar WrapField
  , bulletproofChallenges :: Vector StepIPARounds (SizedF 128 (FVar WrapField))
  , spongeDigestBeforeEvaluations :: FVar WrapField
  , messagesForNextWrapProofDigest :: FVar WrapField
  , messagesForNextStepProof :: FVar WrapField
  }

-- | The main wrap circuit, parameterized over branch count and slot widths.
-- |
-- | Reference: mina/src/lib/crypto/pickles/wrap_main.ml
wrapMainCircuit
  :: forall @branches @slot0Width @slot1Width _branchesPred t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => Reflectable branches Int
  => Reflectable slot0Width Int
  => Reflectable slot1Width Int
  => Add 1 _branchesPred branches
  => WrapMainConfig branches
  -> WrapStatementData
  -> WrapMainAdvice slot0Width slot1Width
  -> Snarky (KimchiConstraint WrapField) t m Unit
wrapMainCircuit config stmt advice = do
  let
    wrapEndo = let Curves.EndoScalar e = Curves.endoScalar @Pallas.BaseField @WrapField in e
    wrapDomainLog2 = config.wrapDomainLog2
    wrapSrsLengthLog2 = config.wrapSrsLengthLog2

    toUnfinalized u =
      { deferredValues: u.deferredValues
      , shouldFinalize: u.shouldFinalize
      , spongeDigestBeforeEvaluations: u.spongeDigestBeforeEvaluations
      }

  -- ======== Block 1: Branch selection + branch_data assert ========
  -- OCaml: One_hot_vector.of_index which_branch' ~length:branches
  whichBranch <- label "block1-one-hot" $
    (Pseudo.oneHotVector :: _ -> _ (Vector branches _)) advice.whichBranch

  -- Pseudo.choose (which_branch, step_widths) ~f:Field.of_int
  firstZero <- label "block1-first-zero" $
    Pseudo.choose whichBranch config.stepWidths
      (\w -> const_ (fromInt w))

  -- ones_vector ~first_zero N2 |> Vector.rev
  { maskVal0, maskVal1 } <- label "block1-ones-vector" do
    let true_ = coerce (const_ one :: FVar WrapField) :: BoolVar WrapField
    eq0 <- equals_ firstZero (const_ zero)
    v0 <- and_ true_ (not_ eq0)
    eq1 <- equals_ firstZero (const_ one)
    v1 <- and_ v0 (not_ eq1)
    pure { maskVal0: v0, maskVal1: v1 }

  -- domain_log2 = Pseudo.choose (which_branch, domain_log2s) ~f:Field.of_int
  domainLog2 <- label "block1-domain-log2" $
    Pseudo.choose whichBranch config.domainLog2s
      (\d -> const_ (fromInt d))

  -- Branch_data.Checked.Wrap.pack + Field.Assert.equal
  label "block1-branch-data-assert" do
    let
      two = fromInt 2 :: WrapField
      four = fromInt 4 :: WrapField
    let twoTimesMask0 = CVar.scale_ two (coerce maskVal0 :: FVar WrapField)
    let packedMask = add_ (coerce maskVal1 :: FVar WrapField) twoTimesMask0
    let fourTimesDom = CVar.scale_ four domainLog2
    let packedBranchData = add_ packedMask fourTimesDom
    assertEqual_ stmt.branchData packedBranchData

  -- ======== Block 2: choose_key + feature flag consistency ========
  chosenVK <- chooseKey whichBranch config.stepKeys
  let
    chosenSigmaCommLast = Vector.index chosenVK.sigmaComm (unsafeFinite @7 6)
    chosenColumnComms =
      { index:
          chosenVK.genericComm :< chosenVK.psmComm :< chosenVK.completeAddComm
            :< chosenVK.mulComm
            :< chosenVK.emulComm
            :< chosenVK.endomulScalarComm
            :< Vector.nil
            :: Vector 6 _
      , coeff: chosenVK.coefficientsComm
      , sigma: Vector.take @6 chosenVK.sigmaComm
      }

  -- ======== Block 3: Compute wrap_domains THEN FOP loop ========
  let
    domainConfig =
      { shifts: LinFFI.domainShifts @WrapField
      , domainGenerator: LinFFI.domainGenerator @WrapField
      }
    fopBaseParams =
      { domainLog2: wrapDomainLog2
      , srsLengthLog2: wrapSrsLengthLog2
      , endo: wrapEndo
      , linearizationPoly: Linearization.vesta
      }

  -- OCaml: Vector.map wrap_domain_indices evaluates right-to-left
  which1 <- label "block3-wrap-domain-1" $
    (Pseudo.oneHotVector :: _ -> _ (Vector 3 _)) advice.wrapDomainIndices.idx1
  domain1 <- Pseudo.toDomain @16 domainConfig which1 config.allPossibleDomainLog2s

  which0 <- label "block3-wrap-domain-0" $
    (Pseudo.oneHotVector :: _ -> _ (Vector 3 _)) advice.wrapDomainIndices.idx0
  domain0 <- Pseudo.toDomain @16 domainConfig which0 config.allPossibleDomainLog2s

  -- FOP proof 0: uses pre-padded slot0 challenges
  { finalized: finalized0, expandedChallenges: expandedChals0 } <- wrapFinalizeOtherProofCircuit
    (Record.merge { domain: { generator: domain0.generator, shifts: domain0.shifts } } fopBaseParams)
    domain0.vanishingPolynomial
    { unfinalized: toUnfinalized advice.prevProofState.unfProof0
    , witness: advice.evals.evals0
    , prevChallenges: advice.paddedChals0
    }
  label "block3-fop-assert-0" do
    assertAny_ [ finalized0, not_ advice.prevProofState.unfProof0.shouldFinalize ]

  -- FOP proof 1: uses pre-padded slot1 challenges
  { finalized: finalized1, expandedChallenges: expandedChals1 } <- wrapFinalizeOtherProofCircuit
    (Record.merge { domain: { generator: domain1.generator, shifts: domain1.shifts } } fopBaseParams)
    domain1.vanishingPolynomial
    { unfinalized: toUnfinalized advice.prevProofState.unfProof1
    , witness: advice.evals.evals1
    , prevChallenges: advice.paddedChals1
    }
  label "block3-fop-assert-1" do
    assertAny_ [ finalized1, not_ advice.prevProofState.unfProof1.shouldFinalize ]

  -- ======== Block 4: Message hash ========
  -- OCaml: Vector.map2 right-to-left → proof 1 first, then proof 0
  -- dummyPaddingSpongeStates: index i = sponge after absorbing (2-i) dummy vectors.
  -- So index = number of REAL vectors provided (0 = all dummies, 2 = no dummies).
  let states = dummyPaddingSpongeStates dummyIpaChallenges.wrapExpanded
  let spongeIdx1 = Vector.length advice.slot1Chals
  msgForWrap1 <- label "block4-msg-hash-1"
    $ evalSpongeM (spongeFromConstants { state: (Vector.index states (unsafeFinite @3 spongeIdx1)).state, spongeState: (Vector.index states (unsafeFinite @3 spongeIdx1)).spongeState })
    $ hashMessagesForNextWrapProofCircuit'
        { sg: advice.prevStepAccs.acc1, allChallenges: advice.slot1Chals }
  let spongeIdx0 = Vector.length advice.slot0Chals
  msgForWrap0 <- label "block4-msg-hash-0"
    $ evalSpongeM (spongeFromConstants { state: (Vector.index states (unsafeFinite @3 spongeIdx0)).state, spongeState: (Vector.index states (unsafeFinite @3 spongeIdx0)).spongeState })
    $ hashMessagesForNextWrapProofCircuit'
        { sg: advice.prevStepAccs.acc0, allChallenges: advice.slot0Chals }

  label "block4-assert-msg-step" $ assertEqual_ stmt.messagesForNextStepProof advice.prevProofState.prevMsgForNextStep

  -- ======== Block 5: pack_statement with split_field ========
  sf0 <- label "block5-split-field-0" $ traverse splitFieldCircuit advice.prevProofState.unfProof0.rawFq
  sf1 <- label "block5-split-field-1" $ traverse splitFieldCircuit advice.prevProofState.unfProof1.rawFq
  let
    mkPerProofTuple unf splitFqs =
      Tuple (map (\sf -> Type2 sf :: Type2 (SplitField (FVar WrapField) (BoolVar WrapField))) splitFqs)
        ( Tuple unf.spongeDigestBeforeEvaluations
            ( Tuple (unf.deferredValues.plonk.beta :< unf.deferredValues.plonk.gamma :< Vector.nil)
                ( Tuple (unf.deferredValues.plonk.alpha :< unf.deferredValues.plonk.zeta :< unf.deferredValues.xi :< Vector.nil)
                    ( Tuple unf.deferredValues.bulletproofChallenges
                        unf.shouldFinalize
                    )
                )
            )
        )

    stmtTuple = Tuple
      (mkPerProofTuple advice.prevProofState.unfProof0 sf0 :< mkPerProofTuple advice.prevProofState.unfProof1 sf1 :< Vector.nil)
      (Tuple advice.prevProofState.prevMsgForNextStep (msgForWrap0 :< msgForWrap1 :< Vector.nil))

    publicInput :: PackedStepPublicInput 2 WrapIPARounds (FVar WrapField) (BoolVar WrapField)
    publicInput = fromPackedTuple stmtTuple

  -- ======== Block 6: wrapVerify (IVP + 4 assertions) ========
  -- Lagrange masking: OCaml masks by EACH branch bool then sums.
  -- For single-domain optimization, the base+correction are Const.
  -- Only CondAdd targets are masked (via maskPt).
  let
    branchBools :: Vector branches (FVar WrapField)
    branchBools = map (coerce :: BoolVar WrapField -> FVar WrapField) whichBranch

    { head: bb0, tail: bbRest } = Vector.uncons branchBools

    maskByBools :: AffinePoint (F WrapField) -> AffinePoint (FVar WrapField)
    maskByBools { x: F x', y: F y' } =
      let
        scaledX0 = CVar.scale_ x' bb0
        scaledY0 = CVar.scale_ y' bb0
        { x: finalX, y: finalY } = foldl
          (\acc b -> { x: CVar.add_ acc.x (CVar.scale_ x' b), y: CVar.add_ acc.y (CVar.scale_ y' b) })
          { x: scaledX0, y: scaledY0 }
          bbRest
      in
        { x: finalX, y: finalY }

    maskedLagrangeComms = map
      (\lb -> { constant: lb.constant, circuit: lb.circuit, maskPt: maskByBools })
      config.lagrangeComms

  let
    ivpParams =
      { curveParams: curveParams (Proxy @VestaG)
      , lagrangeComms: maskedLagrangeComms
      , blindingH: config.blindingH
      , correctionMode: InCircuitCorrections
      , endo: wrapEndo
      , groupMapParams: groupMapParams (Proxy @VestaG)
      , useOptSponge: true
      }

    fullIvpInput =
      { publicInput
      , sgOld: advice.prevStepAccs.acc0 :< advice.prevStepAccs.acc1 :< Vector.nil
      , sgOldMask: coerce maskVal1 :< coerce maskVal0 :< Vector.nil
      , sigmaCommLast: chosenSigmaCommLast
      , columnComms: chosenColumnComms
      , deferredValues:
          { plonk: stmt.plonk
          , combinedInnerProduct: stmt.combinedInnerProduct
          , b: stmt.b
          , xi: stmt.xi
          , bulletproofChallenges: stmt.bulletproofChallenges
          }
      , wComm: advice.messages.wComm
      , zComm: advice.messages.zComm
      , tComm: advice.messages.tComm
      , opening: advice.openingProof
      }

    verifyInput =
      { spongeDigestBeforeEvaluations: stmt.spongeDigestBeforeEvaluations
      , messagesForNextWrapProofDigest: stmt.messagesForNextWrapProofDigest
      , bulletproofChallenges: stmt.bulletproofChallenges
      , newBpChallenges: expandedChals0 :< expandedChals1 :< Vector.nil
      , sg: advice.openingProof.sg
      }

  wrapVerify ivpParams fullIvpInput verifyInput

