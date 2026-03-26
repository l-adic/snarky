module Pickles.CircuitDiffs.PureScript.WrapMain
  ( compileWrapMain
  ) where

-- | Full wrap_main circuit test wrapper.
-- | Parses 401 flat inputs and inlines the wrap_main logic.
-- |
-- | Configuration: single-branch fold, branches=1, step_widths=[1],
-- | Max_proofs_verified=N2, Max_widths_by_slot=[N1,N0], Features.none.
-- |
-- | Input layout (401 fields):
-- |   0-29:    WrapStatement
-- |   30:      which_branch
-- |   31-85:   prev_proof_state (2×27 + 1 = 55)
-- |   86-89:   prev_step_accs (2 points)
-- |   90-104:  old_bp_chals (slot 0: 15 fields)
-- |   105-282: evals (2 × 89 = 178)
-- |   283-284: wrap_domain_indices (2 fields)
-- |   285-354: openings_proof (70 fields)
-- |   355-400: messages (46 fields)

import Prelude

import Data.Fin (getFinite, unsafeFinite)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, dummyVestaPt, unsafeIdx, wrapDomainLog2, wrapEndo, wrapSrsLengthLog2)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.Pseudo as Pseudo
import Record as Record
import Pickles.PackedStatement (PackedStepPublicInput, fromPackedTuple)
import Pickles.PublicInputCommit (CorrectionMode(..))
import Pickles.Sponge (evalSpongeM, spongeFromConstants)
import Pickles.Types (WrapField, WrapIPARounds, StepIPARounds)
import Pickles.Wrap.FinalizeOtherProof (pow2PowMul, wrapFinalizeOtherProofCircuit)
import Pickles.Wrap.MessageHash (dummyPaddingSpongeStates, hashMessagesForNextWrapProofCircuit')
import Pickles.Wrap.Verify (wrapVerify)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import JS.BigInt (fromInt)
import Snarky.Curves.Class (fromBigInt)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, SizedF, Snarky, add_, and_, assertEqual_, assert_, const_, equals_, label, mul_, not_, or_, sub_)
import Snarky.Circuit.Kimchi (SplitField, Type1(..), Type2(..), groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (splitFieldCircuit)
import Type.Proxy (Proxy(..))

type InputSize = 401

-- | Per-proof field layout (27 fields, from composition_types.ml Per_proof.In_circuit.to_data):
-- |   0-4:   fq: cip, b, zetaToSrs, zetaToDom, perm  (5 Type2 fields)
-- |   5:     digest: sponge_digest                      (1 field)
-- |   6-7:   challenge: beta, gamma                     (2 fields)
-- |   8-10:  scalar_challenge: alpha, zeta, xi          (3 fields)
-- |   11-25: bp_chals: WrapIPARounds = 15 fields
-- |   26:    bool: should_finalize                      (1 field)
parseUnfinalizedProof :: (Int -> FVar WrapField) -> Int
  -> { deferredValues ::
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
     -- Raw fq fields for pack_statement (before split_field)
     , rawFq :: Vector 5 (FVar WrapField)
     }
parseUnfinalizedProof at o =
  { deferredValues:
      { plonk:
          { alpha: asSizedF128 (at (o + 8))
          , beta: asSizedF128 (at (o + 6))
          , gamma: asSizedF128 (at (o + 7))
          , zeta: asSizedF128 (at (o + 9))
          , zetaToSrsLength: Type2 (at (o + 2))
          , zetaToDomainSize: Type2 (at (o + 3))
          , perm: Type2 (at (o + 4))
          }
      , combinedInnerProduct: Type2 (at (o + 0))
      , b: Type2 (at (o + 1))
      , xi: asSizedF128 (at (o + 10))
      , bulletproofChallenges: Vector.generate \j -> asSizedF128 (at (o + 11 + getFinite j))
      }
  , shouldFinalize: coerce (at (o + 26)) :: BoolVar WrapField
  , spongeDigestBeforeEvaluations: at (o + 5)
  , rawFq: at (o + 0) :< at (o + 1) :< at (o + 2) :< at (o + 3) :< at (o + 4) :< Vector.nil
  }

wrapMainCircuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => IvpWrapParams
  -> Vector InputSize (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
wrapMainCircuit { lagrangeComms, blindingH } inputs = do
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
    constDummyPt = let { x: F x', y: F y' } = dummyVestaPt in { x: const_ x', y: const_ y' }

    -- ---- 1. WrapStatement (positions 0-29) ----
    plonk =
      { alpha: asSizedF128 (at 0)
      , beta: asSizedF128 (at 1)
      , gamma: asSizedF128 (at 2)
      , zeta: asSizedF128 (at 3)
      , perm: Type1 (at 4)
      , zetaToSrsLength: Type1 (at 5)
      , zetaToDomainSize: Type1 (at 6)
      }
    xi = asSizedF128 (at 7)
    combinedInnerProduct = Type1 (at 8)
    b_ = Type1 (at 9)
    _branchData = at 10
    bulletproofChallenges :: Vector StepIPARounds (SizedF 128 (FVar WrapField))
    bulletproofChallenges = Vector.generate \j -> asSizedF128 (at (11 + getFinite j))
    spongeDigestBeforeEvaluations = at 27
    messagesForNextWrapProofDigest = at 28
    messagesForNextStepProof = at 29

    -- ---- 2. which_branch (position 30) ----
    _whichBranch = at 30

    -- ---- 3. prev_proof_state (positions 31-85, 55 fields) ----
    unfProof0 = parseUnfinalizedProof at 31
    unfProof1 = parseUnfinalizedProof at 58
    prevMsgForNextStep = at 85

    -- ---- 4. prev_step_accs (positions 86-89) ----
    prevStepAcc0 = readPt 86
    prevStepAcc1 = readPt 88

    -- ---- 5. old_bp_chals (positions 90-104, 15 fields) ----
    oldBpChals0 :: Vector WrapIPARounds (FVar WrapField)
    oldBpChals0 = Vector.generate \j -> at (90 + getFinite j)

    -- ---- 6. evals (positions 105-282, 2 × 89 = 178 fields) ----
    parseEvals base =
      let ep b i = { zeta: at (b + 2 * i), omegaTimesZeta: at (b + 2 * i + 1) }
      in
        { allEvals:
            { ftEval1: at (base + 88)
            , publicEvals: { zeta: at base, omegaTimesZeta: at (base + 1) }
            , witnessEvals: Vector.generate \j -> ep (base + 2) (getFinite j)
            , coeffEvals: Vector.generate \j -> ep (base + 32) (getFinite j)
            , zEvals: { zeta: at (base + 62), omegaTimesZeta: at (base + 63) }
            , sigmaEvals: Vector.generate \j -> ep (base + 64) (getFinite j)
            , indexEvals: Vector.generate \j -> ep (base + 76) (getFinite j)
            }
        }
    evals0 = parseEvals 105
    evals1 = parseEvals 194

    -- ---- 7. wrap_domain_indices (positions 283-284) ----
    _wrapDomainIdx0 = at 283
    _wrapDomainIdx1 = at 284

    -- ---- 8. openings_proof (positions 285-354, 70 fields) ----
    openingProof =
      { delta: readPt 285
      , sg: readPt 287
      , lr: (Vector.generate \j ->
              { l: readPt (289 + 4 * getFinite j)
              , r: readPt (289 + 4 * getFinite j + 2)
              }) :: Vector StepIPARounds _
      , z1: Type1 (at 353)
      , z2: Type1 (at 354)
      }

    -- ---- 9. messages (positions 355-400, 46 fields) ----
    wComm :: Vector 15 (AffinePoint (FVar WrapField))
    wComm = Vector.generate \j -> readPt (355 + 2 * getFinite j)
    zComm = readPt 385
    tComm :: Vector 7 (AffinePoint (FVar WrapField))
    tComm = Vector.generate \j -> readPt (387 + 2 * getFinite j)

    -- ---- FOP base params (domain computed dynamically per proof) ----
    -- all_possible_domains = [Pow_2_roots_of_unity 13, 14, 15]
    -- num_possible_domains = 3 (= S(Padded_length) = S(N2))
    allPossibleLog2s = 13 :< 14 :< 15 :< Vector.nil :: Vector 3 Int
    fopBaseParams =
      { domainLog2: wrapDomainLog2  -- TODO: this is still compile-time, used for pow2pow
      , srsLengthLog2: wrapSrsLengthLog2
      , endo: wrapEndo
      , linearizationPoly: Linearization.vesta
      }

  -- ======== Circuit blocks ========

  -- Block 1: Branch selection + branch_data assert
  whichBranchBool <- label "block1-which-branch" do
    b <- equals_ _whichBranch (const_ zero)
    assert_ b
    pure b

  { maskVal0, maskVal1 } <- label "block1-ones-vector" do
    let firstZero = const_ one :: FVar WrapField
    eq0 <- equals_ firstZero (const_ zero)
    let notEq0 = not_ eq0
    v0 <- and_ whichBranchBool notEq0
    eq1 <- equals_ firstZero (const_ one)
    let notEq1 = not_ eq1
    v1 <- and_ v0 notEq1
    pure { maskVal0: v0, maskVal1: v1 }

  label "block1-branch-data-pack" do
    let sixteen = one + one + one + one + one + one + one + one + one + one + one + one + one + one + one + one :: WrapField
        domainLog2 = const_ sixteen :: FVar WrapField
        four = one + one + one + one :: WrapField
        two = one + one :: WrapField
    twoTimesMask0 <- mul_ (const_ two) (coerce maskVal0 :: FVar WrapField)
    let packedMask = add_ (coerce maskVal1 :: FVar WrapField) twoTimesMask0
    fourTimesDom <- mul_ (const_ four) domainLog2
    let packedBranchData = add_ packedMask fourTimesDom
    assertEqual_ _branchData packedBranchData

  -- Block 2: Feature flag consistency
  -- For Features.none: all flags are constant false_, all comms are Opt.Nothing.
  -- expand_feature_flags with all false_ → all expanded flags are false_ (no constraints).
  -- Each assert_consistent Opt.Nothing (lazy false_) → Boolean.Assert.= false_ false_.
  -- 15 assertions of constant equality → may or may not generate constraints depending on impl.
  -- OCaml Boolean.Assert.= with two constants generates an R1CS checking 0 = 0.
  -- In PureScript, assertEqual_ on constants also generates constraints.
  -- TODO: determine if these generate constraints or are optimized away.
  -- For now, attempt the 15 assertions:
  let ff = coerce (const_ zero :: FVar WrapField) :: BoolVar WrapField  -- false_
  -- The OCaml generates constraints from assert_consistent for each optional commitment.
  -- Each call is: Boolean.Assert.= (commitment_flag Opt.Nothing) (Lazy.force flag)
  --            = Boolean.Assert.= false_ false_
  -- This is: assert_ (equals_ false_ false_) which is trivially true for constants.
  -- But the OCaml DOES generate R1CS here because the values flow through non-constant paths
  -- (choose_key makes the VK non-constant even for single branch).
  -- We skip this for now — the VK is constant in our dump, so the flags may differ.

  -- Block 3: Compute wrap_domains + FOP loop (2 proofs)
  -- For each proof, compute domain from wrap_domain_index via one-hot selection
  -- then run FOP with that domain.
  -- Reference: wrap_main.ml:418-485
  let toUnfinalized u = { deferredValues: u.deferredValues, shouldFinalize: u.shouldFinalize, spongeDigestBeforeEvaluations: u.spongeDigestBeforeEvaluations }

  -- Block 3: FOP proof 0 — domain + finalize
  which0 <- label "block3-wrap-domain-0" do
    w <- (Pseudo.oneHotVector :: _ -> _ (Vector 3 _)) _wrapDomainIdx0
    pure w
  gen0 <- label "block3-wrap-domain-gen-0" $
    Pseudo.choose which0 allPossibleLog2s (\log2 -> const_ (LinFFI.domainGenerator @WrapField log2))
  let shifts0 = map const_ (LinFFI.domainShifts @WrapField 15)
  let vanishingPoly z = do
        zetaToN <- pow2PowMul z wrapDomainLog2
        pure (zetaToN `sub_` const_ one)
  { finalized: finalized0, expandedChallenges: expandedChals0 } <- wrapFinalizeOtherProofCircuit
    (Record.merge { domain: { generator: gen0, shifts: shifts0 } } fopBaseParams)
    vanishingPoly
    { unfinalized: toUnfinalized unfProof0
    , witness: evals0
    , prevChallenges: oldBpChals0 :< Vector.nil
    }
  label "block3-fop-assert-0" do
    finalizedOrNot0 <- or_ finalized0 (not_ unfProof0.shouldFinalize)
    assert_ finalizedOrNot0

  -- Block 3: FOP proof 1 — domain + finalize
  which1 <- label "block3-wrap-domain-1" do
    w <- (Pseudo.oneHotVector :: _ -> _ (Vector 3 _)) _wrapDomainIdx1
    pure w
  gen1 <- label "block3-wrap-domain-gen-1" $
    Pseudo.choose which1 allPossibleLog2s (\log2 -> const_ (LinFFI.domainGenerator @WrapField log2))
  let shifts1 = map const_ (LinFFI.domainShifts @WrapField 15)
  { finalized: finalized1, expandedChallenges: expandedChals1 } <- wrapFinalizeOtherProofCircuit
    (Record.merge { domain: { generator: gen1, shifts: shifts1 } } fopBaseParams)
    vanishingPoly
    { unfinalized: toUnfinalized unfProof1
    , witness: evals1
    , prevChallenges: Vector.nil
    }
  label "block3-fop-assert-1" do
    finalizedOrNot1 <- or_ finalized1 (not_ unfProof1.shouldFinalize)
    assert_ finalizedOrNot1

  -- Block 4: prev_statement construction + messages_for_next_step_proof assert
  let states = dummyPaddingSpongeStates dummyIpaChallenges.wrapExpanded
  msgForWrap0 <- label "block4-msg-hash-0" $
    evalSpongeM (spongeFromConstants { state: (Vector.index states (unsafeFinite 1)).state, spongeState: (Vector.index states (unsafeFinite 1)).spongeState }) $
      hashMessagesForNextWrapProofCircuit'
        { sg: prevStepAcc0, allChallenges: oldBpChals0 :< Vector.nil }
  msgForWrap1 <- label "block4-msg-hash-1" $
    evalSpongeM (spongeFromConstants { state: (Vector.index states (unsafeFinite 0)).state, spongeState: (Vector.index states (unsafeFinite 0)).spongeState }) $
      hashMessagesForNextWrapProofCircuit'
        { sg: prevStepAcc1, allChallenges: Vector.nil :: Vector 0 (Vector WrapIPARounds (FVar WrapField)) }

  label "block4-assert-msg-step" $ assertEqual_ messagesForNextStepProof prevMsgForNextStep

  -- Block 5: pack_statement with split_field
  sf0 <- label "block5-split-field-0" $ traverse splitFieldCircuit unfProof0.rawFq
  sf1 <- label "block5-split-field-1" $ traverse splitFieldCircuit unfProof1.rawFq
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
      (mkPerProofTuple unfProof0 sf0 :< mkPerProofTuple unfProof1 sf1 :< Vector.nil)
      (Tuple prevMsgForNextStep (msgForWrap0 :< msgForWrap1 :< Vector.nil))

    publicInput :: PackedStepPublicInput 2 WrapIPARounds (FVar WrapField) (BoolVar WrapField)
    publicInput = fromPackedTuple stmtTuple

  -- Block 6: wrapVerify (IVP + 4 assertions)
  let
    ivpParams =
      { curveParams: curveParams (Proxy @VestaG)
      , lagrangeComms
      , blindingH
      , correctionMode: InCircuitCorrections
      , endo: wrapEndo
      , groupMapParams: groupMapParams (Proxy @VestaG)
      , useOptSponge: true
      }

    fullIvpInput =
      { publicInput
      , sgOld: prevStepAcc0 :< prevStepAcc1 :< Vector.nil
      , sigmaCommLast: constDummyPt
      , columnComms:
          { index: (Vector.replicate constDummyPt) :: Vector 6 _
          , coeff: (Vector.replicate constDummyPt) :: Vector 15 _
          , sigma: (Vector.replicate constDummyPt) :: Vector 6 _
          }
      , deferredValues:
          { plonk
          , combinedInnerProduct
          , b: b_
          , xi
          , bulletproofChallenges
          }
      , wComm
      , zComm
      , tComm
      , opening: openingProof
      }

    verifyInput =
      { spongeDigestBeforeEvaluations
      , messagesForNextWrapProofDigest
      , bulletproofChallenges
      , newBpChallenges: expandedChals0 :< expandedChals1 :< Vector.nil
      , sg: openingProof.sg
      }

  wrapVerify ivpParams fullIvpInput verifyInput

compileWrapMain :: IvpWrapParams -> CompiledCircuit WrapField
compileWrapMain srsData =
  compilePure (Proxy @(Vector InputSize (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> wrapMainCircuit srsData inputs)
    Kimchi.initialState
