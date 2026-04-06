module Pickles.CircuitDiffs.PureScript.WrapMainN2
  ( compileWrapMainN2
  ) where

-- | Full wrap_main circuit test wrapper — N2 specialization.
-- |
-- | This is the N2 case: 2 branches (base+merge IVC pattern).
-- | branches=2, step_widths=[0,2], Max_widths_by_slot=[N2,N1].
-- | Slot 0 carries 2 real proofs' challenges, slot 1 carries 1.
-- |
-- | Input layout (431 fields):
-- |   0-29:    WrapStatement
-- |   30:      which_branch
-- |   31-85:   prev_proof_state (2×27 + 1 = 55)
-- |   86-89:   prev_step_accs (2 points)
-- |   90-134:  old_bp_chals (slot 0: 2×15 + slot 1: 1×15 = 45 fields)
-- |   135-312: evals (2 × 89 = 178)
-- |   313-314: wrap_domain_indices (2 fields)
-- |   315-384: openings_proof (70 fields)
-- |   385-430: messages (46 fields)

import Prelude

import Data.Fin (getFinite, unsafeFinite)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Foldable (foldl)
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, dummyVestaPt, unsafeIdx, wrapDomainLog2, wrapEndo, wrapSrsLengthLog2)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpWrapParams)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PackedStatement (PackedStepPublicInput, fromPackedTuple)
import Pickles.Pseudo as Pseudo
import Pickles.PublicInputCommit (CorrectionMode(..))
import Pickles.Sponge (evalSpongeM, spongeFromConstants)
import Pickles.Types (StepIPARounds, WrapField, WrapIPARounds)
import Pickles.VerificationKey (chooseKey)
import Pickles.Wrap.FinalizeOtherProof (wrapFinalizeOtherProofCircuit)
import Pickles.Wrap.MessageHash (dummyPaddingSpongeStates, hashMessagesForNextWrapProofCircuit')
import Pickles.Wrap.Verify (wrapVerify)
import Record as Record
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, SizedF, Snarky, add_, and_, assertAny_, assertEqual_, const_, equals_, label, not_)
import Snarky.Circuit.Kimchi (SplitField, Type1(..), Type2(..), groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams, fromInt)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (splitFieldCircuit)
import Type.Proxy (Proxy(..))

type InputSize = 431

-- | Per-proof field layout (27 fields) — same as N1
parseUnfinalizedProof
  :: (Int -> FVar WrapField)
  -> Int
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

wrapMainN2Circuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => IvpWrapParams
  -> Vector InputSize (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
wrapMainN2Circuit { lagrangeComms, blindingH } inputs = do
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }

    -- ---- 1. WrapStatement (positions 0-29) — same as N1 ----
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

    -- ---- 3. prev_proof_state (positions 31-85, 55 fields) — same as N1 ----
    unfProof0 = parseUnfinalizedProof at 31
    unfProof1 = parseUnfinalizedProof at 58
    prevMsgForNextStep = at 85

    -- ---- 4. prev_step_accs (positions 86-89) — same as N1 ----
    prevStepAcc0 = readPt 86
    prevStepAcc1 = readPt 88

    -- ---- 5. old_bp_chals (positions 90-134, 45 fields) ----
    -- N2: Max_widths_by_slot=[N2,N1]
    -- Slot 0: 2 vectors of 15 = 30 fields (positions 90-119)
    -- Slot 1: 1 vector of 15 = 15 fields (positions 120-134)
    oldBpChals0a :: Vector WrapIPARounds (FVar WrapField)
    oldBpChals0a = Vector.generate \j -> at (90 + getFinite j)
    oldBpChals0b :: Vector WrapIPARounds (FVar WrapField)
    oldBpChals0b = Vector.generate \j -> at (105 + getFinite j)
    oldBpChals1 :: Vector WrapIPARounds (FVar WrapField)
    oldBpChals1 = Vector.generate \j -> at (120 + getFinite j)

    -- ---- 6. evals (positions 135-312, 2 × 89 = 178 fields) ----
    parseEvals base =
      let
        ep b i = { zeta: at (b + 2 * i), omegaTimesZeta: at (b + 2 * i + 1) }
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
    evals0 = parseEvals 135
    evals1 = parseEvals 224

    -- ---- 7. wrap_domain_indices (positions 313-314) ----
    _wrapDomainIdx0 = at 313
    _wrapDomainIdx1 = at 314

    -- ---- 8. openings_proof (positions 315-384, 70 fields) ----
    -- OCaml hlist order: lr(64), z1(1), z2(1), delta(2), sg(2)
    openingProof =
      { lr:
          ( Vector.generate \j ->
              { l: readPt (315 + 4 * getFinite j)
              , r: readPt (315 + 4 * getFinite j + 2)
              }
          ) :: Vector StepIPARounds _
      , z1: Type1 (at 379)
      , z2: Type1 (at 380)
      , delta: readPt 381
      , sg: readPt 383
      }

    -- ---- 9. messages (positions 385-430, 46 fields) ----
    wComm :: Vector 15 (AffinePoint (FVar WrapField))
    wComm = Vector.generate \j -> readPt (385 + 2 * getFinite j)
    zComm = readPt 415

    tComm :: Vector 7 (AffinePoint (FVar WrapField))
    tComm = Vector.generate \j -> readPt (417 + 2 * getFinite j)

    -- ---- FOP base params ----
    allPossibleLog2s = unsafeFinite @16 13 :< unsafeFinite @16 14 :< unsafeFinite @16 15 :< Vector.nil
    fopBaseParams =
      { domainLog2: wrapDomainLog2
      , srsLengthLog2: wrapSrsLengthLog2
      , endo: wrapEndo
      , linearizationPoly: Linearization.vesta
      }

    dummyWrapChals :: Vector WrapIPARounds (FVar WrapField)
    dummyWrapChals = map const_ dummyIpaChallenges.wrapExpanded

  -- ======== Circuit blocks ========

  -- Block 1: Branch selection + branch_data assert
  -- N2: branches=2, step_widths=[0,2]
  whichBranch <- label "block1-one-hot" $
    (Pseudo.oneHotVector :: _ -> _ (Vector 2 _)) _whichBranch

  firstZero <- label "block1-first-zero" $
    Pseudo.choose whichBranch (0 :< 2 :< Vector.nil :: Vector 2 Int)
      (\w -> const_ (fromInt w))

  { maskVal0, maskVal1 } <- label "block1-ones-vector" do
    let true_ = coerce (const_ one :: FVar WrapField) :: BoolVar WrapField
    eq0 <- equals_ firstZero (const_ zero)
    v0 <- and_ true_ (not_ eq0)
    eq1 <- equals_ firstZero (const_ one)
    v1 <- and_ v0 (not_ eq1)
    pure { maskVal0: v0, maskVal1: v1 }

  -- N2: Pseudo.choose over 2 domains (both 16)
  domainLog2 <- label "block1-domain-log2" $
    Pseudo.choose whichBranch (16 :< 16 :< Vector.nil :: Vector 2 Int)
      (\d -> const_ (fromInt d))

  label "block1-branch-data-assert" do
    let
      two = fromInt 2 :: WrapField
      four = fromInt 4 :: WrapField
    let twoTimesMask0 = CVar.scale_ two (coerce maskVal0 :: FVar WrapField)
    let packedMask = add_ (coerce maskVal1 :: FVar WrapField) twoTimesMask0
    let fourTimesDom = CVar.scale_ four domainLog2
    let packedBranchData = add_ packedMask fourTimesDom
    assertEqual_ _branchData packedBranchData

  -- Block 2: choose_key — N2: 2 VKs
  let
    { x: F dummyX, y: F dummyY } = dummyVestaPt
    dummyPt = { x: const_ dummyX, y: const_ dummyY } :: AffinePoint (FVar WrapField)
    dummyVK =
      { sigmaComm: Vector.replicate dummyPt :: Vector 7 _
      , coefficientsComm: Vector.replicate dummyPt :: Vector 15 _
      , genericComm: dummyPt
      , psmComm: dummyPt
      , completeAddComm: dummyPt
      , mulComm: dummyPt
      , emulComm: dummyPt
      , endomulScalarComm: dummyPt
      }
  chosenVK <- chooseKey whichBranch (dummyVK :< dummyVK :< Vector.nil)
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

  -- Block 3: Compute wrap_domains THEN FOP loop
  let toUnfinalized u = { deferredValues: u.deferredValues, shouldFinalize: u.shouldFinalize, spongeDigestBeforeEvaluations: u.spongeDigestBeforeEvaluations }

  let
    domainConfig =
      { shifts: LinFFI.domainShifts @WrapField
      , domainGenerator: LinFFI.domainGenerator @WrapField
      }

  which1 <- label "block3-wrap-domain-1" $
    (Pseudo.oneHotVector :: _ -> _ (Vector 3 _)) _wrapDomainIdx1
  domain1 <- Pseudo.toDomain @16 domainConfig which1 allPossibleLog2s

  which0 <- label "block3-wrap-domain-0" $
    (Pseudo.oneHotVector :: _ -> _ (Vector 3 _)) _wrapDomainIdx0
  domain0 <- Pseudo.toDomain @16 domainConfig which0 allPossibleLog2s

  -- FOP proof 0
  -- N2: slot 0 has 2 real challenge vectors → no dummy padding needed
  { finalized: finalized0, expandedChallenges: expandedChals0 } <- wrapFinalizeOtherProofCircuit
    (Record.merge { domain: { generator: domain0.generator, shifts: domain0.shifts } } fopBaseParams)
    domain0.vanishingPolynomial
    { unfinalized: toUnfinalized unfProof0
    , witness: evals0
    , prevChallenges: oldBpChals0a :< oldBpChals0b :< Vector.nil
    }
  label "block3-fop-assert-0" do
    assertAny_ [ finalized0, not_ unfProof0.shouldFinalize ]

  -- FOP proof 1
  -- N2: slot 1 has 1 real challenge vector → pad with 1 dummy
  { finalized: finalized1, expandedChallenges: expandedChals1 } <- wrapFinalizeOtherProofCircuit
    (Record.merge { domain: { generator: domain1.generator, shifts: domain1.shifts } } fopBaseParams)
    domain1.vanishingPolynomial
    { unfinalized: toUnfinalized unfProof1
    , witness: evals1
    , prevChallenges: dummyWrapChals :< oldBpChals1 :< Vector.nil
    }
  label "block3-fop-assert-1" do
    assertAny_ [ finalized1, not_ unfProof1.shouldFinalize ]

  -- Block 4: prev_statement + messages_for_next_step_proof assert
  -- OCaml: Vector.map2 right-to-left → proof 1 first, then proof 0
  let states = dummyPaddingSpongeStates dummyIpaChallenges.wrapExpanded
  -- N2: proof 1 has 1 real challenge vector → 1 dummy absorbed → index 1
  msgForWrap1 <- label "block4-msg-hash-1"
    $ evalSpongeM (spongeFromConstants { state: (Vector.index states (unsafeFinite @3 1)).state, spongeState: (Vector.index states (unsafeFinite @3 1)).spongeState })
    $
      hashMessagesForNextWrapProofCircuit'
        { sg: prevStepAcc1, allChallenges: oldBpChals1 :< Vector.nil }
  -- N2: proof 0 has 2 real challenge vectors → 0 dummies absorbed → index 2
  msgForWrap0 <- label "block4-msg-hash-0"
    $ evalSpongeM (spongeFromConstants { state: (Vector.index states (unsafeFinite @3 2)).state, spongeState: (Vector.index states (unsafeFinite @3 2)).spongeState })
    $
      hashMessagesForNextWrapProofCircuit'
        { sg: prevStepAcc0, allChallenges: oldBpChals0a :< oldBpChals0b :< Vector.nil }

  label "block4-assert-msg-step" $ assertEqual_ messagesForNextStepProof prevMsgForNextStep

  -- Block 5: pack_statement with split_field — same as N1
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

  -- Block 6: wrapVerify (IVP + 4 assertions) — same structure as N1
  let
    -- N2: OCaml's lagrange masks by EACH branch bool then sums:
    -- Vector.map2 which_branch ~f:(fun b -> Scale(coord, b))
    -- |> Vector.reduce_exn ~f:Field.(+)
    -- For 2 branches with same domain: result = Scale(coord, b0) + Scale(coord, b1) = Scale(coord, b0+b1)
    -- We use Add(Scale(coord, b0), Scale(coord, b1)) to match the CVar structure.
    { head: branchBool0, tail: branchBoolRest } = Vector.uncons (map (coerce :: BoolVar WrapField -> FVar WrapField) whichBranch)

    maskByBools :: AffinePoint (F WrapField) -> AffinePoint (FVar WrapField)
    maskByBools { x: F x', y: F y' } =
      let
        scaledX0 = CVar.scale_ x' branchBool0
        scaledY0 = CVar.scale_ y' branchBool0
        -- Sum across all branches (for single-domain, all branches produce same coord)
        { x: finalX, y: finalY } = foldl
          (\acc b -> { x: add_ acc.x (CVar.scale_ x' b), y: add_ acc.y (CVar.scale_ y' b) })
          { x: scaledX0, y: scaledY0 }
          branchBoolRest
      in { x: finalX, y: finalY }
    maskedLagrangeComms = map
      ( \lb ->
          { constant: lb.constant, circuit: lb.circuit, maskPt: maskByBools }
      )
      lagrangeComms
  let
    ivpParams =
      { curveParams: curveParams (Proxy @VestaG)
      , lagrangeComms: maskedLagrangeComms
      , blindingH
      , correctionMode: InCircuitCorrections
      , endo: wrapEndo
      , groupMapParams: groupMapParams (Proxy @VestaG)
      , useOptSponge: true
      }

    fullIvpInput =
      { publicInput
      , sgOld: prevStepAcc0 :< prevStepAcc1 :< Vector.nil
      , sgOldMask: coerce maskVal1 :< coerce maskVal0 :< Vector.nil
      , sigmaCommLast: chosenSigmaCommLast
      , columnComms: chosenColumnComms
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

compileWrapMainN2 :: IvpWrapParams -> CompiledCircuit WrapField
compileWrapMainN2 srsData =
  compilePure (Proxy @(Vector InputSize (F WrapField))) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (\inputs -> wrapMainN2Circuit srsData inputs)
    Kimchi.initialState
