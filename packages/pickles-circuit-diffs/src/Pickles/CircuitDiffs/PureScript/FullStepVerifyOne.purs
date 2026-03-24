module Pickles.CircuitDiffs.PureScript.FullStepVerifyOne
  ( compileFullStepVerifyOne
  , FullStepVerifyOneParams
  ) where

-- | Full step_main.verify_one circuit: FOP + message_hash + IVP + assertions.
-- |
-- | Matches OCaml's Step_main.Make(Inductive_rule.Kimchi).verify_one with:
-- |   - Per_proof_witness.typ Field.typ Nat.N1.n (self-recursive, Field app_state)
-- |   - max_proofs_verified = N1
-- |   - wrap_domain = Pow_2_roots_of_unity 14
-- |   - feature_flags = none, num_chunks = 1, zk_rows = 3
-- |
-- | Input layout (286 fields):
-- |   0:        app_state (Field.typ)
-- |   1-114:    wrap_proof (114 fields: w_comm, z_comm, t_comm, lr, z1, z2, delta, sg)
-- |   115-144:  proof_state (30 fields: plonk, cip, b, xi, bp_chals, branch_data, digest, msg_wrap=unit)
-- |   145-233:  prev_proof_evals (89 fields: All_evals)
-- |   234-249:  prev_challenges (Vector N1 (Vector 16 Field.t))
-- |   250-251:  prev_challenge_polynomial_commitments (Vector N1 (curve point))
-- |   252-283:  unfinalized (32 fields: Step.Per_proof via Typ)
-- |   284:      messages_for_next_wrap_proof
-- |   285:      must_verify
-- |
-- | Reference: step_main.ml:17-117 (verify_one)

import Prelude

import Data.Foldable (foldM, for_)
import Data.Fin (getFinite)
import Data.Fin as Fin
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, asSizedF10, dummyPallasPt, dummyWrapSg, stepEndo, unsafeIdx)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.OptSponge as OptSponge
import Pickles.PublicInputCommit (CorrectionMode(..))
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.FinalizeOtherProof (finalizeOtherProofCircuit)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Types (StepField)
import Pickles.Verify (incrementallyVerifyProof)
import Snarky.Circuit.RandomOracle.Sponge as Sponge
import Snarky.Circuit.RandomOracle.Sponge (Sponge)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, and_, assertEq, assert_, const_, if_, label, not_, or_)
import Snarky.Circuit.Kimchi (SplitField(..), Type1(..), Type2(..), groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type FullStepVerifyOneParams =
  { lagrangeComms :: Array (AffinePoint (F StepField))
  , blindingH :: AffinePoint (F StepField)
  }

fullStepVerifyOneCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => FullStepVerifyOneParams
  -> Vector 286 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
fullStepVerifyOneCircuit { lagrangeComms, blindingH } inputs = do
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
    readOtherField i = Type2 (SplitField { sDiv2: at i, sOdd: coerce (at (i + 1)) })

    constDummyPt = let { x: F x', y: F y' } = dummyPallasPt in { x: const_ x', y: const_ y' }
    constDummySg :: AffinePoint (FVar StepField)
    constDummySg = { x: const_ dummyWrapSg.x, y: const_ dummyWrapSg.y }

    -- Offsets: app_state shifts everything by 1 compared to step_verify_circuit
    o = 1 -- offset for app_state

    ---------------------------------------------------------------------------
    -- app_state (position 0)
    ---------------------------------------------------------------------------
    appState = at 0

    ---------------------------------------------------------------------------
    -- Parse wrap_proof (positions 1-114)
    ---------------------------------------------------------------------------
    wComm :: Vector 15 (AffinePoint (FVar StepField))
    wComm = Vector.generate \j -> readPt (o + 2 * getFinite j)

    zComm = readPt (o + 30)

    tComm :: Vector 7 (AffinePoint (FVar StepField))
    tComm = Vector.generate \j -> readPt (o + 32 + 2 * getFinite j)

    lr :: Vector 15 { l :: AffinePoint (FVar StepField), r :: AffinePoint (FVar StepField) }
    lr = Vector.generate \j ->
      { l: readPt (o + 46 + 4 * getFinite j)
      , r: readPt (o + 46 + 4 * getFinite j + 2)
      }

    z1 = readOtherField (o + 106)
    z2 = readOtherField (o + 108)
    delta = readPt (o + 110)
    sg = readPt (o + 112)

    ---------------------------------------------------------------------------
    -- Parse proof_state (positions 115-144)
    ---------------------------------------------------------------------------
    proofStateBase = o + 114

    -- Plonk: alpha(0), beta(1), gamma(2), zeta(3), zetaToSrs(4), zetaToDom(5), perm(6)
    plonkAlpha = asSizedF128 (at proofStateBase)
    plonkBeta = asSizedF128 (at (proofStateBase + 1))
    plonkGamma = asSizedF128 (at (proofStateBase + 2))
    plonkZeta = asSizedF128 (at (proofStateBase + 3))
    plonkZetaToSrsLength = Type1 (at (proofStateBase + 4))
    plonkZetaToDomainSize = Type1 (at (proofStateBase + 5))
    plonkPerm = Type1 (at (proofStateBase + 6))

    -- CIP(7), B(8), Xi(9)
    combinedInnerProduct = Type1 (at (proofStateBase + 7))
    b_val = Type1 (at (proofStateBase + 8))
    xi = asSizedF128 (at (proofStateBase + 9))

    -- Bulletproof challenges (10-25)
    bpChallenges :: Vector 16 _
    bpChallenges = Vector.generate \j -> asSizedF128 (at (proofStateBase + 10 + getFinite j))

    -- Branch_data: mask0(26), mask1(27), domain_log2(28)
    mask0 = at (proofStateBase + 26)
    mask1 = at (proofStateBase + 27)
    domainLog2Var = at (proofStateBase + 28)

    -- Sponge digest (29)
    spongeDigest = at (proofStateBase + 29)

    ---------------------------------------------------------------------------
    -- Parse prev_proof_evals (positions 145-233)
    ---------------------------------------------------------------------------
    evalsBase = o + 144

    evalPair :: forall n. Int -> Fin.Finite n -> { zeta :: FVar StepField, omegaTimesZeta :: FVar StepField }
    evalPair base j =
      { zeta: at (base + 2 * Fin.getFinite j)
      , omegaTimesZeta: at (base + 2 * Fin.getFinite j + 1)
      }

    allEvals =
      { ftEval1: at (evalsBase + 88)
      , publicEvals: { zeta: at evalsBase, omegaTimesZeta: at (evalsBase + 1) }
      , witnessEvals: (Vector.generate (evalPair (evalsBase + 2))) :: Vector 15 _
      , coeffEvals: (Vector.generate (evalPair (evalsBase + 32))) :: Vector 15 _
      , zEvals: { zeta: at (evalsBase + 62), omegaTimesZeta: at (evalsBase + 63) }
      , sigmaEvals: (Vector.generate (evalPair (evalsBase + 64))) :: Vector 6 _
      , indexEvals: (Vector.generate (evalPair (evalsBase + 76))) :: Vector 6 _
      }

    ---------------------------------------------------------------------------
    -- Parse prev_challenges (234-249) and prev_challenge_polynomial_commitments (250-251)
    ---------------------------------------------------------------------------
    prevChallengesBase = 234
    prevChallenges :: Vector 1 (Vector 16 (FVar StepField))
    prevChallenges = (\x -> x :< Vector.nil) (Vector.generate \j -> at (prevChallengesBase + getFinite j))

    prevSg = readPt 250

    ---------------------------------------------------------------------------
    -- Parse unfinalized (positions 252-283)
    ---------------------------------------------------------------------------
    unfBase = 252
    -- OCaml Unfinalized.typ / Per_proof.In_circuit.spec layout:
    --   0-1: cip, 2-3: b, 4-5: zetaToSrs, 6-7: zetaToDom, 8-9: perm (5×fq = 10 fields)
    --   10: sponge_digest (1 digest field)
    --   11: beta, 12: gamma (2 challenge fields)
    --   13: alpha, 14: zeta, 15: xi (3 scalar_challenge fields)
    --   16-30: bulletproof_challenges (15 fields)
    --   31: should_finalize (1 bool field)
    unfDeferredValues =
      { plonk:
          { alpha: asSizedF128 (at (unfBase + 13))
          , beta: asSizedF128 (at (unfBase + 11))
          , gamma: asSizedF128 (at (unfBase + 12))
          , zeta: asSizedF128 (at (unfBase + 14))
          , perm: readOtherField (unfBase + 8)
          , zetaToSrsLength: readOtherField (unfBase + 4)
          , zetaToDomainSize: readOtherField (unfBase + 6)
          }
      , combinedInnerProduct: readOtherField (unfBase + 0)
      , b: readOtherField (unfBase + 2)
      , xi: asSizedF128 (at (unfBase + 15))
      , bulletproofChallenges:
          (Vector.generate \j -> asSizedF128 (at (unfBase + 16 + getFinite j))) :: Vector 15 _
      }
    unfShouldFinalize = coerce (at (unfBase + 31)) :: BoolVar StepField
    unfClaimedDigest = at (unfBase + 10)

    ---------------------------------------------------------------------------
    -- Extra inputs
    ---------------------------------------------------------------------------
    messagesForNextWrapProof = at 284
    mustVerify = coerce (at 285) :: BoolVar StepField

    ---------------------------------------------------------------------------
    -- FOP params (compile-time constants)
    ---------------------------------------------------------------------------
    domainLog2 = 16
    fopParams =
      { domain:
          { generator: LinFFI.domainGenerator @StepField domainLog2
          , shifts: LinFFI.domainShifts @StepField domainLog2
          }
      , domainLog2
      , srsLengthLog2: 16
      , endo: stepEndo
      , linearizationPoly: Linearization.pallas
      }

    -- N1: trim_front [mask0, mask1] with lte N1 N2 → [mask1]
    mask :: Vector 1 (BoolVar StepField)
    mask = (coerce mask1 :: BoolVar StepField) :< Vector.nil

  ---------------------------------------------------------------------------
  -- Step 1: assert should_finalize == must_verify (step_main.ml:28)
  ---------------------------------------------------------------------------
  label "step1_assert_finalize" $ assertEq unfShouldFinalize mustVerify

  ---------------------------------------------------------------------------
  -- Step 2: FOP (step_main.ml:61-73)
  ---------------------------------------------------------------------------
  { finalized, challenges } <- label "step2_fop" $ finalizeOtherProofCircuit StepOtherField.fopShiftOps fopParams
    { unfinalized:
        { deferredValues:
            { plonk:
                { alpha: plonkAlpha
                , beta: plonkBeta
                , gamma: plonkGamma
                , zeta: plonkZeta
                , perm: plonkPerm
                , zetaToSrsLength: plonkZetaToSrsLength
                , zetaToDomainSize: plonkZetaToDomainSize
                }
            , combinedInnerProduct
            , xi
            , bulletproofChallenges: bpChallenges
            , b: b_val
            }
        , shouldFinalize: coerce (const_ one :: FVar StepField)
        , spongeDigestBeforeEvaluations: spongeDigest
        }
    , witness: { allEvals }
    , mask
    , prevChallenges
    , domainLog2Var
    }

  ---------------------------------------------------------------------------
  -- Step 3: Compute sponge_after_index (step_verifier.ml:1167-1176)
  -- Absorb all VK fields into a fresh sponge. All comms are dummy points.
  ---------------------------------------------------------------------------
  let
    absorbPt s pt = do
      s1 <- Sponge.absorb pt.x s
      Sponge.absorb pt.y s1

  spongeAfterIndex <- label "step3_sponge_after_index" do
    let sponge0 = initialSpongeCircuit :: Sponge (FVar StepField)
    -- sigma_comm(7): sigma(6) + sigmaCommLast(1)
    s1 <- foldM absorbPt sponge0 ((Vector.replicate constDummyPt) :: Vector 6 _)
    s2 <- absorbPt s1 constDummyPt
    -- coefficients_comm(15)
    s3 <- foldM absorbPt s2 ((Vector.replicate constDummyPt) :: Vector 15 _)
    -- index comms(6): generic, psm, complete_add, mul, emul, endomul_scalar
    foldM absorbPt s3 ((Vector.replicate constDummyPt) :: Vector 6 _)

  ---------------------------------------------------------------------------
  -- Step 4: hash_messages_for_next_step_proof_opt (step_main.ml:76-104)
  -- Copy sponge_after_index, absorb app_state (Not_opt), then switch to
  -- opt_sponge for masked sg + bp_challenges (Opt).
  ---------------------------------------------------------------------------
  let
    proofMask = coerce mask1 :: BoolVar StepField
    -- OCaml uses prev_challenges (raw input), NOT the FOP's expanded output
    rawChallenges = Vector.head prevChallenges -- Vector 16 (FVar StepField)

  messagesForNextStepProof <- label "msg_hash" do
    -- Copy sponge_after_index and absorb app_state with regular sponge
    -- (app_state is Not_opt, so regular absorb)
    s1 <- label "msg_hash_absorb_app" $ Sponge.absorb appState spongeAfterIndex

    -- Switch to opt_sponge for masked fields
    -- (first Opt input triggers Opt_sponge.of_sponge)
    -- OCaml: old_bulletproof_challenges = prev_challenges (raw input fields)
    -- to_field_elements_without_index: for each proof, absorb sg then bp_challenges
    Tuple msg _ <- label "msg_hash_opt" $ OptSponge.runOptSpongeFromSponge s1 do
      OptSponge.optAbsorb (Tuple proofMask prevSg.x)
      OptSponge.optAbsorb (Tuple proofMask prevSg.y)
      for_ rawChallenges \c ->
        OptSponge.optAbsorb (Tuple proofMask c)
      OptSponge.optSqueeze
    pure msg

  ---------------------------------------------------------------------------
  -- Step 5: Build statement/publicInput (step_main.ml:88-111)
  ---------------------------------------------------------------------------
  let
    packedBranchData =
      let four = one + one + one + one
          two = one + one
      in asSizedF10 (CVar.add_ (CVar.scale_ four domainLog2Var) (CVar.add_ mask0 (CVar.scale_ two mask1)))

    publicInput =
      Tuple
        (( Vector.generate \j ->
              at (proofStateBase +
                case getFinite j of
                  0 -> 7 -- combined_inner_product
                  1 -> 8 -- b
                  2 -> 4 -- zeta_to_srs_length
                  3 -> 5 -- zeta_to_domain_size
                  _ -> 6 -- perm
              )
          ) :: Vector 5 (FVar StepField))
        ( Tuple
            (( Vector.generate \j ->
                  asSizedF128 (at (proofStateBase + 1 + getFinite j))
              ) :: Vector 2 _) -- beta, gamma
            ( Tuple
                (( Vector.generate \j ->
                      asSizedF128 (at (proofStateBase +
                        case getFinite j of
                          0 -> 0 -- alpha
                          1 -> 3 -- zeta
                          _ -> 9 -- xi
                      ))
                  ) :: Vector 3 _) -- alpha, zeta, xi
                ( Tuple
                    (( Vector.generate \j ->
                          case getFinite j of
                            0 -> spongeDigest
                            1 -> messagesForNextWrapProof
                            _ -> messagesForNextStepProof
                      ) :: Vector 3 (FVar StepField))
                    ( Tuple
                        bpChallenges
                        packedBranchData
                    )
                )
            )
        )

  ---------------------------------------------------------------------------
  -- Step 6: IVP (step_main.ml:115-136)
  ---------------------------------------------------------------------------
  let
    ivpParams =
      { curveParams: curveParams (Proxy @PallasG)
      , lagrangeComms
      , blindingH
      , correctionMode: PureCorrections
      , endo: stepEndo
      , groupMapParams: groupMapParams (Proxy @PallasG)
      , useOptSponge: false
      }

    ivpInput =
      { publicInput
      -- sgOld padded to Wrap_hack.Padded_length = 2 (matching OCaml extend_front_exn: dummy first)
      , sgOld: constDummySg :< prevSg :< Vector.nil
      , sigmaCommLast: constDummyPt
      , columnComms:
          { index: (Vector.replicate constDummyPt) :: Vector 6 _
          , coeff: (Vector.replicate constDummyPt) :: Vector 15 _
          , sigma: (Vector.replicate constDummyPt) :: Vector 6 _
          }
      , deferredValues: unfDeferredValues
      , wComm
      , zComm
      , tComm
      , opening:
          { delta
          , sg
          , lr
          , z1
          , z2
          }
      }

  output <- label "step6_ivp" $ evalSpongeM initialSpongeCircuit $
    incrementallyVerifyProof @PallasG StepOtherField.ipaScalarOps ivpParams ivpInput (Just spongeAfterIndex)

  ---------------------------------------------------------------------------
  -- Step 7: Assert sponge digest matches (step_verifier.ml:1293-1294)
  -- OCaml: Field.Assert.equal unfinalized.sponge_digest actual_digest
  -- This is an UNCONDITIONAL equal — no if_ gating.
  ---------------------------------------------------------------------------
  label "step7_assert_digest" $
    assertEq unfClaimedDigest output.spongeDigestBeforeEvaluations

  ---------------------------------------------------------------------------
  -- Step 8: Assert bp challenges (step_verifier.ml:1296-1311)
  -- OCaml: for each i: c2 = if_ is_base_case c1 c2_actual; Assert.equal c1 c2
  ---------------------------------------------------------------------------
  let isBaseCase = not_ mustVerify
  label "step8_assert_bp" $
    for_ (Vector.zip unfDeferredValues.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) -> do
      c2' <- if_ isBaseCase c1 c2
      assertEq c1 c2'

  ---------------------------------------------------------------------------
  -- Step 9: Final result (step_main.ml:148)
  -- OCaml: Boolean.(verified &&& finalized ||| not must_verify)
  ---------------------------------------------------------------------------
  label "step9_final" do
    verifiedAndFinalized <- and_ output.success finalized
    _result <- or_ verifiedAndFinalized (not_ mustVerify)
    pure unit

compileFullStepVerifyOne :: FullStepVerifyOneParams -> CompiledCircuit StepField
compileFullStepVerifyOne params =
  compilePure (Proxy @(Vector 286 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> fullStepVerifyOneCircuit params inputs)
    Kimchi.initialState
