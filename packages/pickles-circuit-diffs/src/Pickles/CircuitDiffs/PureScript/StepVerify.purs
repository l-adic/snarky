module Pickles.CircuitDiffs.PureScript.StepVerify
  ( compileStepVerify
  , StepVerifyParams
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Foldable (for_)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF10, asSizedF128, dummyPallasPt, dummyWrapSg, stepEndo, unsafeIdx)
import Pickles.PublicInputCommit (CorrectionMode(..))
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Types (StepField)
import Pickles.Verify (incrementallyVerifyProof)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.CVar as CVar
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, assertEq, const_, if_)
import Snarky.Circuit.Kimchi (SplitField(..), Type2(..), groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | Step_verifier.verify circuit — wraps incrementallyVerifyProof with:
-- |   1. Public input from statement (Spec.pack) instead of manual tuple
-- |   2. Unconditional digest assertion (step_verifier.ml:1297)
-- |   3. is_base_case-gated bp challenge assertions (step_verifier.ml:1300-1314)
-- |
-- | Input layout (268 fields):
-- |   0-113:   wrap_proof (114 fields, hlist: messages then opening)
-- |   114-143: proof_state (30 fields, hlist: plonk+deferred then digest)
-- |   144-232: all_evals (89 fields, dead inputs — not used by verify)
-- |   233-264: unfinalized (32 fields, spec order: 5×fq, digest, 2×chal, 3×sc, 15×bp, bool)
-- |   265:     is_base_case
-- |   266:     messages_for_next_wrap_proof
-- |   267:     messages_for_next_step_proof
-- |
-- | Reference: step_verifier.ml:1242-1315, step_main.ml:17-117

type StepVerifyParams =
  { lagrangeComms :: Array (AffinePoint (F StepField))
  , blindingH :: AffinePoint (F StepField)
  }

stepVerifyCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => StepVerifyParams
  -> Vector 268 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
stepVerifyCircuit { lagrangeComms, blindingH } inputs = do
  let
    at = unsafeIdx inputs
    readPt i = { x: at i, y: at (i + 1) }
    readOtherField i = Type2 (SplitField { sDiv2: at i, sOdd: coerce (at (i + 1)) })

    constDummySg :: AffinePoint (FVar StepField)
    constDummySg = { x: const_ dummyWrapSg.x, y: const_ dummyWrapSg.y }

    constDummyPt = let { x: F x', y: F y' } = dummyPallasPt in { x: const_ x', y: const_ y' }

    ---------------------------------------------------------------------------
    -- Parse wrap_proof (positions 0-113)
    ---------------------------------------------------------------------------
    -- Messages: w_comm(0-29), z_comm(30-31), t_comm(32-45)
    -- Opening: lr(46-105), z_1(106-107), z_2(108-109), delta(110-111), sg(112-113)
    wComm :: Vector 15 (AffinePoint (FVar StepField))
    wComm = Vector.generate \j -> readPt (2 * getFinite j)

    zComm = readPt 30

    tComm :: Vector 7 (AffinePoint (FVar StepField))
    tComm = Vector.generate \j -> readPt (32 + 2 * getFinite j)

    lr :: Vector 15 { l :: AffinePoint (FVar StepField), r :: AffinePoint (FVar StepField) }
    lr = Vector.generate \j ->
      { l: readPt (46 + 4 * getFinite j)
      , r: readPt (46 + 4 * getFinite j + 2)
      }

    ---------------------------------------------------------------------------
    -- Parse proof_state (positions 114-143) → publicInput for IVP
    ---------------------------------------------------------------------------
    -- Hlist order: plonk(alpha,beta,gamma,zeta,zetaToSrs,zetaToDom,perm),
    --             cip, b, xi, bp_challenges(16), mask(2), domain_log2, digest
    --
    -- Spec.pack layout (from Types.Wrap.Statement.In_circuit.spec + to_data):
    --   Vec5 FVar:       fp = [cip, b, zeta_to_srs, zeta_to_dom, perm]
    --   Vec2 SizedF128:  challenge = [beta, gamma]
    --   Vec3 SizedF128:  scalar_challenge = [alpha, zeta, xi]
    --   Vec3 FVar:       digest = [sponge_digest, msg_wrap, msg_step]
    --   Vec16 SizedF128: bulletproof_challenges (Tick.Rounds = 16)
    --   SizedF10:        branch_data = [domain_log2 packed with proofs_verified]
    --
    -- Branch_data.pack: (four * domain_log2) + pack [mask_0; mask_1]
    -- = 4*domain_log2 + mask_0 + 2*mask_1  (all CVar arithmetic, no constraints)
    packedBranchData =
      let
        four = one + one + one + one
        two = one + one
      in
        CVar.add_ (CVar.scale_ four (at 142)) (CVar.add_ (at 140) (CVar.scale_ two (at 141)))

    publicInput =
      Tuple
        -- fp: [cip(121), b(122), zeta_to_srs(118), zeta_to_dom(119), perm(120)]
        ( (Vector.generate \j ->
            at (case getFinite j of
              0 -> 121  -- combined_inner_product
              1 -> 122  -- b
              2 -> 118  -- zeta_to_srs_length
              3 -> 119  -- zeta_to_domain_size
              _ -> 120  -- perm
            )) :: Vector 5 (FVar StepField)
        )
        ( Tuple
            -- challenge: [beta(115), gamma(116)]
            ( (Vector.generate \j ->
                asSizedF128 (at (115 + getFinite j))) :: Vector 2 _
            )
            ( Tuple
                -- scalar_challenge: [alpha(114), zeta(117), xi(123)]
                ( (Vector.generate \j ->
                    asSizedF128 (at (case getFinite j of
                      0 -> 114  -- alpha
                      1 -> 117  -- zeta
                      _ -> 123  -- xi
                    ))) :: Vector 3 _
                )
                ( Tuple
                    -- digest: [sponge_digest(143), msg_wrap(266), msg_step(267)]
                    ( (Vector.generate \j ->
                        at (case getFinite j of
                          0 -> 143  -- sponge_digest
                          1 -> 266  -- messages_for_next_wrap_proof
                          _ -> 267  -- messages_for_next_step_proof
                        )) :: Vector 3 (FVar StepField)
                    )
                    ( Tuple
                        -- bulletproof_challenges (16, Tick.Rounds)
                        ( (Vector.generate \j ->
                            asSizedF128 (at (124 + getFinite j))) :: Vector 16 _
                        )
                        -- branch_data (packed, see packedBranchData below)
                        (asSizedF10 packedBranchData)
                    )
                )
            )
        )

    ---------------------------------------------------------------------------
    -- Parse unfinalized (positions 233-264, spec order)
    ---------------------------------------------------------------------------
    -- fq(2 each): cip(233), b(235), zetaToSrs(237), zetaToDom(239), perm(241)
    -- digest(243), beta(244), gamma(245), alpha(246), zeta(247), xi(248)
    -- bp_challenges(249-263), should_finalize(264)

    deferredValues =
      { plonk:
          { alpha: asSizedF128 (at 246)
          , beta: asSizedF128 (at 244)
          , gamma: asSizedF128 (at 245)
          , zeta: asSizedF128 (at 247)
          , perm: readOtherField 241
          , zetaToSrsLength: readOtherField 237
          , zetaToDomainSize: readOtherField 239
          }
      , combinedInnerProduct: readOtherField 233
      , b: readOtherField 235
      , xi: asSizedF128 (at 248)
      , bulletproofChallenges:
          (Vector.generate \j -> asSizedF128 (at (249 + getFinite j))) :: Vector 15 _
      }

    isBaseCase = coerce (at 265) :: BoolVar StepField
    claimedDigest = at 243  -- unfinalized sponge_digest

    ---------------------------------------------------------------------------
    -- IVP params and input
    ---------------------------------------------------------------------------
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
      , sgOld: constDummySg :< constDummySg :< Vector.nil
      , sigmaCommLast: constDummyPt
      , columnComms:
          { index: (Vector.replicate constDummyPt) :: Vector 6 _
          , coeff: (Vector.replicate constDummyPt) :: Vector 15 _
          , sigma: (Vector.replicate constDummyPt) :: Vector 6 _
          }
      , deferredValues
      , wComm
      , zComm
      , tComm
      , opening:
          { delta: readPt 110
          , sg: readPt 112
          , lr
          , z1: readOtherField 106
          , z2: readOtherField 108
          }
      }

  -- 1. Run IVP
  output <- evalSpongeM initialSpongeCircuit $
    incrementallyVerifyProof @PallasG StepOtherField.ipaScalarOps ivpParams ivpInput

  -- 2. Assert digest — UNCONDITIONAL (step_verifier.ml:1297)
  assertEq output.spongeDigestBeforeEvaluations claimedDigest

  -- 3. Assert bp challenges — gated by is_base_case (step_verifier.ml:1300-1314)
  for_ (Vector.zip deferredValues.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) -> do
    c2' <- if_ isBaseCase c1 c2
    assertEq c1 c2'

compileStepVerify :: StepVerifyParams -> CompiledCircuit StepField
compileStepVerify srsData =
  compilePure (Proxy @(Vector 268 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> stepVerifyCircuit srsData inputs)
    Kimchi.initialState
