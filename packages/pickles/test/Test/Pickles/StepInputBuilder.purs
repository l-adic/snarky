module Test.Pickles.StepInputBuilder
  ( buildFinalizeParams
  , buildFinalizeInput
  , StepField
  , WrapField
  ) where

-- | Shared helpers for constructing Step circuit input from a WrapProofContext.
-- |
-- | This module is analogous to WrapInputBuilder.purs but in the reverse direction:
-- | it prepares data for the Step verifier (Fp circuit) from a Wrap proof (Fq data).
-- |
-- | Cross-field coercion: The Wrap proof's polynomial evaluations and oracles are
-- | in Fq (Vesta.BaseField). The Step circuit operates on Fp (Vesta.ScalarField).
-- | We coerce via fromBigInt(toBigInt(fqVal)). Since |Fq - Fp| ≈ 2^78 and both
-- | fields are ~255 bits, every Fq value < Fp with probability 1 - 2^{-177}.

import Prelude

import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import JS.BigInt as BigInt
import Pickles.Commitments (combinedInnerProduct)
import Pickles.IPA (computeB, extractScalarChallengesPure)
import Pickles.Linearization as Linearization
import Pickles.Linearization.Env (fieldEnv)
import Pickles.Linearization.FFI (PointEval, evalSelectorPolys, unnormalizedLagrangeBasis, vanishesOnZkAndPreviousRows)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.PlonkChecks.FtEval (ftEval0)
import Pickles.PlonkChecks.GateConstraints (buildChallenges, buildEvalPoint, parseHex)
import Pickles.PlonkChecks.Permutation (permContribution, permScalar)
import Pickles.PlonkChecks.XiCorrect (FrSpongeInput, frSpongeChallengesPure)
import Pickles.Sponge (evalPureSpongeM)
import Pickles.Sponge as Pickles.Sponge
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofInput, FinalizeOtherProofParams)
import Pickles.Verify.Types (expandPlonkMinimal)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (F(..), SizedF, coerceViaBits, wrapF)
import Snarky.Circuit.Kimchi (Type2, toFieldPure, toShifted)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, pow, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.Pickles.ProofFFI as ProofFFI
import Test.Pickles.TestContext (WrapProofContext, computePublicEval, mkWrapIpaContext)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Step circuit field (Fp = Pallas.BaseField = Vesta.ScalarField)
type StepField = Vesta.ScalarField

-- | Wrap proof field (Fq = Vesta.BaseField = Pallas.ScalarField)
type WrapField = Pallas.ScalarField

-- | Value type for FinalizeOtherProof test input
type FinalizeOtherProofTestInput =
  FinalizeOtherProofInput (F StepField) (Type2 (F StepField) Boolean) Boolean

-- | Standard Kimchi constants
zkRows :: Int
zkRows = 3

-------------------------------------------------------------------------------
-- | Cross-field coercion helpers
-------------------------------------------------------------------------------

-- | Coerce an Fq value to Fp via BigInt roundtrip.
-- | Safe because |Fq - Fp| ≈ 2^78, so P(Fq value >= Fp) ≈ 2^{-177}.
coerceFq :: WrapField -> StepField
coerceFq fq = fromBigInt (toBigInt fq)

-- | Coerce a PointEval from Fq to Fp.
coercePointEval :: PointEval WrapField -> PointEval StepField
coercePointEval pe = { zeta: coerceFq pe.zeta, omegaTimesZeta: coerceFq pe.omegaTimesZeta }

-------------------------------------------------------------------------------
-- | Build FinalizeOtherProofParams
-------------------------------------------------------------------------------

-- | Build compile-time parameters for the FinalizeOtherProof circuit.
-- |
-- | - generator: Fp root of unity at domain 2^domainLog2
-- | - shifts: Fq shifts from Wrap prover index, coerced to Fp
-- | - endo: Vesta.endo_scalar ∈ Fp (for challenge expansion)
-- | - linearizationPoly: Pallas linearization (for Pallas constraint systems, evaluated in Fp)
buildFinalizeParams :: WrapProofContext -> FinalizeOtherProofParams StepField
buildFinalizeParams wrapCtx =
  { domain:
      { generator: (ProofFFI.domainGenerator wrapCtx.domainLog2 :: StepField)
      , shifts: map coerceFq (ProofFFI.proverIndexShifts wrapCtx.proverIndex)
      }
  , endo
  , zkRows
  , linearizationPoly: Linearization.pallas
  }

-------------------------------------------------------------------------------
-- | Build FinalizeOtherProofTestInput
-------------------------------------------------------------------------------

-- | Build circuit test input from a WrapProofContext.
-- |
-- | Follows the WrapInputBuilder.buildWrapCircuitInput pattern but in the
-- | reverse direction (Fq→Fp instead of Fp→Fq).
buildFinalizeInput :: { prevChallengeDigest :: StepField, wrapCtx :: WrapProofContext } -> FinalizeOtherProofTestInput
buildFinalizeInput { prevChallengeDigest: prevChallengeDigest_, wrapCtx } =
  let
    -----------------------------------------------------------------------
    -- Step 1: Coerce sponge digest
    -----------------------------------------------------------------------
    spongeDigest = coerceFq wrapCtx.oracles.fqDigest

    -----------------------------------------------------------------------
    -- Step 2: Coerce PlonkMinimal challenges (128-bit cross-field)
    -----------------------------------------------------------------------
    plonk =
      { alpha: wrapF (coerceViaBits wrapCtx.oracles.alphaChal :: SizedF 128 StepField)
      , beta: wrapF (coerceViaBits wrapCtx.oracles.beta :: SizedF 128 StepField)
      , gamma: wrapF (coerceViaBits wrapCtx.oracles.gamma :: SizedF 128 StepField)
      , zeta: wrapF (coerceViaBits wrapCtx.oracles.zetaChal :: SizedF 128 StepField)
      }

    -----------------------------------------------------------------------
    -- Step 3: Expand plonk and compute domain values
    -----------------------------------------------------------------------
    plonkExpanded = expandPlonkMinimal endo plonk
    omega = (ProofFFI.domainGenerator wrapCtx.domainLog2 :: StepField)
    n = BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt wrapCtx.domainLog2)
    zetaToNMinus1 = pow plonkExpanded.zeta n - one
    zkPoly = ProofFFI.permutationVanishingPolynomial
      { domainLog2: wrapCtx.domainLog2, zkRows, pt: plonkExpanded.zeta }
    omegaToMinusZkRows = pow omega (n - BigInt.fromInt zkRows)
    vanishesOnZk = vanishesOnZkAndPreviousRows
      { domainLog2: wrapCtx.domainLog2, zkRows, pt: plonkExpanded.zeta }
    lagrangeFalse0 = unnormalizedLagrangeBasis
      { domainLog2: wrapCtx.domainLog2, zkRows: 0, offset: 0, pt: plonkExpanded.zeta }
    lagrangeTrue1 = unnormalizedLagrangeBasis
      { domainLog2: wrapCtx.domainLog2, zkRows, offset: -1, pt: plonkExpanded.zeta }

    -----------------------------------------------------------------------
    -- Step 4: Coerce polynomial evaluations (Fq → Fp)
    -----------------------------------------------------------------------
    witnessEvals = map coercePointEval (ProofFFI.proofWitnessEvals wrapCtx.proof)
    zEvals = coercePointEval (ProofFFI.proofZEvals wrapCtx.proof)
    sigmaEvals = map coercePointEval (ProofFFI.proofSigmaEvals wrapCtx.proof)
    coeffEvals = map coercePointEval (ProofFFI.proofCoefficientEvals wrapCtx.proof)
    -- Index evals: evaluate selector polys at Fq zeta, then coerce to Fp
    indexEvals = map coercePointEval (evalSelectorPolys wrapCtx.proverIndex wrapCtx.oracles.zeta)

    publicEvals :: PointEval StepField
    publicEvals =
      { zeta: coerceFq wrapCtx.oracles.publicEvalZeta
      , omegaTimesZeta: coerceFq wrapCtx.oracles.publicEvalZetaOmega
      }
    ftEval1 = coerceFq wrapCtx.oracles.ftEval1

    -----------------------------------------------------------------------
    -- Step 5: Run Fp Fr-sponge → xi, r, polyscale, evalscale
    -----------------------------------------------------------------------
    frInput :: FrSpongeInput StepField
    frInput =
      { fqDigest: spongeDigest
      , prevChallengeDigest: prevChallengeDigest_
      , ftEval1
      , publicEvals
      , zEvals
      , indexEvals
      , witnessEvals
      , coeffEvals
      , sigmaEvals
      , endo
      }
    frResult = frSpongeChallengesPure frInput

    -----------------------------------------------------------------------
    -- Step 6: Compute publicEvalForFt
    -----------------------------------------------------------------------
    publicEvalForFt = computePublicEval
      { publicInputs: map coerceFq wrapCtx.publicInputs
      , domainLog2: wrapCtx.domainLog2
      , omega
      , zeta: plonkExpanded.zeta
      }

    -----------------------------------------------------------------------
    -- Step 7: Compute ftEval0 in Fp
    -----------------------------------------------------------------------
    -- Build permutation input
    permInput =
      { w: map _.zeta (Vector.take @7 witnessEvals)
      , sigma: map _.zeta sigmaEvals
      , z: zEvals
      , shifts: map coerceFq (ProofFFI.proverIndexShifts wrapCtx.proverIndex)
      , alpha: plonkExpanded.alpha
      , beta: plonkExpanded.beta
      , gamma: plonkExpanded.gamma
      , zkPolynomial: zkPoly
      , zetaToNMinus1
      , omegaToMinusZkRows
      , zeta: plonkExpanded.zeta
      }
    permContrib = permContribution permInput

    -- Gate constraints
    evalPoint = buildEvalPoint
      { witnessEvals
      , coeffEvals: map _.zeta coeffEvals
      , indexEvals
      , defaultVal: zero
      }
    challenges = buildChallenges
      { alpha: plonkExpanded.alpha
      , beta: plonkExpanded.beta
      , gamma: plonkExpanded.gamma
      , jointCombiner: zero
      , vanishesOnZk
      , lagrangeFalse0
      , lagrangeTrue1
      }
    env = fieldEnv evalPoint challenges parseHex
    gateConstraints = evaluate PallasTokens.constantTermTokens env

    ftEval0Value = ftEval0
      { permContribution: permContrib
      , publicEval: publicEvalForFt
      , gateConstraints
      }

    -----------------------------------------------------------------------
    -- Step 8: Build 45-element eval vector, compute CIP
    -----------------------------------------------------------------------
    ftPointEval :: PointEval StepField
    ftPointEval = { zeta: ftEval0Value, omegaTimesZeta: ftEval1 }

    allEvals45 :: Vector 45 (PointEval StepField)
    allEvals45 =
      (publicEvals :< ftPointEval :< zEvals :< Vector.nil)
        `Vector.append` indexEvals
        `Vector.append` witnessEvals
        `Vector.append` coeffEvals
        `Vector.append` sigmaEvals

    cip = combinedInnerProduct
      { polyscale: frResult.xi
      , evalscale: frResult.evalscale
      , evals: allEvals45
      }

    -----------------------------------------------------------------------
    -- Step 9: Extract bulletproof challenges
    -----------------------------------------------------------------------
    -- L/R pairs have Fp coordinates (Pallas.G base field = Fp = Vesta.ScalarField)
    -- Sponge from mkWrapIpaContext is Fp sponge
    { spongeState } = mkWrapIpaContext wrapCtx

    rawBpChallenges :: Vector 16 (SizedF 128 StepField)
    rawBpChallenges = evalPureSpongeM spongeState do
      _ <- Pickles.Sponge.squeeze -- squeeze for u
      extractScalarChallengesPure (coerce $ ProofFFI.vestaProofOpeningLr wrapCtx.proof)

    bulletproofChallenges :: Vector 16 (SizedF 128 (F StepField))
    bulletproofChallenges = coerce rawBpChallenges

    -----------------------------------------------------------------------
    -- Step 10: Compute b and perm
    -----------------------------------------------------------------------
    -- Expand BP challenges to full Fp for computeB
    expandedChals :: Vector 16 StepField
    expandedChals = map
      (\c -> toFieldPure c endo)
      rawBpChallenges

    b = computeB expandedChals
      { zeta: plonkExpanded.zeta
      , zetaOmega: plonkExpanded.zeta * omega
      , evalscale: frResult.evalscale
      }

    perm = permScalar permInput

    -----------------------------------------------------------------------
    -- Step 11: Compute zetaToSrsLength, zetaToDomainSize
    -----------------------------------------------------------------------
    maxPolySize = ProofFFI.vestaVerifierIndexMaxPolySize wrapCtx.verifierIndex
    zetaToSrsLength = pow plonkExpanded.zeta (BigInt.fromInt maxPolySize)
    zetaToDomainSize = pow plonkExpanded.zeta n

  in
    -----------------------------------------------------------------------
    -- Step 12: Assemble input
    -----------------------------------------------------------------------
    { unfinalized:
        { deferredValues:
            { plonk
            , combinedInnerProduct: toShifted (F cip)
            , xi: coerce frResult.rawXi
            , bulletproofChallenges
            , b: toShifted (F b)
            , perm: toShifted (F perm)
            , zetaToSrsLength: toShifted (F zetaToSrsLength)
            , zetaToDomainSize: toShifted (F zetaToDomainSize)
            }
        , shouldFinalize: true
        , spongeDigestBeforeEvaluations: F spongeDigest
        }
    , witness:
        { allEvals:
            { ftEval1: F ftEval1
            , publicEvals: coerce publicEvals
            , zEvals: coerce zEvals
            , indexEvals: coerce indexEvals
            , witnessEvals: coerce witnessEvals
            , coeffEvals: coerce coeffEvals
            , sigmaEvals: coerce sigmaEvals
            }
        , domainValues:
            { zkPolynomial: F zkPoly
            , zetaToNMinus1: F zetaToNMinus1
            , omegaToMinusZkRows: F omegaToMinusZkRows
            , vanishesOnZk: F vanishesOnZk
            , lagrangeFalse0: F lagrangeFalse0
            , lagrangeTrue1: F lagrangeTrue1
            }
        , publicEvalForFt: F publicEvalForFt
        }
    , prevChallengeDigest: F prevChallengeDigest_
    }

-------------------------------------------------------------------------------
-- | Private helpers
-------------------------------------------------------------------------------

-- | Endo scalar coefficient for challenge expansion (Vesta.endo_scalar ∈ Fp).
-- | This is `Wrap_inner_curve.scalar` in OCaml endo.ml.
endo :: StepField
endo = let EndoScalar e = endoScalar @Vesta.BaseField @Vesta.ScalarField in e
