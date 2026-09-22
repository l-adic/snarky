-- | Deterministic dummy values for bootstrapping Pickles recursion —
-- | what a base case pads its empty previous-proof slots with.
-- |
-- | Everything here is drawn from one `Ro` stream, so the order in
-- | which these constructors are forced is part of the answer, not an
-- | implementation detail. `computeBaseCaseDummies` fixes that order
-- | for a given `max_proofs_verified`.
module Pickles.Step.Dummy
  ( DummySgValues
  , computeDummySgValues
  , wrapDummyUnfinalizedProof
  , mkDummyPerProofUnfinalized
  , stepDummyUnfinalizedProof
  , wrapDomainLog2ForProofsVerified
  , DummyEvals
  , PlonkChals
  , UnfinalizedConstantDummy
  , ProofDummy
  , BaseCaseDummies
  , ForceOrder(..)
  , dummyEvals
  , unfinalizedConstantDummy
  , proofDummy
  , forceOrderFor
  , computeBaseCaseDummies
  , baseCaseDummies
  , dummyWrapProof
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Foldable (foldl)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import JS.BigInt as BigInt
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Pickles.Constants (zkRowsByDefault)
import Pickles.DeferredValues (UnfinalizedProof)
import Pickles.Dummy (RoM, chal, dummyIpaStepChallenges, dummyIpaWrapChallenges, evalRoM, initialRo, pow2, scalarChal, stepEndo, tick, tock, wrapEndo)
import Pickles.Field (StepField, WrapField)
import Pickles.IPA (bPoly, computeB)
import Pickles.Linearization.Env (fieldEnv)
import Pickles.Linearization.FFI (PointEval, domainGenerator, domainShifts, unnormalizedLagrangeBasis)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.PlonkChecks (buildChallenges, buildEvalPoint, frSpongeChallengesPureChunked, padChunkedEvals, permContribution, permScalar, singleChunkEvals)
import Pickles.Prove.Pure.Common (crossFieldDigest)
import Pickles.Sponge (initialSponge)
import Pickles.Types (Evals, PerProofUnfinalized(..), StepIPARounds, WrapIPARounds)
import RandomOracle.Sponge as PureSponge
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Impl.Vesta as VestaImpl
import Snarky.Backend.Kimchi.Proof (Proof, vestaMakeWireProof)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F(..), SizedF, UnChecked(..), coerceViaBits)
import Snarky.Circuit.DSL.SizedF (fromField, toField, unwrapF, wrapF) as SizedF
import Snarky.Circuit.Kimchi (toFieldPure)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, generator, pow, toAffine) as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (class Shifted, SplitField, Type2(..), fromShifted, toShifted)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Ro-consuming dummies
-- |
-- | These types carry only the fields that draw from `Ro`; everything
-- | derived from them is computed at consumer level.
-- |
-- | Draws per primitive, over the three independent counters:
-- |
-- |   dummyEvals                89 fq,  0 fp,  0 chal
-- |   unfinalizedConstantDummy   2 fq,  0 fp,  4 chal
-- |   proofDummy                 2 fq, 89 fp,  4 chal
-- |   dummyIpaWrapChallenges     0 fq,  0 fp, 15 chal
-- |   dummyIpaStepChallenges     0 fq,  0 fp, 16 chal
-------------------------------------------------------------------------------

-- | The dummy evaluations, in the wrap field.
type DummyEvals = Evals WrapField

-- | The four plonk challenges — the layout shared by
-- | `unfinalizedConstantDummy` and `proofDummy`.
type PlonkChals f =
  { alpha :: SizedF 128 f
  , beta :: SizedF 128 f
  , gamma :: SizedF 128 f
  , zeta :: SizedF 128 f
  }

-- | The Ro-consumed fields of a dummy unfinalized proof. `xi`, the
-- | bulletproof challenges, `shouldFinalize`, the sponge digest and
-- | the three shifted plonk values are derived, and rebuilt by
-- | `wrapDummyUnfinalizedProof`.
type UnfinalizedConstantDummy =
  { plonk :: PlonkChals WrapField
  , combinedInnerProduct :: WrapField -- ^ Unshifted.
  , b :: WrapField -- ^ Unshifted.
  }

-- | The Ro-derived fields of a dummy proof. The `sg` padding, the
-- | branch data and the `g0`-valued commitments draw nothing from
-- | `Ro` and are built at consumer level.
type ProofDummy =
  { plonk :: PlonkChals StepField
  , z1 :: WrapField -- ^ From the opening proof.
  , z2 :: WrapField -- ^ From the opening proof.
  , prevEvals :: Evals StepField
  }

-- | The dummy evaluations: 89 draws from the tock stream.
-- |
-- | Each `(zeta, omegaTimesZeta)` pair costs two, one per array, so
-- | the record comes to (6 selectors + 6 sigmas + 15 witness + 15
-- | coefficients + 1 z + 1 public input) × 2 + 1 for `ftEval1` = 89.
-- |
-- | The draw order is fixed, and runs right to left through the
-- | record.
dummyEvals :: RoM DummyEvals
dummyEvals =
  let
    pointEval :: RoM (PointEval WrapField)
    pointEval = do
      oz <- tock -- right element of the pair first
      z <- tock
      pure { zeta: z, omegaTimesZeta: oz }

    pointEvalVec :: forall @n. Reflectable n Int => RoM (Vector n (PointEval WrapField))
    pointEvalVec = do
      v <- Vector.generateA (const pointEval)
      pure (Vector.reverse v)
  in
    do
      -- Draw order: selectors, sigma, z, coefficients, witness,
      -- public input, ft_eval1.
      idxEndomulScalar <- pointEval
      idxEmul <- pointEval
      idxMul <- pointEval
      idxCompleteAdd <- pointEval
      idxPoseidon <- pointEval
      idxGeneric <- pointEval
      let
        indexEvals =
          idxGeneric :< idxPoseidon :< idxCompleteAdd :< idxMul :< idxEmul :< idxEndomulScalar :< Vector.nil
      sigmaEvals <- pointEvalVec @6
      zEvals <- pointEval
      coeffEvals <- pointEvalVec @15
      witnessEvals <- pointEvalVec @15
      publicEvals <- pointEval
      ftEval1 <- tock
      pure { ftEval1, publicEvals, zEvals, indexEvals, witnessEvals, coeffEvals, sigmaEvals }

-- | The Ro-consumed fields of a dummy unfinalized proof: four
-- | challenge draws, then two tock draws.
-- |
-- | The draw order is fixed. The challenges come in declaration
-- | order, but the record around `b` and `combinedInnerProduct` is
-- | built right to left, so `b` draws first.
unfinalizedConstantDummy :: RoM UnfinalizedConstantDummy
unfinalizedConstantDummy = do
  alpha <- scalarChal
  beta <- chal
  gamma <- chal
  zeta <- scalarChal
  b <- tock
  combinedInnerProduct <- tock
  pure { plonk: { alpha, beta, gamma, zeta }, combinedInnerProduct, b }

-- | The Ro-derived fields of a dummy proof: two tock draws, then 89
-- | tick draws, then four challenge draws.
-- |
-- | The draw order is fixed — the opening proof's `z2` then `z1`,
-- | then the previous evaluations, then the plonk challenges from
-- | `zeta` back to `alpha`.
-- |
-- | Callers have to run `dummyEvals` before this in any fresh `Ro`
-- | sequence, or the streams diverge.
proofDummy :: RoM ProofDummy
proofDummy = do
  z2 <- tock
  z1 <- tock
  prevEvals <- proofDummyPrevEvals
  zeta <- scalarChal
  gamma <- chal
  beta <- chal
  alpha <- scalarChal
  pure { plonk: { alpha, beta, gamma, zeta }, z1, z2, prevEvals }

-- | 89 tick draws, in the same record layout as `dummyEvals`.
proofDummyPrevEvals :: RoM (Evals StepField)
proofDummyPrevEvals =
  let
    pointEval :: RoM (PointEval StepField)
    pointEval = do
      oz <- tick
      z <- tick
      pure { zeta: z, omegaTimesZeta: oz }

    pointEvalVec :: forall @n. Reflectable n Int => RoM (Vector n (PointEval StepField))
    pointEvalVec = do
      v <- Vector.generateA (const pointEval)
      pure (Vector.reverse v)
  in
    do
      idxEndomulScalar <- pointEval
      idxEmul <- pointEval
      idxMul <- pointEval
      idxCompleteAdd <- pointEval
      idxPoseidon <- pointEval
      idxGeneric <- pointEval
      let
        indexEvals =
          idxGeneric :< idxPoseidon :< idxCompleteAdd :< idxMul :< idxEmul :< idxEndomulScalar :< Vector.nil
      sigmaEvals <- pointEvalVec @6
      zEvals <- pointEval
      coeffEvals <- pointEvalVec @15
      witnessEvals <- pointEvalVec @15
      publicEvals <- pointEval
      ftEval1 <- tick
      pure { ftEval1, publicEvals, zEvals, indexEvals, witnessEvals, coeffEvals, sigmaEvals }

-- | Everything a compile needs to pad its base-case slots with
-- | Ro-derived values.
type BaseCaseDummies =
  { ipaWrapChallenges :: Vector WrapIPARounds (SizedF 128 WrapField)
  , ipaStepChallenges :: Vector StepIPARounds (SizedF 128 StepField)
  , dummyEvals :: DummyEvals
  , unfinalizedConstantDummy :: UnfinalizedConstantDummy
  , proofDummy :: ProofDummy
  }

-- | Which of `unfinalizedConstantDummy` and `proofDummy` draws from
-- | `Ro` first.
data ForceOrder = UnfinalizedFirst | ProofDummyFirst

forceOrderFor :: { maxProofsVerified :: Int } -> ForceOrder
forceOrderFor { maxProofsVerified } = case maxProofsVerified of
  1 -> ProofDummyFirst
  _ -> UnfinalizedFirst

-- | The `BaseCaseDummies` for a circuit shape. They depend only on
-- | `maxProofsVerified`, so the same N gives the same bits everywhere.
baseCaseDummies :: { maxProofsVerified :: Int } -> BaseCaseDummies
baseCaseDummies cfg = evalRoM (computeBaseCaseDummies cfg) initialRo

-- | Draw the IPA challenges and the three Ro-consuming dummies, in
-- | the order the given circuit shape fixes.
computeBaseCaseDummies :: { maxProofsVerified :: Int } -> RoM BaseCaseDummies
computeBaseCaseDummies cfg = do
  ipaWrapChallenges <- dummyIpaWrapChallenges
  ipaStepChallenges <- dummyIpaStepChallenges
  evals <- dummyEvals
  pair <- case forceOrderFor cfg of
    UnfinalizedFirst -> do
      unf <- unfinalizedConstantDummy
      prf <- proofDummy
      pure { unf, prf }
    ProofDummyFirst -> do
      prf <- proofDummy
      unf <- unfinalizedConstantDummy
      pure { unf, prf }
  pure
    { ipaWrapChallenges
    , ipaStepChallenges
    , dummyEvals: evals
    , unfinalizedConstantDummy: pair.unf
    , proofDummy: pair.prf
    }

-------------------------------------------------------------------------------
-- | Derived dummy values
-- |
-- | Views over `BaseCaseDummies`: the expanded, shifted and hashed
-- | values the step and wrap circuits actually read.
-------------------------------------------------------------------------------

type DummySgValues =
  { ipa ::
      { wrap ::
          { challengesRaw :: Vector WrapIPARounds (SizedF 128 WrapField)
          , challengesExpanded :: Vector WrapIPARounds WrapField
          , sg :: AffinePoint StepField
          }
      , step ::
          { challengesRaw :: Vector StepIPARounds (SizedF 128 StepField)
          , challengesExpanded :: Vector StepIPARounds StepField
          , sg :: AffinePoint WrapField
          }
      }
  , unfinalized ::
      { alphaRaw :: SizedF 128 WrapField
      , betaRaw :: SizedF 128 WrapField
      , gammaRaw :: SizedF 128 WrapField
      , zetaRaw :: SizedF 128 WrapField
      , xiRaw :: SizedF 128 WrapField
      , zetaExpanded :: WrapField
      , alphaExpanded :: WrapField
      , plonk ::
          { perm :: Type2 (F WrapField)
          , zetaToSrsLength :: Type2 (F WrapField)
          , zetaToDomainSize :: Type2 (F WrapField)
          }
      , combinedInnerProduct :: WrapField
      , b :: WrapField
      , spongeDigest :: WrapField
      }
  }

computeDummySgValues :: BaseCaseDummies -> CRS Pallas.G -> CRS Vesta.G -> DummySgValues
computeDummySgValues bcd pallasSrs vestaSrs =
  let
    u = bcd.unfinalizedConstantDummy

    wrapChalExpanded = map (\c -> toFieldPure c wrapEndo) bcd.ipaWrapChallenges
    stepChalExpanded = map (\c -> toFieldPure c stepEndo) bcd.ipaStepChallenges

    alphaExpanded = toFieldPure u.plonk.alpha wrapEndo
    zetaFq = toFieldPure u.plonk.zeta wrapEndo

    wrapSg = PallasImpl.pallasSrsBPolyCommitmentPoint pallasSrs
      (Vector.toUnfoldable wrapChalExpanded)
    stepSg = VestaImpl.vestaSrsBPolyCommitmentPoint vestaSrs
      (Vector.toUnfoldable stepChalExpanded)

    wrapDomainLog2 = reflectType (Proxy :: Proxy WrapIPARounds)
    zetaPow = Curves.pow zetaFq (pow2 wrapDomainLog2)

    digestDummy = Curves.fromBigInt
      ( BigInt.fromInt 1
          + pow2 64
          + pow2 128
          + pow2 192
      )
  in
    { ipa:
        { wrap:
            { challengesRaw: bcd.ipaWrapChallenges
            , challengesExpanded: wrapChalExpanded
            , sg: wrapSg
            }
        , step:
            { challengesRaw: bcd.ipaStepChallenges
            , challengesExpanded: stepChalExpanded
            , sg: stepSg
            }
        }
    , unfinalized:
        { alphaRaw: u.plonk.alpha
        , betaRaw: u.plonk.beta
        , gammaRaw: u.plonk.gamma
        , zetaRaw: u.plonk.zeta
        , xiRaw: unsafePartial $ fromJust $ SizedF.fromField @128
            (Curves.fromBigInt (BigInt.fromInt 1 + pow2 64) :: WrapField)
        , zetaExpanded: zetaFq
        , alphaExpanded
        , plonk:
            { perm: (wrapDummyUnfinalizedProof bcd).deferredValues.plonk.perm
            , zetaToSrsLength: toShifted (F zetaPow)
            , zetaToDomainSize: toShifted (F zetaPow)
            }
        , combinedInnerProduct: u.combinedInnerProduct
        , b: u.b
        , spongeDigest: digestDummy
        }
    }

-- | The wrap-side dummy unfinalized proof, with its derived fields
-- | filled in from `unfinalizedConstantDummy`.
wrapDummyUnfinalizedProof
  :: BaseCaseDummies
  -> UnfinalizedProof WrapIPARounds (F WrapField) (Type2 (F WrapField)) Boolean
wrapDummyUnfinalizedProof bcd =
  let
    u = bcd.unfinalizedConstantDummy
    evals = bcd.dummyEvals
    Curves.EndoScalar wEndo = (Curves.endoScalar)

    alphaExpanded = toFieldPure u.plonk.alpha wEndo
    betaExpanded = SizedF.toField u.plonk.beta :: WrapField
    gammaExpanded = SizedF.toField u.plonk.gamma :: WrapField
    zetaExpanded = toFieldPure u.plonk.zeta wEndo

    -- The wrap domain at `proofs_verified = 2`.
    wrapDomainLog2 = 15
    -- A wrap proof is always one chunk, so this never varies.
    zkRows = zkRowsByDefault
    omega = (domainGenerator wrapDomainLog2)
    n = pow2 wrapDomainLog2
    zetaToNMinus1 = Curves.pow zetaExpanded n - one
    omegaM1 = recip omega
    omegaM2 = omegaM1 * omegaM1
    omegaM3 = omegaM2 * omegaM1
    zkPoly = (zetaExpanded - omegaM1) * (zetaExpanded - omegaM2) * (zetaExpanded - omegaM3)
    omegaToMinusZkRows = Curves.pow omega (n - BigInt.fromInt zkRows)

    permInput =
      { w: map _.zeta (Vector.take @7 evals.witnessEvals)
      , sigma: map _.zeta evals.sigmaEvals
      , z: evals.zEvals
      , shifts: (domainShifts wrapDomainLog2)
      , alpha: alphaExpanded
      , beta: betaExpanded
      , gamma: gammaExpanded
      , zkPolynomial: zkPoly
      , zetaToNMinus1
      , omegaToMinusZkRows
      , zeta: zetaExpanded
      }
    perm = permScalar permInput

    zetaPow = Curves.pow zetaExpanded (pow2 wrapDomainLog2)

    digestDummy = Curves.fromBigInt
      ( BigInt.fromInt 1
          + pow2 64
          + pow2 128
          + pow2 192
      )

    xi :: SizedF 128 (F WrapField)
    xi = SizedF.wrapF $ unsafePartial $ fromJust $ SizedF.fromField @128
      (Curves.fromBigInt (BigInt.fromInt 1 + pow2 64) :: WrapField)
  in
    { deferredValues:
        { plonk:
            { alpha: SizedF.wrapF u.plonk.alpha
            , beta: SizedF.wrapF u.plonk.beta
            , gamma: SizedF.wrapF u.plonk.gamma
            , zeta: SizedF.wrapF u.plonk.zeta
            , perm: toShifted (F perm)
            , zetaToSrsLength: toShifted (F zetaPow)
            , zetaToDomainSize: toShifted (F zetaPow)
            }
        , combinedInnerProduct: Type2 (F u.combinedInnerProduct)
        , xi
        , bulletproofChallenges: map SizedF.wrapF bcd.ipaWrapChallenges
        , b: Type2 (F u.b)
        }
    , shouldFinalize: false
    , spongeDigestBeforeEvaluations: F digestDummy
    }

-- | The step-side dummy `PerProofUnfinalized`, cross-field encoded.
-- | `stepMain` front-pads its public input with these.
mkDummyPerProofUnfinalized
  :: BaseCaseDummies
  -> PerProofUnfinalized
       WrapIPARounds
       (Type2 (SplitField (F StepField) Boolean))
       (F StepField)
       Boolean
mkDummyPerProofUnfinalized bcd =
  let
    du = wrapDummyUnfinalizedProof bcd
    dvDu = du.deferredValues
    pDu = dvDu.plonk

    t2toT2sf :: Type2 (F WrapField) -> Type2 (SplitField (F StepField) Boolean)
    t2toT2sf t = toShifted (fromShifted t :: F WrapField)

    chalToStep :: SizedF 128 (F WrapField) -> SizedF 128 (F StepField)
    chalToStep s = SizedF.wrapF (coerceViaBits (SizedF.unwrapF s))

    digestStep :: F StepField
    digestStep =
      let
        F digestWrap = du.spongeDigestBeforeEvaluations
      in
        F (crossFieldDigest digestWrap)
  in
    PerProofUnfinalized
      { combinedInnerProduct: t2toT2sf dvDu.combinedInnerProduct
      , b: t2toT2sf dvDu.b
      , zetaToSrsLength: t2toT2sf pDu.zetaToSrsLength
      , zetaToDomainSize: t2toT2sf pDu.zetaToDomainSize
      , perm: t2toT2sf pDu.perm
      , spongeDigest: digestStep
      , beta: UnChecked (chalToStep pDu.beta)
      , gamma: UnChecked (chalToStep pDu.gamma)
      , alpha: UnChecked (chalToStep pDu.alpha)
      , zeta: UnChecked (chalToStep pDu.zeta)
      , xi: UnChecked (chalToStep dvDu.xi)
      , bulletproofChallenges: map (UnChecked <<< chalToStep) dvDu.bulletproofChallenges
      , shouldFinalize: false
      }

-- | The step-side dummy unfinalized proof, with its deferred values
-- | expanded.
-- |
-- | `bpChals` is a parameter because the two callers pass different
-- | challenge vectors at different widths; the deferred values are
-- | the same either way.
-- |
-- | `@n` is the most-recent width — the `max_proofs_verified` of the
-- | circuit whose base case is being padded. It sets how many copies
-- | of the step IPA challenges are absorbed into the challenge digest
-- | and how many `sg` eval points precede `cipAllEvals`.
stepDummyUnfinalizedProof
  :: forall @n d sf
   . Reflectable n Int
  => Shifted (F StepField) sf
  => BaseCaseDummies
  -> { domainLog2 :: Int, zkRows :: Int, numChunks :: Int }
  -> Vector d (SizedF 128 (F StepField))
  -> UnfinalizedProof d (F StepField) sf Boolean
stepDummyUnfinalizedProof bcd { domainLog2, zkRows, numChunks } bpChals =
  let
    mostRecentWidth = reflectType (Proxy @n)
    p = bcd.proofDummy.plonk
    -- Every chunk past the first is zero, so the recombined value of
    -- each column is its first chunk: only the fr-sponge and the
    -- combined inner product see the extra chunks.
    evals = bcd.proofDummy.prevEvals
    chunkedEvals = padChunkedEvals numChunks (singleChunkEvals evals)
    Curves.EndoScalar stepEndoScalar = (Curves.endoScalar)

    alphaExpanded = toFieldPure p.alpha stepEndoScalar
    betaExpanded = SizedF.toField p.beta :: StepField
    gammaExpanded = SizedF.toField p.gamma :: StepField
    zetaExpanded = toFieldPure p.zeta stepEndoScalar
    omega = (domainGenerator domainLog2)
    n = pow2 domainLog2
    zetaw = zetaExpanded * omega
    zetaToNMinus1 = Curves.pow zetaExpanded n - one
    -- `(zeta - omega^-1)(zeta - omega^-(zkRows-1))(zeta - omega^-zkRows)`,
    -- at the `zkRows` of the step proof whose evaluations these are.
    omegaToMinusZkRows = Curves.pow omega (n - BigInt.fromInt zkRows)
    omegaToMinusZkPlus1 = Curves.pow omega (n - BigInt.fromInt (zkRows - 1))
    zkPoly = (zetaExpanded - recip omega)
      * (zetaExpanded - omegaToMinusZkPlus1)
      * (zetaExpanded - omegaToMinusZkRows)

    expandedBpChals :: Vector StepIPARounds StepField
    expandedBpChals = map (\c -> toFieldPure c stepEndoScalar) (map coerceViaBits bcd.ipaStepChallenges)

    challengesDigest :: StepField
    challengesDigest =
      let
        sponge0 = initialSponge :: PureSponge.Sponge StepField
        absorbOneCopy s = foldl (\s' c -> PureSponge.absorb c s') s expandedBpChals
        spongeN = Array.foldl (\s _ -> absorbOneCopy s) sponge0 (Array.replicate mostRecentWidth unit)
      in
        (PureSponge.squeeze spongeN).result

    frResult = frSpongeChallengesPureChunked
      { evals: chunkedEvals
      , fqDigest: zero
      , prevChallengeDigest: challengesDigest
      , endo: stepEndoScalar
      }

    permInput =
      { w: map _.zeta (Vector.take @7 evals.witnessEvals)
      , sigma: map _.zeta evals.sigmaEvals
      , z: evals.zEvals
      , shifts: (domainShifts domainLog2)
      , alpha: alphaExpanded
      , beta: betaExpanded
      , gamma: gammaExpanded
      , zkPolynomial: zkPoly
      , zetaToNMinus1
      , omegaToMinusZkRows
      , zeta: zetaExpanded
      }
    perm = permScalar permInput

    permContrib = permContribution permInput
    vanishesOnZk = one :: StepField
    lagrangeFalse0 = unnormalizedLagrangeBasis { domainLog2, zkRows: 0, offset: 0, pt: zetaExpanded }
    lagrangeTrue1 = unnormalizedLagrangeBasis { domainLog2, zkRows, offset: -1, pt: zetaExpanded }
    evalPoint = buildEvalPoint
      { witnessEvals: evals.witnessEvals
      , coeffEvals: map _.zeta evals.coeffEvals
      , indexEvals: evals.indexEvals
      , defaultVal: zero
      }
    challenges_ = buildChallenges
      { alpha: alphaExpanded
      , beta: betaExpanded
      , gamma: gammaExpanded
      , jointCombiner: zero
      , vanishesOnZk
      , lagrangeFalse0
      , lagrangeTrue1
      }
    env = fieldEnv evalPoint challenges_
    gateConstraints = evaluate PallasTokens.constantTermTokens env
    -- `ft_eval0 = permContribution - pEval0Folded - gateConstraints`.
    -- The public evaluation is a single chunk here, so the Horner
    -- fold degenerates to the value itself.
    ftEval0Value = permContrib - evals.publicEvals.zeta - gateConstraints

    ftPointEval :: PointEval StepField
    ftPointEval = { zeta: ftEval0Value, omegaTimesZeta: evals.ftEval1 }

    -- The batch in the verifier's order, each column contributing all
    -- its chunks: public, `ft`, `z`, index, witness, coefficients,
    -- sigma.
    columnChunks :: forall m. Vector m (NonEmptyArray (PointEval StepField)) -> Array (PointEval StepField)
    columnChunks = Array.concatMap NEA.toArray <<< Vector.toUnfoldable

    allEvalsChunked :: Array (PointEval StepField)
    allEvalsChunked =
      NEA.toArray chunkedEvals.publicEvals
        <> [ ftPointEval ]
        <> NEA.toArray chunkedEvals.zEvals
        <> columnChunks chunkedEvals.indexEvals
        <> columnChunks chunkedEvals.witnessEvals
        <> columnChunks chunkedEvals.coeffEvals
        <> columnChunks chunkedEvals.sigmaEvals

    sgPointEval :: PointEval StepField
    sgPointEval = { zeta: bPoly expandedBpChals zetaExpanded, omegaTimesZeta: bPoly expandedBpChals zetaw }
    cipAllEvals = Array.replicate mostRecentWidth sgPointEval <> allEvalsChunked
    cipStep { result, scale } ev =
      let
        term = ev.zeta + frResult.evalscale * ev.omegaTimesZeta
      in
        { result: result + scale * term, scale: scale * frResult.xi }
    cip = (Array.foldl cipStep { result: zero, scale: one } cipAllEvals).result

    b = computeB expandedBpChals { zeta: zetaExpanded, zetaOmega: zetaw, evalscale: frResult.evalscale }

    srsLengthLog2 = reflectType (Proxy :: Proxy StepIPARounds)
    zetaToSrsLength = Curves.pow zetaExpanded (pow2 srsLengthLog2)
    zetaToDomainSize = Curves.pow zetaExpanded n
  in
    { deferredValues:
        { plonk:
            { alpha: SizedF.wrapF p.alpha
            , beta: SizedF.wrapF p.beta
            , gamma: SizedF.wrapF p.gamma
            , zeta: SizedF.wrapF p.zeta
            , perm: toShifted (F perm)
            , zetaToSrsLength: toShifted (F zetaToSrsLength)
            , zetaToDomainSize: toShifted (F zetaToDomainSize)
            }
        , combinedInnerProduct: toShifted (F cip)
        , xi: SizedF.wrapF (coerceViaBits frResult.rawXi)
        , bulletproofChallenges: bpChals
        , b: toShifted (F b)
        }
    , shouldFinalize: false
    , spongeDigestBeforeEvaluations: F (zero)
    }

-- | The wrap-domain log2 for a given `max_proofs_verified`.
wrapDomainLog2ForProofsVerified :: Int -> Int
wrapDomainLog2ForProofsVerified proofsVerified = case proofsVerified of
  0 -> 13
  1 -> 14
  2 -> 15
  _ -> unsafeCrashWith "wrapDomainLog2: proofs_verified must be 0, 1, or 2"

-- | The kimchi-level wrap proof body of a base case.
-- |
-- | It reads `z1`, `z2` and the evaluations out of the passed
-- | `BaseCaseDummies` rather than redrawing them, so the compile's own
-- | `Ro` state stays the single source of truth.
dummyWrapProof
  :: BaseCaseDummies
  -> Proof Pallas.G Vesta.BaseField
dummyWrapProof bcd =
  let
    prf = bcd.proofDummy
    evals = bcd.dummyEvals

    -- The Pallas generator. It is never the point at infinity, so
    -- `toAffine` always gives `Just`.
    g0 = unsafePartial $ fromJust (Curves.toAffine (Curves.generator :: Pallas.G))

    g0XY = [ g0.x, g0.y ]

    wComm = Array.concat (Array.replicate 15 g0XY)

    zComm = g0XY

    -- One per quotient-poly chunk.
    tComm = Array.concat (Array.replicate 7 g0XY)

    -- Laid out flat as `l.x, l.y, r.x, r.y` per round.
    lr = Array.concat (Array.replicate 15 (g0XY <> g0XY))

    delta = g0XY

    sg = g0XY

    -- The kimchi eval order is fixed: the 15 witness evaluations, the
    -- 15 coefficient ones, z, the 6 sigmas, then the 6 index ones.
    flattenVec
      :: forall n
       . Vector n { zeta :: WrapField, omegaTimesZeta :: WrapField }
      -> Array WrapField
    flattenVec v =
      Array.concatMap (\pe -> [ pe.zeta, pe.omegaTimesZeta ])
        (Vector.toUnfoldable v)

    flattenPe :: { zeta :: WrapField, omegaTimesZeta :: WrapField } -> Array WrapField
    flattenPe pe = [ pe.zeta, pe.omegaTimesZeta ]

    evalsFlat =
      flattenVec evals.witnessEvals
        <> flattenVec evals.coeffEvals
        <> flattenPe evals.zEvals
        <> flattenVec evals.sigmaEvals
        <> flattenVec evals.indexEvals
  in
    vestaMakeWireProof
      { wComm
      , zComm
      , tComm
      , lr
      , delta
      , sg
      , z1: prf.z1
      , z2: prf.z2
      , evals: evalsFlat
      , ftEval1: evals.ftEval1
      }

