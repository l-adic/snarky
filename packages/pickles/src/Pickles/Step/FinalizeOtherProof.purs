-- | Discharge, in the step circuit, the deferred values of the wrap
-- | proof it is verifying: that `xi` matches the squeezed challenge,
-- | that `b` and the combined inner product are the claimed ones, and
-- | that the permutation scalar checks out.
-- |
-- | The proof's domain is not known at compile time. Everything that
-- | depends on it — the omega powers, the zk-rows vanishing
-- | polynomial, `zetaToNMinus1` — is therefore computed in-circuit
-- | from a generator masked by the runtime `domain_log2`, either
-- | against the caller's candidate domains or, for a side-loaded
-- | proof, against the `[0..16]` universe.
module Pickles.Step.FinalizeOtherProof
  ( Input
  , finalizeOtherProofCircuit
  , mkSideLoadedOnesPrefixMask
  ) where

import Prelude

import Data.Fin (Finite, getFinite, unsafeFinite)
import Data.Foldable (foldM)
import Data.Int (pow) as Int
import Data.Reflectable (class Reflectable)
import Data.Semigroup.Foldable as Foldable1
import Data.Tuple (Tuple(..), fst)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.DeferredValues (UnfinalizedProof, toPlonkMinimal)
import Pickles.FinalizeOtherProof (DomainMode(..), Output, Params, pow2PowSquare)
import Pickles.IPA (bCorrectCircuit, challengePolyEvals, computeChallenges)
import Pickles.Linearization.Env (AlphaPowersLen, EnvM, buildCircuitEnvM, precomputeAlphaPowers)
import Pickles.Linearization.FFI (class LinearizationFFI, domainGenerator)
import Pickles.Linearization.Interpreter (evaluateM)
import Pickles.Linearization.Types (runLinearizationPoly)
import Pickles.PlonkChecks (buildEvalList, buildEvalPoint, combinedInnerProduct, extractEvalFields, knownDomainVanishingPolynomial, knownDomainWhiches, maskedChallengeDigest, omegaPowers, permContributionCircuit, permScalarCircuit, squeezeXiR, zkPolynomial)
import Pickles.Pseudo as Pseudo
import Pickles.Types (Evals)
import Poseidon (class PoseidonField)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (BoolVar, FVar, Snarky, all_, and_, assertAny_, const_, equals_, if_, label, mul_, not_, pow_, square_, sub_, true_)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (toField)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, class PrimeField, fromInt)

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

-- | Size of the side-loaded domain universe: 17, covering log2s
-- | `[0..16]`.
type SideLoadedDomainCount = 17

sideLoadedDomainLog2Max :: Int
sideLoadedDomainLog2Max = 16

-- | The side-loaded candidate log2s, `[0..16]`.
sideLoadedLog2s :: Vector SideLoadedDomainCount Int
sideLoadedLog2s = Vector.generate getFinite

-- | The generator of each side-loaded candidate domain, as constants.
sideLoadedGenerators :: forall f. LinearizationFFI f => Vector SideLoadedDomainCount (FVar f)
sideLoadedGenerators = map (const_ <<< domainGenerator) sideLoadedLog2s

-- | The domain-mode dispatch, resolved once: what `maskedGen` and the
-- | vanishing polynomial select on. `Known` carries one which-bit per
-- | compile-time candidate domain; `SideLoaded` carries the
-- | ones-prefix mask the iterative vanishing polynomial squares
-- | against, plus the one-hot which-bits over the `[0..16]` universe.
data DomainSel nd f
  = Known (Vector nd (BoolVar f))
  | SideLoaded
      { onesPrefix :: Vector 16 (BoolVar f)
      , whiches :: Vector SideLoadedDomainCount (BoolVar f)
      }

-- | Everything `finalizeOtherProofCircuit` reads about the proof it
-- | is finalizing.
type Input n d f sf b =
  { -- | The deferred values, from the proof's public input.
    unfinalized :: UnfinalizedProof d f sf b
  -- | The proof's polynomial evaluations, as private witness. The
  -- | opening proof belongs to `incrementally_verify_proof`, not here.
  , allEvals :: Evals f
  -- | Proofs-verified mask, for the CIP and the challenge digest.
  , mask :: Vector n b
  -- | The previous proofs' bulletproof challenges, already expanded
  -- | to full field elements.
  , prevChallenges :: Vector n (Vector d f)
  -- | The proof's `domain_log2`, a runtime variable from the public
  -- | input.
  , domainLog2Var :: f
  }

-------------------------------------------------------------------------------
-- | Circuit
-------------------------------------------------------------------------------

-- | Check the wrap proof's deferred values, returning their
-- | conjunction alongside each individual outcome.
-- |
-- | `ops` supplies the shifted-value operations for the caller's
-- | representation; `params` fixes the candidate domains, the shifts,
-- | `zkRows` and the linearization polynomial.
finalizeOtherProofCircuit
  :: forall d dPred nd ndPred n f f' r sf r1 r2
   . Add 1 dPred d
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Reflectable nd Int
  => PrimeField f
  => FieldSizeInBits f 255
  => PoseidonField f
  => HasEndo f f'
  => LinearizationFFI f
  => Reflectable d Int
  => { unshift :: sf -> FVar f
     , shiftedEqual :: sf -> FVar f -> Snarky f (KimchiConstraint f) r (BoolVar f)
     | r1
     }
  -> Params nd f r2
  -> Input n d (FVar f) sf (BoolVar f)
  -> Snarky f (KimchiConstraint f) r (Output d f)
finalizeOtherProofCircuit ops params { unfinalized, allEvals, mask, prevChallenges, domainLog2Var } = label "finalize-other-proof" do
  -- Each candidate domain past the first costs one extra `equals_`
  -- for its mask bit and one extra multiplication in the
  -- vanishing-polynomial mask.
  let
    -- The largest log2 any candidate domain can take, which sizes the
    -- vanishing polynomial's tower of squarings. In side-loaded mode
    -- the universe is fixed at `[0..16]`, so it is 16 whatever
    -- `params.domains` says. The `Foldable1` maximum is total because
    -- `Add 1 ndPred nd` forces `nd ≥ 1`.
    maxLog2 = case params.domainMode of
      KnownDomainsMode -> Foldable1.maximum (map _.log2 params.domains)
      SideLoadedMode -> sideLoadedDomainLog2Max
    -- `buildCircuitEnvM` takes a single Int domain log2, and the
    -- maximum is what a multi-candidate domain reports as its size.
    domainLog2 = maxLog2
    -- The shifts are the same for every candidate domain.
    domain = { shifts: params.shifts }
  let
    deferred = unfinalized.deferredValues
    endoVar = const_ params.endo

  ---------------------------------------------------------------------------
  -- Expand alpha and zeta through the endomorphism. The order is
  -- fixed: `zeta` is expanded before `alpha`.
  ---------------------------------------------------------------------------
  let plonkMin = toPlonkMinimal deferred.plonk
  zeta <- toField @8 plonkMin.zeta endoVar
  alpha <- toField @8 plonkMin.alpha endoVar
  let beta = SizedF.toField plonkMin.beta
  let gamma = SizedF.toField plonkMin.gamma

  ---------------------------------------------------------------------------
  -- `maskedGen` is a linear combination of constants scaled by mask
  -- bits, so it costs no Generic gate; it is non-constant though, so
  -- `mul_ maskedGen zeta` costs one.
  ---------------------------------------------------------------------------
  domainSel <- case params.domainMode of
    -- One which-bit per candidate domain, emitted last domain first.
    KnownDomainsMode -> Known <$> knownDomainWhiches domainLog2Var params.domains
    -- Order is fixed here: the ones-prefix mask first (16 `equals_`
    -- and 16 `and_`), then the 17 one-hot which-bits over `[0..16]`
    -- descending, then the one-hot assertion. No compile-time domain
    -- data enters.
    SideLoadedMode -> do
      onesPrefix <- mkSideLoadedOnesPrefixMask domainLog2Var
      whiches <- knownDomainWhiches domainLog2Var (map { log2: _ } sideLoadedLog2s)
      assertAny_ (Vector.toUnfoldable whiches)
      pure (SideLoaded { onesPrefix, whiches })

  maskedGen <- case domainSel of
    Known whiches -> Pseudo.mask whiches (map _.generator params.domains)
    SideLoaded { whiches } -> Pseudo.mask whiches sideLoadedGenerators
  zetaw <- mul_ maskedGen zeta

  ---------------------------------------------------------------------------
  -- Challenge polynomial evaluations (sg_evals). The order is fixed:
  -- `zetaw` is evaluated before `zeta`.
  ---------------------------------------------------------------------------
  sgZetaw <- challengePolyEvals prevChallenges zetaw
  sgZeta <- challengePolyEvals prevChallenges zeta

  ---------------------------------------------------------------------------
  -- Sponge: absorb the digests and the evaluations, squeeze xi and r.
  ---------------------------------------------------------------------------
  { xi: xiActual, r: rActual } <- squeezeXiR
    { spongeDigestBeforeEvaluations: unfinalized.spongeDigestBeforeEvaluations
    , challengeDigest: maskedChallengeDigest mask prevChallenges
    , allEvals
    , endo: endoVar
    , xiConstrainLowBits: true
    }
  xiCorrect <- equals_ (SizedF.toField xiActual) (SizedF.toField deferred.xi)
  xi <- toField @8 deferred.xi endoVar
  r <- toField @8 rActual endoVar

  ---------------------------------------------------------------------------
  -- The values are discarded; what matters is the `Square`
  -- constraints they emit. The exponent is `srsLengthLog2`, not
  -- `domainLog2`.
  ---------------------------------------------------------------------------
  void $ pow2PowSquare zeta params.srsLengthLog2
  void $ pow2PowSquare zetaw params.srsLengthLog2

  ---------------------------------------------------------------------------
  -- PlonK env and ft_eval0. The alpha powers are shared with
  -- `permScalarCircuit` below, and the emission order is fixed: alpha
  -- powers, then the omega powers, then `zkPoly`, then
  -- `zetaToNMinus1`, then the terms.
  ---------------------------------------------------------------------------
  let
    pEval0 = allEvals.publicEvals.zeta

    evalPoint = buildEvalPoint
      { witnessEvals: allEvals.witnessEvals
      , coeffEvals: map _.zeta allEvals.coeffEvals
      , indexEvals: allEvals.indexEvals
      , defaultVal: const_ zero
      }

    w0 :: Vector 15 (FVar f)
    w0 = map _.zeta allEvals.witnessEvals

    s0 :: Vector 6 (FVar f)
    s0 = map _.zeta allEvals.sigmaEvals

    zZeta = allEvals.zEvals.zeta
    zOmegaTimesZeta = allEvals.zEvals.omegaTimesZeta

    shifts = domain.shifts

  alphaPowers <- precomputeAlphaPowers alpha

  ---------------------------------------------------------------------------
  -- Omega powers in-circuit. `maskedGen` is non-constant, so each
  -- power costs constraints.
  ---------------------------------------------------------------------------
  omegas@{ omegaToMinus1: omegaM1, omegaToZkPlus1: omegaZkP1, omegaToZk: omegaZk } <-
    omegaPowers { generator: maskedGen, zkRows: params.zkRows }
  zkPoly <- zkPolynomial zeta omegas

  -- `zetaToNMinus1`, from the vanishing polynomial of whichever
  -- candidate domain the which-bits select.
  zetaToNMinus1 <- label "domain-vanishing-poly" case domainSel of
    Known whiches -> knownDomainVanishingPolynomial whiches params.domains zeta
    SideLoaded { onesPrefix } -> do
      -- The result is deliberately left unsealed, a bare `acc - 1`.
      -- Sealing it would emit one more Generic gate and throw off the
      -- Generic-pair queue parity at the start of `ft_eval0`;
      -- downstream `mul_`s materialize it as needed.
      acc <- foldM
        ( \accV bit -> do
            sq <- square_ accV
            if_ bit sq accV
        )
        zeta
        onesPrefix
      pure (acc `sub_` const_ one)

  let
    alphaPow n = Vector.index alphaPowers (unsafeFinite @AlphaPowersLen n)
    a21 = alphaPow 21
    a22 = alphaPow 22
    a23 = alphaPow 23

  -- The permutation half of `ft_eval0`. `permContributionCircuit` is
  -- shared with the wrap verifier, and `omegaToMinusZkRows` is the
  -- circuit variable `omegaZk`, not a constant.
  permResult <- permContributionCircuit
    { w: Vector.take @7 w0
    , sigma: s0
    , z: { zeta: zZeta, omegaTimesZeta: zOmegaTimesZeta }
    , shifts
    , alpha
    , beta
    , gamma
    , zkPolynomial: zkPoly
    , zetaToNMinus1
    , omegaToMinusZkRows: omegaZk
    , zeta
    }
    { pEval0, alphaPow21: a21, alphaPow22: a22, alphaPow23: a23 }

  let
    omegaForLagrange { zkRows: zk, offset } =
      if not zk && offset == 0 then const_ one
      else if not zk && offset == 1 then maskedGen
      else if not zk && offset == (-1) then omegaM1
      else if not zk && offset == (-2) then omegaZkP1
      else if not zk && offset == (-3) then omegaZk
      else if zk && offset == 0 then omegaZk
      -- No constant-term token asks for the `(zk, -1)` case.
      else const_ one

    vanishesOnZk = const_ one

    baseEnv :: EnvM f (Snarky f (KimchiConstraint f) r)
    baseEnv = buildCircuitEnvM
      alphaPowers
      zeta
      domainLog2
      omegaForLagrange
      evalPoint
      vanishesOnZk
      beta
      gamma
      (const_ one) -- jointCombiner (None → 1)
    env = baseEnv { computeZetaToNMinus1 = pure zetaToNMinus1 }

  -- Labelled `scalars_env` so the per-label gate totals line up.
  constantTerm <- label "scalars_env" $
    evaluateM (runLinearizationPoly params.linearizationPoly) env

  let ftEval0 = sub_ permResult constantTerm

  ---------------------------------------------------------------------------
  -- Combined inner product. The `zetaw` combination is evaluated
  -- before the `zeta` one.
  ---------------------------------------------------------------------------
  actualCip <- combinedInnerProduct
    { xi
    , r
    , evalsZeta: buildEvalList
        { sgEvals: Vector.zipWith Tuple mask sgZeta
        , publicInput: allEvals.publicEvals.zeta
        , ftEval: ftEval0
        , evals: extractEvalFields _.zeta allEvals
        }
    , evalsZetaw: buildEvalList
        { sgEvals: Vector.zipWith Tuple mask sgZetaw
        , publicInput: allEvals.publicEvals.omegaTimesZeta
        , ftEval: allEvals.ftEval1
        , evals: extractEvalFields _.omegaTimesZeta allEvals
        }
    }
  let expectedCip = ops.unshift deferred.combinedInnerProduct
  cipCorrect <- equals_ expectedCip actualCip

  ---------------------------------------------------------------------------
  -- b_correct. Expand the bulletproof challenges through the
  -- endomorphism.
  ---------------------------------------------------------------------------
  expandedChallenges <- computeChallenges deferred.bulletproofChallenges endoVar

  bCorrect <- label "b_correct" $ bCorrectCircuit
    { challenges: expandedChallenges
    , zeta
    , zetaOmega: zetaw
    , evalscale: r
    , expectedB: ops.unshift deferred.b
    }

  ---------------------------------------------------------------------------
  -- perm_correct, reusing the shared alpha powers and `zkPoly`.
  ---------------------------------------------------------------------------
  actualPerm <- label "perm_actual" $ permScalarCircuit
    { w: Vector.take @6 w0
    , sigma: s0
    , zOmega: zOmegaTimesZeta
    , beta
    , gamma
    , zkPolynomial: zkPoly
    , alphaPow21: a21
    }

  -- Emitted for its constraints; the value is discarded.
  label "perm_pow_zeta_srs" $ void $ pow_ zeta (Int.pow 2 params.srsLengthLog2)

  plonkOk <- label "perm_shifted_equal"
    $ ops.shiftedEqual deferred.plonk.perm actualPerm

  finalized <- all_ [ xiCorrect, bCorrect, cipCorrect, plonkOk ]

  let challenges = deferred.bulletproofChallenges

  pure { finalized, xiCorrect, bCorrect, cipCorrect, plonkOk, challenges, expandedChallenges }

-------------------------------------------------------------------------------
-- | Side-loaded helpers
-------------------------------------------------------------------------------

-- | A 16-bit mask whose bit `i` is true exactly when `i` is below the
-- | runtime `first_zero`: the ones-prefix the side-loaded vanishing
-- | polynomial squares against. One `equals_` and one `and_` per bit,
-- | 32 gates.
mkSideLoadedOnesPrefixMask
  :: forall f r
   . PrimeField f
  => FVar f
  -> Snarky f (KimchiConstraint f) r (Vector 16 (BoolVar f))
mkSideLoadedOnesPrefixMask first_zero = label "ones_prefix_mask" do
  let
    indices :: Vector 16 (Finite 16)
    indices = Vector.generate identity
  map fst $ mapAccumM
    ( \prev fi -> do
        let i = getFinite fi
        eq <- equals_ first_zero (const_ (fromInt i))
        newAcc <- (and_ prev) (not_ eq)
        pure (Tuple newAcc newAcc)
    )
    true_
    indices
