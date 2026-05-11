-- | Deterministic dummy values for Pickles recursion bootstrapping.
-- |
-- | Mirrors OCaml's `mina/src/lib/pickles/dummy.ml`, `ro.ml`, `unfinalized.ml`.
-- |
-- | Reference: mina/src/lib/pickles/dummy.ml, mina/src/lib/pickles/ro.ml,
-- |            mina/src/lib/pickles/unfinalized.ml
-- | Fixture: packages/pickles/test/fixtures/dummy_values.txt
-- | Generator: mina/src/lib/crypto/pickles/dump_dummy/dump_dummy.ml
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
  ) where

import Prelude

import Control.Monad.State (evalState)
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import JS.BigInt as BigInt
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Pickles.Dummy (RoM, chal, dummyIpaStepChallenges, dummyIpaWrapChallenges, initialRo, pow2, scalarChal, stepEndo, tick, tock, wrapEndo)
import Pickles.Field (StepField, WrapField)
import Pickles.IPA (bPoly, computeB)
import Pickles.Linearization.Env (fieldEnv)
import Pickles.Linearization.FFI (PointEval, domainGenerator, domainShifts, unnormalizedLagrangeBasis)
import Pickles.Linearization.Interpreter (evaluate)
import Pickles.Linearization.Pallas as PallasTokens
import Pickles.PlonkChecks (AllEvals)
import Pickles.PlonkChecks.GateConstraints (buildChallenges, buildEvalPoint)
import Pickles.PlonkChecks.Permutation (permContribution, permScalar)
import Pickles.PlonkChecks.XiCorrect (FrSpongeInput, frSpongeChallengesPure)
import Pickles.Prove.Pure.Common (crossFieldDigest)
import Pickles.Sponge (initialSponge)
import Pickles.Types (PerProofUnfinalized(..), StepIPARounds, WrapIPARounds)
import Pickles.Verify.Types (UnfinalizedProof)
import RandomOracle.Sponge as PureSponge
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Backend.Kimchi.Impl.Vesta as VestaImpl
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F(..), SizedF, UnChecked(..), coerceViaBits)
import Snarky.Circuit.DSL.SizedF (fromField, toField, unwrapF, wrapF) as SizedF
import Snarky.Circuit.Kimchi (toFieldPure)
import Snarky.Curves.Class (EndoScalar(..), endoScalar, fromBigInt, pow) as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (class Shifted, SplitField, Type2(..), fromShifted, toShifted)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | OCaml-primitive Ro-consuming dummies
-- |
-- | 1:1 translations of OCaml's three Ro-consuming dummy constructors:
-- |
-- |   OCaml                           PureScript
-- |   -----                           ----------
-- |   `Dummy.evals`                   → `dummyEvals`
-- |   `Unfinalized.Constant.dummy`    → `unfinalizedConstantDummy`
-- |   `Proof.dummy`                   → `proofDummy`
-- |
-- | Each primitive's output type carries EXACTLY the OCaml record fields
-- | that consume Ro, with field names matched to OCaml. Derived fields
-- | that don't consume Ro (xi, bulletproof_challenges, perm, etc.) are
-- | computed at consumer level from shared data.
-- |
-- | Ro footprint per primitive (fq, fp, chal counters are independent):
-- |
-- |   dummyEvals                89 fq,  0 fp, 0 chal
-- |   unfinalizedConstantDummy   2 fq,  0 fp, 4 chal
-- |   proofDummy                 2 fq, 89 fp, 4 chal
-- |   dummyIpaWrapChallenges     0 fq,  0 fp, 15 chal
-- |   dummyIpaStepChallenges     0 fq,  0 fp, 16 chal
-- |
-- | `computeBaseCaseDummies` composes them in the order OCaml's
-- | `Pickles.compile_promise` forces them for a given `max_proofs_verified`.
-- | Verified empirically from instrumented Simple_chain (N1) and
-- | Tree_proof_return (N2) OCaml dumpers (see `/tmp/audit_sc.stderr`,
-- | `/tmp/audit_tree.stderr`).
-------------------------------------------------------------------------------

-- | OCaml `Dummy.evals : Tock.Field.t All_evals.t` (dummy.ml:6-21).
type DummyEvals = AllEvals WrapField

-- | OCaml `scalar_chal`/`chal` outputs share the plonk record layout
-- | in both `Unfinalized.Constant.dummy` and `Proof.dummy.statement`.
type PlonkChals f =
  { alpha :: SizedF 128 f
  , beta :: SizedF 128 f
  , gamma :: SizedF 128 f
  , zeta :: SizedF 128 f
  }

-- | OCaml `Unfinalized.Constant.dummy : Impls.Step.unfinalized_proof`
-- | (unfinalized.ml:25-106). Only the Ro-consumed fields are captured
-- | here; `xi`, `bulletproof_challenges`, `should_finalize`,
-- | `sponge_digest_before_evaluations`, and `plonk.perm/zetaToSrsLength/
-- | zetaToDomainSize` are pure/derived and reconstructed at consumer level.
type UnfinalizedConstantDummy =
  { plonk :: PlonkChals WrapField
  , combinedInnerProduct :: WrapField -- OCaml: deferred_values.combined_inner_product (raw tock)
  , b :: WrapField -- OCaml: deferred_values.b (raw tock)
  }

-- | OCaml `Proof.dummy : h Nat.t -> r Nat.t -> domain_log2:int -> h t`
-- | (proof.ml:115-211). Captures only the Ro-derived fields; the vector
-- | padding (challenge_polynomial_commitments using `Dummy.Ipa.*.sg`),
-- | `branch_data`, and `g0`-valued commitments are non-Ro and computed
-- | at consumer level.
type ProofDummy =
  { plonk :: PlonkChals StepField
  , z1 :: WrapField -- OCaml: proof.openings.proof.z_1 (tock)
  , z2 :: WrapField -- OCaml: proof.openings.proof.z_2 (tock)
  , prevEvals :: AllEvals StepField
  }

-- | 89 tocks, matching OCaml `dummy.ml:7-21`:
-- |
-- |   Evals.map Evaluation_lengths.default ~f:(fun n ->
-- |     let a () = Array.create ~len:n (Ro.tock ()) in (a (), a ()))
-- |
-- | `Array.create ~len:n (Ro.tock ())` consumes exactly one tock per
-- | `a()` call (the value is replicated, not redrawn), so each Evals
-- | field of shape `(array, array)` costs 2 tocks.
-- | Total: (6 selectors + 6 sigmas + 15 w + 15 coefficients + 1 z
-- |        + 1 public_input) × 2 + 1 ft_eval1 = 89.
-- |
-- | Record/tuple evaluation is right-to-left (OCaml).
dummyEvals :: RoM DummyEvals
dummyEvals =
  let
    pointEval :: RoM (PointEval WrapField)
    pointEval = do
      oz <- tock -- right tuple element first (OCaml RTL)
      z <- tock
      pure { zeta: z, omegaTimesZeta: oz }

    pointEvalVec :: forall @n. Reflectable n Int => RoM (Vector n (PointEval WrapField))
    pointEvalVec = do
      v <- Vector.generateA (const pointEval)
      pure (Vector.reverse v)
  in
    do
      -- Evals record RTL: selectors first, then sigma, z, coefficients, w, public_input, ft_eval1
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

-- | 4 chals + 2 tocks, matching OCaml `unfinalized.ml:25-106`:
-- |
-- |   let alpha = scalar_chal ()    -- LTR let-bindings
-- |   let beta  = chal ()
-- |   let gamma = chal ()
-- |   let zeta  = scalar_chal ()
-- |   ...
-- |   { deferred_values = { plonk = { ... alpha; beta; gamma; zeta }
-- |                       ; combined_inner_product = Shifted_value (tock ())
-- |                       ; ...
-- |                       ; b = Shifted_value (tock ()) }
-- |   ; ... }
-- |
-- | The outer record is constructed RTL, so `b` fires before
-- | `combined_inner_product` when both `tock ()` calls execute.
unfinalizedConstantDummy :: RoM UnfinalizedConstantDummy
unfinalizedConstantDummy = do
  alpha <- scalarChal
  beta <- chal
  gamma <- chal
  zeta <- scalarChal
  -- Record RTL: b first, combined_inner_product second
  b <- tock
  combinedInnerProduct <- tock
  pure { plonk: { alpha, beta, gamma, zeta }, combinedInnerProduct, b }

-- | 2 tocks + 89 ticks + 4 chals, matching OCaml `proof.ml:115-211`.
-- |
-- | Top-level record `T { statement; proof; prev_evals }` evaluation
-- | order (empirically verified from instrumented Simple_chain trace):
-- |   1. `proof` evaluates first — openings.proof.{z_2, z_1} tocks (RTL within openings.proof)
-- |   2. `prev_evals` evaluates second — 89 ticks in the same RTL record layout as `dummyEvals`
-- |   3. `statement` evaluates third — plonk.{zeta, gamma, beta, alpha} chals (RTL)
-- |
-- | `Lazy.force Dummy.evals` fires inside `openings` construction if
-- | not yet forced; for byte-parity with OCaml, callers MUST call
-- | `dummyEvals` before `proofDummy` in any fresh Ro sequence.
proofDummy :: RoM ProofDummy
proofDummy = do
  -- 1. openings.proof.{z_2, z_1} RTL
  z2 <- tock
  z1 <- tock
  -- 2. prev_evals (89 ticks)
  prevEvals <- proofDummyPrevEvals
  -- 3. statement.proof_state.deferred_values.plonk RTL: zeta, gamma, beta, alpha
  zeta <- scalarChal
  gamma <- chal
  beta <- chal
  alpha <- scalarChal
  pure { plonk: { alpha, beta, gamma, zeta }, z1, z2, prevEvals }

-- | Internal: 89 ticks in the same RTL Evals record layout as
-- | `dummyEvals`. Extracted for clarity.
proofDummyPrevEvals :: RoM (AllEvals StepField)
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

-- | Composed base-case dummies. A compile threads its own `Ro` and
-- | calls `computeBaseCaseDummies` to obtain everything needed to pad
-- | base-case slots with Ro-derived values.
type BaseCaseDummies =
  { ipaWrapChallenges :: Vector WrapIPARounds (SizedF 128 WrapField)
  , ipaStepChallenges :: Vector StepIPARounds (SizedF 128 StepField)
  , dummyEvals :: DummyEvals
  , unfinalizedConstantDummy :: UnfinalizedConstantDummy
  , proofDummy :: ProofDummy
  }

-- | Which of `Unfinalized.Constant.dummy` vs `Proof.dummy` does
-- | `Pickles.compile_promise` force first? Verified empirically from
-- | instrumented OCaml runs:
-- |
-- |   max_proofs_verified = 1 (Simple_chain) → Proof.dummy first
-- |   max_proofs_verified = 2 (Tree)         → Unfinalized first
data ForceOrder = UnfinalizedFirst | ProofDummyFirst

forceOrderFor :: { maxProofsVerified :: Int } -> ForceOrder
forceOrderFor { maxProofsVerified } = case maxProofsVerified of
  1 -> ProofDummyFirst
  _ -> UnfinalizedFirst

-- | Pure top-level accessor: the `BaseCaseDummies` for a given circuit
-- | shape. Depends ONLY on `maxProofsVerified` — a definition-time
-- | property, not a compile-derived one. Same bits everywhere the same
-- | N is used.
baseCaseDummies :: { maxProofsVerified :: Int } -> BaseCaseDummies
baseCaseDummies cfg = evalState (computeBaseCaseDummies cfg) initialRo

-- | Sequences IPA challenges + the three Ro-consuming dummies in the
-- | OCaml-correct order for the given circuit shape. Consumers read
-- | the returned `BaseCaseDummies` record by semantic field name; no
-- | swaps or reinterpretation is needed.
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
-- | Consumer-level views over `BaseCaseDummies`. Each takes a
-- | `BaseCaseDummies` produced by `computeBaseCaseDummies` and derives
-- | the expanded / shifted / hashed values step/wrap circuits need.
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

-- | Wrap-side dummy unfinalized proof, mirroring OCaml's
-- | `Unfinalized.Constant.dummy` (unfinalized.ml:25-106).
wrapDummyUnfinalizedProof
  :: BaseCaseDummies
  -> UnfinalizedProof WrapIPARounds (F WrapField) (Type2 (F WrapField)) Boolean
wrapDummyUnfinalizedProof bcd =
  let
    u = bcd.unfinalizedConstantDummy
    evals = bcd.dummyEvals
    Curves.EndoScalar wEndo = (Curves.endoScalar :: Curves.EndoScalar Pallas.ScalarField)

    alphaExpanded = toFieldPure u.plonk.alpha wEndo
    betaExpanded = SizedF.toField u.plonk.beta :: WrapField
    gammaExpanded = SizedF.toField u.plonk.gamma :: WrapField
    zetaExpanded = toFieldPure u.plonk.zeta wEndo

    -- wrap_domains ~proofs_verified:2 = Pow_2_roots_of_unity 15
    wrapDomainLog2 = 15
    zkRows = 3
    omega = (domainGenerator wrapDomainLog2 :: WrapField)
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
      , shifts: (domainShifts wrapDomainLog2 :: Vector 7 WrapField)
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

-- | Cross-field-encoded step-side dummy `PerProofUnfinalized` (value
-- | level). Used by `stepMain` to front-pad the step PI's
-- | `unfinalized_proofs` vector from `len` to `mpvMax`. Mirrors OCaml
-- | `step.ml:782-787`'s `Vector.extend_front ... Unfinalized.dummy`.
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

-- | Step-side dummy unfinalized proof, mirroring OCaml's
-- | `Wrap_deferred_values.expand_deferred` applied to `Proof.dummy`.
-- |
-- | Called at two sites (same deferred values, differing only in d/bpChals):
-- |   Step public-input side (d = WrapIPARounds): bpChals from ipaWrapChallenges
-- |   Step FOP advice side   (d = StepIPARounds): bpChals from ipaStepChallenges
-- |
-- | The `@n` phantom is the `most_recent_width` (= max_proofs_verified of
-- | the circuit whose base case we're padding). It drives how many copies
-- | of `Dummy.Ipa.Step.challenges` get absorbed into the challenges
-- | digest and how many `sg` eval points prepend `cipAllEvals`.
stepDummyUnfinalizedProof
  :: forall @n d sf
   . Reflectable n Int
  => Shifted (F StepField) sf
  => BaseCaseDummies
  -> { domainLog2 :: Int }
  -> Vector d (SizedF 128 (F StepField))
  -> UnfinalizedProof d (F StepField) sf Boolean
stepDummyUnfinalizedProof bcd { domainLog2 } bpChals =
  let
    mostRecentWidth = reflectType (Proxy @n)
    p = bcd.proofDummy.plonk
    evals = bcd.proofDummy.prevEvals
    Curves.EndoScalar stepEndoScalar = (Curves.endoScalar :: Curves.EndoScalar Vesta.ScalarField)

    alphaExpanded = toFieldPure p.alpha stepEndoScalar
    betaExpanded = SizedF.toField p.beta :: StepField
    gammaExpanded = SizedF.toField p.gamma :: StepField
    zetaExpanded = toFieldPure p.zeta stepEndoScalar
    zkRows = 3
    omega = (domainGenerator domainLog2 :: StepField)
    n = pow2 domainLog2
    zetaw = zetaExpanded * omega
    zetaToNMinus1 = Curves.pow zetaExpanded n - one
    omegaM1 = recip omega
    omegaM2 = omegaM1 * omegaM1
    omegaM3 = omegaM2 * omegaM1
    zkPoly = (zetaExpanded - omegaM1) * (zetaExpanded - omegaM2) * (zetaExpanded - omegaM3)
    omegaToMinusZkRows = Curves.pow omega (n - BigInt.fromInt zkRows)

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

    frInput :: FrSpongeInput StepField
    frInput =
      { fqDigest: zero
      , prevChallengeDigest: challengesDigest
      , ftEval1: evals.ftEval1
      , publicEvals: evals.publicEvals
      , zEvals: evals.zEvals
      , indexEvals: evals.indexEvals
      , witnessEvals: evals.witnessEvals
      , coeffEvals: evals.coeffEvals
      , sigmaEvals: evals.sigmaEvals
      , endo: stepEndoScalar
      }
    frResult = frSpongeChallengesPure frInput

    permInput =
      { w: map _.zeta (Vector.take @7 evals.witnessEvals)
      , sigma: map _.zeta evals.sigmaEvals
      , z: evals.zEvals
      , shifts: (domainShifts domainLog2 :: Vector 7 StepField)
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
    -- `ft_eval0 = permContribution - pEval0Folded - gateConstraints`
    -- (mirrors `Pickles.Prove.Pure.Common.ftEval0`). Here the public
    -- evaluation is a single-chunk value (`evals.publicEvals.zeta`), so
    -- the Horner-fold degenerates to the value itself.
    ftEval0Value = permContrib - evals.publicEvals.zeta - gateConstraints

    ftPointEval :: PointEval StepField
    ftPointEval = { zeta: ftEval0Value, omegaTimesZeta: evals.ftEval1 }

    allEvals45 :: Vector 45 (PointEval StepField)
    allEvals45 =
      (evals.publicEvals :< ftPointEval :< evals.zEvals :< Vector.nil)
        `Vector.append` evals.indexEvals
        `Vector.append` evals.witnessEvals
        `Vector.append` evals.coeffEvals
        `Vector.append` evals.sigmaEvals

    sgPointEval :: PointEval StepField
    sgPointEval = { zeta: bPoly expandedBpChals zetaExpanded, omegaTimesZeta: bPoly expandedBpChals zetaw }
    cipAllEvals = Array.replicate mostRecentWidth sgPointEval <> Array.fromFoldable allEvals45
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
    , spongeDigestBeforeEvaluations: F (zero :: StepField)
    }

-- | OCaml `common.ml:25-29` — maps max_proofs_verified to the
-- | `wrap_domains.h` log2 used by step FOP constructions.
wrapDomainLog2ForProofsVerified :: Int -> Int
wrapDomainLog2ForProofsVerified proofsVerified = case proofsVerified of
  0 -> 13
  1 -> 14
  2 -> 15
  _ -> unsafeCrashWith "wrapDomainLog2: proofs_verified must be 0, 1, or 2"

