-- | Generic step_main circuit for Pickles recursion.
-- |
-- | Parameterized by `n` (number of previous proofs / max_proofs_verified).
-- | Both Simple_Chain N1 and N2 are specializations of `stepMain`.
-- |
-- | Uses Effect as the base monad with throwing advice for compilation safety:
-- | during circuit compilation, `exists` ignores its argument (CircuitBuilderT),
-- | so the Effect throw never fires. But if a bug causes the prover computation
-- | to be evaluated during compilation, we get a clear error.
-- |
-- | Reference: mina/src/lib/crypto/pickles/step_main.ml
-- |            mina/src/lib/crypto/pickles/dump_circuit_impl.ml
module Pickles.Step.Main
  ( -- * Advice
    advice
  -- * Rule abstraction
  , RuleOutput
  -- * Generic step_main
  , StepMainSrsData
  , stepMain
  , compileStepMain
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Array as Array
import Data.Foldable (foldM, foldMap)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (!!))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBase)
import Pickles.Sponge (initialSpongeCircuit)
import Pickles.Step.Advice (class StepWitnessM, getWrapVerifierIndex)
import Pickles.Step.VerifyOne (VerifyOneInput, verifyOne)
import Pickles.Types (StepField, StepIPARounds, VerificationKey(..), WrapIPARounds)
import Safe.Coerce (coerce)
import Snarky.Backend.Builder (CircuitBuilderState)
import Effect (Effect)
import Effect.Unsafe (unsafePerformEffect)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitM, AsProverT, Bool(..), BoolVar, EvaluationError(..), F, FVar, Snarky, UnChecked(..), assertAll_, const_, exists, label, throwAsProver)
import Snarky.Circuit.DSL.SizedF (SizedF, toField, unsafeMkSizedF)
import Snarky.Circuit.Kimchi (SplitField(..), Type1(..), Type2(..), groupMapParams)
import Snarky.Circuit.Kimchi.EndoScalar (toField) as EndoScalar
import Snarky.Circuit.RandomOracle.Sponge as Sponge
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (EndoScalar(..), curveParams, endoScalar)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Advice: throwing prover computation for compilation safety
-- |
-- | During circuit compilation (CircuitBuilderT), `exists` ignores its
-- | AsProverT argument entirely. This `advice` throws at the Effect level
-- | if somehow evaluated — a safety net against bugs.
-------------------------------------------------------------------------------

advice :: forall f m a. Monad m => AsProverT f m a
advice = throwAsProver (FailedAssertion "advice: evaluated during compilation (bug)")

-------------------------------------------------------------------------------
-- | Rule abstraction
-------------------------------------------------------------------------------

type RuleOutput n f =
  { prevPublicInputs :: Vector n (FVar f)
  , proofMustVerify :: Vector n (BoolVar f)
  }

-------------------------------------------------------------------------------
-- | SRS data for step_main
-------------------------------------------------------------------------------

type StepMainSrsData =
  { lagrangeComms :: Array (LagrangeBase StepField)
  , blindingH :: AffinePoint (F StepField)
  }

-------------------------------------------------------------------------------
-- | Helpers
-------------------------------------------------------------------------------

unwrapPt :: WeierstrassAffinePoint PallasG (FVar StepField) -> AffinePoint (FVar StepField)
unwrapPt (WeierstrassAffinePoint pt) = pt

stepEndoVal :: StepField
stepEndoVal = let EndoScalar e = endoScalar @Vesta.BaseField @StepField in e

-------------------------------------------------------------------------------
-- | Per-proof witness allocation
-- |
-- | Allocates one per-proof witness in OCaml's exact hlist order.
-- | Each `exists advice` call allocates variables sequentially; the order
-- | of calls determines the variable index assignment.
-- |
-- | OCaml Per_proof_witness hlist:
-- |   [statement(Unit), Wrap_proof(Messages+Bulletproof), Proof_state,
-- |    All_evals, prev_challenges, prev_sgs]
-- |
-- | Proof_state uses Typ.transport ~there:to_data order:
-- |   fq=[cip,b,zetaToSrs,zetaToDom,perm], digest=[sponge],
-- |   challenge=[beta,gamma], scalar_challenge=[alpha,zeta,xi], bpChals(16)
-- |   + branch_data(mask0,mask1,domLog2) at end
-------------------------------------------------------------------------------

type PerProofWitness n =
  { wComm :: Vector 15 (WeierstrassAffinePoint PallasG (FVar StepField))
  , zComm :: WeierstrassAffinePoint PallasG (FVar StepField)
  , tComm :: Vector 7 (WeierstrassAffinePoint PallasG (FVar StepField))
  , lr :: Vector 15 { l :: WeierstrassAffinePoint PallasG (FVar StepField), r :: WeierstrassAffinePoint PallasG (FVar StepField) }
  , z1 :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
  , z2 :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
  , delta :: WeierstrassAffinePoint PallasG (FVar StepField)
  , sg :: WeierstrassAffinePoint PallasG (FVar StepField)
  , fopState ::
      { plonk ::
          { alpha :: SizedF 128 (FVar StepField)
          , beta :: SizedF 128 (FVar StepField)
          , gamma :: SizedF 128 (FVar StepField)
          , zeta :: SizedF 128 (FVar StepField)
          , perm :: Type1 (FVar StepField)
          , zetaToSrsLength :: Type1 (FVar StepField)
          , zetaToDomainSize :: Type1 (FVar StepField)
          }
      , combinedInnerProduct :: Type1 (FVar StepField)
      , b :: Type1 (FVar StepField)
      , xi :: SizedF 128 (FVar StepField)
      , bulletproofChallenges :: Vector 16 (SizedF 128 (FVar StepField))
      , spongeDigest :: FVar StepField
      }
  , allEvals ::
      { ftEval1 :: FVar StepField
      , publicEvals :: { zeta :: FVar StepField, omegaTimesZeta :: FVar StepField }
      , witnessEvals :: Vector 15 { zeta :: FVar StepField, omegaTimesZeta :: FVar StepField }
      , coeffEvals :: Vector 15 { zeta :: FVar StepField, omegaTimesZeta :: FVar StepField }
      , zEvals :: { zeta :: FVar StepField, omegaTimesZeta :: FVar StepField }
      , sigmaEvals :: Vector 6 { zeta :: FVar StepField, omegaTimesZeta :: FVar StepField }
      , indexEvals :: Vector 6 { zeta :: FVar StepField, omegaTimesZeta :: FVar StepField }
      }
  , branchData :: { mask0 :: BoolVar StepField, mask1 :: BoolVar StepField, domainLog2Var :: FVar StepField }
  , prevChallenges :: Vector n (Vector 16 (FVar StepField))
  , prevSgs :: Vector n (WeierstrassAffinePoint PallasG (FVar StepField))
  }

allocatePerProofWitness
  :: forall @n t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Reflectable n Int
  => Snarky (KimchiConstraint StepField) t m (PerProofWitness n)
allocatePerProofWitness = do
  -- 1. Wrap_proof.Messages
  wComm <- exists (advice :: _ (Vector 15 (WeierstrassAffinePoint PallasG (F StepField))))
  zComm <- exists (advice :: _ (WeierstrassAffinePoint PallasG (F StepField)))
  tComm <- exists (advice :: _ (Vector 7 (WeierstrassAffinePoint PallasG (F StepField))))

  -- 2. Wrap_proof.Bulletproof
  lr <- exists (advice :: _ (Vector 15 { l :: WeierstrassAffinePoint PallasG (F StepField), r :: WeierstrassAffinePoint PallasG (F StepField) }))
  z1 <- exists (advice :: _ (Type2 (SplitField (F StepField) Boolean)))
  z2 <- exists (advice :: _ (Type2 (SplitField (F StepField) Boolean)))
  delta <- exists (advice :: _ (WeierstrassAffinePoint PallasG (F StepField)))
  sg <- exists (advice :: _ (WeierstrassAffinePoint PallasG (F StepField)))

  -- 3. Proof_state in to_data order
  psCip <- exists (advice :: _ (F StepField))
  psB <- exists (advice :: _ (F StepField))
  psZetaToSrs <- exists (advice :: _ (F StepField))
  psZetaToDom <- exists (advice :: _ (F StepField))
  psPerm <- exists (advice :: _ (F StepField))
  psSponge <- exists (advice :: _ (F StepField))
  psBeta <- exists (advice :: _ (F StepField))
  psGamma <- exists (advice :: _ (F StepField))
  psAlpha <- exists (advice :: _ (F StepField))
  psZeta <- exists (advice :: _ (F StepField))
  psXi <- exists (advice :: _ (F StepField))
  psBpChals :: Vector 16 (FVar StepField) <- exists (advice :: _ (Vector 16 (F StepField)))

  -- Branch_data: mask0(bool), mask1(bool), domLog2(field + endoscalar)
  bdMask0 :: BoolVar StepField <- exists (advice :: _ Boolean)
  bdMask1 :: BoolVar StepField <- exists (advice :: _ Boolean)
  domLog2 <- exists (advice :: _ (F StepField))
  _ <- EndoScalar.toField @1 (unsafeMkSizedF domLog2 :: SizedF 16 (FVar StepField)) (const_ stepEndoVal)

  let
    fopState =
      { plonk:
          { alpha: unsafeMkSizedF psAlpha :: SizedF 128 (FVar StepField)
          , beta: unsafeMkSizedF psBeta :: SizedF 128 (FVar StepField)
          , gamma: unsafeMkSizedF psGamma :: SizedF 128 (FVar StepField)
          , zeta: unsafeMkSizedF psZeta :: SizedF 128 (FVar StepField)
          , perm: Type1 psPerm
          , zetaToSrsLength: Type1 psZetaToSrs
          , zetaToDomainSize: Type1 psZetaToDom
          }
      , combinedInnerProduct: Type1 psCip
      , b: Type1 psB
      , xi: unsafeMkSizedF psXi :: SizedF 128 (FVar StepField)
      , bulletproofChallenges: map unsafeMkSizedF psBpChals :: Vector 16 (SizedF 128 (FVar StepField))
      , spongeDigest: psSponge
      }

  -- 4. All_evals in OCaml hlist order
  let toPair (Tuple z oz) = { zeta: z, omegaTimesZeta: oz }
  publicEvalsZ <- exists (advice :: _ (F StepField))
  publicEvalsOZ <- exists (advice :: _ (F StepField))
  witnessEvalsRaw <- exists (advice :: _ (Vector 15 (Tuple (F StepField) (F StepField))))
  coeffEvalsRaw <- exists (advice :: _ (Vector 15 (Tuple (F StepField) (F StepField))))
  zEvalsZ <- exists (advice :: _ (F StepField))
  zEvalsOZ <- exists (advice :: _ (F StepField))
  sigmaEvalsRaw <- exists (advice :: _ (Vector 6 (Tuple (F StepField) (F StepField))))
  indexEvalsRaw <- exists (advice :: _ (Vector 6 (Tuple (F StepField) (F StepField))))
  ftEval1 <- exists (advice :: _ (F StepField))
  let
    allEvals =
      { ftEval1
      , publicEvals: { zeta: publicEvalsZ, omegaTimesZeta: publicEvalsOZ }
      , witnessEvals: map toPair witnessEvalsRaw
      , coeffEvals: map toPair coeffEvalsRaw
      , zEvals: { zeta: zEvalsZ, omegaTimesZeta: zEvalsOZ }
      , sigmaEvals: map toPair sigmaEvalsRaw
      , indexEvals: map toPair indexEvalsRaw
      }

  -- 5. prev_challenges: n sets of 16 (UnChecked)
  prevChalVecs <- Vector.generateA @n \_ -> do
    uc <- exists (advice :: _ (UnChecked (Vector 16 (F StepField))))
    let UnChecked v = uc
    pure v

  -- 6. prev_sgs: n curve points
  prevSgs <- Vector.generateA @n \_ ->
    exists (advice :: _ (WeierstrassAffinePoint PallasG (F StepField)))

  pure
    { wComm
    , zComm
    , tComm
    , lr
    , z1
    , z2
    , delta
    , sg
    , fopState
    , allEvals
    , branchData: { mask0: bdMask0, mask1: bdMask1, domainLog2Var: domLog2 }
    , prevChallenges: prevChalVecs
    , prevSgs
    }

-------------------------------------------------------------------------------
-- | Unfinalized proof allocation
-------------------------------------------------------------------------------

type UnfinalizedProof =
  { deferredValues ::
      { plonk ::
          { alpha :: SizedF 128 (FVar StepField)
          , beta :: SizedF 128 (FVar StepField)
          , gamma :: SizedF 128 (FVar StepField)
          , zeta :: SizedF 128 (FVar StepField)
          , perm :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
          , zetaToSrsLength :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
          , zetaToDomainSize :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
          }
      , combinedInnerProduct :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
      , b :: Type2 (SplitField (FVar StepField) (BoolVar StepField))
      , xi :: SizedF 128 (FVar StepField)
      , bulletproofChallenges :: Vector 15 (SizedF 128 (FVar StepField))
      }
  , shouldFinalize :: BoolVar StepField
  , claimedDigest :: FVar StepField
  }

allocateUnfinalized
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Snarky (KimchiConstraint StepField) t m UnfinalizedProof
allocateUnfinalized = do
  -- OCaml to_data order: fq(5×Type2), digest, challenge(2), scalar_challenge(3), bpChals(15), bool
  unfCip <- exists (advice :: _ (Type2 (SplitField (F StepField) Boolean)))
  unfB <- exists (advice :: _ (Type2 (SplitField (F StepField) Boolean)))
  unfZetaToSrs <- exists (advice :: _ (Type2 (SplitField (F StepField) Boolean)))
  unfZetaToDom <- exists (advice :: _ (Type2 (SplitField (F StepField) Boolean)))
  unfPerm <- exists (advice :: _ (Type2 (SplitField (F StepField) Boolean)))
  unfClaimedDigest <- exists (advice :: _ (F StepField))
  unfBeta <- exists (advice :: _ (F StepField))
  unfGamma <- exists (advice :: _ (F StepField))
  unfAlpha <- exists (advice :: _ (F StepField))
  unfZeta <- exists (advice :: _ (F StepField))
  unfXi <- exists (advice :: _ (F StepField))
  unfBpChals :: Vector 15 (FVar StepField) <- exists (advice :: _ (Vector 15 (F StepField)))
  unfShouldFinalize :: BoolVar StepField <- exists (advice :: _ Boolean)
  pure
    { deferredValues:
        { plonk:
            { alpha: unsafeMkSizedF unfAlpha :: SizedF 128 (FVar StepField)
            , beta: unsafeMkSizedF unfBeta :: SizedF 128 (FVar StepField)
            , gamma: unsafeMkSizedF unfGamma :: SizedF 128 (FVar StepField)
            , zeta: unsafeMkSizedF unfZeta :: SizedF 128 (FVar StepField)
            , perm: unfPerm
            , zetaToSrsLength: unfZetaToSrs
            , zetaToDomainSize: unfZetaToDom
            }
        , combinedInnerProduct: unfCip
        , b: unfB
        , xi: unsafeMkSizedF unfXi :: SizedF 128 (FVar StepField)
        , bulletproofChallenges: map unsafeMkSizedF unfBpChals :: Vector 15 (SizedF 128 (FVar StepField))
        }
    , shouldFinalize: unfShouldFinalize
    , claimedDigest: unfClaimedDigest
    }

-------------------------------------------------------------------------------
-- | Build verify_one input from allocated witnesses
-------------------------------------------------------------------------------

buildVerifyOneInput
  :: forall @n
   . Reflectable n Int
  => PerProofWitness n
  -> FVar StepField
  -> BoolVar StepField
  -> UnfinalizedProof
  -> FVar StepField
  -> { sigma :: Vector 6 (AffinePoint (FVar StepField))
     , sigmaLast :: AffinePoint (FVar StepField)
     , coeff :: Vector 15 (AffinePoint (FVar StepField))
     , index :: Vector 6 (AffinePoint (FVar StepField))
     }
  -> AffinePoint (FVar StepField) -- dummySg for padding
  -> VerifyOneInput n 15 16 (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (FVar StepField) (BoolVar StepField)
buildVerifyOneInput pw appState mustVerify unfinalized msgWrap vkComms dummySg =
  let
    -- sgOld: pad prevSgs to Vector 2 (Wrap_hack.Padded_length)
    -- extend_front puts padding at front: [dummy..., sg0, sg1, ...]
    n = reflectType (Proxy @n)
    sgArr = map unwrapPt (Vector.toUnfoldable pw.prevSgs :: Array _)
    paddedSgArr = Array.replicate (2 - n) dummySg <> sgArr
    sgOld = unsafePartial $ fromJust $ Vector.toVector @2 paddedSgArr

    -- proofMask: last n elements of [mask0, mask1]
    maskArr = Array.drop (2 - n) [ pw.branchData.mask0, pw.branchData.mask1 ]
    proofMask = unsafePartial $ fromJust $ Vector.toVector @n maskArr
  in
    { appState
    , wComm: map unwrapPt pw.wComm
    , zComm: unwrapPt pw.zComm
    , tComm: map unwrapPt pw.tComm
    , lr: map (\r -> { l: unwrapPt r.l, r: unwrapPt r.r }) pw.lr
    , z1: pw.z1
    , z2: pw.z2
    , delta: unwrapPt pw.delta
    , sg: unwrapPt pw.sg
    , proofState:
        { plonk: pw.fopState.plonk
        , combinedInnerProduct: pw.fopState.combinedInnerProduct
        , b: pw.fopState.b
        , xi: pw.fopState.xi
        , bulletproofChallenges: pw.fopState.bulletproofChallenges
        , spongeDigest: pw.fopState.spongeDigest
        }
    , allEvals: pw.allEvals
    , prevChallenges: pw.prevChallenges
    , prevSgs: map unwrapPt pw.prevSgs
    , unfinalized
    , messagesForNextWrapProof: msgWrap
    , mustVerify
    , branchData:
        { mask0: coerce pw.branchData.mask0 :: FVar StepField
        , mask1: coerce pw.branchData.mask1 :: FVar StepField
        , domainLog2Var: pw.branchData.domainLog2Var
        }
    , proofMask
    , vkComms
    , sgOld
    }

-------------------------------------------------------------------------------
-- | Serialize unfinalized proof to output fields (to_data order)
-------------------------------------------------------------------------------

unfFields :: UnfinalizedProof -> Array (FVar StepField)
unfFields unf =
  let
    sf2 (Type2 (SplitField { sDiv2, sOdd })) = [ sDiv2, coerce sOdd :: FVar StepField ]
  in
    sf2 unf.deferredValues.combinedInnerProduct
      <> sf2 unf.deferredValues.b
      <> sf2 unf.deferredValues.plonk.zetaToSrsLength
      <> sf2 unf.deferredValues.plonk.zetaToDomainSize
      <> sf2 unf.deferredValues.plonk.perm
      <> [ unf.claimedDigest ]
      <>
        [ toField unf.deferredValues.plonk.beta
        , toField unf.deferredValues.plonk.gamma
        ]
      <>
        [ toField unf.deferredValues.plonk.alpha
        , toField unf.deferredValues.plonk.zeta
        , toField unf.deferredValues.xi
        ]
      <> (Vector.toUnfoldable (map toField unf.deferredValues.bulletproofChallenges) :: Array _)
      <> [ coerce unf.shouldFinalize :: FVar StepField ]

-------------------------------------------------------------------------------
-- | Generic step_main circuit
-- |
-- | Parameterized by:
-- | - @n: number of previous proofs (max_proofs_verified)
-- | - @outputSize: total public output size (= 33*n + 1)
-- | - rule: the inductive rule's main function
-------------------------------------------------------------------------------

stepMain
  :: forall @n @outputSize t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => StepWitnessM n StepIPARounds WrapIPARounds m StepField
  => Reflectable n Int
  => Reflectable outputSize Int
  => (FVar StepField -> Snarky (KimchiConstraint StepField) t m (RuleOutput n StepField))
  -> StepMainSrsData
  -> AffinePoint StepField -- dummySg for sgOld padding
  -> Snarky (KimchiConstraint StepField) t m (Vector outputSize (FVar StepField))
stepMain rule { lagrangeComms, blindingH } dummySg = do

  -- 1. exists input_typ (app_state)
  appState <- exists (advice :: _ (F StepField))

  -- 2. rule_main
  { prevPublicInputs, proofMustVerify } <- label "rule_main" $ rule appState

  -- 3. exists: VK via the advice monad. The VerificationKey CircuitType
  --    instance allocates sigma(7), coeff(15), index(6) in OCaml hlist order.
  VerificationKey vkRec <- label "exists_wrap_index" $
    exists $ lift $ getWrapVerifierIndex @n @StepIPARounds @WrapIPARounds unit
  let
    vk =
      { sigma: Vector.take @6 vkRec.sigma
      , sigmaLast: Vector.last vkRec.sigma
      , coeff: vkRec.coeff
      , index: vkRec.index
      }

  -- 4. exists: per-proof witnesses (n proofs, sequential)
  proofWitnesses <- label "exists_prevs" $
    Vector.generateA @n \_ -> allocatePerProofWitness @n

  -- 5. exists: unfinalized proofs (n)
  unfinalizedProofs <- label "exists_unfinalized" $
    Vector.generateA @n \_ -> allocateUnfinalized

  -- 6. exists: messages_for_next_wrap_proof (n digests)
  msgsWrap <- Vector.generateA @n \_ -> exists (advice :: _ (F StepField))

  -- 7. Build VK comms (shared by all proofs since prevs = [self, ...])
  let
    vkComms =
      { sigma: map unwrapPt vk.sigma
      , sigmaLast: unwrapPt vk.sigmaLast
      , coeff: map unwrapPt vk.coeff
      , index: map unwrapPt vk.index
      }

    constDummySg :: AffinePoint (FVar StepField)
    constDummySg = { x: const_ dummySg.x, y: const_ dummySg.y }

    domainLog2 = 16
    fopParams =
      { domain:
          { generator: const_ (LinFFI.domainGenerator @StepField domainLog2)
          , shifts: map const_ (LinFFI.domainShifts @StepField domainLog2)
          }
      , domainLog2
      , srsLengthLog2: 16
      , endo: stepEndoVal
      , linearizationPoly: Linearization.pallas
      }

    ivpParams =
      { curveParams: curveParams (Proxy @PallasG)
      , lagrangeComms
      , blindingH
      , correctionMode: PureCorrections
      , endo: stepEndoVal
      , groupMapParams: groupMapParams (Proxy @PallasG)
      , useOptSponge: false
      }

  -- 8. verify_one × n + Assert.all (inside prevs_verified label)
  results <- label "prevs_verified" do
    rs <- Vector.generateA @n \i -> do
      let
        pw = proofWitnesses !! i
        input = buildVerifyOneInput @n pw
          (prevPublicInputs !! i)
          (proofMustVerify !! i)
          (unfinalizedProofs !! i)
          (msgsWrap !! i)
          vkComms
          constDummySg
      verifyOne fopParams input ivpParams
    -- Boolean.Assert.all = assert_equal (sum vs) (len vs)
    assertAll_ (Vector.toUnfoldable $ map _.result rs)
    pure rs

  -- 9. Outer hash: hash_messages_for_next_step_proof
  outerDigest <- label "hash_messages_for_next_step_proof" do
    let
      absorbPt s pt = do
        let { x, y } = unwrapPt pt
        s1 <- Sponge.absorb x s
        Sponge.absorb y s1

    -- sponge_after_index: absorb VK
    spongeAfterIndex <- do
      let sponge0 = initialSpongeCircuit :: Sponge.Sponge (FVar StepField)
      s1 <- foldM absorbPt sponge0 vk.sigma
      s2 <- absorbPt s1 vk.sigmaLast
      s3 <- foldM absorbPt s2 vk.coeff
      foldM absorbPt s3 vk.index

    -- Absorb app_state
    s1 <- Sponge.absorb appState spongeAfterIndex

    -- For each proof: absorb sg + expanded bp_challenges
    let proofData = (Vector.toUnfoldable $ Vector.zipWith (\pw r -> { sg: pw.sg, expandedChals: r.expandedChallenges }) proofWitnesses results) :: Array _
    sAfterProofs <- foldM
      ( \s { sg: sgPt, expandedChals } -> do
          let pt = unwrapPt sgPt
          s2 <- Sponge.absorb pt.x s
          s3 <- Sponge.absorb pt.y s2
          foldM (\s' c -> Sponge.absorb c s') s3 expandedChals
      )
      s1
      proofData

    -- Squeeze
    { result: digest } <- Sponge.squeeze sAfterProofs
    pure digest

  -- 10. Build output: n × 32 (unfinalized) + 1 (step msg) + n (wrap msgs)
  let
    outputArr =
      foldMap unfFields (Vector.toUnfoldable unfinalizedProofs :: Array _)
        <> [ outerDigest ]
        <> (Vector.toUnfoldable msgsWrap :: Array _)

  pure $ unsafePartial $ fromJust $ Vector.toVector @outputSize outputArr

-------------------------------------------------------------------------------
-- | Compile step_main
-- |
-- | Uses `compile` with `m = Effect`. The Effect-based StepWitnessM instance
-- | (from Pickles.Step.Advice) throws if any advice method is called — but
-- | during compilation, `exists` in `CircuitBuilderT` ignores the AsProverT
-- | argument entirely, so the throw never fires. `unsafePerformEffect` is safe
-- | here because the compilation is deterministic and pure-in-effect.
-------------------------------------------------------------------------------

compileStepMain
  :: forall @n @outputSize
   . Reflectable n Int
  => Reflectable outputSize Int
  => (forall t. CircuitM StepField (KimchiConstraint StepField) t Effect => FVar StepField -> Snarky (KimchiConstraint StepField) t Effect (RuleOutput n StepField))
  -> StepMainSrsData
  -> AffinePoint StepField
  -> CircuitBuilderState (KimchiGate StepField) (AuxState StepField)
compileStepMain rule srsData dummySg = unsafePerformEffect $
  compile (Proxy @Unit) (Proxy @(Vector outputSize (F StepField))) (Proxy @(KimchiConstraint StepField))
    (\_ -> stepMain @n @outputSize rule srsData dummySg)
    Kimchi.initialState
