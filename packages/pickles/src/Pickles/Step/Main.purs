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
  ( -- * Rule abstraction
    RuleOutput
  -- * Generic step_main
  , StepMainSrsData
  , stepMain
  -- * Padded variant (production Pickles)
  , stepMainPadded
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Fin (getFinite)
import Data.Foldable (foldM)
import Data.Array as Array
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.FoldableWithIndex (forWithIndex_)
import Partial.Unsafe (unsafePartial)
import Data.Traversable (traverse)
import Data.Vector (Vector, (!!), (:<))
import Data.Vector as Vector
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBaseLookup)
import Pickles.Sponge (initialSpongeCircuit)
import Pickles.Step.Advice (class StepWitnessM, getMessagesForNextWrapProof, getStepAppState, getStepPerProofWitnesses, getStepUnfinalizedProofs, getWrapVerifierIndex)
import Pickles.Step.VerifyOne (VerifyOneInput, verifyOne)
import Pickles.Verify (ivpTrace)
import Pickles.Types (BranchData(..), FopProofState(..), PaddedLength, PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepField, StepIPARounds, StepPerProofWitness(..), StepProofState(..), VerificationKey(..), WrapIPARounds, WrapProof(..), WrapProofMessages(..), WrapProofOpening(..))
import Prim.Int (class Add, class Mul)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F, FVar, Snarky, UnChecked(..), assertAll_, const_, exists, label)
import Snarky.Circuit.DSL.SizedF (SizedF, toField)
import Snarky.Circuit.Kimchi (SplitField(..), Type1(..), Type2(..), groupMapParams)
import Snarky.Circuit.RandomOracle.Sponge as Sponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (EndoScalar(..), curveParams, endoScalar)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Rule abstraction
-------------------------------------------------------------------------------

-- | Rules route their own witness allocations through application-specific
-- | advice typeclasses (one per rule), not via a generic throwing helper.
-- | Each rule defines a class with methods for the values it needs, plus
-- | an `Effect` instance that throws for compilation. The prover side
-- | provides a real interpreter via a different monad.
-- |
-- | Reference: `SimpleChainAdvice` in StepMainSimpleChain.purs for the
-- | N1 rule, `SimpleChainN2Advice` for N2.
type RuleOutput n f =
  { prevPublicInputs :: Vector n (FVar f)
  , proofMustVerify :: Vector n (BoolVar f)
  }

-------------------------------------------------------------------------------
-- | SRS data for step_main
-------------------------------------------------------------------------------

type StepMainSrsData =
  { lagrangeAt :: LagrangeBaseLookup StepField
  , blindingH :: AffinePoint (F StepField)
  -- | log2 of the step circuit's evaluation domain (OCaml: basic.step_domains.h,
  -- | threaded as Types_map.For_step.step_domains into finalize_other_proof
  -- | where it's used for domain_for_compiled). For simple_chain: 16.
  -- | See dump_circuit_impl.ml:3723.
  , fopDomainLog2 :: Int
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
      , bulletproofChallenges :: Vector StepIPARounds (SizedF 128 (FVar StepField))
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
  , prevChallenges :: Vector n (Vector StepIPARounds (FVar StepField))
  , prevSgs :: Vector n (WeierstrassAffinePoint PallasG (FVar StepField))
  }

allocatePerProofWitness
  :: forall @n t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Reflectable n Int
  => StepPerProofWitness n StepIPARounds WrapIPARounds (FVar StepField) (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (BoolVar StepField)
  -> Snarky (KimchiConstraint StepField) t m (PerProofWitness n)
allocatePerProofWitness (StepPerProofWitness ppw) = do
  let
    WrapProof wrapProofRec = ppw.wrapProof
    WrapProofMessages msgRec = wrapProofRec.messages
    WrapProofOpening openRec = wrapProofRec.opening
    StepProofState psRec = ppw.proofState
    FopProofState fopRec = psRec.fopState
    BranchData branchDataRec = psRec.branchData
    StepAllEvals evalsRec = ppw.prevEvals

    fopState =
      { plonk:
          { alpha: coerce fopRec.alpha
          , beta: coerce fopRec.beta
          , gamma: coerce fopRec.gamma
          , zeta: coerce fopRec.zeta
          , perm: Type1 fopRec.perm
          , zetaToSrsLength: Type1 fopRec.zetaToSrsLength
          , zetaToDomainSize: Type1 fopRec.zetaToDomainSize
          }
      , combinedInnerProduct: Type1 fopRec.combinedInnerProduct
      , b: Type1 fopRec.b
      , xi: coerce fopRec.xi
      , bulletproofChallenges: coerce fopRec.bulletproofChallenges
      , spongeDigest: fopRec.spongeDigest
      }
    unwrapPointEval (PointEval pe) = { zeta: pe.zeta, omegaTimesZeta: pe.omegaTimesZeta }
    allEvals =
      { ftEval1: evalsRec.ftEval1
      , publicEvals: unwrapPointEval evalsRec.publicEvals
      , witnessEvals: map unwrapPointEval evalsRec.witnessEvals
      , coeffEvals: map unwrapPointEval evalsRec.coeffEvals
      , zEvals: unwrapPointEval evalsRec.zEvals
      , sigmaEvals: map unwrapPointEval evalsRec.sigmaEvals
      , indexEvals: map unwrapPointEval evalsRec.indexEvals
      }
  pure
    { wComm: msgRec.wComm
    , zComm: msgRec.zComm
    , tComm: msgRec.tComm
    , lr: openRec.lr
    , z1: openRec.z1
    , z2: openRec.z2
    , delta: openRec.delta
    , sg: openRec.sg
    , fopState
    , allEvals
    , branchData:
        { mask0: branchDataRec.mask0
        , mask1: branchDataRec.mask1
        , domainLog2Var: branchDataRec.domainLog2
        }
    , prevChallenges: coerce ppw.prevChallenges
    , prevSgs: ppw.prevSgs
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
      , bulletproofChallenges :: Vector WrapIPARounds (SizedF 128 (FVar StepField))
      }
  , shouldFinalize :: BoolVar StepField
  , claimedDigest :: FVar StepField
  }

-- | Unpack one PerProofUnfinalized (allocated via the advice monad upstream)
-- | into the legacy `UnfinalizedProof` record shape consumed by `verifyOne`.
unpackUnfinalized
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => PerProofUnfinalized WrapIPARounds (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (FVar StepField) (BoolVar StepField)
  -> Snarky (KimchiConstraint StepField) t m UnfinalizedProof
unpackUnfinalized (PerProofUnfinalized r) = pure
  { deferredValues:
      { plonk:
          { alpha: coerce r.alpha :: SizedF 128 (FVar StepField)
          , beta: coerce r.beta :: SizedF 128 (FVar StepField)
          , gamma: coerce r.gamma :: SizedF 128 (FVar StepField)
          , zeta: coerce r.zeta :: SizedF 128 (FVar StepField)
          , perm: r.perm
          , zetaToSrsLength: r.zetaToSrsLength
          , zetaToDomainSize: r.zetaToDomainSize
          }
      , combinedInnerProduct: r.combinedInnerProduct
      , b: r.b
      , xi: coerce r.xi :: SizedF 128 (FVar StepField)
      , bulletproofChallenges: coerce r.bulletproofChallenges :: Vector WrapIPARounds (SizedF 128 (FVar StepField))
      }
  , shouldFinalize: r.shouldFinalize
  , claimedDigest: r.spongeDigest
  }

-------------------------------------------------------------------------------
-- | Build verify_one input from allocated witnesses
-------------------------------------------------------------------------------

buildVerifyOneInput
  :: forall @n pad
   . Reflectable n Int
  => Reflectable pad Int
  => Add pad n PaddedLength
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
  -> VerifyOneInput n WrapIPARounds StepIPARounds (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (FVar StepField) (BoolVar StepField)
buildVerifyOneInput pw appState mustVerify unfinalized msgWrap vkComms dummySg =
  let
    -- sgOld: pad prevSgs to PaddedLength (Wrap_hack.Padded_length).
    -- extend_front puts `pad` dummies at the front, where pad + n = PaddedLength.
    sgPadding :: Vector pad (AffinePoint (FVar StepField))
    sgPadding = Vector.replicate dummySg

    sgOld :: Vector PaddedLength (AffinePoint (FVar StepField))
    sgOld = Vector.append sgPadding (map unwrapPt pw.prevSgs)

    -- proofMask: drop the front `pad` elements of [mask0, mask1] to keep the last `n`.
    fullMasks :: Vector PaddedLength (BoolVar StepField)
    fullMasks = pw.branchData.mask0 :< pw.branchData.mask1 :< Vector.nil

    proofMask :: Vector n (BoolVar StepField)
    proofMask = Vector.drop @pad fullMasks
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

-- | Unfinalized proof serialized as a fixed-width public-input vector.
-- |
-- | Layout (32 fields = 17 + WrapIPARounds):
-- |   5 × Type2 (10) + digest (1) + 2 challenges + 3 scalar challenges
-- |   + WrapIPARounds bp challenges (15) + shouldFinalize (1)
unfFields :: UnfinalizedProof -> Vector 32 (FVar StepField)
unfFields unf =
  let
    sf2 :: Type2 (SplitField (FVar StepField) (BoolVar StepField)) -> Vector 2 (FVar StepField)
    sf2 (Type2 (SplitField { sDiv2, sOdd })) = sDiv2 :< coerce sOdd :< Vector.nil

    cipFields = sf2 unf.deferredValues.combinedInnerProduct
    bFields = sf2 unf.deferredValues.b
    zetaSrsFields = sf2 unf.deferredValues.plonk.zetaToSrsLength
    zetaDomFields = sf2 unf.deferredValues.plonk.zetaToDomainSize
    permFields = sf2 unf.deferredValues.plonk.perm

    digestField :: Vector 1 (FVar StepField)
    digestField = unf.claimedDigest :< Vector.nil

    betaGamma :: Vector 2 (FVar StepField)
    betaGamma = toField unf.deferredValues.plonk.beta :< toField unf.deferredValues.plonk.gamma :< Vector.nil

    alphaZetaXi :: Vector 3 (FVar StepField)
    alphaZetaXi =
      toField unf.deferredValues.plonk.alpha
        :< toField unf.deferredValues.plonk.zeta
        :< toField unf.deferredValues.xi
        :< Vector.nil

    bpFields :: Vector WrapIPARounds (FVar StepField)
    bpFields = map toField unf.deferredValues.bulletproofChallenges

    shouldFinalizeField :: Vector 1 (FVar StepField)
    shouldFinalizeField = (coerce unf.shouldFinalize :: FVar StepField) :< Vector.nil
  in
    cipFields
      `Vector.append` bFields
      `Vector.append` zetaSrsFields
      `Vector.append` zetaDomFields
      `Vector.append` permFields
      `Vector.append` digestField
      `Vector.append` betaGamma
      `Vector.append` alphaZetaXi
      `Vector.append` bpFields
      `Vector.append` shouldFinalizeField

-------------------------------------------------------------------------------
-- | Generic step_main circuit
-- |
-- | Parameterized by:
-- | - @n: number of previous proofs (max_proofs_verified)
-- | - @outputSize: total public output size (= 33*n + 1)
-- | - rule: the inductive rule's main function
-------------------------------------------------------------------------------

stepMain
  :: forall @n pad @outputSize
       unfsTotal digestPlusUnfs
       t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => StepWitnessM n StepIPARounds WrapIPARounds PallasG StepField m
  => Reflectable n Int
  => Reflectable pad Int
  => Add pad n PaddedLength
  => Mul n 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs n outputSize
  => (FVar StepField -> Snarky (KimchiConstraint StepField) t m (RuleOutput n StepField))
  -> StepMainSrsData
  -> AffinePoint StepField -- dummySg for sgOld padding
  -> Snarky (KimchiConstraint StepField) t m (Vector outputSize (FVar StepField))
stepMain rule { lagrangeAt, blindingH, fopDomainLog2 } dummySg = do

  -- 1. exists: app_state via Req.App_state
  appState <- exists $ lift $ getStepAppState @n @StepIPARounds @WrapIPARounds @PallasG unit

  -- 2. rule_main
  { prevPublicInputs, proofMustVerify } <- label "rule_main" $ rule appState

  -- 3. exists: VK via Req.Wrap_index. The VerificationKey CircuitType
  --    instance allocates sigma(7), coeff(15), index(6) in OCaml hlist order.
  VerificationKey vkRec <- label "exists_wrap_index"
    $ exists
    $ lift
    $ getWrapVerifierIndex @n @StepIPARounds @WrapIPARounds @PallasG unit
  let
    vk =
      { sigma: Vector.take @6 vkRec.sigma
      , sigmaLast: Vector.last vkRec.sigma
      , coeff: vkRec.coeff
      , index: vkRec.index
      }

  -- 4. exists: per-proof witnesses via Req.Proof_with_datas — ONE
  --    structured allocation matching OCaml's
  --    `exists (Prev_typ.f prev_proof_typs)`.
  rawProofWitnesses <- label "exists_prevs"
    $ exists
    $ lift
    $ getStepPerProofWitnesses @n @StepIPARounds @WrapIPARounds @PallasG unit
  proofWitnesses <- traverse (allocatePerProofWitness @n) rawProofWitnesses

  -- 5. exists: unfinalized proofs via Req.Unfinalized_proofs — ONE
  --    structured allocation matching OCaml's
  --    `exists (Vector.typ' Unfinalized.typ ...)`.
  rawUnfinalizedProofs <- label "exists_unfinalized"
    $ exists
    $ lift
    $ getStepUnfinalizedProofs @n @StepIPARounds @WrapIPARounds @PallasG unit
  unfinalizedProofs <- traverse unpackUnfinalized rawUnfinalizedProofs

  -- 6. exists: messages_for_next_wrap_proof via Req.Messages_for_next_wrap_proof
  --    ONE Vector allocation matching OCaml.
  msgsWrap <- exists $ lift $ getMessagesForNextWrapProof @n @StepIPARounds @WrapIPARounds @PallasG unit

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

    -- Wrap proof's domain log2 (OCaml: basic.wrap_domains.h, threaded
    -- through Types_map.For_step.t into step_verifier.verify_one).
    fopParams =
      { domain:
          { generator: const_ (LinFFI.domainGenerator @StepField fopDomainLog2)
          , shifts: map const_ (LinFFI.domainShifts @StepField fopDomainLog2)
          }
      , domainLog2: fopDomainLog2
      , srsLengthLog2: reflectType (Proxy :: Proxy StepIPARounds)
      , endo: stepEndoVal
      , linearizationPoly: Linearization.pallas
      }

    ivpParams =
      { curveParams: curveParams (Proxy @PallasG)
      , lagrangeAt
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

    -- === TRACE: outer hash inputs (NEW step proof's msgForNextStep) ===
    -- Compares to OCaml `step_main_outer.*` traces. PI[32] is the
    -- digest of these inputs; every divergence in PI[32] is a diff
    -- in one of these.
    forWithIndex_ vk.sigma \fi pt -> do
      let i = getFinite fi
      let { x, y } = unwrapPt pt
      ivpTrace ("step_main_outer.vk.sigma." <> show i <> ".x") x
      ivpTrace ("step_main_outer.vk.sigma." <> show i <> ".y") y
    let { x: slX, y: slY } = unwrapPt vk.sigmaLast
    ivpTrace "step_main_outer.vk.sigma_last.x" slX
    ivpTrace "step_main_outer.vk.sigma_last.y" slY
    forWithIndex_ vk.coeff \fi pt -> do
      let i = getFinite fi
      let { x, y } = unwrapPt pt
      ivpTrace ("step_main_outer.vk.coeff." <> show i <> ".x") x
      ivpTrace ("step_main_outer.vk.coeff." <> show i <> ".y") y
    forWithIndex_ vk.index \fi pt -> do
      let i = getFinite fi
      let { x, y } = unwrapPt pt
      ivpTrace ("step_main_outer.vk.index." <> show i <> ".x") x
      ivpTrace ("step_main_outer.vk.index." <> show i <> ".y") y
    ivpTrace "step_main_outer.app_state" appState

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
    let proofData = Vector.zipWith (\pw r -> { sg: pw.sg, expandedChals: r.expandedChallenges }) proofWitnesses results
    forWithIndex_ proofData \fi { sg: sgPt, expandedChals } -> do
      let i = getFinite fi
      let pt = unwrapPt sgPt
      ivpTrace ("step_main_outer.proof." <> show i <> ".sg.x") pt.x
      ivpTrace ("step_main_outer.proof." <> show i <> ".sg.y") pt.y
      forWithIndex_ expandedChals \fj c ->
        ivpTrace ("step_main_outer.proof." <> show i <> ".bp_chal." <> show (getFinite fj)) c
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
    ivpTrace "step_main_outer.digest" digest
    pure digest

  -- 10. Build output: n × 32 (unfinalized) + 1 (step msg) + n (wrap msgs)
  let
    unfsFlat :: Vector unfsTotal (FVar StepField)
    unfsFlat = Vector.concat (map unfFields unfinalizedProofs)

    digestVec :: Vector 1 (FVar StepField)
    digestVec = outerDigest :< Vector.nil

    outputV :: Vector outputSize (FVar StepField)
    outputV = unfsFlat `Vector.append` digestVec `Vector.append` msgsWrap

  pure outputV

-- | Production variant of `stepMain` that pads the output to `PaddedLength`
-- | (= N2), matching OCaml's `pickles.ml` which always compiles the step
-- | circuit with `Max_proofs_verified = N2`.
-- |
-- | Dummies are prepended at the FRONT (matching OCaml's `extend_front`):
-- |   unfinalized_proofs = [dummy_0..dummy_{pad-1}, real_0..real_{n-1}]
-- |   messages_for_next_wrap_proof = [0..0, real_0..real_{n-1}]
-- |
-- | Reference: step_main.ml:584-586, pickles.ml:476 (Max_proofs_verified = N2)
stepMainPadded
  :: forall @n @pad @outputSize
       unfsTotal digestPlusUnfs
       padUnfsTotal paddedUnfsTotal paddedDigestPlusUnfs paddedOutputSize
       t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => StepWitnessM n StepIPARounds WrapIPARounds PallasG StepField m
  => Reflectable n Int
  => Reflectable pad Int
  => Add pad n PaddedLength
  -- n-sized output arithmetic (internal, for stepMain)
  => Mul n 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs n outputSize
  -- Padding arithmetic
  => Mul pad 32 padUnfsTotal
  => Add padUnfsTotal unfsTotal paddedUnfsTotal
  -- PaddedLength-sized output arithmetic (actual output)
  => Add paddedUnfsTotal 1 paddedDigestPlusUnfs
  => Add paddedDigestPlusUnfs PaddedLength paddedOutputSize
  => Reflectable paddedOutputSize Int
  => (FVar StepField -> Snarky (KimchiConstraint StepField) t m (RuleOutput n StepField))
  -> StepMainSrsData
  -> AffinePoint StepField
  -> Snarky (KimchiConstraint StepField) t m (Vector paddedOutputSize (FVar StepField))
stepMainPadded rule srsData dummySg = do
  -- Run the circuit body to get the raw components (n real proofs)
  -- We inline the same logic as stepMain but produce padded output.
  unpadded <- stepMain @n @outputSize rule srsData dummySg

  -- The unpadded output is [unfs(n*32) | digest(1) | msgs(n)].
  -- Convert to Array, split, pad with dummies at front, reassemble.
  let
    arr = Vector.toUnfoldable unpadded :: Array _
    nReal = reflectType (Proxy :: Proxy n)

    realUnfs = Array.take (nReal * 32) arr
    digest = Array.take 1 (Array.drop (nReal * 32) arr)
    realMsgs = Array.drop (nReal * 32 + 1) arr

    dummyUnf = Array.replicate 32 (const_ zero :: FVar StepField)
    padCount = reflectType (Proxy :: Proxy pad)
    dummyUnfs = Array.concat (Array.replicate padCount dummyUnf)
    dummyMsgs = Array.replicate padCount (const_ zero :: FVar StepField)

    paddedArr = dummyUnfs <> realUnfs <> digest <> dummyMsgs <> realMsgs

  pure (unsafePartial fromJust $ Vector.toVector @paddedOutputSize paddedArr)

