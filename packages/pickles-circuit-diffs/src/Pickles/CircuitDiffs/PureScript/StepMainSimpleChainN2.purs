module Pickles.CircuitDiffs.PureScript.StepMainSimpleChainN2
  ( compileStepMainSimpleChainN2
  , StepMainSimpleChainN2Params
  ) where

-- | step_main circuit for the Simple_Chain N2 rule (2 previous proofs).
-- |
-- | Mirrors OCaml dump_circuit_impl.ml:4519-4618.
-- | Rule: prevs = [self, self], self_correct = (1 + prev1 + prev2 == self)
-- | Both proofs have max_proofs_verified = N2.
-- |
-- | Reference: mina/src/lib/crypto/pickles/step_main.ml
-- |            mina/src/lib/crypto/pickles/dump_circuit_impl.ml (step_main_simple_chain_n2)

import Prelude

import Data.Foldable (foldM)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, stepEndo)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBase)
import Pickles.Sponge (initialSpongeCircuit)
import Pickles.Step.VerifyOne (VerifyOneInput, verifyOne)
import Pickles.Types (StepField)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, Snarky, UnChecked(..), assertAll_, assertAny_, const_, equals_, exists, label, not_)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.Kimchi (SplitField(..), Type1(..), Type2(..), groupMapParams)
import Snarky.Circuit.Kimchi.EndoScalar (toField) as EndoScalar
import Snarky.Circuit.RandomOracle.Sponge as Sponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type StepMainSimpleChainN2Params =
  { lagrangeComms :: Array (LagrangeBase StepField)
  , blindingH :: AffinePoint (F StepField)
  }

-------------------------------------------------------------------------------
-- | Inductive Rule for N2: 2 previous proofs
-------------------------------------------------------------------------------

type RuleOutput n f =
  { prevPublicInputs :: Vector n (FVar f)
  , proofMustVerify :: Vector n (BoolVar f)
  }

type InductiveRule n f c t m =
  FVar f -> Snarky c t m (RuleOutput n f)

-- | Simple_Chain N2 rule: self_correct = (1 + prev1 + prev2 == self)
-- | Both proofs have the same proof_must_verify = not is_base_case.
-- | Reference: dump_circuit_impl.ml:4533-4566
simpleChainN2Rule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => InductiveRule 2 StepField (KimchiConstraint StepField) t m
simpleChainN2Rule appState = do
  prev1 <- exists (pure (zero :: F StepField))
  -- proof1 = exists (Typ.prover_value ()) — no circuit effect
  prev2 <- exists (pure (zero :: F StepField))
  -- proof2 = exists (Typ.prover_value ()) — no circuit effect
  isBaseCase <- equals_ (const_ zero) appState
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (CVar.add_ (const_ one) prev1) prev2) appState
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev1 :< prev2 :< Vector.nil
    , proofMustVerify: proofMustVerify :< proofMustVerify :< Vector.nil
    }

-------------------------------------------------------------------------------
-- | Helpers
-------------------------------------------------------------------------------

unwrapPt :: WeierstrassAffinePoint PallasG (FVar StepField) -> AffinePoint (FVar StepField)
unwrapPt (WeierstrassAffinePoint pt) = pt

-------------------------------------------------------------------------------
-- | Number of public inputs for the Step.Statement output (N2)
-- | 2 unfinalized × 32 + 1 (step msg) + 2 (wrap msgs) = 67
-------------------------------------------------------------------------------
type InputSize = 67

-------------------------------------------------------------------------------
-- | Per-proof witness record (reused for both proofs)
-------------------------------------------------------------------------------

type PerProofWitness =
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
  -- N2: 2 prev_challenges + 2 prev_sgs (max_proofs_verified = N2)
  , prevChallenges :: Vector 2 (Vector 16 (FVar StepField))
  , prevSgs :: Vector 2 (WeierstrassAffinePoint PallasG (FVar StepField))
  }

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

-------------------------------------------------------------------------------
-- | Allocate one per-proof witness (OCaml Per_proof_witness.typ for N2)
-------------------------------------------------------------------------------

allocatePerProofWitness
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Snarky (KimchiConstraint StepField) t m PerProofWitness
allocatePerProofWitness = do
  let
    dummy :: forall a b. Applicative b => b a
    dummy = pure (unsafeCoerce unit)

  -- 1. Wrap_proof.Messages: w_comm, z_comm, t_comm
  wComm <- exists (dummy :: _ (Vector 15 (WeierstrassAffinePoint PallasG (F StepField))))
  zComm <- exists (dummy :: _ (WeierstrassAffinePoint PallasG (F StepField)))
  tComm <- exists (dummy :: _ (Vector 7 (WeierstrassAffinePoint PallasG (F StepField))))

  -- 2. Wrap_proof.Bulletproof: lr, z1, z2, delta, sg
  lr <- exists (dummy :: _ (Vector 15 { l :: WeierstrassAffinePoint PallasG (F StepField), r :: WeierstrassAffinePoint PallasG (F StepField) }))
  z1 <- exists (dummy :: _ (Type2 (SplitField (F StepField) Boolean)))
  z2 <- exists (dummy :: _ (Type2 (SplitField (F StepField) Boolean)))
  delta <- exists (dummy :: _ (WeierstrassAffinePoint PallasG (F StepField)))
  sg <- exists (dummy :: _ (WeierstrassAffinePoint PallasG (F StepField)))

  -- 3. Proof_state: in to_data order
  psCip <- exists (dummy :: _ (F StepField))
  psB <- exists (dummy :: _ (F StepField))
  psZetaToSrs <- exists (dummy :: _ (F StepField))
  psZetaToDom <- exists (dummy :: _ (F StepField))
  psPerm <- exists (dummy :: _ (F StepField))
  psSponge <- exists (dummy :: _ (F StepField))
  psBeta <- exists (dummy :: _ (F StepField))
  psGamma <- exists (dummy :: _ (F StepField))
  psAlpha <- exists (dummy :: _ (F StepField))
  psZeta <- exists (dummy :: _ (F StepField))
  psXi <- exists (dummy :: _ (F StepField))
  psBpChals :: Vector 16 (FVar StepField) <- exists (dummy :: _ (Vector 16 (F StepField)))
  -- branch_data: mask0(bool), mask1(bool), domainLog2(field + endoscalar)
  bdMask0 :: BoolVar StepField <- exists (dummy :: _ Boolean)
  bdMask1 :: BoolVar StepField <- exists (dummy :: _ Boolean)
  domLog2 <- exists (dummy :: _ (F StepField))
  let branchData = { mask0: bdMask0, mask1: bdMask1, domainLog2Var: domLog2 }
  _ <- EndoScalar.toField @1 (unsafeCoerce domLog2 :: SizedF 16 (FVar StepField)) (const_ stepEndo)

  let
    fopState =
      { plonk:
          { alpha: unsafeCoerce psAlpha :: SizedF 128 (FVar StepField)
          , beta: unsafeCoerce psBeta :: SizedF 128 (FVar StepField)
          , gamma: unsafeCoerce psGamma :: SizedF 128 (FVar StepField)
          , zeta: unsafeCoerce psZeta :: SizedF 128 (FVar StepField)
          , perm: Type1 psPerm
          , zetaToSrsLength: Type1 psZetaToSrs
          , zetaToDomainSize: Type1 psZetaToDom
          }
      , combinedInnerProduct: Type1 psCip
      , b: Type1 psB
      , xi: unsafeCoerce psXi :: SizedF 128 (FVar StepField)
      , bulletproofChallenges: unsafeCoerce psBpChals :: Vector 16 (SizedF 128 (FVar StepField))
      , spongeDigest: psSponge
      }

  -- 4. All_evals: in OCaml hlist order
  let toPair (Tuple z oz) = { zeta: z, omegaTimesZeta: oz }
  publicEvalsZ <- exists (dummy :: _ (F StepField))
  publicEvalsOZ <- exists (dummy :: _ (F StepField))
  witnessEvalsRaw <- exists (dummy :: _ (Vector 15 (Tuple (F StepField) (F StepField))))
  coeffEvalsRaw <- exists (dummy :: _ (Vector 15 (Tuple (F StepField) (F StepField))))
  zEvalsZ <- exists (dummy :: _ (F StepField))
  zEvalsOZ <- exists (dummy :: _ (F StepField))
  sigmaEvalsRaw <- exists (dummy :: _ (Vector 6 (Tuple (F StepField) (F StepField))))
  indexEvalsRaw <- exists (dummy :: _ (Vector 6 (Tuple (F StepField) (F StepField))))
  ftEval1 <- exists (dummy :: _ (F StepField))
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

  -- 5. prev_challenges: N2 = 2 sets of 16 challenges
  prevChals0 <- exists (dummy :: _ (UnChecked (Vector 16 (F StepField))))
  prevChals1 <- exists (dummy :: _ (UnChecked (Vector 16 (F StepField))))
  let
    UnChecked prevChals0' = prevChals0
    UnChecked prevChals1' = prevChals1
    prevChallenges = prevChals0' :< prevChals1' :< Vector.nil

  -- 6. prev_sgs: N2 = 2 curve points
  prevSg0 <- exists (dummy :: _ (WeierstrassAffinePoint PallasG (F StepField)))
  prevSg1 <- exists (dummy :: _ (WeierstrassAffinePoint PallasG (F StepField)))
  let prevSgs = prevSg0 :< prevSg1 :< Vector.nil

  pure { wComm, zComm, tComm, lr, z1, z2, delta, sg, fopState, allEvals, branchData, prevChallenges, prevSgs }

-------------------------------------------------------------------------------
-- | Allocate one unfinalized proof (same structure as N1)
-------------------------------------------------------------------------------

allocateUnfinalized
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Snarky (KimchiConstraint StepField) t m UnfinalizedProof
allocateUnfinalized = do
  let
    dummy :: forall a b. Applicative b => b a
    dummy = pure (unsafeCoerce unit)

  unfCip <- exists (dummy :: _ (Type2 (SplitField (F StepField) Boolean)))
  unfB <- exists (dummy :: _ (Type2 (SplitField (F StepField) Boolean)))
  unfZetaToSrs <- exists (dummy :: _ (Type2 (SplitField (F StepField) Boolean)))
  unfZetaToDom <- exists (dummy :: _ (Type2 (SplitField (F StepField) Boolean)))
  unfPerm <- exists (dummy :: _ (Type2 (SplitField (F StepField) Boolean)))
  unfClaimedDigest <- exists (dummy :: _ (F StepField))
  unfBeta <- exists (dummy :: _ (F StepField))
  unfGamma <- exists (dummy :: _ (F StepField))
  unfAlpha <- exists (dummy :: _ (F StepField))
  unfZeta <- exists (dummy :: _ (F StepField))
  unfXi <- exists (dummy :: _ (F StepField))
  unfBpChals :: Vector 15 (FVar StepField) <- exists (dummy :: _ (Vector 15 (F StepField)))
  unfShouldFinalize :: BoolVar StepField <- exists (dummy :: _ Boolean)
  pure
    { deferredValues:
        { plonk:
            { alpha: unsafeCoerce unfAlpha :: SizedF 128 (FVar StepField)
            , beta: unsafeCoerce unfBeta :: SizedF 128 (FVar StepField)
            , gamma: unsafeCoerce unfGamma :: SizedF 128 (FVar StepField)
            , zeta: unsafeCoerce unfZeta :: SizedF 128 (FVar StepField)
            , perm: unfPerm
            , zetaToSrsLength: unfZetaToSrs
            , zetaToDomainSize: unfZetaToDom
            }
        , combinedInnerProduct: unfCip
        , b: unfB
        , xi: unsafeCoerce unfXi :: SizedF 128 (FVar StepField)
        , bulletproofChallenges: unsafeCoerce unfBpChals :: Vector 15 (SizedF 128 (FVar StepField))
        }
    , shouldFinalize: unfShouldFinalize
    , claimedDigest: unfClaimedDigest
    }

-------------------------------------------------------------------------------
-- | Build verify_one input from per-proof witnesses
-------------------------------------------------------------------------------

buildVerifyOneInput
  :: PerProofWitness
  -> FVar StepField -- appState for this proof
  -> BoolVar StepField -- mustVerify
  -> UnfinalizedProof
  -> FVar StepField -- messagesForNextWrapProof
  -> { sigma :: Vector 6 (AffinePoint (FVar StepField))
     , sigmaLast :: AffinePoint (FVar StepField)
     , coeff :: Vector 15 (AffinePoint (FVar StepField))
     , index :: Vector 6 (AffinePoint (FVar StepField))
     }
  -> VerifyOneInput 2 15 16 (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (FVar StepField) (BoolVar StepField)
buildVerifyOneInput pw appState mustVerify unfinalized msgWrap vkComms =
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
      { mask0: unsafeCoerce pw.branchData.mask0 :: FVar StepField
      , mask1: unsafeCoerce pw.branchData.mask1 :: FVar StepField
      , domainLog2Var: pw.branchData.domainLog2Var
      }
  -- N2: proofMask = [mask0, mask1] (both entries, since max_proofs_verified = N2)
  , proofMask: pw.branchData.mask0 :< pw.branchData.mask1 :< Vector.nil
  , vkComms
  -- N2: sgOld = prevSgs (no dummy padding, since N2 = Wrap_hack.Padded_length = 2)
  , sgOld: map unwrapPt pw.prevSgs
  }

-------------------------------------------------------------------------------
-- | step_main circuit (N2)
-------------------------------------------------------------------------------

stepMainSimpleChainN2Circuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => StepMainSimpleChainN2Params
  -> Unit
  -> Snarky (KimchiConstraint StepField) t m (Vector InputSize (FVar StepField))
stepMainSimpleChainN2Circuit { lagrangeComms, blindingH } _ = do

  ---------------------------------------------------------------------------
  -- 1. exists input_typ (app_state)
  ---------------------------------------------------------------------------
  appState <- exists (pure (zero :: F StepField))

  ---------------------------------------------------------------------------
  -- 2. rule_main
  ---------------------------------------------------------------------------
  { prevPublicInputs, proofMustVerify } <- label "rule_main" $ simpleChainN2Rule appState

  let
    prevAppState1 = Vector.head prevPublicInputs
    prevAppState2 = Vector.head (Vector.tail prevPublicInputs)
    mustVerify1 = Vector.head proofMustVerify
    mustVerify2 = Vector.head (Vector.tail proofMustVerify)

  ---------------------------------------------------------------------------
  -- 3. exists: VK (same for both proofs since prevs = [self, self])
  ---------------------------------------------------------------------------
  vk <- label "exists_wrap_index" do
    vkSigma <- exists (dummy :: _ (Vector 7 (WeierstrassAffinePoint PallasG (F StepField))))
    vkCoeff <- exists (dummy :: _ (Vector 15 (WeierstrassAffinePoint PallasG (F StepField))))
    vkIndex <- exists (dummy :: _ (Vector 6 (WeierstrassAffinePoint PallasG (F StepField))))
    let
      vkSigma6 = unsafeCoerce (Vector.take @6 vkSigma) :: Vector 6 _
      vkSigmaLast = Vector.last vkSigma
    pure { sigma: vkSigma6, sigmaLast: vkSigmaLast, coeff: vkCoeff, index: vkIndex }

  ---------------------------------------------------------------------------
  -- 4. exists: per-proof witnesses (2 proofs, sequential)
  ---------------------------------------------------------------------------
  { pw1, pw2 } <- label "exists_prevs" do
    pw1 <- allocatePerProofWitness
    pw2 <- allocatePerProofWitness
    pure { pw1, pw2 }

  ---------------------------------------------------------------------------
  -- 5. exists: unfinalized proofs (2)
  ---------------------------------------------------------------------------
  { unf1, unf2 } <- label "exists_unfinalized" do
    unf1 <- allocateUnfinalized
    unf2 <- allocateUnfinalized
    pure { unf1, unf2 }

  ---------------------------------------------------------------------------
  -- 6. exists: messages_for_next_wrap_proof (Vector N2 Digest)
  ---------------------------------------------------------------------------
  msgWrap1 <- exists (dummy :: _ (F StepField))
  msgWrap2 <- exists (dummy :: _ (F StepField))

  ---------------------------------------------------------------------------
  -- 7. Build verify_one inputs and run both verifications
  ---------------------------------------------------------------------------
  let
    vkComms =
      { sigma: map unwrapPt vk.sigma
      , sigmaLast: unwrapPt vk.sigmaLast
      , coeff: map unwrapPt vk.coeff
      , index: map unwrapPt vk.index
      }

    input1 = buildVerifyOneInput pw1 prevAppState1 mustVerify1 unf1 msgWrap1 vkComms
    input2 = buildVerifyOneInput pw2 prevAppState2 mustVerify2 unf2 msgWrap2 vkComms

    domainLog2 = 16
    fopParams =
      { domain:
          { generator: const_ (LinFFI.domainGenerator @StepField domainLog2)
          , shifts: map const_ (LinFFI.domainShifts @StepField domainLog2)
          }
      , domainLog2
      , srsLengthLog2: 16
      , endo: stepEndo
      , linearizationPoly: Linearization.pallas
      }

    ivpParams =
      { curveParams: curveParams (Proxy @PallasG)
      , lagrangeComms
      , blindingH
      , correctionMode: PureCorrections
      , endo: stepEndo
      , groupMapParams: groupMapParams (Proxy @PallasG)
      , useOptSponge: false
      }

  ---------------------------------------------------------------------------
  -- 8. verify_one × 2 + Assert.all (inside prevs_verified label)
  ---------------------------------------------------------------------------
  { expandedChals1, expandedChals2 } <- label "prevs_verified" do
    res1 <- verifyOne fopParams input1 ivpParams
    res2 <- verifyOne fopParams input2 ivpParams
    -- Boolean.Assert.all [v1, v2] = assert_equal (sum bs) (len bs)
    assertAll_ [ res1.result, res2.result ]
    pure { expandedChals1: res1.expandedChallenges, expandedChals2: res2.expandedChallenges }

  ---------------------------------------------------------------------------
  -- 9. Outer hash: hash_messages_for_next_step_proof
  ---------------------------------------------------------------------------
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

    -- Proof 1: absorb sg + expanded bp_challenges
    let sg1 = unwrapPt pw1.sg
    s2 <- Sponge.absorb sg1.x s1
    s3 <- Sponge.absorb sg1.y s2
    s4 <- foldM (\s c -> Sponge.absorb c s) s3 expandedChals1

    -- Proof 2: absorb sg + expanded bp_challenges
    let sg2 = unwrapPt pw2.sg
    s5 <- Sponge.absorb sg2.x s4
    s6 <- Sponge.absorb sg2.y s5
    sAfterProofs <- foldM (\s c -> Sponge.absorb c s) s6 expandedChals2

    -- Squeeze
    { result: digest } <- Sponge.squeeze sAfterProofs
    pure digest

  ---------------------------------------------------------------------------
  -- 10. Build output: 2 × 32 (unfinalized) + 1 (step msg) + 2 (wrap msgs) = 67
  ---------------------------------------------------------------------------
  let
    sf2 (Type2 (SplitField { sDiv2, sOdd })) = [ sDiv2, unsafeCoerce sOdd :: FVar StepField ]

    unfFields unf =
      sf2 unf.deferredValues.combinedInnerProduct
        <> sf2 unf.deferredValues.b
        <> sf2 unf.deferredValues.plonk.zetaToSrsLength
        <> sf2 unf.deferredValues.plonk.zetaToDomainSize
        <> sf2 unf.deferredValues.plonk.perm
        <> [ unf.claimedDigest ]
        <>
          [ unsafeCoerce unf.deferredValues.plonk.beta :: FVar StepField
          , unsafeCoerce unf.deferredValues.plonk.gamma :: FVar StepField
          ]
        <>
          [ unsafeCoerce unf.deferredValues.plonk.alpha :: FVar StepField
          , unsafeCoerce unf.deferredValues.plonk.zeta :: FVar StepField
          , unsafeCoerce unf.deferredValues.xi :: FVar StepField
          ]
        <> Vector.toUnfoldable (unsafeCoerce unf.deferredValues.bulletproofChallenges :: Vector 15 (FVar StepField))
        <> [ unsafeCoerce unf.shouldFinalize :: FVar StepField ]

    outputArr =
      unfFields unf1
        <> unfFields unf2
        <> [ outerDigest ]
        <> [ msgWrap1, msgWrap2 ]

  pure (unsafeCoerce outputArr :: Vector InputSize (FVar StepField))
  where
  dummy :: forall a b. Applicative b => b a
  dummy = pure (unsafeCoerce unit)

compileStepMainSimpleChainN2 :: StepMainSimpleChainN2Params -> CompiledCircuit StepField
compileStepMainSimpleChainN2 params =
  compilePure (Proxy @Unit) (Proxy @(Vector InputSize (F StepField))) (Proxy @(KimchiConstraint StepField))
    (\_ -> stepMainSimpleChainN2Circuit params unit)
    Kimchi.initialState
