-- | Wrap main circuit — the SNARK function for wrapping any step proof.
-- |
-- | Parameterized by:
-- | - @branches: number of step circuit variants (N1 or N2)
-- | - @slot0Width, @slot1Width: per-slot widths of `Max_widths_by_slot.maxes`
-- |
-- | The circuit, in OCaml exists order (matching `wrap_main.ml`):
-- |   1. Req.Which_branch     — single field
-- |   2. (in-circuit) one-hot vector + ones_vector + branch_data assert
-- |   3. Req.Proof_state      — `mpv` unfinalized proofs + msg_for_next_step
-- |   4. (in-circuit) chooseKey + feature flag consistency
-- |   5. Req.Step_accs        — Vector mpv of step accumulators
-- |   6. Req.Old_bulletproof_challenges — heterogeneous slot-grouped chals
-- |   7. Req.Evals            — Vector mpv of `StepAllEvals`
-- |   8. Req.Wrap_domain_indices — Vector mpv of indices
-- |   9. (in-circuit) FOP loop (right-to-left) + assert any [finalized; not should_finalize]
-- |  10. (in-circuit) message hash loop (right-to-left) + assert msg_step
-- |  11. Req.Openings_proof   — full bulletproof opening
-- |  12. Req.Messages         — wComm/zComm/tComm
-- |  13. (in-circuit) pack_statement + split_field
-- |  14. (in-circuit) wrap_verify (IVP + 4 final assertions)
-- |
-- | Reference: mina/src/lib/crypto/pickles/wrap_main.ml
module Pickles.Wrap.Main
  ( WrapMainConfig
  , WrapMainInput
  , WrapMainInputVar
  , wrapMain
  , compileWrapMain
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Fin (Finite, unsafeFinite)
import Data.Foldable (foldl)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (traverse)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PackedStatement (PackedStepPublicInput(..))
import Pickles.Pseudo as Pseudo
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBase)
import Pickles.Sponge (evalSpongeM, spongeFromConstants)
import Pickles.Types (MaxProofsVerified, PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepIPARounds, WrapField, WrapIPARounds, WrapOldBpChals(..), WrapPrevProofState(..), WrapProofMessages(..), WrapProofOpening(..), WrapStatementPacked(..))
import Pickles.ProofWitness (ProofWitness)
import Pickles.Verify.Types (UnfinalizedProof)
import Pickles.VerificationKey (StepVK, chooseKey)
import Pickles.Wrap.Advice (class WrapWitnessM, getEvals, getMessages, getOldBulletproofChallenges, getOpeningProof, getStepAccs, getWhichBranch, getWrapDomainIndices, getWrapProofState)
import Pickles.Wrap.FinalizeOtherProof (wrapFinalizeOtherProofCircuit)
import Pickles.Wrap.MessageHash (dummyPaddingSpongeStates, hashMessagesForNextWrapProofCircuit')
import Pickles.Wrap.Verify (wrapVerify)
import Prim.Int (class Add)
import Record as Record
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (add_, scale_) as CVar
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, UnChecked(..), add_, and_, assertAny_, assertEqual_, const_, equals_, exists, label, not_, true_)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.Kimchi (SplitField, Type1, Type2(..), groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (EndoScalar(..), endoScalar) as Curves
import Snarky.Curves.Class (curveParams, fromInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Snarky.Types.Shifted (splitFieldCircuit)
import Type.Proxy (Proxy(..))

import Effect.Unsafe (unsafePerformEffect)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (compile)
import Snarky.Constraint.Kimchi.Types (AuxState)

-- | Public input to `wrapMain` at value level. The `WrapStatementPacked`
-- | newtype is the OCaml-allocation-faithful representation: challenge fields
-- | are `UnChecked (SizedF 128 ...)` (matching `Spec.wrap_packed_typ` which
-- | allocates them via plain `Field.typ`), Type1 fp fields keep their
-- | forbidden_shifted_values check, and the field order matches OCaml's
-- | `Wrap.Statement.In_circuit.to_data` hlist layout.
-- |
-- | The `d` parameter is the bulletproof-challenges length, which is
-- | `Backend.Tick.Rounds.n = StepIPARounds = 16` because the wrap statement
-- | carries the STEP proof's deferred values (the wrap circuit verifies a
-- | step proof, so its public input contains the step proof's challenges).
type WrapMainInput :: Type
type WrapMainInput =
  WrapStatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean

-- | Public input to `wrapMain` at var level (what the circuit body operates on).
type WrapMainInputVar :: Type
type WrapMainInputVar =
  WrapStatementPacked StepIPARounds (Type1 (FVar WrapField)) (FVar WrapField) (BoolVar WrapField)

-- | Compile-time configuration for `wrapMain`.
-- |
-- | OCaml equivalents:
-- | - stepWidths: (int, branches) Vector.t
-- | - domainLog2s: per-branch step domain log2s (we keep them as ints)
-- | - stepKeys: dummy step VKs (PallasG circuit variables)
-- | - allPossibleDomainLog2s: Wrap_verifier.all_possible_domains
type WrapMainConfig branches =
  { stepWidths :: Vector branches Int
  , domainLog2s :: Vector branches Int
  , stepKeys :: Vector branches (StepVK (FVar WrapField))
  , lagrangeComms :: Array (LagrangeBase WrapField)
  , blindingH :: AffinePoint (F WrapField)
  , allPossibleDomainLog2s :: Vector 3 (Finite 16)
  }

-------------------------------------------------------------------------------
-- | Internal helpers — convert structured advice into the shape consumed
-- | by the existing FOP / IVP sub-circuits.
-------------------------------------------------------------------------------

-- | The legacy "unfinalized proof" record shape consumed by
-- | `wrapFinalizeOtherProofCircuit`. We project a `PerProofUnfinalized` into
-- | this shape because the FOP code already speaks this dialect.
type UnfinalizedView =
  { deferredValues ::
      { plonk ::
          { alpha :: SizedF 128 (FVar WrapField)
          , beta :: SizedF 128 (FVar WrapField)
          , gamma :: SizedF 128 (FVar WrapField)
          , zeta :: SizedF 128 (FVar WrapField)
          , perm :: Type2 (FVar WrapField)
          , zetaToSrsLength :: Type2 (FVar WrapField)
          , zetaToDomainSize :: Type2 (FVar WrapField)
          }
      , combinedInnerProduct :: Type2 (FVar WrapField)
      , b :: Type2 (FVar WrapField)
      , xi :: SizedF 128 (FVar WrapField)
      , bulletproofChallenges :: Vector WrapIPARounds (SizedF 128 (FVar WrapField))
      }
  , shouldFinalize :: BoolVar WrapField
  , spongeDigestBeforeEvaluations :: FVar WrapField
  }

unpackUnfinalized
  :: PerProofUnfinalized WrapIPARounds (Type2 (FVar WrapField)) (FVar WrapField) (BoolVar WrapField)
  -> UnfinalizedView
unpackUnfinalized (PerProofUnfinalized r) =
  { deferredValues:
      { plonk:
          { alpha: coerce r.alpha :: SizedF 128 (FVar WrapField)
          , beta: coerce r.beta :: SizedF 128 (FVar WrapField)
          , gamma: coerce r.gamma :: SizedF 128 (FVar WrapField)
          , zeta: coerce r.zeta :: SizedF 128 (FVar WrapField)
          , perm: r.perm
          , zetaToSrsLength: r.zetaToSrsLength
          , zetaToDomainSize: r.zetaToDomainSize
          }
      , combinedInnerProduct: r.combinedInnerProduct
      , b: r.b
      , xi: coerce r.xi :: SizedF 128 (FVar WrapField)
      , bulletproofChallenges: coerce r.bulletproofChallenges :: Vector WrapIPARounds (SizedF 128 (FVar WrapField))
      }
  , shouldFinalize: r.shouldFinalize
  , spongeDigestBeforeEvaluations: r.spongeDigest
  }

unwrapPt :: WeierstrassAffinePoint VestaG (FVar WrapField) -> AffinePoint (FVar WrapField)
unwrapPt (WeierstrassAffinePoint pt) = pt

-- | Project a `StepAllEvals` newtype (allocated with OCaml-ordered fields) into
-- | the `ProofWitness` record consumed by `wrapFinalizeOtherProofCircuit`. The
-- | `PointEval` newtype is unwrapped to the underlying record at the same time.
stepAllEvalsToProofWitness
  :: StepAllEvals (FVar WrapField)
  -> ProofWitness (FVar WrapField)
stepAllEvalsToProofWitness (StepAllEvals r) =
  let
    unP (PointEval pe) = pe
  in
    { allEvals:
        { ftEval1: r.ftEval1
        , publicEvals: unP r.publicEvals
        , zEvals: unP r.zEvals
        , indexEvals: map unP r.indexEvals
        , witnessEvals: map unP r.witnessEvals
        , coeffEvals: map unP r.coeffEvals
        , sigmaEvals: map unP r.sigmaEvals
        }
    }

-- | OCaml `Wrap_hack.Checked.pad_challenges`: prepend
-- | `(MaxProofsVerified - slotWidth)` dummy challenge vectors so the result
-- | has `Vector MaxProofsVerified ...` shape, ready for the FOP loop.
padWrapChallenges
  :: forall slotWidth pad
   . Reflectable pad Int
  => Add pad slotWidth MaxProofsVerified
  => Vector slotWidth (Vector WrapIPARounds (FVar WrapField))
  -> Vector MaxProofsVerified (Vector WrapIPARounds (FVar WrapField))
padWrapChallenges chals =
  let
    dummy :: Vector WrapIPARounds (FVar WrapField)
    dummy = map const_ dummyIpaChallenges.wrapExpanded

    padding :: Vector pad (Vector WrapIPARounds (FVar WrapField))
    padding = Vector.replicate dummy
  in
    Vector.append padding chals

-- | block5 helper: project a `PerProofUnfinalized` (5 raw `Type2 (FVar f)`
-- | deferred fields, allocated by `Req.Proof_state`) into the
-- | `UnfinalizedProof` shape consumed by `PackedStepPublicInput`. Each raw
-- | deferred field is split into `(sDiv2, sOdd)` via `splitFieldCircuit` so
-- | the wrap verifier's x_hat MSM can fold the result into a single curve
-- | point.
splitPerProofUnfinalized
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => PerProofUnfinalized WrapIPARounds (Type2 (FVar WrapField)) (FVar WrapField) (BoolVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m
       (UnfinalizedProof WrapIPARounds (FVar WrapField) (Type2 (SplitField (FVar WrapField) (BoolVar WrapField))) (BoolVar WrapField))
splitPerProofUnfinalized (PerProofUnfinalized r) = do
  let unType2 (Type2 x) = x
  cipSF <- splitFieldCircuit (unType2 r.combinedInnerProduct)
  bSF <- splitFieldCircuit (unType2 r.b)
  ztSrsSF <- splitFieldCircuit (unType2 r.zetaToSrsLength)
  ztDomSF <- splitFieldCircuit (unType2 r.zetaToDomainSize)
  permSF <- splitFieldCircuit (unType2 r.perm)
  pure
    { deferredValues:
        { plonk:
            { alpha: coerce r.alpha :: SizedF 128 (FVar WrapField)
            , beta: coerce r.beta :: SizedF 128 (FVar WrapField)
            , gamma: coerce r.gamma :: SizedF 128 (FVar WrapField)
            , zeta: coerce r.zeta :: SizedF 128 (FVar WrapField)
            , perm: Type2 permSF
            , zetaToSrsLength: Type2 ztSrsSF
            , zetaToDomainSize: Type2 ztDomSF
            }
        , combinedInnerProduct: Type2 cipSF
        , b: Type2 bSF
        , xi: coerce r.xi :: SizedF 128 (FVar WrapField)
        , bulletproofChallenges: coerce r.bulletproofChallenges :: Vector WrapIPARounds (SizedF 128 (FVar WrapField))
        }
    , shouldFinalize: r.shouldFinalize
    , spongeDigestBeforeEvaluations: r.spongeDigest
    }

-------------------------------------------------------------------------------
-- | The main wrap circuit.
-- |
-- | Body order matches `wrap_main.ml` lines 222-572 verbatim. Each `exists`
-- | call mirrors one OCaml `Req.*` request.
-------------------------------------------------------------------------------

wrapMain
  :: forall @branches @slot0Width @slot1Width pad0 pad1 _branchesPred t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => WrapWitnessM branches MaxProofsVerified slot0Width slot1Width VestaG WrapField m
  => Reflectable branches Int
  => Reflectable slot0Width Int
  => Reflectable slot1Width Int
  => Reflectable pad0 Int
  => Reflectable pad1 Int
  => Add pad0 slot0Width MaxProofsVerified
  => Add pad1 slot1Width MaxProofsVerified
  => Add 1 _branchesPred branches
  => WrapMainConfig branches
  -> WrapMainInputVar
  -> Snarky (KimchiConstraint WrapField) t m Unit
wrapMain config (WrapStatementPacked stmtR) = do
  let
    wrapEndo = let Curves.EndoScalar e = Curves.endoScalar @Pallas.BaseField @WrapField in e
    wrapIpaRounds = reflectType (Proxy @WrapIPARounds)
    wrapDomainLog2 = wrapIpaRounds
    wrapSrsLengthLog2 = wrapIpaRounds

    boolToField :: BoolVar WrapField -> FVar WrapField
    boolToField = coerce

    -- Project the WrapStatementPacked vectors into named fields, in OCaml
    -- `to_data` order. The `coerce` calls strip the `UnChecked` wrapper —
    -- this is the explicit "trusted from public input" boundary the
    -- conceptually-pure design exposes (see WrapStatementPacked docs).
    fpVec = stmtR.fpFields
    chalVec = stmtR.challenges
    scalarChalVec = stmtR.scalarChallenges
    digestVec = stmtR.digests

    stmt =
      { plonk:
          { alpha: coerce (Vector.index scalarChalVec (unsafeFinite @3 0)) :: SizedF 128 (FVar WrapField)
          , beta: coerce (Vector.index chalVec (unsafeFinite @2 0)) :: SizedF 128 (FVar WrapField)
          , gamma: coerce (Vector.index chalVec (unsafeFinite @2 1)) :: SizedF 128 (FVar WrapField)
          , zeta: coerce (Vector.index scalarChalVec (unsafeFinite @3 1)) :: SizedF 128 (FVar WrapField)
          , perm: Vector.index fpVec (unsafeFinite @5 4)
          , zetaToSrsLength: Vector.index fpVec (unsafeFinite @5 2)
          , zetaToDomainSize: Vector.index fpVec (unsafeFinite @5 3)
          }
      , combinedInnerProduct: Vector.index fpVec (unsafeFinite @5 0)
      , b: Vector.index fpVec (unsafeFinite @5 1)
      , xi: coerce (Vector.index scalarChalVec (unsafeFinite @3 2)) :: SizedF 128 (FVar WrapField)
      , bulletproofChallenges:
          map (coerce :: UnChecked (SizedF 128 (FVar WrapField)) -> SizedF 128 (FVar WrapField)) stmtR.bulletproofChallenges
      , spongeDigestBeforeEvaluations: Vector.index digestVec (unsafeFinite @3 0)
      , messagesForNextWrapProofDigest: Vector.index digestVec (unsafeFinite @3 1)
      , messagesForNextStepProof: Vector.index digestVec (unsafeFinite @3 2)
      , branchData: stmtR.branchData
      }

  -- 1. Req.Which_branch  (wrap_main.ml:223)
  whichBranchField <- label "which-branch" $ exists $ lift $
    getWhichBranch @branches @MaxProofsVerified @slot0Width @slot1Width @VestaG unit

  -- 2. In-circuit derivation: one-hot vector, ones_vector, branch_data assert
  --    (wrap_main.ml:228-256)
  whichBranch <- label "block1-one-hot" $
    Pseudo.oneHotVector @branches whichBranchField

  firstZero <- label "block1-first-zero" $
    Pseudo.choose whichBranch config.stepWidths
      (\w -> const_ (fromInt w))

  { maskVal0, maskVal1 } <- label "block1-ones-vector" do
    eq0 <- equals_ firstZero (const_ zero)
    v0 <- and_ true_ (not_ eq0)
    eq1 <- equals_ firstZero (const_ one)
    v1 <- and_ v0 (not_ eq1)
    pure { maskVal0: v0, maskVal1: v1 }

  domainLog2 <- label "block1-domain-log2" $
    Pseudo.choose whichBranch config.domainLog2s
      (\d -> const_ (fromInt d))

  label "block1-branch-data-assert" do
    let
      two = fromInt 2 :: WrapField
      four = fromInt 4 :: WrapField
      maskVal0Field :: FVar WrapField
      maskVal0Field = coerce maskVal0
      maskVal1Field :: FVar WrapField
      maskVal1Field = coerce maskVal1
    let twoTimesMask0 = CVar.scale_ two maskVal0Field
    let packedMask = add_ maskVal1Field twoTimesMask0
    let fourTimesDom = CVar.scale_ four domainLog2
    let packedBranchData = add_ packedMask fourTimesDom
    -- The wrap statement's branch_data is a single packed field (4*log2 + mask),
    -- matching OCaml's `Branch_data.wrap_packed_typ`.
    assertEqual_ stmt.branchData packedBranchData

  -- 3. Req.Proof_state (wrap_main.ml:257-267)
  WrapPrevProofState pps <- label "proof-state" $ exists $ lift $
    getWrapProofState @branches @MaxProofsVerified @slot0Width @slot1Width @VestaG unit
  let
    prevUnfinalized = pps.unfinalizedProofs
    prevMsgForNextStep = pps.messagesForNextStepProof

  -- 4. Block 2: chooseKey + feature flag consistency (wrap_main.ml:269-365)
  chosenVK <- chooseKey whichBranch config.stepKeys
  let
    chosenSigmaCommLast = Vector.index chosenVK.sigmaComm (unsafeFinite @7 6)
    chosenColumnComms =
      { index:
          chosenVK.genericComm :< chosenVK.psmComm :< chosenVK.completeAddComm
            :< chosenVK.mulComm
            :< chosenVK.emulComm
            :< chosenVK.endomulScalarComm
            :< Vector.nil
      , coeff: chosenVK.coefficientsComm
      , sigma: Vector.take @6 chosenVK.sigmaComm
      }

  -- 5. Req.Step_accs (wrap_main.ml:367-371)
  stepAccs <- label "step-accs" $ exists $ lift $
    getStepAccs @branches @MaxProofsVerified @slot0Width @slot1Width @VestaG unit
  let stepAccsAffine = map unwrapPt stepAccs

  -- 6. Req.Old_bulletproof_challenges (wrap_main.ml:372-404)
  WrapOldBpChals oldBp <- label "old-bp-chals" $ exists $ lift $
    getOldBulletproofChallenges @branches @MaxProofsVerified @slot0Width @slot1Width @VestaG unit

  -- 7. Req.Evals (wrap_main.ml:405-415)
  rawEvals <- label "evals" $ exists $ lift $
    getEvals @branches @MaxProofsVerified @slot0Width @slot1Width @VestaG unit

  -- 8. Req.Wrap_domain_indices (wrap_main.ml:418-424)
  wrapDomainIndices <- label "wrap-domain-indices" $ exists $ lift $
    getWrapDomainIndices @branches @MaxProofsVerified @slot0Width @slot1Width @VestaG unit

  -- 9. FOP loop (wrap_main.ml:435-487).
  --    OCaml's Vector.mapn evaluates right-to-left (proof mpv-1 first).
  --    For mpv=2: proof 1 first, then proof 0.
  let
    domainConfig =
      { shifts: LinFFI.domainShifts @WrapField
      , domainGenerator: LinFFI.domainGenerator @WrapField
      }
    fopBaseParams =
      { domainLog2: wrapDomainLog2
      , srsLengthLog2: wrapSrsLengthLog2
      , endo: wrapEndo
      , linearizationPoly: Linearization.vesta
      }

    -- Project the index-i `PerProofUnfinalized` and `StepAllEvals` for the
    -- two FOP iterations.
    unfView0 = unpackUnfinalized (Vector.index prevUnfinalized (unsafeFinite @MaxProofsVerified 0))
    unfView1 = unpackUnfinalized (Vector.index prevUnfinalized (unsafeFinite @MaxProofsVerified 1))
    witness0 = stepAllEvalsToProofWitness (Vector.index rawEvals (unsafeFinite @MaxProofsVerified 0))
    witness1 = stepAllEvalsToProofWitness (Vector.index rawEvals (unsafeFinite @MaxProofsVerified 1))

    -- Pad each slot's challenges to MaxProofsVerified by prepending dummies
    -- (matches OCaml `Wrap_hack.Checked.pad_challenges`).
    paddedChals0 = padWrapChallenges oldBp.slot0
    paddedChals1 = padWrapChallenges oldBp.slot1

  -- Right-to-left: process proof 1 first, then proof 0 (matches OCaml
  -- Vector.mapn evaluation order via right-to-left ::).
  which1 <- label "block3-wrap-domain-1" $
    Pseudo.oneHotVector @3 (Vector.index wrapDomainIndices (unsafeFinite @MaxProofsVerified 1))
  domain1 <- Pseudo.toDomain @16 domainConfig which1 config.allPossibleDomainLog2s

  which0 <- label "block3-wrap-domain-0" $
    Pseudo.oneHotVector @3 (Vector.index wrapDomainIndices (unsafeFinite @MaxProofsVerified 0))
  domain0 <- Pseudo.toDomain @16 domainConfig which0 config.allPossibleDomainLog2s

  -- FOP proof 0. Use the per-domain `vanishingPolynomial` from
  -- `Pseudo.toDomain` (which mirrors OCaml's `wrap_domain.vanishing_polynomial`)
  -- — NOT a hand-rolled `pow2PowMul` wrapper.
  { finalized: finalized0, expandedChallenges: expandedChals0 } <- wrapFinalizeOtherProofCircuit
    (Record.merge { domain: { generator: domain0.generator, shifts: domain0.shifts } } fopBaseParams)
    domain0.vanishingPolynomial
    { unfinalized: unfView0
    , witness: witness0
    , prevChallenges: paddedChals0
    }
  label "block3-fop-assert-0" do
    assertAny_ [ finalized0, not_ unfView0.shouldFinalize ]

  -- FOP proof 1
  { finalized: finalized1, expandedChallenges: expandedChals1 } <- wrapFinalizeOtherProofCircuit
    (Record.merge { domain: { generator: domain1.generator, shifts: domain1.shifts } } fopBaseParams)
    domain1.vanishingPolynomial
    { unfinalized: unfView1
    , witness: witness1
    , prevChallenges: paddedChals1
    }
  label "block3-fop-assert-1" do
    assertAny_ [ finalized1, not_ unfView1.shouldFinalize ]

  -- 10. Message hash loop (wrap_main.ml:489-505) — right-to-left.
  -- The dummyPaddingSpongeStates table holds pre-absorbed sponge states for
  -- (Padded_length - real_count) dummy challenge vectors per slot. Indexing
  -- by the slot's REAL width gives the sponge state ready to absorb the real
  -- challenges.
  let
    states = dummyPaddingSpongeStates dummyIpaChallenges.wrapExpanded
    spongeIdx0 = reflectType (Proxy @slot0Width)
    spongeIdx1 = reflectType (Proxy @slot1Width)
    state0 = Vector.index states (unsafeFinite @3 spongeIdx0)
    state1 = Vector.index states (unsafeFinite @3 spongeIdx1)
  msgForWrap1 <- label "block4-msg-hash-1"
    $ evalSpongeM (spongeFromConstants { state: state1.state, spongeState: state1.spongeState })
    $ hashMessagesForNextWrapProofCircuit'
        { sg: Vector.index stepAccsAffine (unsafeFinite @MaxProofsVerified 1)
        , allChallenges: oldBp.slot1
        }
  msgForWrap0 <- label "block4-msg-hash-0"
    $ evalSpongeM (spongeFromConstants { state: state0.state, spongeState: state0.spongeState })
    $ hashMessagesForNextWrapProofCircuit'
        { sg: Vector.index stepAccsAffine (unsafeFinite @MaxProofsVerified 0)
        , allChallenges: oldBp.slot0
        }

  label "block4-assert-msg-step" $
    assertEqual_ stmt.messagesForNextStepProof prevMsgForNextStep

  -- 11. Req.Openings_proof (wrap_main.ml:506-532)
  WrapProofOpening openingProofRec <- label "openings-proof" $ exists $ lift $
    getOpeningProof @branches @MaxProofsVerified @slot0Width @slot1Width @VestaG unit
  let
    openingProof =
      { lr: map (\r -> { l: unwrapPt r.l, r: unwrapPt r.r }) openingProofRec.lr
      , z1: openingProofRec.z1
      , z2: openingProofRec.z2
      , delta: unwrapPt openingProofRec.delta
      , sg: unwrapPt openingProofRec.sg
      }

  -- 12. Req.Messages (wrap_main.ml:533-541)
  WrapProofMessages messagesRec <- label "messages" $ exists $ lift $
    getMessages @branches @MaxProofsVerified @slot0Width @slot1Width @VestaG unit
  let
    messages =
      { wComm: map unwrapPt messagesRec.wComm
      , zComm: unwrapPt messagesRec.zComm
      , tComm: map unwrapPt messagesRec.tComm
      }

  -- 13. pack_statement + split_field per Type1 (wrap_main.ml:542-548)
  -- For each PerProofUnfinalized, take its 5 raw `Type2 (FVar f)` deferred
  -- fields, run `splitFieldCircuit` on the inner var to derive
  -- `(sDiv2, sOdd)`, and rebuild as `Type2 (SplitField (FVar f) (BoolVar f))`
  -- — the format the wrap verifier consumes for x_hat MSM.
  splitProofs <- label "block5-split-field" $
    traverse splitPerProofUnfinalized prevUnfinalized
  let
    publicInput :: PackedStepPublicInput MaxProofsVerified WrapIPARounds (FVar WrapField) (BoolVar WrapField)
    publicInput = PackedStepPublicInput
      { proofState:
          { unfinalizedProofs: splitProofs
          , messagesForNextStepProof: prevMsgForNextStep
          }
      , messagesForNextWrapProof: msgForWrap0 :< msgForWrap1 :< Vector.nil
      }

  -- 14. Block 6: wrapVerify (IVP + 4 assertions)
  let
    branchBools :: Vector branches (FVar WrapField)
    branchBools = map boolToField whichBranch
    { head: bb0, tail: bbRest } = Vector.uncons branchBools
    maskByBools :: AffinePoint (F WrapField) -> AffinePoint (FVar WrapField)
    maskByBools { x: F x', y: F y' } =
      let
        scaledX0 = CVar.scale_ x' bb0
        scaledY0 = CVar.scale_ y' bb0
        { x: finalX, y: finalY } = foldl
          (\acc b -> { x: CVar.add_ acc.x (CVar.scale_ x' b), y: CVar.add_ acc.y (CVar.scale_ y' b) })
          { x: scaledX0, y: scaledY0 }
          bbRest
      in
        { x: finalX, y: finalY }
    maskedLagrangeComms = map
      (\lb -> { constant: lb.constant, circuit: lb.circuit, maskPt: maskByBools })
      config.lagrangeComms
    ivpParams =
      { curveParams: curveParams (Proxy @VestaG)
      , lagrangeComms: maskedLagrangeComms
      , blindingH: config.blindingH
      , correctionMode: InCircuitCorrections
      , endo: wrapEndo
      , groupMapParams: groupMapParams (Proxy @VestaG)
      , useOptSponge: true
      }
    fullIvpInput =
      { publicInput
      , sgOld: Vector.index stepAccsAffine (unsafeFinite @MaxProofsVerified 0)
          :< Vector.index stepAccsAffine (unsafeFinite @MaxProofsVerified 1)
          :< Vector.nil
      , sgOldMask: boolToField maskVal1 :< boolToField maskVal0 :< Vector.nil
      , sigmaCommLast: chosenSigmaCommLast
      , columnComms: chosenColumnComms
      , deferredValues:
          { plonk: stmt.plonk
          , combinedInnerProduct: stmt.combinedInnerProduct
          , b: stmt.b
          , xi: stmt.xi
          , bulletproofChallenges: stmt.bulletproofChallenges
          }
      , wComm: messages.wComm
      , zComm: messages.zComm
      , tComm: messages.tComm
      , opening: openingProof
      }
    verifyInput =
      { spongeDigestBeforeEvaluations: stmt.spongeDigestBeforeEvaluations
      , messagesForNextWrapProofDigest: stmt.messagesForNextWrapProofDigest
      , bulletproofChallenges: stmt.bulletproofChallenges
      , newBpChallenges: expandedChals0 :< expandedChals1 :< Vector.nil
      , sg: openingProof.sg
      }

  wrapVerify ivpParams fullIvpInput verifyInput

-------------------------------------------------------------------------------
-- | Compile wrapMain
-- |
-- | Mirrors `compileStepMain` (Pickles.Step.Main): uses `compile` with the
-- | `Effect` base monad. The `Effect` instance of `WrapWitnessM` throws on
-- | every method, but during compilation `exists` discards the prover side
-- | so the throws never fire. `unsafePerformEffect` is sound here because
-- | compilation is deterministic and pure-in-effect.
-------------------------------------------------------------------------------

compileWrapMain
  :: forall @branches @slot0Width @slot1Width pad0 pad1 _branchesPred
   . Reflectable branches Int
  => Reflectable slot0Width Int
  => Reflectable slot1Width Int
  => Reflectable pad0 Int
  => Reflectable pad1 Int
  => Add pad0 slot0Width MaxProofsVerified
  => Add pad1 slot1Width MaxProofsVerified
  => Add 1 _branchesPred branches
  => WrapMainConfig branches
  -> CircuitBuilderState (KimchiGate WrapField) (AuxState WrapField)
compileWrapMain config = unsafePerformEffect $
  compile
    (Proxy @WrapMainInput)
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    (\stmt -> wrapMain @branches @slot0Width @slot1Width config stmt)
    Kimchi.initialState
