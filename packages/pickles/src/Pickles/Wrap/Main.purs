-- | Wrap main circuit — the SNARK function for wrapping any step proof.
-- |
-- | Parameterized by:
-- | - @branches: number of step circuit variants
-- | - @slots: per-slot widths of `Max_widths_by_slot.maxes`, encoded
-- |   as one of `NoSlots` (mpv=0), `Slots1 w` (mpv=1), or
-- |   `Slots2 w0 w1` (mpv=2) from `Pickles.Wrap.Slots`. The `mpv`
-- |   parameter is derived from `slots` via the `slots -> mpv`
-- |   functional dependency on `PadSlots`.
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
  ) where

import Prelude

import Control.Monad.State.Trans (evalStateT, get, put)
import Control.Monad.Trans.Class (lift)
import Data.Array as Array
import Data.Fin (Finite, getFinite, unsafeFinite)
import Data.Foldable (foldl, for_)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Int as Int
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PackedStatement (PackedStepPublicInput(..))
import Pickles.ProofWitness (ProofWitness)
import Pickles.Pseudo (PlonkDomain)
import Pickles.Pseudo as Pseudo
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBaseLookup)
import Pickles.Sponge (evalSpongeM, spongeFromConstants)
import Pickles.Types (PaddedLength, PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepIPARounds, WrapField, WrapIPARounds, WrapPrevProofState(..), WrapProofMessages(..), WrapProofOpening(..), WrapStatementPacked(..))
import Pickles.VerificationKey (StepVK, chooseKey)
import Pickles.Verify (ivpTrace)
import Pickles.Verify.Types (UnfinalizedProof)
import Pickles.Wrap.Advice (class WrapWitnessM, getEvals, getMessages, getOldBulletproofChallenges, getOpeningProof, getStepAccs, getWhichBranch, getWrapDomainIndices, getWrapProofState)
import Pickles.Wrap.FinalizeOtherProof (wrapFinalizeOtherProofCircuit)
import Pickles.Wrap.MessageHash (dummyPaddingSpongeStates, hashMessagesForNextWrapProofCircuit')
import Pickles.Wrap.Slots (class PadSlots, padAllSlots, slotWidthsOf)
import Pickles.Wrap.Verify (wrapVerify)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import RandomOracle.Sponge (Sponge)
import Record as Record
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (add_, scale_) as CVar
import Snarky.Circuit.DSL (class CheckedType, class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, UnChecked(..), add_, and_, assertAny_, assertEqual_, const_, equals_, exists, label, not_, true_)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (SplitField(..), Type1, Type2(..), groupMapParams)
import Snarky.Circuit.Types (class CircuitType)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (EndoScalar(..), endoScalar) as Curves
import Snarky.Curves.Class (curveParams, fromInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Snarky.Types.Shifted (splitFieldCircuit)
import Type.Proxy (Proxy(..))

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
  , lagrangeAt :: LagrangeBaseLookup WrapField
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

-------------------------------------------------------------------------------
-- | Per-slot FOP body (post-Pseudo-domain).
-- |
-- | Encapsulates the "after domain has been computed" portion of one
-- | FOP iteration (wrap_main.ml:435-487): call
-- | `wrapFinalizeOtherProofCircuit` with the slot's pre-computed
-- | padded chals + pre-computed Pseudo domain, then emit the
-- | `assertAny_ [finalized, not should_finalize]` guard.
-- |
-- | Deliberately DOES NOT compute the Pseudo domain or padding — the
-- | caller does those in a separate phase to preserve OCaml's
-- | constraint emission order (all Pseudo computations first, then
-- | all FOP bodies — see the dedicated ordering commentary in
-- | `wrapMain`).
-- |
-- | Returns the per-slot expanded challenges (for downstream
-- | message-hash / wrap_verify wiring).
-- |
-- | `slotIdx` is only used in `label` strings.
-------------------------------------------------------------------------------

type FopBodyParams f =
  { domainLog2 :: Int
  , srsLengthLog2 :: Int
  , endo :: f
  , linearizationPoly :: LinearizationPoly f
  }

processOneSlotFopBody
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => FopBodyParams WrapField
  -> Int -- slotIdx, for label only
  -> PlonkDomain WrapField t m
  -> UnfinalizedView
  -> ProofWitness (FVar WrapField)
  -> Vector PaddedLength (Vector WrapIPARounds (FVar WrapField)) -- pre-padded chals
  -> Snarky (KimchiConstraint WrapField) t m (Vector WrapIPARounds (FVar WrapField))
processOneSlotFopBody fopBaseParams slotIdx domain unfView witness paddedChals = do
  { finalized, expandedChallenges } <- wrapFinalizeOtherProofCircuit
    ( Record.merge
        { domain: { generator: domain.generator, shifts: domain.shifts } }
        fopBaseParams
    )
    domain.vanishingPolynomial
    { unfinalized: unfView
    , witness
    , prevChallenges: paddedChals
    }
  label ("block3-fop-assert-" <> show slotIdx) do
    assertAny_ [ finalized, not_ unfView.shouldFinalize ]
  pure expandedChallenges

-------------------------------------------------------------------------------
-- | Per-slot message-hash body.
-- |
-- | Encapsulates one iteration of the message-hash loop
-- | (wrap_main.ml:489-505). The caller pre-computes the sponge state
-- | for this slot (indexed by `PaddedLength - slotWidth` into the
-- | `dummyPaddingSpongeStates` table) and passes it in; the helper
-- | absorbs `sg` + raw bp challenges and squeezes the digest.
-------------------------------------------------------------------------------

hashOneSlotMessage
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => Int -- slotIdx, for labels only
  -> Sponge WrapField -- precomputed sponge state for the slot's pad count
  -> AffinePoint (FVar WrapField) -- step accumulator sg for this slot
  -> Array (Vector WrapIPARounds (FVar WrapField)) -- raw (unpadded) chals
  -> Snarky (KimchiConstraint WrapField) t m (FVar WrapField)
hashOneSlotMessage slotIdx spongeState sg allChallenges =
  label ("block4-msg-hash-" <> show slotIdx)
    $ evalSpongeM (spongeFromConstants { state: spongeState.state, spongeState: spongeState.spongeState })
    $ hashMessagesForNextWrapProofCircuit'
        { sg
        , allChallenges
        }

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
  :: forall @branches @slots mpv _branchesPred totalBases _totalBasesPred t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  -- `slots` carries the per-slot widths; `mpv` is derived via the
  -- `slots -> mpv` fundep on `PadSlots`. Concrete instantiations
  -- supported today: `NoSlots` (mpv=0), `Slots1 w` (mpv=1),
  -- `Slots2 w0 w1` (mpv=2). The `Compare mpv 3 LT` constraint
  -- propagates into `wrapVerify`; today's pickles caps `mpv` at 2.
  => PadSlots slots mpv
  => WrapWitnessM branches mpv slots VestaG WrapField m
  -- `exists` on the result of `getOldBulletproofChallenges` needs
  -- both `CircuitType` and `CheckedType` instances for the `slots`
  -- shape. They exist for concrete `Slots1` / `Slots2` via the
  -- `Product` / `Const Unit` instances in `Snarky.Circuit.Types`
  -- — we just need to thread the constraints through the
  -- polymorphic header.
  => CircuitType WrapField
       (slots (Vector WrapIPARounds (F WrapField)))
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => CheckedType WrapField (KimchiConstraint WrapField)
       (slots (Vector WrapIPARounds (FVar WrapField)))
  => Reflectable branches Int
  => Reflectable mpv Int
  => Add 1 _branchesPred branches
  => Compare mpv 3 LT
  -- Forwarded to `wrapVerify` (which needs `Add sgOldN 45 totalBases`
  -- and `Add 1 _ totalBases`). With `sgOldN = mpv`, these collapse to
  -- the constraints below.
  => Add mpv 45 totalBases
  => Add 1 _totalBasesPred totalBases
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
    getWhichBranch @branches @mpv @slots @VestaG unit

  -- 2. In-circuit derivation: one-hot vector, ones_vector, branch_data assert
  --    (wrap_main.ml:228-256)
  whichBranch <- label "block1-one-hot" $
    Pseudo.oneHotVector @branches whichBranchField

  firstZero <- label "block1-first-zero" $
    Pseudo.choose whichBranch config.stepWidths
      (\w -> const_ (fromInt w))

  -- One-hot ones vector: `mask_i = previousMask && (firstZero != i)`,
  -- starting from `previousMask = true`. Returns a `Vector mpv` of the
  -- per-slot mask booleans in slot order. For mpv=2 this matches the
  -- old hand-unrolled `{ maskVal0, maskVal1 }` pair element-for-element
  -- (slot index = vector index).
  maskVals :: Vector mpv (BoolVar WrapField) <- label "block1-ones-vector" $
    flip evalStateT true_ $ Vector.generateA @mpv \i -> do
      prevV <- get
      eq <- lift $ equals_ firstZero (const_ (fromInt (getFinite i)))
      v <- lift $ and_ prevV (not_ eq)
      put v
      pure v

  domainLog2 <- label "block1-domain-log2" $
    Pseudo.choose whichBranch config.domainLog2s
      (\d -> const_ (fromInt d))

  label "block1-branch-data-assert" do
    let
      four = fromInt 4 :: WrapField
      -- OCaml's `Branch_data.Checked.Wrap.pack` always packs to
      -- `Nat.N2.n = 2` bits via `Vector.extend_front_exn ... Boolean.false_`,
      -- regardless of the actual `mpv`. So the bit width is FIXED at 2
      -- (the global Pickles cap), with `mask_i` going to bit `1 - i`.
      -- For mpv=1: `pack [false, mask_0] = 2*mask_0` (q_c = 2).
      -- For mpv=2: `pack [mask_1, mask_0] = mask_1 + 2*mask_0`
      --   (matches the old hand-unrolled `maskVal1 + 2*maskVal0`).
      branchDataMaskWidth = 2

      packedMask :: FVar WrapField
      packedMask = foldl
        ( \acc (Tuple slotIdx m) ->
            let
              bitIdx = branchDataMaskWidth - 1 - slotIdx
              scaled = CVar.scale_ (fromInt (Int.pow 2 bitIdx) :: WrapField)
                (coerce m :: FVar WrapField)
            in
              add_ acc scaled
        )
        (const_ zero)
        ( Array.zip
            (Array.range 0 (Vector.length maskVals - 1))
            (Vector.toUnfoldable maskVals)
        )
    let fourTimesDom = CVar.scale_ four domainLog2
    let packedBranchData = add_ packedMask fourTimesDom
    -- The wrap statement's branch_data is a single packed field (4*log2 + mask),
    -- matching OCaml's `Branch_data.wrap_packed_typ`.
    assertEqual_ stmt.branchData packedBranchData

  -- 3. Req.Proof_state (wrap_main.ml:257-267)
  WrapPrevProofState pps <- label "proof-state" $ exists $ lift $
    getWrapProofState @branches @mpv @slots @VestaG unit
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
    getStepAccs @branches @mpv @slots @VestaG unit
  let stepAccsAffine = map unwrapPt stepAccs

  -- 6. Req.Old_bulletproof_challenges (wrap_main.ml:372-404).
  -- Returns a `slots`-shaped value (one of `NoSlots`, `Slots1 w`,
  -- `Slots2 w0 w1`). The `PadSlots` class projects this into a
  -- uniform `Vector mpv (Vector PaddedLength a)`, prepending the
  -- right number of dummy bp-challenge stacks per slot to mirror
  -- OCaml's `Wrap_hack.Checked.pad_challenges`.
  slotsValue <- label "old-bp-chals" $ exists $ lift $
    getOldBulletproofChallenges @branches @mpv @slots @VestaG unit
  let
    dummyChallenge :: Vector WrapIPARounds (FVar WrapField)
    dummyChallenge = map const_ dummyIpaChallenges.wrapExpanded

    paddedChalsAll
      :: Vector mpv (Vector PaddedLength (Vector WrapIPARounds (FVar WrapField)))
    paddedChalsAll = padAllSlots dummyChallenge slotsValue

  -- 7. Req.Evals (wrap_main.ml:405-415)
  rawEvals <- label "evals" $ exists $ lift $
    getEvals @branches @mpv @slots @VestaG unit

  -- 8. Req.Wrap_domain_indices (wrap_main.ml:418-424)
  wrapDomainIndices <- label "wrap-domain-indices" $ exists $ lift $
    getWrapDomainIndices @branches @mpv @slots @VestaG unit

  -- 9. FOP loop (wrap_main.ml:435-487).
  --
  -- OCaml's ordering, reflected exactly:
  --   Pseudo domains first (right-to-left: slot N-1 down to slot 0)
  --   then FOP bodies    (left-to-right: slot 0 up to slot N-1)
  --
  -- `processOneSlotFopBody` encapsulates ONLY the post-Pseudo FOP
  -- portion (`wrapFinalizeOtherProofCircuit` + `assertAny_`). The
  -- Pseudo domain computations stay inline to preserve the
  -- all-Pseudos-before-all-FOPs emission order.
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

    -- Per-slot views projected uniformly. These are pure lets; the
    -- helpers consume the prepared views inside the monadic loops
    -- below, so emission order is determined by the traversals.
    unfViews :: Vector mpv UnfinalizedView
    unfViews = map unpackUnfinalized prevUnfinalized

    witnesses :: Vector mpv (ProofWitness (FVar WrapField))
    witnesses = map stepAllEvalsToProofWitness rawEvals

  -- Pseudo domains — right-to-left, matching OCaml's `Vector.map`
  -- evaluation order. We traverse the reversed `wrapDomainIndices`
  -- and reverse the result so the resulting `Vector mpv (PlonkDomain
  -- ...)` is back in slot order. The label index reflects the slot
  -- index (post-reverse), so slot N-1 is emitted first.
  domains <- do
    let
      revIdxs :: Vector mpv Int
      revIdxs = Vector.reverse (Vector.generate @mpv getFinite)
      revWdis = Vector.reverse wrapDomainIndices
      revInputs = Vector.zip revIdxs revWdis
    revDomains <- traverse
      ( \(Tuple slotIdx wdi) -> do
          which <- label ("block3-wrap-domain-" <> show slotIdx) $
            Pseudo.oneHotVector @3 wdi
          Pseudo.toDomain @16 domainConfig which config.allPossibleDomainLog2s
      )
      revInputs
    pure (Vector.reverse revDomains)

  -- FOP bodies — left-to-right (slot 0 first), matching the original
  -- hand-unrolled order. We traverse a `Vector mpv` of slot indices
  -- and look each piece up via `Vector.index` to keep the body
  -- record-flat instead of nesting Tuples.
  expandedChalsAll <-
    let
      idxs :: Vector mpv (Finite mpv)
      idxs = Vector.generate @mpv identity
    in
      traverse
        ( \fi -> do
            let
              slotIdx = getFinite fi
              dom = Vector.index domains fi
              unf = Vector.index unfViews fi
              wit = Vector.index witnesses fi
              chals = Vector.index paddedChalsAll fi
            processOneSlotFopBody fopBaseParams slotIdx dom unf wit chals
        )
        idxs

  -- 10. Message hash loop (wrap_main.ml:489-505) — right-to-left.
  -- The dummyPaddingSpongeStates table holds pre-absorbed sponge states
  -- indexed by the slot's REAL width: index w = sponge after absorbing
  -- `(PaddedLength - w)` dummies offline. Each per-slot hash absorbs
  -- only the unpadded real challenges, so total in-circuit Poseidon
  -- gates per slot = w × roundsPerVector.
  let
    states = dummyPaddingSpongeStates dummyIpaChallenges.wrapExpanded
    paddedLenInt = reflectType (Proxy @PaddedLength)
    slotWidths = slotWidthsOf (Proxy :: Proxy slots)
    perSlotSponge = map (\w -> Vector.index states (unsafeFinite @3 w)) slotWidths

    -- Real (unpadded) challenges per slot: drop the leading padding
    -- entries from each padded vector. Returns `Array` because the
    -- runtime slot width erases the type-level length.
    perSlotReal :: Vector mpv (Array (Vector WrapIPARounds (FVar WrapField)))
    perSlotReal = Vector.zipWith
      (\w padded -> Array.drop (paddedLenInt - w) (Vector.toUnfoldable padded))
      slotWidths
      paddedChalsAll
  msgsForWrap <- do
    let
      idxs :: Vector mpv (Finite mpv)
      idxs = Vector.generate @mpv identity
      revIdxs = Vector.reverse idxs
    revMsgs <- traverse
      ( \fi -> do
          let
            slotIdx = getFinite fi
            state = Vector.index perSlotSponge fi
            sg = Vector.index stepAccsAffine fi
            chals = Vector.index perSlotReal fi
          hashOneSlotMessage slotIdx state sg chals
      )
      revIdxs
    pure (Vector.reverse revMsgs)

  label "block4-assert-msg-step" $
    assertEqual_ stmt.messagesForNextStepProof prevMsgForNextStep

  -- 11. Req.Openings_proof (wrap_main.ml:506-532)
  WrapProofOpening openingProofRec <- label "openings-proof" $ exists $ lift $
    getOpeningProof @branches @mpv @slots @VestaG unit
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
    getMessages @branches @mpv @slots @VestaG unit
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

  -- DIAG: dump every walked field of splitProofs[0] so we can diff
  -- against OCaml's equivalent at wrap.ml pack_statement input point.
  -- The MSM walks these exact values, so any one that differs from
  -- OCaml localizes the remaining xhat divergence.
  forWithIndex_ splitProofs \fi sp -> do
    let slotIdx = getFinite fi
    let unType2Split (Type2 sf) = sf
    let cipSF = unType2Split sp.deferredValues.combinedInnerProduct
    let bSF = unType2Split sp.deferredValues.b
    let permSF = unType2Split sp.deferredValues.plonk.perm
    let ztSrsSF = unType2Split sp.deferredValues.plonk.zetaToSrsLength
    let ztDomSF = unType2Split sp.deferredValues.plonk.zetaToDomainSize
    ivpTrace ("wrap.dbg.unf" <> show slotIdx <> ".cip.sDiv2") (case cipSF of SplitField r -> r.sDiv2)
    ivpTrace ("wrap.dbg.unf" <> show slotIdx <> ".b.sDiv2") (case bSF of SplitField r -> r.sDiv2)
    ivpTrace ("wrap.dbg.unf" <> show slotIdx <> ".perm.sDiv2") (case permSF of SplitField r -> r.sDiv2)
    ivpTrace ("wrap.dbg.unf" <> show slotIdx <> ".ztSrs.sDiv2") (case ztSrsSF of SplitField r -> r.sDiv2)
    ivpTrace ("wrap.dbg.unf" <> show slotIdx <> ".ztDom.sDiv2") (case ztDomSF of SplitField r -> r.sDiv2)
    ivpTrace ("wrap.dbg.unf" <> show slotIdx <> ".spongeDigest") sp.spongeDigestBeforeEvaluations
    ivpTrace ("wrap.dbg.unf" <> show slotIdx <> ".alpha") (SizedF.toField sp.deferredValues.plonk.alpha)
    ivpTrace ("wrap.dbg.unf" <> show slotIdx <> ".beta") (SizedF.toField sp.deferredValues.plonk.beta)
    ivpTrace ("wrap.dbg.unf" <> show slotIdx <> ".gamma") (SizedF.toField sp.deferredValues.plonk.gamma)
    ivpTrace ("wrap.dbg.unf" <> show slotIdx <> ".zeta") (SizedF.toField sp.deferredValues.plonk.zeta)
    ivpTrace ("wrap.dbg.unf" <> show slotIdx <> ".xi") (SizedF.toField sp.deferredValues.xi)
    forWithIndex_ sp.deferredValues.bulletproofChallenges \fj c ->
      ivpTrace ("wrap.dbg.unf" <> show slotIdx <> ".bpc." <> show (getFinite fj)) (SizedF.toField c)

  let
    publicInput :: PackedStepPublicInput mpv WrapIPARounds (FVar WrapField) (BoolVar WrapField)
    publicInput = PackedStepPublicInput
      { proofState:
          { unfinalizedProofs: splitProofs
          , messagesForNextStepProof: prevMsgForNextStep
          }
      , messagesForNextWrapProof: msgsForWrap
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

    -- OCaml `lagrange_with_correction` masks each base by `which_branch`
    -- (step_verifier.ml:435) — we compose `maskByBools` into the underlying
    -- lookup so every `publicInputCommit` leaf that fetches at index `i`
    -- gets a branch-masked version of that base.
    maskedLagrangeAt :: LagrangeBaseLookup WrapField
    maskedLagrangeAt i =
      let
        lb = config.lagrangeAt i
      in
        { constant: lb.constant, circuit: lb.circuit, maskPt: maskByBools }
    ivpParams =
      { curveParams: curveParams (Proxy @VestaG)
      , lagrangeAt: maskedLagrangeAt
      , blindingH: config.blindingH
      , correctionMode: InCircuitCorrections
      , endo: wrapEndo
      , groupMapParams: groupMapParams (Proxy @VestaG)
      , useOptSponge: true
      }
    fullIvpInput =
      { publicInput
      , sgOld: stepAccsAffine
      , sgOldMask: Vector.reverse (map boolToField maskVals)
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
      , newBpChallenges: expandedChalsAll
      , sg: openingProof.sg
      }

  label "block6-wrapVerify" $ wrapVerify ivpParams fullIvpInput verifyInput

