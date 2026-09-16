-- | The wrap circuit: verifies one step proof, producing the proof a
-- | later step circuit verifies in turn.
-- |
-- | `branches` is the number of step-circuit variants the wrap circuit
-- | accepts; `mpv` is the number of previous-proof slots the step
-- | statement carries. The per-slot bullet-proof widths arrive as a
-- | runtime `Vector mpv Int` argument, not as a type-level shape.
module Pickles.Wrap.Main
  ( WrapMainConfig
  , WrapMainInput
  , WrapMainInputVar
  , wrapMain
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (Finite, getFinite, unsafeFinite)
import Data.Foldable (foldl)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Newtype (over)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst)
import Data.Vector (Vector, (!!), (:<))
import Data.Vector as Vector
import Effect.Exception.Unsafe (unsafeThrow)
import Pickles.Constants (zkRowsByDefault)
import Pickles.DeferredValues (UnfinalizedProof)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Field (WrapField)
import Pickles.FinalizeOtherProof (DomainMode(..))
import Pickles.IncrementallyVerifyProof.FqSpongeTranscript (ivpTrace)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PackedStatement (PackedStepPublicInput(..))
import Pickles.Pseudo (PlonkDomain)
import Pickles.Pseudo as Pseudo
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBaseLookup, pow2pow)
import Pickles.PublicInputCommit (unwrapPt, wrapPt) as PIC
import Pickles.Sponge (evalSpongeM, spongeFromConstants)
import Pickles.Typ (existsTyp, perSlotTyp, typOf)
import Pickles.Types (AllocEvals(..), ChunkedCommitment(..), Evals, PaddedLength, PerProofUnfinalized(..), StepIPARounds, WrapIPARounds, WrapProofMessages(..), WrapProofOpening(..))
import Pickles.VerificationKey (StepVK, chooseKey)
import Pickles.Wrap.Advice (WrapAdvice)
import Pickles.Wrap.FinalizeOtherProof (wrapFinalizeOtherProofCircuit)
import Pickles.Wrap.MessageHash (dummyPaddingSpongeStates, hashMessagesForNextWrapProofCircuit')
import Pickles.Wrap.Types (PrevProofState(..), StatementPacked(..))
import Pickles.Wrap.Verify (wrapVerify)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import RandomOracle.Sponge (Sponge)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (add_, scale_) as CVar
import Snarky.Circuit.DSL (Bool(..), BoolVar, F(..), FVar, Snarky, UnChecked(..), add_, and_, assertAny_, assertEqual_, const_, equals_, exists, label, not_, true_)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (SplitField(..), Type1, Type2(..), groupMapParams)
import Snarky.Circuit.Kimchi.Utils (mapAccumM)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField, curveParams, fromInt)
import Snarky.Curves.Class (EndoScalar(..), endoScalar) as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..), WeierstrassAffinePoint(..))
import Snarky.Data.EllipticCurve as EC
import Snarky.Types.Shifted (splitFieldCircuit)
import Type.Proxy (Proxy(..))

-- | Public input to `wrapMain`, at value level.
-- |
-- | The bullet-proof challenge length is `StepIPARounds` (16): the wrap
-- | statement carries the deferred values of the step proof this
-- | circuit verifies.
type WrapMainInput :: Type
type WrapMainInput =
  StatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean

-- | Public input to `wrapMain`, at var level.
type WrapMainInputVar :: Type
type WrapMainInputVar =
  StatementPacked StepIPARounds (Type1 (FVar WrapField)) (FVar WrapField) (BoolVar WrapField)

-- | Compile-time configuration for `wrapMain`: one step width, domain
-- | log2 and step verification key per branch, plus the lagrange data
-- | the public-input commitment needs.
-- |
-- | `allPossibleDomainLog2s` holds one wrap-domain log2 per
-- | `proofs_verified ∈ {0, 1, 2}` — in production `{13, 14, 15}`. The
-- | `Finite 16` bound is `1 + WrapIPARounds`, since a wrap domain is at
-- | most the wrap SRS size `2^WrapIPARounds`.
type WrapMainConfig branches stepChunks =
  { stepWidths :: Vector branches Int
  , domainLog2s :: Vector branches Int
  , stepKeys :: Vector branches (StepVK stepChunks (FVar WrapField))
  -- Lagrange basis for the shared-domain fast path. Always populated;
  -- when `perBranchLagrangeAt` is `Just`, it holds the head domain's
  -- basis and is not consulted. `stepChunks` is the step proof's chunk
  -- count: above one, the basis splits over the wrap SRS and the
  -- public-input commitment accumulates chunkwise.
  , lagrangeAt :: LagrangeBaseLookup stepChunks WrapField
  -- Per-branch lagrange constants per index, for when branch domains
  -- differ: `f i` gives each branch one `Vector stepChunks` of constant
  -- chunks at that branch's own domain log2. `Nothing` selects the
  -- shared-domain fast path.
  , perBranchLagrangeAt ::
      Maybe (Int -> Vector branches (Vector stepChunks (AffinePoint (F WrapField))))
  , blindingH :: AffinePoint (F WrapField)
  , allPossibleDomainLog2s :: Vector 3 (Finite 16)
  }

-- | The unfinalized-proof shape `wrapFinalizeOtherProofCircuit`
-- | consumes, projected from a `PerProofUnfinalized`.
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
unwrapPt (WeierstrassAffinePoint pt) = AffinePoint pt


type FopBodyParams f =
  { domainLog2 :: Int
  , srsLengthLog2 :: Int
  , zkRows :: Int
  , endo :: f
  , linearizationPoly :: LinearizationPoly f
  }

-- | Finalize one slot's deferred values against an already-computed
-- | `PlonkDomain` and already-padded challenges, then assert the slot
-- | either finalized or was not to be finalized. Returns the slot's
-- | expanded bullet-proof challenges.
-- |
-- | Computing the domain and the padding stays with the caller: every
-- | slot's domain is emitted before any slot's FOP body, and that
-- | order is part of the circuit.
processOneSlotFopBody
  :: forall r
   . PrimeField WrapField
  => FopBodyParams WrapField
  -> Int -- slotIdx, for label only
  -> PlonkDomain WrapField r
  -> UnfinalizedView
  -> Evals (FVar WrapField)
  -> Vector PaddedLength (Vector WrapIPARounds (FVar WrapField)) -- pre-padded chals
  -> Snarky WrapField (KimchiConstraint WrapField) r (Vector WrapIPARounds (FVar WrapField))
processOneSlotFopBody fopBaseParams slotIdx domain unfView allEvals paddedChals = do
  { finalized, expandedChallenges } <- wrapFinalizeOtherProofCircuit
    { domains:
        { generator: domain.generator, log2: fopBaseParams.domainLog2 } :< Vector.nil
    , shifts: domain.shifts
    , srsLengthLog2: fopBaseParams.srsLengthLog2
    , zkRows: fopBaseParams.zkRows
    , endo: fopBaseParams.endo
    , linearizationPoly: fopBaseParams.linearizationPoly
    -- Always known: the wrap circuit only verifies its own step
    -- branches, whose domains are fixed at wrap-compile time.
    -- Side-loading is a step-circuit concept.
    , domainMode: KnownDomainsMode
    }
    domain.vanishingPolynomial
    { unfinalized: unfView
    , allEvals
    , prevChallenges: paddedChals
    }
  label ("block3-fop-assert-" <> show slotIdx) do
    assertAny_ [ finalized, not_ unfView.shouldFinalize ]
  pure expandedChallenges

-- | Absorb one slot's `sg` and its unpadded bullet-proof challenges
-- | into the supplied sponge state, and squeeze the digest. The caller
-- | chooses the state, which already has the slot's padding dummies
-- | absorbed.
hashOneSlotMessage
  :: forall r
   . PrimeField WrapField
  => Int -- slotIdx, for labels only
  -> Sponge WrapField -- precomputed sponge state for the slot's pad count
  -> AffinePoint (FVar WrapField) -- step accumulator sg for this slot
  -> Array (Vector WrapIPARounds (FVar WrapField)) -- raw (unpadded) chals
  -> Snarky WrapField (KimchiConstraint WrapField) r (FVar WrapField)
hashOneSlotMessage slotIdx spongeState sg allChallenges =
  label ("block4-msg-hash-" <> show slotIdx)
    $ evalSpongeM (spongeFromConstants { state: spongeState.state, spongeState: spongeState.spongeState })
    $ hashMessagesForNextWrapProofCircuit'
        { sg
        , allChallenges
        }

-- | Split each of a `PerProofUnfinalized`'s five deferred `Type2`
-- | fields into `(sDiv2, sOdd)`, giving the `UnfinalizedProof` shape
-- | `PackedStepPublicInput` packs for the x_hat MSM.
splitPerProofUnfinalized
  :: forall r
   . PrimeField WrapField
  => PerProofUnfinalized WrapIPARounds (Type2 (FVar WrapField)) (FVar WrapField) (BoolVar WrapField)
  -> Snarky WrapField (KimchiConstraint WrapField) r
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

-- | Allocates the per-slot bullet-proof challenges and hands them, with
-- | the widths, to `wrapMainCore`. Everything slot-shaped lives in
-- | these few lines.
-- |
-- | `widths` carries one `max_local_max_proofs_verified` per slot, as a
-- | value. `mpv` is their count and stays type-level because it sizes
-- | the statement vectors the circuit reads.
wrapMain
  :: forall @branches @mpv @stepChunks numChunksPred branchesPred totalBases totalBasesPred tCommLen tCommLenPred wCoeffN indexSigmaN chunkBases nonSgBases sg1 sg2 sg3 sg4 sg5 r
   . PrimeField WrapField
  => Reflectable stepChunks Int
  => Reflectable tCommLen Int
  => Reflectable nonSgBases Int
  => Compare 0 stepChunks LT
  => Add 1 numChunksPred stepChunks
  => Mul 7 stepChunks tCommLen
  => Add 1 tCommLenPred tCommLen
  => Mul 15 stepChunks wCoeffN
  => Mul 6 stepChunks indexSigmaN
  => Mul 44 stepChunks chunkBases
  => Add 1 chunkBases nonSgBases
  => Add stepChunks 1 sg1
  => Add sg1 stepChunks sg2
  => Add sg2 indexSigmaN sg3
  => Add sg3 wCoeffN sg4
  => Add sg4 wCoeffN sg5
  => Add sg5 indexSigmaN nonSgBases
  => Reflectable branches Int
  => Reflectable mpv Int
  => Add 1 branchesPred branches
  => Compare mpv 3 LT
  => Add mpv nonSgBases totalBases
  => Add 1 totalBasesPred totalBases
  => WrapMainConfig branches stepChunks
  -> WrapMainInputVar
  -> WrapAdvice mpv stepChunks
  -> Vector mpv Int
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
wrapMain config input advice widths =
  wrapMainCore @branches @stepChunks config input advice widths
    ( do
        slotsValue <- label "old-bp-chals" $ existsTyp
          (perSlotTyp (Vector.toUnfoldable widths) typOf)
          (pure advice <#> \r -> r.oldBpChals)
        pure (padPerSlot (map const_ dummyIpaChallenges.wrapExpanded) slotsValue)
    )
  where
  -- Front-pad each slot's stack to `PaddedLength`. The lengths come
  -- from `widths`, so both conversions are total; they throw rather
  -- than truncate because a mismatch would change the challenges the
  -- circuit absorbs.
  padPerSlot dummy perSlot =
    orThrow "wrapMain: slot count does not match mpv"
      ( Vector.toVector
          ( map
              ( \stack ->
                  orThrow "wrapMain: slot stack wider than PaddedLength"
                    ( Vector.toVector
                        ( Array.replicate
                            (reflectType (Proxy @PaddedLength) - Array.length stack)
                            dummy
                            <> stack
                        )
                    )
              )
              perSlot
          )
      )

  orThrow :: forall a. String -> Maybe a -> a
  orThrow msg = case _ of
    Just v -> v
    Nothing -> unsafeThrow msg

-- | The wrap circuit proper. Slot-shaped inputs reach it already
-- | flattened: the per-slot widths as a plain `Vector mpv Int`, and the
-- | padded bullet-proof challenge stacks as an action, which must stay
-- | an action because it allocates witness variables at a fixed point
-- | in the `exists` order.
wrapMainCore
  :: forall @branches @stepChunks numChunksPred mpv branchesPred totalBases totalBasesPred tCommLen tCommLenPred wCoeffN indexSigmaN chunkBases nonSgBases sg1 sg2 sg3 sg4 sg5 r
   . PrimeField WrapField
  => Reflectable stepChunks Int
  => Reflectable tCommLen Int
  => Reflectable nonSgBases Int
  => Compare 0 stepChunks LT
  => Add 1 numChunksPred stepChunks
  -- Base layout forwarded to `wrapVerify`: xHat(nc) :: ftComm ::
  -- zComm(nc) :: index(6nc) :: wComm(15nc) :: coeff(15nc) ::
  -- sigma(6nc), so the non-sg count is `1 + 44*nc`. `wCoeffN` and
  -- `indexSigmaN` are shared because `Mul`'s fundep would unify
  -- same-RHS counts otherwise.
  => Mul 7 stepChunks tCommLen
  => Add 1 tCommLenPred tCommLen
  => Mul 15 stepChunks wCoeffN
  => Mul 6 stepChunks indexSigmaN
  => Mul 44 stepChunks chunkBases
  => Add 1 chunkBases nonSgBases
  => Add stepChunks 1 sg1
  => Add sg1 stepChunks sg2
  => Add sg2 indexSigmaN sg3
  => Add sg3 wCoeffN sg4
  => Add sg4 wCoeffN sg5
  => Add sg5 indexSigmaN nonSgBases
  => Reflectable branches Int
  => Reflectable mpv Int
  => Add 1 branchesPred branches
  => Compare mpv 3 LT
  -- `wrapVerify`'s base-count constraints, with `sgOldN = mpv`.
  => Add mpv nonSgBases totalBases
  => Add 1 totalBasesPred totalBases
  => WrapMainConfig branches stepChunks
  -> WrapMainInputVar
  -> WrapAdvice mpv stepChunks
  -- Per-slot `max_local_max_proofs_verified`: selects the padding
  -- sponge state and recovers the unpadded challenges.
  -> Vector mpv Int
  -- Allocates `oldBpChals`, front-padded to `PaddedLength`. An action,
  -- not a value: it must allocate between `stepAccs` and `rawEvals`.
  -> Snarky WrapField (KimchiConstraint WrapField) r
       (Vector mpv (Vector PaddedLength (Vector WrapIPARounds (FVar WrapField))))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
wrapMainCore config (StatementPacked stmtR) advice slotWidths allocPaddedChals = do
  let
    wrapEndo = let Curves.EndoScalar e = Curves.endoScalar @Pallas.BaseField @WrapField in e
    wrapIpaRounds = reflectType (Proxy @WrapIPARounds)
    wrapDomainLog2 = wrapIpaRounds
    wrapSrsLengthLog2 = wrapIpaRounds

    boolToField = coerce

    -- Project the `StatementPacked` vectors into named fields. The
    -- `coerce` calls strip `UnChecked`: this is where values are taken
    -- on trust from the public input.
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

  whichBranchField <- label "which-branch" $ exists $
    pure advice <#> \r -> r.whichBranch

  whichBranch <- label "block1-one-hot" $
    Pseudo.oneHotVector @branches whichBranchField

  firstZero <- label "block1-first-zero" $
    Pseudo.choose whichBranch config.stepWidths
      (\w -> const_ (fromInt w))

  -- Per-slot mask, in slot order:
  -- `mask_i = mask_{i-1} && (firstZero /= i)`, starting from `true`.
  maskVals :: Vector mpv (BoolVar WrapField) <- label "block1-ones-vector"
    $ map fst
    $ mapAccumM
        ( \prevV i -> do
            eq <- equals_ firstZero (const_ (fromInt (getFinite i)))
            v <- and_ prevV (not_ eq)
            pure (Tuple v v)
        )
        true_
        (Vector.indices :: Vector mpv _)

  domainLog2 <- label "block1-domain-log2" $
    Pseudo.choose whichBranch config.domainLog2s
      (\d -> const_ (fromInt d))

  label "block1-branch-data-assert" do
    let
      four = fromInt 4 :: WrapField
      -- The mask packs into a fixed 2 bits — the cap on `mpv` — not
      -- into `mpv` bits, with `mask_i` at bit `1 - i`. So `mpv = 1`
      -- packs to `2*mask_0` and `mpv = 2` to `mask_1 + 2*mask_0`.
      branchDataMaskWidth = 2

      packedMask = foldl
        ( \acc (Tuple slotIdx m) ->
            let
              bitIdx = branchDataMaskWidth - 1 - slotIdx
              scaled = CVar.scale_ (fromInt (Int.pow 2 bitIdx) :: WrapField)
                (coerce m)
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
    -- `branchData` in the wrap statement is one packed field,
    -- `4*domainLog2 + mask`.
    assertEqual_ stmt.branchData packedBranchData

  PrevProofState pps <- label "proof-state" $ exists $
    pure advice <#> \r -> r.wrapProofState
  let
    prevUnfinalized = pps.unfinalizedProofs
    prevMsgForNextStep = pps.messagesForNextStepProof

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

  stepAccs <- label "step-accs" $ exists $
    pure advice <#> \r -> r.stepAccs
  let stepAccsAffine = map unwrapPt stepAccs

  paddedChalsAll <- allocPaddedChals

  rawEvals <- label "evals" $ exists $
    pure advice <#> \r -> r.evals

  wrapDomainIndices <- label "wrap-domain-indices" $ exists $
    pure advice <#> \r -> r.wrapDomainIndices

  -- Emission order is part of the circuit: every slot's Pseudo domain
  -- first, right-to-left, then every FOP body, left-to-right.
  let
    domainConfig =
      { shifts: LinFFI.domainShifts @WrapField
      , domainGenerator: LinFFI.domainGenerator @WrapField
      }
    fopBaseParams =
      { domainLog2: wrapDomainLog2
      , srsLengthLog2: wrapSrsLengthLog2
      -- Fixed at the default, independent of the step proof's chunking.
      , zkRows: zkRowsByDefault
      , endo: wrapEndo
      , linearizationPoly: Linearization.vesta
      }

    unfViews = map unpackUnfinalized prevUnfinalized

    witnesses = map (\(AllocEvals allEvals) -> allEvals) rawEvals

  domains <- do
    let
      revIdxs = Vector.reverse (Vector.generate @mpv getFinite)
      revWdis = Vector.reverse wrapDomainIndices
      revInputs = Vector.zip revIdxs revWdis
    revDomains <- traverse
      ( \(Tuple slotIdx wdi) -> do
          which <- label ("block3-wrap-domain-" <> show slotIdx) $
            -- One-hot over the 3 possible wrap domains.
            Pseudo.oneHotVector @3 wdi
          -- Bound: max wrap domain log2 + 1 = `WrapIPARounds` + 1.
          Pseudo.toDomain @16 domainConfig which config.allPossibleDomainLog2s
      )
      revInputs
    pure (Vector.reverse revDomains)

  expandedChalsAll <-
    let
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

  -- Right-to-left. `dummyPaddingSpongeStates` is indexed by the slot's
  -- real width `w`: entry `w` is the sponge after absorbing
  -- `PaddedLength - w` dummies offline, so each slot absorbs only its
  -- real challenges in circuit.
  let
    states = dummyPaddingSpongeStates dummyIpaChallenges.wrapExpanded
    paddedLenInt = reflectType (Proxy @PaddedLength)
    perSlotSponge = map (\w -> Vector.index states (unsafeFinite @3 w)) slotWidths

    -- Real challenges per slot: drop the leading padding. `Array`
    -- because the runtime slot width erases the type-level length.
    perSlotReal = Vector.zipWith
      (\w padded -> Array.drop (paddedLenInt - w) (Vector.toUnfoldable padded))
      slotWidths
      paddedChalsAll
  msgsForWrap <- do
    let
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
  forWithIndex_ msgsForWrap \fi v -> do
    let i = getFinite fi
    ivpTrace ("wrap.dbg.msgsForWrap." <> show i) v

  label "block4-assert-msg-step" $
    assertEqual_ stmt.messagesForNextStepProof prevMsgForNextStep

  WrapProofOpening openingProofRec <- label "openings-proof" $ exists $
    pure advice <#> \r -> r.openingProof
  let
    openingProof =
      { lr: map (\r -> { l: unwrapPt r.l, r: unwrapPt r.r }) openingProofRec.lr
      , z1: openingProofRec.z1
      , z2: openingProofRec.z2
      , delta: unwrapPt openingProofRec.delta
      , sg: unwrapPt openingProofRec.sg
      }

  WrapProofMessages messagesRec <- label "messages" $ exists $
    pure advice <#> \r -> r.messages
  let
    -- `wComm` and `zComm` stay chunked; `tComm` flattens to
    -- `7 * stepChunks` points.
    tCommChunked :: Vector 7 (ChunkedCommitment stepChunks (AffinePoint (FVar WrapField)))
    tCommChunked = map (over ChunkedCommitment (map unwrapPt)) messagesRec.tComm
    messages =
      { wComm: map (over ChunkedCommitment (map unwrapPt)) messagesRec.wComm
      , zComm: over ChunkedCommitment (map unwrapPt) messagesRec.zComm
      , tComm: Vector.concat (coerce tCommChunked :: Vector 7 (Vector stepChunks (AffinePoint (FVar WrapField))))
      }

  splitProofs <- label "block5-split-field" $
    traverse splitPerProofUnfinalized prevUnfinalized

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
    publicInput = PackedStepPublicInput
      { proofState:
          { unfinalizedProofs: splitProofs
          , messagesForNextStepProof: prevMsgForNextStep
          }
      , messagesForNextWrapProof: msgsForWrap
      }

  let
    branchBools = map boolToField whichBranch

    -- Coordinate-wise sum of the per-branch points, each scaled by its
    -- branch bool. `whichBranch` is 1-hot, so the result is the active
    -- branch's point.
    sumMaskByBranch
      :: Vector branches (AffinePoint (F WrapField))
      -> AffinePoint (FVar WrapField)
    sumMaskByBranch perBranchPts =
      let
        scaledPts = Vector.zipWith
          ( \b (AffinePoint { x: F x', y: F y' }) ->
              { x: CVar.scale_ x' b, y: CVar.scale_ y' b }
          )
          branchBools
          perBranchPts
        { head: spHead, tail: spTail } = Vector.uncons scaledPts
      in
        AffinePoint
          ( foldl
              ( \acc pt ->
                  { x: CVar.add_ acc.x pt.x, y: CVar.add_ acc.y pt.y }
              )
              spHead
              spTail
          )

    -- `sumMaskByBranch` per chunk index: at each chunk position, one
    -- point from each branch is muxed by `whichBranch`.
    sumMaskByBranchChunked
      :: Vector branches (Vector stepChunks (AffinePoint (F WrapField)))
      -> Vector stepChunks (AffinePoint (FVar WrapField))
    sumMaskByBranchChunked perBranchChunkedPts =
      Vector.generate \fi ->
        sumMaskByBranch (map (\vc -> vc !! fi) perBranchChunkedPts)

    -- Lagrange-base lookup driving `publicInputCommit`. `Nothing`:
    -- every branch shares the step domain, so one constant basis
    -- serves all of them. `Just`: the domains differ, so per-branch
    -- points are 1-hot summed and an in-circuit correction at scale
    -- `2^shift` is produced for `scalarMulLeaf`.
    --
    -- The `Nothing` arm still routes its constant through the 1-hot
    -- sum on `condAddPt`, and the `Just` arm carries a `constant`
    -- field nothing reads; both are load-bearing for the emitted
    -- constraints. Neither arm seals `condAddPt` — only step's
    -- side-loaded path does.
    maskedLagrangeAt :: LagrangeBaseLookup stepChunks WrapField
    maskedLagrangeAt i = case config.perBranchLagrangeAt of
      Nothing ->
        let
          lb = config.lagrangeAt i
          replicatedConst = Vector.replicate @branches lb.constant
        in
          { constant: lb.constant
          , circuit: lb.circuit
          , condAddPt: sumMaskByBranchChunked replicatedConst
          , correctionAt: Nothing
          , sealCondAddPt: false
          }
      Just perBranchAt ->
        let
          perBranchPts = perBranchAt i
          summed = sumMaskByBranchChunked perBranchPts
          correctionAtShift shift =
            sumMaskByBranchChunked
              ( map
                  ( map
                      ( \pt ->
                          PIC.wrapPt $ EC.negate_ $ PIC.unwrapPt
                            $ pow2pow (curveParams (Proxy @VestaG)) pt shift
                      )
                  )
                  perBranchPts
              )
        in
          { constant: (Vector.uncons perBranchPts).head
          , circuit: summed
          , condAddPt: summed
          , correctionAt: Just correctionAtShift
          , sealCondAddPt: false
          }
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

