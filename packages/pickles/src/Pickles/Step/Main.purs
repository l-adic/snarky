-- | The generic step circuit: run a rule's body, then verify the wrap
-- | proof of each previous proof the rule declares.
-- |
-- | Everything that varies between rules — the number of slots, each
-- | slot's previous-proof kind, its width and its domain set — comes
-- | from the caller's `prevsSpec`, so one `stepMain` serves every rule
-- | shape.
module Pickles.Step.Main
  ( module Pickles.Step.VkSource
  , class BuildSlotVkSources
  , buildSlotVkSources
  , RuleOutput
  , StepMainSrsData
  , UnfinalizedProof
  , liftDummyPerProofUnfinalized
  , stepMain
  , mpvFrontPad
  , mpvFrontPadVec
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (getFinite)
import Data.Foldable (foldM)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (over, unwrap)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (traverse)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Vector (Vector, (!!), (:<))
import Data.Vector as Vector
import Effect.Class (liftEffect)
import Effect.Exception.Unsafe (unsafeThrow)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Partial.Unsafe (unsafePartial)
import Pickles.DeferredValues (BranchData)
import Pickles.Field (StepField)
import Pickles.FinalizeOtherProof (DomainMode(..))
import Pickles.IncrementallyVerifyProof.FqSpongeTranscript (ivpTrace)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PublicInputCommit (CorrectionMode(..), mkSideloadedLagrangeLookup)
import Pickles.Sideload.Bundle (class HasSideLoadedVk, projectVk)
import Pickles.Sideload.VerificationKey (VerificationKey(..)) as SLVK
import Pickles.Slots (Slot)
import Pickles.Sponge (initialSpongeCircuit)
import Pickles.Step.Advice (StepAdvice(..))
import Pickles.Step.Dummy as Dummy
import Pickles.Step.Slots (class SlotStatementsCarrier, class StepSlotsCarrier, class StepSlotsTyp, PrevValues, Prevs, mkPrevValues, prevsVector, stepSlotsTyp, traverseStepSlotsAWithVk)
import Pickles.Step.Types (AllocBranchData(..), FopProofState(..), PerProofWitness(..), ProofState(..), UnfinalizedFieldCount, WrapProof(..))
import Pickles.Step.VerifyOne (VerifyOneInput, verifyOne)
import Pickles.Step.VkSource (SlotVkBlueprint(..), SlotVkSource(..))
import Pickles.Typ (existsTyp)
import Pickles.Types (AllocEvals(..), ChunkedCommitment(..), PaddedLength, PerProofUnfinalized(..), StepIPARounds, WrapIPARounds, WrapProofMessages(..), WrapProofOpening(..), WrapVkChunks)
import Pickles.VerificationKey (VerificationKey(..))
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (AsProver, Bool(..), BoolVar, F(..), FVar, Snarky, UnChecked(..), assertAll_, const_, exists, false_, label, true_)
import Snarky.Circuit.DSL.Monad (class CheckedType)
import Snarky.Circuit.DSL.SizedF (SizedF, toField)
import Snarky.Circuit.DSL.SizedF (unsafeFromField) as SizedF
import Snarky.Circuit.Kimchi (SplitField(..), Type1(..), Type2(..), groupMapParams)
import Snarky.Circuit.RandomOracle.Sponge as Sponge
import Snarky.Circuit.Types (class CircuitType, varToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField, EndoScalar(..), curveParams, endoScalar)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..), WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

-------------------------------------------------------------------------------
-- | Rule abstraction
-------------------------------------------------------------------------------

-- | What a rule's body returns: one `PrevStatement` per slot of its
-- | prevs spec, packed by `toPrevs`, and the rule's own public output.
-- | Each slot's statement has that slot's own type. A rule with no
-- | public output instantiates `output` at `Unit`.
type RuleOutput prevsSpec output =
  { prevs :: Prevs prevsSpec
  , publicOutput :: output
  }

-- | One `SlotVkSource` per slot, built by walking the spec-indexed
-- | blueprint carrier alongside the side-loaded VK cell carrier.
-- |
-- | The dispatch is on the slot's runtime `SlotVkBlueprint`:
-- | `BlueprintSelf` and `BlueprintExternal` pass straight through and
-- | never read their cell, while `BlueprintSideLoaded` allocates the
-- | runtime VK in-circuit with `exists` and bundles it with the
-- | compile-time per-domain lagrange tables.
-- |
-- | The instance head writes `wrapVkChunks` into both the blueprint
-- | and the source position, so a carrier whose slots disagree on the
-- | chunk count fails to resolve rather than being coerced into
-- | agreement.
class BuildSlotVkSources
  :: Type -> Type -> Int -> Int -> Type -> Type -> Type -> Constraint
class
  BuildSlotVkSources cell prevsSpec wrapVkChunks len blueprints cellCarrier vkCarrier
  | cell prevsSpec -> len blueprints cellCarrier
  , prevsSpec -> vkCarrier
  where
  buildSlotVkSources
    :: forall r
     . PrimeField StepField
    => blueprints
    -> cellCarrier
    -> Snarky StepField (KimchiConstraint StepField) r vkCarrier

instance BuildSlotVkSources cell Unit wrapVkChunks 0 Unit Unit Unit where
  buildSlotVkSources _ _ = pure unit

instance
  ( BuildSlotVkSources cell rest wrapVkChunks restLen restScaffolds restCellCarrier restVkCarrier
  , HasSideLoadedVk wrapVkChunks cell
  , Reflectable wrapVkChunks Int
  , CheckedType StepField (KimchiConstraint StepField)
      (SLVK.VerificationKey wrapVkChunks (FVar StepField) (BoolVar StepField))
  , Add restLen 1 len
  ) =>
  BuildSlotVkSources cell
    (Slot n stmt /\ rest)
    wrapVkChunks
    len
    (SlotVkBlueprint wrapVkChunks /\ restScaffolds)
    (cell /\ restCellCarrier)
    (SlotVkSource wrapVkChunks /\ restVkCarrier)
  where
  buildSlotVkSources (headBlueprint /\ restScaffolds) (headCell /\ restCellCarrier) = do
    headSrc <- case headBlueprint of
      BlueprintSelf lagrange -> pure (SharedExistsVk lagrange)
      BlueprintExternal lagrange v -> pure (ConstVk lagrange v)
      BlueprintSideLoaded headLagrange -> do
        headVar <- exists (pure (projectVk headCell))
        pure (SideloadedExistsVk headLagrange headVar)
    restSrcs <- buildSlotVkSources @cell @rest @wrapVkChunks restScaffolds restCellCarrier
    pure (headSrc /\ restSrcs)

-- | The SRS-derived and per-slot data `stepMain` needs beyond the
-- | rule itself: one shared SRS constant, then one entry per slot,
-- | since each slot's previous proof came from its own source.
type StepMainSrsData :: Int -> Int -> Type -> Type
type StepMainSrsData len nd blueprints =
  { -- | The Tock SRS `h` generator.
    blindingH :: AffinePoint (F StepField)
  -- | Per slot, every step-domain log2 the slot's previous-proof
  -- | source could have been produced at: one entry for a
  -- | single-branch source, one per branch for a multi-branch one.
  , perSlotFopDomainLog2s :: Vector len (Vector nd Int)
  -- | Per slot, the kimchi `zk_rows` its previous step proof's
  -- | deferred permutation scalar was produced at:
  -- | `zkRowsForNumChunks` of that rule's step chunk count.
  , perSlotFopZkRows :: Vector len Int
  -- | Per slot, the compile-time blueprint for where its wrap VK comes
  -- | from; `buildSlotVkSources` bundles in the runtime key for the
  -- | side-loaded slots. The shape mirrors `prevsSpec` slot for slot,
  -- | which is what fixes each cell's chunk count.
  , perSlotVkBlueprints :: blueprints
  }

-------------------------------------------------------------------------------
-- | Helpers
-------------------------------------------------------------------------------

unwrapPt :: WeierstrassAffinePoint PallasG (FVar StepField) -> AffinePoint (FVar StepField)
unwrapPt (WeierstrassAffinePoint pt) = AffinePoint pt

stepEndoVal :: StepField
stepEndoVal = let EndoScalar e = endoScalar @Vesta.BaseField @StepField in e

--------------------------------------------------------------------------------
-- mpvMax-padding
--------------------------------------------------------------------------------

mpvFrontPadVec
  :: forall a mpvPad len mpvMax
   . Add mpvPad len mpvMax
  => Vector mpvPad a
  -> Vector len a
  -> Vector mpvMax a
mpvFrontPadVec = Vector.append

-- | Front-pad a `Vector len a` with `mpvPad` copies of a dummy value.
-- |
-- | The dummy is a thunk so that the `mpvPad = 0` path never forces
-- | it: building one can trigger Rust FFI (lagrange and
-- | blinding-generator computations) that advances shared chacha8 RNG
-- | state. At `mpvPad = 0` the `Add` constraint gives `mpvMax = len`,
-- | which is what makes the `unsafeCoerce` sound.
mpvFrontPad
  :: forall a mpvPad len mpvMax
   . Add mpvPad len mpvMax
  => Reflectable mpvPad Int
  => Reflectable mpvMax Int
  => (Unit -> a)
  -> Vector len a
  -> Vector mpvMax a
mpvFrontPad mkDummy real =
  let
    n = reflectType (Proxy @mpvPad)
  in
    if n == 0 then unsafeCoerce real
    else
      let
        dummy = mkDummy unit
        arr =
          Array.replicate n dummy
            <> (Vector.toUnfoldable real)
      in
        unsafePartial $ fromJust $ Vector.toVector @mpvMax arr

-------------------------------------------------------------------------------
-- | Per-proof witness, reshaped for use
-------------------------------------------------------------------------------

type ReshapedPerProofWitness n stepChunks tCommLen =
  { wComm :: Vector 15 (ChunkedCommitment stepChunks (WeierstrassAffinePoint PallasG (FVar StepField)))
  , zComm :: ChunkedCommitment stepChunks (WeierstrassAffinePoint PallasG (FVar StepField))
  -- Flat tComm: tCommLen = 7 * stepChunks pieces of the quotient poly.
  , tComm :: Vector tCommLen (WeierstrassAffinePoint PallasG (FVar StepField))
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
  , branchData :: BranchData (FVar StepField) (BoolVar StepField)
  , prevChallenges :: Vector n (Vector StepIPARounds (FVar StepField))
  , prevSgs :: Vector n (WeierstrassAffinePoint PallasG (FVar StepField))
  }

-- | Reshape one allocated per-proof witness into the flatter record
-- | the rest of `stepMain` reads: `tComm` concatenated, the newtype
-- | wrappers unwrapped, and the two per-previous-proof arrays
-- | recovered at the slot's width.
-- |
-- | Nothing is allocated here: the `exists` happened upstream against
-- | `Pickles.Step.Types.perProofWitnessTyp`, whose field order is what
-- | fixes the variable indices.
reshapePerProofWitness
  :: forall @n @stepChunks tCommLen
   . Reflectable n Int
  => Reflectable stepChunks Int
  => Mul 7 stepChunks tCommLen
  -- | The slot's width, still type-level because everything below this
  -- | function is indexed by it.
  => Proxy n
  -> PerProofWitness stepChunks StepIPARounds WrapIPARounds (FVar StepField) (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (BoolVar StepField)
  -> ReshapedPerProofWitness n stepChunks tCommLen
reshapePerProofWitness _ (PerProofWitness ppw) =
  let
    WrapProof wrapProofRec = ppw.wrapProof
    WrapProofMessages msgRec = wrapProofRec.messages
    WrapProofOpening openRec = wrapProofRec.opening
    ProofState psRec = ppw.proofState
    FopProofState fopRec = psRec.fopState
    AllocBranchData branchDataRec = psRec.branchData
    AllocEvals allEvals = ppw.prevEvals

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

    tCommFlat :: Vector tCommLen (WeierstrassAffinePoint PallasG (FVar StepField))
    tCommFlat = Vector.concat (coerce msgRec.tComm :: Vector 7 (Vector stepChunks (WeierstrassAffinePoint PallasG (FVar StepField))))
  in
    { wComm: msgRec.wComm
    , zComm: msgRec.zComm
    , tComm: tCommFlat
    , lr: openRec.lr
    , z1: openRec.z1
    , z2: openRec.z2
    , delta: openRec.delta
    , sg: openRec.sg
    , fopState
    , allEvals
    , branchData:
        { proofsVerifiedMask: branchDataRec.proofsVerifiedMask
        , domainLog2: branchDataRec.domainLog2
        }
    , prevChallenges: coerce (atSlotWidth "prevChallenges" ppw.prevChallenges)
    , prevSgs: atSlotWidth "prevSgs" ppw.prevSgs
    }
  where
  -- The witness holds its per-previous-proof data as arrays, since the
  -- slot's width is not in its type; downstream code is still indexed
  -- by it, so the width is recovered once, here. `perProofWitnessTyp`
  -- allocated the array at the width the spec declares, so a mismatch
  -- is a bug in this module, not something a prover can provoke.
  atSlotWidth :: forall a. String -> Array a -> Vector n a
  atSlotWidth field xs = case Vector.toVector xs of
    Just v -> v
    Nothing -> unsafeThrow $
      "reshapePerProofWitness: " <> field <> " has " <> show (Array.length xs)
        <> " entries, expected "
        <> show (reflectType (Proxy :: Proxy n))

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

-- | Unpack one allocated `PerProofUnfinalized` into the
-- | `UnfinalizedProof` shape `verifyOne` consumes.
unpackUnfinalized
  :: forall r
   . PrimeField StepField
  => PerProofUnfinalized WrapIPARounds (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (FVar StepField) (BoolVar StepField)
  -> Snarky StepField (KimchiConstraint StepField) r UnfinalizedProof
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

-- | Lift a value-level dummy `PerProofUnfinalized` to an
-- | `UnfinalizedProof` of circuit constants. Emits no constraints;
-- | `stepMain` uses it for mpvMax-padding.
liftDummyPerProofUnfinalized
  :: PerProofUnfinalized
       WrapIPARounds
       (Type2 (SplitField (F StepField) Boolean))
       (F StepField)
       Boolean
  -> UnfinalizedProof
liftDummyPerProofUnfinalized (PerProofUnfinalized r) =
  let
    liftF (F x) = const_ x :: FVar StepField

    liftSizedF
      :: forall n
       . SizedF n (F StepField)
      -> SizedF n (FVar StepField)
    liftSizedF s =
      let
        F x = toField s
      in
        unsafePartial $ SizedF.unsafeFromField (const_ x)

    liftT2SF
      :: Type2 (SplitField (F StepField) Boolean)
      -> Type2 (SplitField (FVar StepField) (BoolVar StepField))
    liftT2SF (Type2 (SplitField { sDiv2: F sd, sOdd })) =
      Type2
        ( SplitField
            { sDiv2: const_ sd
            , sOdd: if sOdd then true_ else false_
            }
        )

    liftBool b = if b then true_ else false_
  in
    { deferredValues:
        { plonk:
            { alpha: liftSizedF (let UnChecked s = r.alpha in s)
            , beta: liftSizedF (let UnChecked s = r.beta in s)
            , gamma: liftSizedF (let UnChecked s = r.gamma in s)
            , zeta: liftSizedF (let UnChecked s = r.zeta in s)
            , perm: liftT2SF r.perm
            , zetaToSrsLength: liftT2SF r.zetaToSrsLength
            , zetaToDomainSize: liftT2SF r.zetaToDomainSize
            }
        , combinedInnerProduct: liftT2SF r.combinedInnerProduct
        , b: liftT2SF r.b
        , xi: liftSizedF (let UnChecked s = r.xi in s)
        , bulletproofChallenges:
            map (\(UnChecked s) -> liftSizedF s) r.bulletproofChallenges
        }
    , shouldFinalize: liftBool r.shouldFinalize
    , claimedDigest: liftF r.spongeDigest
    }

-------------------------------------------------------------------------------
-- | Build verify_one input from allocated witnesses
-------------------------------------------------------------------------------

-- | Assemble one slot's `verifyOne` input from its reshaped witness,
-- | its previous proof's public input and its VK commitments.
buildVerifyOneInput
  :: forall @n @stepChunks @tCommLen pad
   . Reflectable n Int
  => Reflectable pad Int
  => Add pad n PaddedLength
  => ReshapedPerProofWitness n stepChunks tCommLen
  -> Array (FVar StepField) -- prev proof's public input, pre-flattened
  -> BoolVar StepField
  -> UnfinalizedProof
  -> FVar StepField
  -> { sigma :: Vector 6 (ChunkedCommitment stepChunks (AffinePoint (FVar StepField)))
     , sigmaLast :: ChunkedCommitment stepChunks (AffinePoint (FVar StepField))
     , coeff :: Vector 15 (ChunkedCommitment stepChunks (AffinePoint (FVar StepField)))
     , index :: Vector 6 (ChunkedCommitment stepChunks (AffinePoint (FVar StepField)))
     }
  -> AffinePoint (FVar StepField) -- dummySg for padding
  -> VerifyOneInput n stepChunks tCommLen WrapIPARounds StepIPARounds (Type2 (SplitField (FVar StepField) (BoolVar StepField))) (FVar StepField) (BoolVar StepField)
buildVerifyOneInput pw appStateFields mustVerify unfinalized msgWrap vkComms dummySg =
  let
    -- `sgOld` is `prevSgs` widened to `PaddedLength`, with the `pad`
    -- dummies at the front.
    sgPadding :: Vector pad (AffinePoint (FVar StepField))
    sgPadding = Vector.replicate dummySg

    sgOld :: Vector PaddedLength (AffinePoint (FVar StepField))
    sgOld = Vector.append sgPadding (map unwrapPt pw.prevSgs)

    -- The mask arrives `PaddedLength`-wide as well, so dropping its
    -- front `pad` entries leaves the `n` real ones.
    fullMasks :: Vector PaddedLength (BoolVar StepField)
    fullMasks = pw.branchData.proofsVerifiedMask

    proofMask :: Vector n (BoolVar StepField)
    proofMask = Vector.drop @pad fullMasks
  in
    { appStateFields
    , wComm: map (over ChunkedCommitment (map unwrapPt)) pw.wComm
    , zComm: over ChunkedCommitment (map unwrapPt) pw.zComm
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
    , branchData: pw.branchData
        { proofsVerifiedMask = map (coerce :: BoolVar StepField -> FVar StepField) pw.branchData.proofsVerifiedMask }
    , proofMask
    , vkComms
    , sgOld
    }

-------------------------------------------------------------------------------
-- | Serialize unfinalized proof to output fields (to_data order)
-------------------------------------------------------------------------------

-- | One unfinalized proof serialized into the step circuit's public
-- | input, in the order its consumer reads them back: five `Type2`
-- | values (two fields each), the digest, `beta` and `gamma`, then
-- | `alpha`, `zeta` and `xi`, the `WrapIPARounds` bulletproof
-- | challenges, and `shouldFinalize` — 32 fields in all.
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
    shouldFinalizeField = (coerce unf.shouldFinalize) :< Vector.nil
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
-- | step_main
-------------------------------------------------------------------------------

stepMain
  :: forall @prevsSpec pad outputSize @inputVal input @outputVal output
       @valCarrier @mpvMax mpvPad @nd ndPred @cell
       len carrier carrierVar sideloadedVkCarrier vkSourcesCarrier blueprints
       unfsTotal digestPlusUnfs
       r
   . PrimeField StepField
  => BuildSlotVkSources cell prevsSpec WrapVkChunks len blueprints sideloadedVkCarrier vkSourcesCarrier
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Reflectable nd Int
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => SlotStatementsCarrier prevsSpec valCarrier
  -- The carrier's layout as a value. `CircuitType` cannot supply it:
  -- each slot's witness holds its previous-proof data in arrays, so
  -- the variable count is not derivable from the type. The widths
  -- come from the spec.
  => StepSlotsTyp prevsSpec carrier carrierVar
  => StepSlotsCarrier
       prevsSpec
       WrapVkChunks
       StepIPARounds
       WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       len
       carrierVar
       vkSourcesCarrier
  => CheckedType StepField (KimchiConstraint StepField) input
  => Reflectable len Int
  => Reflectable pad Int
  => Reflectable mpvMax Int
  => Reflectable mpvPad Int
  => Add pad len PaddedLength
  -- mpvMax-padding; at `mpvPad = 0` it emits nothing.
  => Add mpvPad len mpvMax
  => Mul mpvMax UnfinalizedFieldCount unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
  => ( AsProver StepField r (PrevValues prevsSpec)
       -> input
       -> Snarky StepField (KimchiConstraint StepField) r (RuleOutput prevsSpec output)
     )
  -> StepMainSrsData len nd blueprints
  -> AffinePoint StepField
  -> sideloadedVkCarrier
  -> StepAdvice prevsSpec StepIPARounds WrapIPARounds WrapVkChunks inputVal len carrier valCarrier sideloadedVkCarrier
  -> Ref (Maybe (Array (FVar StepField)))
  -> Snarky StepField (KimchiConstraint StepField) r (Vector outputSize (FVar StepField))
stepMain
  rule
  { blindingH
  , perSlotFopDomainLog2s
  , perSlotFopZkRows
  , perSlotVkBlueprints
  }
  dummySg
  sideloadedVkCarrier
  advice
  captureRef = do
  -- Projecting the public input out of the advice from inside the
  -- `exists` body defers the read to solve time: compile discards
  -- that body, so the dummy advice is never projected.
  publicInput <- exists (pure advice <#> \(StepAdvice r) -> r.publicInput)

  -- Label boundaries are externally fixed, so the side-loaded VK
  -- `exists` is emitted inside `rule_main` rather than beside it. A
  -- compiled-only rule has no `BlueprintSideLoaded` slot, so
  -- `buildSlotVkSources` emits no `exists` at all.
  { prevs, publicOutput, perSlotVkSources } <-
    label "rule_main" do
      perSlotVkSources <- buildSlotVkSources @cell @prevsSpec @WrapVkChunks perSlotVkBlueprints sideloadedVkCarrier
      -- The rule reads previous proofs' statements through this
      -- deferred getter, forced only inside the rule's own `exists`
      -- bodies.
      result <- rule
        (pure advice <#> \(StepAdvice r) -> mkPrevValues @prevsSpec r.prevAppStates)
        publicInput
      pure
        { prevs: prevsVector @len result.prevs
        , publicOutput: result.publicOutput
        , perSlotVkSources
        }

  let
    publicInputFields = varToFields @StepField @inputVal publicInput
    publicOutputFields = varToFields @StepField @outputVal publicOutput
    hashAppFields = publicInputFields <> publicOutputFields

  -- Capture the rule's `publicOutput` vars so the prover can evaluate
  -- them after the solve. The write sits inside an `exists` body, so
  -- it never fires at compile time; `stepSolveAndProve` reads the Ref
  -- once the solver completes. The `exists` is at `Unit`
  -- (`sizeInFields = 0`), so it adds no constraints.
  _ :: Unit <- exists $ liftEffect do
    Ref.write (Just publicOutputFields) captureRef

  -- This compile's own wrap VK, allocated once and reused by every
  -- `BlueprintSelf` slot; `BlueprintExternal` slots ignore it and
  -- inline their constant VK instead. The outer hash below absorbs
  -- these same commitments once, not per slot.
  (VerificationKey sharedVkRec :: VerificationKey WrapVkChunks (WeierstrassAffinePoint PallasG (FVar StepField))) <-
    label "exists_wrap_index"
      $ exists (pure advice <#> \(StepAdvice r) -> r.wrapVerifierIndex)
  let
    vk =
      { sigma: Vector.take @6 sharedVkRec.sigma
      , sigmaLast: Vector.last sharedVkRec.sigma
      , coeff: sharedVkRec.coeff
      , index: sharedVkRec.index
      }

  -- Each cell of the carrier is a `StepSlot` typed at its own width.
  slotsCarrier <- label "exists_prevs"
    $ existsTyp (stepSlotsTyp @prevsSpec)
        (pure advice <#> \(StepAdvice r) -> r.perProofSlotsCarrier)

  -- Uniform across slots, so one `Vector len` rather than a per-slot
  -- carrier.
  rawUnfinalizedProofs <- label "exists_unfinalized"
    $ exists (pure advice <#> \(StepAdvice r) -> r.publicUnfinalizedProofs)
  unfinalizedProofs <- traverse unpackUnfinalized rawUnfinalizedProofs

  -- `messages_for_next_wrap_proof` is allocated in two `exists` — the
  -- real entries and the padding — and concatenated. Each padding
  -- entry has to be a fresh Var rather than a `const_`, so that the
  -- output-to-public-input `assertEqual_` on a padded slot ties by
  -- permutation instead of emitting a Generic gate. Either way the
  -- var count is `len + mpvPad = mpvMax`.
  msgsWrapReal <- exists (pure advice <#> \(StepAdvice r) -> r.messagesForNextWrapProof)
  msgsWrapPadding <- exists
    (pure advice <#> \(StepAdvice r) -> Vector.replicate @mpvPad r.messagesForNextWrapProofDummyHash)
  let
    msgsWrap :: Vector mpvMax (FVar StepField)
    msgsWrap = mpvFrontPadVec msgsWrapPadding msgsWrapReal

  let
    -- Lift a value-side VK to `const_` vars, for a `ConstVk` slot:
    -- its coordinates become compile-time constants in the circuit.
    liftConstVk
      :: forall slotVkChunks
       . VerificationKey slotVkChunks (WeierstrassAffinePoint PallasG (F StepField))
      -> VerificationKey slotVkChunks (WeierstrassAffinePoint PallasG (FVar StepField))
    liftConstVk (VerificationKey r) = VerificationKey
      { sigma: map (over ChunkedCommitment (map liftWaPt)) r.sigma
      , coeff: map (over ChunkedCommitment (map liftWaPt)) r.coeff
      , index: map (over ChunkedCommitment (map liftWaPt)) r.index
      }
      where
      liftWaPt :: WeierstrassAffinePoint PallasG (F StepField) -> WeierstrassAffinePoint PallasG (FVar StepField)
      liftWaPt (WeierstrassAffinePoint pt) =
        let
          F x = pt.x
          F y = pt.y
        in
          WeierstrassAffinePoint
            { x: const_ x, y: const_ y }

    constDummySg :: AffinePoint (FVar StepField)
    constDummySg = AffinePoint { x: const_ (unwrap dummySg).x, y: const_ (unwrap dummySg).y }

  -- `verifyOne` per slot, then assert them all. The traversal keeps
  -- each slot's own width in scope, so its sizes, domains and VK
  -- commitments are computed at that slot's own parameters.
  results <- label "prevs_verified" do
    rs <- traverseStepSlotsAWithVk @prevsSpec @WrapVkChunks
      ( \slotWidth i sppw slotVkSrc -> do
          let
            pw = reshapePerProofWitness slotWidth sppw

            slotFopDomainLog2s = perSlotFopDomainLog2s !! i
            -- Shifts are constant across a slot's candidate domains,
            -- so any one of them gives the right value.
            slotShiftsLog2 = Vector.head slotFopDomainLog2s

            -- A compiled slot carries its lagrange table from compile
            -- time and its corrections are constants. A side-loaded
            -- slot muxes three per-domain tables on the in-circuit
            -- `actualWrapDomainSize` one-hot bits, which yields
            -- in-circuit corrections, so it must run in
            -- `InCircuitCorrections` mode — `PureCorrections` rejects
            -- `AddWithCircuitCorrection`.
            --
            -- `slotVkSrc` and `sppw` share the slot's chunk count,
            -- because `traverseStepSlotsAWithVk` walks them in
            -- lockstep. The wrap proof's chunk count equalling its
            -- VK's is therefore a type-level fact here.
            slotConfig = case slotVkSrc of
              ConstVk lagrange constVk ->
                { lagrangeAt: lagrange
                , correctionMode: PureCorrections
                , fopDomainMode: KnownDomainsMode
                , vkRec: let VerificationKey r = liftConstVk constVk in r
                }
              SharedExistsVk lagrange ->
                { lagrangeAt: lagrange
                , correctionMode: PureCorrections
                , fopDomainMode: KnownDomainsMode
                -- A self slot verifies a proof of this system, so it
                -- checks against this compile's own wrap VK.
                -- `sharedVkRec` is the single allocation made above;
                -- allocating one per slot would emit extra `exists`
                -- calls and change the circuit.
                , vkRec: sharedVkRec
                }
              SideloadedExistsVk perDomainLagrangeAts (SLVK.VerificationKey sl) ->
                { lagrangeAt: mkSideloadedLagrangeLookup
                    (curveParams (Proxy @PallasG))
                    sl.actualWrapDomainSize
                    perDomainLagrangeAts
                , correctionMode: InCircuitCorrections
                , fopDomainMode: SideLoadedMode
                , vkRec: let VerificationKey r = sl.wrapIndex in r
                }

            slotIvpParams =
              { curveParams: curveParams (Proxy @PallasG)
              , lagrangeAt: slotConfig.lagrangeAt
              , blindingH
              , correctionMode: slotConfig.correctionMode
              , endo: stepEndoVal
              , groupMapParams: groupMapParams (Proxy @PallasG)
              , useOptSponge: false
              }

            slotFopParams =
              -- One `{generator, log2}` per candidate source branch.
              { domains: map
                  ( \log2 ->
                      { generator: const_ (LinFFI.domainGenerator @StepField log2)
                      , log2
                      }
                  )
                  slotFopDomainLog2s
              , shifts: map const_ (LinFFI.domainShifts @StepField slotShiftsLog2)
              , srsLengthLog2: reflectType (Proxy :: Proxy StepIPARounds)
              , zkRows: perSlotFopZkRows !! i
              , endo: stepEndoVal
              , linearizationPoly: Linearization.pallas
              , domainMode: slotConfig.fopDomainMode
              }

            slotVkRec = slotConfig.vkRec

            slotVk =
              { sigma: Vector.take @6 slotVkRec.sigma
              , sigmaLast: Vector.last slotVkRec.sigma
              , coeff: slotVkRec.coeff
              , index: slotVkRec.index
              }

            slotVkComms =
              { sigma: map (over ChunkedCommitment (map unwrapPt)) slotVk.sigma
              , sigmaLast: over ChunkedCommitment (map unwrapPt) slotVk.sigmaLast
              , coeff: map (over ChunkedCommitment (map unwrapPt)) slotVk.coeff
              , index: map (over ChunkedCommitment (map unwrapPt)) slotVk.index
              }

            prev = prevs !! i
            input = buildVerifyOneInput pw
              prev.fields
              prev.proofMustVerify
              (unfinalizedProofs !! i)
              (msgsWrapReal !! i)
              slotVkComms
              constDummySg
          r <- label ("slot_" <> show (getFinite i)) $
            verifyOne slotFopParams input slotIvpParams
          -- `pw.sg` is carried out so the outer hash can absorb it.
          pure { sg: pw.sg, expandedChallenges: r.expandedChallenges, result: r.result }
      )
      slotsCarrier
      perSlotVkSources
    assertAll_ (Vector.toUnfoldable $ map _.result rs)
    pure rs

  -- Trace labels for a VK commitment are fixed by its chunk count: a
  -- single-chunk array traces as `label.x` / `label.y`, a multi-chunk
  -- one as `label.{i}.x` / `label.{i}.y` per chunk.
  outerDigest <- label "hash_messages_for_next_step_proof" do
    let
      absorbPt s pt = do
        let AffinePoint { x, y } = unwrapPt pt
        s1 <- Sponge.absorb x s
        Sponge.absorb y s1
      absorbChunks s = foldM absorbPt s <<< unwrap
      traceChunks lbl cc =
        case Vector.toUnfoldable (unwrap cc) of
          [ pt ] -> do
            let AffinePoint { x, y } = unwrapPt pt
            ivpTrace (lbl <> ".x") x
            ivpTrace (lbl <> ".y") y
          cs -> forWithIndex_ cs \j pt -> do
            let AffinePoint { x, y } = unwrapPt pt
            ivpTrace (lbl <> "." <> show j <> ".x") x
            ivpTrace (lbl <> "." <> show j <> ".y") y

    -- The seven sigmas trace under one contiguous `sigma.0..6` index,
    -- even though the code splits them into `sigma` and `sigmaLast`
    -- for the sponge path.
    forWithIndex_ vk.sigma \fi chunks ->
      traceChunks ("step_main_outer.vk.sigma." <> show (getFinite fi)) chunks
    traceChunks "step_main_outer.vk.sigma.6" vk.sigmaLast
    forWithIndex_ vk.coeff \fi chunks ->
      traceChunks ("step_main_outer.vk.coeff." <> show (getFinite fi)) chunks
    -- The six index commitments trace under fixed names.
    let idxNames = "generic" :< "psm" :< "complete_add" :< "mul" :< "emul" :< "endomul_scalar" :< Vector.nil
    forWithIndex_ vk.index \fi chunks ->
      traceChunks ("step_main_outer.vk.idx." <> Vector.index idxNames fi) chunks
    forWithIndex_ hashAppFields \i f ->
      ivpTrace ("step_main_outer.app_state." <> show i) f

    spongeAfterIndex <- do
      let sponge0 = initialSpongeCircuit :: Sponge.Sponge (FVar StepField)
      s1 <- foldM absorbChunks sponge0 vk.sigma
      s2 <- absorbChunks s1 vk.sigmaLast
      s3 <- foldM absorbChunks s2 vk.coeff
      foldM absorbChunks s3 vk.index

    s1 <- foldM (flip Sponge.absorb) spongeAfterIndex hashAppFields

    -- What the outer hash absorbs stays at length `len`, the rule's
    -- own previous-proof count: the bulletproof challenges here are
    -- unpadded. Only the output `unfinalized_proofs` is widened to
    -- `mpvMax`.
    let proofData = map (\r -> { sg: r.sg, expandedChals: r.expandedChallenges }) results
    forWithIndex_ proofData \fi { sg: sgPt, expandedChals } -> do
      let i = getFinite fi
      let AffinePoint pt = unwrapPt sgPt
      ivpTrace ("step_main_outer.proof." <> show i <> ".sg.x") pt.x
      ivpTrace ("step_main_outer.proof." <> show i <> ".sg.y") pt.y
      forWithIndex_ expandedChals \fj c ->
        ivpTrace ("step_main_outer.proof." <> show i <> ".bp_chal." <> show (getFinite fj)) c
    sAfterProofs <- foldM
      ( \s { sg: sgPt, expandedChals } -> do
          let AffinePoint pt = unwrapPt sgPt
          s2 <- Sponge.absorb pt.x s
          s3 <- Sponge.absorb pt.y s2
          foldM (\s' c -> Sponge.absorb c s') s3 expandedChals
      )
      s1
      proofData

    { result: digest } <- Sponge.squeeze sAfterProofs
    ivpTrace "step_main_outer.digest" digest
    pure digest

  -- The output is `mpvMax × UnfinalizedFieldCount` unfinalized fields,
  -- then the step message digest, then `mpvMax` wrap messages.
  -- `unfinalizedProofs` is front-padded here with constant dummies;
  -- `msgsWrap` was already widened at its `exists`.
  --
  -- The padding dummy is built at `maxProofsVerified = len`, the
  -- rule's own previous-proof count, not `mpvMax`.
  let
    dummyUnfp _ =
      liftDummyPerProofUnfinalized
        ( Dummy.mkDummyPerProofUnfinalized
            ( Dummy.baseCaseDummies
                { maxProofsVerified: reflectType (Proxy @len) }
            )
        )

    unfinalizedProofsPadded :: Vector mpvMax UnfinalizedProof
    unfinalizedProofsPadded = mpvFrontPad dummyUnfp unfinalizedProofs

    unfsFlat :: Vector unfsTotal (FVar StepField)
    unfsFlat = Vector.concat (map unfFields unfinalizedProofsPadded)

    digestVec :: Vector 1 (FVar StepField)
    digestVec = outerDigest :< Vector.nil

    outputV :: Vector outputSize (FVar StepField)
    outputV = unfsFlat `Vector.append` digestVec `Vector.append` msgsWrap

  pure outputV

