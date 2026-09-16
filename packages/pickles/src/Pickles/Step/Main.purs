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
  ( module Pickles.Step.VkSource
  , class BuildSlotVkSources
  , buildSlotVkSources
  -- * Rule abstraction
  , RuleOutput
  -- * Spec-indexed per-slot carrier step_main
  , StepMainSrsData
  , UnfinalizedProof
  , liftDummyPerProofUnfinalized
  , stepMain
  -- * mpvMax-padding
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
import Pickles.Step.Slots (class StepSlotsCarrier, class StepSlotsTyp, stepSlotsTyp, traverseStepSlotsAWithVk)
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

-- | Rules route their own witness allocations through application-specific
-- | advice typeclasses (one per rule), not via a generic throwing helper.
-- | Each rule defines a class with methods for the values it needs, plus
-- | an `Effect` instance that throws for compilation. The prover side
-- | provides a real interpreter via a different monad.
-- |
-- | Reference: `SimpleChainAdvice` in StepMainSimpleChain.purs for the
-- | N1 rule, `SimpleChainN2Advice` for N2.
-- | The `prevInput` type parameter is the PREVIOUS proofs' public_input
-- | slot type (what flows into `previous_proof_statements[i].public_input`
-- | in OCaml `Inductive_rule.t`). For self-recursive Input-mode rules
-- | this coincides with self's own `input` type; for Output-mode or
-- | heterogeneous recursion it's the prev rules' `public_output` type
-- | (e.g. `FVar StepField` for StepField-valued outputs). Kept separate from
-- | the self-input parameter because OCaml treats each prev's
-- | public_input independently via `Types_map.public_input tag` (see
-- | step_main.ml:318-332).
-- | The `output` type parameter is the rule's `public_output` (OCaml
-- | `Inductive_rule.t.public_output`). For the common Input-mode case
-- | (`~public_input:(Input _)`) the rule has no output and callers use
-- | `output = Unit`. For Output-mode rules the computed output flows
-- | through `publicOutput` back to the caller.
type RuleOutput n prevInput output =
  { prevPublicInputs :: Vector n prevInput
  , proofMustVerify :: Vector n (BoolVar StepField)
  , publicOutput :: output
  }

-- | Per-slot wrap VK source — three-way dispatch.
-- |
-- | * `ConstVk constVk` — compiled External tag whose wrap VK is
-- |   known at step-compile time. The VK is baked as compile-time
-- |   constants; downstream `mul_ const var` short-circuits to
-- |   `Scale` (no allocation, no on-curve checks).
-- |
-- | * `SharedExistsVk` — Self tag. Self's wrap VK doesn't exist at
-- |   step-compile time (cycle with wrap compile), so it's allocated
-- |   ONCE at the top of `stepMain` via `Req.Wrap_index` and every
-- |   Self slot reuses that single allocation.
-- |
-- | * `SideloadedExistsVk perDomainLagrangeAts` — side-loaded tag.
-- |   The wrap VK is supplied at runtime via
-- |   `Pickles.Sideload.Advice.SideloadedVKsCarrier` and allocated
-- |   PER SLOT against `verificationKeyTyp`. The carried `Vector 3
-- |   (Int -> AffinePoint (F StepField))` is the three per-domain
-- |   lagrange-base lookup tables (one per `wrap_domain ∈ {N0, N1,
-- |   N2}`); the IVP's `lagrangeAt` for this slot muxes among them
-- |   via the in-circuit `actualWrapDomainSize` one-hot bits (see
-- |   `Pickles.PublicInputCommit.mkSideloadedLagrangeLookup`).
-- |
-- | Build a heterogeneous per-slot wrap-VK carrier by walking the
-- | spec-indexed blueprint carrier alongside the (also spec-indexed)
-- | side-loaded VK cell carrier. The output is a Tuple-chain mirroring
-- | `Pickles.Step.Slots`'s `vkCarrier` — each slot's `SlotVkSource nc`
-- | is sized by *that slot's* `nc` from `Slot n nc statement`.
-- |
-- | The dispatch is on the slot's runtime `SlotVkBlueprint`, which is
-- | where the kind of the slot actually lives: `BlueprintSelf` and
-- | `BlueprintExternal` pass straight through to `SharedExistsVk` /
-- | `ConstVk`, and `BlueprintSideLoaded` allocates the runtime VK
-- | in-circuit via `exists` and bundles it with the compile-time
-- | per-domain lagrange tables into `SideloadedExistsVk`. The cell
-- | carrier supplies that runtime descriptor; at the other two cases
-- | its cell is never read.
-- |
-- | Reference: OCaml `step_main.ml`'s tag-kind dispatch, which is a
-- | runtime match on `Types_map.t` for the same reason.
-- |
-- | `wrapVkChunks` is the outer compile's wrap-VK chunks count. The
-- | instance head STRUCTURALLY UNIFIES the slot's nc with
-- | `wrapVkChunks` (by reusing the same type variable name in the
-- | slot's `nc` position). If a caller's spec writes `Slot n 2 stmt`
-- | while `wrapVkChunks = 1` is in scope, the instance does not resolve
-- | and the user gets a compile-time type error — not a silent runtime
-- | coerce.
-- |
-- | `Pickles.Step.Slots.StepSlotsCarrier` takes `nc` as a class
-- | parameter for the same reason, so the traversal callback hands the
-- | dispatch a `PerProofWitness wrapVkChunks …` and a
-- | `SlotVkSource wrapVkChunks` directly. That is what lets the body
-- | below call `verifyOne` with no `unsafeCoerce` anywhere on the
-- | per-slot path: every width in sight is the same one, by
-- | construction rather than by argument.
-- |
-- | This is a wrap-side count, and a wrap domain never exceeds the wrap
-- | SRS, so it is 1 for every slot of every compile. The count that
-- | genuinely varies is Dim 1, `stepChunks`, which belongs to the wrap
-- | circuit verifying a step proof — see `Pickles.Wrap.Main`.
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

-- | SRS data for `stepMain`. Carries per-slot FOP domain-log2s
-- | (`finalize_other_proof` consumes the prev's `step_domains` Vector;
-- | self-recursive rules share one value across slots, heterogeneous
-- | prevs differ per slot) and per-slot wrap-VK sources (see
-- | `SlotVkSource`).
type StepMainSrsData :: Int -> Int -> Type -> Type
type StepMainSrsData len nd blueprints =
  { -- | Shared Tock SRS h-generator. `Generators.h =
    -- | Kimchi_bindings.Protocol.SRS.Fq.urs_h (Tock URS)`
    -- | (step_main_inputs.ml:182-187); a single SRS-level constant,
    -- | NOT per-slot.
    --
    -- | The per-slot lagrange bases used to live here as a
    -- | `Vector len (LagrangeBaseLookup wrapVkChunks _)`, one width for
    -- | every slot. They are per-slot data at the slot's own chunk
    -- | count, so they travel in `perSlotVkBlueprints` instead. In OCaml
    -- | `x_hat = Σᵢ x[i] * lagrange_commitment(~domain:d.wrap_domain, srs, i)`
    -- | (step_verifier.ml:564-571) reads the PREV's `wrap_domain` from
    -- | the per-slot `Types_map.For_step.t`, which is the same story:
    -- | shared SRS (one Tock URS, step_main.ml:394), per-slot domain.
    blindingH :: AffinePoint (F StepField)
  -- | Per-slot Vector of all step-domain log2s the slot's prev
  -- | source could have. For single-rule callers (and any slot whose
  -- | source has a single branch) this is `Vector 1 [theLog2]`;
  -- | for multi-rule Self prevs whose source is a `branches`-branch
  -- | proof system this is `Vector branches [log2_0, ..., log2_{branches-1}]`.
  -- | Mirrors OCaml `domain_for_compiled`'s `domains` Vector
  -- | (`step_verifier.ml:879-899`), which is then deduped into
  -- | `unique_domains` for `Pseudo.Domain.to_domain` dispatch.
  , perSlotFopDomainLog2s :: Vector len (Vector nd Int)
  -- | Per-slot kimchi `zk_rows` of the slot's prev step proof, the value
  -- | its deferred permutation scalar was produced at
  -- | (`zkRowsForNumChunks` of that rule's `@stepChunks`; 3 at one
  -- | chunk). Mirrors OCaml `step_main.ml`'s `d.zk_rows` from the prev
  -- | tag's `step_branch_data`.
  , perSlotFopZkRows :: Vector len Int
  -- | Spec-indexed compile-time blueprint for each slot's wrap-VK
  -- | source — one `SlotVkBlueprint nc` per slot, at that slot's own
  -- | chunk count. The runtime VK for side-loaded slots is bundled in
  -- | by `buildSlotVkSources` at circuit-build time. The `blueprints`
  -- | shape mirrors `prevsSpec` slot-for-slot, which is what fixes each
  -- | cell's `nc`; which of the three sources a slot has is runtime
  -- | data inside the cell.
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
--
-- `Add mpvPad len mpvMax` relates the two widths, for step PI
-- mpvMax-padding (mirroring OCaml `step.ml:782-787`'s
-- `Vector.extend_front unfinalized_proofs ... Unfinalized.dummy`).
--
-- This used to be three classes — `IntEq`, `MpvPaddingDispatch` and
-- `MpvPadding` — dispatching on whether `len` equalled `mpvMax` so
-- that the `mpvPad = 0` case could avoid asking `Prim.Int.Add` to
-- solve `Add 0 len len` for an abstract `len`. `Add` discharges that
-- case at every site in this tree, so the dispatch was buying nothing.
--------------------------------------------------------------------------------

-- | Concatenate a padding vector with a real vector to produce the
-- | full mpvMax-sized vector.
mpvFrontPadVec
  :: forall a mpvPad len mpvMax
   . Add mpvPad len mpvMax
  => Vector mpvPad a
  -> Vector len a
  -> Vector mpvMax a
mpvFrontPadVec = Vector.append

-- | Front-pad a `Vector len a` with `mpvPad` copies of a dummy value
-- | to produce a `Vector mpvMax a`. The `Add mpvPad len mpvMax`
-- | constraint witnesses `mpvPad + len = mpvMax` at the type level.
-- |
-- | The dummy is a thunk so the single-rule path (`mpvPad = 0`) does
-- | NOT force evaluation of the dummy — important because building
-- | the dummy can trigger Rust FFI (lagrange / blinding-generator
-- | computations) that advance shared chacha8 RNG state.
-- |
-- | Implementation: when `mpvPad = 0`, `Add 0 len mpvMax` gives
-- | `mpvMax = len` so we `unsafeCoerce real` directly (zero work,
-- | byte-identical witness). When `mpvPad > 0`, we build a
-- | runtime-sized array and re-wrap via `Vector.toVector +
-- | unsafePartial fromJust` (the runtime check is a tautology — array
-- | length always equals `mpvPad + len = mpvMax`).
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
-- |
-- | The allocation itself is `Pickles.Step.Types.perProofWitnessTyp`,
-- | which lays the witness out in OCaml's exact hlist order: variables
-- | are allocated sequentially, so that order fixes the variable index
-- | assignment. What follows here only rearranges what it produced.
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

-- | Reshape one allocated per-proof witness into the flatter record the
-- | rest of `stepMain` reads: `tComm` concatenated, the nested
-- | newtype wrappers unwrapped, and the two per-previous-proof arrays
-- | recovered at the slot's width.
-- |
-- | Nothing is allocated here — this emits no constraints and reads no
-- | advice. The `exists` happened upstream, against
-- | `Pickles.Step.Types.perProofWitnessTyp`.
reshapePerProofWitness
  :: forall @n @stepChunks tCommLen
   . Reflectable n Int
  => Reflectable stepChunks Int
  => Mul 7 stepChunks tCommLen
  -- | The slot's width. Still type-level, because everything below this
  -- | function is indexed by it; the witness above no longer is.
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
    -- wComm/zComm carry chunks through; tComm flattens Vector 7 (ChunkedCommitment nc pt)
    -- to flat Vector tCommLen pt via Vector.concat (= 7 * stepChunks pieces).
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
  -- The witness carries its per-previous-proof data as arrays, since
  -- the slot's width is not in its type. Everything downstream of here
  -- is still indexed by that width, so it is recovered once, at this
  -- boundary. The array was allocated by `perProofWitnessTyp` at the
  -- width the spec declares, which is the same `n`, so a mismatch is a
  -- bug in this module rather than anything a prover can provoke.
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

-- | Unpack one PerProofUnfinalized (allocated via the advice monad upstream)
-- | into the legacy `UnfinalizedProof` record shape consumed by `verifyOne`.
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

-- | Lift a value-level dummy `PerProofUnfinalized` (cross-field-encoded
-- | in step field) directly to an `UnfinalizedProof` (circuit-var,
-- | unpacked) via `const_` / boolean-constant lifting. Pure: emits no
-- | constraints. Used by `stepMain` for mpvMax-padding.
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

-- | At the per-slot level there's ONE chunks dimension: the slot's
-- | wrap proof / wrap VK chunks count (must agree by protocol).
-- | OCaml `step_main.ml:347`'s `num_chunks_by_default = 1` pins this
-- | to 1 today; we keep it polymorphic and let call sites specify.
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
    -- sgOld: pad prevSgs to PaddedLength (Wrap_hack.Padded_length).
    -- extend_front puts `pad` dummies at the front, where pad + n = PaddedLength.
    sgPadding :: Vector pad (AffinePoint (FVar StepField))
    sgPadding = Vector.replicate dummySg

    sgOld :: Vector PaddedLength (AffinePoint (FVar StepField))
    sgOld = Vector.append sgPadding (map unwrapPt pw.prevSgs)

    -- proofMask: drop the front `pad` elements of [mask0, mask1] to keep the last `n`.
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
-- | V2 step_main — spec-indexed per-slot carrier variant
-- |
-- | Drops `getStepPerProofWitnesses` / `Vector.generateA @n` in favor of
-- | `getStepSlotsCarrier` + a single `traverseStepSlotsA` that walks the
-- | carrier per slot, extracting SPPW from `StepSlot`, reshaping it, and
-- | running verify_one — all with the per-slot `n_i` in scope.
-- |
-- | Everything else (public input allocation, wrap VK, unfinalized
-- | proofs, messages_for_next_wrap_proof, outer hash, output
-- | assembly) is identical to `stepMain` — the only structural
-- | difference is the per-slot heterogeneity source.
-------------------------------------------------------------------------------

stepMain
  :: forall @prevsSpec pad outputSize @inputVal input @outputVal output @prevInputVal prevInput
       @valCarrier @mpvMax mpvPad @nd ndPred @cell
       len carrier carrierVar sideloadedVkCarrier vkSourcesCarrier blueprints
       unfsTotal digestPlusUnfs
       r
   . PrimeField StepField
  -- Spec-indexed walk that, at each `BlueprintSideLoaded` slot,
  -- allocates a `SLVK.VerificationKey (FVar _) (BoolVar _)` via
  -- `exists` and bundles it (alongside the compile-time per-domain
  -- lagrange tables) into the per-slot `SlotVkSource nc`, and walks
  -- `BlueprintSelf` / `BlueprintExternal` straight through. The
  -- output is a heterogeneous Tuple-chain `vkSourcesCarrier` with
  -- each cell sized by *that slot's* `nc`.
  --
  -- The wrap VK is one chunk (`Pickles.Types.WrapVkChunks`), so this
  -- signature names the constant rather than quantifying over it. It
  -- used to carry fourteen constraints deriving the chunked-base layout
  -- from an abstract count; at 1 they are `tCommLen = 7`,
  -- `nonSgBases = 45`, `totalBases = 47`, and the solver discharges
  -- them at `verifyOne` without being told.
  => BuildSlotVkSources cell prevsSpec WrapVkChunks len blueprints sideloadedVkCarrier vkSourcesCarrier
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Reflectable nd Int
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  -- The carrier's layout as a value. It cannot come from `CircuitType`
  -- any more: each slot's witness holds its previous-proof data in
  -- arrays, so nothing can count the variables from the type alone.
  -- The widths come from the spec, which still declares them.
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
  -- mpvMax-padding. When `mpvMax = len` then `mpvPad = 0` and padding
  -- emits nothing (circuit shape unchanged). When `mpvPad > 0`,
  -- `mpvFrontPad` prepends that many dummy entries.
  => Add mpvPad len mpvMax
  => Mul mpvMax UnfinalizedFieldCount unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
  => ( AsProver StepField r valCarrier
       -> input
       -> Snarky StepField (KimchiConstraint StepField) r (RuleOutput len prevInput output)
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
  -- 1. exists: public input via Req.App_state. Projected from the
  -- advice value through the functor so the read defers to solve time
  -- (compile discards the `exists` body, so the dummy advice is never
  -- projected).
  publicInput <- exists (pure advice <#> \(StepAdvice r) -> r.publicInput)

  -- 2. rule_main — wraps both the user's rule body AND the side-loaded VK
  -- exists. Mirrors OCaml's `with_label "rule_main" (fun () -> rule.main ...)`
  -- where the rule body itself contains `exists Side_loaded_verification_key.typ`
  -- (dump_circuit_impl.ml:4388 inside the lambda passed to `with_label`).
  -- For compiled-only rules no slot's blueprint is
  -- `BlueprintSideLoaded` and `buildSlotVkSources` emits no `exists`
  -- calls.
  { prevPublicInputs, proofMustVerify, publicOutput, perSlotVkSources } <-
    label "rule_main" do
      perSlotVkSources <- buildSlotVkSources @cell @prevsSpec @WrapVkChunks perSlotVkBlueprints sideloadedVkCarrier
      -- The rule reads previous proofs' statements through this deferred
      -- getter (projected from advice; forced only inside the rule's own
      -- `exists` bodies, so compile never touches the dummy advice).
      result <- rule (pure advice <#> \(StepAdvice r) -> r.prevAppStates) publicInput
      pure
        { prevPublicInputs: result.prevPublicInputs
        , proofMustVerify: result.proofMustVerify
        , publicOutput: result.publicOutput
        , perSlotVkSources
        }

  let
    publicInputFields = varToFields @StepField @inputVal publicInput
    publicOutputFields = varToFields @StepField @outputVal publicOutput
    hashAppFields = publicInputFields <> publicOutputFields

  -- Capture the rule's user `publicOutput` FVars so the prover can
  -- evaluate them post-solve. Written to `captureRef` from inside an
  -- `exists` body (OCaml's `Req.Return_value`,
  -- mina/src/lib/crypto/pickles/step.ml:896-898). At compile time
  -- `exists` skips the witness body so the write never fires; at solve
  -- time `stepSolveAndProve` reads the Ref after the solver completes.
  -- The `exists` allocates a fresh `Unit` var (`sizeInFields = 0`, no
  -- actual circuit slot allocated), so this introduces no constraints.
  _ :: Unit <- exists $ liftEffect do
    Ref.write (Just publicOutputFields) captureRef

  -- 3. exists: SHARED VK via Req.Wrap_index.
  --    Mirrors OCaml's `dlog_plonk_index` (step_main.ml:498) — one
  --    exists-allocation at the top, reused by every `BlueprintSelf`
  --    slot (i.e. slots whose prev is SELF). `BlueprintExternal` slots
  --    ignore this allocation and inline their constant VK instead.
  --
  -- Also used directly by the outer hash (step 9) — the
  -- hash_messages_for_next_step_proof sponge absorbs self's wrap VK
  -- commitments (= `dlog_plonk_index`) once, NOT per-slot.
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

  -- 4. exists: per-slot carrier via Req.Proof_with_datas — the v2
  --    spec-indexed variant. Each slot of the carrier holds a
  --    `StepSlot n_i ds dw …` typed with its own per-slot n_i.
  slotsCarrier <- label "exists_prevs"
    $ existsTyp (stepSlotsTyp @prevsSpec)
        (pure advice <#> \(StepAdvice r) -> r.perProofSlotsCarrier)

  -- 5. exists: unfinalized proofs (uniform Vector len).
  rawUnfinalizedProofs <- label "exists_unfinalized"
    $ exists (pure advice <#> \(StepAdvice r) -> r.publicUnfinalizedProofs)
  unfinalizedProofs <- traverse unpackUnfinalized rawUnfinalizedProofs

  -- 6. exists: messages_for_next_wrap_proof.
  --    Mirrors OCaml step_main.ml:368-370 which allocates
  --    `Vector.typ Digest.typ Max_proofs_verified.n` via `exists` —
  --    the prover supplies real values for the rule's actual prev
  --    count and dummy values for padding positions.
  --
  --    PS does this in two `exists` (real + padding) and concatenates
  --    via `mpvFrontPadVec`. Each padding entry is a fresh Var (not a
  --    `const_` Constant), so the output→PI assertEqual_ on padded
  --    slots permutation-ties (no extra Generic gate). Total Var
  --    count is `len + mpvPad = mpvMax`, matching OCaml's single
  --    mpvMax allocation.
  msgsWrapReal <- exists (pure advice <#> \(StepAdvice r) -> r.messagesForNextWrapProof)
  msgsWrapPadding <- exists
    (pure advice <#> \(StepAdvice r) -> Vector.replicate @mpvPad r.messagesForNextWrapProofDummyHash)
  let
    msgsWrap :: Vector mpvMax (FVar StepField)
    msgsWrap = mpvFrontPadVec msgsWrapPadding msgsWrapReal

  let
    -- Lift a value-side VK to const_ FVars. Used when a slot has
    -- `Just vk` — the VK coords appear as compile-time constants in
    -- the circuit (matches OCaml's `Array.map ~f:Inner_curve.constant`
    -- in `of_compiled_with_known_wrap_key`, types_map.ml:214-215).
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

  -- 8. verify_one × len + Assert.all (inside prevs_verified label).
  -- Drive structurally via traverseStepSlotsA — each callback invocation
  -- has its slot's `n_i` in scope so per-slot sizes (prevSgs, etc.)
  -- are correct, and each slot's `fopParams` / `vkComms` are computed
  -- from the slot's own `fopDomainLog2` and `knownWrapKey`
  -- (mirroring OCaml's `finalize_other_proof ~step_domains:d.step_domains`
  -- and the `of_compiled_with_known_wrap_key` / `self_data` dispatch
  -- at step_main.ml:513-528).
  results <- label "prevs_verified" do
    rs <- traverseStepSlotsAWithVk @prevsSpec @WrapVkChunks
      ( \slotWidth i sppw slotVkSrc -> do
          let
            pw = reshapePerProofWitness slotWidth sppw

            -- Per-slot Vector nd of all possible source-branch step domains.
            -- For nd=1 this is `Vector 1 [theLog2]` (single-rule, External
            -- with single-branch source, or Self with single-branch source).
            -- For nd>1 this is the full deduped list for multi-rule Self
            -- prevs (e.g. TwoPhaseChain Self → [9, 14]).
            slotFopDomainLog2s = perSlotFopDomainLog2s !! i
            -- Single-Int representative used for shifts only — OCaml's
            -- `Pseudo.Domain.shifts` asserts shifts are constant across
            -- all unique_domains, so any element gives the right
            -- (constant) value.
            slotShiftsLog2 = Vector.head slotFopDomainLog2s

            -- Per-slot config: lagrange lookup, correction mode, and
            -- VK record. Compiled slots (ConstVk / SharedExistsVk)
            -- use the compile-time `perSlotLagrangeAt` table with
            -- pure (constant) corrections. Side-loaded slots mux
            -- among three per-domain lagrange tables via the in-circuit
            -- `actualWrapDomainSize` one-hot bits — that path produces
            -- in-circuit FVar corrections, so it must use
            -- `InCircuitCorrections` mode (PureCorrections rejects
            -- `AddWithCircuitCorrection`).
            --
            -- `slotVkSrc :: SlotVkSource nc` shares the slot's `nc`
            -- with `sppw :: PerProofWitness n nc …` via the parallel
            -- `traverseStepSlotsAWithVk` lockstep walk — the type
            -- system enforces the protocol invariant that the wrap
            -- proof's chunks count equals its VK's chunks count.
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
                -- A Self slot verifies a proof of THIS system, so the
                -- key it checks against is this compile's own wrap VK.
                -- `sharedVkRec` is the one allocation made at the top
                -- of `stepMain` (step 3) and reused by every Self slot;
                -- allocating per slot would emit extra `exists` calls
                -- and change the circuit.
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
              -- Multi-domain shape: one `{generator, log2}` per
              -- possible source branch. For nd=1 this collapses to a
              -- Vector 1 (byte-identical gate emission as
              -- single-domain). For nd>1 the FOP body emits one
              -- extra `StepField.equal` and one extra mask `StepField.mul`
              -- per additional branch.
              { domains: map
                  ( \log2 ->
                      { generator: const_ (LinFFI.domainGenerator @StepField log2)
                      , log2
                      }
                  )
                  slotFopDomainLog2s
              -- shifts are constant across all unique_domains
              -- (`disabled_not_the_same`); any branch's log2 gives the
              -- same answer.
              , shifts: map const_ (LinFFI.domainShifts @StepField slotShiftsLog2)
              , srsLengthLog2: reflectType (Proxy :: Proxy StepIPARounds)
              -- OCaml `step_main.ml`: the prev tag's `zk_rows` (its
              -- `step_branch_data`, derived from that rule's num_chunks).
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

            -- Map over both outer Vector 7/15/6 and the inner chunks
            -- ChunkedCommitment slotNc, since each VK commitment is chunked.
            slotVkComms =
              { sigma: map (over ChunkedCommitment (map unwrapPt)) slotVk.sigma
              , sigmaLast: over ChunkedCommitment (map unwrapPt) slotVk.sigmaLast
              , coeff: map (over ChunkedCommitment (map unwrapPt)) slotVk.coeff
              , index: map (over ChunkedCommitment (map unwrapPt)) slotVk.index
              }

            prevInputVar = prevPublicInputs !! i
            input = buildVerifyOneInput pw
              (varToFields @StepField @prevInputVal prevInputVar)
              (proofMustVerify !! i)
              (unfinalizedProofs !! i)
              (msgsWrapReal !! i)
              slotVkComms
              constDummySg
          r <- label ("slot_" <> show (getFinite i)) $
            verifyOne slotFopParams input slotIvpParams
          -- Carry pw.sg out alongside the verify_one result so the
          -- outer hash can absorb it.
          pure { sg: pw.sg, expandedChallenges: r.expandedChallenges, result: r.result }
      )
      slotsCarrier
      perSlotVkSources
    assertAll_ (Vector.toUnfoldable $ map _.result rs)
    pure rs

  -- 9. Outer hash: hash_messages_for_next_step_proof. Mirrors
  -- OCaml `common.ml:45-52` / `common.ml:103-112`'s
  -- `trace_point_arr` shape: each VK commitment is a chunk array;
  -- single-chunk arrays trace as `label.x` / `label.y`, multi-chunk
  -- ones trace as `label.{i}.x` / `label.{i}.y` per chunk.
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

    -- Emit all 7 sigmas under a contiguous `sigma.0..6` index to match
    -- OCaml's `Vector.iter dlog_plonk_index.sigma_comm`. Internally PS
    -- splits into `sigma` (Vector 6) + `sigmaLast` for the sponge path,
    -- but the trace labels stay contiguous.
    forWithIndex_ vk.sigma \fi chunks ->
      traceChunks ("step_main_outer.vk.sigma." <> show (getFinite fi)) chunks
    traceChunks "step_main_outer.vk.sigma.6" vk.sigmaLast
    forWithIndex_ vk.coeff \fi chunks ->
      traceChunks ("step_main_outer.vk.coeff." <> show (getFinite fi)) chunks
    -- Emit the 6 "idx" commitments by OCaml's name order (generic, psm,
    -- complete_add, mul, emul, endomul_scalar) to match `List.iter
    -- idx_pts` in step_main.ml.
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

    -- IMPORTANT: OCaml `step_main.ml:540-555` builds
    -- `challenge_polynomial_commitments` from `proof_witnesses` (length =
    -- rule's actual prev count), and the comment at L651-653 explicitly
    -- says `(* Note: the bulletproof_challenges here are unpadded! *)`.
    -- The mpvMax `Vector.extend_front` happens ONLY on
    -- `unfinalized_proofs` (the output, L661-663), NOT on the inputs to
    -- `hash_messages_for_next_step_proof`. So `proofData` here stays at
    -- length `len` (= rule's prev count) — never padded to `mpvMax`.
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

  -- 10. Build output: `mpvMax × 32` (unfinalized) + 1 (step msg) +
  --     `mpvMax` (wrap msgs). Front-pad `unfinalizedProofs` from `len`
  --     to `mpvMax` with `const_` dummies. `msgsWrap` is already
  --     `mpvMax`-sized — padding entries were `exists`-allocated at
  --     step 6, so its dummy positions are circuit Vars (not
  --     Constants) and the output→PI `assertEqual_` permutation-ties
  --     without emitting an extra Generic gate.
  --
  -- The padding dummy uses `bcd.maxProofsVerified = len` (the rule's
  -- own prev count, NOT `mpvMax`).
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

