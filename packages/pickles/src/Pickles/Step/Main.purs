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
  ( SlotVkSource(..)
  -- * Rule abstraction
  , RuleOutput
  -- * Spec-indexed per-slot carrier step_main
  , StepMainSrsData
  , UnfinalizedProof
  , liftDummyPerProofUnfinalized
  , stepMain
  -- * mpvMax-padding
  , class IntEq
  , class MpvPaddingDispatch
  , mpvFrontPadVecD
  , class MpvPadding
  , mpvFrontPad
  , mpvFrontPadVec
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Array as Array
import Data.Fin (getFinite)
import Data.Foldable (foldM)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Maybe (Maybe(..), fromJust)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (traverse)
import Data.Vector (Vector, (!!), (:<))
import Data.Vector as Vector
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBaseLookup, mkSideloadedLagrangeLookup)
import Pickles.Sponge (initialSpongeCircuit)
import Pickles.Sideload.Advice (class TraverseSideloadedVKsCarrier, traverseSideloadedVKsCarrier)
import Pickles.Sideload.VerificationKey (Checked(..))
import Pickles.Step.Advice (class StepPrevValuesM, class StepSlotsM, class StepUserOutputM, class StepWitnessM, getMessagesForNextWrapProof, getMessagesForNextWrapProofDummyHash, getStepPublicInput, getStepSlotsCarrier, getStepUnfinalizedProofs, getWrapVerifierIndex, setUserPublicOutputFields)
import Pickles.Step.FinalizeOtherProof (DomainMode(..))
import Pickles.Step.Prevs (class PrevsCarrier, StepSlot(..), traversePrevsA)
import Pickles.Step.VerifyOne (VerifyOneInput, verifyOne)
import Pickles.Types (BranchData(..), FopProofState(..), PaddedLength, PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepField, StepIPARounds, StepPerProofWitness(..), StepProofState(..), UnfinalizedFieldCount, VerificationKey(..), WrapIPARounds, WrapProof(..), WrapProofMessages(..), WrapProofOpening(..))
import Pickles.Verify (ivpTrace)
import Prim.Boolean (False, True)
import Prim.Int (class Add, class Compare, class Mul)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, UnChecked(..), assertAll_, const_, exists, false_, label, true_)
import Snarky.Circuit.DSL.Monad (class CheckedType)
import Snarky.Circuit.DSL.SizedF (SizedF, toField)
import Snarky.Circuit.DSL.SizedF (unsafeFromField) as SizedF
import Snarky.Circuit.Kimchi (SplitField(..), Type1(..), Type2(..), groupMapParams)
import Snarky.Circuit.RandomOracle.Sponge as Sponge
import Snarky.Circuit.Types (class CircuitType, varToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (EndoScalar(..), curveParams, endoScalar)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
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
-- | (e.g. `FVar StepField` for Field-valued outputs). Kept separate from
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

-------------------------------------------------------------------------------
-- | Per-slot wrap VK source — three-way dispatch.
-- |
-- | Each prev slot's verifier-circuit wrap-VK comes from one of
-- | three sources, mirroring OCaml `step_main.ml:513-528`'s dispatch
-- | on `Type_equal.Id.same_witness self.id tag.id` + `tag.kind`:
-- |
-- |   * `ConstVk constVk` — slot's prev is a COMPILED rule whose
-- |     wrap VK is known at step-compile time. OCaml
-- |     `of_compiled_with_known_wrap_key` maps `~f:Inner_curve.constant`
-- |     over the coords; the VK lives as compile-time CONSTANTS in
-- |     the circuit (no allocation, no on-curve checks, downstream
-- |     `mul_ const var` short-circuits to `Scale`). Used for
-- |     External tags.
-- |
-- |   * `SharedExistsVk` — slot's prev is SELF. Self's wrap VK
-- |     doesn't exist at step-compile time (chicken-and-egg with wrap
-- |     compile), so OCaml uses `dlog_plonk_index`
-- |     (`step_main.ml:498`) — the SHARED VK allocated ONCE at the
-- |     top of `step_main` via `Req.Wrap_index`. Every Self slot
-- |     reuses that single allocation. Used for Self tags.
-- |
-- |   * `SideloadedExistsVk perDomainLagrangeAts` — slot's prev is a
-- |     side-loaded tag whose wrap VK is supplied at runtime via the
-- |     `Pickles.Sideload.Advice.SideloadedVKsCarrier`. The in-circuit
-- |     VK is allocated PER SLOT against `verificationKeyTyp` —
-- |     distinct from `SharedExistsVk` because each side-loaded slot
-- |     can have a different VK and because the side-loaded VK
-- |     carries extra fields (`max_proofs_verified` and
-- |     `actual_wrap_domain_size` one-hot bits) for the verifier's
-- |     proofs-verified mask + lagrange-domain mux. Mirrors OCaml
-- |     `dump_side_loaded_main.ml:142-156`'s
-- |     `exists Side_loaded.Verification_key.typ ~compute:` +
-- |     `Side_loaded.in_circuit` flow.
-- |
-- |     The carried `Vector 3 (Int -> AffinePoint (F StepField))` are
-- |     the three per-domain lagrange-base lookup tables (one each
-- |     for `wrap_domain ∈ {N0, N1, N2}`). The IVP's
-- |     `lagrangeAt` for this slot muxes among them via the in-circuit
-- |     `actualWrapDomainSize` one-hot bits — see
-- |     `Pickles.PublicInputCommit.mkSideloadedLagrangeLookup` and
-- |     OCaml `step_verifier.ml`'s `public_input_commitment_dynamic`
-- |     (lines 409-456).
data SlotVkSource
  = ConstVk (VerificationKey (WeierstrassAffinePoint PallasG (F StepField)))
  | SharedExistsVk
  | SideloadedExistsVk (Vector 3 (Int -> AffinePoint (F StepField)))

-------------------------------------------------------------------------------
-- | SRS data for step_main
-------------------------------------------------------------------------------

-- | SRS data that carries per-slot FOP domain-log2 values and
-- | per-slot wrap-VK sources.
-- |
-- | In OCaml's `step_main`, `finalize_other_proof` is called per prev
-- | slot with `~step_domains:d.step_domains` — the PREV'S
-- | step_domains vector. For self-recursive rules (Simple_chain) all
-- | slots share the same value; for heterogeneous prevs
-- | (Tree_proof_return: slot 0's prev = No_recursion_return @ 2^13;
-- | slot 1's prev = self @ 2^16) the per-slot values differ.
-- |
-- | Per-slot wrap-VK source dispatched via `SlotVkSource` — see its
-- | doc above for the semantics of each constructor.
-- |
-- | Shapes for the test fixtures:
-- |   * Simple_chain N1  : `[SharedExistsVk]`
-- |   * Simple_chain N2  : `[SharedExistsVk, SharedExistsVk]`
-- |   * Add_one_return   : `[]` (N=0, no slots)
-- |   * Tree_proof_return: `[ConstVk no_rec_vk, SharedExistsVk]`
-- |   * Side-loaded main : `[SideloadedExistsVk, …]`
type StepMainSrsData len nd =
  { -- | Per-slot lagrange commitments. In OCaml
    -- | `x_hat = Σᵢ x[i] * lagrange_commitment(~domain:d.wrap_domain, srs, i)`
    -- | (step_verifier.ml:564-571) uses the PREV's `wrap_domain`, read
    -- | from the per-slot `Types_map.For_step.t`. The SRS itself is
    -- | shared (one Tock URS, step_main.ml:394). For heterogeneous
    -- | prevs (Tree_proof_return: slot 0 @ domain 2^13; slot 1 @
    -- | domain 2^14), the lagrange commitments at each index differ
    -- | per slot — same SRS, different domain size, different `i`-th
    -- | lagrange basis point.
    perSlotLagrangeAt :: Vector len (LagrangeBaseLookup StepField)
  -- | Shared Tock SRS h-generator. `Generators.h =
  -- | Kimchi_bindings.Protocol.SRS.Fq.urs_h (Tock URS)`
  -- | (step_main_inputs.ml:182-187); a single SRS-level constant,
  -- | NOT per-slot.
  , blindingH :: AffinePoint (F StepField)
  -- | Per-slot Vector of all step-domain log2s the slot's prev
  -- | source could have. For single-rule callers (and any slot whose
  -- | source has a single branch) this is `Vector 1 [theLog2]`;
  -- | for multi-rule Self prevs whose source is a `branches`-branch
  -- | proof system this is `Vector branches [log2_0, ..., log2_{branches-1}]`.
  -- | Mirrors OCaml `domain_for_compiled`'s `domains` Vector
  -- | (`step_verifier.ml:879-899`), which is then deduped into
  -- | `unique_domains` for `Pseudo.Domain.to_domain` dispatch.
  , perSlotFopDomainLog2s :: Vector len (Vector nd Int)
  , perSlotVkSources :: Vector len SlotVkSource
  -- | Thunk producing the dummy `UnfinalizedProof` used to front-pad
  -- | the step PI's unfinalized_proofs vector from `len` to `mpvMax`.
  -- | Mirrors OCaml `step.ml:782-787` (`Vector.extend_front ...
  -- | Unfinalized.dummy`). Construct via
  -- | `liftDummyPerProofUnfinalized` applied to
  -- | `Pickles.Prove.Step.mkDummyPerProofUnfinalized`.
  -- |
  -- | Wrapped in `Unit ->` because `mkDummyPerProofUnfinalized`
  -- | indirectly calls Rust FFI (`pallasSrsBPolyCommitmentPoint`,
  -- | `vestaSrsBPolyCommitmentPoint`) which can advance the chacha8
  -- | RNG counter shared with the kimchi prover. Forcing the thunk
  -- | only when `mpvPad > 0` keeps the single-rule path
  -- | byte-identical with the pre-Phase-2b.31a witness.
  , dummyUnfp :: Unit -> UnfinalizedProof
  }

-------------------------------------------------------------------------------
-- | Helpers
-------------------------------------------------------------------------------

unwrapPt :: WeierstrassAffinePoint PallasG (FVar StepField) -> AffinePoint (FVar StepField)
unwrapPt (WeierstrassAffinePoint pt) = pt

stepEndoVal :: StepField
stepEndoVal = let EndoScalar e = endoScalar @Vesta.BaseField @StepField in e

--------------------------------------------------------------------------------
-- MpvPadding class
--
-- Relates `mpvPad + len = mpvMax` at the type level for step PI
-- mpvMax-padding (mirroring OCaml `step.ml:782-787`'s
-- `Vector.extend_front unfinalized_proofs ... Unfinalized.dummy`).
--
-- Implementation dispatches on `IntEq len mpvMax` — both positions
-- are always concrete at use sites (from caller @-args), so the
-- Boolean is determined cleanly. The True branch (`len = mpvMax`)
-- pins `mpvPad = 0` via the head pattern; the False branch defers
-- to `Prim.Int.Add` for the actual relation.
--
-- The asymmetric formulations we tried earlier (literal `0` in head,
-- IsZero-gated dispatch) all hit corners of PureScript's instance
-- resolution where `else` chains don't fall through cleanly. Keying
-- the dispatch on `IntEq len mpvMax` works because `len` and
-- `mpvMax` are *always* both concrete at the points PS needs to
-- discharge the constraint:
--
--   * abstract `MpvPadding 0 a a`: IntEq a a → True ✓
--   * concrete distinct `MpvPadding 1 0 1`: IntEq 0 1 → False, defers
--     to Add 1 0 1 ✓
--   * fundep-derived `MpvPadding ? 1 1`: IntEq 1 1 → True, pins
--     mpvPad = 0 ✓
--------------------------------------------------------------------------------

class IntEq (a :: Int) (b :: Int) (res :: Boolean) | a b -> res

instance IntEq a a True
else instance IntEq a b False

class
  MpvPaddingDispatch (isEqual :: Boolean) (mpvPad :: Int) (len :: Int) (mpvMax :: Int)
  | isEqual mpvPad len -> mpvMax
  , isEqual len mpvMax -> mpvPad
  , isEqual mpvPad mpvMax -> len
  where
  mpvFrontPadVecD :: forall a. Vector mpvPad a -> Vector len a -> Vector mpvMax a

instance MpvPaddingDispatch True 0 len len where
  mpvFrontPadVecD _ real = real

instance Add mpvPad len mpvMax => MpvPaddingDispatch False mpvPad len mpvMax where
  mpvFrontPadVecD padding real = Vector.append padding real

class
  MpvPadding (mpvPad :: Int) (len :: Int) (mpvMax :: Int)
  | mpvPad len -> mpvMax
  , len mpvMax -> mpvPad
  , mpvPad mpvMax -> len
  where
  -- | Concatenate a padding vector with a real vector to produce the
  -- | full mpvMax-sized vector. Dispatches through `MpvPaddingDispatch`:
  -- | when `mpvPad = 0` the True instance returns `real` directly (no
  -- | `Add 0 len len` constraint needed); otherwise the False instance
  -- | uses `Vector.append`.
  mpvFrontPadVec :: forall a. Vector mpvPad a -> Vector len a -> Vector mpvMax a

instance
  ( IntEq len mpvMax isEqual
  , MpvPaddingDispatch isEqual mpvPad len mpvMax
  ) =>
  MpvPadding mpvPad len mpvMax where
  mpvFrontPadVec = mpvFrontPadVecD @isEqual

-- | Front-pad a `Vector len a` with `mpvPad` copies of a dummy value
-- | to produce a `Vector mpvMax a`. The `MpvPadding mpvPad len mpvMax`
-- | constraint witnesses `mpvPad + len = mpvMax` at the type level.
-- |
-- | The dummy is a thunk so the single-rule path (`mpvPad = 0`) does
-- | NOT force evaluation of the dummy — important because building
-- | the dummy can trigger Rust FFI (lagrange / blinding-generator
-- | computations) that advance shared chacha8 RNG state.
-- |
-- | Implementation: when `mpvPad = 0`, `MpvPadding 0 len len` instance
-- | guarantees `mpvMax = len` so we `unsafeCoerce real` directly
-- | (zero work, byte-identical witness). When `mpvPad > 0`, we build
-- | a runtime-sized array and re-wrap via `Vector.toVector +
-- | unsafePartial fromJust` (the runtime check is a tautology — array
-- | length always equals `mpvPad + len = mpvMax`).
mpvFrontPad
  :: forall a mpvPad len mpvMax
   . MpvPadding mpvPad len mpvMax
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
            <> (Vector.toUnfoldable real :: Array a)
      in
        unsafePartial $ fromJust $ Vector.toVector @mpvMax arr

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

buildVerifyOneInput
  :: forall @n pad
   . Reflectable n Int
  => Reflectable pad Int
  => Add pad n PaddedLength
  => PerProofWitness n
  -> Array (FVar StepField) -- prev proof's public input, pre-flattened
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
    fullMasks = pw.branchData.mask0 :< pw.branchData.mask1 :< Vector.nil

    proofMask :: Vector n (BoolVar StepField)
    proofMask = Vector.drop @pad fullMasks
  in
    { appStateFields
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
-- | V2 step_main — spec-indexed per-slot carrier variant
-- |
-- | Drops `getStepPerProofWitnesses` / `traverse allocatePerProofWitness`
-- | / `Vector.generateA @n` in favor of `getStepSlotsCarrier` + a single
-- | `traversePrevsA` that walks the carrier per slot, extracting SPPW
-- | from `StepSlot`, allocating, and running verify_one — all with the
-- | per-slot `n_i` in scope.
-- |
-- | Everything else (public input allocation, wrap VK, unfinalized
-- | proofs, messages_for_next_wrap_proof, outer hash, output
-- | assembly) is identical to `stepMain` — the only structural
-- | difference is the per-slot heterogeneity source.
-------------------------------------------------------------------------------

stepMain
  :: forall @prevsSpec pad @outputSize @inputVal @input @outputVal @output @prevInputVal @prevInput
       @valCarrier @mpvMax @mpvPad @nd ndPred
       len carrier carrierVar sideloadedVkCarrier
       unfsTotal digestPlusUnfs
       t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  -- Spec-indexed walk that allocates a per-side-loaded-slot
  -- `VerificationKeyVar StepField` via `exists` against each
  -- bundle's `circuit` (a `Checked Boolean ...`). Compiled slots
  -- contribute `Nothing`. Caller decides where the carrier value
  -- comes from — for compiled-only specs the carrier is an
  -- all-Unit chain (`mkUnitVkCarrier` synthesizes one); for specs
  -- with side-loaded slots the caller sources from advice.
  => TraverseSideloadedVKsCarrier prevsSpec len sideloadedVkCarrier
  => Add 1 ndPred nd
  => Compare 0 nd LT
  => Reflectable nd Int
  => StepWitnessM len StepIPARounds WrapIPARounds PallasG StepField m inputVal
  => StepSlotsM prevsSpec StepIPARounds WrapIPARounds PallasG StepField m len carrier
  => StepPrevValuesM m valCarrier
  => StepUserOutputM m
  => CircuitType StepField inputVal input
  => CircuitType StepField outputVal output
  => CircuitType StepField prevInputVal prevInput
  => CircuitType StepField carrier carrierVar
  => CheckedType StepField (KimchiConstraint StepField) carrierVar
  => PrevsCarrier
       prevsSpec
       StepIPARounds
       WrapIPARounds
       (FVar StepField)
       (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
       (BoolVar StepField)
       len
       carrierVar
  => CheckedType StepField (KimchiConstraint StepField) input
  => Reflectable len Int
  => Reflectable pad Int
  => Reflectable mpvMax Int
  => Reflectable mpvPad Int
  => Add pad len PaddedLength
  -- mpvMax-padding. When `mpvMax = len` then `mpvPad = 0` and padding
  -- emits nothing (circuit shape unchanged). When `mpvPad > 0`,
  -- `mpvFrontPad` prepends that many dummy entries.
  => MpvPadding mpvPad len mpvMax
  => Mul mpvMax UnfinalizedFieldCount unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs mpvMax outputSize
  => (input -> Snarky (KimchiConstraint StepField) t m (RuleOutput len prevInput output))
  -> StepMainSrsData len nd
  -> AffinePoint StepField
  -> sideloadedVkCarrier
  -> Snarky (KimchiConstraint StepField) t m (Vector outputSize (FVar StepField))
stepMain
  rule
  { perSlotLagrangeAt
  , blindingH
  , perSlotFopDomainLog2s
  , perSlotVkSources
  , dummyUnfp
  }
  dummySg
  sideloadedVkCarrier = do
  -- 1. exists: public input via Req.App_state.
  let
    requestInput :: m inputVal
    requestInput = getStepPublicInput @len @StepIPARounds @WrapIPARounds @PallasG unit
  (publicInput :: input) <- exists $ lift requestInput

  -- 2. rule_main
  { prevPublicInputs, proofMustVerify, publicOutput } <-
    label "rule_main" $ rule publicInput

  let
    publicInputFields = varToFields @StepField @inputVal publicInput
    publicOutputFields = varToFields @StepField @outputVal publicOutput
    hashAppFields = publicInputFields <> publicOutputFields

  -- Capture the rule's user `publicOutput` FVars so the prover can
  -- evaluate them post-solve. Dispatched through the same `exists +
  -- m`-action pattern as the other advice methods, mirroring how
  -- OCaml sends `Req.Return_value` from inside an `exists` block
  -- (mina/src/lib/crypto/pickles/step.ml:896-898). At compile time
  -- `exists` skips the witness body so the `Effect` `throw` instance
  -- never fires; at solve time the `StepProverT` instance writes to
  -- its `StepProverCapture` State slot, which `stepSolveAndProve`
  -- reads after the solver completes. The `exists` allocates a fresh
  -- `Unit` var (`sizeInFields = 0`, no actual circuit slot
  -- allocated), so this introduces no constraints.
  _ :: Unit <- exists $ lift do
    setUserPublicOutputFields publicOutputFields
    pure unit

  -- 3. exists: SHARED VK via Req.Wrap_index.
  --    Mirrors OCaml's `dlog_plonk_index` (step_main.ml:498) — one
  --    exists-allocation at the top, reused by every `Nothing` slot
  --    (i.e. slots whose prev is SELF). Slots with `Just vk` ignore
  --    this allocation and inline their constant VK instead.
  --
  -- Also used directly by the outer hash (step 9) — the
  -- hash_messages_for_next_step_proof sponge absorbs self's wrap VK
  -- commitments (= `dlog_plonk_index`) once, NOT per-slot.
  VerificationKey sharedVkRec <- label "exists_wrap_index"
    $ exists
    $ lift
    $ getWrapVerifierIndex @len @StepIPARounds @WrapIPARounds @PallasG unit
  let
    vk =
      { sigma: Vector.take @6 sharedVkRec.sigma
      , sigmaLast: Vector.last sharedVkRec.sigma
      , coeff: sharedVkRec.coeff
      , index: sharedVkRec.index
      }

  -- 3b. exists: per-slot side-loaded VKs.
  --    Walks the spec-indexed `sideloadedVkCarrier` (a chain of
  --    `Unit /\ ... /\ VerificationKey /\ ...`); for each
  --    `PrevsSpecSideLoadedCons` slot, allocates a
  --    `VerificationKeyVar StepField` via `exists` against the
  --    bundle's `circuit` field (`Checked Boolean ...`). Compiled
  --    slots contribute `Nothing`. Result is a parallel
  --    `Vector len (Maybe (VerificationKeyVar StepField))` aligned
  --    slot-by-slot with `perSlotVkSources`.
  --
  --    Mirrors OCaml `dump_side_loaded_main.ml:142-156`:
  --      let vk = exists Side_loaded.Verification_key.typ ~compute:...
  --      Side_loaded.in_circuit side_loaded_tag vk
  --
  --    For compiled-only rules (no `PrevsSpecSideLoadedCons` in
  --    the spec) the carrier is the all-Unit chain and the
  --    traversal contributes no constraints.
  perSlotSideloadedVks <- label "exists_sideloaded_vks"
    $ traverseSideloadedVKsCarrier @prevsSpec sideloadedVkCarrier

  -- 4. exists: per-slot carrier via Req.Proof_with_datas — the v2
  --    spec-indexed variant. Each slot of the carrier holds a
  --    `StepSlot n_i ds dw …` typed with its own per-slot n_i.
  slotsCarrier <- label "exists_prevs"
    $ exists
    $ lift
    $ getStepSlotsCarrier @prevsSpec @StepIPARounds @WrapIPARounds @PallasG unit

  -- 5. exists: unfinalized proofs (uniform Vector len).
  rawUnfinalizedProofs <- label "exists_unfinalized"
    $ exists
    $ lift
    $ getStepUnfinalizedProofs @len @StepIPARounds @WrapIPARounds @PallasG unit
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
  msgsWrapReal <- exists $ lift
    $ getMessagesForNextWrapProof @len @StepIPARounds @WrapIPARounds @PallasG unit
  msgsWrapPadding <- exists $ lift do
    dummyHash <- getMessagesForNextWrapProofDummyHash
      @len
      @StepIPARounds
      @WrapIPARounds
      @PallasG
      unit
    pure (Vector.replicate @mpvPad dummyHash)
  let
    msgsWrap :: Vector mpvMax (FVar StepField)
    msgsWrap = mpvFrontPadVec msgsWrapPadding msgsWrapReal

  let
    -- Lift a value-side VK to const_ FVars. Used when a slot has
    -- `Just vk` — the VK coords appear as compile-time constants in
    -- the circuit (matches OCaml's `Array.map ~f:Inner_curve.constant`
    -- in `of_compiled_with_known_wrap_key`, types_map.ml:214-215).
    liftConstVk
      :: VerificationKey (WeierstrassAffinePoint PallasG (F StepField))
      -> VerificationKey (WeierstrassAffinePoint PallasG (FVar StepField))
    liftConstVk (VerificationKey r) = VerificationKey
      { sigma: map liftWaPt r.sigma
      , coeff: map liftWaPt r.coeff
      , index: map liftWaPt r.index
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
    constDummySg = { x: const_ dummySg.x, y: const_ dummySg.y }

  -- 8. verify_one × len + Assert.all (inside prevs_verified label).
  -- Drive structurally via traversePrevsA — each callback invocation
  -- has its slot's `n_i` in scope so per-slot sizes (prevSgs, etc.)
  -- are correct, and each slot's `fopParams` / `vkComms` are computed
  -- from the slot's own `fopDomainLog2` and `knownWrapKey`
  -- (mirroring OCaml's `finalize_other_proof ~step_domains:d.step_domains`
  -- and the `of_compiled_with_known_wrap_key` / `self_data` dispatch
  -- at step_main.ml:513-528).
  results <- label "prevs_verified" do
    rs <- traversePrevsA @prevsSpec
      ( \i (StepSlot slotRec) -> do
          pw <- allocatePerProofWitness slotRec.sppw
          let
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
            slotConfig = case perSlotVkSources !! i of
              ConstVk constVk ->
                { lagrangeAt: perSlotLagrangeAt !! i
                , correctionMode: PureCorrections
                , fopDomainMode: KnownDomainsMode
                , vkRec: let VerificationKey r = liftConstVk constVk in r
                }
              SharedExistsVk ->
                { lagrangeAt: perSlotLagrangeAt !! i
                , correctionMode: PureCorrections
                , fopDomainMode: KnownDomainsMode
                , vkRec: sharedVkRec
                }
              -- Side-loaded: read the per-slot exists-allocated VK
              -- from `perSlotSideloadedVks` (built above by
              -- `traverseSideloadedVKsCarrier`). Each `Just (Checked
              -- sl)` contains the slot's `wrapIndex` and
              -- `actualWrapDomainSize` one-hot bitvec; mux the three
              -- per-domain lagrange tables via
              -- `mkSideloadedLagrangeLookup`. A `Nothing` would
              -- indicate a spec/dispatch mismatch (the spec's
              -- `PrevsSpecSideLoadedCons` slot got routed to
              -- `SideloadedExistsVk` here, but the traversal class
              -- produced `Nothing` at this position — should be
              -- impossible by construction).
              SideloadedExistsVk perDomainLagrangeAts ->
                case perSlotSideloadedVks !! i of
                  Just (Checked sl) ->
                    { lagrangeAt: mkSideloadedLagrangeLookup
                        (curveParams (Proxy @PallasG))
                        sl.actualWrapDomainSize
                        perDomainLagrangeAts
                    , correctionMode: InCircuitCorrections
                    , fopDomainMode: SideLoadedMode
                    , vkRec: let VerificationKey r = sl.wrapIndex in r
                    }
                  Nothing ->
                    unsafeCrashWith
                      "Pickles.Step.Main: SideloadedExistsVk slot has \
                      \no per-slot allocated VK — \
                      \traverseSideloadedVKsCarrier should have \
                      \produced a Just for every PrevsSpecSideLoadedCons \
                      \position. Spec/dispatch mismatch."

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
              -- extra `Field.equal` and one extra mask `Field.mul`
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
              { sigma: map unwrapPt slotVk.sigma
              , sigmaLast: unwrapPt slotVk.sigmaLast
              , coeff: map unwrapPt slotVk.coeff
              , index: map unwrapPt slotVk.index
              }

            prevInputVar = prevPublicInputs !! i
            input = buildVerifyOneInput pw
              (varToFields @StepField @prevInputVal prevInputVar)
              (proofMustVerify !! i)
              (unfinalizedProofs !! i)
              (msgsWrapReal !! i)
              slotVkComms
              constDummySg
          r <- verifyOne slotFopParams input slotIvpParams
          -- Carry pw.sg out alongside the verify_one result so the
          -- outer hash can absorb it.
          pure { sg: pw.sg, expandedChallenges: r.expandedChallenges, result: r.result }
      )
      slotsCarrier
    assertAll_ (Vector.toUnfoldable $ map _.result rs)
    pure rs

  -- 9. Outer hash: hash_messages_for_next_step_proof (identical to v1).
  outerDigest <- label "hash_messages_for_next_step_proof" do
    let
      absorbPt s pt = do
        let { x, y } = unwrapPt pt
        s1 <- Sponge.absorb x s
        Sponge.absorb y s1

    -- Emit all 7 sigmas under a contiguous `sigma.0..6` index to match
    -- OCaml's `Vector.iter dlog_plonk_index.sigma_comm`. Internally PS
    -- splits into `sigma` (Vector 6) + `sigmaLast` for the sponge path,
    -- but the trace labels stay contiguous.
    forWithIndex_ vk.sigma \fi pt -> do
      let i = getFinite fi
      let { x, y } = unwrapPt pt
      ivpTrace ("step_main_outer.vk.sigma." <> show i <> ".x") x
      ivpTrace ("step_main_outer.vk.sigma." <> show i <> ".y") y
    let { x: slX, y: slY } = unwrapPt vk.sigmaLast
    ivpTrace "step_main_outer.vk.sigma.6.x" slX
    ivpTrace "step_main_outer.vk.sigma.6.y" slY
    forWithIndex_ vk.coeff \fi pt -> do
      let i = getFinite fi
      let { x, y } = unwrapPt pt
      ivpTrace ("step_main_outer.vk.coeff." <> show i <> ".x") x
      ivpTrace ("step_main_outer.vk.coeff." <> show i <> ".y") y
    -- Emit the 6 "idx" commitments by OCaml's name order (generic, psm,
    -- complete_add, mul, emul, endomul_scalar) to match `List.iter
    -- idx_pts` in step_main.ml.
    let idxNames = "generic" :< "psm" :< "complete_add" :< "mul" :< "emul" :< "endomul_scalar" :< Vector.nil
    forWithIndex_ vk.index \fi pt -> do
      let { x, y } = unwrapPt pt
      let name = Vector.index idxNames fi
      ivpTrace ("step_main_outer.vk.idx." <> name <> ".x") x
      ivpTrace ("step_main_outer.vk.idx." <> name <> ".y") y
    forWithIndex_ hashAppFields \i f ->
      ivpTrace ("step_main_outer.app_state." <> show i) f

    spongeAfterIndex <- do
      let sponge0 = initialSpongeCircuit :: Sponge.Sponge (FVar StepField)
      s1 <- foldM absorbPt sponge0 vk.sigma
      s2 <- absorbPt s1 vk.sigmaLast
      s3 <- foldM absorbPt s2 vk.coeff
      foldM absorbPt s3 vk.index

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

    { result: digest } <- Sponge.squeeze sAfterProofs
    ivpTrace "step_main_outer.digest" digest
    pure digest

  -- 10. Build output: mpvMax × 32 (unfinalized) + 1 (step msg) + mpvMax (wrap msgs).
  --     Front-pad `unfinalizedProofs` from `len` to `mpvMax` with const_
  --     dummies (mirrors OCaml `step.ml:782-787`'s
  --     `Vector.extend_front ... Unfinalized.dummy`). `msgsWrap` is
  --     already mpvMax-sized: padding entries were exists-allocated at
  --     step 6 (mirroring OCaml step_main.ml:368-370), so its dummy
  --     positions are circuit Vars (not Constants) and the
  --     output→PI assertEqual_ permutation-ties without emitting an
  --     extra Generic gate.
  let
    unfinalizedProofsPadded :: Vector mpvMax UnfinalizedProof
    unfinalizedProofsPadded = mpvFrontPad dummyUnfp unfinalizedProofs

    unfsFlat :: Vector unfsTotal (FVar StepField)
    unfsFlat = Vector.concat (map unfFields unfinalizedProofsPadded)

    digestVec :: Vector 1 (FVar StepField)
    digestVec = outerDigest :< Vector.nil

    outputV :: Vector outputSize (FVar StepField)
    outputV = unfsFlat `Vector.append` digestVec `Vector.append` msgsWrap

  pure outputV

