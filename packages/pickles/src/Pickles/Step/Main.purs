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
  -- * Spec-indexed per-slot carrier step_main
  , StepMainSrsData
  , stepMain
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Array as Array
import Data.Fin (getFinite)
import Data.Foldable (foldM)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable, reflectType)
import Data.Traversable (traverse)
import Data.Vector (Vector, (!!), (:<))
import Data.Vector as Vector
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBaseLookup)
import Pickles.Sponge (initialSpongeCircuit)
import Pickles.Step.Advice (class StepSlotsM, class StepWitnessM, getMessagesForNextWrapProof, getStepPublicInput, getStepSlotsCarrier, getStepUnfinalizedProofs, getWrapVerifierIndex)
import Pickles.Step.Prevs (class PrevsCarrier, StepSlot(..), traversePrevsA)
import Pickles.Step.VerifyOne (VerifyOneInput, verifyOne)
import Pickles.Types (BranchData(..), FopProofState(..), PaddedLength, PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepField, StepIPARounds, StepPerProofWitness(..), StepProofState(..), VerificationKey(..), WrapIPARounds, WrapProof(..), WrapProofMessages(..), WrapProofOpening(..))
import Pickles.Util.Fatal (fromJust')
import Pickles.Verify (ivpTrace)
import Prim.Int (class Add, class Mul)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, UnChecked(..), assertAll_, const_, exists, label)
import Snarky.Circuit.DSL.Monad (class CheckedType)
import Snarky.Circuit.DSL.SizedF (SizedF, toField)
import Snarky.Circuit.Kimchi (SplitField(..), Type1(..), Type2(..), groupMapParams)
import Snarky.Circuit.RandomOracle.Sponge as Sponge
import Snarky.Circuit.Types (class CircuitType, varToFields)
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
-- | SRS data for step_main
-------------------------------------------------------------------------------

-- | SRS data that carries per-slot FOP domain-log2 values and
-- | per-slot known wrap verification keys.
-- |
-- | In OCaml's `step_main`, `finalize_other_proof` is called per prev
-- | slot with `~step_domains:d.step_domains` — the PREV'S
-- | step_domains vector. For self-recursive rules (Simple_chain) all
-- | slots share the same value; for heterogeneous prevs
-- | (Tree_proof_return: slot 0's prev = No_recursion_return @ 2^13;
-- | slot 1's prev = self @ 2^16) the per-slot values differ.
-- |
-- | Per-slot wrap VK mirrors OCaml's `~known_wrap_keys:
-- | 'branches Optional_wrap_key.t list`
-- | (= `'branches known option list`, `types_map.ml:188-196`). Each
-- | slot's entry is:
-- |
-- |   * `Just vk`   — slot's prev is a COMPILED rule whose wrap VK is
-- |                   known at step-compile time. OCaml's
-- |                   `Types_map.For_step.of_compiled_with_known_wrap_key`
-- |                   maps `~f:Inner_curve.constant` over the coords, so
-- |                   the VK lives as COMPILE-TIME CONSTANTS in the
-- |                   circuit — no allocation, no on-curve checks,
-- |                   downstream `mul_ const var` short-circuits to
-- |                   `Scale`.
-- |   * `Nothing`   — slot's prev is SELF. Self's wrap VK doesn't exist
-- |                   at step-compile time (chicken-and-egg with wrap
-- |                   compile), so OCaml uses `dlog_plonk_index`
-- |                   (step_main.ml:498) — the SHARED VK allocated via
-- |                   `exists` at the top of `step_main`. We mirror
-- |                   that: one shared exists-allocation, reused by
-- |                   every `Nothing` slot.
-- |
-- | Reference: step_main.ml:513-528 (the per-slot match on
-- | `self.id ?= tag.id` that dispatches to
-- | `of_compiled_with_known_wrap_key` or `self_data`).
-- |
-- | Shapes for the 4 circuit-diff fixtures:
-- |   * Simple_chain N1  : `[Nothing]`
-- |   * Simple_chain N2  : `[Nothing, Nothing]`
-- |   * Add_one_return   : `[]` (N=0, no slots)
-- |   * Tree_proof_return: `[Just no_rec_vk, Nothing]`
type StepMainSrsData len =
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
  , perSlotFopDomainLog2 :: Vector len Int
  , perSlotKnownWrapKeys ::
      Vector len
        (Maybe (VerificationKey (WeierstrassAffinePoint PallasG (F StepField))))
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
       len carrier carrierVar
       unfsTotal digestPlusUnfs
       t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => StepWitnessM len StepIPARounds WrapIPARounds PallasG StepField m inputVal
  => StepSlotsM prevsSpec StepIPARounds WrapIPARounds PallasG StepField m len carrier
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
  => Add pad len PaddedLength
  => Mul len 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs len outputSize
  => (input -> Snarky (KimchiConstraint StepField) t m (RuleOutput len prevInput output))
  -> StepMainSrsData len
  -> AffinePoint StepField
  -> Snarky (KimchiConstraint StepField) t m (Vector outputSize (FVar StepField))
stepMain
  rule
  { perSlotLagrangeAt
  , blindingH
  , perSlotFopDomainLog2
  , perSlotKnownWrapKeys
  }
  dummySg = do
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

  -- 6. exists: messages_for_next_wrap_proof (uniform Vector len).
  msgsWrap <- exists $ lift $ getMessagesForNextWrapProof @len @StepIPARounds @WrapIPARounds @PallasG unit

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
            slotFopDomainLog2 = perSlotFopDomainLog2 !! i
            slotLagrangeAt = perSlotLagrangeAt !! i

            slotIvpParams =
              { curveParams: curveParams (Proxy @PallasG)
              , lagrangeAt: slotLagrangeAt
              , blindingH
              , correctionMode: PureCorrections
              , endo: stepEndoVal
              , groupMapParams: groupMapParams (Proxy @PallasG)
              , useOptSponge: false
              }

            slotFopParams =
              { domain:
                  { generator: const_ (LinFFI.domainGenerator @StepField slotFopDomainLog2)
                  , shifts: map const_ (LinFFI.domainShifts @StepField slotFopDomainLog2)
                  }
              , domainLog2: slotFopDomainLog2
              , srsLengthLog2: reflectType (Proxy :: Proxy StepIPARounds)
              , endo: stepEndoVal
              , linearizationPoly: Linearization.pallas
              }

            -- Per-slot VK selection: Just → inline constants, Nothing
            -- → use shared exists-allocated VK.
            slotVkRec = case perSlotKnownWrapKeys !! i of
              Just constVk ->
                let VerificationKey r = liftConstVk constVk in r
              Nothing -> sharedVkRec

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
              (msgsWrap !! i)
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
    let idxNames = [ "generic", "psm", "complete_add", "mul", "emul", "endomul_scalar" ]
    forWithIndex_ vk.index \fi pt -> do
      let i = getFinite fi
      let { x, y } = unwrapPt pt
      let name = fromJust' ("step_main_outer idx name lookup at " <> show i) (Array.index idxNames i)
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

  -- 10. Build output: len × 32 (unfinalized) + 1 (step msg) + len (wrap msgs).
  let
    unfsFlat :: Vector unfsTotal (FVar StepField)
    unfsFlat = Vector.concat (map unfFields unfinalizedProofs)

    digestVec :: Vector 1 (FVar StepField)
    digestVec = outerDigest :< Vector.nil

    outputV :: Vector outputSize (FVar StepField)
    outputV = unfsFlat `Vector.append` digestVec `Vector.append` msgsWrap

  pure outputV

