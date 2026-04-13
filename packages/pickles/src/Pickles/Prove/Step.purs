-- | Prover-side infrastructure for `Pickles.Step.Main.stepMain`.
-- |
-- | Sister to `Pickles.Prove.Wrap`. This module provides the
-- | **effectful** glue that feeds `stepMain`'s `Req.*` advice during
-- | witness generation:
-- |
-- | * `StepAdvice` — a record holding all advice pieces (one per
-- |   OCaml `Req.*` request) with concrete, already-computed values.
-- | * `StepProverT` — a `ReaderT` transformer serving `StepAdvice` to
-- |   the circuit body. Instances below implement `StepWitnessM` so
-- |   the `stepMain` circuit body can `ask` for each advice piece.
-- | * `runStepProverT` — runner that supplies the advice and unwraps
-- |   to the base monad (`Effect`).
-- | * `stepProve` — compile + solve + kimchi proof creation, mirroring
-- |   OCaml's `Backend.Tick.Proof.create_async` call site in
-- |   `mina/src/lib/crypto/pickles/step.ml:800-852`.
-- |
-- | The module is polymorphic in `n` (max_proofs_verified), `ds`
-- | (step IPA rounds), and `dw` (wrap IPA rounds), matching
-- | `StepWitnessM`'s parameters. The commitment curve is pinned to
-- | `PallasG` (the wrap proof being verified by step has commitments
-- | on Pallas) and the field to `StepField` (= `Vesta.ScalarField` =
-- | `Pallas.BaseField`) — both of which are structural for any step
-- | circuit in the Pasta cycle, not specific to any one application
-- | rule.
module Pickles.Prove.Step
  ( StepBranchData
  , StepAdvice
  , StepProverT(..)
  , runStepProverT
  , BuildStepAdviceInput
  , buildStepAdvice
  , StepRule
  , StepProveContext
  , StepProveResult
  , stepProve
  ) where

import Prelude

import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Data.Array (concatMap)
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Newtype (class Newtype, un)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Exception (Error, error)
import Data.Maybe (fromJust)
import Partial.Unsafe (unsafePartial)
import Safe.Coerce (coerce)
import Pickles.Dummy (dummyIpaChallenges, roComputeResult, stepDummyFopProofState, wrapDummyUnfinalizedProof, wrapDomainLog2ForProofsVerified)
import Pickles.PlonkChecks (AllEvals)
import Pickles.Linearization.FFI (PointEval) as LFFI
import Pickles.ProofFFI (Proof, createProof)
import Pickles.ProofWitness (ProofWitness)
import Pickles.Step.Advice (class StepWitnessM)
import Pickles.Step.Main (RuleOutput, StepMainSrsData, stepMain)
import Pickles.Types (BranchData(..), FopProofState(..), PaddedLength, PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), StepField, StepIPARounds, StepPerProofWitness(..), StepProofState(..), VerificationKey(..), WrapField, WrapIPARounds, WrapProof(..), WrapProofMessages(..), WrapProofOpening(..))
import Pickles.Verify.Types (UnfinalizedProof)
import Prim.Int (class Add, class Mul)
import Snarky.Circuit.DSL (SizedF, coerceViaBits)
import Snarky.Circuit.DSL.SizedF (unwrapF, wrapF) as SizedF
import Snarky.Curves.Class (class PrimeField, fromBigInt, fromInt, generator, toAffine, toBigInt) as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Types.Shifted (SplitField, Type1, Type2, fromShifted, toShifted)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (SolverT, compile, makeSolver', runSolverT)
import Snarky.Backend.Kimchi (makeConstraintSystem, makeWitness)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor, createProverIndex, createVerifierIndex, verifyProverIndex)
import Snarky.Backend.Kimchi.Types (CRS, ConstraintSystem, ProverIndex, VerifierIndex)
import Snarky.Backend.Prover (emptyProverState)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, UnChecked(..))
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState(..), toKimchiRows)
import Snarky.Curves.Class (EndoScalar(..), endoScalar)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Advice
--------------------------------------------------------------------------------

-- | Per-proof branch data. OCaml:
-- |   `mina/src/lib/crypto/pickles/step_main.ml` packs each prev
-- |   proof's `branch_data` into the output via
-- |   `branch_data.pack = 4*domain_log2 + mask[0] + 2*mask[1]`.
-- |
-- | For single-rule compiles, all slots have the same `domainLog2`
-- | (read from `basic.step_domains.h` — for Simple_chain this is 16,
-- | per `dump_circuit_impl.ml:3723`) and `mask0`/`mask1` encode
-- | which prev-proof slot is active.
type StepBranchData =
  { domainLog2 :: F StepField
  , mask0 :: Boolean
  , mask1 :: Boolean
  }

-- | Private witness data the step prover supplies to `stepMain`. One
-- | field per `Req.*` request, in the same order `step_main.ml`
-- | consumes them. The field set mirrors the raw `StepWitnessM`
-- | accessors; the composed helpers (`getStepPerProofWitnesses` etc.)
-- | are derived in the `StepWitnessM` instance below.
-- |
-- | Type parameters mirror `StepWitnessM`:
-- |
-- | * `n`   — max_proofs_verified (varies per compile: N0, N1, or N2).
-- | * `ds`  — step IPA rounds (= `StepIPARounds` for production pickles).
-- | * `dw`  — wrap IPA rounds (= `WrapIPARounds` for production pickles).
-- |
-- | The commitment curve is pinned to `PallasG` (the wrap proof's
-- | commitment curve) and the field to `StepField` (= `Vesta.ScalarField`
-- | = `Pallas.BaseField`) — both are structural for any step circuit
-- | in the Pasta cycle.
type StepAdvice (n :: Int) (ds :: Int) (dw :: Int) =
  { stepInputFields :: Array (F StepField)
  , evals :: Vector n (ProofWitness (F StepField))
  , prevChallenges :: Vector n (Vector ds (F StepField))
  , messages ::
      Vector n
        { wComm :: Vector 15 (AffinePoint (F StepField))
        , zComm :: AffinePoint (F StepField)
        , tComm :: Vector 7 (AffinePoint (F StepField))
        }
  , openingProofs ::
      Vector n
        { delta :: AffinePoint (F StepField)
        , sg :: AffinePoint (F StepField)
        , lr :: Vector dw { l :: AffinePoint (F StepField), r :: AffinePoint (F StepField) }
        , z1 :: Type2 (SplitField (F StepField) Boolean)
        , z2 :: Type2 (SplitField (F StepField) Boolean)
        }
  , fopProofStates ::
      Vector n (UnfinalizedProof ds (F StepField) (Type1 (F StepField)) Boolean)
  , messagesForNextWrapProof :: Vector n (F StepField)
  , wrapVerifierIndex ::
      VerificationKey (WeierstrassAffinePoint PallasG (F StepField))
  , sgOld :: Vector n (AffinePoint (F StepField))
  , appState :: F StepField
  , publicUnfinalizedProofs ::
      Vector n
        ( PerProofUnfinalized
            dw
            (Type2 (SplitField (F StepField) Boolean))
            (F StepField)
            Boolean
        )
  -- | One per prev-proof slot. OCaml reads this from `step_domains`
  -- | + the active branch's proofs-verified mask; here we receive it
  -- | pre-computed so the advice stays purely data.
  , branchData :: Vector n StepBranchData
  }

--------------------------------------------------------------------------------
-- ReaderT + StepWitnessM instance
--------------------------------------------------------------------------------

-- | ReaderT transformer carrying a `StepAdvice` over a base monad.
newtype StepProverT
  :: Int
  -> Int
  -> Int
  -> (Type -> Type)
  -> Type
  -> Type
newtype StepProverT n ds dw m a =
  StepProverT (ReaderT (StepAdvice n ds dw) m a)

derive instance Newtype (StepProverT n ds dw m a) _
derive newtype instance Functor m => Functor (StepProverT n ds dw m)
derive newtype instance Apply m => Apply (StepProverT n ds dw m)
derive newtype instance Applicative m => Applicative (StepProverT n ds dw m)
derive newtype instance Bind m => Bind (StepProverT n ds dw m)
derive newtype instance Monad m => Monad (StepProverT n ds dw m)

-- | Supply the advice record and run the prover computation in the
-- | base monad.
runStepProverT
  :: forall n ds dw m a
   . StepAdvice n ds dw
  -> StepProverT n ds dw m a
  -> m a
runStepProverT advice (StepProverT m) = runReaderT m advice

-- | `StepWitnessM` instance. Raw getters are plain record projections
-- | via `ask`; `getStepPerProofWitnesses` composes the wire-format
-- | `StepPerProofWitness` from several raw fields, matching
-- | `step_main.ml`'s per-slot advice layout.
-- |
-- | Polymorphic in `ds`/`dw` (the IPA-round counts); the caller's
-- | choice gets unified with the stepMain constraint
-- | (`StepWitnessM n StepIPARounds WrapIPARounds PallasG StepField m`)
-- | at the `stepProve` call site via ordinary type inference, so
-- | `Pickles.Prove.Step` itself never writes `StepIPARounds` /
-- | `WrapIPARounds` literally.
instance
  ( Monad m
  , Reflectable n Int
  ) =>
  StepWitnessM
    n
    ds
    dw
    PallasG
    StepField
    (StepProverT n ds dw m) where
  getStepInputFields _ = StepProverT $ map _.stepInputFields ask
  getProofWitnesses _ = StepProverT $ map _.evals ask
  getPrevChallenges _ = StepProverT $ map _.prevChallenges ask
  getMessages _ = StepProverT $ map _.messages ask
  getOpeningProof _ = StepProverT $ map _.openingProofs ask
  getFopProofStates _ = StepProverT $ map _.fopProofStates ask
  getMessagesForNextWrapProof _ = StepProverT $ map _.messagesForNextWrapProof ask
  getWrapVerifierIndex _ = StepProverT $ map _.wrapVerifierIndex ask
  getSgOld _ = StepProverT $ map _.sgOld ask
  getStepAppState _ = StepProverT $ map _.appState ask
  getStepUnfinalizedProofs _ = StepProverT $ map _.publicUnfinalizedProofs ask
  getStepPerProofWitnesses _ = StepProverT $ do
    adv <- ask
    pure $ Vector.generate \i ->
      let
        pw = Vector.index adv.evals i
        fop = Vector.index adv.fopProofStates i
        opening = Vector.index adv.openingProofs i
        msgs = Vector.index adv.messages i
        bd = Vector.index adv.branchData i
        dv = fop.deferredValues
        p = dv.plonk
      in
        StepPerProofWitness
          { wrapProof: WrapProof
              { opening: WrapProofOpening
                  { lr: map (\r -> { l: WeierstrassAffinePoint r.l, r: WeierstrassAffinePoint r.r }) opening.lr
                  , z1: opening.z1
                  , z2: opening.z2
                  , delta: WeierstrassAffinePoint opening.delta
                  , sg: WeierstrassAffinePoint opening.sg
                  }
              , messages: WrapProofMessages
                  { wComm: map WeierstrassAffinePoint msgs.wComm
                  , zComm: WeierstrassAffinePoint msgs.zComm
                  , tComm: map WeierstrassAffinePoint msgs.tComm
                  }
              }
          , proofState: StepProofState
              { fopState: FopProofState
                  { combinedInnerProduct: fromShifted dv.combinedInnerProduct
                  , b: fromShifted dv.b
                  , zetaToSrsLength: fromShifted p.zetaToSrsLength
                  , zetaToDomainSize: fromShifted p.zetaToDomainSize
                  , perm: fromShifted p.perm
                  , spongeDigest: fop.spongeDigestBeforeEvaluations
                  , beta: UnChecked p.beta
                  , gamma: UnChecked p.gamma
                  , alpha: UnChecked p.alpha
                  , zeta: UnChecked p.zeta
                  , xi: UnChecked dv.xi
                  , bulletproofChallenges: map UnChecked dv.bulletproofChallenges
                  }
              , branchData: BranchData
                  { domainLog2: bd.domainLog2
                  , mask0: bd.mask0
                  , mask1: bd.mask1
                  }
              }
          , prevEvals: StepAllEvals
              { publicEvals: PointEval pw.allEvals.publicEvals
              , witnessEvals: map PointEval pw.allEvals.witnessEvals
              , coeffEvals: map PointEval pw.allEvals.coeffEvals
              , zEvals: PointEval pw.allEvals.zEvals
              , sigmaEvals: map PointEval pw.allEvals.sigmaEvals
              , indexEvals: map PointEval pw.allEvals.indexEvals
              , ftEval1: pw.allEvals.ftEval1
              }
          , prevChallenges: map UnChecked adv.prevChallenges
          , prevSgs: map WeierstrassAffinePoint adv.sgOld
          }

--------------------------------------------------------------------------------
-- Base-case advice builder
--
-- `buildStepAdvice` assembles a fully-populated `StepAdvice` from the
-- few parameters a specific inductive rule's BASE case actually picks
-- (appState, stepDomainLog2, mostRecentWidth). Every other field is
-- filled from the Ro-derived dummies in `Pickles.Dummy`, which are
-- hardcoded at the Pasta protocol constants `Tick.Rounds.n = 16`
-- and `Tock.Rounds.n = 15` — matching OCaml `dummy.ml:27-55` exactly.
--
-- Polymorphic in `n` (the step circuit's max_proofs_verified): the
-- per-slot fields are `Vector.replicate`d to the caller's choice of
-- `n`. The output type pins `ds` and `dw` at `StepIPARounds` /
-- `WrapIPARounds` because the underlying Pickles.Dummy helpers are
-- concretized there (see the module note above). Upstream
-- `stepMain`'s `StepWitnessM n StepIPARounds WrapIPARounds ...`
-- constraint lines up with this output type via type inference, so
-- the call site (e.g. SimpleChain.purs) never has to write the
-- round-count constants literally.
--
-- References:
--   OCaml `Proof.dummy h most_recent_width ~domain_log2` (proof.ml:115-208)
--   OCaml `step_main.ml:368-376` exists calls for Req.App_state,
--                                  Req.Unfinalized_proofs, Req.Wrap_index
--------------------------------------------------------------------------------

-- | Inputs `buildStepAdvice` needs from the caller. Everything else
-- | is protocol-constant dummy data derived from `Pickles.Dummy`.
type BuildStepAdviceInput =
  { -- | Value bound to the step circuit's app_state public input
    -- | (OCaml `Req.App_state`). For Simple_chain base case this is
    -- | `F zero` (self = 0).
    appState :: F StepField

  -- | `most_recent_width` parameter the OCaml `Proof.dummy` call
  -- | would pass. For Simple_chain at N1 this is 1. Drives the
  -- | wrap-domain choice for `stepDummyFopProofState` via
  -- | `common.ml:25-29 wrap_domains` (0 → 13, 1 → 14, 2 → 15).
  , mostRecentWidth :: Int

  -- | OCaml `Pickles.Proof.dummy`'s `~domain_log2` parameter. This is
  -- | the dummy wrap proof's evaluation domain, which becomes
  -- | `branch_data.domain_log2` inside its statement (see
  -- | `proof.ml:140-141`), and must equal the step circuit's FOP
  -- | `params.domainLog2` (= `wrap_domains.h` from `common.ml:25-29`).
  -- | For Simple_chain N1 this is 14. NOTE: This is NOT the step
  -- | circuit's own kimchi domain (= 16 per
  -- | `dump_circuit_impl.ml:3721-3723`); that value is determined by
  -- | kimchi at proof-creation time, not read from advice.
  , wrapDomainLog2 :: Int
  }

-- | Build a base-case `StepAdvice n` populated from Ro-derived
-- | dummies. Every per-slot field is replicated `n` times; for a
-- | single real slot the caller receives n=1 and all slots collapse
-- | to one entry. For multi-slot compiles (n > 1) the same dummy
-- | values are reused across slots — OCaml does the equivalent via
-- | `Vector.init Max_proofs_verified.n` in `step.ml:704-735`.
buildStepAdvice
  :: forall n
   . Reflectable n Int
  => BuildStepAdviceInput
  -> StepAdvice n StepIPARounds WrapIPARounds
buildStepAdvice input =
  let
    -- Pallas generator (= OCaml `Tock.Curve.one`). Reused for every
    -- curve-point field in the base-case dummy advice.
    g0 :: AffinePoint (F StepField)
    g0 = coerce
      ( unsafePartial fromJust $ Curves.toAffine (Curves.generator :: Pallas.G)
          :: AffinePoint StepField
      )

    g0w :: WeierstrassAffinePoint PallasG (F StepField)
    g0w = WeierstrassAffinePoint g0

    -- Ro-derived constants shared across all fields.
    r = roComputeResult

    -- z1 / z2 from OCaml `proof.ml:dummy` openings (Ro.tock values
    -- re-wrapped as cross-field Type2 SplitField in the step field).
    z1 :: Type2 (SplitField (F StepField) Boolean)
    z1 = toShifted (F r.proofZ1)

    z2 :: Type2 (SplitField (F StepField) Boolean)
    z2 = toShifted (F r.proofZ2)

    -- Ro-derived AllEvals (matches OCaml `Dummy.evals` at
    -- `dummy.ml:7-20`). Each bare StepField wrapped in F.
    -- NB: the `PointEval` here is the raw record from
    -- `Pickles.Linearization.FFI` (imported as `LFFI.PointEval`), NOT
    -- the `Pickles.Types.PointEval` newtype — they share the name but
    -- the record-based one is what `Pickles.PlonkChecks.AllEvals`
    -- uses internally.
    wrapPE :: LFFI.PointEval StepField -> LFFI.PointEval (F StepField)
    wrapPE pe = { zeta: F pe.zeta, omegaTimesZeta: F pe.omegaTimesZeta }

    wrapAE :: AllEvals StepField -> AllEvals (F StepField)
    wrapAE ae =
      { ftEval1: F ae.ftEval1
      , publicEvals: wrapPE ae.publicEvals
      , zEvals: wrapPE ae.zEvals
      , indexEvals: map wrapPE ae.indexEvals
      , witnessEvals: map wrapPE ae.witnessEvals
      , coeffEvals: map wrapPE ae.coeffEvals
      , sigmaEvals: map wrapPE ae.sigmaEvals
      }

    dummyProofWitness :: ProofWitness (F StepField)
    dummyProofWitness = { allEvals: wrapAE r.stepDummyPrevEvals }

    -- Ro-derived FOP proof state for the dummy wrap proof.
    dummyFopProofState
      :: UnfinalizedProof StepIPARounds (F StepField) (Type1 (F StepField)) Boolean
    dummyFopProofState = stepDummyFopProofState
      { proofsVerified: input.mostRecentWidth }

    -- Cross-field conversion of `wrapDummyUnfinalizedProof` (which
    -- is in wrap-field `Type2 (F WrapField)`) to the step-field
    -- `Type2 (SplitField (F StepField) Boolean)` that step_main's
    -- `publicInputCommit` walks over. Same two-step bridge the old
    -- `dummyStepAdvice` used in Pickles.Dummy before its deletion.
    du = wrapDummyUnfinalizedProof

    t2toT2sf :: Type2 (F WrapField) -> Type2 (SplitField (F StepField) Boolean)
    t2toT2sf t = toShifted (fromShifted t :: F WrapField)

    chalToStep :: SizedF 128 (F WrapField) -> SizedF 128 (F StepField)
    chalToStep s = SizedF.wrapF (coerceViaBits (SizedF.unwrapF s))

    digestStep :: F StepField
    digestStep =
      let F digestWrap = du.spongeDigestBeforeEvaluations
      in F (Curves.fromBigInt (Curves.toBigInt digestWrap) :: StepField)

    dv = du.deferredValues
    p = dv.plonk

    dummyPublicUnfinalized
      :: PerProofUnfinalized
           WrapIPARounds
           (Type2 (SplitField (F StepField) Boolean))
           (F StepField)
           Boolean
    dummyPublicUnfinalized = PerProofUnfinalized
      { combinedInnerProduct: t2toT2sf dv.combinedInnerProduct
      , b: t2toT2sf dv.b
      , zetaToSrsLength: t2toT2sf p.zetaToSrsLength
      , zetaToDomainSize: t2toT2sf p.zetaToDomainSize
      , perm: t2toT2sf p.perm
      , spongeDigest: digestStep
      , beta: UnChecked (chalToStep p.beta)
      , gamma: UnChecked (chalToStep p.gamma)
      , alpha: UnChecked (chalToStep p.alpha)
      , zeta: UnChecked (chalToStep p.zeta)
      , xi: UnChecked (chalToStep dv.xi)
      , bulletproofChallenges: map (UnChecked <<< chalToStep) dv.bulletproofChallenges
      , shouldFinalize: false
      }

    -- Per-slot branch data. All slots get the same entry for the
    -- base case (single-rule compile). `domainLog2` is the wrap
    -- proof's evaluation domain (OCaml `Proof.dummy`'s
    -- `~domain_log2` parameter, stored in the dummy proof's
    -- statement at `proof.ml:140-141`). mask0/mask1 encode which
    -- prev-proof slot is the active one — for Simple_chain at N1
    -- the single slot is `mask1 = true, mask0 = false`.
    dummyBranch :: StepBranchData
    dummyBranch =
      { domainLog2: F (Curves.fromInt input.wrapDomainLog2 :: StepField)
      , mask0: false
      , mask1: true
      }
  in
    { stepInputFields: []
    , evals: Vector.replicate dummyProofWitness
    , prevChallenges: Vector.replicate (map F dummyIpaChallenges.stepExpanded)
    , messages: Vector.replicate
        { wComm: Vector.generate (\_ -> g0)
        , zComm: g0
        , tComm: Vector.generate (\_ -> g0)
        }
    , openingProofs: Vector.replicate
        { delta: g0
        , sg: g0
        , lr: Vector.generate (\_ -> { l: g0, r: g0 })
        , z1
        , z2
        }
    , fopProofStates: Vector.replicate dummyFopProofState
    , messagesForNextWrapProof: Vector.replicate (F zero)
    , wrapVerifierIndex:
        VerificationKey
          { sigma: Vector.generate (const g0w)
          , coeff: Vector.generate (const g0w)
          , index: Vector.generate (const g0w)
          }
    , sgOld: Vector.replicate g0
    , appState: input.appState
    , publicUnfinalizedProofs: Vector.replicate dummyPublicUnfinalized
    , branchData: Vector.replicate dummyBranch
    }

--------------------------------------------------------------------------------
-- stepProve — compile + solve + kimchi proof creation
--------------------------------------------------------------------------------

-- | Rule type the step prover accepts. This is the inductive-rule
-- | body `stepMain` passes to `verifyOne` for each previous proof.
-- |
-- | The type is polymorphic in both `t` and the base monad `m'` so
-- | that `stepProve` can reuse the same rule for compile-time (circuit
-- | shape walk, `m' = Effect`) and solve-time (witness generation,
-- | `m' = StepProverT n ...`).
-- |
-- | Mirrors OCaml's `Inductive_rule.main` signature at
-- | `mina/src/lib/crypto/pickles/inductive_rule.ml` + the usage site
-- | in `step_main.ml:278-283`.
type StepRule (n :: Int) =
  forall t m'
   . CircuitM StepField (KimchiConstraint StepField) t m'
  => StepWitnessM n StepIPARounds WrapIPARounds PallasG StepField m'
  => FVar StepField
  -> Snarky (KimchiConstraint StepField) t m' (RuleOutput n StepField)

-- | Ambient data the step prover needs alongside the advice and rule.
-- |
-- | * `srsData` — `StepMainSrsData` that `stepMain` consumes as a
-- |   compile-time parameter (lagrange-base lookup, blinding H,
-- |   fop domain log2).
-- | * `dummySg` — dummy sg point for sg_old padding in verify_one.
-- | * `crs` — the step circuit's Vesta SRS.
type StepProveContext =
  { srsData :: StepMainSrsData
  , dummySg :: AffinePoint StepField
  , crs :: CRS VestaG
  }

-- | Artifacts produced by `stepProve`. Shape mirrors
-- | `WrapProveResult` so downstream code can retarget with minimal
-- | glue.
type StepProveResult (outputSize :: Int) =
  { proverIndex :: ProverIndex VestaG StepField
  , verifierIndex :: VerifierIndex VestaG StepField
  , constraintSystem :: ConstraintSystem StepField
  , witness :: Vector 15 (Array StepField)
  , publicInputs :: Array StepField
  , publicOutputs :: Vector outputSize (F StepField)
  , proof :: Proof VestaG StepField
  , assignments :: Map Variable StepField
  }

-- | Run the step prover end-to-end: compile stepMain against the
-- | given inductive rule, run the witness solver with the supplied
-- | advice, check constraint satisfaction, and create the kimchi
-- | proof.
-- |
-- | Mirrors `Pickles.Prove.Wrap.wrapProve` exactly — same monad
-- | polymorphism, same `onError` parameter for solver failures,
-- | same compile/solve/proof shape.
-- |
-- | The type parameters `@n` and `@outputSize` are the two the caller
-- | pins at the call site; `@pad`, `@unfsTotal`, `@digestPlusUnfs`
-- | are derived via `Add`/`Mul` constraints (the same stepMain uses).
-- |
-- | Reference:
-- |   `mina/src/lib/crypto/pickles/step.ml:800-852` — OCaml step prover
-- |   `mina/src/lib/crypto/pickles/step_main.ml:237-594` — the circuit body
stepProve
  :: forall @n @outputSize pad unfsTotal digestPlusUnfs m
   . CircuitGateConstructor StepField VestaG
  => Reflectable n Int
  => Reflectable pad Int
  => Reflectable outputSize Int
  => Add pad n PaddedLength
  => Mul n 32 unfsTotal
  => Add unfsTotal 1 digestPlusUnfs
  => Add digestPlusUnfs n outputSize
  => Monad m
  => (Error -> m (StepProveResult outputSize))
  -> StepProveContext
  -> StepRule n
  -> StepAdvice n StepIPARounds WrapIPARounds
  -> m (StepProveResult outputSize)
stepProve onError ctx rule advice = do
  -- ===== compile =====
  let
    compileAction
      :: StepProverT n StepIPARounds WrapIPARounds m
           (CircuitBuilderState (KimchiGate StepField) (AuxState StepField))
    compileAction =
      compile
        (Proxy @Unit)
        (Proxy @(Vector outputSize (F StepField)))
        (Proxy @(KimchiConstraint StepField))
        (\_ -> stepMain @n @outputSize rule ctx.srsData ctx.dummySg)
        (Kimchi.initialState :: CircuitBuilderState (KimchiGate StepField) (AuxState StepField))

  builtState <- runStepProverT advice compileAction

  let
    kimchiRows = concatMap (toKimchiRows <<< _.constraint) builtState.constraints
    { constraintSystem, constraints } = makeConstraintSystem @StepField
      { constraints: kimchiRows
      , publicInputs: builtState.publicInputs
      , unionFind: (un AuxState builtState.aux).wireState.unionFind
      }

  -- ===== solve (populates assignments via the StepWitnessM advice methods) =====
  let
    rawSolver
      :: SolverT StepField (KimchiConstraint StepField)
           (StepProverT n StepIPARounds WrapIPARounds m)
           Unit
           (Vector outputSize (F StepField))
    rawSolver =
      makeSolver' (emptyProverState { debug = true }) (Proxy @(KimchiConstraint StepField))
        (\_ -> stepMain @n @outputSize rule ctx.srsData ctx.dummySg)

  eRes <- runStepProverT advice (runSolverT rawSolver unit)

  case eRes of
    Left e -> onError (error ("stepProve solver: " <> show e))
    Right (Tuple publicOutputs assignments) ->
      let
        { witness, publicInputs } = makeWitness
          { assignments
          , constraints: map _.variables constraints
          , publicInputs: builtState.publicInputs
          }

        -- Production endo choice (see Pickles.Prove.Wrap for the
        -- memory note on why endoScalar is the right choice for
        -- verifiable proofs, not endoBase).
        endo :: StepField
        endo =
          let EndoScalar e = (endoScalar :: EndoScalar StepField) in e

        proverIndex =
          createProverIndex @StepField @VestaG
            { endo, constraintSystem, crs: ctx.crs }

        verifierIndex = createVerifierIndex @StepField @VestaG proverIndex
        csSatisfied = verifyProverIndex @StepField @VestaG
          { proverIndex, witness, publicInputs }
      in
        if not csSatisfied then
          onError (error "stepProve: constraint system not satisfied")
        else
          let proof = createProof { proverIndex, witness }
          in pure
            { proverIndex
            , verifierIndex
            , constraintSystem
            , witness
            , publicInputs
            , publicOutputs
            , proof
            , assignments
            }
