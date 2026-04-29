module Pickles.CircuitDiffs.PureScript.StepMainTreeProofReturn
  ( compileStepMainTreeProofReturn
  , StepMainTreeProofReturnParams
  , class TreeProofReturnAdvice
  , getTreeProofReturnIsBaseCase
  , getTreeProofReturnNoRecursiveInput
  , getTreeProofReturnPrev
  ) where

-- | step_main circuit for the Tree_proof_return rule.
-- |
-- | **N = 2**, **Output mode**, **heterogeneous prevs** at the rule
-- | level but homogeneous at the value-type level: both prev
-- | `public_input` slots are `Field.typ` even though the first prev's
-- | rule has `max_proofs_verified = N0` (No_recursion_return) and the
-- | second is `self` with `max_proofs_verified = N2`. Our
-- | `Vector n (FVar StepField)` `prevPublicInputs` field handles this
-- | shape without needing an HList.
-- |
-- | Rule body computes `self = if is_base_case then 0 else 1 + prev`
-- | and exposes it as `publicOutput`. This exercises the Output-mode
-- | `hashAppFields = varToFields input <> varToFields output` path
-- | where `input = Unit` (contributes `[]`) and `output = FVar StepField`
-- | (contributes `[self]`) — matching OCaml step_main.ml:566-573's
-- | `Output _ -> ret_var` branch.
-- |
-- | Reference: mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:315-392
-- |            (Tree_proof_return).
-- | OCaml dump target: `step_main_tree_proof_return_circuit.json`
-- |            produced by `mina/src/lib/crypto/pickles/dump_circuit_impl.ml`.

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Maybe (Maybe(..), fromJust)
import Data.Vector (Vector, (:<))
import Data.Tuple (Tuple)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Exception (throw)
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyWrapSg)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Step.Main (RuleOutput, stepMain)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Types (StatementIO, StepField, VerificationKey(..))
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, Snarky, const_, exists, if_, not_)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class as Curves
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))

-- | Tree_proof_return has HETEROGENEOUS prev wrap_domains (slot 0: 2^13
-- | from No_recursion_return; slot 1: 2^14 from self @
-- | override_wrap_domain:N1). Each slot needs its own lagrange lookup
-- | keyed on the slot's domain size.
type StepMainTreeProofReturnParams =
  { perSlotLagrangeAt :: Vector 2 (LagrangeBaseLookup StepField)
  , blindingH :: AffinePoint (F StepField)
  }

-- | Application-specific advice for the Tree_proof_return rule.
-- |
-- | Three requests from the OCaml test fixture:
-- | * `Is_base_case` — boolean controlling the base-vs-inductive branch.
-- | * `No_recursion_input` — the prev[0] public_input value (the
-- |   No_recursion_return proof's output field).
-- | * `Recursive_input` — the prev[1] public_input value (the parent
-- |   Tree_proof_return proof's output field).
-- |
-- | The proof witnesses themselves are tracked abstractly via the step
-- | advice monad; this class only supplies the field / boolean values
-- | the rule's `exists` calls request.
class Monad m <= TreeProofReturnAdvice m where
  getTreeProofReturnIsBaseCase :: Unit -> m Boolean
  getTreeProofReturnNoRecursiveInput :: Unit -> m (F StepField)
  getTreeProofReturnPrev :: Unit -> m (F StepField)

-- | Compilation instance: throws if evaluated. `exists` discards the
-- | AsProverT during circuit shape walks, so the throw never fires.
instance TreeProofReturnAdvice Effect where
  getTreeProofReturnIsBaseCase _ =
    throw "TreeProofReturnAdvice.getTreeProofReturnIsBaseCase: not available during compilation"
  getTreeProofReturnNoRecursiveInput _ =
    throw "TreeProofReturnAdvice.getTreeProofReturnNoRecursiveInput: not available during compilation"
  getTreeProofReturnPrev _ =
    throw "TreeProofReturnAdvice.getTreeProofReturnPrev: not available during compilation"

-- | Tree_proof_return rule:
-- |   `self = if is_base_case then 0 else 1 + prev`
-- |   prev[0].public_input = no_recursive_input (always verified)
-- |   prev[1].public_input = prev (verified unless base case)
-- |   public_output = self
-- |
-- | Reference: test_no_sideloaded.ml:354-390
treeProofReturnRule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => TreeProofReturnAdvice m
  => Unit
  -> Snarky (KimchiConstraint StepField) t m
       (RuleOutput 2 (FVar StepField) (FVar StepField))
treeProofReturnRule _ = do
  no_recursive_input <- exists $ lift $ getTreeProofReturnNoRecursiveInput unit
  prev <- exists $ lift $ getTreeProofReturnPrev unit
  (is_base_case :: BoolVar StepField) <- exists $ lift $
    getTreeProofReturnIsBaseCase unit
  let proofMustVerify = not_ is_base_case
  self <- if_ is_base_case (const_ zero) (CVar.add_ (const_ one) prev)
  pure
    { prevPublicInputs: no_recursive_input :< prev :< Vector.nil
    -- prev[0] always verifies (Boolean.true_ in OCaml);
    -- prev[1] verifies iff not base case.
    , proofMustVerify:
        (coerce (const_ one :: FVar StepField) :: BoolVar StepField)
          :< proofMustVerify
          :< Vector.nil
    , publicOutput: self
    }

compileStepMainTreeProofReturn
  :: StepMainTreeProofReturnParams -> Effect (CompiledCircuit StepField)
compileStepMainTreeProofReturn params =
  compile (Proxy @Unit) (Proxy @(Vector 67 (F StepField))) (Proxy @(KimchiConstraint StepField))
    -- N=2, output size = 33*2 + 1 = 67 (two unfinalized proofs + digest
    -- + two msg_wrap entries). Wrap domain log2 = 14 from
    -- `override_wrap_domain:N1` (common.ml:25-29).
    -- Self: input=Unit (Output mode), output=Field. Prevs: both
    -- public_input slots are Field (prev[0]=No_recursion_return's
    -- output, prev[1]=self's output), so prevInputVal=F StepField.
    -- Heterogeneous spec: slot 0 is No_recursion_return (n=0), slot 1 is
    -- self (n=2). With stepMain's spec-indexed carrier, slot 0's SPPW
    -- has empty prev_challenges / prev_sgs (correctly reflecting that a
    -- N=0 prev verified zero prior proofs). The v1 path over-allocated
    -- slot 0 to size 2, producing ~4 extra on-curve-check rows vs OCaml.
    -- Per-slot FOP domain_log2 — `finalize_other_proof ~step_domains`
    -- uses the prev's STEP_DOMAINS (NOT wrap_domains):
    -- * slot 0: no_rec_data.step_domains[0].h = 2^13
    --   (dump_circuit_impl.ml:3902-3906).
    -- * slot 1: self's step_domains[0].h = 2^16
    --   (dump_circuit_impl.ml:3974). Note: self's wrap_domains.h is
    --   2^14 (override_wrap_domain:N1), but that's used for the IVP
    --   lagrange lookup, not the FOP domain.
    --
    -- Per-slot known wrap keys:
    -- * slot 0: Just noRecKnownWrapKey — matches OCaml's
    --   `Some no_rec_known` in dump_circuit_impl.ml:4017. The VK's
    --   commitments are all `Pallas.generator` (placeholder; OCaml
    --   uses `Tick.Inner_curve.one` at dump_circuit_impl.ml:3999-4009).
    -- * slot 1: Nothing — slot's prev is SELF, uses the shared
    --   `exists`-allocated VK inside stepMain.
    -- Single-rule: mpvMax = len = 2, mpvPad = 0.
    ( \_ -> stepMain
        @( PrevsSpecCons 0 (StatementIO Unit (F StepField))
            (PrevsSpecCons 2 (StatementIO Unit (F StepField)) PrevsSpecNil)
        )
        @67
        @Unit
        @Unit
        @(F StepField)
        @(FVar StepField)
        @(F StepField)
        @(FVar StepField)
        @( Tuple (StatementIO Unit (F StepField))
             (Tuple (StatementIO Unit (F StepField)) Unit)
         )
        @2
        @0
        treeProofReturnRule
        { perSlotLagrangeAt: params.perSlotLagrangeAt
        , blindingH: params.blindingH
        , perSlotFopDomainLog2: 13 :< 16 :< Vector.nil
        , perSlotKnownWrapKeys: Just noRecKnownWrapKey :< Nothing :< Vector.nil
        -- Phase 2b.31a: thunks for mpvMax-padding dummies. Single-rule
        -- callers have mpvPad=0 so `mpvFrontPad` short-circuits and the
        -- thunks never fire — `unsafeCrashWith` is fine.
        , dummyUnfp: \_ -> unsafeCrashWith "dummyUnfp: unused at mpvPad=0"
        , dummyMsgWrapHash: \_ -> unsafeCrashWith "dummyMsgWrapHash: unused at mpvPad=0"
        }
        dummyWrapSg
    )
    Kimchi.initialState

-- | Placeholder wrap VK for slot 0's No_recursion_return prev.
-- |
-- | OCaml (dump_circuit_impl.ml:3999-4010) fills the
-- | `Optional_wrap_key.known.wrap_key` with `Tick.Inner_curve.one`
-- | (Pallas generator) in all 28 commitment slots — not a real VK, just
-- | a constant placeholder. We do the same here so the compiled circuit
-- | has the same compile-time constants as the OCaml fixture.
noRecKnownWrapKey
  :: VerificationKey (WeierstrassAffinePoint PallasG (F StepField))
noRecKnownWrapKey =
  let
    g :: AffinePoint StepField
    g = unsafePartial $ fromJust $ Curves.toAffine (Curves.generator :: Pallas.G)

    pt :: WeierstrassAffinePoint PallasG (F StepField)
    pt = WeierstrassAffinePoint { x: F g.x, y: F g.y }
  in
    VerificationKey
      { sigma: Vector.generate (const pt)
      , coeff: Vector.generate (const pt)
      , index: Vector.generate (const pt)
      }
