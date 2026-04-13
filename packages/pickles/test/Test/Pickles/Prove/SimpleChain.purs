-- | PureScript-side analog of OCaml's `Simple_chain` test
-- | (`mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:128-205` +
-- |  `mina/src/lib/crypto/pickles/dump_simple_chain/dump_simple_chain.ml`).
-- |
-- | Runs the exact same inductive rule (`prev + 1`) at
-- | `max_proofs_verified = N1`, base case only (self = 0), through
-- | the generic `Pickles.Prove.Step.stepProve` orchestrator. The trace
-- | file PureScript emits is diffed byte-for-byte against the OCaml
-- | fixture at `packages/pickles/test/fixtures/simple_chain_base_case.trace`
-- | via `tools/simple_chain_trace_diff.sh`.
-- |
-- | This file is the top-level binding for the Simple_chain test —
-- | the ONLY place concrete `n=1` + `stepDomainLog2=16` +
-- | `wrapDomainLog2=14` + `mostRecentWidth=1` appear. Everything
-- | downstream (`Pickles.Prove.Step`, `Pickles.Step.Main`,
-- | `Pickles.Types`) stays polymorphic in `n`, `ds`, `dw`; type
-- | inference unifies them against `stepMain`'s
-- | `StepWitnessM n StepIPARounds WrapIPARounds ...` constraint when
-- | `stepProve` is invoked here.
-- |
-- | Required env vars at runtime:
-- | - `PICKLES_TRACE_FILE` — path to the trace log (truncated).
-- | - `KIMCHI_DETERMINISTIC_SEED` — u64 seed for the patched kimchi RNG.
module Test.Pickles.Prove.SimpleChain
  ( spec
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Tuple (Tuple(..))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles.Prove.Step (StepRule, buildStepAdvice, stepProve)
import Pickles.ProofFFI (vestaSrsBlindingGenerator, vestaSrsLagrangeCommitmentAt) as ProofFFI
import Pickles.PublicInputCommit (mkConstLagrangeBaseLookup)
import Pickles.Trace as Trace
import Pickles.Types (StepField)
import Safe.Coerce (coerce)
import Snarky.Curves.Class (fromInt) as Curves
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F(..), assertAny_, const_, equals_, exists, not_)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Spec (SpecT, describe, it)
import Control.Monad.Trans.Class (lift) as MT

-- | PureScript translation of the Simple_chain inductive rule, verbatim
-- | from OCaml `dump_simple_chain.ml:62-82` (which itself is verbatim
-- | from `test_no_sideloaded.ml:149-172`):
-- |
-- |     main = fun { public_input = self } ->
-- |       let prev = exists Field.typ ~request:Prev_input in
-- |       let proof = exists (Typ.prover_value ()) ~request:Proof in
-- |       let is_base_case = Field.equal Field.zero self in
-- |       let proof_must_verify = Boolean.not is_base_case in
-- |       let self_correct = Field.(equal (one + prev) self) in
-- |       Boolean.Assert.any [ self_correct; is_base_case ] ;
-- |       { previous_proof_statements = [ { public_input = prev; proof; proof_must_verify } ]
-- |       ; public_output = ()
-- |       ; auxiliary_output = ()
-- |       }
-- |
-- | For the base case (self = 0), `is_base_case` is true so the
-- | assertion passes regardless of `prev`. OCaml's handler supplies
-- | `-1` via `Req.Prev_input`; PureScript can use `0` (the value
-- | doesn't affect the circuit output when `is_base_case = true`).
simpleChainRule :: StepRule 1
simpleChainRule self = do
  prev <- exists $ MT.lift $ pure (F zero :: F StepField)
  isBaseCase <- equals_ (const_ zero) self
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) self
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev :< Vector.nil
    , proofMustVerify: proofMustVerify :< Vector.nil
    }

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.SimpleChain" do
  it "base case trace matches OCaml fixture" \_ -> do
    -- Mirror OCaml dump_simple_chain.ml's begin sentinel.
    liftEffect $ Trace.string "simple_chain.begin" "base_case"

    -- ===== SRS + context setup =====
    -- OCaml's Simple_chain loads the Pallas (wrap-side) SRS for the
    -- lagrange basis lookup and the Vesta (step-side) SRS for the
    -- actual step proof creation. Mirror that here.
    lagrangeSrs <- liftEffect PallasImpl.createCRS
    proofCrs <- liftEffect $ createCRS @StepField

    let
      -- OCaml `basic.wrap_domains.h` for N1, from
      -- `dump_circuit_impl.ml:3718-3719`:
      --   { Import.Domains.h = Pow_2_roots_of_unity 14 }
      -- This is the WRAP proof's evaluation domain. It drives THREE
      -- call sites that all need to agree for the step FOP's
      -- domain-masking check (`finalizeOtherProofCircuit:213-214`'s
      -- `equals_ params.domainLog2 domainLog2Var`) to produce a
      -- non-zero `maskedGen`:
      --
      --   1. `srsData.fopDomainLog2 = 14` — the step circuit's
      --      knowledge of the wrap proof's domain, passed to
      --      stepMain as a compile-time constant.
      --
      --   2. `buildStepAdviceInput.wrapDomainLog2 = 14` — the dummy
      --      wrap proof's own `~domain_log2` parameter, which
      --      becomes `branch_data.domain_log2 = 14` in the dummy's
      --      statement (OCaml `proof.ml:140-141`).
      --
      --   3. `stepDummyFopProofState.domainLog2 = wrap_domains.h
      --      = 14` via `wrapDomainLog2ForProofsVerified 1` — the
      --      dummy FOP proof state's declared wrap-domain.
      --
      -- All three resolve to `wrap_domains ~proofs_verified:1 = 14`
      -- in OCaml `common.ml:25-29`. The STEP circuit's own kimchi
      -- domain log2 (= 16 for Simple_chain per
      -- `dump_circuit_impl.ml:3721-3723`) is a different concept
      -- entirely — decided by kimchi at proof creation, not read
      -- from advice.
      wrapDomainLog2 = 14

      srsData =
        { lagrangeAt:
            mkConstLagrangeBaseLookup \i ->
              (coerce (ProofFFI.vestaSrsLagrangeCommitmentAt lagrangeSrs wrapDomainLog2 i))
                :: AffinePoint (F StepField)
        , blindingH: (coerce $ ProofFFI.vestaSrsBlindingGenerator lagrangeSrs)
            :: AffinePoint (F StepField)
        , fopDomainLog2: wrapDomainLog2
        }

      dummySg :: AffinePoint StepField
      dummySg = { x: zero, y: zero }

      ctx =
        { srsData
        , dummySg
        , crs: proofCrs
        }

      -- Simple_chain's base-case advice. Everything except the four
      -- caller-supplied fields is filled with Ro-derived dummies by
      -- `buildStepAdvice`. Type inference pins the advice to
      -- `StepAdvice 1 StepIPARounds WrapIPARounds` via `stepProve`'s
      -- downstream constraint — this file never writes the
      -- round-count constants literally.
      advice = buildStepAdvice
        { appState: F zero
        , mostRecentWidth: 1
        , wrapDomainLog2
        }

    -- ===== Run the step prover =====
    result <- liftEffect $
      stepProve @1 @34
        (\e -> Exc.throw ("stepProve: " <> show e))
        ctx
        simpleChainRule
        advice

    -- ===== Trace the public input array =====
    -- Mirrors mina/src/lib/crypto/pickles/step.ml:828-833 which
    -- iterates over `Backend.Tick.Field.Vector.length public_inputs`
    -- and emits `step.proof.public_input.{i}` per element.
    liftEffect $ for_ (Array.mapWithIndex Tuple result.publicInputs) \(Tuple i x) ->
      Trace.field ("step.proof.public_input." <> show i) x

    liftEffect $ Trace.string "simple_chain.end" "base_case_verified"
