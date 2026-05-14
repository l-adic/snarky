-- | PureScript-side analog of OCaml's `chunks4` base-case (b0) test
-- | (`mina/src/lib/crypto/pickles/test/chunked_circuits/chunks4.ml`).
-- |
-- | Single N=0 rule whose body fills 2^17 rows with `mul_ (fresh_zero)
-- | (fresh_zero)` plus one 7-wire Raw Generic gate; declared with
-- | `num_chunks = 4` and `wrap_domain_override = N1` so kimchi's PCS
-- | runs at step num_chunks=4 (max_poly_size = 2^16, domain = 2^18).
-- | The proof creation triggers a step and a wrap kimchi prover
-- | invocation — counters 0 and 1 in `KIMCHI_WITNESS_DUMP` — so the
-- | witness can be diffed against `dump_chunks4.exe` byte-for-byte.
module Test.Pickles.Prove.Chunks4
  ( Chunks4Rules
  , chunks4Rule
  , spec
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Control.Monad.Rec.Class (Step(..), tailRecM)
import Data.Either (Either(..))
import Data.Int.Bits as Bits
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (tuple1)
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles (BranchProver(..), NoSlots, RulesCons, RulesNil, StepField, StepRule, compileMulti, mkRuleEntry, verify)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F, addConstraint, exists, mul_)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | The chunks4 leaf rule body: 2^18 + 1 `mul_ (fresh_zero) (fresh_zero)`
-- | fillers (each R1CS = half a kimchi row, so we get 2^17 + 1 rows)
-- | followed by a 7-wire Raw Generic with zero coeffs (forces the 7th
-- | permuted column's polynomial degree above 2^17). Mirrors the
-- | `main` field of the OCaml `chunks4.ml` choice.
chunks4Rule :: StepRule 0 Unit Unit Unit Unit Unit Unit Unit
chunks4Rule _ = do
  let
    freshZero = exists (pure (zero :: F StepField))
    iters = (1 `Bits.shl` 18) + 1
    mulOne = do
      z1 <- freshZero
      z2 <- freshZero
      _ <- mul_ z1 z2
      pure unit
  tailRecM
    ( \i ->
        if i >= iters then pure (Done unit)
        else mulOne *> pure (Loop (i + 1))
    )
    0
  z <- freshZero
  addConstraint $ KimchiRawGeneric7
    (z :< z :< z :< z :< z :< z :< z :< Vector.nil)
  pure
    { prevPublicInputs: Vector.nil
    , proofMustVerify: Vector.nil
    , publicOutput: unit
    }

-- | Single-rule carrier for chunks4: one `RulesCons` for the leaf rule,
-- | terminated by `RulesNil`. Same shape as chunks2/NRR (N=0, no prevs).
type Chunks4Rules =
  RulesCons 0 Unit Unit Unit
    RulesNil

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.Chunks4" do
  it "base case (b0) — chunks=4 step+wrap proves end-to-end" \_ -> do
    -- Step kimchi uses `vestaSrs` (depth 2^16 via cache load). With
    -- chunks4's 2^17-row step circuit, the step domain rounds to
    -- 2^18 → num_chunks = 4 (= 2^18 / 2^16). Wrap kimchi uses
    -- `pallasSrs` at depth 2^15 — matches OCaml's Tock URS
    -- (`Backend.Tock.Keypair.load_urs ()` at `Tock.Rounds.n = N15`,
    -- `kimchi_pasta_basic.ml:6`). Wrap domain is 2^14 (override) so
    -- num_chunks at wrap = 1.
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Bits.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    -- @nc=1 placeholder for side-loaded-slot chunks count
    -- (no side-loaded slots here).
    chunks4Entry <- liftEffect $ mkRuleEntry @0 @Unit @Unit @1 chunks4Rule unit
    let rules = tuple1 chunks4Entry

    output <- liftEffect $ compileMulti
      @Chunks4Rules
      @Unit
      @Unit
      @NoSlots
      @4
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Just 14
      }
      rules

    let BranchProver chunks4Prover = fst output.provers
    eResult <- liftEffect $ runExceptT $ chunks4Prover
      { appInput: unit, prevs: unit, sideloadedVKs: unit }
    case eResult of
      Left e -> liftEffect $ Exc.throw ("chunks4Prover: " <> show e)
      Right compiledProof ->
        verify output.verifier [ compiledProof ] `shouldEqual` true
