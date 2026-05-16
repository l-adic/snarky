-- | PureScript-side analog of OCaml's `chunks2` base-case (b0) test
-- | (`mina/src/lib/crypto/pickles/test/chunked_circuits/chunks2.ml:9-56`).
-- |
-- | Single N=0 rule whose body fills 2^16 rows with `mul_ (fresh_zero)
-- | (fresh_zero)` plus one 7-wire Raw Generic gate; declared with
-- | `num_chunks = 2` and `wrap_domain_override = N1` so kimchi's PCS
-- | runs at num_chunks=2 (max_poly_size = 2^16, domain = 2^17). The
-- | proof creation triggers a step and a wrap kimchi prover invocation
-- | — counters 0 and 1 in `KIMCHI_WITNESS_DUMP` — so the witness can
-- | be diffed against `dump_chunks2.exe` byte-for-byte.
module Test.Pickles.Prove.Chunks2
  ( Chunks2Rules
  , chunks2Rule
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

-- | The chunks2 leaf rule body: 2^17 + 1 `mul_ (fresh_zero) (fresh_zero)`
-- | fillers (each R1CS = half a kimchi row, so we get 2^16 + 1 rows)
-- | followed by a 7-wire Raw Generic with zero coeffs (forces the 7th
-- | permuted column's polynomial degree above 2^16). Mirrors the
-- | `main` field of the OCaml `chunks2.ml` choice at lines 18-48.
chunks2Rule :: StepRule 0 Unit Unit Unit Unit Unit Unit Unit
chunks2Rule _ = do
  let
    freshZero = exists (pure (zero :: F StepField))
    iters = (1 `Bits.shl` 17) + 1
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

-- | Single-rule carrier for chunks2: one `RulesCons` for the leaf rule,
-- | terminated by `RulesNil`. Same shape as NRR (N=0, no prevs).
type Chunks2Rules =
  RulesCons 0 Unit Unit Unit
    RulesNil

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.Chunks2" do
  it "base case (b0) — chunks=2 step+wrap proves end-to-end" \_ -> do
    -- Step kimchi uses `vestaSrs` (depth 2^16 by default cache load).
    -- With chunks2's 2^16-row step circuit, the step domain rounds to
    -- 2^17 → num_chunks = 2 (= 2^17 / 2^16). Wrap kimchi uses
    -- `pallasSrs` at depth 2^15 — matches OCaml's Tock URS
    -- (`Backend.Tock.Keypair.load_urs ()` at `Tock.Rounds.n = N15`,
    -- `kimchi_pasta_basic.ml:6`). Wrap domain is 2^14 (override) so
    -- num_chunks at wrap = 1; the smaller SRS gives the correct
    -- max_poly_size = 32768 byte-for-byte with OCaml.
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Bits.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    -- @nc=1 is a placeholder for the side-loaded-slot chunks count
    -- (no side-loaded slots here; nc is irrelevant but must be pinned
    -- for `Reflectable nc Int` to resolve at module-load time).
    chunks2Entry <- liftEffect $ mkRuleEntry @0 @Unit @Unit @1 @1 chunks2Rule unit
    let rules = tuple1 chunks2Entry

    output <- liftEffect $ compileMulti
      @Chunks2Rules
      @Unit
      @Unit
      @NoSlots
      @2
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      -- N1 wrap_domain override (= log2 14), matching chunks2.ml's
      -- `~override_wrap_domain:N1`.
      , wrapDomainOverride: Just 14
      }
      rules

    let BranchProver chunks2Prover = fst output.provers
    eResult <- liftEffect $ runExceptT $ chunks2Prover
      { appInput: unit, prevs: unit, sideloadedVKs: unit }
    case eResult of
      Left e -> liftEffect $ Exc.throw ("chunks2Prover: " <> show e)
      Right compiledProof ->
        verify output.verifier [ compiledProof ] `shouldEqual` true
