-- | Shared definitions for the pickles benchmark suite: the example
-- | circuit (an N=2 `Tree_proof_return`-shaped rule + its NRR base),
-- | the workload-tuning constants, and the *shared, pre-warmed* SRS.
-- |
-- | `mkBenchSrs` creates ONE SRS pair and pre-warms the lagrange-basis
-- | cache for the domains the workload touches. The cache lives inside
-- | the SRS object (Rust interior mutability), so threading this same
-- | record into every group means SRS construction + lagrange-basis
-- | computation happen once, untimed, and are excluded from every
-- | bench's measured region. See `Bench.Pickles.Main`.
module Bench.Pickles.Common
  ( BenchSrs
  , mkBenchSrs
  , fillerIters
  , benchIterations
  , TreeProofReturnPrevsSpec
  , NrrRules
  , TreeRules
  , benchTreeRule
  , nrrRule
  ) where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRecM)
import Data.Foldable (for_)
import Data.Int.Bits as Bits
import Data.Tuple.Nested (Tuple2, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles (Compiled, RulesCons, RulesNil, Slot, SlotWrapKey, StatementIO(..), StepField, StepRule)
import Snarky.Backend.Kimchi.Impl.Pallas as P
import Snarky.Backend.Kimchi.Impl.Vesta as V
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, const_, exists, if_, mul_, not_, true_)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Lagrange.Cache (pallasOps, vestaOps, warmer)
import Snarky.Lagrange.Cache.FS (defaultDir, fsCache)

-- | The shared SRS pair threaded through every bench group. Field types
-- | match `compileMulti`'s `srs` config exactly.
type BenchSrs = { vestaSrs :: CRS VestaG, pallasSrs :: CRS PallasG }

-- | Create the SRS pair once and pre-warm the lagrange-basis cache so
-- | neither SRS construction nor `get_lagrange_basis` lands in any
-- | timed region. Domains warmed:
-- |   * Vesta / Fp (step): tree step domain = 2^16; NRR step is smaller.
-- |   * Pallas / Fq (wrap): tree wrap = 2^14 (override); NRR wrap +
-- |     internal commitments up to 2^15 (the Tock URS depth).
-- | Warming a domain that is never queried is harmless — the goal is
-- | simply to move *all* lagrange work ahead of the benchmarks.
mkBenchSrs :: Effect BenchSrs
mkBenchSrs = do
  -- Build the SRS directly, then PRE-WARM the Lagrange bases here (untimed,
  -- before any bench), through the on-disk cache: a cold run FFTs + stores each
  -- basis; later runs inject them. The bench compile configs use `Nothing`, so
  -- no warming lands in a timed region. (Bench deliberately keeps this pre-warm
  -- rather than the lazy compile-time warm, to exclude it from the measurement.)
  cache <- fsCache <$> defaultDir
  let
    vestaSrs = V.vestaCrsCreate (1 `Bits.shl` 16)
    pallasSrs = P.pallasCrsCreate (1 `Bits.shl` 15)
  warmV <- warmer cache vestaOps vestaSrs
  for_ [ 13, 14, 15, 16 ] warmV
  warmP <- warmer cache pallasOps pallasSrs
  for_ [ 13, 14, 15 ] warmP
  pure { vestaSrs, pallasSrs }

-- | Per-call `mul_ freshZero freshZero` filler. Each ≈ ½ a kimchi row.
-- | Tuned (probe-confirmed) so the N=2 step circuit is 53960 rows
-- | ∈ (2^15, 2^16] ⇒ domain log2 = 16, num_chunks = 1.
fillerIters :: Int
fillerIters = 1 `Bits.shl` 16

-- | Timed-trial count for the compile bench. Each trial is one FULL N=2
-- | domain-2^16 compilation (multiple minutes). Deliberately tiny — NOT
-- | benchlib's default 1000.
benchIterations :: Int
benchIterations = 3

type TreeProofReturnPrevsSpec =
  Tuple2
    (Slot Compiled 0 1 (StatementIO Unit (F StepField)))
    (Slot Compiled 2 1 (StatementIO Unit (F StepField)))

-- | Verbatim `Tree_proof_return` N=2 rule + the tunable filler loop
-- | (stack-safe `tailRecM`; `StepRule` carries `MonadRec`).
benchTreeRule
  :: StepRule 2
       (Tuple2 (StatementIO Unit (F StepField)) (StatementIO Unit (F StepField)))
       Unit
       Unit
       (F StepField)
       (FVar StepField)
       (F StepField)
       (FVar StepField)
benchTreeRule getPrevStates _ = do
  -- The two prev statements arrive via the deferred getter (slot 0 = NRR
  -- base, slot 1 = the recursive `Self` prev); their public OUTPUT is the
  -- field this rule threads. Read each slot's `.output` through `exists`.
  nrrInput <- exists $ getPrevStates <#> \(StatementIO { output } /\ _) -> output
  prevInput <- exists $ getPrevStates <#> \(_ /\ StatementIO { output } /\ _) -> output
  isBaseCase <- exists $ getPrevStates <#> \(_ /\ StatementIO { output } /\ _) -> output == F (negate one)
  let proofMustVerifySlot1 = not_ isBaseCase
  selfVal <- if_ isBaseCase (const_ zero) (CVar.add_ (const_ one) prevInput)
  let
    freshZero = exists (pure (zero :: F StepField))
    mulOne = do
      z1 <- freshZero
      z2 <- freshZero
      _ <- mul_ z1 z2
      pure unit
  tailRecM
    ( \i ->
        if i >= fillerIters then pure (Done unit)
        else mulOne *> pure (Loop (i + 1))
    )
    0
  pure
    { prevPublicInputs: nrrInput :< prevInput :< Vector.nil
    , proofMustVerify: true_ :< proofMustVerifySlot1 :< Vector.nil
    , publicOutput: selfVal
    }

nrrRule :: StepRule 0 Unit Unit Unit (F StepField) (FVar StepField) Unit Unit
nrrRule _ _ = pure
  { prevPublicInputs: Vector.nil
  , proofMustVerify: Vector.nil
  , publicOutput: const_ zero
  }

type NrrRules =
  RulesCons 0 Unit Unit Unit
    RulesNil

type TreeRules =
  RulesCons 2
    (Tuple2 (StatementIO Unit (F StepField)) (StatementIO Unit (F StepField)))
    TreeProofReturnPrevsSpec
    (Tuple2 SlotWrapKey SlotWrapKey)
    RulesNil
