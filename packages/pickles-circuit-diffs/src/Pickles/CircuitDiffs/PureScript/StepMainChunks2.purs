module Pickles.CircuitDiffs.PureScript.StepMainChunks2
  ( compileStepMainChunks2
  , StepMainChunks2Params
  , class Chunks2Advice
  ) where

-- | step_main circuit for the chunks2 leaf rule (N = 0, num_chunks = 2,
-- | override_wrap_domain = N1). Mirrors the OCaml dumper at
-- | `mina/src/lib/crypto/pickles/dump_chunks2/dump_chunks2.ml`.
-- |
-- | Same N=0 shape as `step_main_no_recursion_return_circuit` but the
-- | rule body fills `2^17 + 1` `Field.mul (fresh_zero) (fresh_zero)`
-- | half-rows (= ~2^16 kimchi rows) plus one 7-wire Raw Generic with
-- | zero coeffs (forces the 7th permuted column's polynomial degree
-- | above 2^16). The resulting step domain rounds to 2^17 and the
-- | kimchi PCS commits with `num_chunks = 2` at max_poly_size = 2^16.
-- |
-- | OCaml dump target:
-- | `packages/pickles-circuit-diffs/circuits/ocaml/chunks2_step_main_circuit.json`
-- | (Generic = 65622, Poseidon = 308, Zero = 28; total 65958 gates).

import Prelude

import Data.Array as Array
import Data.Foldable (foldM)
import Data.Int.Bits as Bits
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (StepArtifact, dummyWrapSg, mkStepArtifact)
import Pickles.Field (StepField)
import Pickles.PublicInputCommit (LagrangeBaseLookup)
import Pickles.Step.Main (RuleOutput, stepMain)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitM, F, Snarky, addConstraint, exists, mul_)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

type StepMainChunks2Params =
  { lagrangeAt :: LagrangeBaseLookup 1 StepField
  , blindingH :: AffinePoint (F StepField)
  }

-- | Chunks2 rule allocates only `exists` witnesses for the `fresh_zero`
-- | inputs; no further plumbing is needed. The class stays uniform with
-- | the other rules so `stepMain`'s typeclass dictionary resolves.
class Monad m <= Chunks2Advice m

instance (Monad m) => Chunks2Advice m

-- | Chunks2 leaf rule body. Verbatim PS analog of `dump_chunks2.ml`'s
-- | choice body — `2^17 + 1` `mul_ fresh_zero fresh_zero` half-rows
-- | followed by a single 7-wire Raw Generic with zero coeffs.
chunks2Rule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Chunks2Advice m
  => Unit
  -> Snarky (KimchiConstraint StepField) t m (RuleOutput 0 Unit Unit)
chunks2Rule _ = do
  let
    freshZero = exists (pure (zero :: F StepField))
    iters = (1 `Bits.shl` 17) + 1
    mulOne _ = do
      z1 <- freshZero
      z2 <- freshZero
      _ <- mul_ z1 z2
      pure unit
  foldM (\_ i -> mulOne i) unit (Array.range 0 (iters - 1))
  z <- freshZero
  addConstraint $ KimchiRawGeneric7
    (z :< z :< z :< z :< z :< z :< z :< Vector.nil)
  pure
    { prevPublicInputs: Vector.nil
    , proofMustVerify: Vector.nil
    , publicOutput: unit
    }

compileStepMainChunks2
  :: StepMainChunks2Params -> Effect StepArtifact
compileStepMainChunks2 params =
  mkStepArtifact <$>
    compile (Proxy @Unit) (Proxy @(Vector 1 (F StepField))) (Proxy @(KimchiConstraint StepField))
      -- N=0: output size = 32*0 + 1 + 0 = 1 (just the msgForNextStep
      -- digest — no unfinalized_proofs, no messages_for_next_wrap_proof
      -- entries). Single-rule, Nil prevs: len = 0, mpvMax = 0, mpvPad = 0.
      -- inputVal/outputVal both Unit — chunks2 is `Input Typ.unit`
      -- (degenerate Input mode) with `~auxiliary_typ:Typ.unit`.
      ( \_ -> stepMain @Unit @Unit @Unit @Unit @Unit @0 @1 @Unit @1
          chunks2Rule
          { perSlotLagrangeAt: Vector.nil
          , blindingH: params.blindingH
          , perSlotFopDomainLog2s: Vector.nil
          , perSlotVkBlueprints: unit
          }
          dummyWrapSg
          -- Side-loaded VK carrier: no slots, carrier = Unit.
          unit
      )
      Kimchi.initialState
