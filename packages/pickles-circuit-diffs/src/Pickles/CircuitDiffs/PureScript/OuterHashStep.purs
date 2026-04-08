module Pickles.CircuitDiffs.PureScript.OuterHashStep
  ( compileOuterHashStep
  ) where

-- | Isolated outer hash_messages_for_next_step_proof circuit.
-- | Matches OCaml's outer_hash_step_circuit:
-- |   - Allocate VK via exists (with curve checks)
-- |   - Allocate appState, sg, 16 bp_challenges
-- |   - Run the non-opt hash: sponge_after_index(VK) → absorb app_state → sg → bp_chals → squeeze

import Prelude

import Data.Foldable (foldM)
import Data.Vector (Vector)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Sponge (initialSpongeCircuit)
import Pickles.Types (StepField, StepIPARounds)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, exists, label)
import Snarky.Circuit.RandomOracle.Sponge as Sponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

-- | Never-evaluated prover value for exists
dummy :: forall a b. Applicative b => b a
dummy = pure (unsafeCoerce unit)

compileOuterHashStep :: CompiledCircuit StepField
compileOuterHashStep =
  compilePure (Proxy @Unit) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    outerHashCircuit
    Kimchi.initialState

outerHashCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Unit
  -> Snarky (KimchiConstraint StepField) t m Unit
outerHashCircuit _ = do
  -- Allocate VK (with curve checks, matching OCaml exists with Inner_curve.typ)
  vk <- exists
    ( dummy
        :: _
             { sigma :: Vector 6 (WeierstrassAffinePoint PallasG (F StepField))
             , sigmaLast :: WeierstrassAffinePoint PallasG (F StepField)
             , coeff :: Vector 15 (WeierstrassAffinePoint PallasG (F StepField))
             , index :: Vector 6 (WeierstrassAffinePoint PallasG (F StepField))
             }
    )

  -- Allocate appState
  appState <- exists (dummy :: _ (F StepField))

  -- Allocate sg point (curve-checked)
  sg <- exists (dummy :: _ (WeierstrassAffinePoint PallasG (F StepField)))

  -- Allocate 16 bp_challenges as plain fields (matching OCaml)
  bpChallenges :: Vector StepIPARounds (FVar StepField) <- exists (dummy :: _ (Vector StepIPARounds (F StepField)))

  -- Run the non-opt hash
  let unwrapPt (WeierstrassAffinePoint pt) = pt
  _digest <- label "hash_messages_for_next_step_proof" do
    let
      absorbPt s pt = do
        let { x, y } = unwrapPt pt
        s1 <- Sponge.absorb x s
        Sponge.absorb y s1

    -- 1. sponge_after_index: absorb VK fields
    spongeAfterIndex <- do
      let sponge0 = initialSpongeCircuit :: Sponge.Sponge (FVar StepField)
      s1 <- foldM absorbPt sponge0 vk.sigma
      s2 <- absorbPt s1 vk.sigmaLast
      s3 <- foldM absorbPt s2 vk.coeff
      foldM absorbPt s3 vk.index

    -- 2. Absorb app_state
    s1 <- Sponge.absorb appState spongeAfterIndex

    -- 3. For each proof: sg + bp_challenges
    let sgPt = unwrapPt sg
    s2 <- Sponge.absorb sgPt.x s1
    s3 <- Sponge.absorb sgPt.y s2
    sAfterProofs <- foldM (\s c -> Sponge.absorb c s) s3 bpChallenges

    -- 4. Squeeze
    { result: digest } <- Sponge.squeeze sAfterProofs
    pure digest

  pure unit
