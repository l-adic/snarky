module Pickles.CircuitDiffs.PureScript.SchnorrVerify
  ( SchnorrVerifyInput
  , parseSchnorrVerifyInput
  , compileSchnorrVerify
  ) where

import Prelude

import Data.Maybe (fromJust)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Data.Schnorr.ChainId (ChainId(..), signaturePrefix)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, unsafeIdx)
import Pickles.Field (StepField)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (F, FVar, const_)
import Snarky.Circuit.Schnorr (Signature(..), verifies)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (generator, toAffine)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

-- | Schnorr verifier circuit-diff input — same layout as the OCaml
-- | fixture's `Typ` ((pk*Field*Field) * msg[1] = 5 fields).
type SchnorrVerifyInput f =
  { pk :: AffinePoint (FVar f)
  , r :: FVar f
  , s :: FVar f
  , message :: Vector 1 (FVar f)
  }

parseSchnorrVerifyInput :: Vector 5 (FVar StepField) -> SchnorrVerifyInput StepField
parseSchnorrVerifyInput inputs =
  let
    at = unsafeIdx inputs
  in
    { pk: { x: at 0, y: at 1 }
    , r: at 2
    , s: at 3
    , message: at 4 :< Vector.nil
    }

-- | Pallas generator as a circuit-constant point.
generatorPallas :: AffinePoint (FVar StepField)
generatorPallas =
  let
    g = unsafePartial $ fromJust $ toAffine (generator :: PallasG)
  in
    { x: const_ g.x, y: const_ g.y }

compileSchnorrVerify :: CompiledCircuit StepField
compileSchnorrVerify =
  compilePure (Proxy @(Vector 5 (F StepField))) (Proxy @Boolean) (Proxy @(KimchiConstraint StepField))
    ( \inputs ->
        let
          { pk, r, s, message } = parseSchnorrVerifyInput inputs
        in
          verifies (signaturePrefix Mainnet) generatorPallas
            { publicKey: pk
            , signature: Signature { r, s }
            , message
            }
    )
    Kimchi.initialState
