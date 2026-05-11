module Pickles.CircuitDiffs.PureScript.BCorrect
  ( BCorrectInput
  , parseBCorrectInput
  , bCorrectStepCircuit
  , compileBCorrect
  ) where

import Prelude

import Data.Fin (getFinite)
import Data.Traversable (for)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, stepEndo, unsafeIdx)
import Pickles.IPA (bCorrectCircuit) as IPA
import Pickles.Step.Types (Field)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F, FVar, SizedF, Snarky, const_)
import Snarky.Circuit.Kimchi (Type1(..), fromShiftedType1Circuit, toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Type.Proxy (Proxy(..))

type BCorrectInput f =
  { rawChallenges :: Vector 16 (SizedF 128 (FVar f))
  , zeta :: FVar f
  , zetaOmega :: FVar f
  , evalscale :: FVar f
  , claimedB :: Type1 (FVar f)
  }

parseBCorrectInput :: Vector 20 (FVar Field) -> BCorrectInput Field
parseBCorrectInput inputs =
  let
    at = unsafeIdx inputs
  in
    { rawChallenges: Vector.generate \j -> asSizedF128 (at (getFinite j))
    , zeta: at 16
    , zetaOmega: at 17
    , evalscale: at 18
    , claimedB: Type1 (at 19)
    }

bCorrectStepCircuit
  :: forall t m
   . CircuitM Field (KimchiConstraint Field) t m
  => BCorrectInput Field
  -> Snarky (KimchiConstraint Field) t m (BoolVar Field)
bCorrectStepCircuit input = do
  let endoVar = const_ stepEndo :: FVar Field
  -- Expand challenges in reverse order (OCaml right-to-left evaluation)
  expandedRev <- for (Vector.reverse input.rawChallenges) \c -> toField @8 c endoVar
  let expanded = Vector.reverse expandedRev
  IPA.bCorrectCircuit
    { challenges: expanded
    , zeta: input.zeta
    , zetaOmega: input.zetaOmega
    , evalscale: input.evalscale
    , expectedB: fromShiftedType1Circuit input.claimedB
    }

compileBCorrect :: CompiledCircuit Field
compileBCorrect =
  compilePure (Proxy @(Vector 20 (F Field))) (Proxy @Unit) (Proxy @(KimchiConstraint Field))
    (\inputs -> void $ bCorrectStepCircuit (parseBCorrectInput inputs))
    Kimchi.initialState
