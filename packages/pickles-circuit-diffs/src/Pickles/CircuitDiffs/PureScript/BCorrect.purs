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
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, stepEndo, unsafeIdx)
import Pickles.Field (StepField)
import Pickles.IPA (bCorrectCircuit) as IPA
import Run as Run
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (BoolVar, F, FVar, SizedF, Snarky, const_)
import Snarky.Circuit.Kimchi (Type1(..), fromShiftedType1Circuit, toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField)
import Type.Proxy (Proxy(..))

type BCorrectInput f =
  { rawChallenges :: Vector 16 (SizedF 128 (FVar f))
  , zeta :: FVar f
  , zetaOmega :: FVar f
  , evalscale :: FVar f
  , claimedB :: Type1 (FVar f)
  }

parseBCorrectInput :: Vector 20 (FVar StepField) -> BCorrectInput StepField
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
  :: forall r
   . PrimeField StepField
  => BCorrectInput StepField
  -> Snarky StepField (KimchiConstraint StepField) r (BoolVar StepField)
bCorrectStepCircuit input = do
  let endoVar = const_ stepEndo :: FVar StepField
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

compileBCorrect :: Effect (CompiledCircuit StepField)
compileBCorrect =
  Run.runBaseEffect $ compile (Proxy @(Vector 20 (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> void $ bCorrectStepCircuit (parseBCorrectInput inputs))
