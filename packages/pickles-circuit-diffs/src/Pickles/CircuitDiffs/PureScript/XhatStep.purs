module Pickles.CircuitDiffs.PureScript.XhatStep
  ( XhatStepInput
  , compileXhatStep
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple6, tuple6, uncurry6)
import Data.Vector (Vector)
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit)
import Pickles.Field (StepField)
import Pickles.PublicInputCommit (class PublicInputCommit, CorrectionMode(..), LagrangeBaseLookup, ScalarMulResult, publicInputCommit, scalarMuls)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, F, FVar, SizedF, Snarky, UnChecked(..), genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class PrimeField, curveParams)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams)
import Type.Proxy (Proxy(..))

type XhatStepParams f =
  { lagrangeAt :: LagrangeBaseLookup 1 f
  , blindingH :: AffinePoint (F f)
  }

-- | `xhat_step_circuit`'s input (OCaml `dump_circuit_impl.ml`): the packed wrap statement
-- | without its feature cells (`Pickles.Wrap.Types.StatementPacked`'s first six fields), each
-- | leaf committed at its width — the shifted scalars and the digests at full width, the
-- | challenges at 128 bits, the branch data at 10.
newtype XhatStepInput f = XhatStepInput
  { fpFields :: Vector 5 f -- combined_inner_product, b, zetaToSrsLength, zetaToDomainSize, perm
  , challenges :: Vector 2 (SizedF 128 f) -- beta, gamma
  , scalarChallenges :: Vector 3 (SizedF 128 f) -- alpha, zeta, xi
  , digests :: Vector 3 f -- sponge_digest, msg_for_next_wrap, msg_for_next_step
  , bulletproofChallenges :: Vector 16 (SizedF 128 f)
  , branchData :: SizedF 10 f
  }

-- | The wire order.
type XhatStepTuple f =
  Tuple6 (Vector 5 f) (Vector 2 (SizedF 128 f)) (Vector 3 (SizedF 128 f)) (Vector 3 f)
    (Vector 16 (SizedF 128 f))
    (SizedF 10 f)

toTuple :: forall f. XhatStepInput f -> XhatStepTuple f
toTuple (XhatStepInput i) =
  tuple6 i.fpFields i.challenges i.scalarChallenges i.digests i.bulletproofChallenges i.branchData

fromTuple :: forall f. XhatStepTuple f -> XhatStepInput f
fromTuple = uncurry6 \fpFields challenges scalarChallenges digests bulletproofChallenges branchData ->
  XhatStepInput { fpFields, challenges, scalarChallenges, digests, bulletproofChallenges, branchData }

instance CircuitType f fa fv => CircuitType f (XhatStepInput fa) (XhatStepInput fv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(XhatStepTuple fa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(XhatStepTuple fa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(XhatStepTuple fa)

instance
  ( PublicInputCommit (XhatStepTuple (FVar f)) f
  ) =>
  PublicInputCommit (XhatStepInput (FVar f)) f where
  scalarMuls
    :: forall @stepChunks r
     . PrimeField f
    => Reflectable stepChunks Int
    => CurveParams f
    -> XhatStepInput (FVar f)
    -> LagrangeBaseLookup stepChunks f
    -> Int
    -> Snarky f (KimchiConstraint f) r (ScalarMulResult stepChunks f)
  scalarMuls params x lookup idx =
    scalarMuls @(XhatStepTuple (FVar f)) @f params (toTuple x) lookup idx

xhatStepCircuit
  :: forall r
   . XhatStepParams StepField
  -> UnChecked (XhatStepInput (FVar StepField))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
xhatStepCircuit { lagrangeAt, blindingH } (UnChecked publicInput) =
  void $ publicInputCommit @1
    { curveParams: curveParams (Proxy @PallasG)
    , lagrangeAt
    , blindingH
    , correctionMode: PureCorrections
    }
    publicInput

compileXhatStep :: XhatStepParams StepField -> Effect (CompiledCircuit StepField)
compileXhatStep srsData =
  compile noAdvice (Proxy @(UnChecked (XhatStepInput (F StepField)))) (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    (xhatStepCircuit srsData)
