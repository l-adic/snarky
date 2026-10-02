module Pickles.CircuitDiffs.PureScript.WrapVerify
  ( WrapVerifyInput(..)
  , compileWrapVerify
  ) where

-- | Wrap verify circuit (N1): the library `wrapVerify` over the dump's typed input.

import Prelude

import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple5, tuple5, uncurry5)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyVestaPt, wrapEndo)
import Pickles.CircuitDiffs.PureScript.IvpWrap (IvpHarnessInput(..), IvpWrapInput, IvpWrapParams)
import Pickles.Field (WrapField)
import Pickles.PublicInputCommit (CorrectionMode(..))
import Pickles.Types (ChunkedCommitment(..), WrapIPARounds, WrapProofMessages(..))
import Pickles.Wrap.Verify (wrapVerify)
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, BoolVar, F(..), FVar, Snarky, UnChecked(..), const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | `wrap_verify{,_n2}_circuit`'s input (OCaml `dump_circuit_impl.ml`) at `n` proofs:
-- | `ivp_wrap_circuit`'s input, the claimed `messages_for_next_wrap_proof` digest, the `n` new
-- | challenge vectors, `unused`, then the `n` `sg_old` points. `unused` is one cell at one
-- | proof (OCaml computes the offset at 16 rounds where the wrap side has 15; at two proofs
-- | the second challenge vector covers it) and `Unit`, no cells, at two.
newtype WrapVerifyInput n gap f b pt = WrapVerifyInput
  { ivp :: IvpWrapInput f b pt
  , messagesForNextWrapProofDigest :: f
  , newBpChallenges :: Vector n (Vector WrapIPARounds f)
  , unused :: gap
  , sgOld :: Vector n pt
  }

-- | The wire order.
type WrapVerifyTuple n gap f b pt =
  Tuple5 (IvpWrapInput f b pt) f (Vector n (Vector WrapIPARounds f)) gap (Vector n pt)

toTuple :: forall n gap f b pt. WrapVerifyInput n gap f b pt -> WrapVerifyTuple n gap f b pt
toTuple (WrapVerifyInput i) =
  tuple5 i.ivp i.messagesForNextWrapProofDigest i.newBpChallenges i.unused i.sgOld

fromTuple :: forall n gap f b pt. WrapVerifyTuple n gap f b pt -> WrapVerifyInput n gap f b pt
fromTuple = uncurry5 \ivp messagesForNextWrapProofDigest newBpChallenges unused sgOld ->
  WrapVerifyInput { ivp, messagesForNextWrapProofDigest, newBpChallenges, unused, sgOld }

instance
  ( Reflectable n Int
  , CircuitType f fa fv
  , CircuitType f ga gv
  , CircuitType f pa pv
  , CircuitType f (IvpWrapInput fa ba pa) (IvpWrapInput fv bv pv)
  ) =>
  CircuitType f (WrapVerifyInput n ga fa ba pa) (WrapVerifyInput n gv fv bv pv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(WrapVerifyTuple n ga fa ba pa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(WrapVerifyTuple n ga fa ba pa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(WrapVerifyTuple n ga fa ba pa)

wrapVerifyCircuit
  :: forall r
   . IvpWrapParams
  -> UnChecked (WrapVerifyInput 1 (FVar WrapField) (FVar WrapField) (BoolVar WrapField) (AffinePoint (FVar WrapField)))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
wrapVerifyCircuit { lagrangeAt, blindingH } (UnChecked (WrapVerifyInput input)) = do
  let
    IvpHarnessInput ivp = input.ivp
    WrapProofMessages m = ivp.messages
    constDummyPt = let AffinePoint { x: F x', y: F y' } = dummyVestaPt in AffinePoint { x: const_ x', y: const_ y' }

    ivpParams =
      { curveParams: curveParams (Proxy @VestaG)
      , lagrangeAt
      , blindingH
      , correctionMode: InCircuitCorrections
      , endo: wrapEndo
      , groupMapParams: groupMapParams (Proxy @VestaG)
      , useOptSponge: true
      }

    fullIvpInput =
      { publicInput: ivp.publicInput
      , sgOld: input.sgOld
      , sgOldMask: Just (Vector.replicate (const_ one))
      , sigmaCommLast: ChunkedCommitment (Vector.singleton constDummyPt)
      , columnComms:
          { index: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 6 _
          , coeff: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 15 _
          , sigma: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 6 _
          }
      , deferredValues: ivp.deferredValues
      , wComm: m.wComm
      , zComm: m.zComm
      , tComm: Vector.concat (coerce m.tComm :: Vector 7 (Vector 1 (AffinePoint (FVar WrapField))))
      , opening: ivp.opening
      }

    verifyInput =
      { spongeDigestBeforeEvaluations: ivp.claimedDigest
      , messagesForNextWrapProofDigest: input.messagesForNextWrapProofDigest
      , bulletproofChallenges: ivp.deferredValues.bulletproofChallenges
      , newBpChallenges: input.newBpChallenges
      , sg: ivp.opening.sg
      }

  wrapVerify ivpParams fullIvpInput verifyInput

compileWrapVerify :: IvpWrapParams -> Effect (CompiledCircuit WrapField)
compileWrapVerify srsData =
  compile noAdvice
    (Proxy @(UnChecked (WrapVerifyInput 1 (F WrapField) (F WrapField) Boolean (AffinePoint WrapField))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    (wrapVerifyCircuit srsData)
