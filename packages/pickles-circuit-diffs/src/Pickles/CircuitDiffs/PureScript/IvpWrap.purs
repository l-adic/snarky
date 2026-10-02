module Pickles.CircuitDiffs.PureScript.IvpWrap
  ( IvpHarnessInput(..)
  , IvpWrapInput
  , IvpWrapParams
  , IvpOpening
  , compileIvpWrap
  ) where

import Prelude

import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (Tuple10, Tuple2, Tuple5, tuple10, tuple2, tuple5, uncurry10, uncurry2, uncurry5)
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, dummyVestaPt, wrapEndo)
import Pickles.DeferredValues (DeferredValues)
import Pickles.Field (WrapField)
import Pickles.IncrementallyVerifyProof (incrementallyVerifyProof)
import Pickles.PackedStatement (PackedStepPublicInput)
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBaseLookup)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Types (ChunkedCommitment(..), WrapProofMessages(..))
import Pickles.Wrap.OtherField as WrapOtherField
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (class CircuitType, BoolVar, F(..), FVar, SizedF, Snarky, UnChecked(..), assertEq, assertEqual_, const_, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (Type1, groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

type IvpWrapParams =
  { lagrangeAt :: LagrangeBaseLookup 1 WrapField
  , blindingH :: AffinePoint (F WrapField)
  }

-- | A proof's opening, as `incrementallyVerifyProof` takes it, at `n` rounds.
type IvpOpening n pt s =
  { delta :: pt
  , sg :: pt
  , lr :: Vector n { l :: pt, r :: pt }
  , z1 :: s
  , z2 :: s
  }

-- | An `ivp_{step,wrap}_circuit` input (OCaml `dump_circuit_impl.ml`): the public input `pi`,
-- | the verified proof's deferred values at `d` rounds and shifted values `s`, its messages and
-- | opening at one chunk, and the claimed sponge digest before evaluations. The deferred
-- | values travel as the plonk challenges `alpha`, `beta`, `gamma`, `zeta`, then `perm`,
-- | `zetaToSrsLength`, `zetaToDomainSize`, `cip`, `b`, `xi` and the challenges; the opening as
-- | `delta`, `sg`, the `(L, R)` pairs, `z1`, `z2`.
newtype IvpHarnessInput pi d f pt s = IvpHarnessInput
  { publicInput :: pi
  , deferredValues :: DeferredValues d f s
  , messages :: WrapProofMessages 1 pt
  , opening :: IvpOpening d pt s
  , claimedDigest :: f
  }

-- | `ivp_wrap_circuit`'s input: the packed step statement at one proof and 15 rounds, the step
-- | proof at 16 rounds, Type1-shifted.
type IvpWrapInput f b pt = IvpHarnessInput (PackedStepPublicInput 1 15 f b) 16 f pt (Type1 f)

-- | The deferred values in the dump's order.
type DeferredTuple d f s =
  Tuple10 (SizedF 128 f) (SizedF 128 f) (SizedF 128 f) (SizedF 128 f) s s s s s
    (Tuple2 (SizedF 128 f) (Vector d (SizedF 128 f)))

-- | The opening in the dump's order.
type OpeningTuple d pt s = Tuple5 pt pt (Vector d { l :: pt, r :: pt }) s s

-- | The wire order.
type IvpTuple pi d f pt s =
  Tuple5 pi (DeferredTuple d f s) (WrapProofMessages 1 pt) (OpeningTuple d pt s) f

toTuple :: forall pi d f pt s. IvpHarnessInput pi d f pt s -> IvpTuple pi d f pt s
toTuple (IvpHarnessInput i) =
  tuple5 i.publicInput
    ( tuple10 p.alpha p.beta p.gamma p.zeta p.perm p.zetaToSrsLength p.zetaToDomainSize
        dv.combinedInnerProduct
        dv.b
        (tuple2 dv.xi dv.bulletproofChallenges)
    )
    i.messages
    (tuple5 i.opening.delta i.opening.sg i.opening.lr i.opening.z1 i.opening.z2)
    i.claimedDigest
  where
  dv = i.deferredValues
  p = dv.plonk

fromTuple :: forall pi d f pt s. IvpTuple pi d f pt s -> IvpHarnessInput pi d f pt s
fromTuple = uncurry5 \publicInput dv messages opening claimedDigest ->
  IvpHarnessInput
    { publicInput
    , deferredValues: dv # uncurry10 \alpha beta gamma zeta perm zetaToSrsLength zetaToDomainSize combinedInnerProduct b rest ->
        rest # uncurry2 \xi bulletproofChallenges ->
          { plonk: { alpha, beta, gamma, zeta, perm, zetaToSrsLength, zetaToDomainSize }
          , combinedInnerProduct
          , xi
          , bulletproofChallenges
          , b
          }
    , messages
    , opening: opening # uncurry5 \delta sg lr z1 z2 -> { delta, sg, lr, z1, z2 }
    , claimedDigest
    }

instance
  ( Reflectable d Int
  , CircuitType f ia iv
  , CircuitType f fa fv
  , CircuitType f pa pv
  , CircuitType f sa sv
  ) =>
  CircuitType f (IvpHarnessInput ia d fa pa sa) (IvpHarnessInput iv d fv pv sv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(IvpTuple ia d fa pa sa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(IvpTuple ia d fa pa sa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(IvpTuple ia d fa pa sa)

-- | The library's `incrementallyVerifyProof` on the wrap side, at the conditional sponge
-- | with no `sg_old` and the dummy key, then the digest and challenges against the claims.
ivpWrapCircuit
  :: forall r
   . IvpWrapParams
  -> UnChecked (IvpWrapInput (FVar WrapField) (BoolVar WrapField) (AffinePoint (FVar WrapField)))
  -> Snarky WrapField (KimchiConstraint WrapField) r Unit
ivpWrapCircuit { lagrangeAt, blindingH } (UnChecked (IvpHarnessInput input)) = do
  let
    constDummyPt = let AffinePoint { x: F x', y: F y' } = dummyVestaPt in AffinePoint { x: const_ x', y: const_ y' }
    WrapProofMessages m = input.messages

    ivpParams =
      { curveParams: curveParams (Proxy @VestaG)
      , lagrangeAt
      , blindingH
      , correctionMode: InCircuitCorrections
      , endo: wrapEndo
      , groupMapParams: groupMapParams (Proxy @VestaG)
      , useOptSponge: true
      }
    ivpInput =
      { publicInput: input.publicInput
      , sgOld: Vector.nil
      , sgOldMask: Just Vector.nil
      -- VK data as circuit variables (dummy constants for circuit-diff test)
      , sigmaCommLast: ChunkedCommitment (Vector.singleton constDummyPt)
      , columnComms:
          { index: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 6 _
          , coeff: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 15 _
          , sigma: (Vector.replicate (ChunkedCommitment (Vector.singleton constDummyPt))) :: Vector 6 _
          }
      , deferredValues: input.deferredValues
      , wComm: m.wComm
      , zComm: m.zComm
      , tComm: Vector.concat (coerce m.tComm :: Vector 7 (Vector 1 (AffinePoint (FVar WrapField))))
      , opening: input.opening
      }
  output <- evalSpongeM initialSpongeCircuit $
    incrementallyVerifyProof @VestaG WrapOtherField.ipaScalarOps ivpParams ivpInput Nothing
  assertEqual_ output.spongeDigestBeforeEvaluations input.claimedDigest
  for_ (Vector.zip input.deferredValues.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) ->
    assertEq c1 c2

compileIvpWrap :: IvpWrapParams -> Effect (CompiledCircuit WrapField)
compileIvpWrap srsData =
  compile noAdvice
    (Proxy @(UnChecked (IvpWrapInput (F WrapField) Boolean (AffinePoint WrapField))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint WrapField))
    (ivpWrapCircuit srsData)
