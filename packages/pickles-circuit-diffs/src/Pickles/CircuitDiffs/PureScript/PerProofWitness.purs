module Pickles.CircuitDiffs.PureScript.PerProofWitness
  ( PerProofWitnessInput(..)
  , DeferredHlist
  , deferredToHlist
  , deferredFromHlist
  , WrapDeferredHlist
  , wrapDeferredToHlist
  , wrapDeferredFromHlist
  , unfinalizedDeferredValues
  ) where

import Prelude

import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple10, Tuple2, Tuple3, Tuple7, tuple10, tuple2, tuple3, tuple7, uncurry10, uncurry2, uncurry3, uncurry7)
import Data.Vector (Vector)
import Pickles.DeferredValues (DeferredValues, WrapDeferredValues)
import Pickles.Step.Types (WrapProof)
import Pickles.Types (AllocEvals, PerProofUnfinalized(..))
import Snarky.Circuit.DSL (class CircuitType, FVar, SizedF, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Circuit.Kimchi (SplitField, Type1, Type2)
import Type.Proxy (Proxy(..))

-- | The step-side verify harnesses' per-proof witness (OCaml `Per_proof_witness`, as
-- | `dump_circuit_impl.ml` lays it out): the application state, the wrap proof at 15 rounds
-- | and one chunk, its statement's deferred values at 16 rounds, the sponge digest, the
-- | evaluations, and the `w` previous challenge vectors and `sg`s. The deferred values travel
-- | in OCaml's hlist order: `alpha`, `beta`, `gamma`, `zeta`, `zetaToSrsLength`,
-- | `zetaToDomainSize`, `perm`, `cip`, `b`, `xi`, the challenges, the mask, `domainLog2`.
newtype PerProofWitnessInput a w f b pt = PerProofWitnessInput
  { appState :: a
  , wrapProof :: WrapProof 15 1 pt (Type2 (SplitField f b))
  , deferredValues :: WrapDeferredValues 16 f (Type1 f) b
  , spongeDigest :: f
  , evals :: AllocEvals f
  , prevChallenges :: Vector w (Vector 16 f)
  , prevSgs :: Vector w pt
  }

-- | Deferred values at `d` rounds in OCaml's hlist order: `alpha`, `beta`, `gamma`, `zeta`,
-- | `zetaToSrsLength`, `zetaToDomainSize`, `perm`, `cip`, `b`, `xi`, the challenges.
type DeferredHlist d f s =
  Tuple10 (SizedF 128 f) (SizedF 128 f) (SizedF 128 f) (SizedF 128 f) s s s s s
    (Tuple2 (SizedF 128 f) (Vector d (SizedF 128 f)))

deferredToHlist :: forall d f s. DeferredValues d f s -> DeferredHlist d f s
deferredToHlist dv =
  tuple10 p.alpha p.beta p.gamma p.zeta p.zetaToSrsLength p.zetaToDomainSize p.perm
    dv.combinedInnerProduct
    dv.b
    (tuple2 dv.xi dv.bulletproofChallenges)
  where
  p = dv.plonk

deferredFromHlist :: forall d f s. DeferredHlist d f s -> DeferredValues d f s
deferredFromHlist = uncurry10 \alpha beta gamma zeta zetaToSrsLength zetaToDomainSize perm combinedInnerProduct b rest ->
  rest # uncurry2 \xi bulletproofChallenges ->
    { plonk: { alpha, beta, gamma, zeta, perm, zetaToSrsLength, zetaToDomainSize }
    , combinedInnerProduct
    , xi
    , bulletproofChallenges
    , b
    }

-- | A wrap statement's deferred values at 16 rounds in OCaml's hlist order: the deferred
-- | values, the mask, `domainLog2`.
type WrapDeferredHlist f b = Tuple3 (DeferredHlist 16 f (Type1 f)) (Vector 2 b) f

wrapDeferredToHlist :: forall f b. WrapDeferredValues 16 f (Type1 f) b -> WrapDeferredHlist f b
wrapDeferredToHlist dv =
  tuple3
    ( deferredToHlist
        { plonk: dv.plonk
        , combinedInnerProduct: dv.combinedInnerProduct
        , xi: dv.xi
        , bulletproofChallenges: dv.bulletproofChallenges
        , b: dv.b
        }
    )
    dv.branchData.proofsVerifiedMask
    dv.branchData.domainLog2

wrapDeferredFromHlist :: forall f b. WrapDeferredHlist f b -> WrapDeferredValues 16 f (Type1 f) b
wrapDeferredFromHlist = uncurry3 \deferred proofsVerifiedMask domainLog2 ->
  let
    dv = deferredFromHlist deferred
  in
    { plonk: dv.plonk
    , combinedInnerProduct: dv.combinedInnerProduct
    , xi: dv.xi
    , bulletproofChallenges: dv.bulletproofChallenges
    , b: dv.b
    , branchData: { domainLog2, proofsVerifiedMask }
    }

-- | The wire order.
type PerProofWitnessTuple a w f b pt =
  Tuple7 a (WrapProof 15 1 pt (Type2 (SplitField f b))) (WrapDeferredHlist f b) f (AllocEvals f)
    (Vector w (Vector 16 f))
    (Vector w pt)

toTuple :: forall a w f b pt. PerProofWitnessInput a w f b pt -> PerProofWitnessTuple a w f b pt
toTuple (PerProofWitnessInput i) =
  tuple7 i.appState i.wrapProof (wrapDeferredToHlist i.deferredValues) i.spongeDigest i.evals
    i.prevChallenges
    i.prevSgs

fromTuple :: forall a w f b pt. PerProofWitnessTuple a w f b pt -> PerProofWitnessInput a w f b pt
fromTuple = uncurry7 \appState wrapProof dv spongeDigest evals prevChallenges prevSgs ->
  PerProofWitnessInput
    { appState
    , wrapProof
    , deferredValues: wrapDeferredFromHlist dv
    , spongeDigest
    , evals
    , prevChallenges
    , prevSgs
    }

instance
  ( Reflectable w Int
  , CircuitType f aa av
  , CircuitType f fa fv
  , CircuitType f ba bv
  , CircuitType f pa pv
  , CircuitType f (Type1 fa) (Type1 fv)
  , CircuitType f (Type2 (SplitField fa ba)) (Type2 (SplitField fv bv))
  ) =>
  CircuitType f (PerProofWitnessInput aa w fa ba pa) (PerProofWitnessInput av w fv bv pv) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(PerProofWitnessTuple aa w fa ba pa))
  valueToFields = genericValueToFields <<< toTuple
  fieldsToValue = fromTuple <<< genericFieldsToValue
  varToFields = genericVarToFields @(PerProofWitnessTuple aa w fa ba pa) <<< toTuple
  fieldsToVar = fromTuple <<< genericFieldsToVar @(PerProofWitnessTuple aa w fa ba pa)

-- | An unfinalized entry's deferred values, as the verifier takes them.
unfinalizedDeferredValues
  :: forall d sf f b
   . PerProofUnfinalized d sf (FVar f) b
  -> DeferredValues d (FVar f) sf
unfinalizedDeferredValues (PerProofUnfinalized u) =
  { plonk:
      { alpha: unwrap u.alpha
      , beta: unwrap u.beta
      , gamma: unwrap u.gamma
      , zeta: unwrap u.zeta
      , perm: u.perm
      , zetaToSrsLength: u.zetaToSrsLength
      , zetaToDomainSize: u.zetaToDomainSize
      }
  , combinedInnerProduct: u.combinedInnerProduct
  , b: u.b
  , xi: unwrap u.xi
  , bulletproofChallenges: map unwrap u.bulletproofChallenges
  }
