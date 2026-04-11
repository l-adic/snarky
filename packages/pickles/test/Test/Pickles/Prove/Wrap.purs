-- | Smoke test for `Pickles.Prove.Wrap.WrapProverT` — the
-- | ReaderT-based advice monad that serves `wrapMain`'s 8 `Req.*`
-- | requests.
-- |
-- | The test constructs a zero-valued `WrapAdvice` of a concrete
-- | shape (`mpv = 2`, `slot0Width = 1`, `slot1Width = 1`,
-- | `branches = 1`) and runs a monadic computation that calls all 8
-- | advice methods. Each projection's returned value is forced into
-- | an unused binding so any runtime crash (missing typeclass
-- | instance, undefined record field, etc.) surfaces here rather
-- | than much later during a real `wrapMain` witness-generation
-- | call.
-- |
-- | This is a **wiring** test — it doesn't touch `wrap_main` or make
-- | any semantic claim about what the advice should contain. It only
-- | verifies that the record can be built, that the instance
-- | resolves, and that each method round-trips through `ask`.
module Test.Pickles.Prove.Wrap
  ( spec
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Vector as Vector
import Effect (Effect)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Pickles.Prove.Wrap (WrapAdvice, WrapProverT, runWrapProverT)
import Pickles.Types (PerProofUnfinalized(..), PointEval(..), StepAllEvals(..), WrapField, WrapOldBpChals(..), WrapPrevProofState(..), WrapProofMessages(..), WrapProofOpening(..))
import Pickles.Wrap.Advice (getEvals, getMessages, getOldBulletproofChallenges, getOpeningProof, getStepAccs, getWhichBranch, getWrapDomainIndices, getWrapProofState)
import Snarky.Circuit.DSL (F(..), UnChecked(..))
import Snarky.Circuit.DSL.SizedF (SizedF, unsafeFromField)
import Snarky.Circuit.Kimchi (Type1(..), Type2(..))
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint(..))
import Test.Spec (Spec, describe, it)

--------------------------------------------------------------------------------
-- Zero-valued helpers for the advice pieces.
--------------------------------------------------------------------------------

zeroWeierstrass :: WeierstrassAffinePoint VestaG (F WrapField)
zeroWeierstrass = WeierstrassAffinePoint { x: F zero, y: F zero }

zeroType1 :: Type1 (F WrapField)
zeroType1 = Type1 (F zero)

zeroType2 :: Type2 (F WrapField)
zeroType2 = Type2 (F zero)

-- | `SizedF 128 (F WrapField)` holding the constant zero.
-- | `unsafeFromField` is safe because the `zero` value trivially
-- | fits in 128 bits.
zeroSized128 :: SizedF 128 (F WrapField)
zeroSized128 = unsafePartial (unsafeFromField (F zero))

zeroUncheckedSized128 :: UnChecked (SizedF 128 (F WrapField))
zeroUncheckedSized128 = UnChecked zeroSized128

zeroPointEval :: PointEval (F WrapField)
zeroPointEval = PointEval { zeta: F zero, omegaTimesZeta: F zero }

zeroStepAllEvals :: StepAllEvals (F WrapField)
zeroStepAllEvals =
  StepAllEvals
    { publicEvals: zeroPointEval
    , witnessEvals: Vector.replicate zeroPointEval
    , coeffEvals: Vector.replicate zeroPointEval
    , zEvals: zeroPointEval
    , sigmaEvals: Vector.replicate zeroPointEval
    , indexEvals: Vector.replicate zeroPointEval
    , ftEval1: F zero
    }

-- | Zero `PerProofUnfinalized` in wrap-field Type2 form. Matches the
-- | shape `WrapPrevProofState.unfinalizedProofs` expects.
zeroPerProofUnfinalized
  :: forall d
   . Reflectable d Int
  => PerProofUnfinalized d (Type2 (F WrapField)) (F WrapField) Boolean
zeroPerProofUnfinalized =
  PerProofUnfinalized
    { combinedInnerProduct: zeroType2
    , b: zeroType2
    , zetaToSrsLength: zeroType2
    , zetaToDomainSize: zeroType2
    , perm: zeroType2
    , spongeDigest: F zero
    , beta: zeroUncheckedSized128
    , gamma: zeroUncheckedSized128
    , alpha: zeroUncheckedSized128
    , zeta: zeroUncheckedSized128
    , xi: zeroUncheckedSized128
    , bulletproofChallenges: Vector.replicate zeroUncheckedSized128
    , shouldFinalize: false
    }

zeroWrapPrevProofState
  :: forall mpv
   . Reflectable mpv Int
  => WrapPrevProofState mpv (Type2 (F WrapField)) (F WrapField) Boolean
zeroWrapPrevProofState =
  WrapPrevProofState
    { unfinalizedProofs: Vector.replicate zeroPerProofUnfinalized
    , messagesForNextStepProof: F zero
    }

zeroWrapOldBpChals
  :: forall s0 s1
   . Reflectable s0 Int
  => Reflectable s1 Int
  => WrapOldBpChals s0 s1 (F WrapField)
zeroWrapOldBpChals =
  WrapOldBpChals
    { slot0: Vector.replicate (Vector.replicate (F zero))
    , slot1: Vector.replicate (Vector.replicate (F zero))
    }

zeroWrapProofOpening
  :: forall n
   . Reflectable n Int
  => WrapProofOpening n (WeierstrassAffinePoint VestaG (F WrapField)) (Type1 (F WrapField))
zeroWrapProofOpening =
  WrapProofOpening
    { lr: Vector.replicate { l: zeroWeierstrass, r: zeroWeierstrass }
    , z1: zeroType1
    , z2: zeroType1
    , delta: zeroWeierstrass
    , sg: zeroWeierstrass
    }

zeroWrapProofMessages
  :: WrapProofMessages (WeierstrassAffinePoint VestaG (F WrapField))
zeroWrapProofMessages =
  WrapProofMessages
    { wComm: Vector.replicate zeroWeierstrass
    , zComm: zeroWeierstrass
    , tComm: Vector.replicate zeroWeierstrass
    }

--------------------------------------------------------------------------------
-- Concrete advice for mpv = 2, slot0 = 1, slot1 = 1.
--------------------------------------------------------------------------------

zeroAdvice :: WrapAdvice 2 1 1
zeroAdvice =
  { whichBranch: F zero
  , wrapProofState: zeroWrapPrevProofState
  , stepAccs: Vector.replicate zeroWeierstrass
  , oldBpChals: zeroWrapOldBpChals
  , evals: Vector.replicate zeroStepAllEvals
  , wrapDomainIndices: Vector.replicate (F zero)
  , openingProof: zeroWrapProofOpening
  , messages: zeroWrapProofMessages
  }

--------------------------------------------------------------------------------
-- Smoke spec — force every advice method through the reader.
--------------------------------------------------------------------------------

-- | Monadic body that calls each of the 8 advice methods. Visible
-- | type applications pin the class parameters (branches, mpv,
-- | slot0Width, slot1Width, g) — the class doesn't have a fundep
-- | from `m` to those parameters, so instance resolution needs them
-- | spelled out, matching how `Pickles.Wrap.Main.wrapMain` invokes
-- | the methods.
driveAllMethods
  :: WrapProverT 1 2 1 1 Effect Unit
driveAllMethods = do
  _wb <- getWhichBranch @1 @2 @1 @1 @VestaG unit
  _ps <- getWrapProofState @1 @2 @1 @1 @VestaG unit
  _sa <- getStepAccs @1 @2 @1 @1 @VestaG unit
  _bp <- getOldBulletproofChallenges @1 @2 @1 @1 @VestaG unit
  _ev <- getEvals @1 @2 @1 @1 @VestaG unit
  _wd <- getWrapDomainIndices @1 @2 @1 @1 @VestaG unit
  _op <- getOpeningProof @1 @2 @1 @1 @VestaG unit
  _ms <- getMessages @1 @2 @1 @1 @VestaG unit
  pure unit

spec :: Spec Unit
spec = describe "Pickles.Prove.Wrap.WrapProverT" do
  it "runWrapProverT serves every advice method from the reader" do
    liftEffect $ runWrapProverT zeroAdvice driveAllMethods
