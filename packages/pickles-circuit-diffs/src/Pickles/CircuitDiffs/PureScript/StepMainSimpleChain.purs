module Pickles.CircuitDiffs.PureScript.StepMainSimpleChain
  ( compileStepMainSimpleChain
  , StepMainSimpleChainParams
  ) where

-- | step_main circuit for the Simple_Chain inductive rule (N1, 1 previous proof).
-- |
-- | Mirrors OCaml step_main.ml: the InductiveRule provides `main`, step_main
-- | allocates witnesses via `exists`, runs verify_one, and hashes messages.
-- |
-- | Reference: mina/src/lib/crypto/pickles/step_main.ml
-- |            mina/src/lib/crypto/pickles/dump_circuit_impl.ml (step_main_simple_chain)

import Prelude

import Data.Foldable (foldM)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, asSizedF128, dummyWrapSg, stepEndo)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PublicInputCommit (CorrectionMode(..), LagrangeBase)
import Pickles.Sponge (initialSpongeCircuit)
import Pickles.Step.VerifyOne (VerifyOneInput, verifyOne)
import Pickles.Types (StepField)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, UnChecked(..), assertAny_, assert_, const_, equals_, exists, label, not_)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.Kimchi (SplitField, Type1, Type2, groupMapParams)
import Snarky.Circuit.RandomOracle.Sponge as Sponge
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

type StepMainSimpleChainParams =
  { lagrangeComms :: Array (LagrangeBase StepField)
  , blindingH :: AffinePoint (F StepField)
  }

-------------------------------------------------------------------------------
-- | Inductive Rule abstraction
-- |
-- | Mirrors OCaml's Inductive_rule.t. The rule's `main` receives the
-- | app_state and returns previous proof statements (public_input per prev
-- | proof + proof_must_verify flags).
-- |
-- | For Simple_Chain (N1): 1 previous proof whose public_input is a single field.
-------------------------------------------------------------------------------

-- | Output of an inductive rule's `main` function.
-- | `prevPublicInputs` are the public inputs to previous proofs.
-- | `proofMustVerify` flags indicate which proofs actually need verification.
type RuleOutput n f =
  { prevPublicInputs :: Vector n (FVar f)
  , proofMustVerify :: Vector n (BoolVar f)
  }

-- | An inductive rule: given the circuit's own public input (app_state),
-- | produce the previous proof statements.
type InductiveRule n f c t m =
  FVar f -> Snarky c t m (RuleOutput n f)

-------------------------------------------------------------------------------
-- | Simple_Chain rule
-- |
-- | Reference: dump_circuit_impl.ml:4390-4413
-- |   exists prev; is_base_case = (0 == self); proof_must_verify = not is_base_case;
-- |   self_correct = (1+prev == self); Assert.any [self_correct, is_base_case]
-------------------------------------------------------------------------------

simpleChainRule
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => InductiveRule 1 StepField (KimchiConstraint StepField) t m
simpleChainRule appState = do
  prev <- exists (pure (zero :: F StepField))
  -- proof = exists (Typ.prover_value ()) — no circuit effect
  isBaseCase <- equals_ (const_ zero) appState
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) appState
  assertAny_ [ selfCorrect, isBaseCase ]
  pure
    { prevPublicInputs: prev :< Vector.nil
    , proofMustVerify: proofMustVerify :< Vector.nil
    }

-------------------------------------------------------------------------------
-- | Helpers
-------------------------------------------------------------------------------

-- | Unwrap WeierstrassAffinePoint to plain AffinePoint for use in verify_one.
unwrapPt :: WeierstrassAffinePoint PallasG (FVar StepField) -> AffinePoint (FVar StepField)
unwrapPt (WeierstrassAffinePoint pt) = pt

-------------------------------------------------------------------------------
-- | Number of public inputs for the Step.Statement output (N1)
-------------------------------------------------------------------------------
type InputSize = 34

-------------------------------------------------------------------------------
-- | step_main circuit
-------------------------------------------------------------------------------

stepMainSimpleChainCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => StepMainSimpleChainParams
  -> Vector InputSize (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
stepMainSimpleChainCircuit { lagrangeComms, blindingH } _publicInputs = do

  ---------------------------------------------------------------------------
  -- 1. exists input_typ (app_state)
  ---------------------------------------------------------------------------
  appState <- exists (pure (zero :: F StepField))

  ---------------------------------------------------------------------------
  -- 2. rule_main
  ---------------------------------------------------------------------------
  { prevPublicInputs, proofMustVerify } <- label "rule_main" $ simpleChainRule appState

  let
    prevAppState = Vector.head prevPublicInputs
    mustVerify = Vector.head proofMustVerify

  ---------------------------------------------------------------------------
  -- 3. exists: allocate all witness data using typed exists
  --    OCaml: dlog_plonk_index, prevs, unfinalized, messages, etc.
  --
  --    `dummy` provides a never-evaluated prover value. During compilation
  --    `exists` only allocates variables + runs CheckedType; the prover
  --    computation is not executed (Effect instance throws).
  ---------------------------------------------------------------------------
  let
    -- Never-evaluated prover value for exists. During compilation exists
    -- only allocates variables + runs CheckedType; the prover value is not read.
    dummy :: forall a b. Applicative b => b a
    dummy = pure (unsafeCoerce unit)

  -- VK (Plonk_verification_key_evals.typ with Inner_curve.typ)
  -- On-curve checks happen automatically via WeierstrassAffinePoint CheckedType
  vk <- exists (dummy :: _ { sigma :: Vector 6 (WeierstrassAffinePoint PallasG (F StepField))
         , sigmaLast :: WeierstrassAffinePoint PallasG (F StepField)
         , coeff :: Vector 15 (WeierstrassAffinePoint PallasG (F StepField))
         , index :: Vector 6 (WeierstrassAffinePoint PallasG (F StepField))
         })

  -- Per-proof witness: commitments (curve-checked)
  comms <- exists (dummy :: _ { wComm :: Vector 15 (WeierstrassAffinePoint PallasG (F StepField))
           , zComm :: WeierstrassAffinePoint PallasG (F StepField)
           , tComm :: Vector 7 (WeierstrassAffinePoint PallasG (F StepField))
           })

  -- Per-proof witness: opening (curve points checked, z1/z2 unchecked)
  opening <- exists (dummy :: _ { lr :: Vector 15 { l :: WeierstrassAffinePoint PallasG (F StepField), r :: WeierstrassAffinePoint PallasG (F StepField) }
             , z1 :: UnChecked (Type2 (SplitField (F StepField) Boolean))
             , z2 :: UnChecked (Type2 (SplitField (F StepField) Boolean))
             , delta :: WeierstrassAffinePoint PallasG (F StepField)
             , sg :: WeierstrassAffinePoint PallasG (F StepField)
             })

  -- Per-proof proof_state (Type1 deferred values — unchecked, OCaml uses typ_unchecked)
  fopState <- exists (dummy :: _ (UnChecked { plonk ::
                  { alpha :: SizedF 128 (F StepField)
                  , beta :: SizedF 128 (F StepField)
                  , gamma :: SizedF 128 (F StepField)
                  , zeta :: SizedF 128 (F StepField)
                  , perm :: Type1 (F StepField)
                  , zetaToSrsLength :: Type1 (F StepField)
                  , zetaToDomainSize :: Type1 (F StepField)
                  }
              , combinedInnerProduct :: Type1 (F StepField)
              , b :: Type1 (F StepField)
              , xi :: SizedF 128 (F StepField)
              , bulletproofChallenges :: Vector 16 (SizedF 128 (F StepField))
              , spongeDigest :: F StepField
              }))

  -- Per-proof allEvals (unchecked)
  allEvals <- exists (dummy :: _ (UnChecked { ftEval1 :: F StepField
              , publicEvals :: { zeta :: F StepField, omegaTimesZeta :: F StepField }
              , witnessEvals :: Vector 15 { zeta :: F StepField, omegaTimesZeta :: F StepField }
              , coeffEvals :: Vector 15 { zeta :: F StepField, omegaTimesZeta :: F StepField }
              , zEvals :: { zeta :: F StepField, omegaTimesZeta :: F StepField }
              , sigmaEvals :: Vector 6 { zeta :: F StepField, omegaTimesZeta :: F StepField }
              , indexEvals :: Vector 6 { zeta :: F StepField, omegaTimesZeta :: F StepField }
              }))

  -- Previous challenges + sg (curve-checked)
  prevChals <- exists (dummy :: _ { challenges :: UnChecked (Vector 16 (F StepField))
               , sg :: WeierstrassAffinePoint PallasG (F StepField)
               })

  -- Unfinalized proof (unchecked — OCaml uses typ_unchecked for Other_field)
  unfinalized <- exists (dummy :: _ (UnChecked { deferredValues ::
                     { plonk ::
                         { alpha :: SizedF 128 (F StepField)
                         , beta :: SizedF 128 (F StepField)
                         , gamma :: SizedF 128 (F StepField)
                         , zeta :: SizedF 128 (F StepField)
                         , perm :: Type2 (SplitField (F StepField) Boolean)
                         , zetaToSrsLength :: Type2 (SplitField (F StepField) Boolean)
                         , zetaToDomainSize :: Type2 (SplitField (F StepField) Boolean)
                         }
                     , combinedInnerProduct :: Type2 (SplitField (F StepField) Boolean)
                     , b :: Type2 (SplitField (F StepField) Boolean)
                     , xi :: SizedF 128 (F StepField)
                     , bulletproofChallenges :: Vector 15 (SizedF 128 (F StepField))
                     }
                 , shouldFinalize :: Boolean
                 , claimedDigest :: F StepField
                 }))

  -- Branch data (unchecked)
  branchData <- exists (dummy :: _ (UnChecked { mask0 :: F StepField, mask1 :: F StepField, domainLog2Var :: F StepField }))

  -- Messages for next wrap proof
  messagesForNextWrapProof <- exists (dummy :: _ (F StepField))

  ---------------------------------------------------------------------------
  -- 4. Build verify_one input from allocated witnesses
  ---------------------------------------------------------------------------
  let
    constDummySg :: AffinePoint (FVar StepField)
    constDummySg = { x: const_ dummyWrapSg.x, y: const_ dummyWrapSg.y }

    vkComms =
      { sigma: map unwrapPt vk.sigma
      , sigmaLast: unwrapPt vk.sigmaLast
      , coeff: map unwrapPt vk.coeff
      , index: map unwrapPt vk.index
      }

    -- Unwrap UnChecked wrappers
    UnChecked fopState' = fopState
    UnChecked allEvals' = allEvals
    UnChecked unfinalized' = unfinalized
    UnChecked branchData' = branchData
    UnChecked prevChallenges' = prevChals.challenges

    input =
      { appState: prevAppState
      , wComm: map unwrapPt comms.wComm
      , zComm: unwrapPt comms.zComm
      , tComm: map unwrapPt comms.tComm
      , lr: map (\r -> { l: unwrapPt r.l, r: unwrapPt r.r }) opening.lr
      , z1: unsafeCoerce opening.z1 -- UnChecked Type2 → Type2
      , z2: unsafeCoerce opening.z2
      , delta: unwrapPt opening.delta
      , sg: unwrapPt opening.sg
      , proofState:
          { plonk: fopState'.plonk
          , combinedInnerProduct: fopState'.combinedInnerProduct
          , b: fopState'.b
          , xi: fopState'.xi
          , bulletproofChallenges: fopState'.bulletproofChallenges
          , spongeDigest: fopState'.spongeDigest
          }
      , allEvals: allEvals'
      , prevChallenges: prevChallenges' :< Vector.nil
      , prevSgs: unwrapPt prevChals.sg :< Vector.nil
      , unfinalized:
          { deferredValues: unfinalized'.deferredValues
          , shouldFinalize: unsafeCoerce unfinalized'.shouldFinalize :: BoolVar StepField
          , claimedDigest: unfinalized'.claimedDigest
          }
      , messagesForNextWrapProof
      , mustVerify
      , branchData: branchData'
      , proofMask: (unsafeCoerce branchData'.mask1 :: BoolVar StepField) :< Vector.nil
      , vkComms
      , sgOld: constDummySg :< unwrapPt prevChals.sg :< Vector.nil
      }

    domainLog2 = 16
    fopParams =
      { domain:
          { generator: const_ (LinFFI.domainGenerator @StepField domainLog2)
          , shifts: map const_ (LinFFI.domainShifts @StepField domainLog2)
          }
      , domainLog2
      , srsLengthLog2: 16
      , endo: stepEndo
      , linearizationPoly: Linearization.pallas
      }

    ivpParams =
      { curveParams: curveParams (Proxy @PallasG)
      , lagrangeComms
      , blindingH
      , correctionMode: PureCorrections
      , endo: stepEndo
      , groupMapParams: groupMapParams (Proxy @PallasG)
      , useOptSponge: false
      }

  ---------------------------------------------------------------------------
  -- 5. verify_one + Assert.all (inside prevs_verified label)
  ---------------------------------------------------------------------------
  { challenges, result: _ } <- label "prevs_verified" do
    res <- verifyOne fopParams input ivpParams
    -- Boolean.Assert.all [v] for N1 = assert_ v
    assert_ res.result
    pure res

  ---------------------------------------------------------------------------
  -- 6. Outer hash: hash_messages_for_next_step_proof
  --    OCaml: sponge_after_index(VK) → absorb app_state → absorb sg + bp_challenges → squeeze
  ---------------------------------------------------------------------------
  _outerDigest <- label "hash_messages_for_next_step_proof" do
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

    -- 2. Absorb app_state (for Simple_Chain: 1 field via var_to_fields)
    s1 <- Sponge.absorb appState spongeAfterIndex

    -- 3. For each proof: absorb sg (challenge_polynomial_commitment) + bp_challenges
    let sgPt = unwrapPt opening.sg
    s2 <- Sponge.absorb sgPt.x s1
    s3 <- Sponge.absorb sgPt.y s2
    sAfterProofs <- foldM (\s c -> Sponge.absorb (unsafeCoerce c :: FVar StepField) s) s3 challenges

    -- 4. Squeeze
    { result: digest } <- Sponge.squeeze sAfterProofs
    pure digest

  pure unit

compileStepMainSimpleChain :: StepMainSimpleChainParams -> CompiledCircuit StepField
compileStepMainSimpleChain params =
  compilePure (Proxy @(Vector InputSize (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> stepMainSimpleChainCircuit params inputs)
    Kimchi.initialState
