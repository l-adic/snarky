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
import Data.Tuple (Tuple(..))
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
import Snarky.Circuit.Kimchi (SplitField, Type1(..), Type2, groupMapParams)
import Snarky.Circuit.Kimchi.EndoScalar (toField) as EndoScalar
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

  -- VK (Plonk_verification_key_evals.typ): OCaml hlist order:
  --   sigma_comm(7), coefficients_comm(15), generic, psm, complete_add, mul, emul, endomul_scalar
  -- Note: our sigma(6) + sigmaLast(1) = OCaml's sigma_comm(7)
  vk <- label "exists_wrap_index" do
    -- sigma_comm: 7 curve points (Permuts.n = 7)
    vkSigma <- exists (dummy :: _ (Vector 7 (WeierstrassAffinePoint PallasG (F StepField))))
    -- coefficients_comm: 15 curve points (Columns.n = 15)
    vkCoeff <- exists (dummy :: _ (Vector 15 (WeierstrassAffinePoint PallasG (F StepField))))
    -- 6 individual commitments
    vkIndex <- exists (dummy :: _ (Vector 6 (WeierstrassAffinePoint PallasG (F StepField))))
    -- Split sigma into sigma(6) + sigmaLast(1) for the verifyOne input
    let vkSigma6 = unsafeCoerce (Vector.take @6 vkSigma) :: Vector 6 _
        vkSigmaLast = Vector.last vkSigma
    pure { sigma: vkSigma6, sigmaLast: vkSigmaLast, coeff: vkCoeff, index: vkIndex }

  -- Per-proof witness: allocated in OCaml hlist order to match variable indices.
  -- OCaml Per_proof_witness hlist: [statement; Wrap_proof; Proof_state; All_evals; prev_challenges; prev_sgs]
  { wComm, zComm, tComm, lr, z1, z2, delta, sg, fopState, allEvals, branchData, prevChallenges, prevSg } <- label "exists_prevs" do
    -- 1. Wrap_proof.Messages: w_comm, z_comm, t_comm (OCaml hlist order)
    wComm <- exists (dummy :: _ (Vector 15 (WeierstrassAffinePoint PallasG (F StepField))))
    zComm <- exists (dummy :: _ (WeierstrassAffinePoint PallasG (F StepField)))
    tComm <- exists (dummy :: _ (Vector 7 (WeierstrassAffinePoint PallasG (F StepField))))

    -- 2. Wrap_proof.Bulletproof: lr, z1, z2, delta, sg (OCaml hlist order)
    lr <- exists (dummy :: _ (Vector 15 { l :: WeierstrassAffinePoint PallasG (F StepField), r :: WeierstrassAffinePoint PallasG (F StepField) }))
    z1 <- exists (dummy :: _ (Type2 (SplitField (F StepField) Boolean)))
    z2 <- exists (dummy :: _ (Type2 (SplitField (F StepField) Boolean)))
    delta <- exists (dummy :: _ (WeierstrassAffinePoint PallasG (F StepField)))
    sg <- exists (dummy :: _ (WeierstrassAffinePoint PallasG (F StepField)))

    -- 3. Proof_state: allocated in OCaml's typ hlist order:
    --    Plonk.In_circuit.typ: alpha, beta, gamma, zeta, perm, zetaToSrs, zetaToDom
    --    Deferred_values: [Plonk, cip, b, xi, bpChals, branch_data]
    --    Proof_state: [Deferred_values, sponge_digest, Unit]
    psAlpha <- exists (dummy :: _ (F StepField))  -- Scalar_challenge
    psBeta <- exists (dummy :: _ (F StepField))  -- Challenge
    psGamma <- exists (dummy :: _ (F StepField))  -- Challenge
    psZeta <- exists (dummy :: _ (F StepField))  -- Scalar_challenge
    psPerm <- exists (dummy :: _ (F StepField))  -- fp (shifted Type1)
    psZetaToSrs <- exists (dummy :: _ (F StepField))  -- fp (shifted Type1)
    psZetaToDom <- exists (dummy :: _ (F StepField))  -- fp (shifted Type1)
    psCip <- exists (dummy :: _ (F StepField))  -- fp (shifted Type1)
    psB <- exists (dummy :: _ (F StepField))  -- fp (shifted Type1)
    psXi <- exists (dummy :: _ (F StepField))  -- Scalar_challenge
    psBpChals :: Vector 16 (FVar StepField) <- exists (dummy :: _ (Vector 16 (F StepField)))
    -- branch_data is LAST in Deferred_values.In_circuit.typ
    -- OCaml Branch_data.typ hlist: [proofs_verified_mask, domain_log2]
    -- Mask first (2 Booleans), then domain_log2 (field)
    bdMask0 :: BoolVar StepField <- exists (dummy :: _ Boolean)
    bdMask1 :: BoolVar StepField <- exists (dummy :: _ Boolean)
    domLog2 <- exists (dummy :: _ (F StepField))
    let branchData = { mask0: bdMask0, mask1: bdMask1, domainLog2Var: domLog2 }
    _ <- EndoScalar.toField @1 (unsafeCoerce domLog2 :: SizedF 16 (FVar StepField)) (const_ stepEndo)
    -- sponge_digest comes AFTER Deferred_values in the Proof_state.In_circuit.typ hlist
    psSponge <- exists (dummy :: _ (F StepField))
    -- Build the fopState record (after all allocations)
    let fopState =
          { plonk:
              { alpha: unsafeCoerce psAlpha :: SizedF 128 (FVar StepField)
              , beta: unsafeCoerce psBeta :: SizedF 128 (FVar StepField)
              , gamma: unsafeCoerce psGamma :: SizedF 128 (FVar StepField)
              , zeta: unsafeCoerce psZeta :: SizedF 128 (FVar StepField)
              , perm: Type1 psPerm
              , zetaToSrsLength: Type1 psZetaToSrs
              , zetaToDomainSize: Type1 psZetaToDom
              }
          , combinedInnerProduct: Type1 psCip
          , b: Type1 psB
          , xi: unsafeCoerce psXi :: SizedF 128 (FVar StepField)
          , bulletproofChallenges: unsafeCoerce psBpChals :: Vector 16 (SizedF 128 (FVar StepField))
          , spongeDigest: psSponge
          }

    -- 4. All_evals: allocated in OCaml hlist order
    --    All_evals = { evals: With_public_input, ft_eval1 }
    --    With_public_input = { public_input: (zeta, omega), evals: Evals }
    --    Evals hlist: w(15), coefficients(15), z(1), s(6), generic_sel, poseidon_sel,
    --                 complete_add_sel, mul_sel, emul_sel, endomul_scalar_sel
    --    Each eval is a pair (zeta_eval, omega_eval) — allocated as (zeta, omega)
    --    Note: OCaml's pair is (fst, snd) = (zeta, omega) in left-to-right order
    publicEvalsZ <- exists (dummy :: _ (F StepField))
    publicEvalsOZ <- exists (dummy :: _ (F StepField))
    -- Eval pairs: OCaml allocates (zeta, omega) left-to-right.
    -- PureScript record { omegaTimesZeta, zeta } RowList is o < z = wrong order.
    -- Use Tuple to force zeta-first allocation, then convert.
    let toPair (Tuple z oz) = { zeta: z, omegaTimesZeta: oz }
    witnessEvalsRaw <- exists (dummy :: _ (Vector 15 (Tuple (F StepField) (F StepField))))
    coeffEvalsRaw <- exists (dummy :: _ (Vector 15 (Tuple (F StepField) (F StepField))))
    zEvalsZ <- exists (dummy :: _ (F StepField))
    zEvalsOZ <- exists (dummy :: _ (F StepField))
    sigmaEvalsRaw <- exists (dummy :: _ (Vector 6 (Tuple (F StepField) (F StepField))))
    indexEvalsRaw <- exists (dummy :: _ (Vector 6 (Tuple (F StepField) (F StepField))))
    ftEval1 <- exists (dummy :: _ (F StepField))
    let allEvals =
          { ftEval1
          , publicEvals: { zeta: publicEvalsZ, omegaTimesZeta: publicEvalsOZ }
          , witnessEvals: map toPair witnessEvalsRaw
          , coeffEvals: map toPair coeffEvalsRaw
          , zEvals: { zeta: zEvalsZ, omegaTimesZeta: zEvalsOZ }
          , sigmaEvals: map toPair sigmaEvalsRaw
          , indexEvals: map toPair indexEvalsRaw
          }

    -- 5. prev_challenges
    prevChallenges <- exists (dummy :: _ (UnChecked (Vector 16 (F StepField))))

    -- 6. prev_sgs (curve check comes AFTER all of the above)
    prevSg <- exists (dummy :: _ (WeierstrassAffinePoint PallasG (F StepField)))

    pure { wComm, zComm, tComm, lr, z1, z2, delta, sg, fopState, allEvals, branchData, prevChallenges, prevSg }

  -- Unfinalized proof: OCaml's Unfinalized.typ checks:
  --   5 × Other_field.check (forbidden shifted values) on the Type2 shifted values
  --   1 × Boolean.typ check on shouldFinalize
  --   Challenges/digest/bpChallenges: plain Field.typ, NO check
  unfinalized <- label "exists_unfinalized" $ exists (dummy :: _ { deferredValues ::
                     { plonk ::
                         { alpha :: UnChecked (SizedF 128 (F StepField))  -- Challenge: no check
                         , beta :: UnChecked (SizedF 128 (F StepField))
                         , gamma :: UnChecked (SizedF 128 (F StepField))
                         , zeta :: UnChecked (SizedF 128 (F StepField))
                         , perm :: Type2 (SplitField (F StepField) Boolean)  -- Other_field: checked
                         , zetaToSrsLength :: Type2 (SplitField (F StepField) Boolean)
                         , zetaToDomainSize :: Type2 (SplitField (F StepField) Boolean)
                         }
                     , combinedInnerProduct :: Type2 (SplitField (F StepField) Boolean)
                     , b :: Type2 (SplitField (F StepField) Boolean)
                     , xi :: UnChecked (SizedF 128 (F StepField))  -- Scalar_challenge: no check
                     , bulletproofChallenges :: UnChecked (Vector 15 (SizedF 128 (F StepField)))  -- no check
                     }
                 , shouldFinalize :: Boolean  -- Boolean.typ: checked
                 , claimedDigest :: UnChecked (F StepField)  -- Digest: no check
                 })

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

    -- Unwrap UnChecked wrappers where needed
    UnChecked prevChallenges' = prevChallenges
    branchDomainLog2 = branchData.domainLog2Var

    input =
      { appState: prevAppState
      , wComm: map unwrapPt wComm
      , zComm: unwrapPt zComm
      , tComm: map unwrapPt tComm
      , lr: map (\r -> { l: unwrapPt r.l, r: unwrapPt r.r }) lr
      , z1
      , z2
      , delta: unwrapPt delta
      , sg: unwrapPt sg
      , proofState:
          { plonk: fopState.plonk
          , combinedInnerProduct: fopState.combinedInnerProduct
          , b: fopState.b
          , xi: fopState.xi
          , bulletproofChallenges: fopState.bulletproofChallenges
          , spongeDigest: fopState.spongeDigest
          }
      , allEvals
      , prevChallenges: prevChallenges' :< Vector.nil
      , prevSgs: unwrapPt prevSg :< Vector.nil
      , unfinalized:
          let dv = unfinalized.deferredValues
              UnChecked bpChals = dv.bulletproofChallenges
              UnChecked claimedDigest = unfinalized.claimedDigest
          in
          { deferredValues:
              { plonk:
                  { alpha: unsafeCoerce dv.plonk.alpha  -- unwrap UnChecked SizedF
                  , beta: unsafeCoerce dv.plonk.beta
                  , gamma: unsafeCoerce dv.plonk.gamma
                  , zeta: unsafeCoerce dv.plonk.zeta
                  , perm: dv.plonk.perm
                  , zetaToSrsLength: dv.plonk.zetaToSrsLength
                  , zetaToDomainSize: dv.plonk.zetaToDomainSize
                  }
              , combinedInnerProduct: dv.combinedInnerProduct
              , b: dv.b
              , xi: unsafeCoerce dv.xi
              , bulletproofChallenges: bpChals
              }
          , shouldFinalize: unsafeCoerce unfinalized.shouldFinalize :: BoolVar StepField
          , claimedDigest
          }
      , messagesForNextWrapProof
      , mustVerify
      , branchData: { mask0: unsafeCoerce branchData.mask0 :: FVar StepField
                    , mask1: unsafeCoerce branchData.mask1 :: FVar StepField
                    , domainLog2Var: branchDomainLog2
                    }
      , proofMask: branchData.mask1 :< Vector.nil
      , vkComms
      , sgOld: constDummySg :< unwrapPt prevSg :< Vector.nil
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
  { expandedChallenges, result: _ } <- label "prevs_verified" do
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
    let sgPt = unwrapPt sg
    s2 <- Sponge.absorb sgPt.x s1
    s3 <- Sponge.absorb sgPt.y s2
    -- OCaml's FOP returns compute_challenges ~scalar bp_challenges = expanded via to_field_checked.
    -- These are compound CVars (scale a endo + b), not simple Vars.
    sAfterProofs <- foldM (\s c -> Sponge.absorb c s) s3 expandedChallenges

    -- 4. Squeeze
    { result: digest } <- Sponge.squeeze sAfterProofs
    pure digest

  pure unit

compileStepMainSimpleChain :: StepMainSimpleChainParams -> CompiledCircuit StepField
compileStepMainSimpleChain params =
  compilePure (Proxy @(Vector InputSize (F StepField))) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    (\inputs -> stepMainSimpleChainCircuit params inputs)
    Kimchi.initialState
