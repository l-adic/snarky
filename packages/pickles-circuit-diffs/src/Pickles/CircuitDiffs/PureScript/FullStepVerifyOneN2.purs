module Pickles.CircuitDiffs.PureScript.FullStepVerifyOneN2
  ( compileFullStepVerifyOneN2
  ) where

-- | `full_step_verify_one_circuit` at two previous proofs: the whole mask, `sg_old` the
-- | proofs' own `sg`s.

import Prelude

import Data.Array.NonEmpty as NEA
import Effect (Effect)
import Pickles.CircuitDiffs.PureScript.Common (CompiledCircuit, stepEndo)
import Pickles.CircuitDiffs.PureScript.FullStepVerifyOne (FullStepVerifyOneInput(..), FullStepVerifyOneParams, verifyOneInputOf)
import Pickles.CircuitDiffs.PureScript.PerProofWitness (PerProofWitnessInput(..))
import Pickles.Constants (zkRowsByDefault)
import Pickles.Field (StepField)
import Pickles.FinalizeOtherProof (DomainMode(..))
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PublicInputCommit (CorrectionMode(..))
import Pickles.Step.VerifyOne (verifyOne)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Compile (compile)
import Snarky.Circuit.DSL (BoolVar, F, FVar, Snarky, UnChecked(..), const_)
import Snarky.Circuit.Kimchi (groupMapParams)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (curveParams)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Type.Proxy (Proxy(..))

fullStepVerifyOneN2Circuit
  :: forall r
   . FullStepVerifyOneParams
  -> UnChecked (FullStepVerifyOneInput 2 (FVar StepField) (BoolVar StepField) (AffinePoint (FVar StepField)))
  -> Snarky StepField (KimchiConstraint StepField) r Unit
fullStepVerifyOneN2Circuit { lagrangeAt, blindingH } (UnChecked input@(FullStepVerifyOneInput i)) = do
  let
    PerProofWitnessInput witness = i.witness
    proofMask = witness.deferredValues.branchData.proofsVerifiedMask

    domainLog2 = 16
    fopParams =
      { domains:
          NEA.singleton
            { generator: const_ (LinFFI.domainGenerator @StepField domainLog2)
            , log2: domainLog2
            }
      , shifts: map const_ (LinFFI.domainShifts @StepField domainLog2)
      , srsLengthLog2: 16
      , zkRows: zkRowsByDefault
      , endo: stepEndo
      , linearizationPoly: Linearization.pallas
      , domainMode: KnownDomainsMode
      }

    ivpParams =
      { curveParams: curveParams (Proxy @PallasG)
      , lagrangeAt
      , blindingH
      , correctionMode: PureCorrections
      , endo: stepEndo
      , groupMapParams: groupMapParams (Proxy @PallasG)
      , useOptSponge: false
      }

  _result <- verifyOne fopParams (verifyOneInputOf proofMask witness.prevSgs input) ivpParams
  pure unit

compileFullStepVerifyOneN2 :: FullStepVerifyOneParams -> Effect (CompiledCircuit StepField)
compileFullStepVerifyOneN2 params =
  compile noAdvice
    (Proxy @(UnChecked (FullStepVerifyOneInput 2 (F StepField) Boolean (AffinePoint StepField))))
    (Proxy @Unit)
    (Proxy @(KimchiConstraint StepField))
    (fullStepVerifyOneN2Circuit params)
