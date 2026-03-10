-- | Circuit JSON comparison test for FinalizeOtherProof.
-- |
-- | Tests the library's `finalizeOtherProofCircuit` by compiling it with a
-- | thin wrapper that unpacks a flat 151-element public input vector into the
-- | typed record structure the library expects, then compares the resulting
-- | constraint system against the OCaml fixture.
-- |
-- | OCaml reference: dump_circuit_impl.ml:1090-1226 (input layout),
-- |                  step_verifier.ml:828-1165 (computation)
module Test.Pickles.CircuitJson (spec, CompiledCircuit, compileIvpWrap, compileBulletReduce, compileBulletReduceOne, compileXhat, compileFtcomm, compileCombinePoly, compileGroupMap) where

import Prelude

import Data.Array (concatMap, filter)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (getFinite)
import Data.Foldable (foldl, for_, intercalate)
import Data.Int (pow)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust, fromMaybe)
import Data.Set as Set
import Data.Traversable (for)
import Data.Tuple (Tuple(..), snd)
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Foreign (MultipleErrors)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Partial.Unsafe (unsafePartial)
import Pickles.FtComm (ftComm)
import Pickles.IPA (bCorrectCircuit, bulletReduceCircuit, combinePolynomials)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PackedStatement (fromPackedTuple)
import Pickles.PublicInputCommit (publicInputCommit)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.ChallengeDigest as ChallengeDigest
import Pickles.Step.Domain (pow2PowSquare)
import Pickles.Step.FinalizeOtherProof (finalizeOtherProofCircuit)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Types (StepField, WrapField)
import Pickles.Verify (incrementallyVerifyProof)
import Pickles.Wrap.FinalizeOtherProof (wrapFinalizeOtherProofCircuit)
import Pickles.Wrap.OtherField as WrapOtherField
import Safe.Coerce (coerce)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (compilePure)
import Snarky.Backend.Kimchi.CircuitJson (CircuitData, CircuitGateData, GateDiff, circuitToJson, diffCircuits, extractCachedConstants, formatGate, readCachedConstantsJson, readCircuitJson)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Backend.Kimchi.Impl.Vesta (vestaCrsCreate)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, SizedF, Snarky, assertEq, assertEqual_, const_)
import Snarky.Circuit.Kimchi (SplitField(..), Type1(..), Type2(..), addComplete, endo, endoInv, fromShiftedType1Circuit, groupMapCircuit, groupMapParams, toField)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (class PrimeField, class SerdeHex, EndoScalar(..), curveParams, endoScalar, generator, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Pickles.ProofFFI (pallasSrsBlindingGenerator, pallasSrsLagrangeCommitments)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

-------------------------------------------------------------------------------
-- | Constants
-------------------------------------------------------------------------------

-- | Domain log2 for the Step circuit (matches OCaml: Pow_2_roots_of_unity 16)
domainLog2 :: Int
domainLog2 = 16

-- | Endo coefficient for scalar challenge expansion (= Wrap_inner_curve.scalar)
stepEndo :: StepField
stepEndo = let EndoScalar e = endoScalar @Vesta.BaseField @StepField in e

-- | srs_length_log2 = Max_degree.step_log2 = Nat.to_int Tick.Rounds.n = 16
srsLengthLog2 :: Int
srsLengthLog2 = 16

-- | Domain log2 for the Wrap circuit (matches OCaml: Pow_2_roots_of_unity 15)
wrapDomainLog2 :: Int
wrapDomainLog2 = 15

-- | Endo coefficient for Wrap challenge expansion (= Step_inner_curve.scalar = Pallas.endo_scalar)
wrapEndo :: WrapField
wrapEndo = let EndoScalar e = endoScalar @Pallas.BaseField @WrapField in e

-- | Wrap srs_length_log2 = Nat.to_int Tock.Rounds.n = 15
wrapSrsLengthLog2 :: Int
wrapSrsLengthLog2 = 15

-------------------------------------------------------------------------------
-- | Input parsing helpers
-------------------------------------------------------------------------------

-- | Unsafe array index into a Vector (for compile-time circuit building only)
unsafeIdx :: forall n f. Vector n f -> Int -> f
unsafeIdx v i =
  let
    arr = Vector.toUnfoldable v :: Array f
  in
    unsafePartial $ Array.unsafeIndex arr i

-- | Treat a field variable as a 128-bit scalar challenge (for circuit compilation)
asSizedF128 :: forall f. FVar f -> SizedF 128 (FVar f)
asSizedF128 = unsafeCoerce

-------------------------------------------------------------------------------
-- | Full FinalizeOtherProof Step circuit
-- |
-- | Thin wrapper that unpacks a flat 151-input vector into the typed records
-- | expected by the library's `finalizeOtherProofCircuit`, then calls it.
-- |
-- | Input layout (151 fields):
-- |   0: alpha, 1: beta, 2: gamma, 3: zeta (scalar challenges)
-- |   4: zeta_to_srs_length, 5: zeta_to_domain_size, 6: perm (Type1)
-- |   7: combined_inner_product, 8: b (Type1)
-- |   9: xi (scalar_challenge inner)
-- |   10-25: bulletproof_challenges[0..15]
-- |   26-27: proofs_verified_mask[0..1]
-- |   28: domain_log2
-- |   29-30: public_input (zeta, zetaw)
-- |   31-60: w[0..14] pairs, 61-90: coeff[0..14] pairs
-- |   91-92: z pair, 93-104: s[0..5] pairs, 105-116: selectors[0..5] pairs
-- |   117: ft_eval1
-- |   118-133: prev_challenges[0], 134-149: prev_challenges[1]
-- |   150: sponge_digest_before_evaluations
-------------------------------------------------------------------------------

finalizeOtherProofStepCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 151 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
finalizeOtherProofStepCircuit inputs = do
  let
    at i = unsafeIdx inputs i

    -- PlonkInCircuit: scalar challenges + shifted values
    plonk =
      { alpha: asSizedF128 (at 0)
      , beta: asSizedF128 (at 1)
      , gamma: asSizedF128 (at 2)
      , zeta: asSizedF128 (at 3)
      , zetaToSrsLength: Type1 (at 4)
      , zetaToDomainSize: Type1 (at 5)
      , perm: Type1 (at 6)
      }

    -- DeferredValues
    deferredValues =
      { plonk
      , combinedInnerProduct: Type1 (at 7)
      , b: Type1 (at 8)
      , xi: asSizedF128 (at 9)
      , bulletproofChallenges:
          (Vector.generate \j -> asSizedF128 (at (10 + getFinite j))) :: Vector 16 _
      }

    -- UnfinalizedProof
    unfinalized =
      { deferredValues
      , shouldFinalize: coerce (const_ one :: FVar StepField)
      , spongeDigestBeforeEvaluations: at 150
      }

    -- Mask (2 booleans)
    mask :: Vector 2 (BoolVar StepField)
    mask = Vector.generate \j -> coerce (at (26 + getFinite j))

    -- AllEvals (polynomial evaluations witness)
    allEvals =
      { ftEval1: at 117
      , publicEvals: { zeta: at 29, omegaTimesZeta: at 30 }
      , witnessEvals:
          ( Vector.generate \j ->
              { zeta: at (31 + 2 * getFinite j)
              , omegaTimesZeta: at (31 + 2 * getFinite j + 1)
              }
          ) :: Vector 15 _
      , coeffEvals:
          ( Vector.generate \j ->
              { zeta: at (61 + 2 * getFinite j)
              , omegaTimesZeta: at (61 + 2 * getFinite j + 1)
              }
          ) :: Vector 15 _
      , zEvals: { zeta: at 91, omegaTimesZeta: at 92 }
      , sigmaEvals:
          ( Vector.generate \j ->
              { zeta: at (93 + 2 * getFinite j)
              , omegaTimesZeta: at (93 + 2 * getFinite j + 1)
              }
          ) :: Vector 6 _
      , indexEvals:
          ( Vector.generate \j ->
              { zeta: at (105 + 2 * getFinite j)
              , omegaTimesZeta: at (105 + 2 * getFinite j + 1)
              }
          ) :: Vector 6 _
      }

    witness = { allEvals }

    -- Previous challenges (2 proofs × 16 challenges)
    prevChallenges :: Vector 2 (Vector 16 (FVar StepField))
    prevChallenges = Vector.generate \j ->
      Vector.generate \k ->
        at (118 + 16 * getFinite j + getFinite k)

    -- Build input record
    input =
      { unfinalized
      , witness
      , mask
      , prevChallenges
      , domainLog2Var: at 28
      }

    -- Build compile-time params
    params =
      { domain:
          { generator: LinFFI.domainGenerator @StepField domainLog2
          , shifts: LinFFI.domainShifts @StepField domainLog2
          }
      , domainLog2
      , srsLengthLog2
      , endo: stepEndo
      , linearizationPoly: Linearization.pallas
      }

  void $ finalizeOtherProofCircuit StepOtherField.fopShiftOps params input

-------------------------------------------------------------------------------
-- | Full FinalizeOtherProof Wrap circuit
-- |
-- | Thin wrapper that unpacks a flat 148-input vector into the typed records
-- | expected by the library's `wrapFinalizeOtherProofCircuit`, then calls it.
-- |
-- | Input layout (148 fields):
-- |   0: alpha, 1: beta, 2: gamma, 3: zeta (scalar challenges)
-- |   4: zeta_to_srs_length, 5: zeta_to_domain_size, 6: perm (Type2 shifted)
-- |   7: combined_inner_product, 8: b (Type2 shifted)
-- |   9: xi (scalar_challenge inner)
-- |   10-25: bulletproof_challenges[0..15]
-- |   26-27: public_input (zeta, zetaw)
-- |   28-57: w[0..14] pairs, 58-87: coeff[0..14] pairs
-- |   88-89: z pair, 90-101: s[0..5] pairs, 102-113: selectors[0..5] pairs
-- |   114: ft_eval1
-- |   115-146: prev_challenges (2×16)
-- |   147: sponge_digest_before_evaluations
-------------------------------------------------------------------------------

finalizeOtherProofWrapCircuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => Vector 148 (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
finalizeOtherProofWrapCircuit inputs = do
  let
    at i = unsafeIdx inputs i

    -- PlonkInCircuit: scalar challenges + Type2 shifted values
    plonk =
      { alpha: asSizedF128 (at 0)
      , beta: asSizedF128 (at 1)
      , gamma: asSizedF128 (at 2)
      , zeta: asSizedF128 (at 3)
      , zetaToSrsLength: Type2 (at 4)
      , zetaToDomainSize: Type2 (at 5)
      , perm: Type2 (at 6)
      }

    -- DeferredValues (no mask, no domainLog2)
    deferredValues =
      { plonk
      , combinedInnerProduct: Type2 (at 7)
      , b: Type2 (at 8)
      , xi: asSizedF128 (at 9)
      , bulletproofChallenges:
          (Vector.generate \j -> asSizedF128 (at (10 + getFinite j))) :: Vector 16 _
      }

    -- UnfinalizedProof
    unfinalized =
      { deferredValues
      , shouldFinalize: coerce (const_ one :: FVar WrapField)
      , spongeDigestBeforeEvaluations: at 147
      }

    -- AllEvals (same structure as Step, offset by 26 instead of 29)
    allEvals =
      { ftEval1: at 114
      , publicEvals: { zeta: at 26, omegaTimesZeta: at 27 }
      , witnessEvals:
          ( Vector.generate \j ->
              { zeta: at (28 + 2 * getFinite j)
              , omegaTimesZeta: at (28 + 2 * getFinite j + 1)
              }
          ) :: Vector 15 _
      , coeffEvals:
          ( Vector.generate \j ->
              { zeta: at (58 + 2 * getFinite j)
              , omegaTimesZeta: at (58 + 2 * getFinite j + 1)
              }
          ) :: Vector 15 _
      , zEvals: { zeta: at 88, omegaTimesZeta: at 89 }
      , sigmaEvals:
          ( Vector.generate \j ->
              { zeta: at (90 + 2 * getFinite j)
              , omegaTimesZeta: at (90 + 2 * getFinite j + 1)
              }
          ) :: Vector 6 _
      , indexEvals:
          ( Vector.generate \j ->
              { zeta: at (102 + 2 * getFinite j)
              , omegaTimesZeta: at (102 + 2 * getFinite j + 1)
              }
          ) :: Vector 6 _
      }

    witness = { allEvals }

    -- Previous challenges (2 proofs × 16 challenges)
    prevChallenges :: Vector 2 (Vector 16 (FVar WrapField))
    prevChallenges = Vector.generate \j ->
      Vector.generate \k ->
        at (115 + 16 * getFinite j + getFinite k)

    -- Build input record (no mask, no domainLog2Var)
    input =
      { unfinalized
      , witness
      , prevChallenges
      }

    -- Build compile-time params
    params =
      { domain:
          { generator: LinFFI.domainGenerator @WrapField wrapDomainLog2
          , shifts: LinFFI.domainShifts @WrapField wrapDomainLog2
          }
      , domainLog2: wrapDomainLog2
      , srsLengthLog2: wrapSrsLengthLog2
      , endo: wrapEndo
      , linearizationPoly: Linearization.vesta
      }

  void $ wrapFinalizeOtherProofCircuit params input

-------------------------------------------------------------------------------
-- | pow2PowSquare sub-circuit
-- |
-- | 1 input → compute x^(2^16) via Square constraints.
-- | OCaml reference: dump_circuit_impl.ml pow2_pow_circuit
-------------------------------------------------------------------------------

pow2PowCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 1 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
pow2PowCircuit inputs = do
  let at i = unsafeIdx inputs i
  void $ pow2PowSquare (at 0) 16

-------------------------------------------------------------------------------
-- | bCorrect sub-circuit
-- |
-- | 20 inputs: 0-15 raw scalar challenges, 16 zeta, 17 zetaw, 18 r,
-- | 19 claimedB (Type1 shifted).
-- | OCaml reference: dump_circuit_impl.ml b_correct_circuit
-------------------------------------------------------------------------------

bCorrectTestCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 20 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
bCorrectTestCircuit inputs = do
  let
    at i = unsafeIdx inputs i
    endoVar = const_ stepEndo :: FVar StepField

    rawChallenges :: Vector 16 (SizedF 128 (FVar StepField))
    rawChallenges = Vector.generate \j -> asSizedF128 (at (getFinite j))
  -- Expand challenges in reverse order (OCaml right-to-left evaluation)
  expandedRev <- for (Vector.reverse rawChallenges) \c -> toField @8 c endoVar
  let expanded = Vector.reverse expandedRev
  void $ bCorrectCircuit
    { challenges: expanded
    , zeta: at 16
    , zetaOmega: at 17
    , evalscale: at 18
    , expectedB: fromShiftedType1Circuit (Type1 (at 19))
    }

-------------------------------------------------------------------------------
-- | challengeDigest sub-circuit
-- |
-- | 34 inputs: 0-1 mask booleans, 2-33 prev_challenges (2×16 scalar challenges).
-- | OCaml reference: dump_circuit_impl.ml challenge_digest_circuit
-------------------------------------------------------------------------------

challengeDigestTestCircuit
  :: forall t m
   . CircuitM StepField (KimchiConstraint StepField) t m
  => Vector 34 (FVar StepField)
  -> Snarky (KimchiConstraint StepField) t m Unit
challengeDigestTestCircuit inputs = do
  let
    at i = unsafeIdx inputs i

    mask :: Vector 2 (BoolVar StepField)
    mask = Vector.generate \j -> coerce (at (getFinite j))

    oldChallenges :: Vector 2 (Vector 16 (SizedF 128 (FVar StepField)))
    oldChallenges = Vector.generate \j ->
      Vector.generate \k -> asSizedF128 (at (2 + 16 * getFinite j + getFinite k))
  void $ ChallengeDigest.challengeDigestCircuit { mask, oldChallenges }

-------------------------------------------------------------------------------
-- | IVP Wrap circuit (incrementally_verify_proof via verify)
-- |
-- | Thin wrapper that unpacks a flat 177-input vector into the typed structures
-- | expected by the library's `verify`, then calls it.
-- |
-- | This tests the Wrap circuit's IVP subcircuit in isolation:
-- |   1. publicInputCommit (x_hat MSM over PackedStepPublicInput)
-- |   2. spongeTranscriptCircuit (Fq-sponge deriving alpha/beta/gamma/zeta)
-- |   3. ftComm (FT polynomial commitment)
-- |   4. checkBulletproof (IPA opening proof verification)
-- |   5. verify assertions (digest + bulletproof challenge matching)
-- |
-- | Input layout (177 fields):
-- |   PackedStepPublicInput (n=1, dw=15), OCaml to_data order:
-- |     0-1:   cip (Type2 SplitField: sDiv2, sOdd)
-- |     2-3:   b
-- |     4-5:   zetaToSrsLength
-- |     6-7:   zetaToDomainSize
-- |     8-9:   perm
-- |     10:    sponge_digest_before_evaluations
-- |     11-12: beta, gamma (SizedF 128)
-- |     13-15: alpha, zeta, xi (SizedF 128)
-- |     16-30: bulletproof_challenges[0..14]
-- |     31:    should_finalize
-- |     32:    messages_for_next_step_proof
-- |     33:    messages_for_next_wrap_proof[0]
-- |   IVP DeferredValues (Type1 shifted, d=16):
-- |     34-37: alpha, beta, gamma, zeta (SizedF 128)
-- |     38-40: perm, zetaToSrsLength, zetaToDomainSize (Type1)
-- |     41-42: combinedInnerProduct, b (Type1)
-- |     43:    xi (SizedF 128)
-- |     44-59: bulletproofChallenges[0..15] (SizedF 128)
-- |   Messages:
-- |     60-89:   wComm[0..14] (15 × 2 fields)
-- |     90-91:   zComm (2 fields)
-- |     92-105:  tComm[0..6] (7 × 2 fields)
-- |   Opening proof:
-- |     106-107: delta (2 fields)
-- |     108-109: sg (2 fields)
-- |     110-173: lr[0..15] (16 × 4 fields: l.x, l.y, r.x, r.y)
-- |     174:     z1 (Type1)
-- |     175:     z2 (Type1)
-- |   Verify:
-- |     176:     claimedDigest
-------------------------------------------------------------------------------

-- | Dummy Vesta generator point wrapped in F (for constant curve points)
dummyVestaPt :: AffinePoint (F WrapField)
dummyVestaPt =
  let
    g = unsafePartial $ fromJust $ toAffine (generator :: VestaG)
  in
    { x: F g.x, y: F g.y }

ivpWrapCircuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => { lagrangeComms :: Array (AffinePoint (F WrapField))
     , blindingH :: AffinePoint (F WrapField)
     }
  -> Vector 177 (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
ivpWrapCircuit { lagrangeComms, blindingH } inputs = do
  let
    at i = unsafeIdx inputs i

    -- Helper: read 2 fields as an AffinePoint
    readPt :: Int -> AffinePoint (FVar WrapField)
    readPt i = { x: at i, y: at (i + 1) }

    ---------------------------------------------------------------------------
    -- PackedStepPublicInput (n=1, dw=15) via tuple construction
    ---------------------------------------------------------------------------

    -- Build the PerProofTuple from fields 0-31
    splitField :: Int -> Type2 (SplitField (FVar WrapField) (BoolVar WrapField))
    splitField i = Type2 (SplitField { sDiv2: at i, sOdd: coerce (at (i + 1)) })

    perProofTuple =
      Tuple
        ( splitField 0 :< splitField 2 :< splitField 4
            :< splitField 6
            :< splitField 8
            :< Vector.nil
        )
        ( Tuple (at 10)
            ( Tuple (asSizedF128 (at 11) :< asSizedF128 (at 12) :< Vector.nil)
                ( Tuple
                    ( asSizedF128 (at 13) :< asSizedF128 (at 14)
                        :< asSizedF128 (at 15)
                        :< Vector.nil
                    )
                    ( Tuple
                        ( (Vector.generate \j -> asSizedF128 (at (16 + getFinite j)))
                            :: Vector 15 _
                        )
                        (coerce (at 31) :: BoolVar WrapField)
                    )
                )
            )
        )

    stmtTuple =
      Tuple
        (perProofTuple :< Vector.nil)
        (Tuple (at 32) (at 33 :< Vector.nil))

    publicInput = fromPackedTuple stmtTuple

    ---------------------------------------------------------------------------
    -- IVP DeferredValues (d=16, Type1 shifted)
    ---------------------------------------------------------------------------

    deferredValues =
      { plonk:
          { alpha: asSizedF128 (at 34)
          , beta: asSizedF128 (at 35)
          , gamma: asSizedF128 (at 36)
          , zeta: asSizedF128 (at 37)
          , perm: Type1 (at 38)
          , zetaToSrsLength: Type1 (at 39)
          , zetaToDomainSize: Type1 (at 40)
          }
      , combinedInnerProduct: Type1 (at 41)
      , b: Type1 (at 42)
      , xi: asSizedF128 (at 43)
      , bulletproofChallenges:
          (Vector.generate \j -> asSizedF128 (at (44 + getFinite j))) :: Vector 16 _
      }

    ---------------------------------------------------------------------------
    -- Messages (curve point commitments)
    ---------------------------------------------------------------------------

    wComm :: Vector 15 (AffinePoint (FVar WrapField))
    wComm = Vector.generate \j -> readPt (60 + 2 * getFinite j)

    zComm = readPt 90

    tComm :: Vector 7 (AffinePoint (FVar WrapField))
    tComm = Vector.generate \j -> readPt (92 + 2 * getFinite j)

    ---------------------------------------------------------------------------
    -- Opening proof
    ---------------------------------------------------------------------------

    opening =
      { delta: readPt 106
      , sg: readPt 108
      , lr:
          ( Vector.generate \j ->
              { l: readPt (110 + 4 * getFinite j)
              , r: readPt (110 + 4 * getFinite j + 2)
              }
          ) :: Vector 16 _
      , z1: Type1 (at 174)
      , z2: Type1 (at 175)
      }

    ---------------------------------------------------------------------------
    -- Claimed sponge digest (for verify assertion)
    ---------------------------------------------------------------------------

    claimedDigest = at 176

    ---------------------------------------------------------------------------
    -- IVP input record
    ---------------------------------------------------------------------------

    ivpInput =
      { publicInput
      , sgOld: Vector.nil
      , deferredValues
      , wComm
      , zComm
      , tComm
      , opening
      }

    ---------------------------------------------------------------------------
    -- Compile-time constants (dummy values — circuit structure is independent)
    ---------------------------------------------------------------------------

    ivpParams =
      { curveParams: curveParams (Proxy @VestaG)
      , lagrangeComms
      , blindingH
      , sigmaCommLast: dummyVestaPt
      , columnComms:
          { index: (Vector.replicate dummyVestaPt) :: Vector 6 _
          , coeff: (Vector.replicate dummyVestaPt) :: Vector 15 _
          , sigma: (Vector.replicate dummyVestaPt) :: Vector 6 _
          }
      , indexDigest: zero
      , endo: wrapEndo
      , groupMapParams: groupMapParams (Proxy @VestaG)
      }

  output <- evalSpongeM initialSpongeCircuit $
    incrementallyVerifyProof @VestaG WrapOtherField.ipaScalarOps ivpParams ivpInput
  assertEqual_ output.spongeDigestBeforeEvaluations claimedDigest
  for_ (Vector.zip deferredValues.bulletproofChallenges output.bulletproofChallenges) \(Tuple c1 c2) ->
    assertEq c1 c2

-------------------------------------------------------------------------------
-- | Test infrastructure
-------------------------------------------------------------------------------

fixtureDir :: String
fixtureDir = "packages/snarky-kimchi/test/fixtures/"

-- | Count gates by kind
gateTypeSummary :: forall f. Array (CircuitGateData f) -> String
gateTypeSummary gates =
  let
    counts = foldl (\m g -> Map.insertWith (+) (show g.kind) 1 m) Map.empty gates
    lines = map (\(Tuple k v) -> "  " <> k <> ": " <> show v)
      (Map.toUnfoldable counts :: Array (Tuple String Int))
  in
    intercalate "\n" lines

-- | Generic comparison test: compile PS circuit, load OCaml fixture, compare.
-- | Quiet on success. On failure, writes detailed diagnostics to /tmp/circuit_diff_<name>.txt
-- | and throws a concise error message.
compareCircuit
  :: forall f
   . SerdeHex f
  => Show f
  => Ord f
  => PrimeField f
  => String -- display name
  -> String -- fixture name (without _circuit.json)
  -> CompiledCircuit f
  -> Either MultipleErrors (CircuitData f)
  -> Aff Unit
compareCircuit name fixtureName compiled ocamlResult = do
  let
    psConsts = extractCachedConstants compiled.state

    psCircuit :: Either MultipleErrors (CircuitData f)
    psCircuit = readCircuitJson compiled.json
  case ocamlResult, psCircuit of
    Right ocaml, Right ps -> do
      let
        ocamlLen = Array.length ocaml.gates
        psLen = Array.length ps.gates
      ps.publicInputSize `shouldEqual` ocaml.publicInputSize
      ocamlConsts <- loadCachedConstants @f fixtureName
      compareCachedConstants name ocamlConsts psConsts
      let diffs = diffCircuits ocaml ps
      if Array.length diffs > 0 || ocamlLen /= psLen then do
        -- Write detailed diagnostics to file
        let diagFile = "/tmp/circuit_diff_" <> name <> ".txt"
        liftEffect $ FS.writeTextFile UTF8 diagFile (buildDiagnostics ocaml.gates ps.gates diffs)
        -- Throw concise error
        let
          first = unsafePartial $ Array.unsafeIndex diffs 0
          msg = "Circuit mismatch (OCaml=" <> show ocamlLen <> " PS=" <> show psLen <> " gates, "
            <> show (Array.length diffs)
            <> " diffs). "
            <> "First at gate "
            <> show first.index
            <> " ("
            <> show first.ocaml.kind
            <> "). "
            <> "Details: "
            <> diagFile
        liftEffect $ throw msg
      else pure unit
    Left e, _ -> liftEffect $ throw $ "Failed to parse OCaml JSON: " <> show e
    _, Left e -> liftEffect $ throw $ "Failed to parse PureScript JSON: " <> show e

-- | Build detailed diagnostic text for a circuit mismatch (written to file, not console).
buildDiagnostics
  :: forall f
   . Show f
  => Eq f
  => Semiring f
  => Ring f
  => Array (CircuitGateData f)
  -> Array (CircuitGateData f)
  -> Array (GateDiff f)
  -> String
buildDiagnostics ocaml ps diffs =
  let
    ocamlLen = Array.length ocaml
    psLen = Array.length ps
    showCoeffs coeffs = intercalate "," $ map
      ( \c ->
          if c == zero then "0"
          else if c == one then "1"
          else if c == (-one) then "-1"
          else show c
      )
      coeffs

    unbatch gates = concatMap
      ( \g ->
          if Array.length g.coeffs <= 5 then [ g.coeffs ]
          else [ Array.take 5 g.coeffs, Array.drop 5 g.coeffs ]
      )
      gates
    ocHalfRows = unbatch ocaml
    psHalfRows = unbatch ps
    hrDiffs = Array.catMaybes $ Array.mapWithIndex
      ( \i ocHR ->
          if i < Array.length psHalfRows then
            let
              psHR = unsafePartial $ Array.unsafeIndex psHalfRows i
            in
              if ocHR /= psHR then Just i else Nothing
          else Just i
      )
      ocHalfRows

    ocamlKinds = map _.kind ocaml
    psKinds = map _.kind ps
    kindDivergences = Array.catMaybes $ Array.mapWithIndex
      ( \i ok ->
          if i < Array.length psKinds then
            let
              pk = unsafePartial $ Array.unsafeIndex psKinds i
            in
              if ok /= pk then Just (show i <> ": OCaml=" <> show ok <> " PS=" <> show pk) else Nothing
          else Just (show i <> ": OCaml=" <> show ok <> " PS=<missing>")
      )
      ocamlKinds

    lines = Array.concat
      [ [ "Circuit comparison: OCaml=" <> show ocamlLen <> " PS=" <> show psLen <> " gates"
        , "OCaml gate types:\n" <> gateTypeSummary ocaml
        , "PS gate types:\n" <> gateTypeSummary ps
        , ""
        , "Differing gate indices: " <> intercalate ", "
            (map (\d -> show d.index <> "(" <> show d.ocaml.kind <> ")") diffs)
        , "Gate kind mismatches: " <> intercalate ", " (Array.take 20 kindDivergences)
        , "Half-row coeff diffs: " <> show (Array.length hrDiffs) <> "/" <> show (Array.length ocHalfRows)
        , ""
        ]
      , diffs <#> \d ->
          "[" <> show d.index <> "] " <> show d.ocaml.kind <> "\n"
            <> "  OCaml: "
            <> formatGate d.index d.ocaml
            <> "\n"
            <> "  PS:    "
            <> formatGate d.index d.ps
      , [ "" ]
      , if Array.length hrDiffs > 0 then
          let
            firstDiffHR = fromMaybe 0 (Array.head hrDiffs)
            windowStart = max 0 (firstDiffHR - 5)
            windowEnd = min (Array.length ocHalfRows) (firstDiffHR + 10)
          in
            [ "Half-row dump around first diff HR " <> show firstDiffHR <> ":"
            , "  HR#  | gate | half | OCaml coeffs | PS coeffs | match?"
            ] <> map
              ( \i ->
                  let
                    ocHR = unsafePartial $ Array.unsafeIndex ocHalfRows i
                    psHR = if i < Array.length psHalfRows then unsafePartial $ Array.unsafeIndex psHalfRows i else []
                    gateIdx = i / 2
                    halfStr = if i `mod` 2 == 0 then "1st" else "2nd"
                    matchStr = if ocHR == psHR then "OK" else "DIFF"
                  in
                    "  " <> show i <> " | g" <> show gateIdx <> " | " <> halfStr
                      <> " | ["
                      <> showCoeffs ocHR
                      <> "] | ["
                      <> showCoeffs psHR
                      <> "] | "
                      <> matchStr
              )
              (Array.range windowStart (windowEnd - 1))
        else []
      ]
  in
    intercalate "\n" lines

loadFixture :: forall @f. SerdeHex f => String -> Aff (Either MultipleErrors (CircuitData f))
loadFixture name = liftEffect do
  buf <- FS.readFile (fixtureDir <> name <> ".json")
  json <- Buffer.toString UTF8 buf
  pure (readCircuitJson json)

loadCachedConstants :: forall @f. Ord f => PrimeField f => String -> Aff (Array (Tuple String f))
loadCachedConstants name = liftEffect do
  buf <- FS.readFile (fixtureDir <> name <> "_cached_constants.json")
  json <- Buffer.toString UTF8 buf
  case readCachedConstantsJson json of
    Left e -> throw $ "Failed to parse cached constants: " <> show e
    Right s -> pure s

compareCachedConstants
  :: forall f
   . Ord f
  => Show f
  => String
  -> Array (Tuple String f) -- OCaml cached constants
  -> Array (Tuple String f) -- PS cached constants
  -> Aff Unit
compareCachedConstants name ocamlConsts psConsts = do
  let
    ocamlSet = Set.fromFoldable $ snd <$> ocamlConsts
    psSet = Set.fromFoldable $ snd <$> psConsts
    ocamlOnly = filter (\(Tuple _ y) -> not $ Set.member y psSet) ocamlConsts
    psOnly = filter (\(Tuple _ y) -> not $ Set.member y ocamlSet) psConsts
  when (ocamlSet /= psSet) do
    let
      diagFile = "/tmp/circuit_diff_" <> name <> "_cached_constants.txt"
      lines = Array.concat
        [ [ "Cached constants mismatch: OCaml=" <> show (Set.size ocamlSet) <> " PS=" <> show (Set.size psSet) ]
        , if not (Array.null ocamlOnly) then [ "Only in OCaml (" <> show (Array.length ocamlOnly) <> "):" ]
            <> map (\(Tuple var value) -> "  " <> show { var, value }) ocamlOnly
          else []
        , if not (Array.null psOnly) then [ "Only in PS (" <> show (Array.length psOnly) <> "):" ]
            <> map (\(Tuple var value) -> "  " <> show { var, value }) psOnly
          else []
        ]
    liftEffect $ FS.writeTextFile UTF8 diagFile (intercalate "\n" lines)
    liftEffect $ throw $ "Cached constants mismatch (" <> name <> "): OCaml="
      <> show (Set.size ocamlSet)
      <> " PS="
      <> show (Set.size psSet)
      <> ". Details: "
      <> diagFile

-------------------------------------------------------------------------------
-- | Compiled circuit
-------------------------------------------------------------------------------

type V1 = Vector 1 (F StepField)
type V20 = Vector 20 (F StepField)
type V34 = Vector 34 (F StepField)
type V151 = Vector 151 (F StepField)

-- | A compiled circuit: the builder state and the JSON representation.
type CompiledCircuit f =
  { state :: CircuitBuilderState (KimchiGate f) (AuxState f)
  , json :: String
  }

compiledCircuit
  :: forall @f g
   . CircuitGateConstructor f g
  => PrimeField f
  => CircuitBuilderState (KimchiGate f) (AuxState f)
  -> CompiledCircuit f
compiledCircuit s = { state: s, json: circuitToJson @f s }

compilePow2Pow :: CompiledCircuit StepField
compilePow2Pow = compiledCircuit @StepField $
  compilePure (Proxy @V1) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    pow2PowCircuit
    Kimchi.initialState

compileBCorrect :: CompiledCircuit StepField
compileBCorrect = compiledCircuit @StepField $
  compilePure (Proxy @V20) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    bCorrectTestCircuit
    Kimchi.initialState

compileChallengeDigest :: CompiledCircuit StepField
compileChallengeDigest = compiledCircuit @StepField $
  compilePure (Proxy @V34) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    challengeDigestTestCircuit
    Kimchi.initialState

compileFopStep :: CompiledCircuit StepField
compileFopStep = compiledCircuit @StepField $
  compilePure (Proxy @V151) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    finalizeOtherProofStepCircuit
    Kimchi.initialState

type V148 = Vector 148 (F WrapField)

compileFopWrap :: CompiledCircuit WrapField
compileFopWrap = compiledCircuit @WrapField $
  compilePure (Proxy @V148) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    finalizeOtherProofWrapCircuit
    Kimchi.initialState

type V177 = Vector 177 (F WrapField)

compileIvpWrap
  :: { lagrangeComms :: Array (AffinePoint (F WrapField))
     , blindingH :: AffinePoint (F WrapField)
     }
  -> CompiledCircuit WrapField
compileIvpWrap srsData = compiledCircuit @WrapField $
  compilePure (Proxy @V177) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (ivpWrapCircuit srsData)
    Kimchi.initialState

-------------------------------------------------------------------------------
-- | xhat sub-circuit
-- |
-- | Public input commitment MSM (x_hat computation) isolated from the full IVP.
-- | Takes 34 input fields (same as IVP fields 0-33: the PackedStepPublicInput),
-- | builds the public input structure, and computes x_hat via publicInputCommit.
-- |
-- | Input layout (34 fields) — same as IVP wrap fields 0-33:
-- |   0-1:   cip (Type2 SplitField: sDiv2, sOdd)
-- |   2-3:   b
-- |   4-5:   zetaToSrsLength
-- |   6-7:   zetaToDomainSize
-- |   8-9:   perm
-- |   10:    sponge_digest_before_evaluations
-- |   11-12: beta, gamma (SizedF 128)
-- |   13-15: alpha, zeta, xi (SizedF 128)
-- |   16-30: bulletproof_challenges[0..14]
-- |   31:    should_finalize
-- |   32:    messages_for_next_step_proof
-- |   33:    messages_for_next_wrap_proof[0]
-- |
-- | OCaml reference: dump_circuit_impl.ml xhat_circuit
-------------------------------------------------------------------------------

xhatTestCircuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => { lagrangeComms :: Array (AffinePoint (F WrapField))
     , blindingH :: AffinePoint (F WrapField)
     }
  -> Vector 34 (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
xhatTestCircuit { lagrangeComms, blindingH } inputs = do
  let
    at i = unsafeIdx inputs i

    -- Build the PerProofTuple from fields 0-31 (same as ivpWrapCircuit)
    splitField :: Int -> Type2 (SplitField (FVar WrapField) (BoolVar WrapField))
    splitField i = Type2 (SplitField { sDiv2: at i, sOdd: coerce (at (i + 1)) })

    perProofTuple =
      Tuple
        ( splitField 0 :< splitField 2 :< splitField 4
            :< splitField 6
            :< splitField 8
            :< Vector.nil
        )
        ( Tuple (at 10)
            ( Tuple (asSizedF128 (at 11) :< asSizedF128 (at 12) :< Vector.nil)
                ( Tuple
                    ( asSizedF128 (at 13) :< asSizedF128 (at 14)
                        :< asSizedF128 (at 15)
                        :< Vector.nil
                    )
                    ( Tuple
                        ( (Vector.generate \j -> asSizedF128 (at (16 + getFinite j)))
                            :: Vector 15 _
                        )
                        (coerce (at 31) :: BoolVar WrapField)
                    )
                )
            )
        )

    stmtTuple =
      Tuple
        (perProofTuple :< Vector.nil)
        (Tuple (at 32) (at 33 :< Vector.nil))

    publicInput = fromPackedTuple stmtTuple

  void $ publicInputCommit
    { curveParams: curveParams (Proxy @VestaG)
    , lagrangeComms
    , blindingH
    }
    publicInput

type V34W = Vector 34 (F WrapField)

compileXhat
  :: { lagrangeComms :: Array (AffinePoint (F WrapField))
     , blindingH :: AffinePoint (F WrapField)
     }
  -> CompiledCircuit WrapField
compileXhat srsData = compiledCircuit @WrapField $
  compilePure (Proxy @V34W) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    (xhatTestCircuit srsData)
    Kimchi.initialState

-------------------------------------------------------------------------------
-- | bullet_reduce sub-circuit
-- |
-- | Input layout (80 fields):
-- |   0-63:  lr[0..15] (16 × 4 fields: l.x, l.y, r.x, r.y)
-- |   64-79: scalar_challenges[0..15]
-------------------------------------------------------------------------------

bulletReduceTestCircuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => Vector 80 (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
bulletReduceTestCircuit inputs = do
  let
    at i = unsafeIdx inputs i

    readPt :: Int -> AffinePoint (FVar WrapField)
    readPt i = { x: at i, y: at (i + 1) }

    pairs :: Vector 16 { l :: AffinePoint (FVar WrapField), r :: AffinePoint (FVar WrapField) }
    pairs = Vector.generate \j ->
      { l: readPt (4 * getFinite j), r: readPt (4 * getFinite j + 2) }

    challenges :: Vector 16 (SizedF 128 (FVar WrapField))
    challenges = Vector.generate \j -> asSizedF128 (at (64 + getFinite j))
  void $ bulletReduceCircuit @WrapField @VestaG
    { pairs, challenges }

-- | Single bullet_reduce round: endoInv(l, u) + endo(r, u) + addComplete
-- | Input: l.x, l.y, r.x, r.y, scalar = 5 fields
bulletReduceOneCircuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => Vector 5 (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
bulletReduceOneCircuit inputs = do
  let
    at i = unsafeIdx inputs i
    l = { x: at 0, y: at 1 }
    r = { x: at 2, y: at 3 }
    u = asSizedF128 (at 4)
  lScaled <- endoInv @WrapField @Vesta.ScalarField @VestaG l u
  rScaled <- endo r u
  void $ addComplete lScaled rScaled

type V5 = Vector 5 (F WrapField)

compileBulletReduceOne :: CompiledCircuit WrapField
compileBulletReduceOne = compiledCircuit @WrapField $
  compilePure (Proxy @V5) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    bulletReduceOneCircuit
    Kimchi.initialState

type V80 = Vector 80 (F WrapField)

compileBulletReduce :: CompiledCircuit WrapField
compileBulletReduce = compiledCircuit @WrapField $
  compilePure (Proxy @V80) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    bulletReduceTestCircuit
    Kimchi.initialState

-------------------------------------------------------------------------------
-- | ftcomm sub-circuit
-- |
-- | FT polynomial commitment (linearization) from IVP wrap.
-- | Input layout (17 fields):
-- |   0-13:  tComm[0..6] (7 × 2 coords)
-- |   14:    perm (Type1 shifted)
-- |   15:    zetaToSrsLength (Type1 shifted)
-- |   16:    zetaToDomainSize (Type1 shifted)
-- |
-- | sigma_comm_last is constant (Vesta generator, matching IVP's dummy_comm).
-- | OCaml reference: dump_circuit_impl.ml ftcomm_circuit
-------------------------------------------------------------------------------

ftcommTestCircuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => Vector 17 (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
ftcommTestCircuit inputs = do
  let
    at i = unsafeIdx inputs i

    readPt :: Int -> AffinePoint (FVar WrapField)
    readPt i = { x: at i, y: at (i + 1) }

    tComm :: Vector 7 (AffinePoint (FVar WrapField))
    tComm = Vector.generate \j -> readPt (2 * getFinite j)

    -- sigma_comm_last = constant Vesta generator (same as IVP dummy_comm)
    sigmaLast :: AffinePoint (FVar WrapField)
    sigmaLast =
      let
        g = unsafePartial $ fromJust $ toAffine (generator :: VestaG)
      in
        { x: const_ g.x, y: const_ g.y }

  void $ ftComm WrapOtherField.ipaScalarOps
    { sigmaLast
    , tComm
    , perm: Type1 (at 14)
    , zetaToSrsLength: Type1 (at 15)
    , zetaToDomainSize: Type1 (at 16)
    }

type V17W = Vector 17 (F WrapField)

compileFtcomm :: CompiledCircuit WrapField
compileFtcomm = compiledCircuit @WrapField $
  compilePure (Proxy @V17W) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    ftcommTestCircuit
    Kimchi.initialState

-------------------------------------------------------------------------------
-- | combine_poly sub-circuit
-- |
-- | Split_commitments.combine from IVP wrap bulletproof.
-- | Input layout (37 fields):
-- |   0-1:   x_hat (1 point)
-- |   2-3:   ft_comm (1 point)
-- |   4-5:   z_comm (1 point)
-- |   6-35:  w_comm[0..14] (15 points × 2 coords)
-- |   36:    xi (scalar challenge)
-- |
-- | Constant bases (27 = 6 index + 15 coeff + 6 sigma) from dummy VK (Vesta generator).
-- | Total: 18 variable + 27 constant = 45 bases.
-- | OCaml reference: dump_circuit_impl.ml combine_poly_circuit
-------------------------------------------------------------------------------

combinePolyTestCircuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => Vector 37 (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
combinePolyTestCircuit inputs = do
  let
    at i = unsafeIdx inputs i

    readPt :: Int -> AffinePoint (FVar WrapField)
    readPt i = { x: at i, y: at (i + 1) }

    -- Variable points from inputs
    xHat = readPt 0
    ftCommPt = readPt 2
    zComm = readPt 4

    wComm :: Vector 15 (AffinePoint (FVar WrapField))
    wComm = Vector.generate \j -> readPt (6 + 2 * getFinite j)

    -- Constant points from dummy VK (Vesta generator)
    g = unsafePartial $ fromJust $ toAffine (generator :: VestaG)

    dummyPt :: AffinePoint (FVar WrapField)
    dummyPt = { x: const_ g.x, y: const_ g.y }

    indexComms :: Vector 6 (AffinePoint (FVar WrapField))
    indexComms = Vector.generate \_ -> dummyPt

    coeffComms :: Vector 15 (AffinePoint (FVar WrapField))
    coeffComms = Vector.generate \_ -> dummyPt

    sigmaComms :: Vector 6 (AffinePoint (FVar WrapField))
    sigmaComms = Vector.generate \_ -> dummyPt

    -- Assemble all 45 bases in the same order as IVP:
    -- x_hat, ft_comm, z_comm, index(6), w(15), coeff(15), sigma(6)
    allBases :: Vector 45 (AffinePoint (FVar WrapField))
    allBases =
      (xHat :< ftCommPt :< zComm :< Vector.nil)
        `Vector.append` indexComms
        `Vector.append` wComm
        `Vector.append` coeffComms
        `Vector.append` sigmaComms

    xi = asSizedF128 (at 36)

  void $ combinePolynomials allBases xi

type V37W = Vector 37 (F WrapField)

compileCombinePoly :: CompiledCircuit WrapField
compileCombinePoly = compiledCircuit @WrapField $
  compilePure (Proxy @V37W) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    combinePolyTestCircuit
    Kimchi.initialState

--------------------------------------------------------------------------------
-- | group_map sub-circuit
-- |
-- | BW19 hash-to-curve: maps a single field element to a curve point.
-- | Input layout (1 field): the field element to map.
-- | OCaml reference: dump_circuit_impl.ml group_map_circuit
--------------------------------------------------------------------------------

groupMapTestCircuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => Vector 1 (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
groupMapTestCircuit inputs = do
  let params = groupMapParams (Proxy @VestaG)
  void $ groupMapCircuit params (Vector.head inputs)

type V1W = Vector 1 (F WrapField)

compileGroupMap :: CompiledCircuit WrapField
compileGroupMap = compiledCircuit @WrapField $
  compilePure (Proxy @V1W) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    groupMapTestCircuit
    Kimchi.initialState

-------------------------------------------------------------------------------
-- | Debug: row → labels mapping
-------------------------------------------------------------------------------

-- | Dump row-to-label mapping for the Wrap FOP circuit as a string.
-- | Each line: "row_index: label1, label2, ..."
{-
dumpRowLabels :: String
dumpRowLabels =
  let
    s :: CircuitBuilderState (KimchiGate WrapField) (AuxState WrapField)
    s = compilePure (Proxy @V148) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
      finalizeOtherProofWrapCircuit
      Kimchi.initialState
    rowLabels = buildRowLabels s
  in
    intercalate "\n" $ map
      ( \(Tuple row labels) ->
          show row <> ": " <> intercalate ", " labels
      )
      rowLabels
-}
-------------------------------------------------------------------------------
-- | Spec
-------------------------------------------------------------------------------

spec :: Spec Unit
spec =
  describe "FinalizeOtherProof CircuitJson" do
    it "pow2PowSquare sub-circuit" do
      ocaml <- loadFixture @StepField "pow2_pow_circuit"
      compareCircuit "pow2_pow" "pow2_pow_circuit" compilePow2Pow ocaml
    it "bCorrect sub-circuit" do
      ocaml <- loadFixture @StepField "b_correct_circuit"
      compareCircuit "b_correct" "b_correct_circuit" compileBCorrect ocaml
    it "challengeDigest sub-circuit" do
      ocaml <- loadFixture @StepField "challenge_digest_circuit"
      compareCircuit "challenge_digest" "challenge_digest_circuit" compileChallengeDigest ocaml
    it "Full: finalize_other_proof Step circuit" do
      ocaml <- loadFixture @StepField "finalize_other_proof_circuit"
      compareCircuit "full_fop" "finalize_other_proof_circuit" compileFopStep ocaml
    it "Full: finalize_other_proof Wrap circuit" do
      ocaml <- loadFixture @WrapField "finalize_other_proof_wrap_circuit"
      compareCircuit "full_fop_wrap" "finalize_other_proof_wrap_circuit" compileFopWrap ocaml
    it "IVP Wrap circuit" do
      let
        srs = vestaCrsCreate (pow 2 16)
        srsData =
          { lagrangeComms: coerce $ pallasSrsLagrangeCommitments srs 16 177
          , blindingH: coerce $ pallasSrsBlindingGenerator srs
          }
        compiled = compileIvpWrap srsData
      ocaml <- loadFixture @WrapField "ivp_wrap_circuit"
      compareCircuit "ivp_wrap" "ivp_wrap_circuit" compiled ocaml
    it "xhat sub-circuit" do
      let
        srs = vestaCrsCreate (pow 2 16)
        srsData =
          { lagrangeComms: coerce $ pallasSrsLagrangeCommitments srs 16 177
          , blindingH: coerce $ pallasSrsBlindingGenerator srs
          }
      ocaml <- loadFixture @WrapField "xhat_circuit"
      compareCircuit "xhat" "xhat_circuit" (compileXhat srsData) ocaml
    it "ftcomm sub-circuit" do
      ocaml <- loadFixture @WrapField "ftcomm_circuit"
      compareCircuit "ftcomm" "ftcomm_circuit" compileFtcomm ocaml
    it "combine_poly sub-circuit" do
      ocaml <- loadFixture @WrapField "combine_poly_circuit"
      compareCircuit "combine_poly" "combine_poly_circuit" compileCombinePoly ocaml
    it "bullet_reduce_one sub-circuit" do
      ocaml <- loadFixture @WrapField "bullet_reduce_one_circuit"
      compareCircuit "bullet_reduce_one" "bullet_reduce_one_circuit" compileBulletReduceOne ocaml
    it "bullet_reduce sub-circuit" do
      ocaml <- loadFixture @WrapField "bullet_reduce_circuit"
      compareCircuit "bullet_reduce" "bullet_reduce_circuit" compileBulletReduce ocaml
    it "group_map sub-circuit" do
      ocaml <- loadFixture @WrapField "group_map_circuit"
      compareCircuit "group_map" "group_map_circuit" compileGroupMap ocaml
