-- | Circuit JSON comparison test for FinalizeOtherProof.
-- |
-- | Tests the library's `finalizeOtherProofCircuit` by compiling it with a
-- | thin wrapper that unpacks a flat 151-element public input vector into the
-- | typed record structure the library expects, then compares the resulting
-- | constraint system against the OCaml fixture.
-- |
-- | OCaml reference: dump_circuit_impl.ml:1090-1226 (input layout),
-- |                  step_verifier.ml:828-1165 (computation)
module Test.Pickles.CircuitJson (spec) where

import Prelude

import Data.Array (concatMap)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Fin (getFinite)
import Data.Foldable (foldl, intercalate)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.Map as Map
import Data.Maybe (fromJust, fromMaybe)
import Data.Set as Set
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Class.Console (log)
import Effect.Exception (throw)
import Foreign (MultipleErrors)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Partial.Unsafe (unsafePartial)
import Pickles.IPA (bCorrectCircuit)
import Pickles.Linearization as Linearization
import Pickles.Linearization.FFI as LinFFI
import Pickles.PackedStatement (fromPackedTuple)
import Pickles.Sponge (evalSpongeM, initialSpongeCircuit)
import Pickles.Step.ChallengeDigest as ChallengeDigest
import Pickles.Step.Domain (pow2PowSquare)
import Pickles.Step.FinalizeOtherProof (finalizeOtherProofCircuit)
import Pickles.Step.OtherField as StepOtherField
import Pickles.Types (StepField, WrapField)
import Pickles.Verify (verify)
import Pickles.Wrap.FinalizeOtherProof (wrapFinalizeOtherProofCircuit)
import Pickles.Wrap.OtherField as WrapOtherField
import Safe.Coerce (coerce)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (compilePure)
import Snarky.Backend.Kimchi (makePublicInputRows, placeVariables)
import Snarky.Backend.Kimchi.CircuitJson (CircuitData, CircuitGateData, circuitToJson, diffCircuits, formatGate, readCircuitJson)
import Snarky.Circuit.CVar (Variable)
import Snarky.Circuit.DSL (class CircuitM, Bool(..), BoolVar, F(..), FVar, SizedF, Snarky, assert_, const_, false_)
import Snarky.Circuit.Kimchi (SplitField(..), Type1(..), Type2(..), fromShiftedType1Circuit, groupMapParams, toField)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState, KimchiRow, toKimchiRows)
import Snarky.Curves.Class (class PrimeField, class SerdeHex, EndoScalar(..), curveParams, endoScalar, generator, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
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
  let g = unsafePartial $ fromJust $ toAffine (generator :: VestaG)
  in { x: F g.x, y: F g.y }

ivpWrapCircuit
  :: forall t m
   . CircuitM WrapField (KimchiConstraint WrapField) t m
  => Vector 177 (FVar WrapField)
  -> Snarky (KimchiConstraint WrapField) t m Unit
ivpWrapCircuit inputs = do
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
            :< splitField 6 :< splitField 8 :< Vector.nil
        )
        ( Tuple (at 10)
            ( Tuple (asSizedF128 (at 11) :< asSizedF128 (at 12) :< Vector.nil)
                ( Tuple
                    ( asSizedF128 (at 13) :< asSizedF128 (at 14)
                        :< asSizedF128 (at 15) :< Vector.nil
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
      , lagrangeComms: Array.replicate 34 dummyVestaPt
      , blindingH: dummyVestaPt
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

  success <- evalSpongeM initialSpongeCircuit $
    verify @VestaG WrapOtherField.ipaScalarOps ivpParams ivpInput false_ claimedDigest
  assert_ success

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
compareCircuit
  :: forall f
   . SerdeHex f
  => Show f
  => Eq f
  => String -- fixture name (without .json)
  -> String -- compiled PS circuit JSON
  -> Either MultipleErrors (CircuitData f)
  -> Aff Unit
compareCircuit name psJson ocamlResult = do
  let
    psCircuit :: Either MultipleErrors (CircuitData f)
    psCircuit = readCircuitJson psJson
  case ocamlResult, psCircuit of
    Right ocaml, Right ps -> do
      let
        ocamlLen = Array.length ocaml.gates
        psLen = Array.length ps.gates
      log $ name <> " OCaml: pi=" <> show ocaml.publicInputSize <> ", gates=" <> show ocamlLen
      log $ name <> " PS:    pi=" <> show ps.publicInputSize <> ", gates=" <> show psLen
      log $ "OCaml gate types:\n" <> gateTypeSummary ocaml.gates
      log $ "PS gate types:\n" <> gateTypeSummary ps.gates
      ps.publicInputSize `shouldEqual` ocaml.publicInputSize
      -- Check gate count match first — don't silently drop gates
      if ocamlLen /= psLen then
        log $ "Gate count mismatch: OCaml=" <> show ocamlLen <> " PS=" <> show psLen
      else pure unit
      -- Compare gates that exist in both, report first divergence
      let diffs = diffCircuits ocaml ps
      log $ "Differing gate indices: " <> intercalate ", "
        (map (\d -> show d.index <> "(" <> show d.ocaml.kind <> ")") diffs)
      if Array.length diffs > 0 then do
        let
          first = unsafePartial $ Array.unsafeIndex diffs 0
          msg = "First divergence at gate " <> show first.index <> ":\n"
            <> "  OCaml: "
            <> formatGate first.index first.ocaml
            <> "\n"
            <> "  PS:    "
            <> formatGate first.index first.ps
            <> "\n"
            <> "Total differences: "
            <> show (Array.length diffs)
            <> " / "
            <> show (max ocamlLen psLen)
        liftEffect $ throw msg
      else pure unit
      -- If all zipped gates match but lengths differ, that's still a failure
      if ocamlLen /= psLen then
        liftEffect $ throw $ "Gate count mismatch: OCaml=" <> show ocamlLen <> " PS=" <> show psLen
          <> ". All "
          <> show (min ocamlLen psLen)
          <> " shared gates match."
      else pure unit
    Left e, _ -> liftEffect $ throw $ "Failed to parse OCaml JSON: " <> show e
    _, Left e -> liftEffect $ throw $ "Failed to parse PureScript JSON: " <> show e

loadFixture :: forall @f. SerdeHex f => String -> Aff (Either MultipleErrors (CircuitData f))
loadFixture name = liftEffect do
  buf <- FS.readFile (fixtureDir <> name <> ".json")
  json <- Buffer.toString UTF8 buf
  pure (readCircuitJson json)

-------------------------------------------------------------------------------
-- | Compiled circuit
-------------------------------------------------------------------------------

type V1 = Vector 1 (F StepField)
type V20 = Vector 20 (F StepField)
type V34 = Vector 34 (F StepField)
type V151 = Vector 151 (F StepField)

compilePow2Pow :: String
compilePow2Pow = circuitToJson @StepField $
  compilePure (Proxy @V1) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    pow2PowCircuit
    Kimchi.initialState

compileBCorrect :: String
compileBCorrect = circuitToJson @StepField $
  compilePure (Proxy @V20) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    bCorrectTestCircuit
    Kimchi.initialState

compileChallengeDigest :: String
compileChallengeDigest = circuitToJson @StepField $
  compilePure (Proxy @V34) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    challengeDigestTestCircuit
    Kimchi.initialState

compileFopStep :: String
compileFopStep = circuitToJson @StepField $
  compilePure (Proxy @V151) (Proxy @Unit) (Proxy @(KimchiConstraint StepField))
    finalizeOtherProofStepCircuit
    Kimchi.initialState

type V148 = Vector 148 (F WrapField)

compileFopWrap :: String
compileFopWrap = circuitToJson @WrapField $
  compilePure (Proxy @V148) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    finalizeOtherProofWrapCircuit
    Kimchi.initialState

type V177 = Vector 177 (F WrapField)

compileIvpWrap :: String
compileIvpWrap = circuitToJson @WrapField $
  compilePure (Proxy @V177) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
    ivpWrapCircuit
    Kimchi.initialState

-------------------------------------------------------------------------------
-- | Debug: row → labels mapping
-------------------------------------------------------------------------------

-- | Build a mapping from gate row index to the set of labels of variables
-- | appearing in that row. Uses varMetadata (variable → birth labels) and
-- | placeVariables (variable → cell positions) to cross-reference.
buildRowLabels
  :: forall f
   . PrimeField f
  => CircuitBuilderState (KimchiGate f) (AuxState f)
  -> Array (Tuple Int (Array String))
buildRowLabels s =
  let
    piRows :: Array (KimchiRow f)
    piRows = makePublicInputRows s.publicInputs
    rows = piRows <> concatMap toKimchiRows s.constraints
    placement = placeVariables rows

    -- Reverse map: for each variable, get its labels and its cell positions
    -- Then build row → Set of labels
    rowLabelMap :: Map.Map Int (Set.Set String)
    rowLabelMap = foldlWithIndex
      ( \var acc cells ->
          let
            labels = fromMaybe [] (Map.lookup var s.varMetadata)
            labelStr = intercalate " > " labels
          in
            if Array.null labels then acc
            else foldl
              ( \m (Tuple row _col) ->
                  Map.insertWith Set.union row (Set.singleton labelStr) m
              )
              acc
              cells
      )
      Map.empty
      (placement :: Map.Map Variable (Array (Tuple Int Int)))

  in
    map (\(Tuple row labels) -> Tuple row (Set.toUnfoldable labels :: Array String))
      (Map.toUnfoldable rowLabelMap :: Array (Tuple Int (Set.Set String)))

-- | Dump row-to-label mapping for the Wrap FOP circuit as a string.
-- | Each line: "row_index: label1, label2, ..."
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

-------------------------------------------------------------------------------
-- | Spec
-------------------------------------------------------------------------------

spec :: Spec Unit
spec =
  describe "FinalizeOtherProof CircuitJson" do
    it "pow2PowSquare sub-circuit" do
      ocaml <- loadFixture @StepField "pow2_pow_circuit"
      compareCircuit "pow2_pow" compilePow2Pow ocaml
    it "bCorrect sub-circuit" do
      ocaml <- loadFixture @StepField "b_correct_circuit"
      compareCircuit "b_correct" compileBCorrect ocaml
    it "challengeDigest sub-circuit" do
      ocaml <- loadFixture @StepField "challenge_digest_circuit"
      compareCircuit "challenge_digest" compileChallengeDigest ocaml
    it "Full: finalize_other_proof Step circuit" do
      ocaml <- loadFixture @StepField "finalize_other_proof_circuit"
      compareCircuit "full_fop" compileFopStep ocaml
    it "Full: finalize_other_proof Wrap circuit" do
      ocaml <- loadFixture @WrapField "finalize_other_proof_wrap_circuit"
      compareCircuit "full_fop_wrap" compileFopWrap ocaml
    it "IVP Wrap circuit" do
      ocaml <- loadFixture @WrapField "ivp_wrap_circuit"
      compareCircuit "ivp_wrap" compileIvpWrap ocaml
    it "IVP Wrap labels" do
      let
        s :: CircuitBuilderState (KimchiGate WrapField) (AuxState WrapField)
        s = compilePure (Proxy @V177) (Proxy @Unit) (Proxy @(KimchiConstraint WrapField))
          ivpWrapCircuit
          Kimchi.initialState
        rowLabels = buildRowLabels s
        -- Summarize: for each label, find min and max row
        labelRanges = foldl
          ( \m (Tuple row labels) ->
              foldl (\m' lbl -> Map.insertWith
                (\(Tuple lo hi) (Tuple lo2 hi2) -> Tuple (min lo lo2) (max hi hi2))
                lbl (Tuple row row) m') m labels
          )
          Map.empty
          rowLabels
        rangeLines = map
          (\(Tuple lbl (Tuple lo hi)) ->
            lbl <> ": rows " <> show lo <> "-" <> show hi <> " (" <> show (hi - lo + 1) <> " rows)")
          (Map.toUnfoldable labelRanges :: Array (Tuple String (Tuple Int Int)))
      log $ "IVP label ranges:\n" <> intercalate "\n" rangeLines
