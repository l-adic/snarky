-- | Wrap-prover orchestration: pure PS port of the `deferred_values`
-- | step inside OCaml `mina/src/lib/crypto/pickles/wrap.ml:90-272`.
-- |
-- | The OCaml function `Wrap.For_tests_only.deferred_values` is what
-- | the wrap prover runs to turn a freshly-minted **step proof** into
-- | the step-field `Deferred_values.t` + `x_hat_evals` +
-- | `sponge_digest_before_evaluations` hints the wrap circuit's
-- | auxiliary inputs need.
-- |
-- | Everything here runs in the **step field** (`Step.Field` = `Fp` =
-- | `Tick.Field`) and produces `Type1`-shifted values — mirroring
-- | OCaml's `Type1 = Plonk_checks.Make (Shifted_value.Type1)
-- | (Scalars_tokens_interpreter.Tick)` functor instantiation.
-- |
-- | All scalar math (`derivePlonk`, `ftEval0`,
-- | `combinedInnerProductBatch`, `computeBpChalsAndB`) is pulled from
-- | `Pickles.Prove.Pure.Common`; this module plumbs the step proof,
-- | its oracles, and the prev (sg, expanded bp challenges) pairs
-- | through those helpers and wraps the output in the step-field Type1
-- | records that `wrap_main` reads.
-- |
-- | Non-chunked assumption: single chunk per polynomial (= standard
-- | Mina `num_chunks = 1`). Caller recombines via
-- | `Common.evalsOfSplitPoint` upstream if chunks are ever needed.
module Pickles.Prove.Pure.Wrap
  ( WrapDeferredValuesInput
  , WrapDeferredValuesOutput
  , wrapComputeDeferredValues
  , AssembleWrapMainInputInput
  , assembleWrapMainInput
  , branchDataMaskWidth
  , revOnesVector
  , packBranchDataWrap
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (getFinite, unsafeFinite)
import Data.Vector (Vector, (!!), (:<))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks (AllEvals)
import Pickles.ProofFFI (OraclesResult, Proof, pallasProofOpeningPrechallengesVec, pallasProofOracles)
import Pickles.Prove.Pure.Common (BulletproofBOutput, CombinedInnerProductBatchInput, DerivePlonkInput, FtEval0Input, combinedInnerProductBatch, computeBpChalsAndB, crossFieldDigest, derivePlonk, ftEval0)
import Pickles.Step.Types as Step
import Pickles.Types (StepIPARounds)
import Pickles.Verify.Types (BranchData, PlonkInCircuit, PlonkMinimal, ScalarChallenge)
import Pickles.Wrap.Types as Wrap
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Circuit.DSL (F(..), UnChecked(..))
import Snarky.Circuit.DSL.SizedF (SizedF, coerceViaBits, unsafeFromField, unwrapF, wrapF)
import Snarky.Circuit.Kimchi (Type1, fromShifted, toShifted)
import Snarky.Curves.Class (fromInt)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)

--------------------------------------------------------------------------------
-- Input / output
--------------------------------------------------------------------------------

-- | Input to `wrapComputeDeferredValues`.
-- |
-- | Type parameter `n` is the number of previous proofs that fed into
-- | the step proof being wrapped (= `actual_proofs_verified` in OCaml).
-- | Their `sgs` and already-expanded bp challenges are threaded into
-- | the kimchi oracle call (as `Challenge_polynomial.t list`) and into
-- | `combinedInnerProductBatch`'s `old_bulletproof_challenges`.
-- |
-- | Field shape:
-- |
-- | * step proof commitments live on the Vesta curve (base field =
-- |   `Vesta.BaseField` = `Pallas.ScalarField` = `Wrap.Field`), so
-- |   `prevSgs` coordinates are in `Wrap.Field`;
-- | * the expanded bp challenges carried alongside are in
-- |   `Step.Field` = `Tick.Field`.
type WrapDeferredValuesInput n =
  { -- ===== The step proof being wrapped and its context. =====
    proof :: Proof Vesta.G Step.Field
  , verifierIndex :: VerifierIndex Vesta.G Step.Field
  , publicInput :: Array Step.Field

  -- ===== Polynomial evaluations from the step proof (recombined). =====
  --
  -- Caller builds this from `proof{Z,Witness,Coefficient,Sigma,Index}Evals`
  -- and oracle public evals.
  , allEvals :: AllEvals Step.Field
  , pEval0Chunks :: Array Step.Field

  -- ===== Step domain info. =====
  , domainLog2 :: Int
  , zkRows :: Int
  , srsLengthLog2 :: Int
  , generator :: Step.Field
  , shifts :: Vector 7 Step.Field
  , vanishesOnZk :: Step.Field
  , omegaForLagrange :: { zkRows :: Boolean, offset :: Int } -> Step.Field

  -- ===== Endo + linearization. =====
  --
  -- `endo` is the step-field scalar endo coefficient
  -- (`Endo.Wrap_inner_curve.scalar` in OCaml, = `endoScalar
  -- @Vesta.BaseField @Vesta.ScalarField` in PS). Used both to expand
  -- raw 128-bit plonk/opening challenges to full step-field values and
  -- by `Plonk_checks.scalars_env` inside `ftEval0`.
  , endo :: Step.Field
  -- `linearizationPoly` is the Tick linearization (=
  -- `Pickles.Linearization.pallas`).
  , linearizationPoly :: LinearizationPoly Step.Field

  -- ===== Previous-proof data (= `actual_proofs_verified` entries). =====
  --
  -- `prevSgs`: each entry is a point on the Vesta curve (step proof's
  -- commitment curve); coordinates live in Vesta's base field =
  -- `Wrap.Field`.
  , prevSgs :: Vector n (AffinePoint Wrap.Field)
  -- `prevChallenges`: already-expanded bp challenges from the previous
  -- step proofs, in the step field. Matches OCaml's
  -- `prev_challenges : ((Backend.Tick.Field.t, _) Vector.t, n) Vector.t`.
  , prevChallenges :: Vector n (Vector StepIPARounds Step.Field)

  -- ===== Output packaging. =====
  --
  -- `proofsVerifiedMask` goes directly into the output `BranchData`.
  -- OCaml derives it from `actual_proofs_verified : n Nat.t`; since PS
  -- can't introspect the type-level `n` at runtime, the caller passes
  -- the two-bit mask explicitly (N0 → [F,F], N1 → [T,F], N2 → [T,T]).
  , proofsVerifiedMask :: Vector 2 Boolean
  }

-- | Output of `wrapComputeDeferredValues`: mirrors OCaml's
-- | `deferred_values_and_hints`.
-- |
-- | * `plonk` / `combinedInnerProduct` / `xi` / `bulletproofPrechallenges` /
-- |   `b` / `branchData` together form
-- |   `Types.Proof_state.Deferred_values.t` (Type1 instantiation,
-- |   step-field values). Matches OCaml's storage convention —
-- |   `bulletproof_challenges` is stored as `Bulletproof_challenge.t =
-- |   { prechallenge : Scalar_challenge.t }`, i.e. **raw 128-bit**,
-- |   not endo-expanded. Callers that need the expanded field values
-- |   (e.g. for `Ipa.Wrap.compute_sg`) read `newBulletproofChallenges`
-- |   instead.
-- | * `xHatEvals` is the pair of public-input polynomial evaluations
-- |   at `(zeta, zeta·omega)`, exactly `x_hat_evals` from OCaml.
-- | * `spongeDigestBeforeEvaluations` = `O.digest_before_evaluations`.
-- | * `oracles` is the raw kimchi `OraclesResult`, exposed so callers
-- |   can reuse it without re-running the FFI.
-- | * `newBulletproofChallenges` is the **endo-expanded** opening
-- |   prechallenges + `b_actual` (= `b_poly(zeta) + r·b_poly(zetaw)`
-- |   over the freshly-derived challenges). Used downstream by
-- |   `Ipa.Wrap.compute_sg` and the wrap-proof handler's
-- |   `next_accumulator` assembly — everywhere the expanded field
-- |   values are wanted instead of the raw 128-bit form.
type WrapDeferredValuesOutput =
  { plonk :: PlonkInCircuit (F Step.Field) (Type1 (F Step.Field))
  , combinedInnerProduct :: Type1 (F Step.Field)
  , xi :: ScalarChallenge (F Step.Field)
  , bulletproofPrechallenges :: Vector StepIPARounds (ScalarChallenge (F Step.Field))
  , b :: Type1 (F Step.Field)
  , branchData :: BranchData Step.Field Boolean
  , xHatEvals :: { zeta :: Step.Field, omegaTimesZeta :: Step.Field }
  , spongeDigestBeforeEvaluations :: Step.Field
  , oracles :: OraclesResult Step.Field
  , newBulletproofChallenges :: BulletproofBOutput StepIPARounds Step.Field
  }

--------------------------------------------------------------------------------
-- wrapComputeDeferredValues
--------------------------------------------------------------------------------

-- | Pure PS port of OCaml `Wrap.For_tests_only.deferred_values`
-- | (`wrap.ml:90-272`). Given a freshly-minted step proof plus its
-- | predecessor `(sg, expanded-bp-challenges)` pairs, computes the
-- | step-field Type1 `Deferred_values.t` that the wrap circuit feeds
-- | into `wrap_main`, together with the `x_hat_evals` and sponge
-- | digest hints.
-- |
-- | Internal structure (OCaml line → PS wiring):
-- |
-- | * 97-107  `O.create_with_public_evals`                 → `pallasProofOracles`
-- | * 108-114 `x_hat` from public_evals / oracle p_eval    → `oracles.publicEval{Zeta,ZetaOmega}`
-- | * 118-132 plonk0 (raw 128-bit challenges)              → `wrapPlonkMinimal`
-- | * 133-148 expand raw chals via `SC.to_field_constant`  → done inside `Common.derivePlonk`
-- | * 149     `domain = Pow_2_roots_of_unity ...`          → caller passes `domainLog2`
-- | * 150     `zetaw = zeta * step_vk.domain.group_gen`    → `zetaField * input.generator`
-- | * 158-164 `evals_of_split_evals`                       → caller recombined upstream
-- | * 165-201 `scalars_env` + `derive_plonk`               → `Common.derivePlonk @Step.Field`
-- | * 202-208 `Type1.derive_plonk` (Tick)                  → same, picked by return type
-- | * 209-224 opening prechals → chals → b                 → `Common.computeBpChalsAndB`
-- | * 226-245 `shift_value` (Type1) of CIP / b             → `toShifted`
-- | * 226-268 assemble `Deferred_values.t`                 → `WrapDeferredValuesOutput`
-- | * 270-271 `x_hat_evals` + `digest_before_evaluations`  → direct FFI projections
wrapComputeDeferredValues
  :: forall n
   . WrapDeferredValuesInput n
  -> WrapDeferredValuesOutput
wrapComputeDeferredValues input =
  let
    -- ===== kimchi oracles (Fp sponge; recursive variant). =====
    --
    -- OCaml step `O.create_with_public_evals` (wrap.ml:98-107) passes a
    -- `Challenge_polynomial.t list` built from `sgs` and
    -- `prev_challenges`. We thread the same pair through the FFI's
    -- `prevChallenges` field; kimchi replays the transcript from the
    -- beginning after absorbing each prev challenge polynomial.
    prevChallengeList
      :: Array
           { sgX :: Wrap.Field
           , sgY :: Wrap.Field
           , challenges :: Array Step.Field
           }
    prevChallengeList =
      Array.fromFoldable
        ( Vector.zipWith
            ( \sg chals ->
                { sgX: sg.x
                , sgY: sg.y
                , challenges: Array.fromFoldable chals
                }
            )
            input.prevSgs
            input.prevChallenges
        )

    oraclesResult :: OraclesResult Step.Field
    oraclesResult = pallasProofOracles input.verifierIndex
      { proof: input.proof
      , publicInput: input.publicInput
      , prevChallenges: prevChallengeList
      }

    -- x_hat: single chunk per side (non-chunked assumption).
    xHatEvals :: { zeta :: Step.Field, omegaTimesZeta :: Step.Field }
    xHatEvals =
      { zeta: oraclesResult.publicEvalZeta
      , omegaTimesZeta: oraclesResult.publicEvalZetaOmega
      }

    -- ===== plonk0 / tick_plonk_minimal. =====
    --
    -- wrap.ml:118-132 assembles `plonk0` with raw 128-bit challenges.
    -- `Common.derivePlonk` does the endo expansion internally via
    -- `expandPlonkMinimal`, so we just carry the raw values here.
    stepPlonkMinimal :: PlonkMinimal (F Step.Field)
    stepPlonkMinimal =
      { alpha: wrapF oraclesResult.alphaChal
      , beta: wrapF oraclesResult.beta
      , gamma: wrapF oraclesResult.gamma
      , zeta: wrapF oraclesResult.zetaChal
      }

    zetaField :: Step.Field
    zetaField = oraclesResult.zeta

    zetaw :: Step.Field
    zetaw = zetaField * input.generator

    -- ===== Type1.derive_plonk (wrap.ml:202-208). =====
    derivePlonkInput :: DerivePlonkInput Step.Field
    derivePlonkInput =
      { plonkMinimal: stepPlonkMinimal
      , w: map _.zeta (Vector.take @7 input.allEvals.witnessEvals)
      , sigma: map _.zeta input.allEvals.sigmaEvals
      , zZeta: input.allEvals.zEvals.zeta
      , zOmegaTimesZeta: input.allEvals.zEvals.omegaTimesZeta
      , shifts: input.shifts
      , generator: input.generator
      , domainLog2: input.domainLog2
      , zkRows: input.zkRows
      , srsLengthLog2: input.srsLengthLog2
      , endo: input.endo
      }

    stepPlonkDerived :: PlonkInCircuit (F Step.Field) (Type1 (F Step.Field))
    stepPlonkDerived = derivePlonk derivePlonkInput

    -- ===== ft_eval0 for the step field (via Common). =====
    --
    -- OCaml inlines this inside `combined_inner_product` (wrap.ml:33-39),
    -- sharing it with the scalars_env built for `derive_plonk`. In PS
    -- the helper is stand-alone.
    ftEval0Input :: FtEval0Input Step.Field
    ftEval0Input =
      { plonkMinimal: stepPlonkMinimal
      , allEvals: input.allEvals
      , pEval0Chunks: input.pEval0Chunks
      , shifts: input.shifts
      , generator: input.generator
      , domainLog2: input.domainLog2
      , zkRows: input.zkRows
      , srsLengthLog2: input.srsLengthLog2
      , endo: input.endo
      , vanishesOnZk: input.vanishesOnZk
      , omegaForLagrange: input.omegaForLagrange
      , linearizationPoly: input.linearizationPoly
      }

    stepFtEval0 :: Step.Field
    stepFtEval0 = ftEval0 ftEval0Input

    -- ===== combined_inner_product (wrap.ml:22-62, 235-245). =====
    --
    -- `oracles.v` = xi, `oracles.u` = r — both already endo-expanded
    -- by the kimchi FFI.
    cipInput :: CombinedInnerProductBatchInput n StepIPARounds Step.Field
    cipInput =
      { allEvals: input.allEvals
      , publicEvals: input.allEvals.publicEvals
      , ftEval0: stepFtEval0
      , ftEval1: input.allEvals.ftEval1
      , oldBulletproofChallenges: input.prevChallenges
      , xi: oraclesResult.v
      , r: oraclesResult.u
      , zeta: zetaField
      , zetaw
      }

    cipActual :: Step.Field
    cipActual = combinedInnerProductBatch cipInput

    -- ===== new bulletproof challenges + b (wrap.ml:209-224). =====
    --
    -- `O.opening_prechallenges` returns the raw 128-bit scalar
    -- challenges from the IPA round loop. We wrap each into a
    -- `SizedF 128` and feed through `computeBpChalsAndB`, which endo-
    -- expands them and evaluates `b_poly(zeta) + r·b_poly(zetaw)`.
    rawPrechalsVec :: Vector StepIPARounds (SizedF 128 Step.Field)
    rawPrechalsVec = map (unsafePartial unsafeFromField)
      ( pallasProofOpeningPrechallengesVec input.verifierIndex
          { proof: input.proof
          , publicInput: input.publicInput
          , prevChallenges: prevChallengeList
          }
      )

    newBpResult :: BulletproofBOutput StepIPARounds Step.Field
    newBpResult = computeBpChalsAndB
      { rawPrechallenges: rawPrechalsVec
      , endo: input.endo
      , zeta: zetaField
      , zetaw
      , r: oraclesResult.u
      }

    -- ===== branch_data (wrap.ml:246-260). =====
    branchDataOut :: BranchData Step.Field Boolean
    branchDataOut =
      { domainLog2: fromInt input.domainLog2
      , proofsVerifiedMask: input.proofsVerifiedMask
      }
  in
    { plonk: stepPlonkDerived
    , combinedInnerProduct: toShifted (F cipActual)
    , xi: wrapF oraclesResult.vChal
    , bulletproofPrechallenges: map wrapF rawPrechalsVec
    , b: toShifted (F newBpResult.b)
    , branchData: branchDataOut
    , xHatEvals
    , spongeDigestBeforeEvaluations: oraclesResult.fqDigest
    , oracles: oraclesResult
    , newBulletproofChallenges: newBpResult
    }

--------------------------------------------------------------------------------
-- Statement assembly — cross-field pack the deferred values into the
-- wrap circuit's public input (`Wrap.StatementPacked`).
--------------------------------------------------------------------------------

-- | Input to `assembleWrapMainInput`.
-- |
-- | * `deferredValues` — the step-field `WrapDeferredValuesOutput`
-- |   from `wrapComputeDeferredValues`.
-- | * `messagesForNextStepProofDigest` — the **hashed**
-- |   `prev_statement.proof_state.messages_for_next_step_proof` in the
-- |   step field. OCaml computes this via
-- |   `Common.hash_messages_for_next_step_proof`
-- |   (`wrap.ml:327-331`); the PS helper is
-- |   `Pickles.Step.MessageHash.hashMessagesForNextStepProofPure`.
-- | * `messagesForNextWrapProofDigest` — the **hashed**
-- |   `next_statement.proof_state.messages_for_next_wrap_proof` in the
-- |   wrap field. OCaml computes this via
-- |   `Wrap_hack.hash_messages_for_next_wrap_proof`
-- |   (`wrap.ml:554`); the PS helper is
-- |   `Pickles.Wrap.MessageHash.hashMessagesForNextWrapProofPureGeneral`.
type AssembleWrapMainInputInput =
  { deferredValues :: WrapDeferredValuesOutput
  , messagesForNextStepProofDigest :: Step.Field
  , messagesForNextWrapProofDigest :: Wrap.Field
  }

-- | Cross-field convert a same-field step Type1 shifted value
-- | (produced in the step field by `Common.derivePlonk`) into the
-- | cross-field wrap Type1 representation the wrap statement stores.
-- |
-- | Round-trip through the step-field same-field instance
-- | (`fromShifted :: Type1 (F Step.Field) -> F Step.Field`) and then
-- | the cross-field instance
-- | (`toShifted :: F Step.Field -> Type1 (F Wrap.Field)`). Both instances
-- | are defined in `Snarky.Types.Shifted`; the compiler picks them via
-- | the type annotations on the intermediate and the result.
crossFieldType1Step :: Type1 (F Step.Field) -> Type1 (F Wrap.Field)
crossFieldType1Step t =
  toShifted (fromShifted t :: F Step.Field)

-- | Coerce a `SizedF 128 (F Step.Field)` to `SizedF 128 (F Wrap.Field)`
-- | via bit decomposition. Safe because 128 < 255 = field size.
crossFieldSized128
  :: SizedF 128 (F Step.Field)
  -> SizedF 128 (F Wrap.Field)
crossFieldSized128 s = wrapF (coerceViaBits (unwrapF s))

-- | Width of the packed proofs-verified mask in `Branch_data.pack`.
-- |
-- | OCaml spells this inline as `Nat.N2.n` inside
-- | `Branch_data.pack` / `composition_types.ml`. It's the **global
-- | pickles cap** on `max_proofs_verified`: the mask is always
-- | padded to this width regardless of any particular circuit's
-- | `mpv`. Not to be confused with `Pickles.Types.MaxProofsVerified`
-- | (a per-circuit type alias slated to become polymorphic) or
-- | `PaddedLength` (the wrap_hack padding target). All three equal
-- | 2 today but have independent semantics.
branchDataMaskWidth :: Int
branchDataMaskWidth = 2

-- | Pure port of OCaml's `ones_vector ~first_zero:mostRecentWidth |>
-- | Vector.rev`, padded to `branchDataMaskWidth`. Entry `i` is true
-- | iff `i >= branchDataMaskWidth - mostRecentWidth`. For
-- | `mostRecentWidth ∈ {0, 1, 2}`:
-- |
-- |   0 → [F, F]
-- |   1 → [F, T]
-- |   2 → [T, T]
-- |
-- | This is the `proofsVerifiedMask` field consumed by
-- | `packBranchDataWrap`. The wrap-side `wrapMain` block1 computes
-- | the same reversed mask in-circuit (with a different bit
-- | convention that produces the same packed value, see the comment
-- | there).
revOnesVector :: Int -> Vector 2 Boolean
revOnesVector mostRecentWidth =
  Vector.generate @2 \i ->
    getFinite i >= branchDataMaskWidth - mostRecentWidth

-- | Port of OCaml's `Branch_data.pack` — packs the mask + log2 into a
-- | single wrap-field element. Encoding: `4 · domain_log2 + mask[0] +
-- | 2 · mask[1]`. Matches `branch_data.ml` and the existing PS
-- | circuit check.
packBranchDataWrap
  :: BranchData Step.Field Boolean
  -> Wrap.Field
packBranchDataWrap { domainLog2, proofsVerifiedMask } =
  let
    boolToField :: Boolean -> Wrap.Field
    boolToField b = if b then one else zero

    m0 :: Wrap.Field
    m0 = boolToField (proofsVerifiedMask !! unsafeFinite @2 0)

    m1 :: Wrap.Field
    m1 = boolToField (proofsVerifiedMask !! unsafeFinite @2 1)

    two :: Wrap.Field
    two = fromInt 2

    four :: Wrap.Field
    four = fromInt 4

    log2W :: Wrap.Field
    log2W = crossFieldDigest domainLog2
  in
    four * log2W + m0 + two * m1

-- | Pure PS port of OCaml's wrap-statement packing (wrap.ml:458-567
-- | plus the `Spec.wrap_packed_typ` allocation discipline in
-- | `composition_types.ml`).
-- |
-- | Takes the step-field `WrapDeferredValuesOutput` + the two message
-- | hashes (already computed by the caller) and builds the public
-- | input `wrap_main` consumes. All cross-field conversions live
-- | here, not in `wrapComputeDeferredValues` — keeping that function
-- | semantically aligned with OCaml's `deferred_values`, which also
-- | stays in the step field.
-- |
-- | OCaml field order (`Wrap.Statement.In_circuit.to_data`):
-- |
-- | * `fpFields` (5, Type1 in wrap field):
-- |     combined_inner_product, b, zetaToSrsLength, zetaToDomainSize, perm
-- | * `challenges` (2, raw 128-bit): beta, gamma
-- | * `scalarChallenges` (3, raw 128-bit): alpha, zeta, xi
-- | * `digests` (3, wrap field):
-- |     spongeDigest, msgForNextWrap, msgForNextStep
-- | * `bulletproofChallenges` (StepIPARounds, raw 128-bit)
-- | * `branchData` (1, packed into a wrap-field element)
-- | * `featureFlags` (8, all constant zero)
-- | * `lookupOptFlag` (1, zero) + `lookupOptScalarChallenge` (1, zero)
assembleWrapMainInput
  :: AssembleWrapMainInputInput
  -> Wrap.StatementPacked StepIPARounds (Type1 (F Wrap.Field)) (F Wrap.Field) Boolean
assembleWrapMainInput input =
  let
    dv = input.deferredValues

    -- ===== 5 Type1 fp fields (cross-field from Step.Field) =====
    fpFields :: Vector 5 (Type1 (F Wrap.Field))
    fpFields =
      crossFieldType1Step dv.combinedInnerProduct
        :< crossFieldType1Step dv.b
        :< crossFieldType1Step dv.plonk.zetaToSrsLength
        :< crossFieldType1Step dv.plonk.zetaToDomainSize
        :< crossFieldType1Step dv.plonk.perm
        :< Vector.nil

    -- ===== Raw 128-bit challenges (cross-field via bit coercion) =====
    --
    -- beta / gamma: OCaml `challenges` vector, in `to_data` order.
    challenges :: Vector 2 (UnChecked (SizedF 128 (F Wrap.Field)))
    challenges =
      UnChecked (crossFieldSized128 dv.plonk.beta)
        :< UnChecked (crossFieldSized128 dv.plonk.gamma)
        :< Vector.nil

    -- alpha / zeta / xi: `scalar_challenges` vector.
    scalarChallenges :: Vector 3 (UnChecked (SizedF 128 (F Wrap.Field)))
    scalarChallenges =
      UnChecked (crossFieldSized128 dv.plonk.alpha)
        :< UnChecked (crossFieldSized128 dv.plonk.zeta)
        :< UnChecked (crossFieldSized128 dv.xi)
        :< Vector.nil

    -- ===== 3 digests (all wrap field) =====
    --
    -- Order matches OCaml's `to_data`:
    --   (sponge_digest, msg_for_next_wrap, msg_for_next_step)
    digests :: Vector 3 (F Wrap.Field)
    digests = map F
      ( crossFieldDigest dv.spongeDigestBeforeEvaluations
          :< input.messagesForNextWrapProofDigest
          :< crossFieldDigest input.messagesForNextStepProofDigest
          :< Vector.nil
      )

    -- ===== Bulletproof prechallenges (raw 128-bit, cross-field) =====
    bulletproofChallenges
      :: Vector StepIPARounds (UnChecked (SizedF 128 (F Wrap.Field)))
    bulletproofChallenges =
      map (UnChecked <<< crossFieldSized128) dv.bulletproofPrechallenges

    -- ===== Branch data (packed into a single wrap-field element) =====
    branchData :: F Wrap.Field
    branchData = F (packBranchDataWrap dv.branchData)

    -- ===== Feature flag + lookup slots — constant zeros =====
    --
    -- OCaml's `Spec.T.Constant` in `wrap_packed_typ` still allocates
    -- these as field elements (with the check skipped). For
    -- `Features.Full.none` + `lookup.use = No`, all slots are zero.
    featureFlags :: Vector 8 (F Wrap.Field)
    featureFlags = Vector.replicate zero
  in
    Wrap.StatementPacked
      { fpFields
      , challenges
      , scalarChallenges
      , digests
      , bulletproofChallenges
      , branchData
      , featureFlags
      , lookupOptFlag: zero
      , lookupOptScalarChallenge: zero
      }

