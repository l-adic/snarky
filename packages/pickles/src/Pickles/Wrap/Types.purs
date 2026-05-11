-- | Wrap-circuit-specific Pickles types. Extracted from `Pickles.Types`
-- | because their importers are confined to `Pickles.Wrap.*` /
-- | `Pickles.Prove.*` / `Pickles.Sideload.*` / circuit-diff fixtures —
-- | no step-side module imports any of these directly.
module Pickles.Wrap.Types
  ( Field
  , IvpBaseline
  , PrevProofState(..)
  , StatementPacked(..)
  ) where

import Data.Foldable (traverse_)
import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple2, Tuple3, Tuple7, tuple2, tuple3, tuple7, uncurry2, uncurry3, uncurry7)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Types (PerProofUnfinalized, WrapIPARounds)
import Snarky.Circuit.DSL (BoolVar, F, FVar, UnChecked)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.DSL.SizedF (SizedF)
import Snarky.Circuit.Types (class CircuitType, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Curves.Pallas as Pallas
import Type.Proxy (Proxy(..))

-- | Wrap circuit f (Fq = Pallas.ScalarField = Vesta.BaseField).
type Field = Pallas.ScalarField

-- | Wrap circuit's IVP MSM base count minus the per-proof `sg_old`s.
-- | Used in `Add mpv IvpBaseline totalBases` — `totalBases` is
-- | the full count of bases the wrap IVP iterates over, and equals
-- | `mpv` (one `sg_old` per proof) plus this baseline (everything
-- | else: SRS commitments, sigma commitments, etc.). Mirrors OCaml
-- | `Nat.N45.add` in `wrap_verifier.ml:1457`.
type IvpBaseline = 45

-- | The combined wrap-circuit `Req.Proof_state` allocation: `mpv`
-- | unfinalized proofs (Type2-shifted scalars) + `messages_for_next_step_proof`.
-- |
-- | OCaml's `wrap_typ` over `Types.Step.Proof_state` puts `unfinalized_proofs`
-- | first (a Vector of length `mpv`) and `messages_for_next_step_proof` second.
-- |
-- | Reference: mina/src/lib/crypto/pickles/composition_types/composition_types.ml
-- | (`Types.Step.Proof_state.wrap_typ`) and `wrap_main.ml:267` exists call.
newtype PrevProofState (mpv :: Int) sf f b = PrevProofState
  { unfinalizedProofs :: Vector mpv (PerProofUnfinalized WrapIPARounds sf f b)
  , messagesForNextStepProof :: f
  }

instance
  ( CircuitType f sf sfvar
  , CircuitType f b bvar
  , FieldSizeInBits f m
  , Reflectable mpv Int
  ) =>
  CircuitType f
    (PrevProofState mpv sf (F f) b)
    (PrevProofState mpv sfvar (FVar f) bvar) where
  sizeInFields pf _ = genericSizeInFields pf
    (Proxy @(Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sf (F f) b)) (F f)))
  valueToFields (PrevProofState r) = genericValueToFields
    (tuple2 r.unfinalizedProofs r.messagesForNextStepProof)
  fieldsToValue fs =
    let
      tup :: Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sf (F f) b)) (F f)
      tup = genericFieldsToValue fs
    in
      uncurry2
        ( \unfinalizedProofs messagesForNextStepProof ->
            PrevProofState { unfinalizedProofs, messagesForNextStepProof }
        )
        tup
  varToFields (PrevProofState r) = genericVarToFields
    @(Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sf (F f) b)) (F f))
    (tuple2 r.unfinalizedProofs r.messagesForNextStepProof)
  fieldsToVar fs =
    let
      tup :: Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sfvar (FVar f) bvar)) (FVar f)
      tup = genericFieldsToVar
        @(Tuple2 (Vector mpv (PerProofUnfinalized WrapIPARounds sf (F f) b)) (F f))
        fs
    in
      uncurry2
        ( \unfinalizedProofs messagesForNextStepProof ->
            PrevProofState { unfinalizedProofs, messagesForNextStepProof }
        )
        tup

instance
  ( CheckedType f c (PerProofUnfinalized WrapIPARounds sfvar fvar bvar)
  , CheckedType f c fvar
  ) =>
  CheckedType f c (PrevProofState mpv sfvar fvar bvar) where
  check (PrevProofState r) = check (tuple2 r.unfinalizedProofs r.messagesForNextStepProof)

-------------------------------------------------------------------------------
-- | Wrap statement public input (allocation-side representation)
-- |
-- | This is the type that the wrap circuit's `compile` allocates as the
-- | public input for `wrapMain`. It mirrors the OCaml
-- | `Wrap.Statement.In_circuit` allocation pattern from
-- | `composition_types.ml:776-831` (`In_circuit.to_data`):
-- |
-- |   [ fp                       (* 5: cip, b, ztSrs, ztDom, perm  *)
-- |   ; challenge                (* 2: beta, gamma                 *)
-- |   ; scalar_challenge         (* 3: alpha, zeta, xi             *)
-- |   ; digest                   (* 3: sponge, msg_wrap, msg_step  *)
-- |   ; bulletproof_challenges   (* d: 16 in production            *)
-- |   ; index                    (* 1: branch_data                 *)
-- |   ]
-- |
-- | The challenge fields are wrapped in `UnChecked (SizedF 128 f)` because
-- | OCaml's `Spec.wrap_packed_typ` allocates them via plain `Field.typ`
-- | (no bit-range check at allocation). The bit-size invariant is
-- | re-established later by the consumer that needs it (e.g.,
-- | `Scalar_challenge.to_field_checked` does the bit check inline at
-- | endo-expansion time). This mirrors the existing `PerProofUnfinalized`
-- | pattern in this module — see Step.Main.unpackUnfinalized for the
-- | corresponding `coerce` discipline.
-- |
-- | The 5 fp fields stay as `sf` (= `Type1 (FVar f)` in circuit) because
-- | their `CheckedType` instance models OCaml's `Other_field.check`
-- | (forbidden_shifted_values check). The digests and branch_data are
-- | plain `f` because OCaml allocates them as plain `Field.typ`.
newtype StatementPacked :: Int -> Type -> Type -> Type -> Type
newtype StatementPacked d sf f b = StatementPacked
  { -- 5 Type1 fp fields, in OCaml `to_data` order:
    -- combined_inner_product, b, zetaToSrsLength, zetaToDomainSize, perm
    fpFields :: Vector 5 sf
  -- 2 raw challenges: beta, gamma
  , challenges :: Vector 2 (UnChecked (SizedF 128 f))
  -- 3 scalar challenges: alpha, zeta, xi
  , scalarChallenges :: Vector 3 (UnChecked (SizedF 128 f))
  -- 3 digests: sponge_digest, msg_for_next_wrap, msg_for_next_step
  , digests :: Vector 3 f
  -- d bulletproof challenges
  , bulletproofChallenges :: Vector d (UnChecked (SizedF 128 f))
  -- 1 packed branch_data field
  , branchData :: f
  -- 8 constant feature_flags slots. OCaml's `Spec.T.Constant` in
  -- `wrap_packed_typ` still allocates the underlying `Boolean.typ` field
  -- (with the check skipped, see spec.ml:485-494). For `Features.Full.none`
  -- all 8 are constant `false`. The wrap_main body never reads them.
  , featureFlags :: Vector 8 f
  -- 2 lookup-parameters slots. OCaml's `Lookup_parameters.opt_spec` is
  -- `Spec.T.Opt { inner = Struct [Scalar Challenge]; flag = use; ... }`.
  -- For `lookup.use = No`, `Opt.constant_layout_typ` (opt.ml:118) still
  -- allocates `tuple2 Boolean.typ inner_typ` — that's 1 boolean flag
  -- field plus 1 scalar challenge field, both unconstrained. The wrap
  -- circuit never reads them.
  , lookupOptFlag :: f
  , lookupOptScalarChallenge :: f
  }

-- | Tuple shape mirroring `to_data`. The CircuitType instance delegates
-- | through this tuple, which gives the OCaml hlist field order. The
-- | feature_flags + lookup tail is grouped into a `Tuple3` so the whole
-- | thing fits in `Tuple7`.
type StatementPackedTuple d sf x =
  Tuple7
    (Vector 5 sf)
    (Vector 2 (UnChecked (SizedF 128 x)))
    (Vector 3 (UnChecked (SizedF 128 x)))
    (Vector 3 x)
    (Vector d (UnChecked (SizedF 128 x)))
    x
    (Tuple3 (Vector 8 x) x x)

instance
  ( CircuitType f sf sfvar
  , FieldSizeInBits f m
  , Reflectable d Int
  ) =>
  CircuitType f
    (StatementPacked d sf (F f) Boolean)
    (StatementPacked d sfvar (FVar f) (BoolVar f)) where
  sizeInFields pf _ = genericSizeInFields pf
    (Proxy @(StatementPackedTuple d sf (F f)))
  valueToFields (StatementPacked r) = genericValueToFields
    ( tuple7 r.fpFields r.challenges r.scalarChallenges r.digests r.bulletproofChallenges r.branchData
        (tuple3 r.featureFlags r.lookupOptFlag r.lookupOptScalarChallenge)
    )
  fieldsToValue fs =
    let
      tup :: StatementPackedTuple d sf (F f)
      tup = genericFieldsToValue fs
    in
      uncurry7
        ( \fpFields challenges scalarChallenges digests bulletproofChallenges branchData tail3 ->
            uncurry3
              ( \featureFlags lookupOptFlag lookupOptScalarChallenge ->
                  StatementPacked
                    { fpFields
                    , challenges
                    , scalarChallenges
                    , digests
                    , bulletproofChallenges
                    , branchData
                    , featureFlags
                    , lookupOptFlag
                    , lookupOptScalarChallenge
                    }
              )
              tail3
        )
        tup
  varToFields (StatementPacked r) = genericVarToFields
    @(StatementPackedTuple d sf (F f))
    ( tuple7 r.fpFields r.challenges r.scalarChallenges r.digests r.bulletproofChallenges r.branchData
        (tuple3 r.featureFlags r.lookupOptFlag r.lookupOptScalarChallenge)
    )
  fieldsToVar fs =
    let
      tup :: StatementPackedTuple d sfvar (FVar f)
      tup = genericFieldsToVar @(StatementPackedTuple d sf (F f)) fs
    in
      uncurry7
        ( \fpFields challenges scalarChallenges digests bulletproofChallenges branchData tail3 ->
            uncurry3
              ( \featureFlags lookupOptFlag lookupOptScalarChallenge ->
                  StatementPacked
                    { fpFields
                    , challenges
                    , scalarChallenges
                    , digests
                    , bulletproofChallenges
                    , branchData
                    , featureFlags
                    , lookupOptFlag
                    , lookupOptScalarChallenge
                    }
              )
              tail3
        )
        tup

instance
  ( CheckedType f c sfvar
  , CheckedType f c fvar
  ) =>
  CheckedType f c (StatementPacked d sfvar fvar bvar) where
  check (StatementPacked r) =
    -- Only the fp fields get a non-trivial check (Type1's
    -- forbidden_shifted_values, mirroring OCaml's Other_field.check).
    -- Challenges are UnChecked → no-op. Digests, branchData, featureFlags,
    -- and lookupOpt fields are plain f → no-op. So this `check` reduces to
    -- just the 5 fp checks.
    --
    -- IMPORTANT: emit the checks in REVERSE order. OCaml's `Vector.map`
    -- processes `f x :: map xs ~f` right-to-left (because `::` evaluates
    -- right-to-left), so `Other_field.check` runs on `perm` first and
    -- `combined_inner_product` last. The `Vector.reverse` here matches
    -- that evaluation order so PI-variable copy-cycles line up with OCaml.
    traverse_ check (Vector.reverse r.fpFields)
