-- | Step-circuit-specific Pickles types. Extracted from `Pickles.Types`
-- | because their importers are confined to `Pickles.Step.*` /
-- | `Pickles.Prove.*` / `Pickles.Sideload.*` / circuit-diff fixtures —
-- | no wrap-side module imports any of these directly.
module Pickles.Step.Types
  ( UnfinalizedFieldCount
  , BranchData(..)
  , WrapProof(..)
  , FopProofState(..)
  , ProofState(..)
  , PerProofWitness(..)
  ) where

import Prelude

import Data.Reflectable (class Reflectable)
import Data.Tuple.Nested (Tuple10, Tuple2, Tuple3, Tuple5, tuple10, tuple2, tuple3, tuple5, uncurry10, uncurry2, uncurry3, uncurry5)
import Data.Vector (Vector)
import Partial.Unsafe (unsafePartial)
import Pickles.Field (StepField)
import Pickles.Types (StepAllEvals, WrapProofMessages, WrapProofOpening)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (BoolVar, F, FVar, UnChecked, const_, label)
import Snarky.Circuit.DSL.Monad (class CheckedType, check)
import Snarky.Circuit.DSL.SizedF (SizedF, unsafeFromField)
import Snarky.Circuit.Kimchi.EndoScalar (toField) as EndoScalar
import Snarky.Circuit.Types (class CircuitType, genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits, class HasEndo, EndoScalar(..), endoScalar)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint)
import Type.Proxy (Proxy(..))

-- | Number of step-field scalars produced when a per-proof
-- | `Unfinalized` is laid out into the step circuit's public input.
-- | Used in `Mul mpvMax UnfinalizedFieldCount unfsTotal` constraints
-- | that size the step PI's unfinalized-proofs region.
type UnfinalizedFieldCount = 32

-- | Per-proof branch data: which previous proof slot is in use, plus the
-- | wrap proof's domain log2.
-- |
-- | OCaml hlist order: (mask0, mask1, domainLog2). Allocation order matches
-- | the OCaml `Branch_data.typ`.
-- |
-- | The `CheckedType` instance:
-- | - Boolean checks on the masks (via Tuple3 delegation to inner instances)
-- | - Endoscalar check on `domainLog2` (matching OCaml's
-- |   `Branch_data.typ.check`, which expands the 16-bit log2 into a full
-- |   f element through the endo).
-- |
-- | The endo constant is determined by `f` via the `HasEndo` class — for
-- | `f = StepField` (= Vesta.ScalarField), the base f is Vesta.BaseField
-- | and `endoScalar @Vesta.BaseField @StepField` gives the right value.
-- |
-- | Reference: branch_data.ml, mina/src/lib/crypto/pickles/impls.ml
newtype BranchData f b = BranchData
  { mask0 :: b
  , mask1 :: b
  , domainLog2 :: f
  }

instance
  ( CircuitType f a fvar
  , CircuitType f b bvar
  ) =>
  CircuitType f (BranchData a b) (BranchData fvar bvar) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(Tuple3 b b a))
  valueToFields (BranchData r) = genericValueToFields (tuple3 r.mask0 r.mask1 r.domainLog2)
  fieldsToValue fs =
    let
      tup :: Tuple3 b b a
      tup = genericFieldsToValue fs
    in
      uncurry3 (\mask0 mask1 domainLog2 -> BranchData { mask0, mask1, domainLog2 }) tup
  varToFields (BranchData r) = genericVarToFields @(Tuple3 b b a) (tuple3 r.mask0 r.mask1 r.domainLog2)
  fieldsToVar fs =
    let
      tup :: Tuple3 bvar bvar fvar
      tup = genericFieldsToVar @(Tuple3 b b a) fs
    in
      uncurry3 (\mask0 mask1 domainLog2 -> BranchData { mask0, mask1, domainLog2 }) tup

-- | CheckedType for the var representation: Boolean checks on the masks
-- | plus the endoscalar check on domainLog2.
instance
  ( FieldSizeInBits f n
  , Compare 16 n LT
  , HasEndo basef f
  , CheckedType f (KimchiConstraint f) (Tuple3 (BoolVar f) (BoolVar f) (FVar f))
  ) =>
  CheckedType f (KimchiConstraint f) (BranchData (FVar f) (BoolVar f)) where
  check (BranchData r) = label "branch-data-check" do
    -- Boolean checks on masks + (no-op) check on domLog2 via Tuple3 delegation
    check (tuple3 r.mask0 r.mask1 r.domainLog2)
    -- Endoscalar check on domainLog2 (matches OCaml Branch_data.typ.check)
    let EndoScalar e = endoScalar @basef @f
    _ <- EndoScalar.toField @1 (unsafePartial (unsafeFromField r.domainLog2) :: SizedF 16 (FVar f)) (const_ e)
    pure unit

-- | Combined wrap proof: messages + opening, in OCaml's `Wrap_proof.Checked.t` order.
-- |
-- | Reference: wrap_proof.ml — `{ messages; opening }` allocated via
-- | `of_hlistable` which gives field order (messages first, then opening).
newtype WrapProof :: Int -> Type -> Type -> Type
newtype WrapProof n pt sf = WrapProof
  { messages :: WrapProofMessages pt
  , opening :: WrapProofOpening n pt sf
  }

instance
  ( CircuitType f a avar
  , CircuitType f b bvar
  , Reflectable n Int
  ) =>
  CircuitType f (WrapProof n a b) (WrapProof n avar bvar) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(Tuple2 (WrapProofMessages a) (WrapProofOpening n a b)))
  valueToFields (WrapProof r) = genericValueToFields (tuple2 r.messages r.opening)
  fieldsToValue fs =
    let
      tup :: Tuple2 (WrapProofMessages a) (WrapProofOpening n a b)
      tup = genericFieldsToValue fs
    in
      uncurry2 (\messages opening -> WrapProof { messages, opening }) tup
  varToFields (WrapProof r) = genericVarToFields @(Tuple2 (WrapProofMessages a) (WrapProofOpening n a b)) (tuple2 r.messages r.opening)
  fieldsToVar fs =
    let
      tup :: Tuple2 (WrapProofMessages avar) (WrapProofOpening n avar bvar)
      tup = genericFieldsToVar @(Tuple2 (WrapProofMessages a) (WrapProofOpening n a b)) fs
    in
      uncurry2 (\messages opening -> WrapProof { messages, opening }) tup

instance
  ( CheckedType f c avar
  , CheckedType f c bvar
  , Reflectable n Int
  ) =>
  CheckedType f c (WrapProof n avar bvar) where
  check (WrapProof r) = check (tuple2 r.messages r.opening)

-- | FOP proof state: deferred values + sponge digest, in OCaml's to_data order.
-- |
-- | OCaml to_data order (from `Spec.pack` of `Per_proof_witness.proof_state`):
-- |   cip, b, zetaToSrs, zetaToDom, perm,    -- 5 plain fields (Type1 in step)
-- |   spongeDigest,                          -- digest (plain f)
-- |   beta, gamma,                           -- 2 128-bit challenges
-- |   alpha, zeta, xi,                       -- 3 128-bit scalar challenges
-- |   bulletproofChallenges                  -- Vector d of 128-bit challenges
-- |
-- | The `UnChecked (SizedF 128 f)` fields are claimed-128-bit but NOT range-checked
-- | at allocation (matching OCaml's `Challenge.typ = Typ.f`). Use
-- | `challengeToSizedF` at the boundary with FOP/IVP code that needs
-- | `SizedF 128 f`.
-- |
-- | Note: the `branchData` is allocated separately within the per-proof witness;
-- | it is NOT part of this newtype.
newtype FopProofState (d :: Int) f = FopProofState
  { combinedInnerProduct :: f
  , b :: f
  , zetaToSrsLength :: f
  , zetaToDomainSize :: f
  , perm :: f
  , spongeDigest :: f
  , beta :: UnChecked (SizedF 128 f)
  , gamma :: UnChecked (SizedF 128 f)
  , alpha :: UnChecked (SizedF 128 f)
  , zeta :: UnChecked (SizedF 128 f)
  , xi :: UnChecked (SizedF 128 f)
  , bulletproofChallenges :: Vector d (UnChecked (SizedF 128 f))
  }

-- | Tuple shape for FopProofState (parameterized by element type x).
-- | Used by both value (x = F f) and var (x = FVar f) instances.
type FopProofStateTuple d x =
  Tuple2
    (Tuple10 x x x x x x (UnChecked (SizedF 128 x)) (UnChecked (SizedF 128 x)) (UnChecked (SizedF 128 x)) (UnChecked (SizedF 128 x)))
    (Tuple2 (UnChecked (SizedF 128 x)) (Vector d (UnChecked (SizedF 128 x))))

instance
  ( FieldSizeInBits f m
  , Reflectable d Int
  ) =>
  CircuitType f (FopProofState d (F f)) (FopProofState d (FVar f)) where
  sizeInFields pf _ = genericSizeInFields pf (Proxy @(FopProofStateTuple d (F f)))
  valueToFields (FopProofState r) = genericValueToFields
    ( tuple2
        (tuple10 r.combinedInnerProduct r.b r.zetaToSrsLength r.zetaToDomainSize r.perm r.spongeDigest r.beta r.gamma r.alpha r.zeta)
        (tuple2 r.xi r.bulletproofChallenges)
    )
  fieldsToValue fs =
    let
      tup :: FopProofStateTuple d (F f)
      tup = genericFieldsToValue fs
    in
      uncurry2
        ( \t10 t2 ->
            uncurry10
              ( \cip b zetaToSrsLength zetaToDomainSize perm spongeDigest beta gamma alpha zeta ->
                  uncurry2
                    ( \xi bulletproofChallenges ->
                        FopProofState { combinedInnerProduct: cip, b, zetaToSrsLength, zetaToDomainSize, perm, spongeDigest, beta, gamma, alpha, zeta, xi, bulletproofChallenges }
                    )
                    t2
              )
              t10
        )
        tup
  varToFields (FopProofState r) = genericVarToFields
    @(FopProofStateTuple d (F f))
    ( tuple2
        (tuple10 r.combinedInnerProduct r.b r.zetaToSrsLength r.zetaToDomainSize r.perm r.spongeDigest r.beta r.gamma r.alpha r.zeta)
        (tuple2 r.xi r.bulletproofChallenges)
    )
  fieldsToVar fs =
    let
      tup :: FopProofStateTuple d (FVar f)
      tup = genericFieldsToVar @(FopProofStateTuple d (F f)) fs
    in
      uncurry2
        ( \t10 t2 ->
            uncurry10
              ( \cip b zetaToSrsLength zetaToDomainSize perm spongeDigest beta gamma alpha zeta ->
                  uncurry2
                    ( \xi bulletproofChallenges ->
                        FopProofState { combinedInnerProduct: cip, b, zetaToSrsLength, zetaToDomainSize, perm, spongeDigest, beta, gamma, alpha, zeta, xi, bulletproofChallenges }
                    )
                    t2
              )
              t10
        )
        tup

instance (CheckedType f c var) => CheckedType f c (FopProofState d var) where
  check (FopProofState r) = check
    ( tuple2
        (tuple10 r.combinedInnerProduct r.b r.zetaToSrsLength r.zetaToDomainSize r.perm r.spongeDigest r.beta r.gamma r.alpha r.zeta)
        (tuple2 r.xi r.bulletproofChallenges)
    )

-- | Step proof state: deferred values + sponge digest + branch data, in
-- | the OCaml allocation order from `Wrap.Proof_state.In_circuit`'s
-- | `Spec.packed_typ` flattening.
-- |
-- | The to_data order puts the FopProofState fields first (cip, b, zetaToSrs,
-- | zetaToDom, perm, sponge, beta, gamma, alpha, zeta, xi, bpChals), then
-- | branchData (mask0, mask1, domLog2 with endoscalar check) at the end.
-- |
-- | Reference: composition_types.ml `Wrap.Proof_state` allocation
-- | `d` parameter is the step IPA round count (structurally always
-- | `StepIPARounds` for the Pasta cycle; kept polymorphic here to mirror
-- | OCaml `Proof_state.t`'s `'bulletproof_challenges` type parameter,
-- | so `Pickles.Prove.Step` and friends can stay polymorphic in `ds`
-- | and only concretize at the top-level binding).
newtype ProofState (d :: Int) f b = ProofState
  { fopState :: FopProofState d f
  , branchData :: BranchData f b
  }

instance
  ( FieldSizeInBits f m
  , Reflectable d Int
  ) =>
  CircuitType f (ProofState d (F f) Boolean) (ProofState d (FVar f) (BoolVar f)) where
  sizeInFields pf _ = genericSizeInFields pf
    (Proxy @(Tuple2 (FopProofState d (F f)) (BranchData (F f) Boolean)))
  valueToFields (ProofState r) = genericValueToFields (tuple2 r.fopState r.branchData)
  fieldsToValue fs =
    let
      tup :: Tuple2 (FopProofState d (F f)) (BranchData (F f) Boolean)
      tup = genericFieldsToValue fs
    in
      uncurry2 (\fopState branchData -> ProofState { fopState, branchData }) tup
  varToFields (ProofState r) = genericVarToFields
    @(Tuple2 (FopProofState d (F f)) (BranchData (F f) Boolean))
    (tuple2 r.fopState r.branchData)
  fieldsToVar fs =
    let
      tup :: Tuple2 (FopProofState d (FVar f)) (BranchData (FVar f) (BoolVar f))
      tup = genericFieldsToVar @(Tuple2 (FopProofState d (F f)) (BranchData (F f) Boolean)) fs
    in
      uncurry2 (\fopState branchData -> ProofState { fopState, branchData }) tup

instance
  ( CheckedType f (KimchiConstraint f) (FopProofState d (FVar f))
  , CheckedType f (KimchiConstraint f) (BranchData (FVar f) (BoolVar f))
  ) =>
  CheckedType f (KimchiConstraint f) (ProofState d (FVar f) (BoolVar f)) where
  check (ProofState r) = check (tuple2 r.fopState r.branchData)

-- | Composed per-proof witness: the OCaml `Per_proof_witness.No_app_state.t`.
-- |
-- | OCaml hlist order (5 components after dropping the Unit statement):
-- |   1. wrap_proof  : Wrap_proof.Checked.t      (messages + opening)
-- |   2. proof_state : Wrap.Proof_state.In_circuit.t  (deferred values + sponge_digest + branch_data, with msg_for_next_wrap=unit)
-- |   3. prev_proof_evals : All_evals.In_circuit.t
-- |   4. prev_challenges : (Vector field tick, max_proofs_verified) Vector
-- |   5. prev_challenge_polynomial_commitments : (inner_curve, max_proofs_verified) Vector
-- |
-- | This is one structured `exists` call in OCaml step_main:
-- |   `exists (Prev_typ.f prev_proof_typs) ~request:Req.Proof_with_datas`
-- |
-- | Reference: per_proof_witness.ml, step_main.ml
-- |
-- | Type parameters:
-- |   - `n`  : max_proofs_verified (= the outer Vector length)
-- |   - `ds` : step-side IPA round count (= `Tick.Rounds.n` = `StepIPARounds`
-- |            structurally). Parameterizes the inner `ProofState`'s
-- |            `FopProofState` and the `prevChallenges` vector length.
-- |   - `dw` : wrap-side IPA round count (= `Tock.Rounds.n` = `WrapIPARounds`
-- |            structurally). Parameterizes the inner `WrapProof`'s
-- |            opening proof length.
-- |
-- | Both `ds` and `dw` are kept polymorphic to mirror OCaml's
-- | `Per_proof_witness.t`, which takes the bulletproof-challenges vector
-- | type as a separate parameter (see `composition_types.ml:188`). The
-- | Pasta protocol constants only appear at top-level bindings that
-- | instantiate the type.
newtype PerProofWitness (n :: Int) (ds :: Int) (dw :: Int) f sf b = PerProofWitness
  { wrapProof :: WrapProof dw (WeierstrassAffinePoint PallasG f) sf
  , proofState :: ProofState ds f b
  , prevEvals :: StepAllEvals f
  , prevChallenges :: Vector n (UnChecked (Vector ds f))
  , prevSgs :: Vector n (WeierstrassAffinePoint PallasG f)
  }

-- | Tuple shape for PerProofWitness, parameterized by:
-- |   - n / ds / dw : vector lengths (propagated from the newtype)
-- |   - x           : field element type (F f or FVar f)
-- |   - sf          : shifted-f type
-- |   - b           : boolean type
type PerProofWitnessTuple n ds dw x sf b =
  Tuple5
    (WrapProof dw (WeierstrassAffinePoint PallasG x) sf)
    (ProofState ds x b)
    (StepAllEvals x)
    (Vector n (UnChecked (Vector ds x)))
    (Vector n (WeierstrassAffinePoint PallasG x))

instance
  ( FieldSizeInBits f m
  , CircuitType f sf sfvar
  , Reflectable n Int
  , Reflectable ds Int
  , Reflectable dw Int
  ) =>
  CircuitType f
    (PerProofWitness n ds dw (F f) sf Boolean)
    (PerProofWitness n ds dw (FVar f) sfvar (BoolVar f)) where
  sizeInFields pf _ = genericSizeInFields pf
    (Proxy @(PerProofWitnessTuple n ds dw (F f) sf Boolean))
  valueToFields (PerProofWitness r) = genericValueToFields
    (tuple5 r.wrapProof r.proofState r.prevEvals r.prevChallenges r.prevSgs)
  fieldsToValue fs =
    let
      tup :: PerProofWitnessTuple n ds dw (F f) sf Boolean
      tup = genericFieldsToValue fs
    in
      uncurry5
        ( \wrapProof proofState prevEvals prevChallenges prevSgs ->
            PerProofWitness { wrapProof, proofState, prevEvals, prevChallenges, prevSgs }
        )
        tup
  varToFields (PerProofWitness r) = genericVarToFields
    @(PerProofWitnessTuple n ds dw (F f) sf Boolean)
    (tuple5 r.wrapProof r.proofState r.prevEvals r.prevChallenges r.prevSgs)
  fieldsToVar fs =
    let
      tup :: PerProofWitnessTuple n ds dw (FVar f) sfvar (BoolVar f)
      tup = genericFieldsToVar @(PerProofWitnessTuple n ds dw (F f) sf Boolean) fs
    in
      uncurry5
        ( \wrapProof proofState prevEvals prevChallenges prevSgs ->
            PerProofWitness { wrapProof, proofState, prevEvals, prevChallenges, prevSgs }
        )
        tup

instance
  ( CheckedType StepField (KimchiConstraint StepField) (WrapProof dw (WeierstrassAffinePoint PallasG (FVar StepField)) sfvar)
  , CheckedType StepField (KimchiConstraint StepField) (ProofState ds (FVar StepField) (BoolVar StepField))
  , CheckedType StepField (KimchiConstraint StepField) (StepAllEvals (FVar StepField))
  , Reflectable n Int
  , Reflectable ds Int
  ) =>
  CheckedType StepField (KimchiConstraint StepField) (PerProofWitness n ds dw (FVar StepField) sfvar (BoolVar StepField)) where
  check (PerProofWitness r) =
    let
      tup :: PerProofWitnessTuple n ds dw (FVar StepField) sfvar (BoolVar StepField)
      tup = tuple5 r.wrapProof r.proofState r.prevEvals r.prevChallenges r.prevSgs
    in
      check tup
