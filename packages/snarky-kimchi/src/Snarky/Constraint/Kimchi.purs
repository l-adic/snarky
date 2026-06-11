module Snarky.Constraint.Kimchi
  ( KimchiConstraint(..)
  , KimchiGate
  , class KimchiVerify
  , eval
  , initialState
  , postCondition
  ) where

import Prelude

import Data.Array (all)
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (over, un)
import Data.Set as Set
import Data.Traversable (for, traverse)
import Data.Tuple (Tuple(..))
import Data.UnionFind (equivalenceClasses)
import Data.Vector (Vector)
import Poseidon (class PoseidonField)
import Snarky.Backend.Builder (class CompileCircuit, CircuitBuilderState, Labeled)
import Snarky.Backend.Builder as CircuitBuilder
import Snarky.Backend.Prover (class SolveCircuit, ProverState)
import Snarky.Circuit.CVar (Variable, v0)
import Snarky.Circuit.DSL (class BasicSystem, Basic(..), EvaluationError, FVar)
import Snarky.Constraint.Basic as Basic
import Snarky.Constraint.Kimchi.AddComplete (AddComplete)
import Snarky.Constraint.Kimchi.AddComplete as AddComplete
import Snarky.Constraint.Kimchi.EndoMul (EndoMul)
import Snarky.Constraint.Kimchi.EndoMul as EndoMul
import Snarky.Constraint.Kimchi.EndoScalar (EndoScalar)
import Snarky.Constraint.Kimchi.EndoScalar as EndoScalar
import Snarky.Constraint.Kimchi.GenericPlonk as GenericPlonk
import Snarky.Constraint.Kimchi.Poseidon (PoseidonConstraint)
import Snarky.Constraint.Kimchi.Poseidon as Poseidon
import Snarky.Constraint.Kimchi.Reduction (class PlonkReductionM, Rows, finalizeGateQueue, mkRawGeneric7Row, reduceAsBuilder, reduceAsProver, reduceToVariable)
import Snarky.Constraint.Kimchi.Reduction as Reduction
import Snarky.Constraint.Kimchi.Types (class ToKimchiRows, AuxState(..), initialAuxState, toKimchiRows)
import Snarky.Constraint.Kimchi.VarBaseMul (VarBaseMul)
import Snarky.Constraint.Kimchi.VarBaseMul as VarBaseMul
import Snarky.Curves.Class (class HasEndo, class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.Snarky.Circuit.Utils (PostCondition)

data KimchiConstraint f
  = KimchiBasic (Basic f)
  | KimchiAddComplete (AddComplete f)
  | KimchiPoseidon (PoseidonConstraint f)
  | KimchiVarBaseMul (VarBaseMul f)
  | KimchiEndoScalar (EndoScalar f)
  | KimchiEndoMul (EndoMul (FVar f))
  | KimchiRawGeneric7 (Vector 7 (FVar f))

data KimchiGate f
  = KimchiGatePlonk (Reduction.Rows f)
  | KimchiGateAddComplete (AddComplete.Rows f)
  | KimchiGatePoseidon (Poseidon.Rows f)
  | KimchiGateVarBaseMul (VarBaseMul.Rows f)
  | KimchiGateEndoScalar (EndoScalar.Rows f)
  | KimchiGateEndoMul (EndoMul.Rows f)
  | KimchiGateNoOp

instance ToKimchiRows f (KimchiGate f) where
  toKimchiRows = case _ of
    KimchiGatePlonk a -> toKimchiRows a
    KimchiGateAddComplete a -> toKimchiRows a
    KimchiGatePoseidon a -> toKimchiRows a
    KimchiGateVarBaseMul a -> toKimchiRows a
    KimchiGateEndoScalar a -> toKimchiRows a
    KimchiGateEndoMul a -> toKimchiRows a
    KimchiGateNoOp -> []

reduceRawGeneric7
  :: forall n f
   . PlonkReductionM n f
  => Vector 7 (FVar f)
  -> n (Rows f)
reduceRawGeneric7 vs = do
  varsReduced <- traverse reduceToVariable vs
  pure (mkRawGeneric7Row varsReduced)

instance PoseidonField f => CompileCircuit f (KimchiGate f) (KimchiConstraint f) (AuxState f) where
  appendBuilderConstraint = case _ of
    KimchiAddComplete c -> go AddComplete.reduce KimchiGateAddComplete c
    KimchiPoseidon c -> go Poseidon.reduce KimchiGatePoseidon c
    KimchiBasic c -> go GenericPlonk.reduce (const KimchiGateNoOp) c
    KimchiVarBaseMul c -> go VarBaseMul.reduce KimchiGateVarBaseMul c
    KimchiEndoScalar c -> go EndoScalar.reduce KimchiGateEndoScalar c
    KimchiEndoMul c -> go EndoMul.reduce KimchiGateEndoMul c
    KimchiRawGeneric7 vs -> go reduceRawGeneric7 KimchiGatePlonk vs
    where
    go
      :: forall a c
       . (forall n. PlonkReductionM n f => c -> n a)
      -> (a -> KimchiGate f)
      -> c
      -> CircuitBuilderState (KimchiGate f) (AuxState f)
      -> CircuitBuilderState (KimchiGate f) (AuxState f)
    go reducer wrap c s =
      let
        Tuple rows res = reduceAsBuilder
          { nextVariable: s.nextVar
          , aux: s.aux
          }
          (reducer c)
        lbl = s.labelStack

        labelGate :: forall g. g -> Labeled g
        labelGate g = { constraint: g, context: lbl }
      in
        s
          { nextVar = res.nextVariable
          , constraints =
              CircuitBuilder.snocConstraint (labelGate (wrap rows))
                ( CircuitBuilder.appendConstraintsBatch
                    (map (labelGate <<< KimchiGatePlonk) res.constraints)
                    s.constraints
                )
          , aux = res.aux
          }

  finalize s =
    let
      mRow = finalizeGateQueue (un AuxState s.aux)
      lbl = s.labelStack
    in
      s
        { constraints = maybe s.constraints (\r -> CircuitBuilder.snocConstraint { constraint: KimchiGatePlonk r, context: lbl } s.constraints) mRow
        , aux = over AuxState
            ( \st ->
                st
                  { queuedGenericGate = Nothing
                  }
            )
            s.aux
        }

instance (KimchiVerify f f') => SolveCircuit f (KimchiConstraint f) where
  proverConstraint kc s = case kc of
    KimchiAddComplete c -> go AddComplete.reduce c
    KimchiPoseidon c -> go Poseidon.reduce c
    KimchiBasic c -> goBasic c
    KimchiVarBaseMul c -> go VarBaseMul.reduce c
    KimchiEndoScalar c -> go EndoScalar.reduce c
    KimchiEndoMul c -> go EndoMul.reduce c
    KimchiRawGeneric7 vs -> go reduceRawGeneric7 vs
    where
    -- Run the reducer and update prover state. Per-gate equation checks
    -- (formerly in `goDebug`'s `when s.debug …` branch) were removed in
    -- favor of the circuit-diffs JSON byte-equality check, which is a
    -- strictly stronger correctness signal.
    go
      :: forall c g
       . ToKimchiRows f g
      => (forall n. PlonkReductionM n f => c -> n g)
      -> c
      -> Either EvaluationError (ProverState f)
    go reducer c =
      reduceAsProver { assignments: s.assignments, nextVariable: s.nextVar } (reducer c) <#>
        \(Tuple _ res) -> s { assignments = res.assignments, nextVar = res.nextVariable }

    -- Basic constraints keep their `debugCheck` (pure-PS, no FFI) for
    -- richer error messages (e.g. "R1CS failed: 42 * 7 != 293") when
    -- the prover state has `debug: true`.
    goBasic :: Basic f -> Either EvaluationError (ProverState f)
    goBasic c = do
      Tuple _ res <- reduceAsProver { assignments: s.assignments, nextVariable: s.nextVar } (GenericPlonk.reduce c)
      let s' = s { assignments = res.assignments, nextVar = res.nextVariable }
      if s.debug then case Basic.debugCheck (flip Map.lookup res.assignments) c of
        Nothing -> Right s'
        Just e -> Left e
      else Right s'

initialState :: forall f. CircuitBuilderState (KimchiGate f) (AuxState f)
initialState =
  { nextVar: v0
  , constraints: CircuitBuilder.emptyConstraints
  , publicInputs: mempty
  , aux: initialAuxState
  , labelStack: []
  , varMetadata: Map.empty
  }

postCondition
  :: forall f
   . PrimeField f
  => PostCondition f (KimchiGate f) (AuxState f)
postCondition lookup { aux: AuxState { wireState: { unionFind } } } = do
  classes <- for (equivalenceClasses unionFind) \_class -> do
    values <- traverse lookup _class
    pure $ Set.fromFoldable values
  pure $ all (\s -> Set.size s == 1) classes

-- | Per-gate constraint sanity checker, threaded by `Test.Snarky.Circuit
-- | .Utils.TestConfig` as the `checker:` field (used by `random-oracle`,
-- | `merkle-tree`, `schnorr`, `example` tests).
-- |
-- | Historically this dispatched per-gate to a Rust-FFI'd equation check
-- | (`verifyPallasPoseidonGadget`, `verifyPallasCompleteAdd`, etc.) so
-- | every prover-emitted gate was cross-checked against kimchi's reference
-- | implementation. The Rust path was deleted alongside `snarky-crypto`;
-- | retaining a pure-PS port wasn't worth the LOC. Tests still get
-- | wire-equivalence via `postCondition` and result-value assertions
-- | from their own circuit-correctness invariants.
eval
  :: forall f m
   . Applicative m
  => (Variable -> m f)
  -> KimchiGate f
  -> m Boolean
eval _ _ = pure true

-- | Marker class for curves usable with the kimchi backend. Brings in
-- | the cycle's `HasEndo` instances and the Poseidon round constants
-- | (`PoseidonField`, needed by `Poseidon.reduce`). Historically also
-- | required `GenericPlonkVerifiable`/`AddCompleteVerifiable`/…/
-- | `VarBaseMulVerifiable` for a Rust-FFI cross-check of each gate's
-- | equation during proving; that path was deleted in favor of
-- | circuit-diffs JSON byte-equality.
class
  ( HasEndo f f'
  , HasEndo f' f
  , PoseidonField f
  ) <=
  KimchiVerify f f'
  | f -> f'

instance KimchiVerify Pallas.ScalarField Vesta.ScalarField
instance KimchiVerify Vesta.ScalarField Pallas.ScalarField

instance PrimeField f => BasicSystem f (KimchiConstraint f) where
  r1cs = KimchiBasic <<< R1CS
  equal a b = KimchiBasic $ Equal a b
  square a c = KimchiBasic $ Square a c
  boolean = KimchiBasic <<< Boolean
