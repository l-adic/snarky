-- | Per-slot containers for `stepMain`, one entry per previous proof a
-- | rule declares.
-- |
-- | A rule's prevs are a type-level chain of `Pickles.Slots.Slot`
-- | descriptors ending in `Unit`, and the slots need not agree on a
-- | statement type:
-- |
-- |   Slot 1 (StatementIO Stmt Unit) /\ Slot 2 Stmt' /\ Unit
-- |
-- | Two carriers come from that one spec: `pwCarrier`, the per-slot
-- | `PerProofWitness` values, and `vkCarrier`, the per-slot wrap-VK
-- | sources. `traverseStepSlotsAWithVk` walks them in lockstep under
-- | one shared chunk count per slot.
-- |
-- | A rule body sees the spec through two more types indexed by it:
-- | `PrevValues`, the previous statements it reads as advice, and
-- | `Prevs`, the previous statements it returns.
module Pickles.Step.Slots
  ( class StepSlotsCarrier
  , class SlotStatementsCarrier
  , class SlotKindPrev
  , class SlotKindValue
  , class SlotPrevStatements
  , class SlotVkCarrier
  , class StepSlotsTyp
  , EncodedPrev
  , PrevStatement(..)
  , PrevValues
  , Prevs
  , SideLoadedPrevStatement(..)
  , SideLoadedPrevValue
  , encodeSlotPrev
  , mkSlotValue
  , SlotWitnessVal
  , SlotWitnessVar
  , mkPrevValues
  , prevValues
  , prevsVector
  , stepSlotsTyp
  , toPrevs
  , traverseStepSlotsA
  , traverseStepSlotsAWithVk
  , replicateStepSlotsCarrier
  ) where

import Prelude

import Data.Array as Array
import Data.Fin (Finite, finZero, shiftSucc)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Exception.Unsafe (unsafeThrow)
import Pickles.Field (StepField)
import Pickles.Sideload.BoundVk.Internal (BoundVk(..))
import Pickles.Sideload.Bundle (SlotProveVk, projectVk)
import Pickles.Sideload.VerificationKey (VerificationKey) as SLVK
import Pickles.Slots (Compiled, SideLoaded, SlotKind, SlotOf)
import Pickles.Step.Types (PerProofWitness, WrapProof, perProofWitnessTyp)
import Pickles.Step.VkSource (SlotVkSource)
import Pickles.Typ (Typ, pairTyp, unitTyp)
import Pickles.Types (PaddedLength, StepIPARounds, WrapIPARounds, WrapVkChunks)
import Prim.Int (class Add)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, BoolVar, F, FVar)
import Snarky.Circuit.Types (varToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint)
import Snarky.Types.Shifted (SplitField, Type2)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

-- | `spec` → `vkCarrier`, split out of `StepSlotsCarrier` so the two
-- | `StepSlotsCarrier` constraints a caller needs — one at value
-- | elements, one at variables — agree on the carrier. `SlotVkSource`
-- | carries no field-element parameter, so the shape is the same for
-- | both; without the tighter fundep PS infers two distinct carrier
-- | variables.
class SlotVkCarrier :: Type -> Type -> Constraint
class SlotVkCarrier spec vkCarrier | spec -> vkCarrier

instance SlotVkCarrier Unit Unit

instance
  SlotVkCarrier rest restVk =>
  SlotVkCarrier (SlotOf k n statement /\ rest) (SlotVkSource WrapVkChunks /\ restVk)

-- | `spec` → (`len`, `pwCarrier`, `vkCarrier`), with two traversals:
-- | one over `pwCarrier` alone, one zipping it with `vkCarrier`.
-- | Compiled and side-loaded slots present the same carrier shapes, so
-- | the spec does not distinguish them.
-- |
-- | `nc`, the wrap-VK chunk count, is a class parameter rather than a
-- | per-slot rank-2 binder: that is what lets the callback body use the
-- | caller's own layout constraints at `nc`, so `verifyOne` can be
-- | called directly, with no restated constraints and no `unsafeCoerce`.
-- | Being a wrap-side count, it is `Pickles.Types.WrapVkChunks` for
-- | every slot of every compile.
class StepSlotsCarrier
  :: Type -> Int -> Int -> Int -> Type -> Type -> Type -> Int -> Type -> Type -> Constraint
class
  SlotVkCarrier spec vkCarrier <=
  StepSlotsCarrier spec nc ds dw f sf b len pwCarrier vkCarrier
  | spec ds dw f sf b -> len pwCarrier
  , spec -> vkCarrier
  where
  -- | Walk `pwCarrier` in slot order, ignoring the VK carrier.
  traverseStepSlotsA
    :: forall m result
     . Applicative m
    => ( forall n pad
          . Reflectable n Int
         => Reflectable pad Int
         => Add pad n PaddedLength
         => Proxy n
         -> Finite len
         -> PerProofWitness nc ds dw f sf b
         -> m result
       )
    -> pwCarrier
    -> m (Vector len result)

  -- | Walk `pwCarrier` and `vkCarrier` in lockstep. The callback gets a
  -- | slot's `PerProofWitness` and its `SlotVkSource` at the same `nc`,
  -- | so no equality bridge is needed.
  traverseStepSlotsAWithVk
    :: forall m result
     . Applicative m
    => ( forall n pad
          . Reflectable n Int
         => Reflectable pad Int
         => Add pad n PaddedLength
         => Proxy n
         -> Finite len
         -> PerProofWitness nc ds dw f sf b
         -> SlotVkSource nc
         -> m result
       )
    -> pwCarrier
    -> vkCarrier
    -> m (Vector len result)

  -- | Build a `pwCarrier` by specializing one rank-2 dummy slot at each
  -- | slot's own `n`.
  replicateStepSlotsCarrier
    :: ( forall n pad
          . Reflectable n Int
         => Reflectable pad Int
         => Add pad n PaddedLength
         => Proxy n
         -> PerProofWitness nc ds dw f sf b
       )
    -> pwCarrier

instance StepSlotsCarrier Unit nc ds dw f sf b 0 Unit Unit where
  traverseStepSlotsA _ _ = pure Vector.nil
  traverseStepSlotsAWithVk _ _ _ = pure Vector.nil
  replicateStepSlotsCarrier _ = unit

instance
  ( StepSlotsCarrier rest WrapVkChunks ds dw f sf b restLen restPw restVk
  , Add restLen 1 len
  , Reflectable n Int
  , Add pad n PaddedLength
  , Reflectable pad Int
  ) =>
  StepSlotsCarrier
    (SlotOf k n statement /\ rest)
    WrapVkChunks
    ds
    dw
    f
    sf
    b
    len
    (PerProofWitness WrapVkChunks ds dw f sf b /\ restPw)
    (SlotVkSource WrapVkChunks /\ restVk)
  where
  traverseStepSlotsA f (here /\ rest) =
    Vector.cons
      <$> f (Proxy :: Proxy n) (finZero :: Finite len) here
      <*> traverseStepSlotsA @rest (\pn i' pw -> f pn (shiftSucc i') pw) rest

  traverseStepSlotsAWithVk f (pwHere /\ pwRest) (vkHere /\ vkRest) =
    Vector.cons
      <$> f (Proxy :: Proxy n) (finZero :: Finite len) pwHere vkHere
      <*> traverseStepSlotsAWithVk @rest
        (\pn i' pw vk -> f pn (shiftSucc i') pw vk)
        pwRest
        vkRest

  replicateStepSlotsCarrier dummyPPW =
    dummyPPW (Proxy :: Proxy n) /\ replicateStepSlotsCarrier @rest dummyPPW

-- | A slot's per-proof witness at the one pair of instantiations every
-- | caller of `StepSlotsCarrier` uses: values over `F StepField`,
-- | variables over `FVar StepField`.
type SlotWitnessVal slotVkChunks =
  PerProofWitness slotVkChunks StepIPARounds WrapIPARounds
    (F StepField)
    (Type2 (SplitField (F StepField) Boolean))
    Boolean

type SlotWitnessVar slotVkChunks =
  PerProofWitness slotVkChunks StepIPARounds WrapIPARounds
    (FVar StepField)
    (Type2 (SplitField (FVar StepField) (BoolVar StepField)))
    (BoolVar StepField)

-- | The per-proof carrier's layout, as a `Typ`.
-- |
-- | `StepSlotsCarrier` is indexed by one field-element type at a time,
-- | so it names the value carrier and the variable carrier through two
-- | separate dictionaries. A `Typ` relates the two and needs both at
-- | once — hence a second class over the same spec, pinned to the pair
-- | of instantiations every caller uses.
-- |
-- | It is also where the slot width crosses from the type level to the
-- | value level: the spec declares it, and it is reflected here and
-- | handed to `perProofWitnessTyp` as an ordinary integer.
class StepSlotsTyp :: Type -> Type -> Type -> Constraint
class StepSlotsTyp spec valCarrier varCarrier | spec -> valCarrier varCarrier where
  stepSlotsTyp :: Typ StepField (KimchiConstraint StepField) valCarrier varCarrier

instance StepSlotsTyp Unit Unit Unit where
  stepSlotsTyp = unitTyp

instance
  ( StepSlotsTyp rest restVal restVar
  , Reflectable n Int
  , CircuitType StepField
      (WrapProof WrapIPARounds WrapVkChunks (WeierstrassAffinePoint PallasG (F StepField)) (Type2 (SplitField (F StepField) Boolean)))
      (WrapProof WrapIPARounds WrapVkChunks (WeierstrassAffinePoint PallasG (FVar StepField)) (Type2 (SplitField (FVar StepField) (BoolVar StepField))))
  , CheckedType StepField (KimchiConstraint StepField)
      (WrapProof WrapIPARounds WrapVkChunks (WeierstrassAffinePoint PallasG (FVar StepField)) (Type2 (SplitField (FVar StepField) (BoolVar StepField))))
  ) =>
  StepSlotsTyp
    (SlotOf k n statement /\ rest)
    (SlotWitnessVal WrapVkChunks /\ restVal)
    (SlotWitnessVar WrapVkChunks /\ restVar)
  where
  stepSlotsTyp =
    pairTyp (perProofWitnessTyp (reflectType (Proxy :: Proxy n))) (stepSlotsTyp @rest)

-- | What one slot of kind `k` contributes to the advice a rule reads:
-- | a compiled slot its statement alone, a side-loaded slot its
-- | statement and the runtime key the rule has to bind.
class SlotKindValue :: SlotKind -> Type -> Type -> Constraint
class SlotKindValue k statement valElem | k statement -> valElem where
  -- | Build the element from the slot's statement and whatever the
  -- | prove call supplied for its key.
  mkSlotValue :: statement -> SlotProveVk WrapVkChunks -> valElem

instance SlotKindValue Compiled statement statement where
  mkSlotValue statement _ = statement

-- | A side-loaded slot's advice: the prev's statement, and the
-- | verification key the prove call supplied for it.
type SideLoadedPrevValue statement =
  { statement :: statement
  , verificationKey :: SLVK.VerificationKey WrapVkChunks (F StepField) Boolean
  }

instance SlotKindValue SideLoaded statement (SideLoadedPrevValue statement) where
  -- `projectVk` throws when the slot's key is missing. The read is
  -- deferred: the rule projects this inside an `exists` body, which
  -- compile discards.
  mkSlotValue statement slotVk = { statement, verificationKey: projectVk slotVk }

-- | `spec` → the per-slot statements carrier: one entry per prev, at
-- | that slot's kind and statement type.
class SlotStatementsCarrier :: Type -> Type -> Constraint
class SlotStatementsCarrier spec valCarrier | spec -> valCarrier

instance SlotStatementsCarrier Unit Unit

instance
  ( SlotKindValue k statement valElem
  , SlotStatementsCarrier rest restValCarrier
  ) =>
  SlotStatementsCarrier
    (SlotOf k n statement /\ rest)
    (valElem /\ restValCarrier)

-- | The prover-side values of a rule's previous statements, indexed by
-- | its prevs spec. `prevValues` opens it as the `SlotStatementsCarrier`
-- | tuple.
-- |
-- | The index is what lets a rule's type name only its spec: the tuple
-- | is computed at the `prevValues` call, where the spec is concrete.
foreign import data PrevValues :: Type -> Type

-- | The tuple of previous statements, one entry per slot.
prevValues
  :: forall spec values
   . SlotStatementsCarrier spec values
  => PrevValues spec
  -> values
-- The fundep `spec -> values` gives each spec exactly one carrier, so
-- this and `mkPrevValues` only ever coerce a value back to its own type.
prevValues = unsafeCoerce

-- | Index a tuple of previous statements by the spec it was built for.
mkPrevValues
  :: forall @spec values
   . SlotStatementsCarrier spec values
  => values
  -> PrevValues spec
mkPrevValues = unsafeCoerce

-- | One previous proof as a rule returns it: its statement, and whether
-- | the proof must verify.
newtype PrevStatement stmtVar = PrevStatement
  { publicInput :: stmtVar
  , proofMustVerify :: BoolVar StepField
  }

-- | One previous proof of a side-loaded slot. The key is a `BoundVk`,
-- | so the rule cannot return a slot whose key it has not tied to its
-- | own statement.
newtype SideLoadedPrevStatement stmtVar = SideLoadedPrevStatement
  { publicInput :: stmtVar
  , proofMustVerify :: BoolVar StepField
  , verificationKey :: BoundVk
  }

-- | One slot's encoded entry: its statement's fields, its flag, and,
-- | for a side-loaded slot, the key the step circuit verifies against.
type EncodedPrev =
  { fields :: Array (FVar StepField)
  , proofMustVerify :: BoolVar StepField
  , verificationKey ::
      Maybe (SLVK.VerificationKey WrapVkChunks (FVar StepField) (BoolVar StepField))
  }

-- | A rule's previous statements, each already encoded to fields by its
-- | own slot's `CircuitType`, indexed by the rule's prevs spec. Built
-- | only by `toPrevs`.
newtype Prevs :: Type -> Type
newtype Prevs spec = Prevs (Array EncodedPrev)

-- | What one slot of kind `k` contributes to what a rule returns.
class SlotKindPrev :: SlotKind -> Type -> Type -> Constraint
class SlotKindPrev k stmtVar prevElem | k stmtVar -> prevElem where
  encodeSlotPrev :: (stmtVar -> Array (FVar StepField)) -> prevElem -> EncodedPrev

instance SlotKindPrev Compiled stmtVar (PrevStatement stmtVar) where
  encodeSlotPrev encode (PrevStatement here) =
    { fields: encode here.publicInput
    , proofMustVerify: here.proofMustVerify
    , verificationKey: Nothing
    }

instance SlotKindPrev SideLoaded stmtVar (SideLoadedPrevStatement stmtVar) where
  encodeSlotPrev encode (SideLoadedPrevStatement here) =
    let
      BoundVk vk = here.verificationKey
    in
      { fields: encode here.publicInput
      , proofMustVerify: here.proofMustVerify
      , verificationKey: Just vk
      }

-- | `spec` → the tuple a rule returns: one entry per slot, at that
-- | slot's kind and the variable type of its statement.
class SlotPrevStatements :: Type -> Type -> Constraint
class SlotPrevStatements spec prevs | spec -> prevs where
  toPrevs :: prevs -> Prevs spec

instance SlotPrevStatements Unit Unit where
  toPrevs _ = Prevs []

instance
  ( CircuitType StepField statement statementVar
  , SlotKindPrev k statementVar prevElem
  , SlotPrevStatements rest restPrevs
  ) =>
  SlotPrevStatements
    (SlotOf k n statement /\ rest)
    (prevElem /\ restPrevs)
  where
  toPrevs (here /\ rest) =
    let
      Prevs restEntries = toPrevs @rest rest
    in
      Prevs $ Array.cons
        (encodeSlotPrev @k (varToFields @StepField @statement) here)
        restEntries

-- | The encoded previous statements at the rule's slot count.
prevsVector
  :: forall @len spec
   . Reflectable len Int
  => Prevs spec
  -> Vector len EncodedPrev
prevsVector (Prevs entries) = case Vector.toVector entries of
  Just v -> v
  -- `toPrevs` emits one entry per slot of `spec`, and `len` is that
  -- slot count, so a mismatch is a bug in the caller's constraints.
  Nothing -> unsafeThrow $
    "prevsVector: " <> show (Array.length entries)
      <> " previous statements, expected "
      <> show (reflectType (Proxy :: Proxy len))
