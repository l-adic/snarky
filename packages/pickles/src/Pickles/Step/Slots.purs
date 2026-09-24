-- | Per-slot data for `stepMain`, one entry per previous proof a rule
-- | declares.
-- |
-- | A rule's prevs are a type-level chain of `Pickles.Slots.Slot`
-- | descriptors ending in `Unit`, and the slots need not agree on a
-- | statement type:
-- |
-- |   Slot 1 (StatementIO Stmt Unit) /\ Slot 2 Stmt' /\ Unit
-- |
-- | What does not depend on a slot's statement type is a `Vector` over
-- | the slots: each slot's width, read from the spec by `SlotWidths`,
-- | and its per-proof witness, allocated by `stepSlotsTyp`.
-- |
-- | A rule body sees the spec through two more types indexed by it:
-- | `PrevValues`, the previous statements it reads as advice, and
-- | `Prevs`, the previous statements it returns.
module Pickles.Step.Slots
  ( class SlotStatementsCarrier
  , class SlotKindPrev
  , class SlotKindValue
  , class SlotPrevStatements
  , class SlotWidths
  , EncodedPrev
  , PrevStatement(..)
  , PrevValues
  , Prevs
  , SideLoadedPrevStatement(..)
  , SideLoadedPrevValue
  , SlotWidth
  , encodeSlotPrev
  , SlotWitnessVal
  , SlotWitnessVar
  , mkPrevValues
  , prevValues
  , prevsVector
  , slotWidthInt
  , slotWidthsOf
  , stepSlotsTyp
  , toPrevs
  , withSlotWidth
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Exception.Unsafe (unsafeThrow)
import Pickles.Field (StepField)
import Pickles.Sideload.BoundVk.Internal (BoundVk(..))
import Pickles.Sideload.VerificationKey (VerificationKey) as SLVK
import Pickles.Slots (Compiled, SideLoaded, SlotKind, SlotOf)
import Pickles.Step.Types (PerProofWitness, perProofWitnessTyp)
import Pickles.Typ (Typ, vectorTyp)
import Pickles.Types (PaddedLength, StepIPARounds, WrapIPARounds, WrapVkChunks)
import Prim.Int (class Add, class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (class CircuitType, BoolVar, F, FVar)
import Snarky.Circuit.Types (varToFields)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Types.Shifted (SplitField, Type2)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

-- | One slot's width `n`, the prev's `max_proofs_verified`, packed
-- | with the `pad` that fills it out to `PaddedLength`, so that slots
-- | of different widths share one `Vector`.
newtype SlotWidth = SlotWidth
  ( forall r
     . ( forall n pad
          . Reflectable n Int
         => Reflectable pad Int
         => Add pad n PaddedLength
         => Compare n 3 LT
         => Proxy n
         -> r
       )
    -> r
  )

-- | Run `k` at the slot's width, as types.
withSlotWidth
  :: forall r
   . SlotWidth
  -> ( forall n pad
        . Reflectable n Int
       => Reflectable pad Int
       => Add pad n PaddedLength
       => Compare n 3 LT
       => Proxy n
       -> r
     )
  -> r
withSlotWidth (SlotWidth run) k = run k

-- | The slot's width as an ordinary integer.
slotWidthInt :: SlotWidth -> Int
slotWidthInt w = withSlotWidth w \p -> reflectType p

-- | `spec` → its slot count `len`, and each slot's width, read from the
-- | `n` of its `SlotOf k n statement`.
class SlotWidths :: Type -> Int -> Constraint
class SlotWidths spec len | spec -> len where
  slotWidthsOf :: forall proxy. proxy spec -> Vector len SlotWidth

instance SlotWidths Unit 0 where
  slotWidthsOf _ = Vector.nil

instance
  ( SlotWidths rest restLen
  , Add restLen 1 len
  , Reflectable n Int
  , Reflectable pad Int
  , Add pad n PaddedLength
  , Compare n 3 LT
  ) =>
  SlotWidths (SlotOf k n statement /\ rest) len where
  slotWidthsOf _ =
    Vector.cons (SlotWidth \k -> k (Proxy :: Proxy n))
      (slotWidthsOf (Proxy :: Proxy rest))

-- | A slot's per-proof witness at the one pair of instantiations every
-- | caller uses: values over `F StepField`, variables over
-- | `FVar StepField`.
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

-- | The layout of a rule's per-proof witnesses, one per slot, each at
-- | its slot's width and its previous step proof's chunk count.
stepSlotsTyp
  :: forall len
   . Vector len SlotWidth
  -> Vector len Int
  -> Typ StepField (KimchiConstraint StepField)
       (Vector len (SlotWitnessVal WrapVkChunks))
       (Vector len (SlotWitnessVar WrapVkChunks))
stepSlotsTyp widths numChunks =
  vectorTyp
    ( Vector.zipWith
        (\w nc -> perProofWitnessTyp { width: slotWidthInt w, numChunks: nc })
        widths
        numChunks
    )

-- | What one slot of kind `k` contributes to the advice a rule reads:
-- | a compiled slot its statement alone, a side-loaded slot its
-- | statement and the runtime key the rule has to bind.
class SlotKindValue :: SlotKind -> Type -> Type -> Constraint
class SlotKindValue k statement valElem | k statement -> valElem

instance SlotKindValue Compiled statement statement

-- | A side-loaded slot's advice: the prev's statement, and the
-- | verification key the prove call supplied for it.
type SideLoadedPrevValue statement =
  { statement :: statement
  , verificationKey :: SLVK.VerificationKey WrapVkChunks (F StepField) Boolean
  }

instance SlotKindValue SideLoaded statement (SideLoadedPrevValue statement)

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
