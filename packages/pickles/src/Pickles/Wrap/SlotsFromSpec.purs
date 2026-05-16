-- | Derive a wrap-side `Pickles.Wrap.Slots` shape from a step-side
-- | slot spec (`Slot k n stmt /\ rest`). The wrap circuit's per-prev
-- | bp_chals carrier is sized by each slot's `n` independently.
module Pickles.Wrap.SlotsFromSpec
  ( class SlotsFromSpec
  , slotsProxy
  ) where

import Data.Const (Const)
import Data.Functor.Product (Product)
import Data.Tuple.Nested (type (/\))
import Data.Vector (Vector)
import Pickles.Slots (Compiled, SideLoaded, Slot)
import Prelude (Unit)
import Type.Proxy (Proxy(..))

-- | Derive a wrap-side `Slots*` shape from a step-side slot spec.
class SlotsFromSpec :: Type -> (Type -> Type) -> Constraint
class SlotsFromSpec spec slots | spec -> slots where
  -- | Forces PS to dispatch the class instance, grounding `slots`
  -- | from `spec` via the funcdep. Without a method, PS may leave
  -- | `slots` polymorphic and fail downstream constraints (e.g.,
  -- | `PadSlots slots mpv`) with a `NoInstanceFound`.
  slotsProxy :: Proxy spec -> Proxy slots

instance SlotsFromSpec Unit (Const Unit) where
  slotsProxy _ = Proxy

instance
  SlotsFromSpec rest restSlots =>
  SlotsFromSpec (Slot Compiled n slotVkChunks stmt /\ rest) (Product (Vector n) restSlots)
  where
  slotsProxy _ = Proxy

instance
  SlotsFromSpec rest restSlots =>
  SlotsFromSpec (Slot SideLoaded n slotVkChunks stmt /\ rest) (Product (Vector n) restSlots)
  where
  slotsProxy _ = Proxy
