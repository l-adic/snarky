module Pickles.Wrap.SlotsForPrevs
  ( class SlotsForPrevsSpec
  , slotsProxy
  ) where

import Prelude (Unit)

import Data.Const (Const)
import Data.Functor.Product (Product)
import Data.Vector (Vector)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil, PrevsSpecSideLoadedCons)
import Type.Proxy (Proxy(..))

-- | Derive a wrap-side `Slots*` shape from a step-side `PrevsSpec*`.
class SlotsForPrevsSpec :: Type -> (Type -> Type) -> Constraint
class SlotsForPrevsSpec prevsSpec slots | prevsSpec -> slots where
  -- | Forces PS to dispatch the class instance, grounding `slots` from
  -- | `prevsSpec` via the funcdep. Without a method, PS may leave
  -- | `slots` polymorphic and fail downstream constraints (e.g.,
  -- | `PadSlots slots mpv`) with a `NoInstanceFound`.
  slotsProxy :: Proxy prevsSpec -> Proxy slots

instance SlotsForPrevsSpec PrevsSpecNil (Const Unit) where
  slotsProxy _ = Proxy

instance
  SlotsForPrevsSpec rest restSlots =>
  SlotsForPrevsSpec (PrevsSpecCons n stmt rest) (Product (Vector n) restSlots)
  where
  slotsProxy _ = Proxy

instance
  SlotsForPrevsSpec rest restSlots =>
  SlotsForPrevsSpec (PrevsSpecSideLoadedCons n stmt rest) (Product (Vector n) restSlots)
  where
  slotsProxy _ = Proxy
