-- | Persistent proof cache, keyed by content-address (`stmtKey`). On join a
-- | peer loads its cached proofs and announces them, so a reload/rejoin resumes
-- | instead of redoing work; each proved/received proof is written through.
-- | Degrades to a no-op where IndexedDB is unavailable.
module Snarky.Example.P2P.Cache
  ( cachePut
  , cacheAll
  ) where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

foreign import cachePut :: String -> String -> Effect Unit
foreign import _cacheAll :: EffectFnAff (Array { key :: String, wire :: String })

cacheAll :: Aff (Array { key :: String, wire :: String })
cacheAll = fromEffectFnAff _cacheAll
