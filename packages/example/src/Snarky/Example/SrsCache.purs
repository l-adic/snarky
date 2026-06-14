-- | Browser SRS setup with a persistent lagrange-basis cache.
-- |
-- | The dominant browser setup cost is warming the SRS lagrange bases
-- | (~33s); `srs_create` itself is ~1s and deterministic. So we rebuild the
-- | g-vector fresh each load (cheap) and cache only the lagrange bases
-- | (~12 MB) in IndexedDB: first load warms + caches them, a reload restores
-- | them via `set_lagrange_basis` without recomputing. Mirrors
-- | `Snarky.Example.Env.mkConfig`'s depths/domains exactly, so the result is a
-- | drop-in `Config`. Falls back to plain warming where IndexedDB is absent.
module Snarky.Example.SrsCache
  ( buildCachedConfig
  ) where

import Prelude

import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Mina.ChainId (ChainId)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Curves.Pasta (PallasG, VestaG)

foreign import buildCachedSrsImpl :: EffectFnAff { pallasSrs :: CRS PallasG, vestaSrs :: CRS VestaG }

buildCachedConfig
  :: ChainId
  -> Aff { pallasSrs :: CRS PallasG, vestaSrs :: CRS VestaG, chainId :: ChainId }
buildCachedConfig chainId = do
  srs <- fromEffectFnAff buildCachedSrsImpl
  pure { pallasSrs: srs.pallasSrs, vestaSrs: srs.vestaSrs, chainId }
