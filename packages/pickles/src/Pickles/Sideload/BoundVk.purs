-- | A side-loaded verification key a rule has tied to its own
-- | statement, which is what makes a side-loaded slot certify which
-- | child it verified rather than any child the prover chose.
module Pickles.Sideload.BoundVk
  ( module Reexport
  ) where

import Pickles.Sideload.BoundVk.Internal (BoundVk) as Reexport
