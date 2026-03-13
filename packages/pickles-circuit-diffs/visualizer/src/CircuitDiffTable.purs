module CircuitDiffTable where

import Pickles.CircuitDiffs.Types (CircuitComparison)
import React.Basic (ReactComponent)

foreign import _mkCircuitDiffTable :: ReactComponent { comparison :: CircuitComparison }
