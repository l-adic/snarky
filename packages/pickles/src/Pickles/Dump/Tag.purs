-- | The theorems' dump of one tag: its wrap circuit and, per branch, its
-- | step circuit and rule, each circuit with the constants it was compiled
-- | with and its key. `compileMulti` writes it when its config names a
-- | path; the Lean side rebuilds every circuit from it and compares.
module Pickles.Dump.Tag
  ( CircuitDump
  , BranchDump
  , TagDump
  , writeTagDump
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), lastIndexOf, take)
import Effect (Effect)
import Node.Encoding (Encoding(..))
import Node.FS.Perms (permsAll)
import Node.FS.Sync (mkdir', writeTextFile)
import Pickles.CircuitDiffs.Types (ComparableCircuit, Constants)
import Pickles.Dump.Constants (KeyExport)
import Pickles.Prove.RuleDump (RuleDump, encodeRuleDump)
import Simple.JSON (writeJSON)

-- | A circuit as dumped: its constraint system, the constants it bakes in,
-- | and its key.
type CircuitDump =
  { circuit :: ComparableCircuit
  , constants :: Constants
  , key :: KeyExport
  }

-- | A branch: its step circuit and its rule.
type BranchDump =
  { stepMain :: CircuitDump
  , rule :: RuleDump
  }

-- | A tag: its wrap circuit and its branches, in rule order.
type TagDump =
  { wrapMain :: CircuitDump
  , branches :: Array BranchDump
  }

-- | Write a tag's dump to `path`, creating its directory if needed.
writeTagDump :: String -> TagDump -> Effect Unit
writeTagDump path d = do
  case lastIndexOf (Pattern "/") path of
    Just i -> mkdir' (take i path) { recursive: true, mode: permsAll }
    Nothing -> pure unit
  writeTextFile UTF8 path $ writeJSON
    { wrapMain: d.wrapMain
    , branches: d.branches <#> \b -> { stepMain: b.stepMain, rule: encodeRuleDump b.rule }
    }
