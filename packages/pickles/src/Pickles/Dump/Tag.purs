-- | The theorems' dump of one tag: its wrap circuit and, per branch, its
-- | step circuit and rule, each circuit with the constants it was compiled
-- | with, the wrap circuit's key, and the values its prover pads a slot a
-- | rule lacks with. `compileMulti` writes it when its config names a
-- | path; the Lean side rebuilds every circuit from it and compares.
module Pickles.Dump.Tag
  ( CircuitDump
  , BranchDump
  , TagDump
  , WrapPadding
  , wrapPadding
  , writeTagDump
  ) where

import Prelude

import Data.Enum (fromEnum)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), lastIndexOf, take)
import Effect (Effect)
import JS.BigInt as BigInt
import Node.Encoding (Encoding(..))
import Node.FS.Perms (permsAll)
import Node.FS.Sync (mkdir', writeTextFile)
import Pickles.CircuitDiffs.Types (ComparableCircuit, Constants, Point)
import Pickles.Dump.Constants (KeyExport)
import Pickles.Field (WrapField)
import Pickles.ProofsVerified (ProofsVerified)
import Pickles.Prove.RuleDump (RuleDump, encodeRuleDump)
import Pickles.Types (AllocEvals)
import Simple.JSON (writeJSON)
import Snarky.Circuit.DSL (F(..), valueToFields)
import Snarky.Curves.Class (toBigInt)
import Snarky.Curves.Pasta (VestaG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint(..))

-- | A circuit as dumped: its constraint system and the constants it
-- | bakes in, with the fields in `r`.
type CircuitDump r =
  { circuit :: ComparableCircuit
  , constants :: Constants
  | r
  }

-- | A branch: its step circuit and its rule.
type BranchDump =
  { stepMain :: CircuitDump ()
  , rule :: RuleDump
  }

-- | What the wrap prover allocates for a slot its rule lacks: the step
-- | proof's accumulator, the evaluations' cells and the wrap domain's
-- | index.
type WrapPadding = { stepAcc :: Point, evals :: Array String, domain :: Int }

-- | The padding values as the dump records them.
wrapPadding
  :: { stepAcc :: WeierstrassAffinePoint VestaG (F WrapField)
     , evals :: AllocEvals (F WrapField)
     , domain :: ProofsVerified
     }
  -> WrapPadding
wrapPadding p =
  { stepAcc: case p.stepAcc of
      WeierstrassAffinePoint { x: F x, y: F y } -> [ field x, field y ]
  , evals: map field (valueToFields @WrapField p.evals)
  , domain: fromEnum p.domain
  }
  where
  field :: WrapField -> String
  field = BigInt.toString <<< toBigInt

-- | A tag: its wrap circuit with its key and padding, and its branches, in
-- | rule order.
type TagDump =
  { wrapMain :: CircuitDump (key :: KeyExport, padding :: WrapPadding)
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
