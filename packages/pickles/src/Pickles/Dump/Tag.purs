-- | The theorems' fixture of one tag: its wrap circuit and, per branch, its
-- | step circuit and rule, each circuit with the constants it was compiled
-- | with, the wrap circuit's key, and the values its prover pads a slot a
-- | rule lacks with. `compileMulti` writes it when its config names a
-- | path; the Lean side rebuilds every circuit from it and compares.
module Pickles.Dump.Tag
  ( CircuitDump
  , BranchDump
  , TagFixture
  , WrapPadding
  , wrapPadding
  , writeTagDump
  ) where

import Prelude

import Data.Enum (fromEnum)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), lastIndexOf, take)
import Data.String.CodeUnits as CodeUnits
import Effect (Effect)
import JS.BigInt as BigInt
import Node.Encoding (Encoding(..))
import Node.FS.Perms (permsAll)
import Node.FS.Sync (mkdir', writeTextFile)
import Pickles.CircuitDiffs.Types (ComparableCircuit, Constants, Point)
import Pickles.Dump.Constants (KeyExport)
import Pickles.Dump.Shape (ShapeDump)
import Pickles.Field (WrapField)
import Pickles.ProofsVerified (ProofsVerified)
import Pickles.Prove.RuleDump (RuleDumpJson)
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
  , rule :: RuleDumpJson
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

-- | A tag's circuit comparison data, separate from its small shape file.
type TagFixture =
  { wrapMain :: CircuitDump (key :: KeyExport, padding :: WrapPadding)
  , branches :: Array BranchDump
  }

-- | Write the circuit fixture at `path` and its shape at the adjacent
-- | `shapes/<tag>.json`. Existing circuit readers only scan the parent
-- | directory for JSON files, so they do not mistake shapes for tags.
writeTagDump :: String -> ShapeDump -> TagFixture -> Effect Unit
writeTagDump path shape d = do
  let
    { dir, fileName } = case lastIndexOf (Pattern "/") path of
      Just i -> { dir: take i path, fileName: CodeUnits.drop (i + 1) path }
      Nothing -> { dir: ".", fileName: path }
    shapesDir = dir <> "/shapes"
  mkdir' dir { recursive: true, mode: permsAll }
  mkdir' shapesDir { recursive: true, mode: permsAll }
  writeTextFile UTF8 path (writeJSON d)
  writeTextFile UTF8 (shapesDir <> "/" <> fileName) (writeJSON shape)
