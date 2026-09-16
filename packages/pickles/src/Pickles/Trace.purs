-- | Trace logger for byte-identical pickles transcript reproduction tests.
-- |
-- | Writes one line per traced value, `[LABEL] DECIMAL_VALUE`, to the
-- | file named by the `PICKLES_TRACE_FILE` env var. With that var unset
-- | every function here is a no-op costing one env lookup, so circuit
-- | code can carry trace points permanently.
-- |
-- | Labels are semantic, dot-separated and lowercase:
-- | `[step.unfinalized.0.beta]`,
-- | `[wrap.statement.deferred_values.combined_inner_product]`.
module Pickles.Trace
  ( field
  , fieldF
  ) where

import Prelude

import Effect (Effect)
import JS.BigInt as BigInt
import Snarky.Circuit.DSL (F(..))
import Snarky.Curves.Class (class PrimeField, toBigInt)

-- A trace is only useful diffed against the reference implementation's,
-- so the label strings and their emission order have to agree with
-- `pickles_trace.ml` exactly. Renaming a label here breaks the diff
-- silently: both files still parse.

-- | Emit one trace line. The file handle is opened lazily on the first
-- | call, truncating, and stays open for the life of the process.
foreign import emitLineImpl :: String -> String -> Effect Unit

-- | Trace a prime-field element as a canonical decimal: positive and
-- | less than the field order.
field :: forall f. PrimeField f => String -> f -> Effect Unit
field label x = emitLineImpl label (BigInt.toString (toBigInt x))

-- | Trace a wrapped `F f` (the snarky DSL field-value newtype).
fieldF :: forall f. PrimeField f => String -> F f -> Effect Unit
fieldF label (F x) = field label x
