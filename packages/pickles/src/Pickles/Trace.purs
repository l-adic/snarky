-- | Trace logger for byte-identical pickles transcript reproduction tests.
-- |
-- | Sister module to OCaml's `Pickles_trace`
-- | (`mina/src/lib/crypto/pickles/pickles_trace.ml`). Both write to the file
-- | named by the `PICKLES_TRACE_FILE` env var, one line per traced value, in
-- | the format `[LABEL] DECIMAL_VALUE`. Both sides MUST emit the same labels
-- | in the same order so the resulting trace files can be diffed.
-- |
-- | When `PICKLES_TRACE_FILE` is unset, every trace function is a no-op
-- | (it pays only an env-var lookup), so production circuit code that
-- | sprinkles trace points pays effectively zero cost.
-- |
-- | Label naming convention: semantic, dot-separated, lowercase. Examples:
-- |
-- |     [step.app_state]
-- |     [step.unfinalized.0.beta]
-- |     [step.proof.public_input.0]
-- |     [wrap.statement.deferred_values.combined_inner_product]
-- |
-- | The OCaml-side helper at `mina/src/lib/crypto/pickles/pickles_trace.ml`
-- | MUST emit the same label strings for the same logical values.
module Pickles.Trace
  ( field
  , fieldF
  , int
  , string
  ) where

import Prelude

import Effect (Effect)
import JS.BigInt as BigInt
import Snarky.Circuit.DSL (F(..))
import Snarky.Curves.Class (class PrimeField, toBigInt)

-- | FFI: emit a single trace line `[LABEL] VALUE\n` to the trace file
-- | named by `PICKLES_TRACE_FILE`. No-op when the env var is unset. The
-- | underlying file handle is opened lazily on first call (truncating
-- | mode) and kept open for the lifetime of the process.
foreign import emitLineImpl :: String -> String -> Effect Unit

-- | Trace a bare prime-field element `f` as decimal.
-- |
-- | Used for the kinds of values that carry semantic meaning at the
-- | trace boundary — public inputs, sponge digests, scalar challenges,
-- | etc. The decimal representation is canonical (positive, < field
-- | order), matching what OCaml's `{Tick,Tock}.Field.to_string` emits.
field :: forall f. PrimeField f => String -> f -> Effect Unit
field label x = emitLineImpl label (BigInt.toString (toBigInt x))

-- | Trace a wrapped `F f` (the snarky DSL field-value newtype).
fieldF :: forall f. PrimeField f => String -> F f -> Effect Unit
fieldF label (F x) = field label x

-- | Trace a primitive int.
int :: String -> Int -> Effect Unit
int label x = emitLineImpl label (show x)

-- | Trace an opaque string. Useful for sentinel markers (e.g. begin/end of
-- | a circuit phase) where the value is structural rather than numeric.
string :: String -> String -> Effect Unit
string label x = emitLineImpl label x
