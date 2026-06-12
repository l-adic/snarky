-- | The prover's error channel as tagged JS exceptions.
-- |
-- | The circuit/witness monads are direct readers over `Effect`; a failing
-- | witness or constraint must abort the whole interpretation. Threading
-- | `Either` through every bind would tax the hot path for the (rare) error
-- | case, so instead `throwEvalError` throws a JS `Error` carrying the
-- | `EvaluationError` under a private symbol, and `catchEvalError` (used
-- | only at interpreter boundaries — `runAsProver`, `runCircuitProver`)
-- | recovers it.
-- |
-- | Although the underlying JS `try` necessarily intercepts EVERY thrown
-- | error, `catchEvalError` converts only errors carrying this module's
-- | private `Symbol` tag to `Left`; anything else is RETHROWN, so genuine
-- | JS errors (bugs) cannot be mistaken for circuit failures, and no
-- | foreign code can forge or intercept the tag (the `Symbol` never
-- | leaves `EvalError.js`).
-- |
-- | Throw-only semantics: there is deliberately no user-facing `catch` —
-- | matching the old `EXCEPT`-row behavior where `Except.catch` was never
-- | used.
module Snarky.Circuit.EvalError
  ( throwEvalError
  , catchEvalError
  ) where

import Data.Either (Either(..))
import Effect (Effect)
import Snarky.Circuit.CVar (EvaluationError)

foreign import throwEvalErrorImpl :: forall a. EvaluationError -> Effect a

foreign import catchEvalErrorImpl
  :: forall a r
   . (EvaluationError -> r)
  -> (a -> r)
  -> Effect a
  -> Effect r

throwEvalError :: forall a. EvaluationError -> Effect a
throwEvalError = throwEvalErrorImpl

catchEvalError :: forall a. Effect a -> Effect (Either EvaluationError a)
catchEvalError = catchEvalErrorImpl Left Right
