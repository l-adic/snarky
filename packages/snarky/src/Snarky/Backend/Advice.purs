-- | The advice handler: how an application discharges the open advice tail
-- | `r` of a circuit (or witness) program when an interpreter runs it.
-- |
-- | The circuit interpreters (`Snarky.Backend.Builder`, `Snarky.Backend
-- | .Prover`) and the witness runner (`runAsProver`) interpret their `Run`
-- | programs DIRECTLY into `Effect` — they handle the `circuit` / `except` /
-- | `reader` / `effect` labels inline and delegate everything else (the
-- | application's advice effects: Merkle requests, account lookups, ...) to
-- | an `AdviceHandler r` supplied by the caller.
-- |
-- | A newtype rather than a synonym because handlers are STORED — in
-- | pickles `RuleEntry` record fields and prover carriers — and PureScript
-- | rejects rank-2 types at the record-field level. The rank-2 polymorphism
-- | is real: one handler value is applied both at the circuit row and, via
-- | `Exists`, at the witness row. The newtype is erased by purs-backend-es.
module Snarky.Backend.Advice
  ( AdviceHandler(..)
  , runAdviceHandler
  , noAdvice
  , badAdvice
  ) where

import Data.Functor.Variant (VariantF, case_)
import Data.NaturalTransformation (type (~>))
import Effect (Effect)
import Effect.Exception (error, throwException)

newtype AdviceHandler :: Row (Type -> Type) -> Type
newtype AdviceHandler r = AdviceHandler (VariantF r ~> Effect)

runAdviceHandler :: forall r a. AdviceHandler r -> VariantF r a -> Effect a
runAdviceHandler (AdviceHandler f) = f

-- | The handler for the empty advice row (`VariantF ()` is uninhabited).
noAdvice :: AdviceHandler ()
noAdvice = AdviceHandler case_

-- | A handler for ANY advice row that throws if ever invoked. The
-- | compile-time handler: compilation only allocates variables (`exists`
-- | bodies are discarded), so no advice op can fire — pass `badAdvice`
-- | instead of building a per-op crash record. Passing it to a PROVER is
-- | a bug, and the error says so.
badAdvice :: forall r. AdviceHandler r
badAdvice = AdviceHandler \_ ->
  throwException
    ( error
        "badAdvice: an advice op was invoked. badAdvice is only safe for compilation (which never runs advice); the prover needs a real AdviceHandler."
    )
