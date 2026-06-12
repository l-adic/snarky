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
  ) where

import Data.Functor.Variant (VariantF, case_)
import Data.NaturalTransformation (type (~>))
import Effect (Effect)

newtype AdviceHandler :: Row (Type -> Type) -> Type
newtype AdviceHandler r = AdviceHandler (VariantF r ~> Effect)

runAdviceHandler :: forall r a. AdviceHandler r -> VariantF r a -> Effect a
runAdviceHandler (AdviceHandler f) = f

-- | The handler for the empty advice row (`VariantF ()` is uninhabited).
noAdvice :: AdviceHandler ()
noAdvice = AdviceHandler case_
