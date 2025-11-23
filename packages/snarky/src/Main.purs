module Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import Snarky.Curves.BN254 as BN254
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

main :: Effect Unit
main = do
  log "🐙 Snarky: Demonstrating the curves library!"

  log "\n🔵 Pallas curve operations:"
  let pallasFour = (one + one + one + one) :: Pallas.ScalarField
  log $ "1 + 1 + 1 + 1 = " <> show pallasFour
  log $ "4 * 2 = " <> show (pallasFour * (one + one))

  log "\n🟡 Vesta curve operations:"
  let vestaFour = (one + one + one + one) :: Vesta.ScalarField
  log $ "1 + 1 + 1 + 1 = " <> show vestaFour
  log $ "4 * 2 = " <> show (vestaFour * (one + one))

  log "\n🟢 BN254 curve operations:"
  let bn254Four = (one + one + one + one) :: BN254.ScalarField
  log $ "1 + 1 + 1 + 1 = " <> show bn254Four
  log $ "4 * 2 = " <> show (bn254Four * (one + one))

  log "\n✨ All three curves working together!"