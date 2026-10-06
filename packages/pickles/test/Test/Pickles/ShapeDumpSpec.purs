module Test.Pickles.ShapeDumpSpec (spec) where

import Prelude

import Colog (LoggerT, Message)
import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Foreign (MultipleErrors)
import Pickles.Dump.Shape (ShapeDump, SlotSourceDump(..), SlotSourceSeed(..), assembleShape)
import Simple.JSON (readJSON, writeJSON)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Dump.Shape" do
  it "encodes and decodes all three slot-source variants" \_ -> liftEffect do
    let
      statement = { inputFields: 1, outputFields: 0 }
      imported = { statement: { inputFields: 0, outputFields: 2 }, width: 1 }

      shape :: ShapeDump
      shape =
        { statement
        , imports: [ imported ]
        , branches:
            [ { slots: [] }
            , { slots: [ SelfSource, ExternalSource 0, SideLoadedSource imported ] }
            ]
        }
      json = writeJSON shape
    case (readJSON json :: Either MultipleErrors ShapeDump) of
      Left _ -> throw "shape JSON did not decode"
      Right decoded -> writeJSON decoded `shouldEqual` json

  it "assembles branch-local slots without circuit data" \_ -> liftEffect do
    let
      statement = { inputFields: 1, outputFields: 0 }
      sideLoaded = { statement: { inputFields: 0, outputFields: 2 }, width: 2 }
      result = assembleShape
        [ { statement, slots: [] }
        , { statement
          , slots:
              [ { statement, width: 2, source: SelfSeed }
              , { statement: sideLoaded.statement, width: 2, source: SideLoadedSeed }
              ]
          }
        ]

      expected :: ShapeDump
      expected =
        { statement
        , imports: []
        , branches: [ { slots: [] }, { slots: [ SelfSource, SideLoadedSource sideLoaded ] } ]
        }
    case result of
      Left _ -> throw "valid shape assembly failed"
      Right shape -> writeJSON shape `shouldEqual` writeJSON expected

  it "rejects a Self slot with a different statement field count" \_ -> liftEffect do
    let
      statement = { inputFields: 1, outputFields: 0 }
      other = { inputFields: 0, outputFields: 2 }
    case assembleShape [ { statement, slots: [ { statement: other, width: 1, source: SelfSeed } ] } ] of
      Left _ -> pure unit
      Right _ -> throw "a mismatched Self statement was accepted"

  it "reuses an import index for the same complete key" \_ -> liftEffect do
    let
      statement = { inputFields: 0, outputFields: 1 }
      imported = { inputFields: 1, outputFields: 0 }
      source = ExternalSeed { key: "complete verifier index A", statement: imported, width: 0 }
      slot = { statement: imported, width: 0, source }
      reinterpretedSlot = { statement, width: 0, source }
      result = assembleShape
        [ { statement, slots: [ slot ] }
        , { statement, slots: [ reinterpretedSlot, slot ] }
        ]

      expected :: ShapeDump
      expected =
        { statement
        , imports: [ { statement: imported, width: 0 } ]
        , branches:
            [ { slots: [ ExternalSource 0 ] }
            , { slots: [ ExternalSource 0, ExternalSource 0 ] }
            ]
        }
    case result of
      Left _ -> throw "repeated import assembly failed"
      Right shape -> writeJSON shape `shouldEqual` writeJSON expected

  it "rejects one key with conflicting source layouts" \_ -> liftEffect do
    let
      statement = { inputFields: 0, outputFields: 1 }
      sourceA = ExternalSeed
        { key: "complete verifier index A", statement: { inputFields: 1, outputFields: 0 }, width: 0 }
      sourceB = ExternalSeed
        { key: "complete verifier index A", statement: { inputFields: 0, outputFields: 1 }, width: 0 }
    case
      assembleShape
        [ { statement, slots: [ { statement, width: 0, source: sourceA } ] }
        , { statement, slots: [ { statement, width: 0, source: sourceB } ] }
        ]
      of
      Left _ -> pure unit
      Right _ -> throw "one imported key received two statement layouts"
