import PicklesFixture.TokenParser

/-!
# PicklesFixture — decoders for recorded pickles data

The JSON ingestion layer for the `pickles` package, kept OUT of the `Pickles` library on
the same principle as `KimchiFixture`, `FixtureKit` and `BulletproofFixture`: checking
against recorded production data is not part of the development, so the proof library never
depends on a decoder. The `scripts/check_*` drivers import this directly.
-/
