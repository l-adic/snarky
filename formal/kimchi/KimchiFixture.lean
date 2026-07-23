import KimchiFixture.Kimchi
import KimchiFixture.PS

/-!
# The `KimchiFixture` library root

The JSON decoders the fixture-check scripts read production dumps with (see the module
docstrings of `KimchiFixture.Kimchi` and `KimchiFixture.PS`). This root exists so the
library has a single importable module — the lint and kernel-replay gates resolve the
library through it, mirroring `FixtureKit` (poseidon) and `BulletproofFixture`
(bulletproof-pcs).
-/
