import Poseidon.ConstantsFp
import Poseidon.ConstantsFq
import Poseidon.Basic
import Poseidon.FqSponge
import Poseidon.GroupMap
import Poseidon.RandomOracle

/-!
# Poseidon — the kimchi Poseidon sponge, executable and definitional

Root module of the `Poseidon` library:

- `Poseidon/Basic.lean`, with the generated `ConstantsFp` / `ConstantsFq` tables — the
  Poseidon permutation and duplex-sponge automaton over both Pasta base fields, at the
  production `fp_kimchi` / `fq_kimchi` parameters.
- `Poseidon/FqSponge.lean` — the field-pair generic consumer layer.
- `Poseidon/GroupMap.lean` — the SvdW map-to-curve.
- `Poseidon/RandomOracle.lean` — the block-mode hash (`Random_oracle.hash`), identified
  with the duplex automaton by `hash_eq_squeeze`.

Everything here is *specification*, validated against proof-systems vectors by the fixture
drivers under `scripts/` and not proved sound. Treating this sponge as a random oracle is the
Fiat–Shamir idealisation; its consumers, the bulletproof PCS and the kimchi verifier, carry
that as the uniform challenge table of their forking games rather than as an axiom.
-/
