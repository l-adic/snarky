import Poseidon.ConstantsFp
import Poseidon.ConstantsFq
import Poseidon.Basic
import Poseidon.FqSponge
import Poseidon.GroupMap
import Poseidon.RandomOracle

/-!
# Poseidon — the kimchi Poseidon sponge, executable and definitional

Root module of the `Poseidon` library:

- `Poseidon/Basic.lean` — the Poseidon permutation and duplex sponge over both Pasta base
  fields, with the generated parameter tables `Poseidon/ConstantsFp.lean` and
  `Poseidon/ConstantsFq.lean`.
- `Poseidon/FqSponge.lean` — the Fq-sponge the kimchi verifier consumes.
- `Poseidon/GroupMap.lean` — the SvdW map-to-curve.
- `Poseidon/RandomOracle.lean` — the block-mode hash, identified with the duplex sponge by
  `hash_eq_squeeze`.

Everything here is specification, checked against upstream vectors by the drivers in
`poseidon/scripts/` and not proved sound.
-/
