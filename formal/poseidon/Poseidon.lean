import Poseidon.ConstantsFp
import Poseidon.ConstantsFq
import Poseidon.Basic
import Poseidon.FqSponge
import Poseidon.GroupMap

/-!
# Poseidon — the kimchi Poseidon sponge, executable and definitional

Root module of the `Poseidon` library: the Poseidon permutation and duplex-sponge
automaton over both Pasta base fields with the production `fp_kimchi`/`fq_kimchi`
parameter tables (`Basic`, `ConstantsFp/Fq`), the field-pair generic `FqSponge`
consumer layer (`FqSponge`), and the SvdW map-to-curve (`GroupMap`).

Everything here is *specification*, validated against proof-systems vectors by the
fixture drivers under `scripts/` — not proved sound. Treating this sponge as a random
oracle is precisely the Fiat–Shamir assumption its consumers (the bulletproof PCS, the
kimchi verifier) declare as their axiom.
-/
