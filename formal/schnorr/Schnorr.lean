import Schnorr.UnpackFull
import Schnorr.Wire

/-!
# The schnorr exemplar

The verifier-faithfulness rehearsal at the smallest statement. `Wire` is the protocol as
a deployed verifier sees it: a Schnorr identification statement over Vesta, on the wire
as five field elements, and `verify` the whole check at that encoding — deserialization
included. The in-circuit implementation and the laws tying it to `verify` arrive on top
of this.

`UnpackFull` is the canonical bit decomposition the challenge derivation needs: OCaml
`unpack_full`, which locks a decomposition to the representative below the modulus. It
lives here rather than in snarky's DSL because this package is its only consumer.

**What this package is NOT.** It does not model `packages/schnorr` — the deployed
PureScript port of Mina's production Schnorr *signature* verifier. That protocol runs
over Pallas with a `(r, s)` signature, a message, an `is_even` parity check, and an
x-only comparison; this package is a self-contained *identification* protocol over
Vesta with a package-local generator and full point equality, sharing only the kimchi
challenge convention and the gadget stack. Nothing here carries a byte-parity or
CS-oracle obligation against deployed circuits.
-/
