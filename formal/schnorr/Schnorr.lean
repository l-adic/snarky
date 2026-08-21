import Schnorr.Wire
import Schnorr.Circuit
import Schnorr.UnpackFull
import Schnorr.Laws
import Schnorr.Boundary

/-!
# The schnorr exemplar

The verifier-faithfulness rehearsal at the smallest statement: a wire-protocol
Schnorr identification verifier over Vesta (`Wire`), its in-circuit implementation
on the deployed kimchi gadget stack (`Circuit`), and the proofs that the circuit is
faithful to the wire — the endpoint pair (`Laws`) and the whole-circuit compile/solve
seam (`Boundary`), with the canonical bit-decomposition lock ported in `UnpackFull`.

**What this package is NOT.** It does not model `packages/schnorr` — the deployed
PureScript port of Mina's production Schnorr *signature* verifier. That protocol runs
over Pallas with a `(r, s)` signature, a message, an `is_even` parity check, and an
x-only comparison; this package is a self-contained *identification* protocol over
Vesta with a package-local generator and full point equality, sharing only the kimchi
challenge convention and the gadget stack. `UnpackFull` alone is a PS port (its
deviations recorded in its docstring); nothing here carries a byte-parity or
CS-oracle obligation against deployed circuits.
-/
