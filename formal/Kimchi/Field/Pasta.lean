import Mathlib.Data.ZMod.Basic

/-!
# The Pasta base fields `Fp` (Pallas) and `Fq` (Vesta)

The two 255-bit primes of the Pasta cycle, taken verbatim from the PureScript
backend (`packages/curves/src/Snarky/Curves/PastaField.js`):

* `pastaP` — Pallas base field = Vesta scalar field.
* `pastaQ` — Vesta base field = Pallas scalar field.

These are the fields the dumped kimchi circuits live over: a circuit's coefficient
and witness values are elements of `Fp` (the executable checker runs in `ZMod pastaP`,
which is a `CommRing` for free — no primality needed).

## Primality

`Field (ZMod pastaP)` (needed only to *instantiate* the EC-gate soundness theorems at
Pasta, not to run the checker) requires `Fact (Nat.Prime pastaP)`. Primality of a
255-bit number is not something `decide`/`norm_num` can discharge in the kernel, so we
record it as an explicit, documented axiom. It is a published, well-established fact;
the honest upgrade is a Pratt certificate over the known factorization of `pastaP − 1`.
The axiom is part of the same trusted base as the `Cycle/Axioms.lean` Pasta postulates.

**Planned upgrade (axiom removal).** Daira Hopwood's `CompElliptic`
(https://github.com/daira/CompElliptic, MIT/Apache-2.0) already proves exactly these two
facts with machine-verified Lucas–Pratt certificates — its `PALLAS_BASE_CARD` /
`PALLAS_SCALAR_CARD` are byte-identical to `pastaP` / `pastaQ` here. It also supplies a
verified short-Weierstrass group law for Pallas/Vesta bridging to Mathlib, which would let
us instantiate the generic `AddComplete` soundness theorems at the real curves. It targets
Lean `v4.30.0-rc2`, so adopting it is a deliberate toolchain/Mathlib bump deferred to a
focused follow-up; the swap is mechanical because the constants already match.
-/

namespace Kimchi.Field

/-- Pallas base field characteristic (Vesta scalar field). -/
def pastaP : ℕ :=
  0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001

/-- Vesta base field characteristic (Pallas scalar field). -/
def pastaQ : ℕ :=
  0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

/-- **AXIOM.** `pastaP` is prime. (Published Pasta-cycle fact; see module docstring.) -/
axiom pastaP_prime : Nat.Prime pastaP
/-- **AXIOM.** `pastaQ` is prime. (Published Pasta-cycle fact; see module docstring.) -/
axiom pastaQ_prime : Nat.Prime pastaQ

instance : Fact (Nat.Prime pastaP) := ⟨pastaP_prime⟩
instance : Fact (Nat.Prime pastaQ) := ⟨pastaQ_prime⟩

/-- Pallas base field. -/
abbrev Fp := ZMod pastaP
/-- Vesta base field. -/
abbrev Fq := ZMod pastaQ

end Kimchi.Field
