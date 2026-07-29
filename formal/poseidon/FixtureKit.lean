import FixtureKit.Parse
import FixtureKit.Trace

/-!
# FixtureKit — shared JSON decoders and the trace-check driver

Root module of the `FixtureKit` library: the shared vocabulary of the proof-systems fixture
files (canonical-decimal field elements, coordinate-pair points), and the cases-×-ops trace
driver the `check_*` scripts build on.

None of it is Poseidon-specific. It ships with this package because the sponge checks were
its first consumer; the PCS and kimchi fixture harnesses reuse it too.
-/
