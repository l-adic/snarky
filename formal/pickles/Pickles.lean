import Pickles.Reflect.Soundness
import Pickles.FtEval0
import Pickles.IPA
import Pickles.CombinedInnerProduct

/-!
# Pickles — the in-circuit kimchi verifier

The PureScript `packages/pickles` verification gadgets, ported to the snarky DSL and
proved faithful to the DEPLOYED verifier: `Kimchi.Verifier.kimchiVerify` and the closed
forms of `Kimchi/Verifier/Reflect.lean`. Those are the specs — a fragment's soundness is
stated against the run function it implements, never against a restatement of it.

The statement shape is `Schnorr`'s at scale: every satisfying valuation of the compiled
constraints certifies the wire computation, and the honest run completes. It is
**relative** faithfulness. It neither assumes nor establishes that the wire verifier is
sound; see `formal/docs/soundness-line-retirement.md` for why soundness is out of scope
here, and `formal/docs/circuit-verifier-faithfulness.md` for the fragment decomposition
this package follows.
-/
