import Snarky.Encoding.ReadsAttr
import Snarky.Prover
import Snarky.Types.Shifted
import Snarky.Kimchi.Circuit.AddComplete
import Snarky.Kimchi.Circuit.Poseidon

/-!
# The reading simp set

The formers' reading lemmas and the hand-written leaf instances', as one simp set. A
record's `CircuitType` instance is `CircuitType.ofEquiv` at its product decomposition; with
that decomposition's `@[simps apply]` projection lemma, `simp [reads_simps]` rewrites
`Reads V x a` through the named instance (`reads_ofEquiv` matches it: instances are
reducible), through the products and vectors, down to the cells — for nested records too.
No per-record reading lemma is needed; the projection lemma is the record's whole
contribution.
-/

namespace Snarky

attribute [reads_simps]
  CircuitType.reads_ofEquiv CircuitType.scoped_ofEquiv CircuitType.readVal_ofEquiv
  CircuitType.reads_prod CircuitType.scoped_prod
  CircuitType.reads_vector CircuitType.scoped_vector
  CircuitType.reads_fvar CircuitType.scoped_fvar
  CircuitType.reads_boolVar CircuitType.scoped_boolVar
  CircuitType.reads_unchecked CircuitType.scoped_unchecked
  CircuitType.reads_unit CircuitType.scoped_unit
  reads_type1 scoped_type1
  Kimchi.reads_affinePoint Kimchi.scoped_affinePoint
  Kimchi.reads_spongeState Kimchi.scoped_spongeState

end Snarky
