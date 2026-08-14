/-!
# Kimchi circuit utilities

Port of `Snarky.Circuit.Kimchi.Utils`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/Utils.purs): `mapAccumM`, the
accumulating traversal the gate gadgets thread their per-row state through.

Name map: `mapAccumM` keeps its name. The module's `verifyCircuit`/`verifyCircuitM`
are solver smoke-test `Effect` machinery with no analogue in the pure embedding and
are not ported.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS defines it as a `StateT` traversal; here it is a `forIn` loop, so the `Std.Do`
  loop rules walk it directly and it owes no composition laws of its own. The
  spelling is bind-for-bind the same traversal: one `f` call per element, outputs
  collected in element order.
- PS's `Traversable t` renders at `List` (the constraint payloads are lists).
-/

namespace Snarky.Kimchi

/-- Thread an accumulator through a monadic map (PS `mapAccumM`): one `f` call per
element in order, returning the outputs in element order and the final
accumulator. -/
def mapAccumM {m : Type u → Type v} [Monad m] {s a b : Type u}
    (f : s → a → m (b × s)) (init : s) (xs : List a) : m (List b × s) := do
  let mut acc := init
  let mut out : List b := []
  for x in xs do
    let (y, acc') ← f acc x
    out := out ++ [y]
    acc := acc'
  pure (out, acc)

end Snarky.Kimchi
