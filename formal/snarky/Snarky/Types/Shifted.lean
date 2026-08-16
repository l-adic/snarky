/-!
# Shifted scalar types

Port of `Snarky.Types.Shifted`
(packages/snarky-kimchi/src/Snarky/Types/Shifted.purs): the wrappers marking a scalar
as SHIFTED — carried in a form whose true value the consuming ladder recovers.
`Type1 t` stands for the scalar `2·t + 2^n + 1` (`n` the field size in bits), the
representation used when the scalar field is no larger than the circuit field;
`varBaseMul`'s ladder consumes it.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- Only the `Type1` newtype is ported — the `varBaseMul` gadget's scalar wrapper. PS's
  `Type2`/`SplitField` (the split representation for the larger-scalar-field case),
  the `Shifted` class, the forbidden-values checks, and the shifted circuit ops are
  consumed only by the pickles modules and arrive with them. The shift equation
  above is likewise not code here: it is the semantic reading the laws state.
-/

namespace Snarky

/-- A scalar carried shifted (PS `Type1`): the wrapped value `t` stands for
`2·t + 2^n + 1`. Phantom: the ladder consuming it realizes the shift. -/
structure Type1 (α : Type u) where
  /-- The shifted representative. -/
  val : α

end Snarky
