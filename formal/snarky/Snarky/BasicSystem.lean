import Snarky.CVar

namespace Snarky

universe u

/-- The constraint constructors every backend supplies (PS `class BasicSystem f c`). -/
class BasicSystem (F c : Type u) where
  /-- The rank-1 constraint `left * right = output`. -/
  r1cs : (left right output : CVar F) → c
  /-- The equality constraint `a = b`. -/
  equal : (a b : CVar F) → c
  /-- The square constraint `a * a = sq`. -/
  square : (a sq : CVar F) → c
  /-- The booleanity constraint: `x` must evaluate to `0` or `1`. -/
  boolean : (x : CVar F) → c

end Snarky
