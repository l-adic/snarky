import Kimchi.Sponge.FqSponge

/-!
# The Vesta map-to-curve

The SvdW map from the Vesta base field onto the Vesta curve, transcribed from proof-systems
`groupmap/src/lib.rs` (`BWParameters::to_group`). The kimchi verifier derives the per-proof
`U` base by squeezing a base-field element from the transcript and mapping it here.

The `setup()` parameters are fixed numerals, each validated by an `example` beside its
definition: the seed `u = 1` (the first abscissa with `f(u) ≠ 0`), `f(u) = 6`, `√(-3u²)`,
`(√(-3u²) − u)/2` (a primitive cube root of unity — the Vesta endomorphism coefficient `β`),
and `(3u²)⁻¹`. The square-root *choice* in `√(-3u²)` is arkworks' (the value `setup()`
computes); its sign is pinned by the `u_base` fixture comparison.

For a field element `t`: `α = (t²·(t² + f(u)))⁻¹` (zero when non-invertible, matching the
Rust `unwrap_or(zero)` and `ZMod`'s `0⁻¹ = 0`), then three candidate abscissae

* `x₁ = (√(-3u²) − u)/2 − t⁴·α·√(-3u²)`,
* `x₂ = −u − x₁`,
* `x₃ = u − (t² + f(u))³·α·(3u²)⁻¹`,

of which at least one is the abscissa of a curve point (SvdW06); the image is the first
`(xᵢ, √(xᵢ³ + B))` that exists. Runtime square roots are CompElliptic's self-validating
Tonelli–Shanks (`vestaBase.sqrt?`); the fixture check compares the full image point against
the production verifier's `U`, so a root-choice divergence from arkworks would surface
there. The Rust panics when no candidate lands on the curve (unreachable by SvdW06); here
that branch returns the identity sentinel `(0, 0)`.

Validated against the `u_base` of the production `SRS::verify` transcript by
`scripts/check_fq_sponge.lean`.
-/

namespace Kimchi.Sponge.GroupMapVesta

open CompElliptic.Fields.Pasta Kimchi.Sponge.FqVesta

/-- The curve equation right-hand side `f(x) = x³ + B` (Vesta: `A = 0`, `B = 5`). -/
def curveEqn (x : Fq) : Fq := x ^ 3 + 5

/-- The SvdW seed: the first abscissa with `f(u) ≠ 0`. -/
def u : Fq := 1

/-- `f(u)`. -/
def fu : Fq := 6

example : fu = curveEqn u := by decide

/-- `√(-3u²)` — the root `setup()` computes. -/
def sqrtNegThreeUSquared : Fq :=
  5885731217013704028947117152987276604395468276778445611234961748972736355487

example : sqrtNegThreeUSquared ^ 2 = -3 * u ^ 2 := by decide

/-- `(√(-3u²) − u) / 2`. At `u = 1` this is `(√-3 − 1)/2`, a primitive cube root of unity —
the Vesta base-field endomorphism coefficient `β`, of which it is a reuse. -/
def sqrtNegThreeUSquaredMinusUOver2 : Fq := Kimchi.Pasta.vesta_endo

example : 2 * sqrtNegThreeUSquaredMinusUOver2 = sqrtNegThreeUSquared - u := by decide

/-- `(3u²)⁻¹`. -/
def invThreeUSquared : Fq :=
  19298681539552699237261830834781317975575370987961098253119828498928908632065

example : invThreeUSquared * (3 * u ^ 2) = 1 := by decide

/-- `√(f(x))`, when `x` is the abscissa of a curve point (`get_y`). -/
def getY (x : Fq) : Option Fq := vestaBase.sqrt? (curveEqn x)

/-- The three SvdW candidate abscissae for `t` (`potential_xs`). -/
def potentialXs (t : Fq) : Fq × Fq × Fq :=
  let t2 := t ^ 2
  let alpha := (t2 * (t2 + fu))⁻¹
  let x1 := sqrtNegThreeUSquaredMinusUOver2 - t2 ^ 2 * alpha * sqrtNegThreeUSquared
  let x2 := -u - x1
  let x3 := u - (t2 + fu) ^ 2 * (alpha * (t2 + fu)) * invThreeUSquared
  (x1, x2, x3)

/-- The map-to-curve (`to_group`): the first candidate abscissa on the curve, with its
square root. The no-candidate branch (a Rust panic, unreachable by SvdW06) returns
`(0, 0)`. -/
def toGroup (t : Fq) : Fq × Fq :=
  let (x1, x2, x3) := potentialXs t
  match getY x1 with
  | some y => (x1, y)
  | none =>
    match getY x2 with
    | some y => (x2, y)
    | none =>
      match getY x3 with
      | some y => (x3, y)
      | none => (0, 0)

end Kimchi.Sponge.GroupMapVesta
