import CompElliptic.Curves.Pasta
import Poseidon.FqSponge

/-!
# The SvdW map-to-curve

The Shallue–van de Woestijne (SvdW) map from a curve's base field onto the curve,
transcribed from proof-systems `groupmap/src/lib.rs` (`BWParameters::to_group`) and generic
over the field. The kimchi verifier uses it to derive the per-proof `U` base: it squeezes a
base-field element from the transcript and maps it here.

A `Spec` carries the curve (with `A = 0`, since the construction is for curves
`y² = x³ + B`), the Tonelli–Shanks square-root data, and the `setup()` parameters as fixed
numerals, each validated by an `example` beside its instantiation. The square-root *choices*
baked into those constants are arkworks' — the values `setup()` computes — and their signs
are pinned by the fixture vectors.

## The three candidates

For a field element `t`, put `α = (t²·(t² + f(u)))⁻¹`, which is zero when non-invertible,
matching the Rust `unwrap_or(zero)` and `ZMod`'s `0⁻¹ = 0`. The candidate abscissae are

* `x₁ = (√(-3u²) − u)/2 − t⁴·α·√(-3u²)`,
* `x₂ = −u − x₁`,
* `x₃ = u − (t² + f(u))³·α·(3u²)⁻¹`,

and at least one of them is the abscissa of a curve point. The image is the first
`(xᵢ, √(xᵢ³ + B))` that exists, returned as an `SWPoint`; it is on-curve by construction,
because the square roots are CompElliptic's self-validating Tonelli–Shanks.

That some candidate always lands on the curve is Shallue and van de Woestijne's theorem, and
is not proved here. The Rust panics when none does; this branch returns the identity
`𝒪 = (0, 0)` instead.

## The Pasta instantiations

`GroupMapVesta` and `GroupMapPallas` instantiate the two Pasta curves, both `y² = x³ + 5`
with seed `u = 1` and `f(u) = 6`. Both are validated against production `to_group` vectors by
`scripts/check_fq_sponge.lean`.
-/

namespace Poseidon

open CompElliptic.Fields CompElliptic.CurveForms.ShortWeierstrass

namespace GroupMap

/-- The per-curve data of the SvdW map: the target curve (`A = 0`), the square-root data,
and the `setup()` constants. -/
structure Spec (q : ℕ) [Field (ZMod q)] [Fintype (ZMod q)] [DecidableEq (ZMod q)] where
  /-- The target curve — of the form `y² = x³ + B`, per `hA`. -/
  E : SWCurve (ZMod q)
  /-- The curve has no linear term, which the construction assumes throughout. -/
  hA : E.A = 0
  /-- The Tonelli–Shanks square-root data for the base field. -/
  sqrt : TonelliShanks (ZMod q)
  /-- The SvdW seed `u` (`setup()`). -/
  u : ZMod q
  /-- `f(u) = u³ + B` (`setup()` `fu`). -/
  fu : ZMod q
  /-- `√(-3u²)` — arkworks' root choice, pinned by the fixture vectors (`setup()`). -/
  sqrtNegThreeUSquared : ZMod q
  /-- `(√(-3u²) − u) / 2` (`setup()`). -/
  sqrtNegThreeUSquaredMinusUOver2 : ZMod q
  /-- `(3u²)⁻¹` (`setup()`). -/
  invThreeUSquared : ZMod q

variable {q : ℕ} [Field (ZMod q)] [Fintype (ZMod q)] [DecidableEq (ZMod q)]

/-- The curve equation right-hand side `f(x) = x³ + B`. -/
def curveEqn (spec : Spec q) (x : ZMod q) : ZMod q := x ^ 3 + spec.E.B

/-- `√(f(x))`, when `x` is the abscissa of a curve point (`get_y`). The *sign* of the root is
the Tonelli–Shanks representative's, which matches arkworks' current convention by
construction and is pinned by the group-map vectors rather than derived. So an arkworks
sqrt-convention change on a proof-systems bump would flip the derived `U` base, and would
surface only as a fixture mismatch (external-audit A-14). -/
def getY (spec : Spec q) (x : ZMod q) : Option (ZMod q) :=
  spec.sqrt.sqrt? (curveEqn spec x)

/-- The three SvdW candidate abscissae for `t` (`potential_xs`). -/
def potentialXs (spec : Spec q) (t : ZMod q) : ZMod q × ZMod q × ZMod q :=
  let t2 := t ^ 2
  let alpha := (t2 * (t2 + spec.fu))⁻¹
  let x1 := spec.sqrtNegThreeUSquaredMinusUOver2 - t2 ^ 2 * alpha * spec.sqrtNegThreeUSquared
  let x2 := -spec.u - x1
  let x3 := spec.u - (t2 + spec.fu) ^ 2 * (alpha * (t2 + spec.fu)) * spec.invThreeUSquared
  (x1, x2, x3)

/-- A found candidate is on the curve: `sqrt?` is self-validating (`sqrt?_mul_self`), so
`getY spec x = some y` means `y² = f(x)`. -/
private theorem onCurve_of_getY (spec : Spec q) {x y : ZMod q} (h : getY spec x = some y) :
    OnCurve spec.E.A spec.E.B (x, y) := by
  have hy : y * y = curveEqn spec x := TonelliShanks.sqrt?_mul_self spec.sqrt h
  show y ^ 2 = x ^ 3 + spec.E.A * x + spec.E.B
  rw [spec.hA, zero_mul, _root_.add_zero, pow_two, hy, curveEqn]

/-- The map-to-curve (`to_group`): the first candidate abscissa on the curve, with its
square root — a point correct by construction (`onCurve_of_getY`). The no-candidate
branch returns the identity `𝒪 = (0, 0)`. -/
def toGroup (spec : Spec q) (t : ZMod q) : SWPoint spec.E :=
  let (x1, x2, x3) := potentialXs spec t
  match h1 : getY spec x1 with
  | some y => ⟨x1, y, Or.inl (onCurve_of_getY spec h1)⟩
  | none =>
    match h2 : getY spec x2 with
    | some y => ⟨x2, y, Or.inl (onCurve_of_getY spec h2)⟩
    | none =>
      match h3 : getY spec x3 with
      | some y => ⟨x3, y, Or.inl (onCurve_of_getY spec h3)⟩
      | none => ⟨0, 0, Or.inr rfl⟩

end GroupMap

/-! ## The Vesta instantiation -/

namespace GroupMapVesta

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The SvdW seed: the first abscissa with `f(u) ≠ 0`. -/
def u : Fq := 1

/-- `f(u)`. -/
private def fu : Fq := 6

/-- `√(-3u²)` — the root `setup()` computes. -/
private def sqrtNegThreeUSquared : Fq :=
  5885731217013704028947117152987276604395468276778445611234961748972736355487

example : sqrtNegThreeUSquared ^ 2 = -3 * u ^ 2 := by decide

/-- `(√(-3u²) − u) / 2`. At `u = 1` this is `(√-3 − 1)/2`, a primitive cube root of unity, so
it is literally `Pasta.vestaEndo` — the Vesta base-field endomorphism coefficient `β`. -/
private def sqrtNegThreeUSquaredMinusUOver2 : Fq := Pasta.vestaEndo

example : 2 * sqrtNegThreeUSquaredMinusUOver2 = sqrtNegThreeUSquared - u := by decide

/-- `(3u²)⁻¹`. -/
private def invThreeUSquared : Fq :=
  19298681539552699237261830834781317975575370987961098253119828498928908632065

example : invThreeUSquared * (3 * u ^ 2) = 1 := by decide

/-- The Vesta SvdW parameters (`BWParameters::<VestaParameters>::setup()`). -/
def spec : GroupMap.Spec PALLAS_SCALAR_CARD where
  E := Vesta.curve
  hA := rfl
  sqrt := vestaBase
  u := u
  fu := fu
  sqrtNegThreeUSquared := sqrtNegThreeUSquared
  sqrtNegThreeUSquaredMinusUOver2 := sqrtNegThreeUSquaredMinusUOver2
  invThreeUSquared := invThreeUSquared

example : fu = GroupMap.curveEqn spec u := by decide

/-- The Vesta map-to-curve. -/
def toGroup : Fq → SWPoint Vesta.curve :=
  GroupMap.toGroup spec

end GroupMapVesta

/-! ## The Pallas instantiation -/

namespace GroupMapPallas

open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The SvdW seed: the first abscissa with `f(u) ≠ 0`. -/
def u : Fp := 1

/-- `f(u)`. -/
private def fu : Fp := 6

/-- `√(-3u²)` — the root `setup()` computes (the opposite sign choice to the Vesta side). -/
private def sqrtNegThreeUSquared : Fp :=
  17006931536212783554987228065028097629383328157457783420645920607630467569011

example : sqrtNegThreeUSquared ^ 2 = -3 * u ^ 2 := by decide

/-- `(√(-3u²) − u) / 2`. At `u = 1` this is `(√-3 − 1)/2` at `setup()`'s root choice, which
picks the *other* primitive cube root of unity than the Pallas endomorphism coefficient does:
it is `pallasEndo²`, not `pallasEndo`. -/
private def sqrtNegThreeUSquaredMinusUOver2 : Fp :=
  8503465768106391777493614032514048814691664078728891710322960303815233784505

example : sqrtNegThreeUSquaredMinusUOver2 = Pasta.pallasEndo ^ 2 := by decide

example : 2 * sqrtNegThreeUSquaredMinusUOver2 = sqrtNegThreeUSquared - u := by decide

/-- `(3u²)⁻¹`. -/
private def invThreeUSquared : Fp :=
  19298681539552699237261830834781317975575370987961040477303117842899978420225

example : invThreeUSquared * (3 * u ^ 2) = 1 := by decide

/-- The Pallas SvdW parameters (`BWParameters::<PallasParameters>::setup()`). -/
def spec : GroupMap.Spec PALLAS_BASE_CARD where
  E := Pallas.curve
  hA := rfl
  sqrt := pallasBase
  u := u
  fu := fu
  sqrtNegThreeUSquared := sqrtNegThreeUSquared
  sqrtNegThreeUSquaredMinusUOver2 := sqrtNegThreeUSquaredMinusUOver2
  invThreeUSquared := invThreeUSquared

example : fu = GroupMap.curveEqn spec u := by decide

/-- The Pallas map-to-curve. -/
def toGroup : Fp → SWPoint Pallas.curve :=
  GroupMap.toGroup spec

end GroupMapPallas

end Poseidon
