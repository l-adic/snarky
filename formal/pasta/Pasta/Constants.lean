import Mathlib.Data.Int.Notation
import CompElliptic.Fields.Pasta

/-!
# The Pasta GLV constants

The endomorphism coefficients `β` and scalar eigenvalues `λ` of the Pallas and Vesta GLV
endomorphisms `φ(x, y) = (β·x, y)`, as concrete numerals in a leaf module: the CM axioms
(`φ = [λ]`) and the GLV short-basis certificates that consume them live in
`pasta/Pasta/Basic.lean` (whose import cone includes all of Mathlib via the EC oracle), while the
Fiat-Shamir layer (the `poseidon` package) consumes `vesta_lam` and `vesta_endo` from the fast
import lane.

Each `β` is *proved* a primitive cube root of unity beside its definition — the property
that makes `φ` a curve endomorphism on `y² = x³ + b`. The only remaining trusted facts about
the endomorphisms are the eigenvalue relations (`Pasta.pallas_eigen` /
`vesta_eigen`).
-/

namespace Pasta

open CompElliptic.Fields.Pasta

/-- The Pallas base-field endomorphism coefficient `β`: a primitive cube root of unity
    (proved below), so `φ(x, y) = (β·x, y)` maps `y² = x³ + 5` to itself. -/
def pallas_endo : Fp :=
  20444556541222657078399132219657928148671392403212669005631716460534733845831

/-- `β³ = 1` on Pallas. -/
theorem pallas_endo_cube : pallas_endo ^ 3 = 1 := by decide

/-- `β ≠ 1` on Pallas (with `pallas_endo_cube`: `β` is a *primitive* cube root). -/
theorem pallas_endo_ne_one : pallas_endo ≠ 1 := by decide

/-- The Vesta base-field endomorphism coefficient `β`: a primitive cube root of unity
    (proved below), so `φ(x, y) = (β·x, y)` maps `y² = x³ + 5` to itself. It is also the
    SvdW map-to-curve parameter `(√-3 − 1)/2` (`Poseidon.GroupMapVesta`). -/
def vesta_endo : Fq :=
  2942865608506852014473558576493638302197734138389222805617480874486368177743

/-- `β³ = 1` on Vesta. -/
theorem vesta_endo_cube : vesta_endo ^ 3 = 1 := by decide

/-- `β ≠ 1` on Vesta (with `vesta_endo_cube`: `β` is a *primitive* cube root). -/
theorem vesta_endo_ne_one : vesta_endo ≠ 1 := by decide

/-- The scalar eigenvalue `λ` of the Pallas endomorphism `φ` — a primitive cube root of unity
    in the scalar field (`endo_scalar`, from `Snarky.Curves.PastaCurve`). Concrete, so the
    GLV short-basis fact in `pasta/Pasta/Basic.lean` is *proved*, not assumed. -/
def pallas_lam : ℤ :=
  26005156700822196841419187675678338661165322343552424574062261873906994770353

/-- The scalar eigenvalue `λ` of the Vesta endomorphism `φ` — a primitive cube root of unity
    in the scalar field (`endo_scalar`). Concrete, so the GLV short-basis fact in
    `pasta/Pasta/Basic.lean` is proved; it is also the `λ` of the Fiat-Shamir challenge expansion
    (proof-systems `endos::<Vesta>().1`). -/
def vesta_lam : ℤ :=
  8503465768106391777493614032514048814691664078728891710322960303815233784505

end Pasta
