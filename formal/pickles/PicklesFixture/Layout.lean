import Snarky.DSL.SizedF
import Snarky.Kimchi.Constraint
import Kimchi.Columns
import Kimchi.Verifier.Kimchi
import Pasta.Endo

/-!
# The dumps' input layouts and the production constants they carry

The circuit dumps hand a driver one flat vector of field cells per circuit, and a harness
lays that vector out as the records the library gadgets take. This module holds the parts
of that layout shared by more than one driver: the two constraint types, the GLV
eigenvalues, the coset shifts production samples, and the two block readers (the previous
challenge vectors and the evaluation record).

The coset shifts are production values written out as literals, so they live here rather
than in any one driver: a second copy is a second thing to drift.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi CompElliptic.Fields.Pasta

/-- `unpack`'s bit reads go through the canonical representative. -/
instance toNatFp : ToNat Fp := ⟨ZMod.val⟩

/-- The same at the wrap field. -/
instance toNatFq : ToNat Fq := ⟨ZMod.val⟩

/-- The kimchi constraint sum at the step field. -/
abbrev C := KimchiConstraint Fp

/-- The kimchi constraint sum at the wrap field. -/
abbrev Cq := KimchiConstraint Fq

/-- Vesta's GLV eigenvalue, as a scalar-field element. -/
def endoVestaLam : Fp := (Pasta.vestaLam : ℤ)

/-- The wrap-side scalar-challenge endomorphism (OCaml `Endo.Step_inner_curve.scalar`):
Pallas's `λ` at the wrap field. -/
def endoPallasLam : Fq := (Pasta.pallasLam : ℤ)

/-- The step-side coset shifts: the Vesta scalar field's (`KimchiCurve.shifts`). They enter the
dump as Generic coefficients, so the comparison checks them against production rather than
trusting them. -/
def stepShifts : Fin permCols → Fp := fun i => Bulletproof.IpaVesta.curve.shifts[i]

/-- The wrap-side coset shifts: the Pallas scalar field's (`KimchiCurve.shifts`). -/
def wrapShifts : Fin permCols → Fq := fun i => Bulletproof.IpaPallas.curve.shifts[i]

/-- The two previous-challenge vectors from `base`, `rounds` entries each. -/
def prevChallengesOf {p : ℕ} (get : ℕ → FVar (ZMod p)) (base : ℕ) (rounds : ℕ := 16) :
    List (List (FVar (ZMod p))) :=
  [(List.range rounds).map fun i => get (base + i),
   (List.range rounds).map fun i => get (base + rounds + i)]

open Kimchi.Verifier in
/-- The public pair and the evaluation record from the dumps' layout, the public pair at
`pubBase`: then the 15 `w` pairs, 15 coefficient pairs, the `z` pair, 6 `s` pairs and the 6
selector pairs. -/
def evalsAt {p : ℕ} (get : ℕ → FVar (ZMod p)) (pubBase : ℕ) :
    PointEvaluations (FVar (ZMod p)) × ProofEvaluations (FVar (ZMod p)) :=
  let pair (i : ℕ) : PointEvaluations (FVar (ZMod p)) :=
    ⟨get (pubBase + i), get (pubBase + i + 1)⟩
  (pair 0,
   { w := Vector.ofFn fun j => pair (2 + 2 * j)
     coefficients := Vector.ofFn fun j => pair (32 + 2 * j)
     z := pair 62
     s := Vector.ofFn fun j => pair (64 + 2 * j)
     genericSelector := pair 76
     poseidonSelector := pair 78
     completeAddSelector := pair 80
     mulSelector := pair 82
     emulSelector := pair 84
     endomulScalarSelector := pair 86 })

end PicklesFixture
