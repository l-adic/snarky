import Snarky
import Snarky.Kimchi.Backend.Compile
import KimchiFixture.PS
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

/-- The step-side coset shifts, production's Blake2b-sampled `Shifts::new` values (PS reads
them through `domainShifts`; recorded in `kimchi/fixtures/linearization_vesta{,_emul}.json`,
identical at both domain sizes there). They enter the dump as Generic coefficients, so the
comparison checks them against production rather than trusting them. -/
def stepShifts : Fin permCols → Fp := fun i =>
  (#[1, 328286983623303317637963920346571898945724874896624808297627776768640590563,
     91433028157768305433241271390810941046493237899366836746431422160024463706,
     240213425742950025341713987028051046476975246675775993287051503548513551377,
     417757293700961807788464308236931191792053554682199437460107260306038610067,
     430348682428487492383428014506756320686619984007091686553051322507181255952,
     326625242707153437805405281465150497418605074624614708160829052937679007395]
    : Array ℕ)[(i : ℕ)]?.getD 0

/-- The wrap-side coset shifts, production's `Shifts::new` values recorded in
`kimchi/fixtures/linearization_pallas.json`. -/
def wrapShifts : Fin permCols → Fq := fun i =>
  (#[1, 328286983623303317637963920346571898945724874896624808297627776768640590563,
     220790353665890403705559231885806581221301230221265349993193424985261418438,
     211720422259245489258933986578227917398506328781182391541883955346082631533,
     211634429328372259348572816867521795029192573698954618296359582461568682420,
     317476258975906211462498873025720239242336777696786967497139785505242641540,
     99141114743446054294525453467100398765600279346526770105380817318185104545]
    : Array ℕ)[(i : ℕ)]?.getD 0

/-- The two previous-challenge vectors from `base`. -/
def prevChallengesOf {p : ℕ} (get : ℕ → FVar (ZMod p)) (base : ℕ) : List (List (FVar (ZMod p))) :=
  [(List.range 16).map fun i => get (base + i), (List.range 16).map fun i => get (base + 16 + i)]

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
