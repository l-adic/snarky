import Pickles.Linearization.Interpreter
import Kimchi.Protocol.Linearization
import Pickles.Linearization.Map

/-!
# The interpreter's environment, from the verifier's own evaluations

`Kimchi.Protocol.Linearization.gateLinearization` takes exactly the atoms the deployed
token stream reads — `(endo, mds, α, e)` — so the interpreter environment that adjudicates
the stream against it should be BUILT from those, not assembled independently. `toEnv` is
that adapter, and it is the single definition the fixture driver and any reflection proof
both go through.

## What `toEnv` decides

Four choices, none of them forced by the type:

* **Optional features are off.** `ifFeature` always takes the disabled branch. It cannot be
  a parameter: the enabled branches read lookup columns, which this environment sends to
  zero, so they would compute nonsense rather than the feature's real contribution. The
  regime is CLAUDE.md's modelled fragment.
* **Out-of-range indices and lookup columns read as zero**, mirroring the interpreter's own
  defaulting rather than ruling them out by typing. Neither is reachable in the live stream.
* **`literal` casts in `F` and then embeds**, rather than casting straight into `R`. The
  two agree (`algebraMap` is a ring homomorphism, so it commutes with `Nat.cast`), but a
  cast into `R` is computed by `Nat.unaryCast` at a polynomial algebra — one `+ 1` per
  unit — and the dumped literals run to 255 bits. Casting in the field first keeps the
  reflection finite. Soundness rests on the literals being canonical residues of `F`'s
  characteristic, which is why a reflection must work over `ZMod p` and not `ℤ`.
* **`β`, `γ`, `jointCombiner` and the ZK-vanishing evaluation are parameters**, though the
  constant term reads none of them. Taking them lets a reflection give each a fresh
  variable and conclude for every value, instead of for one choice. `ulb` cannot get that
  treatment — it is a function, so it is supplied outright; the live stream reaches it zero
  times, both occurrences sitting inside disabled branches.
-/

namespace Kimchi.Protocol.Linearization

open Kimchi.Lift Kimchi.Lift.Gate

-- `Env` lives at `Type`, and `Argument.constraints` needs `R` in the same universe as
-- `F`; both carriers of interest (`ZMod p` and `CMvPolynomial n (ZMod p)`) are there.
variable {F : Type} [Field F] {R : Type} [CommRing R] [Algebra F R]

/-! ## The interpreter environment -/

open Pickles.Linearization in
/-- The environment the deployed token stream is read in, built from the same atoms
`gateLinearizationAt` takes. See the preamble for the four choices this makes. -/
def Evals.toEnv (endo : F) (mds : Kimchi.Gate.Poseidon.Mds F)
    (α β γ jc van : R) (ulb : Bool → Int → R) (e : Evals R) : Env Id R where
  add a b := a + b
  sub a b := a - b
  mul a b := pure (a * b)
  pow v n := pure (v ^ n)
  cell x := x
  var col row := match col, row with
    | .witness i, .curr => if h : i < wCols then e.w ⟨i, h⟩ else 0
    | .witness i, .next => if h : i < wCols then e.wOmega ⟨i, h⟩ else 0
    | .coefficient i, _ => if h : i < coeffCols then e.coeffs ⟨i, h⟩ else 0
    | .index .generic, _ => e.genericSelector
    | .index .poseidon, _ => e.poseidonSelector
    | .index .completeAdd, _ => e.completeAddSelector
    | .index .varBaseMul, _ => e.mulSelector
    | .index .endoMul, _ => e.emulSelector
    | .index .endoMulScalar, _ => e.endoScalarSelector
    | _, _ => 0
  alphaPow n := α ^ n
  mds r c := match r, c with
    | 0, 0 => algebraMap F R mds.m00 | 0, 1 => algebraMap F R mds.m01
    | 0, 2 => algebraMap F R mds.m02 | 1, 0 => algebraMap F R mds.m10
    | 1, 1 => algebraMap F R mds.m11 | 1, 2 => algebraMap F R mds.m12
    | 2, 0 => algebraMap F R mds.m20 | 2, 1 => algebraMap F R mds.m21
    | 2, 2 => algebraMap F R mds.m22 | _, _ => 0
  endoCoefficient := algebraMap F R endo
  literal v := algebraMap F R (v : F)
  vanishesOnZeroKnowledgeAndPreviousRows := van
  unnormalizedLagrangeBasis zk off := pure (ulb zk off)
  jointCombiner := jc
  beta := β
  gamma := γ
  ifFeature _ _ onFalse := onFalse ()

/-! ## Naturality

`toEnv` commutes with an `F`-algebra homomorphism, which is what lets the interpreter be
run once over a polynomial algebra and read back at the field. The gate parameters are
untouched — `φ` meets them only through `commutes`, since they enter via `algebraMap`. -/

open Pickles.Linearization in
/-- Mapping the evaluations and building the environment is building the environment and
transporting it along `φ`. -/
theorem toEnv_compatible {S : Type} [CommRing S] [Algebra F S] (φ : R →ₐ[F] S)
    (endo : F) (mds : Kimchi.Gate.Poseidon.Mds F) (α β γ jc van : R)
    (ulb : Bool → Int → R) (e : Evals R) :
    Compatible φ (e.toEnv endo mds α β γ jc van ulb)
      ((e.map φ).toEnv endo mds (φ α) (φ β) (φ γ) (φ jc) (φ van)
        (fun zk off => φ (ulb zk off))) where
  add a b := map_add φ a b
  sub a b := map_sub φ a b
  mul a b := map_mul φ a b
  pow v n := map_pow φ v n
  var c r := by
    cases c with
    | index g => cases g <;> cases r <;> simp [Evals.toEnv, Evals.map]
    | _ => cases r <;> simp [Evals.toEnv, Evals.map, apply_dite (f := φ), map_zero]
  cell _ := rfl
  alphaPow n := map_pow φ α n
  mds r c := by
    match r, c with
    | 0, 0 | 0, 1 | 0, 2 | 1, 0 | 1, 1 | 1, 2 | 2, 0 | 2, 1 | 2, 2 => exact φ.commutes _
    | _ + 3, _ | _, _ + 3 => simp [Evals.toEnv]
  endoCoefficient := φ.commutes _
  literal v := φ.commutes _
  vanishes := rfl
  ulb _ _ := rfl
  jointCombiner := rfl
  beta := rfl
  gamma := rfl
  ifFeatureLeft _ _ _ := rfl
  ifFeatureRight _ _ _ := rfl

end Kimchi.Protocol.Linearization
