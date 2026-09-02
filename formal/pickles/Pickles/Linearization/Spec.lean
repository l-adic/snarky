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

* **The feature predicate and the lookup evaluations are PARAMETERS**, following the
  PureScript, where `ifFeature` is a field of `Env` and the eval point carries lookup
  accessors — both specialised at the instantiation site rather than inside the
  environment. The deployed instantiation passes `fun _ => false` and `LookupEvals.zero`,
  which is CLAUDE.md's modelled fragment; pinning them here instead would make the enabled
  case unstateable rather than merely unproved.
* **Out-of-range indices read as zero**, mirroring the interpreter's own defaulting rather
  than ruling them out by typing. Not reachable in the live stream.
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

open Kimchi.Lift Kimchi.Lift.Gate Pickles.Linearization

-- `Env` lives at `Type`, and `Argument.constraints` needs `R` in the same universe as
-- `F`; both carriers of interest (`ZMod p` and `CMvPolynomial n (ZMod p)`) are there.
variable {F : Type} [Field F] {R : Type} [CommRing R] [Algebra F R]

/-! ## The interpreter environment -/

/-- The lookup columns' evaluations. Kimchi's `Evals` has no fields for these — the
modelled fragment excludes lookups — so they enter `toEnv` as a separate record, mirroring
the accessors PureScript's eval point carries (`lookupAggreg`, `lookupSorted`, …). The
deployed instantiation passes zeros, exactly as the PureScript harness does; carrying them
as a PARAMETER rather than pinning them inside `toEnv` is what leaves the door open if the
protocol formalization ever grows lookups. -/
structure LookupEvals (R : Type) where
  /-- Sorted lookup column `i` at a row. -/
  sorted : Nat → CurrOrNext → R
  /-- The lookup aggregation column at a row. -/
  aggreg : CurrOrNext → R
  /-- The lookup table column at a row. -/
  table : CurrOrNext → R
  /-- The runtime lookup table column at a row. -/
  runtimeTable : CurrOrNext → R
  /-- The runtime lookup selector column at a row. -/
  runtimeSelector : CurrOrNext → R
  /-- The selector of a lookup family. -/
  kindIndex : LookupPattern → R

/-- All lookup columns read as zero: the modelled fragment's instantiation. -/
def LookupEvals.zero [Zero R] : LookupEvals R where
  sorted _ _ := 0
  aggreg _ := 0
  table _ := 0
  runtimeTable _ := 0
  runtimeSelector _ := 0
  kindIndex _ := 0

/-- Push a carrier map through the lookup evaluations. -/
def LookupEvals.map {S : Type} (φ : R → S) (lk : LookupEvals R) : LookupEvals S where
  sorted i row := φ (lk.sorted i row)
  aggreg row := φ (lk.aggreg row)
  table row := φ (lk.table row)
  runtimeTable row := φ (lk.runtimeTable row)
  runtimeSelector row := φ (lk.runtimeSelector row)
  kindIndex p := φ (lk.kindIndex p)

/-- Zero is preserved: the modelled fragment's lookup evaluations transport to themselves.
-/
@[simp] theorem LookupEvals.map_zero {S : Type} [Zero R] [Zero S] {φ : R → S} (h0 : φ 0 = 0) :
    LookupEvals.map φ LookupEvals.zero = (LookupEvals.zero : LookupEvals S) := by
  simp [LookupEvals.map, LookupEvals.zero, h0]



open Pickles.Linearization in
/-- The environment the deployed token stream is read in, built from the same atoms
`gateLinearizationAt` takes. See the preamble for the four choices this makes. -/
def Evals.toEnv (endo : F) (mds : Kimchi.Gate.Poseidon.Mds F)
    (α β γ jc van : R) (ulb : Bool → Int → R) (lk : LookupEvals R)
    (feat : FeatureFlag → Bool) (e : Evals R) : Env Id R where
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
    | .lookupSorted i, row => lk.sorted i row
    | .lookupAggreg, row => lk.aggreg row
    | .lookupTable, row => lk.table row
    | .lookupRuntimeTable, row => lk.runtimeTable row
    | .lookupRuntimeSelector, row => lk.runtimeSelector row
    | .lookupKindIndex p, _ => lk.kindIndex p
    | .index _, _ => 0
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
  ifFeature f onTrue onFalse := if feat f then onTrue () else onFalse ()

/-! ## Naturality

`toEnv` commutes with an `F`-algebra homomorphism, which is what lets the interpreter be
run once over a polynomial algebra and read back at the field. The gate parameters are
untouched — `φ` meets them only through `commutes`, since they enter via `algebraMap`. -/

open Pickles.Linearization in
/-- Mapping the evaluations and building the environment is building the environment and
transporting it along `φ`. -/
theorem toEnv_compatible {S : Type} [CommRing S] [Algebra F S] (φ : R →ₐ[F] S)
    (endo : F) (mds : Kimchi.Gate.Poseidon.Mds F) (α β γ jc van : R)
    (ulb : Bool → Int → R) (lk : LookupEvals R) (feat : FeatureFlag → Bool) (e : Evals R) :
    Compatible φ (e.toEnv endo mds α β γ jc van ulb lk feat)
      ((e.map φ).toEnv endo mds (φ α) (φ β) (φ γ) (φ jc) (φ van)
        (fun zk off => φ (ulb zk off)) (lk.map φ) feat) where
  add a b := map_add φ a b
  sub a b := map_sub φ a b
  mul a b := map_mul φ a b
  pow v n := map_pow φ v n
  var c r := by
    cases c with
    | index g => cases g <;> cases r <;> simp [Evals.toEnv, Evals.map]
    | witness i => cases r <;> simp [Evals.toEnv, Evals.map, apply_dite (f := φ), map_zero]
    | coefficient i =>
      cases r <;> simp [Evals.toEnv, Evals.map, apply_dite (f := φ), map_zero]
    | _ => cases r <;> simp [Evals.toEnv, LookupEvals.map]
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
  ifFeature f t₁ n₁ t₂ n₂ ht hn := by
    simp only [Evals.toEnv]
    split <;> assumption

end Kimchi.Protocol.Linearization
