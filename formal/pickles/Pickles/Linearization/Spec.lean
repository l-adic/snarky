import Pickles.Linearization.Interpreter
import Kimchi.Protocol.Linearization

/-!
# The interpreter's environment, from the verifier's own evaluations

`Kimchi.Protocol.Linearization.gateLinearization` takes exactly the atoms the deployed
token stream reads, `(endo, mds, α, e)`, so the interpreter environment that adjudicates
the stream against it is built from those.

## Main definitions

* `LookupEvals`: the lookup columns' evaluations, which kimchi's `Evals` does not carry.
* `Evals.toEnv`: the pure interpreter environment at an evaluation record, over any
  `F`-algebra `R`, with the α-table, the Lagrange basis and the feature predicate as
  parameters.

## Implementation notes

The feature predicate, the lookup evaluations, the challenges `β`, `γ`, the joint combiner
and the vanishing evaluation are parameters rather than pinned, following the PureScript;
the deployed instantiation passes `fun _ => false`, `LookupEvals.zero` and the recorded
values. Leaving them free lets a reflection give each a fresh variable and conclude for
every value.

Out-of-range column indices read as zero, mirroring the interpreter's own defaulting.

`literal` casts in `F` and then embeds into `R` rather than casting into `R` directly: at a
polynomial algebra a `Nat` cast is computed by `Nat.unaryCast`, one `+ 1` per unit, and the
dumped literals run to 255 bits. This is why a reflection must work over `ZMod p` and not
`ℤ`: the literals are canonical residues of `F`'s characteristic.
-/

namespace Kimchi.Protocol.Linearization

open Kimchi.Lift Kimchi.Lift.Gate Pickles.Linearization

-- `Env` lives at `Type`, and `Argument.constraints` needs `R` in the same universe as
-- `F`; both carriers of interest (`ZMod p` and `CMvPolynomial n (ZMod p)`) are there.
variable {F : Type} [Field F] {R : Type} [CommRing R] [Algebra F R]

/-! ## The interpreter environment -/

/-- The lookup columns' evaluations, which kimchi's `Evals` has no fields for. The deployed
instantiation passes `LookupEvals.zero`. -/
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

/-- All lookup columns read as zero. -/
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

omit [CommRing R] in
/-- `LookupEvals.zero` transports to itself along a zero-preserving map. -/
@[simp] theorem LookupEvals.map_zero {S : Type} [Zero R] [Zero S] {φ : R → S} (h0 : φ 0 = 0) :
    LookupEvals.map φ LookupEvals.zero = (LookupEvals.zero : LookupEvals S) := by
  simp [LookupEvals.map, LookupEvals.zero, h0]



open Pickles.Linearization in
/-- The pure interpreter environment at the evaluations `e`, over an `F`-algebra `R`. The
α-table `alphaPow`, the Lagrange basis `ulb` and the feature predicate `feat` are
parameters; the reflection instantiates the table at `(α ^ ·)`. -/
def Evals.toEnv (endo : F) (mds : Kimchi.Gate.Poseidon.Mds F) (alphaPow : Nat → R)
    (β γ jc van : R) (ulb : Bool → Int → R) (lk : LookupEvals R)
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
  alphaPow n := alphaPow n
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

section projections

open Pickles.Linearization

variable (endo : F) (mds : Kimchi.Gate.Poseidon.Mds F) (alphaPow : Nat → R) (β γ jc van : R)
  (ulb : Bool → Int → R) (lk : LookupEvals R) (feat : FeatureFlag → Bool) (e : Evals R)

@[simp] theorem Evals.toEnv_add (a b : R) :
    (e.toEnv endo mds alphaPow β γ jc van ulb lk feat).add a b = a + b := rfl

@[simp] theorem Evals.toEnv_sub (a b : R) :
    (e.toEnv endo mds alphaPow β γ jc van ulb lk feat).sub a b = a - b := rfl

@[simp] theorem Evals.toEnv_mul (a b : R) :
    (e.toEnv endo mds alphaPow β γ jc van ulb lk feat).mul a b = pure (a * b) := rfl

@[simp] theorem Evals.toEnv_pow (v : R) (n : Nat) :
    (e.toEnv endo mds alphaPow β γ jc van ulb lk feat).pow v n = pure (v ^ n) := rfl

@[simp] theorem Evals.toEnv_cell (x : R) :
    (e.toEnv endo mds alphaPow β γ jc van ulb lk feat).cell x = x := rfl

@[simp] theorem Evals.toEnv_alphaPow (n : Nat) :
    (e.toEnv endo mds alphaPow β γ jc van ulb lk feat).alphaPow n = alphaPow n := rfl

@[simp] theorem Evals.toEnv_endoCoefficient :
    (e.toEnv endo mds alphaPow β γ jc van ulb lk feat).endoCoefficient = algebraMap F R endo := rfl

@[simp] theorem Evals.toEnv_literal (v : Nat) :
    (e.toEnv endo mds alphaPow β γ jc van ulb lk feat).literal v = algebraMap F R (v : F) := rfl

@[simp] theorem Evals.toEnv_vanishes :
    (e.toEnv endo mds alphaPow β γ jc van ulb lk feat).vanishesOnZeroKnowledgeAndPreviousRows
      = van := rfl

@[simp] theorem Evals.toEnv_unnormalizedLagrangeBasis (zk : Bool) (off : Int) :
    (e.toEnv endo mds alphaPow β γ jc van ulb lk feat).unnormalizedLagrangeBasis zk off
      = pure (ulb zk off) := rfl

@[simp] theorem Evals.toEnv_jointCombiner :
    (e.toEnv endo mds alphaPow β γ jc van ulb lk feat).jointCombiner = jc := rfl

@[simp] theorem Evals.toEnv_beta :
    (e.toEnv endo mds alphaPow β γ jc van ulb lk feat).beta = β := rfl

@[simp] theorem Evals.toEnv_gamma :
    (e.toEnv endo mds alphaPow β γ jc van ulb lk feat).gamma = γ := rfl

@[simp] theorem Evals.toEnv_ifFeature (f : FeatureFlag) (t n : Unit → Id R) :
    (e.toEnv endo mds alphaPow β γ jc van ulb lk feat).ifFeature f t n
      = if feat f then t () else n () := rfl

open Pickles.Linearization in
/-- Two `toEnv` environments differing only in the α-table and the Lagrange basis read
position `i` alike when the tables agree at the exponent read there, if any, and the
position does not read the Lagrange basis. -/
theorem Evals.toEnv_agreeAt (alphaPow' : Nat → R) (ulb' : Bool → Int → R)
    (toks : Array PolishToken) (i : Nat)
    (hα : ∀ n, alphaExponentAt toks i = some n → alphaPow n = alphaPow' n)
    (hulb : noUlbAt toks i = true) :
    (e.toEnv endo mds alphaPow β γ jc van ulb lk feat).agreeAt
      (e.toEnv endo mds alphaPow' β γ jc van ulb' lk feat) toks i := by
  simp only [Env.agreeAt, alphaExponentAt, noUlbAt] at hα hulb ⊢
  cases h : toks[i]? with
  | none => trivial
  | some t =>
    simp only [h] at hα hulb ⊢
    cases t with
    | challenge c =>
      cases c with
      | alpha =>
        cases h' : toks[i + 1]? with
        | some u =>
          cases u with
          | pow n => simp only [h'] at hα ⊢; exact hα n rfl
          | _ => simp only [h'] at hα ⊢; exact hα 1 rfl
        | none => simp only [h'] at hα ⊢; exact hα 1 rfl
      | _ => simp [evalChallenge]
    | unnormalizedLagrangeBasis zk off => simp at hulb
    | constant c => cases c <;> simp [evalConstant, Evals.toEnv]
    | _ => first | trivial | simp [Evals.toEnv]

end projections

end Kimchi.Protocol.Linearization
