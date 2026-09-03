import Snarky.DSL.Field
import Kimchi.Protocol.Linearization
import Kimchi.Columns

set_option mvcgen.warning false

/-!
# The permutation scalar in circuit

Port of the PureScript `Pickles.PlonkChecks.Permutation.permScalarCircuit`: the scalar of
the permutation commitment in the linearization,
`−z(ζω) · β · α²¹ · zkpm(ζ) · ∏_{i<6} (γ + β·σᵢ + wᵢ)`, as the verifiers recompute it for the
`perm_correct` check against the deferred claim.

## Main definitions

* `permScalarCircuit`: the `mul` chain in OCaml's order, `α²¹` supplied by the caller.

## Main results

* `permScalarCircuit_spec`: the output reads as `Kimchi.Protocol.Linearization.permScalar`.
-/

namespace Pickles

open Std.Do Snarky Kimchi.Protocol.Linearization
open scoped Kimchi

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]

/-- `−(z(ζω) · β · α²¹ · zkp · ∏_{i<6} (γ + β·σᵢ + wᵢ))` over the six evaluated σ columns and
the first six witness columns. -/
def permScalarCircuit (w s : Fin sigmaRows → FVar F)
    (zOmega beta gamma zkPoly alphaPow21 : FVar F) : CircuitM F c (FVar F) := do
  let t ← mul zOmega beta
  let t ← mul t alphaPow21
  let acc ← mul t zkPoly
  let bs ← mul beta (s 0)
  let acc ← mul acc (CVar.add_ (CVar.add_ gamma bs) (w 0))
  let bs ← mul beta (s 1)
  let acc ← mul acc (CVar.add_ (CVar.add_ gamma bs) (w 1))
  let bs ← mul beta (s 2)
  let acc ← mul acc (CVar.add_ (CVar.add_ gamma bs) (w 2))
  let bs ← mul beta (s 3)
  let acc ← mul acc (CVar.add_ (CVar.add_ gamma bs) (w 3))
  let bs ← mul beta (s 4)
  let acc ← mul acc (CVar.add_ (CVar.add_ gamma bs) (w 4))
  let bs ← mul beta (s 5)
  let acc ← mul acc (CVar.add_ (CVar.add_ gamma bs) (w 5))
  pure (CVar.negate_ acc)

/-- Under any valuation satisfying the emitted constraints, with `wᵢ`, `σᵢ` and `z(ζω)`
reading as the evaluations of `e`, `β`, `γ` as themselves, `zkPoly` as `zkp` and
`alphaPow21` as `α²¹`, the output reads as
`−(z(ζω) · β · α²¹ · zkp · ∏_{i<6} (γ + β·σᵢ + wᵢ))`, which is `permScalar β γ α zkp e`. -/
theorem permScalarCircuit_spec [ConstraintHolds F c] [LawfulBasicSystem F c] {V : Valuation F}
    (w s : Fin sigmaRows → FVar F) (zOmega beta gamma zkPoly alphaPow21 : FVar F)
    (e : Evals F) (α zkp : F)
    (hw : ∀ i, (w i).val V = e.w (Kimchi.sigmaCol i)) (hs : ∀ i, (s i).val V = e.s i)
    (hz : zOmega.val V = e.zOmega) (hzk : zkPoly.val V = zkp)
    (ha : alphaPow21.val V = α ^ 21) :
    ⦃⌜True⌝⦄ permScalarCircuit (c := Builder V c) w s zOmega beta gamma zkPoly alphaPow21
    ⦃⇓ a _ => ⌜a.val V = permScalar (beta.val V) (gamma.val V) α zkp e⌝⦄ := by
  simp only [permScalarCircuit]
  mvcgen
  simp only [CVar.val_negate_, CVar.val_add_, permScalar, Fin.prod_univ_six, *]
  congr 1
  ac_rfl

end Pickles
