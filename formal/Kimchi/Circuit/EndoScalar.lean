import Kimchi.Gate.EndoScalar

/-!
# The `EndoScalar` circuit: the effective scalar `a·λ + b`

Composition of `Kimchi.Gate.EndoScalar` rows into the full endo-scalar
decomposition. A challenge is processed 8 crumbs at a time, each row threading the
`(a,b,n)` accumulators; the result is the effective scalar `a·λ + b` and the raw
register `n`, which the wrapper asserts equals the input challenge.

Because each row is a `List.foldl` over its crumbs, chaining rows is just folding
over the concatenated crumb list (`List.foldl_append`) — the multi-row layout
adds nothing to the math, so the full-challenge (multi-row) spec is deferred until
a consumer (EndoMul) needs it.

## Main results

* `gate_toField` — a satisfying row from the canonical init `(a,b,n) = (2,2,0)`
  outputs the effective scalar `toField crumbs λ` and the register
  `nReconstruct crumbs`.
* `endoScalar_spec` — with the wrapper's `n = challenge`, that register IS the
  challenge: the gate computes the endo-decomposition of the challenge.
-/

namespace Kimchi.Circuit.EndoScalar

open Kimchi.Gate.EndoScalar

variable {F : Type*} [Field F]

/-- The `a`-accumulator of the Algorithm-2 decomposition (`a := 2a + cPoly x`),
    from the canonical init `2`. -/
def decomposeA (crumbs : List F) : F := crumbs.foldl (fun a x => 2 * a + cPoly x) 2

/-- The `b`-accumulator (`b := 2b + dPoly x`), from init `2`. -/
def decomposeB (crumbs : List F) : F := crumbs.foldl (fun b x => 2 * b + dPoly x) 2

/-- The raw challenge reconstructed from its base-4 crumbs (`n := 4n + x`), the
    gate's `n` register. -/
def nReconstruct (crumbs : List F) : F := crumbs.foldl (fun n x => 4 * n + x) 0

/-- The effective scalar the gate outputs: `a·λ + b` (`λ` the endomorphism
    eigenvalue). This is the pure `to_field` of the challenge. -/
def toField (crumbs : List F) (lam : F) : F :=
  decomposeA crumbs * lam + decomposeB crumbs

/-- A satisfying `EndoScalar` row, started from the canonical init `(2,2,0)`,
    outputs the effective scalar `toField crumbs λ` and reconstructs the register
    `nReconstruct crumbs`. (Definitional once the init is fixed — `Holds`'s folds
    are exactly `decomposeA`/`decomposeB`/`nReconstruct`.) -/
theorem gate_toField (lam : F) (w : Witness F) (h : Holds w)
    (ha0 : w.a0 = 2) (hb0 : w.b0 = 2) (hn0 : w.n0 = 0) :
    w.a8 * lam + w.b8 = toField w.crumbs lam ∧ w.n8 = nReconstruct w.crumbs := by
  obtain ⟨hn, ha, hb, _⟩ := h
  rw [ha0] at ha
  rw [hb0] at hb
  rw [hn0] at hn
  exact ⟨by rw [ha, hb, toField, decomposeA, decomposeB], by rw [hn, nReconstruct]⟩

/-- The endo-scalar spec: a satisfying row from the canonical init, whose register
    the wrapper has asserted equal to the input `challenge`, computes the effective
    scalar — and the crumbs are the base-4 decoding of `challenge`. -/
theorem endoScalar_spec (lam challenge : F) (w : Witness F) (h : Holds w)
    (ha0 : w.a0 = 2) (hb0 : w.b0 = 2) (hn0 : w.n0 = 0) (hchal : w.n8 = challenge) :
    w.a8 * lam + w.b8 = toField w.crumbs lam ∧ nReconstruct w.crumbs = challenge := by
  obtain ⟨hout, hn⟩ := gate_toField lam w h ha0 hb0 hn0
  exact ⟨hout, hn ▸ hchal⟩

end Kimchi.Circuit.EndoScalar
