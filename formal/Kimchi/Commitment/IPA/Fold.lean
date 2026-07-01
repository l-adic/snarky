import Mathlib
import Kimchi.Commitment.IPA.Basic

/-!
# The IPA round fold and cross-terms

Implementation-only transcription of one round of the kimchi inner-product
argument (IPA): the per-round fold of the coefficient, evaluation-point, and
generator vectors, together with the cross-commitments `L` and `R`.

Ground truth: `references/ipa.rs`, `open` — the folding loop (l.843–872) and the
cross-commitments `L`/`R` (l.806–825). Cross-checked against
`references/ironwood/` (`foldVec lo hi u := lo + u • hi`).

Everything here is **definitions only** — no soundness or binding statement. The
group `G` is an abstract `F`-module.

The IPA is **asymmetric** (kimchi/proof-systems, not the Halo 2019 paper):

* `a' = aLo + u⁻¹ · aHi`  (`foldA`)
* `b' = bLo + u  · bHi`  (`foldB`)
* `g' = gLo + u  · gHi`  (`foldG`)

The `+`/`•` on `Fin m → _` are the Pi-type pointwise operations.
-/

namespace Kimchi.Commitment.IPA

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Coefficient fold `a'` (`def:ipa_foldA`). One IPA round folds the length-`2m`
coefficient vector, already split into low/high halves `aLo`/`aHi`, into a
length-`m` vector `aLo + u⁻¹ · aHi` (pointwise). The low coefficient is `1`, the
high is `u⁻¹` — the asymmetric kimchi form, **not** `aHi·u⁻¹ + aLo·u`.
Source: ipa.rs `open` (l.843–854), `a = a_lo + u_inv * a_hi`. -/
def foldA {m : ℕ} (aLo aHi : Fin m → F) (u : F) : Fin m → F :=
  aLo + u⁻¹ • aHi

/-- Evaluation-point fold `b'` (`def:ipa_foldB`). Folds the evaluation-point
vector into `bLo + u · bHi` (pointwise); the challenge multiplies the *high*
half with coefficient `u` (versus `u⁻¹` for `foldA`).
Source: ipa.rs `open` (l.859–869), `b = b_lo + u * b_hi`. -/
def foldB {m : ℕ} (bLo bHi : Fin m → F) (u : F) : Fin m → F :=
  bLo + u • bHi

/-- Generator fold `g'` (`def:ipa_foldG`). Folds the generator bases into
`gLo + u · gHi` (pointwise). `combine_one_endo` is the endomorphism-optimised
MSM computing exactly this; we transcribe the scalar semantics.
Source: ipa.rs `open` (l.872), `g = combine_one_endo(g_lo, g_hi, u)`. -/
def foldG {m : ℕ} (gLo gHi : Fin m → G) (u : F) : Fin m → G :=
  gLo + u • gHi

/-- Left cross-term `L` (`def:ipa_crossL`). The Pedersen commitment over bases
`[gLo, h, U]` to scalars `[aHi, randL, ⟪aHi, bLo⟫]`:
`L = ⟪aHi, gLo⟫ + randL · σ.h + ⟪aHi, bLo⟫ · σ.U`.
Source: ipa.rs `open` (l.806–815). -/
def crossL {m : ℕ} (σ : SRS G) (aHi : Fin m → F) (gLo : Fin m → G)
    (bLo : Fin m → F) (randL : F) : G :=
  commitGen gLo aHi + randL • σ.h + innerProduct aHi bLo • σ.U

/-- Right cross-term `R` (`def:ipa_crossR`). The Pedersen commitment over bases
`[gHi, h, U]` to scalars `[aLo, randR, ⟪aLo, bHi⟫]`:
`R = ⟪aLo, gHi⟫ + randR · σ.h + ⟪aLo, bHi⟫ · σ.U`. The blinders `randL`/`randR`
are kept, modelling the ZK hiding faithfully.
Source: ipa.rs `open` (l.817–825). -/
def crossR {m : ℕ} (σ : SRS G) (aLo : Fin m → F) (gHi : Fin m → G)
    (bHi : Fin m → F) (randR : F) : G :=
  commitGen gHi aLo + randR • σ.h + innerProduct aLo bHi • σ.U

end Kimchi.Commitment.IPA
