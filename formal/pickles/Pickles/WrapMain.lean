import Pickles.WrapFinalize
import Pickles.VkComms

set_option mvcgen.warning false

/-!
# The wrap circuit

Transcribes `wrap_main.ml`. The wrap circuit verifies one step proof, chosen among the tag's
branches, and finalizes the previous wrap proofs that step proof verified.

## Main definitions

* `onesVector`: the slot mask, `true` up to the branch's first unused slot.
* `chooseKey`: the active branch's step key, the branches' keys summed under the one-hot bits
  and sealed.
-/

namespace Pickles

open Snarky Snarky.Kimchi

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]

/-- The slot mask over `mpv` slots: slot `i` is set while no slot up to `i` equals
`firstZero`, one `equals` and one `and` per slot, in slot order. -/
def onesVector (firstZero : FVar F) (mpv : ℕ) : CircuitM F c (List (BoolVar F)) :=
  go true_ 0 mpv
where
  /-- The slots from `i` on, `value` the mask so far. -/
  go (value : BoolVar F) (i : ℕ) : ℕ → CircuitM F c (List (BoolVar F))
    | 0 => pure []
    | m + 1 => do
      let eq ← equals firstZero (.const (i : F))
      let v ← Snarky.and value (Snarky.not eq)
      let rest ← go v (i + 1) m
      pure (v :: rest)

section ChooseKey

variable {nc : ℕ}

/-- A point's coordinates multiplied by a bit, `y` before `x`: one branch's term of the
coordinate-wise selection. -/
private def scalePt (b : FVar F) (p : AffinePoint (FVar F)) :
    CircuitM F c (AffinePoint (FVar F)) := do
  let y ← mul b p.y
  let x ← mul b p.x
  pure ⟨x, y⟩

/-- `f` over a vector's entries, last to first, the results in entry order. -/
private def vecMapMRev {α β : Type} {n : ℕ} (f : α → CircuitM F c β) (v : Vector α n) :
    CircuitM F c (Vector β n) := do
  let rev ← v.reverse.mapM f
  pure rev.reverse

/-- `f` over a key's commitments: the selectors from endo-mul-scalar back to generic, then the
coefficients and `σ` each last to first; each commitment's chunks first to last. -/
private def VkComms.mapMRev (f : AffinePoint (FVar F) → CircuitM F c (AffinePoint (FVar F)))
    (k : VkComms nc (AffinePoint (FVar F))) : CircuitM F c (VkComms nc (AffinePoint (FVar F))) := do
  let endomulScalarComm ← k.endomulScalarComm.mapM f
  let emulComm ← k.emulComm.mapM f
  let mulComm ← k.mulComm.mapM f
  let completeAddComm ← k.completeAddComm.mapM f
  let poseidonComm ← k.poseidonComm.mapM f
  let genericComm ← k.genericComm.mapM f
  let coefficientsComm ← vecMapMRev (·.mapM f) k.coefficientsComm
  let sigmaComm ← vecMapMRev (·.mapM f) k.sigmaComm
  pure ⟨sigmaComm, coefficientsComm, genericComm, poseidonComm, completeAddComm, mulComm,
    emulComm, endomulScalarComm⟩

/-- Two keys' commitments added point by point. -/
private def VkComms.add (a b : VkComms nc (AffinePoint (FVar F))) :
    VkComms nc (AffinePoint (FVar F)) :=
  let pt (p q : AffinePoint (FVar F)) : AffinePoint (FVar F) :=
    ⟨CVar.add_ p.x q.x, CVar.add_ p.y q.y⟩
  let ch (u v : Vector (AffinePoint (FVar F)) nc) := Vector.zipWith pt u v
  ⟨Vector.zipWith ch a.sigmaComm b.sigmaComm,
    Vector.zipWith ch a.coefficientsComm b.coefficientsComm, ch a.genericComm b.genericComm,
    ch a.poseidonComm b.poseidonComm, ch a.completeAddComm b.completeAddComm,
    ch a.mulComm b.mulComm, ch a.emulComm b.emulComm, ch a.endomulScalarComm b.endomulScalarComm⟩

/-- The active branch's key, selected coordinate by coordinate: each branch's commitments
multiplied by its bit, branches last to first, the products summed and each sum sealed. With
one-hot bits, every inactive branch contributes zero to each coordinate. -/
def chooseKey {branches : ℕ} (bits : Vector (BoolVar F) (branches + 1))
    (keys : Vector (VkComms nc (AffinePoint (FVar F))) (branches + 1)) :
    CircuitM F c (VkComms nc (AffinePoint (FVar F))) := do
  let scaled ← vecMapMRev (fun (e : BoolVar F × VkComms nc (AffinePoint (FVar F))) =>
    VkComms.mapMRev (scalePt (↑e.1 : FVar F)) e.2) (bits.zip keys)
  let sum := scaled.tail.toList.foldl VkComms.add scaled.head
  VkComms.mapMRev sealPoint sum

end ChooseKey

end Pickles
