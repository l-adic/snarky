import Snarky.Circuit.DSL.Field
import Kimchi.Gate.Semantics.EndoMul
import Snarky.Circuit.DSL.Assert
import Snarky.Circuit.DSL.Bits
import Snarky.Kimchi.Semantics
import Snarky.Kimchi.Circuit.Utils
import Snarky.Kimchi.Circuit.AddComplete

/-!
# The EndoMul gadget

Port of `Snarky.Circuit.Kimchi.EndoMul`
(packages/snarky-kimchi/src/Snarky/Circuit/Kimchi/EndoMul.purs): the
endomorphism-optimized scalar multiplication. `endoMul` witnesses the scalar's
`4·rounds` bits MSB-first in ONE bulk `exists` — four per GLV round, plain field
`0`/`1` values (the gate's own booleanity rows cover them) — builds the initial
accumulator `[2](g + φ(g))` from a sealed `β·x` and two `addFast`s, threads
`(acc, nAcc)` through `mapAccumM` with one eight-field witness per round, pins the
scalar register to the scalar, and emits the `endoMul` constraint.

Name map: PS `endo` becomes `endoMul`, the gate's own name — `endo` names the
coefficient family here (`endoBase`, `Pasta.pallasEndo`); the coefficient
parameter is `eb` after the PS binding. `endoInv` is a higher-level consumer
(cross-field scalar-multiplication witnesses over an on-curve checked point) and
is not ported, like `EndoScalar.expandToEndoScalar`.

Deviations from the PS original (per `formal/docs/snarky-kimchi-alignment.md`):
- PS's type-level `SizedF k` sizing renders as the explicit `rounds` parameter with
  `4 · rounds` bits, and the bit reads go through `[ToNat F]`.
- PS batches the whole witness chain through `mkWitnessTable`/`computeEndoChain`
  (Montgomery-trick advice; its own comment: the emitted circuit is untouched).
  The port computes each round's witness sequentially from the threaded variables
  via the gate's own `Kimchi.Gate.EndoMul.build` — the same field values, and the
  same eight-variable allocation per round in the PS record's alphabetical order
  `(inv, nAccNext, r, s, s1, s3)`.
- PS reads the endo coefficient off the ambient `HasEndo` class; the deep embedding
  passes it as the `eb` parameter (the Poseidon parameter-data deviation).
-/

namespace Snarky.Kimchi

open Snarky

variable {F c : Type}

/-- The scalar's `4·rounds` bits MSB-first as field values, four per row (PS's
bulk bit witness: `toBits` reversed). -/
private def bitsWit [Field F] [ToNat F] (rounds : ℕ) (scalar : FVar F) :
    AsProver F (Vector (Vector F 4) rounds) := do
  let v ← AsProver.readCVar scalar
  let n := ToNat.toNat v
  pure (Vector.ofFn fun r => Vector.ofFn fun j =>
    if n.testBit (4 * rounds - 1 - (4 * r.1 + j.1)) then 1 else 0)

/-- One GLV round's witness: read the base, the threaded accumulator and register,
and the four window bits, and build the gate's canonical row
(`Kimchi.Gate.EndoMul.build` — two `stepWindow` double-adds, the scalar recoding,
the distinct-point inverse). Returned in the PS record's alphabetical allocation
order `(inv, nAccNext, r.x, r.y, s.x, s.y, s1, s3)`. -/
private def rowWit [Field F] [DecidableEq F] (eb : F) (t : AffinePoint (FVar F))
    (bs : Vector (FVar F) 4) (st : AffinePoint (FVar F) × FVar F) :
    AsProver F (F × F × F × F × F × F × F × F) := do
  let xt ← AsProver.readCVar t.x
  let yt ← AsProver.readCVar t.y
  let xp ← AsProver.readCVar st.1.x
  let yp ← AsProver.readCVar st.1.y
  let n ← AsProver.readCVar st.2
  let b1 ← AsProver.readCVar bs[0]
  let b2 ← AsProver.readCVar bs[1]
  let b3 ← AsProver.readCVar bs[2]
  let b4 ← AsProver.readCVar bs[3]
  let w := Kimchi.Gate.EndoMul.build eb xt yt xp yp n b1 b2 b3 b4
  pure (w.inv, w.nPrime, w.xR, w.yR, w.xS, w.yS, w.s1, w.s3)

/-- The endomorphism-optimized scalar multiplication (PS `endo`; OCaml
`Pickles.Step_main_inputs.Ops.endo`): witness the MSB-first bits, seal `β·x` and
build `acc = [2](g + φ(g))` with two `addFast`s, run the `rounds` window rounds
threading `(acc, nAcc)`, pin the scalar fold, emit one `endoMul` constraint, and
return the final accumulator. -/
def endoMul [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]
    (eb : F) (rounds : ℕ) (g : AffinePoint (FVar F)) (scalar : FVar F) :
    CircuitM F c (AffinePoint (FVar F)) := do
  let bits ← witness (val := Vector (Vector F 4) rounds) (bitsWit rounds scalar)
  let phix ← sealVar (CVar.scale_ eb g.x)
  let p1 ← addFast .checkFinite g ⟨phix, g.y⟩
  let p2 ← addFast .checkFinite p1.p p1.p
  let (state, fin) ← mapAccumM
    (fun (st : AffinePoint (FVar F) × FVar F) (bs : Vector (FVar F) 4) => do
      let w ← witness (val := F × F × F × F × F × F × F × F) (rowWit eb g bs st)
      let s : AffinePoint (FVar F) := ⟨w.2.2.2.2.1, w.2.2.2.2.2.1⟩
      pure (({ t := g, p := st.1, r := ⟨w.2.2.1, w.2.2.2.1⟩, s,
               s1 := w.2.2.2.2.2.2.1, s3 := w.2.2.2.2.2.2.2,
               nAcc := st.2, nAccNext := w.2.1,
               bit0 := bs[0], bit1 := bs[1], bit2 := bs[2], bit3 := bs[3],
               inv := w.1 } : EndoMulRound F),
            (s, w.2.1)))
    (p2.p, .const 0) bits.toList
  assertEqual fin.2 scalar
  addConstraint (KimchiSystem.endoMul { state, s := fin.1, nAcc := fin.2, endo := eb })
  pure fin.1

end Snarky.Kimchi
