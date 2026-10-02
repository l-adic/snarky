import Pickles.Statement
import Pickles.Verify
import Pickles.FinalizeOtherProof
import KimchiFixture.Cache

/-!
# Proofs read off the proof cache

A cached proof's records as the circuits take them: its public input as the wrap or step
statement it packs (`PicklesFixture.wrapStatementOf`, `PicklesFixture.stepStatementOf`), its
commitments and opening as cells (`PicklesFixture.ivpProofOf`), its old accumulators' points
(`PicklesFixture.sgOldOf`) and its evaluations (`PicklesFixture.chunkedEvalsOf`). A wrap
proof's statement lives in the wrap field and a step proof's in the step field;
`PicklesFixture.toStep` and `PicklesFixture.toWrap` carry a cell across by value.
-/

namespace PicklesFixture

open Lean Snarky Snarky.Kimchi Kimchi Kimchi.Fixture Bulletproof CompElliptic.Fields.Pasta
open scoped Kimchi

/-- Wrap proofs: Pallas commitments, statement cells in the wrap field. -/
abbrev CW := IpaPallas.curve
/-- Step proofs: Vesta commitments, statement cells in the step field. -/
abbrev CS := IpaVesta.curve

/-- A wrap-field cell as the step-field value it carries: the shifted scalars are `Type1`
representatives, the challenges are 128-bit, the digests are full elements — all
transported by value. -/
def toStep (x : CW.ScalarField) : Fp := (x.val : Fp)

/-- A step-field cell as the wrap-field value it carries — a digest, a 128-bit challenge, a
split half or a Type1 register, all transported by value. -/
def toWrap (x : CS.ScalarField) : Fq := (x.val : Fq)

/-- The wrap statement's packed branch data `4·domain_log2 + m₀ + 2·m₁`: `domain_log2` and
the two mask bits in slot order. The mask reads slot `i` as "at least `2 − i` proofs", so
the real accumulators sit in the LAST slots and padding goes in front; a step statement of
`n ≤ 2` slots reads the last `n` bits. -/
def unpackBranchData (bd : ℕ) : ℕ × Vector ℕ 2 := (bd / 4, #v[bd % 2, (bd / 2) % 2])

/-- A finalized proof's evaluations off its checked wire record at `nc` chunks: `ft(ζω)`,
the carried public chunks, the record's chunks. -/
def chunkedEvalsOf (C : Ipa.KimchiCurve) {nc k : ℕ} (cp : Kimchi.Verifier.KimchiProof C nc k) :
    Except String (Pickles.ChunkedEvals nc C.ScalarField) := do
  let pub ← match cp.pubEvals with
    | .carried pe => pure pe
    | .barycentric _ => throw "the proof carries no public evaluations (one-chunk wire form)"
  return ⟨cp.ftEval1, pub, cp.evals⟩

/-- A wrap statement off a wrap proof's public input, carried into `F` by `conv`
(`Pickles.WrapStatement.packed`'s order): `cip, b, ζ^{2^k}, ζⁿ, perm` at 0–4, `β, γ` at 5–6,
`α, ζ, ξ` at 7–9, the three digests at 10–12 (the step proof's sponge digest first), the `k`
round challenges from 13, the packed branch data `4·domain_log2 + m₀ + 2·m₁` last, unpacked
(`unpackBranchData`). -/
def wrapStatementOf {F : Type} [Field F] (conv : Fq → F) (k : ℕ) (c : Array Fq) :
    Except String (Pickles.WrapStatement k F Bool (Type1 F)) := do
  unless 14 + k ≤ c.size do throw s!"wrap public input: {c.size} cells at {k} rounds"
  let g (i : ℕ) : F := conv (c.getD i 0)
  let (domainLog2, mask) := unpackBranchData (c.getD (13 + k) 0).val
  return { proofState :=
             { deferredValues :=
                 { plonk := { alpha := ⟨g 7⟩, beta := ⟨g 5⟩, gamma := ⟨g 6⟩, zeta := ⟨g 8⟩,
                              perm := ⟨g 4⟩, zetaToSrsLength := ⟨g 2⟩, zetaToDomainSize := ⟨g 3⟩ }
                   combinedInnerProduct := ⟨g 0⟩, b := ⟨g 1⟩, xi := ⟨g 9⟩
                   bulletproofChallenges := Vector.ofFn fun j => ⟨g (13 + j)⟩
                   branchData := { domainLog2 := (domainLog2 : F)
                                   proofsVerifiedMask := mask.map (· == 1) } }
               spongeDigestBeforeEvaluations := g 10
               messagesForNextWrapProof := g 11 }
           messagesForNextStepProof := g 12 }

/-- A step statement off a step proof's public input, carried into `F` by `conv`, at `k`
rounds per slot and `n` slots (`Pickles.StepStatement.packed`'s order): per slot the five
split claims `cip, b, ζ^{2^k}, ζⁿ, perm` as `(half, parity)` pairs at 0–9, the digest at 10,
`β, γ` at 11–12, `α, ζ, ξ` at 13–15, the `k` round challenges from 16, `should_finalize`
last; then `messages_for_next_step_proof` and the `n` `messages_for_next_wrap_proof`
digests. -/
def stepStatementOf {F : Type} (conv : Fp → F) (k n : ℕ) (c : Array Fp) :
    Except String (Pickles.StepStatement (Pickles.UnfinalizedProof k F Bool
        (Type2 (SplitField F Bool))) F n) := do
  let slotSize := 17 + k
  unless c.size = n * slotSize + 1 + n do
    throw s!"step public input: {c.size} cells, expected {n * slotSize + 1 + n} at {n} slots \
      of {k} rounds"
  let g (i : ℕ) : F := conv (c.getD i 0)
  let bit (i : ℕ) : Bool := decide (c.getD i 0 = 1)
  let slot (s : ℕ) : Pickles.UnfinalizedProof k F Bool (Type2 (SplitField F Bool)) :=
    let b := s * slotSize
    let split (i : ℕ) : Type2 (SplitField F Bool) := ⟨⟨g (b + 2 * i), bit (b + 2 * i + 1)⟩⟩
    { deferredValues :=
        { plonk := { alpha := ⟨g (b + 13)⟩, beta := ⟨g (b + 11)⟩, gamma := ⟨g (b + 12)⟩,
                     zeta := ⟨g (b + 14)⟩, perm := split 4, zetaToSrsLength := split 2,
                     zetaToDomainSize := split 3 }
          combinedInnerProduct := split 0, b := split 1, xi := ⟨g (b + 15)⟩
          bulletproofChallenges := Vector.ofFn fun j => ⟨g (b + 16 + j)⟩ }
      shouldFinalize := bit (b + 16 + k)
      spongeDigestBeforeEvaluations := g (b + 10) }
  return { proofState := { unfinalizedProofs := Vector.ofFn fun i => slot i
                           messagesForNextStepProof := g (n * slotSize) }
           messagesForNextWrapProof := Vector.ofFn fun i => g (n * slotSize + 1 + i) }

/-- A checked proof's cells for a group half at its `nc` chunks: its commitments as affine
points, the opening with `z₁`, `z₂` through `shift` (the side's shifted register). -/
def ivpProofOf (C : Ipa.KimchiCurve) {k nc : ℕ} {sf : Type} (shift : C.ScalarField → sf)
    (cp : Kimchi.Verifier.KimchiProof C nc k) :
    Except String (Pickles.IvpProof k nc C.BaseField sf) := do
  let pt (P : C.Point) : AffinePoint C.BaseField := ⟨P.x, P.y⟩
  let tComm : Vector (AffinePoint C.BaseField) (quotChunks * nc) ←
    if h : cp.tComm.size = quotChunks * nc then pure ⟨cp.tComm.map pt, by simp [h]⟩
    else throw s!"t_comm: {cp.tComm.size} chunks, expected {quotChunks * nc}"
  return { wComm := cp.wComm.map (·.map pt)
           zComm := cp.zComm.map pt
           tComm
           opening := { lr := cp.opening.lr.map fun q => (pt q.1, pt q.2)
                        z1 := shift cp.opening.z1, z2 := shift cp.opening.z2
                        delta := pt cp.opening.delta, sg := pt cp.opening.sg } }

/-- A checked proof's accumulators' `sg`, as `m` affine points: the proof's own in the LAST
slots (`unpackBranchData`), `pad` in front of them. A proof carries one accumulator per real
predecessor of its rule, which a statement padded to the system's width exceeds — a
heterogeneous system has rules with fewer predecessors than slots — and a padding slot's
keep bit is off, so its point is never absorbed; it only has to be a point. -/
def sgOldOf (C : Ipa.KimchiCurve) {k nc : ℕ} (m : ℕ) (pad : C.Point)
    (cp : Kimchi.Verifier.KimchiProof C nc k) :
    Except String (Vector (AffinePoint C.BaseField) m) :=
  let pt (P : C.Point) : AffinePoint C.BaseField := ⟨P.x, P.y⟩
  let sgs := cp.olds.map fun a => pt a.sg
  if sgs.size ≤ m then
    let all := Array.replicate (m - sgs.size) (pt pad) ++ sgs
    if h : all.size = m then pure ⟨all, h⟩ else throw s!"accumulators: {sgs.size} of {m}"
  else throw s!"accumulators: {sgs.size}, more than the {m} slots"

end PicklesFixture
