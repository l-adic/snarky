import Pickles.FinalizeOtherProof
import Pickles.Domain

set_option mvcgen.warning false

/-!
# The wrap circuit's finalize block

Transcribes the finalize block of `wrap_main.ml`. Each previous proof's slot carries a wrap
domain index as advice. The block pins each index to the domain the active branch was compiled
for, selects each slot's domain from its index, then finalizes each slot's deferred values
against that domain and asserts the slot finalized or was not to be.

## Main definitions

* `pinWrapDomainIndex`: one slot's pin against the branches' compile-time indices.
* `wrapFinalizePrevProofs`: the pins, left to right; the domains, right to left; the finalize
  bodies with their assertions, left to right.

## Implementation notes

A slot whose predecessor is side-loaded in some branch has no compile-time domain there. That
branch's term is zero on both sides of the pin, so while it is active the index is
unconstrained.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Pickles.Linearization

variable {F c : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F c] [KimchiSystem F c]

/-- One slot's pin. `atSlot` holds each branch's compile-time domain index for the slot, `none`
for a side-loaded predecessor. When every branch knows it, the index equals the one-hot choice;
otherwise the known branches' bits scale the index to that choice. -/
def pinWrapDomainIndex (whichBranch : List (BoolVar F)) (atSlot : List (Option ℕ))
    (index : FVar F) : CircuitM F c PUnit :=
  match atSlot.allSome with
  | some ks => do
    let chosen ← Pseudo.choose whichBranch ks fun j => .const (j : F)
    assertEqual index chosen
  | none => do
    let chosen ← Pseudo.choose whichBranch atSlot fun k => .const (k.elim 0 fun j => (j : F))
    let knownBranch ← Pseudo.choose whichBranch atSlot fun k => .const (k.elim 0 fun _ => 1)
    let pinned ← mul knownBranch index
    assertEqual pinned chosen

/-- The wrap circuit's finalize block over its slots. `pins` holds each slot's column of
compile-time domain indices over the branches, and `log2s` the possible wrap domains, with
generators `gen`. Returns each slot's finalize output. -/
def wrapFinalizePrevProofs {k nc : ℕ} (P : FopParams F) (gen : ℕ → F) (log2s : List ℕ)
    (whichBranch : List (BoolVar F)) (pins : List (List (Option ℕ))) (indices : List (FVar F))
    (us : List (UnfinalizedProof k (FVar F) (BoolVar F) (Type2 (FVar F))))
    (ws : List (ChunkedEvals nc (FVar F))) (prevs : List (List (List (FVar F)))) :
    CircuitM F c (List (FopOutput F)) := do
  (indices.zip pins).forM fun (index, atSlot) => pinWrapDomainIndex whichBranch atSlot index
  let rev ← indices.reverse.mapM fun index => do
    let which ← oneHotVector log2s.length index
    toDomain gen which log2s
  (rev.reverse.zip (us.zip (ws.zip prevs))).mapM fun (d, u, w, prev) => do
    let o ← finalizeOtherProofWrap P d.generator d.vanishingPolynomial u w prev
    assertAny [o.finalized, Snarky.not u.shouldFinalize]
    pure o

end Pickles
