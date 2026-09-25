import Snarky.Kimchi.Circuit.AddComplete
import Snarky.Kimchi.Circuit.Point
import Kimchi.Verifier.Kimchi
import Pickles.Curve
import Pickles.ListLemmas

/-!
# The in-circuit public-input commitment

The port of `packages/pickles/src/Pickles/PublicInputCommit.purs`: the per-chunk MSM that
commits to a proof's public input, at chunk `c` `-(Σ_leaf [scalarₗ]·baseₗ[c]) + h`.

The public input reaches this gadget as a flat list of size-tagged `Leaf`s — a scalar with
its ladder width, or a 1-bit `condAdd`. Packing (a structured statement → this list) is a
separate concern; this module's soundness claim is stated against the list, and lands on
`Kimchi.Verifier.publicCommitment` via `publicCommitment_eq_sum`.

Three gadgets share the leaf interface: `publicInputCommitFull` (the wrap side: corrections
summed in circuit, the fold interleaved), `publicInputCommitSealed` (the same fold over
cells sealed first, for bases masked across branches) and `publicInputCommitKnown` (the step
side, at a known domain: every ladder first, then one fold from the first ladder result, then
the constant correction sum). All read as `-(publicMsm) + h` over the circuit-side point group
(`publicInputCommitFold_reads`, `publicInputCommitKnown_reads`). Whatever the bases read as,
`publicInputCommitFull` and `publicInputCommitSealed` bound every leaf's scalar to its ladder's
width (`Leaf.Bound`; `publicInputCommitFull_bound`, `publicInputCommitSealed_bound`).

The last section is the wire crossing: `xHat_reads_publicCommitment` and
`xHatKnown_reads_publicCommitment` cross those reads to the wire verifier's own
`Kimchi.Verifier.publicCommitment` on the commitment curve, generically over a `PastaShape`
(the point group, the `SWPoint.equivPoint` crossing, and the group's order killing it, so the
integer→scalar reduction is exact — the read carries no slack), instantiated at
`pastaShapeVesta` (Vesta) and `pastaShapePallas` (Pallas).

The tables the gadgets take are a verifier key's data, so the module ends by computing them:
a packed scalar list (`PackedScalar`) against a key's Lagrange points gives the leaves
(`packLeavesOf`) and the tables (`XhatTable.ofKey`, `XhatTable.ofKeyKnown`), bound as the
reads require (`xhatBinding_const`, `bound_ofKeyKnown`), with the known-domain fold's
correction sum a commitment to named coefficients (`corrCoeffs`, `corrSumPt_map_msm`). The
public input of those leaves is the packed scalars reduced into the scalar field
(`PackedScalar.reduced`, `pubOf_zipWith_constLeaf`).
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi CompElliptic.Fields.Pasta

/-- A size-tagged public-input leaf, the flat interface the commitment gadget folds over.
The three scalar cases fix the `scaleFast2'` ladder width `(n, chunks, sDiv2Bits)` and carry
a precomputed shift correction, a constant point per chunk that the read requires to be
`-(2^{5·chunks})·base` — cancelling the ladder's shift so the net is `[scalar]·base`.
`condAdd` is the 1-bit conditional-add path (a boolean statement field or a shifted scalar's
parity), no correction. Each field is chunked (`Vector _ nc`) so the per-chunk accumulator
runs in parallel. -/
inductive Leaf (F : Type) [Field F] (nc : ℕ) where
  /-- A full 255-bit field element: `(n, chunks, sDiv2Bits) = (255, 51, 254)`. -/
  | full (scalar : FVar F) (base correction : Vector (AffinePoint (FVar F)) nc)
  /-- A 128-bit packed value: `(255, 26, 127)`. -/
  | b128 (scalar : FVar F) (base correction : Vector (AffinePoint (FVar F)) nc)
  /-- A 10-bit packed value (branch data): `(255, 2, 9)`. -/
  | b10 (scalar : FVar F) (base correction : Vector (AffinePoint (FVar F)) nc)
  /-- A 1-bit conditional add: `if b then base else 0`. -/
  | condAdd (b : BoolVar F) (base : Vector (AffinePoint (FVar F)) nc)

/-! ## The leaf reads -/

section Reads

variable {F : Type} [Field F] [DecidableEq F] [ToNat F]

/-- **Narrow ladders are in regime.** When the ladder width `L` is small enough that
`3·2^L ≤ order`, `scaleFast2'`'s regime holds for EVERY witness — the subwrap disjunct of
`LadderRegime`. This covers the `b128` (L = 5·26 = 130) and `b10` (L = 5·2 = 10) leaves
against the ~2^254 Pasta order; only the full 255-bit leaf reaches the one-wrap case. -/
private theorem ladderRegime_subwrap {F : Type} [Field F] [DecidableEq F] (d : HasCurve F)
    (L : ℕ) (z : ℤ) (h : 3 * 2 ^ L ≤ d.W.order) : d.LadderRegime L z := by
  unfold HasCurve.LadderRegime
  exact Or.inl h

/-- One leaf's scalar as a `CVar`: the scalar for the three widths, the bit for `condAdd`.
The public-input entry a leaf contributes to the MSM, before the group-order reduction. -/
def Leaf.scalarVar : Leaf F nc → CVar F
  | .full s _ _ => s
  | .b128 s _ _ => s
  | .b10 s _ _ => s
  | .condAdd b _ => (↑b : CVar F)

/-- A cell as a `scaleFast2'` ladder bounds it: `2·z + bb` for a bit `bb` and a half
`0 ≤ z < 2^w`. -/
def CellBound (V : Valuation F) (w : ℕ) (s : FVar F) : Prop :=
  ∃ (z : ℤ) (bb : Bool), 0 ≤ z ∧ z < 2 ^ w ∧ ((2 * z + (if bb then 1 else 0) : ℤ) : F) = s.val V

end Reads

/-! ## The chunked fold -/

section Fold

variable {F S : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F S] [KimchiSystem F S]

/-- `f` at every chunk, in chunk order: the inner loop of every chunked step below. -/
private def chunkwise {β : Type} (f : Fin nc → CircuitM F S β) : CircuitM F S (Vector β nc) :=
  (Vector.ofFn id).mapM f

/-- One leaf at chunk `ci` onto `acc`: a scalar leaf adds its bare `scaleFast2'` ladder — the
shift `+2^{5·chunks}` is not cancelled here, since `sumCorrectionsHead` sums the corrections
separately into the fold's initial accumulator — and a `condAdd` leaf conditionally adds its
base. -/
private def leafStep (ci : Fin nc) (acc : AffinePoint (FVar F)) :
    Leaf F nc → CircuitM F S (AffinePoint (FVar F))
  | .full scalar base _ => do
      let l ← scaleFast2' 255 51 254 base[ci] scalar
      (·.p) <$> addFast .checkFinite acc l
  | .b128 scalar base _ => do
      let l ← scaleFast2' 255 26 127 base[ci] scalar
      (·.p) <$> addFast .checkFinite acc l
  | .b10 scalar base _ => do
      let l ← scaleFast2' 255 2 9 base[ci] scalar
      (·.p) <$> addFast .checkFinite acc l
  | .condAdd b base => do
      let r ← addFast .checkFinite base[ci] acc
      select b r.p acc

/-- The leaves folded onto one accumulator per chunk, leaf by leaf and each leaf chunk by chunk:
chunk `k`'s ladder and add both run before chunk `k + 1`'s, the order the deployed gate
stream has. -/
private def foldChunks :
    Vector (AffinePoint (FVar F)) nc → List (Leaf F nc) →
      CircuitM F S (Vector (AffinePoint (FVar F)) nc)
  | acc, [] => pure acc
  | acc, leaf :: rest => do
      let acc' ← chunkwise fun c => leafStep c acc[c] leaf
      foldChunks acc' rest

/-- The public-input commitment from the corrections' sum `init`, per chunk: fold the leaves'
ladders, then negate and add the blinding `h` — `-(Σ [scalar]·base[c]) + h`. The
fold's bare-ladder shifts cancel against `init` in the spec. -/
private def publicInputCommitChunks (init : Vector (AffinePoint (FVar F)) nc)
    (blindingH : AffinePoint (FVar F)) (leaves : List (Leaf F nc)) :
    CircuitM F S (Vector (AffinePoint (FVar F)) nc) := do
  let acc ← foldChunks init leaves
  chunkwise fun c => (·.p) <$> addFast .checkFinite ⟨acc[c].x, CVar.negate_ acc[c].y⟩ blindingH

/-- A correction added onto the accumulator, chunk by chunk. -/
private def addChunks (acc corr : Vector (AffinePoint (FVar F)) nc) :
    CircuitM F S (Vector (AffinePoint (FVar F)) nc) :=
  chunkwise fun c => (·.p) <$> addFast .checkFinite acc[c] corr[c]

/-- Sum the leaves' shift corrections onto `acc`, leaf by leaf and each leaf chunk by chunk:
each scalar leaf adds its `correction`, `condAdd` contributes nothing. -/
private def sumCorrections :
    Vector (AffinePoint (FVar F)) nc → List (Leaf F nc) →
      CircuitM F S (Vector (AffinePoint (FVar F)) nc)
  | acc, [] => pure acc
  | acc, .full _ _ corr :: rest => do
      let acc' ← addChunks acc corr
      sumCorrections acc' rest
  | acc, .b128 _ _ corr :: rest => do
      let acc' ← addChunks acc corr
      sumCorrections acc' rest
  | acc, .b10 _ _ corr :: rest => do
      let acc' ← addChunks acc corr
      sumCorrections acc' rest
  | acc, .condAdd _ _ :: rest => sumCorrections acc rest

/-- The leaves reach a scalar leaf — so the head-seeded corrections fold has a seed. -/
def leafHasScalar : List (Leaf F nc) → Prop
  | [] => False
  | .condAdd _ _ :: rest => leafHasScalar rest
  | _ => True

/-- Head-seeded corrections sum: the first scalar leaf's correction seeds the fold (no gate),
each later scalar correction adds one per chunk (`n` corrections → `n−1` gates per chunk).
`condAdd` leaves are skipped; the all-`condAdd`/empty case is the unused origin. -/
private def sumCorrectionsHead : List (Leaf F nc) → CircuitM F S (Vector (AffinePoint (FVar F)) nc)
  | [] => pure (Vector.replicate nc ⟨.const 0, .const 0⟩)
  | .full _ _ corr :: rest => sumCorrections corr rest
  | .b128 _ _ corr :: rest => sumCorrections corr rest
  | .b10 _ _ corr :: rest => sumCorrections corr rest
  | .condAdd _ _ :: rest => sumCorrectionsHead rest

/-- The boolean leaves constrain their own bits, in walk order, before any ladder runs: every
bit assertion precedes the adds, and a caller does not supply the constraints itself. -/
private def constrainBits [BasicSystem F S] : List (Leaf F nc) → CircuitM F S PUnit
  | [] => pure PUnit.unit
  | .condAdd b _ :: rest => do
      addConstraint (BasicSystem.boolean (↑b : CVar F) : S)
      constrainBits rest
  | .full _ _ _ :: rest => constrainBits rest
  | .b128 _ _ _ :: rest => constrainBits rest
  | .b10 _ _ _ :: rest => constrainBits rest

/-- The wrap side's fold: the head-seeded corrections, the ladders folded onto them, negate,
add `h`. -/
private def publicInputCommitFold (blindingH : AffinePoint (FVar F)) (leaves : List (Leaf F nc)) :
    CircuitM F S (Vector (AffinePoint (FVar F)) nc) := do
  let init ← sumCorrectionsHead leaves
  publicInputCommitChunks init blindingH leaves

/-- The public-input commitment at every chunk, the wrap side's shape: the bits, then
`publicInputCommitFold`. -/
def publicInputCommitFull (blindingH : AffinePoint (FVar F)) (leaves : List (Leaf F nc)) :
    CircuitM F S (Vector (AffinePoint (FVar F)) nc) := do
  constrainBits leaves
  publicInputCommitFold blindingH leaves

/-- One leaf of the sealing walk: a `condAdd` leaf constrains its bit, a scalar leaf seals its
correction chunks and then its base chunks. -/
private def sealLeaf : Leaf F nc → CircuitM F S (Leaf F nc)
  | .condAdd b base => do
      addConstraint (BasicSystem.boolean (↑b : CVar F) : S)
      pure (.condAdd b base)
  | .full s base corr => do
      let corr ← corr.mapM sealPoint
      let base ← base.mapM sealPoint
      pure (.full s base corr)
  | .b128 s base corr => do
      let corr ← corr.mapM sealPoint
      let base ← base.mapM sealPoint
      pure (.b128 s base corr)
  | .b10 s base corr => do
      let corr ← corr.mapM sealPoint
      let base ← base.mapM sealPoint
      pure (.b10 s base corr)

/-- `publicInputCommitFull` over leaves whose scalar bases and corrections are affine
combinations, sealed in walk order before the fold reads them. -/
def publicInputCommitSealed (blindingH : AffinePoint (FVar F)) (leaves : List (Leaf F nc)) :
    CircuitM F S (Vector (AffinePoint (FVar F)) nc) := do
  let leaves ← leaves.mapM sealLeaf
  publicInputCommitFold blindingH leaves

/-- The reading + ladder-witness data the fold produces for one leaf: a scalar leaf yields its
ladder width `L = 5·chunks`, the split witness `(z, bb)` and the base's curve point `T`; a
`condAdd` leaf yields its bit and base point. -/
private inductive LeafInfo (F : Type) [Field F] [DecidableEq F] (d : HasCurve F) where
  /-- A scalar leaf: shift width `L`, split `(z, bb)`, base point `T`. -/
  | scalar (L : ℕ) (z : ℤ) (bb : Bool) (T : d.W.Point)
  /-- A `condAdd` leaf: bit and base point. -/
  | cond (bb : Bool) (T : d.W.Point)

variable {F : Type} [Field F] [DecidableEq F] [ToNat F] {d : HasCurve F}

/-- The curve point a leaf adds to the accumulator in `foldChunks`: a scalar leaf adds its bare
ladder `(2z + bit + 2^L)·T` (shift not yet cancelled); a `condAdd` adds `T` iff its bit. -/
private def LeafInfo.delta : LeafInfo F d → d.W.Point
  | .scalar L z bb T => (2 * z + (if bb then 1 else 0) + 2 ^ L) • T
  | .cond bb T => if bb then T else 0

/-- The ladder regime a scalar leaf's contribution is valid under (`True` for `condAdd`). At
the deployed layer this is discharged by `ladderRegime_subwrap` for the narrow leaves and by
the top bound for the full-width leaf (`PastaShape.regime`). -/
private def LeafInfo.regimeOK : LeafInfo F d → Prop
  | .scalar L z _ _ => d.LadderRegime L (Pasta.Shifted.unshiftType1 L z)
  | .cond _ _ => True

/-- The shift correction a scalar leaf's `init` supplies: `-(2^L)·T` (cancelling the ladder's
`+2^L`); `0` for `condAdd`. Depends only on the leaf's width and base, not the split. -/
private def LeafInfo.corrDelta : LeafInfo F d → d.W.Point
  | .scalar L _ _ T => -(2 ^ L : ℤ) • T
  | .cond _ _ => 0

/-- The net `[scalar]·T` a leaf contributes once the shift is cancelled: `(2z+bit)·T` for a
scalar leaf, `T` iff the bit for `condAdd`. This is the honest MSM summand. -/
private def LeafInfo.netDelta : LeafInfo F d → d.W.Point
  | .scalar _ z bb T => (2 * z + (if bb then 1 else 0)) • T
  | .cond bb T => if bb then T else 0

omit [ToNat F] in
/-- Per leaf, the correction plus the bare ladder is the net: the shift cancels. -/
private theorem LeafInfo.corrDelta_add_delta (i : LeafInfo F d) :
    i.corrDelta + i.delta = i.netDelta := by
  cases i with
  | scalar L z bb T =>
      simp only [corrDelta, delta, netDelta]
      rw [← add_zsmul]
      congr 1
      ring
  | cond bb T => simp only [corrDelta, delta, netDelta, zero_add]

omit [ToNat F] in
/-- Summed: `Σ corrections + Σ bare-ladders = Σ net MSM terms`. -/
private theorem LeafInfo.sum_corrDelta_add_delta (infos : List (LeafInfo F d)) :
    (infos.map corrDelta).sum + (infos.map delta).sum = (infos.map netDelta).sum := by
  induction infos with
  | nil => simp
  | cons i rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [add_add_add_comm, corrDelta_add_delta, ih]

/-- The per-leaf precondition the fold assumes: the base at chunk `ci` reads as a curve point,
and — for a `condAdd` — its bit is boolean-valued under `V`, carried as a well-formedness
premise. -/
def LeafPre (ci : Fin nc) (V : Valuation F) : Leaf F nc → d.W.Point → Prop
  | .full _ base _, T => OnCurveAt d.W V base[ci] T
  | .b128 _ base _, T => OnCurveAt d.W V base[ci] T
  | .b10 _ base _, T => OnCurveAt d.W V base[ci] T
  | .condAdd b base, T =>
      OnCurveAt d.W V base[ci] T ∧ ∃ bb : Bool, (↑b : CVar F).val V = bit bb

/-- One leaf's correction reads as a curve point at chunk `ci`: a scalar leaf's `correction`
on-curve as `cp` (deployed: `-(2^L)·base`, i.e. its `LeafInfo.corrDelta`), a `condAdd`
contributing nothing (`cp = 0`). -/
def CorrPre (ci : Fin nc) (V : Valuation F) : Leaf F nc → d.W.Point → Prop
  | .full _ _ corr, cp => OnCurveAt d.W V corr[ci] cp
  | .b128 _ _ corr, cp => OnCurveAt d.W V corr[ci] cp
  | .b10 _ _ corr, cp => OnCurveAt d.W V corr[ci] cp
  | .condAdd _ _, cp => cp = 0

/-- One leaf reads as one `LeafInfo` at chunk `ci`: the base on-curve as `T`, the scalar split
pinned to the scalar's value (with the width's range on `z` — for the full leaf the pinned
`2^253`, `scaleFast2'`'s top-bit pin at the field width, which makes `2z + bb < 2^254` and the
decode canonical), or the `condAdd` bit read. The ladder regime is deliberately absent — it
is `LeafInfo.regimeOK`, a premise of the fold. -/
private def LeafReads (ci : Fin nc) (V : Valuation F) : Leaf F nc → LeafInfo F d → Prop
  | .full scalar base _, .scalar L z bb T =>
      L = 255 ∧ OnCurveAt d.W V base[ci] T ∧ 0 ≤ z ∧ z < 2 ^ 253 ∧
        ((2 * z + (if bb then 1 else 0) : ℤ) : F) = scalar.val V
  | .b128 scalar base _, .scalar L z bb T =>
      L = 130 ∧ OnCurveAt d.W V base[ci] T ∧ 0 ≤ z ∧ z < 2 ^ 127 ∧
        ((2 * z + (if bb then 1 else 0) : ℤ) : F) = scalar.val V
  | .b10 scalar base _, .scalar L z bb T =>
      L = 10 ∧ OnCurveAt d.W V base[ci] T ∧ 0 ≤ z ∧ z < 2 ^ 9 ∧
        ((2 * z + (if bb then 1 else 0) : ℤ) : F) = scalar.val V
  | .condAdd b base, .cond bb T =>
      OnCurveAt d.W V base[ci] T ∧ (↑b : CVar F).val V = bit bb
  | _, _ => False

omit [ToNat F] in
/-- **Regime discharge per width.** A leaf's `regimeOK` follows from the subwrap bounds for the
narrow widths (`b128` at `L = 130`, `b10` at `L = 10`, via `ladderRegime_subwrap`) and a
supplied full-width regime (`hfull`, discharged at the deployed curve from the top
bound). `condAdd` is trivial. -/
theorem LeafReads.regimeOK {V : Valuation F} {ci : Fin nc}
    {leaf : Leaf F nc} {info : LeafInfo F d}
    (h130 : 3 * 2 ^ 130 ≤ d.W.order) (h10 : 3 * 2 ^ 10 ≤ d.W.order)
    (hr : LeafReads ci V leaf info)
    (hfull : ∀ z bb T, info = LeafInfo.scalar 255 z bb T →
        d.LadderRegime 255 (Pasta.Shifted.unshiftType1 255 z)) :
    info.regimeOK := by
  cases leaf <;> cases info <;> simp only [LeafReads] at hr <;>
    first
      | exact hr.elim
      | trivial
      | (obtain ⟨hL, -, -, -, -⟩ := hr
         subst hL
         simp only [LeafInfo.regimeOK]
         first
           | exact hfull _ _ _ rfl
           | exact ladderRegime_subwrap d _ _ h130
           | exact ladderRegime_subwrap d _ _ h10)

omit [ToNat F] in
/-- **The regime discharge, lifted to the whole leaf list.** Every info a leaf list reads to
is in regime, off the narrow subwrap bounds and a single full-width regime premise
(supplied at the deployed curve). The list form `publicInputCommitFold_spec`'s regime premise
wants. -/
private theorem leafReads_regimeOK_all {V : Valuation F} {ci : Fin nc}
    (h130 : 3 * 2 ^ 130 ≤ d.W.order) (h10 : 3 * 2 ^ 10 ≤ d.W.order)
    {leaves : List (Leaf F nc)} {infos : List (LeafInfo F d)}
    (hr : List.Forall₂ (LeafReads ci V) leaves infos)
    (hfull : ∀ z bb T, LeafInfo.scalar 255 z bb T ∈ infos →
        d.LadderRegime 255 (Pasta.Shifted.unshiftType1 255 z)) :
    ∀ i ∈ infos, i.regimeOK := by
  induction hr with
  | nil => simp
  | @cons leaf info ls is hli _ ih =>
      intro i hi
      rcases List.mem_cons.1 hi with rfl | hi'
      · exact LeafReads.regimeOK h130 h10 hli
          (fun z bb T heq => hfull z bb T (heq ▸ List.mem_cons_self ..))
      · exact ih (fun z bb T hmem => hfull z bb T (List.mem_cons_of_mem info hmem)) i hi'

/-- **A scalar leaf's correction cell reads as the honest shift `-(2^{5·chunks})·base`.** The
public premise the seed condition needs: the constant correction is exactly what cancels the
ladder's `+2^L` shift. `condAdd` has no correction. Stated over the leaf's own cells (no
`LeafInfo`), so it can sit on the public glue hypothesis. -/
def CorrHonest (d : HasCurve F) (ci : Fin nc) (V : Valuation F) : Leaf F nc → Prop
  | .full _ base corr =>
      ∀ T, OnCurveAt d.W V base[ci] T → OnCurveAt d.W V corr[ci] (-(2 ^ 255 : ℤ) • T)
  | .b128 _ base corr =>
      ∀ T, OnCurveAt d.W V base[ci] T → OnCurveAt d.W V corr[ci] (-(2 ^ 130 : ℤ) • T)
  | .b10 _ base corr =>
      ∀ T, OnCurveAt d.W V base[ci] T → OnCurveAt d.W V corr[ci] (-(2 ^ 10 : ℤ) • T)
  | .condAdd _ _ => True

omit [ToNat F] in
/-- **The seed discharge.** With honest corrections, the corrections' readings sum to the
`corrDelta` sum — exactly `publicInputCommitFold_spec`'s seed premise. Position-wise
`cp = corrDelta info` (via `OnCurveAt.eq` on the shared cell), lifted over the list. -/
private theorem corrSum_eq {V : Valuation F} {ci : Fin nc} :
    ∀ {leaves : List (Leaf F nc)} {cps : List d.W.Point} {infos : List (LeafInfo F d)},
      List.Forall₂ (CorrPre ci V) leaves cps →
      List.Forall₂ (LeafReads ci V) leaves infos →
      (∀ leaf ∈ leaves, CorrHonest d ci V leaf) →
      cps.sum = (infos.map LeafInfo.corrDelta).sum
  | [], [], [], .nil, .nil, _ => by simp
  | leaf :: ls, cp :: cps, info :: is, .cons hcp hcps, .cons hr hrs, hhon => by
      simp only [List.sum_cons, List.map_cons]
      rw [corrSum_eq hcps hrs (fun l hl => hhon l (List.mem_cons_of_mem _ hl))]
      have hhead : cp = LeafInfo.corrDelta info := by
        have hh := hhon leaf (List.mem_cons_self ..)
        cases leaf with
        | full scalar base corr =>
            cases info with
            | scalar L z bb T =>
                obtain ⟨hL, hb, -, -, -⟩ := hr
                subst hL
                simp only [CorrPre] at hcp
                simp only [CorrHonest] at hh
                simp only [LeafInfo.corrDelta]
                exact OnCurveAt.eq hcp (hh _ hb) rfl rfl
            | cond bb T => simp only [LeafReads] at hr
        | b128 scalar base corr =>
            cases info with
            | scalar L z bb T =>
                obtain ⟨hL, hb, -, -, -⟩ := hr
                subst hL
                simp only [CorrPre] at hcp
                simp only [CorrHonest] at hh
                simp only [LeafInfo.corrDelta]
                exact OnCurveAt.eq hcp (hh _ hb) rfl rfl
            | cond bb T => simp only [LeafReads] at hr
        | b10 scalar base corr =>
            cases info with
            | scalar L z bb T =>
                obtain ⟨hL, hb, -, -, -⟩ := hr
                subst hL
                simp only [CorrPre] at hcp
                simp only [CorrHonest] at hh
                simp only [LeafInfo.corrDelta]
                exact OnCurveAt.eq hcp (hh _ hb) rfl rfl
            | cond bb T => simp only [LeafReads] at hr
        | condAdd b base =>
            cases info with
            | scalar L z bb T => simp only [LeafReads] at hr
            | cond bb T =>
                simp only [CorrPre] at hcp
                simp only [LeafInfo.corrDelta]
                exact hcp
      rw [hhead]

omit [ToNat F] in
/-- `chunkwise f` reads at chunk `ci` as `f ci` alone does; the other chunks say nothing. -/
private theorem chunkwise_at {V : Valuation F} {β : Type}
    (f : Fin nc → CircuitM F (Builder V (KimchiConstraint F)) β) (ci : Fin nc) (Q : β → Prop)
    (h : ⦃⌜True⌝⦄ f ci ⦃⇓ r _ => ⌜Q r⌝⦄) :
    ⦃⌜True⌝⦄ chunkwise f ⦃⇓ rs _ => ⌜Q rs[ci]⌝⦄ := by
  unfold chunkwise
  refine builder_spec_imp _ _ _
    (builder_spec_vector_mapM_get f (fun c r => c = ci → Q r) (fun c => ?_) _) fun rs h => ?_
  · by_cases hc : c = ci
    · subst hc
      exact builder_spec_imp _ _ _ h fun r hr _ => hr
    · exact builder_spec_imp _ _ _ (builder_spec_true _) fun r _ h => absurd h hc
  · simpa using h ci

omit [ToNat F] in
/-- An `addFast`'s point reads as the sum. -/
private theorem addFastP_spec {V : Valuation F} (p q : AffinePoint (FVar F)) :
    ⦃⌜True⌝⦄ Functor.map (·.p) (addFast (c := Builder V (KimchiConstraint F)) .checkFinite p q)
    ⦃⇓ r _ => ⌜∀ P Q : d.W.Point, OnCurveAt d.W V p P → OnCurveAt d.W V q Q →
      OnCurveAt d.W V r (P + Q)⌝⦄ := by
  have h := addFast_checkFinite_spec (V := V) d.W d.short d.two_ne d.two_torsion_free p q
  mvcgen [-Snarky.Kimchi.addFast_spec, h]

/-- **One leaf at one chunk reads as the accumulator plus its delta.** The ladder's shift is
still present in the delta; the top-level's `init = Σ corrections` cancels it. -/
private theorem leafStep_spec (ci : Fin nc) {V : Valuation F} (acc : AffinePoint (FVar F)) :
    ∀ (leaf : Leaf F nc) (T : d.W.Point), LeafPre ci V leaf T →
      ⦃⌜True⌝⦄ leafStep (S := Builder V (KimchiConstraint F)) ci acc leaf
      ⦃⇓ r _ => ⌜∃ info : LeafInfo F d, LeafReads ci V leaf info ∧
        ∀ accv : d.W.Point, OnCurveAt d.W V acc accv → info.regimeOK →
          OnCurveAt d.W V r (accv + info.delta)⌝⦄
  | .full scalar base _, T, hT => by
      simp only [leafStep]
      have hsf := scaleFast2'_spec (V := V) d 255 51 254 (by norm_num) (by norm_num) base[ci] scalar
      have hadd := fun l => addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
        d.two_torsion_free acc l
      mvcgen [-Snarky.Kimchi.addFast_spec, hsf, hadd]
      rename_i _ _ _ hsf' _ _
      intro hadd'
      obtain ⟨z, bb, h0, -, hlt, hval, hladder⟩ := hsf' T hT
      refine ⟨.scalar 255 z bb T, ⟨rfl, hT, h0, hlt (by norm_num), hval⟩, fun accv hacc hreg => ?_⟩
      have hstep := hadd' accv _ hacc (hladder hreg)
      simp only [LeafInfo.delta, Pasta.Shifted.unshiftType2] at hstep ⊢
      exact hstep
  | .b128 scalar base _, T, hT => by
      simp only [leafStep]
      have hsf := scaleFast2'_spec (V := V) d 255 26 127 (by norm_num) (by norm_num) base[ci] scalar
      have hadd := fun l => addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
        d.two_torsion_free acc l
      mvcgen [-Snarky.Kimchi.addFast_spec, hsf, hadd]
      rename_i _ _ _ hsf' _ _
      intro hadd'
      obtain ⟨z, bb, h0, hlt, -, hval, hladder⟩ := hsf' T hT
      refine ⟨.scalar 130 z bb T, ⟨rfl, hT, h0, hlt, hval⟩, fun accv hacc hreg => ?_⟩
      have hstep := hadd' accv _ hacc (hladder hreg)
      simp only [LeafInfo.delta, Pasta.Shifted.unshiftType2] at hstep ⊢
      exact hstep
  | .b10 scalar base _, T, hT => by
      simp only [leafStep]
      have hsf := scaleFast2'_spec (V := V) d 255 2 9 (by norm_num) (by norm_num) base[ci] scalar
      have hadd := fun l => addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
        d.two_torsion_free acc l
      mvcgen [-Snarky.Kimchi.addFast_spec, hsf, hadd]
      rename_i _ _ _ hsf' _ _
      intro hadd'
      obtain ⟨z, bb, h0, hlt, -, hval, hladder⟩ := hsf' T hT
      refine ⟨.scalar 10 z bb T, ⟨rfl, hT, h0, hlt, hval⟩, fun accv hacc hreg => ?_⟩
      have hstep := hadd' accv _ hacc (hladder hreg)
      simp only [LeafInfo.delta, Pasta.Shifted.unshiftType2] at hstep ⊢
      exact hstep
  | .condAdd b base, T, hT => by
      simp only [leafStep]
      have haddc := addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
        d.two_torsion_free base[ci] acc
      have hsel := fun t => select_affinePoint_spec (V := V) (c := KimchiConstraint F) b t acc
      mvcgen [-Snarky.Kimchi.addFast_spec, haddc, hsel]
      rename_i _ _ _ haddc' _ _
      intro hsel'
      obtain ⟨hToc, bb, hbb⟩ := hT
      refine ⟨.cond bb T, ⟨hToc, hbb⟩, fun accv hacc _ => ?_⟩
      have hsc := hsel' bb hbb (T + accv) accv (haddc' T accv hToc hacc) hacc
      cases bb
      · simpa [LeafInfo.delta] using hsc
      · simpa [LeafInfo.delta, add_comm] using hsc

/-- **The chunked fold reads, at each chunk, as the accumulator plus the sum of leaf deltas.**
For a satisfying assignment, `foldChunks acc leaves` reads at chunk `ci`, at any `accv` for
`acc[ci]`, as `accv + Σ (LeafInfo.delta)` over infos the leaves read to — provided each scalar
leaf's ladder regime holds (`regimeOK`). -/
private theorem foldChunks_spec (ci : Fin nc) {V : Valuation F} :
    ∀ (leaves : List (Leaf F nc)) (Ts : List d.W.Point) (acc : Vector (AffinePoint (FVar F)) nc),
      List.Forall₂ (LeafPre ci V) leaves Ts →
      ⦃⌜True⌝⦄ foldChunks (S := Builder V (KimchiConstraint F)) acc leaves
      ⦃⇓ r _ => ⌜∃ infos : List (LeafInfo F d), List.Forall₂ (LeafReads ci V) leaves infos ∧
        ∀ accv : d.W.Point, OnCurveAt d.W V acc[ci] accv → (∀ i ∈ infos, i.regimeOK) →
          OnCurveAt d.W V r[ci] (accv + (infos.map LeafInfo.delta).sum)⌝⦄
  | [], [], acc, .nil => by
      simp only [foldChunks]
      mvcgen
      exact ⟨[], .nil, fun accv hacc _ => by simpa using hacc⟩
  | leaf :: rest, T :: Ts, acc, .cons hT hrest => by
      simp only [foldChunks]
      have hstep := chunkwise_at
        (fun c => leafStep (S := Builder V (KimchiConstraint F)) c acc[c] leaf) ci _
        (leafStep_spec (d := d) ci acc[ci] leaf T hT)
      have ih := fun acc' => foldChunks_spec ci rest Ts acc' hrest
      mvcgen [hstep, ih]
      rename_i _ _ hstep' _ _
      rintro ⟨rest_infos, hrf, hrest_oc⟩
      obtain ⟨info, hinfo, hoc⟩ := hstep'
      refine ⟨info :: rest_infos, .cons hinfo hrf, fun accv hacc hregs => ?_⟩
      have h1 := hoc accv hacc (hregs _ List.mem_cons_self)
      have h2 := hrest_oc _ h1 fun i hi => hregs i (List.mem_cons_of_mem _ hi)
      simpa [add_assoc] using h2

/-- **The commitment from `init` reads, at each chunk, as `-(init + Σ deltas) + h`.**
Composing `foldChunks_spec` with the pure negate (`OnCurveAt.neg`) and the final `addFast h`.
At the deployed layer `init` reads as `Σ (-2^{L}·base)` (the corrections) and the shifts in the
deltas cancel it, leaving `-(Σ [scalar]·base) + h = publicCommitment`. -/
private theorem publicInputCommitChunks_spec (ci : Fin nc) {V : Valuation F}
    (init : Vector (AffinePoint (FVar F)) nc) (blindingH : AffinePoint (FVar F))
    (leaves : List (Leaf F nc)) (Ts : List d.W.Point)
    (Iv Hv : d.W.Point) (hI : OnCurveAt d.W V init[ci] Iv) (hH : OnCurveAt d.W V blindingH Hv)
    (hpre : List.Forall₂ (LeafPre ci V) leaves Ts) :
    ⦃⌜True⌝⦄
    publicInputCommitChunks (S := Builder V (KimchiConstraint F)) init blindingH leaves
    ⦃⇓ r _ => ⌜∃ infos : List (LeafInfo F d), List.Forall₂ (LeafReads ci V) leaves infos ∧
      ((∀ i ∈ infos, i.regimeOK) →
        OnCurveAt d.W V r[ci] (-(Iv + (infos.map LeafInfo.delta).sum) + Hv))⌝⦄ := by
  simp only [publicInputCommitChunks]
  have hfold := foldChunks_spec (d := d) ci leaves Ts init hpre
  have hfin := fun acc : Vector (AffinePoint (FVar F)) nc => chunkwise_at
    (fun c => (·.p) <$> addFast (c := Builder V (KimchiConstraint F)) .checkFinite
      ⟨acc[c].x, CVar.negate_ acc[c].y⟩ blindingH) ci _
    (addFastP_spec (d := d) ⟨acc[ci].x, CVar.negate_ acc[ci].y⟩ blindingH)
  mvcgen [hfold, hfin]
  rename_i _ _ hfold' _ _
  intro haddpost
  obtain ⟨infos, hrf, hoc⟩ := hfold'
  refine ⟨infos, hrf, fun hregs => ?_⟩
  have hacc := hoc Iv hI hregs
  have hneg := OnCurveAt.neg ⟨d.short.1, d.short.2.2.1⟩ hacc
  exact haddpost _ Hv hneg hH

/-- **The commitment computes the honest MSM at each chunk.** When `init[ci]` reads as the
corrections' sum `Σ corrDelta` (over the produced infos), the shifts cancel and the output
reads as `-(Σ netDelta) + h` — `-(Σ [scalar]·base) + h`, the shape `publicCommitment` has. -/
private theorem publicInputCommitChunks_net_spec (ci : Fin nc) {V : Valuation F}
    (init : Vector (AffinePoint (FVar F)) nc) (blindingH : AffinePoint (FVar F))
    (leaves : List (Leaf F nc)) (Ts : List d.W.Point)
    (Iv Hv : d.W.Point) (hI : OnCurveAt d.W V init[ci] Iv) (hH : OnCurveAt d.W V blindingH Hv)
    (hpre : List.Forall₂ (LeafPre ci V) leaves Ts) :
    ⦃⌜True⌝⦄
    publicInputCommitChunks (S := Builder V (KimchiConstraint F)) init blindingH leaves
    ⦃⇓ r _ => ⌜∃ infos : List (LeafInfo F d), List.Forall₂ (LeafReads ci V) leaves infos ∧
      (Iv = (infos.map LeafInfo.corrDelta).sum → (∀ i ∈ infos, i.regimeOK) →
        OnCurveAt d.W V r[ci] (-(infos.map LeafInfo.netDelta).sum + Hv))⌝⦄ := by
  refine builder_spec_imp _ _ _
    (publicInputCommitChunks_spec ci init blindingH leaves Ts Iv Hv hI hH hpre) fun r hr => ?_
  obtain ⟨infos, hrf, hoc⟩ := hr
  refine ⟨infos, hrf, fun hIeq hregs => ?_⟩
  have h := hoc hregs
  rw [hIeq, LeafInfo.sum_corrDelta_add_delta] at h
  exact h

/-- A boolean leaf's bit is boolean; the scalar leaves say nothing. What the bit pre-pass
forces of each leaf. -/
def Leaf.bitBoolean (V : Valuation F) : Leaf F nc → Prop
  | .condAdd b _ => ∃ bb : Bool, (↑b : CVar F).val V = bit bb
  | _ => True

omit [ToNat F] in
/-- **The bit pre-pass makes every boolean leaf's bit boolean.** The pass is the gadget's own
opening move, so the commitment's read assumes this of its leaves rather than asking a
consumer for it (`builder_spec_bind_of`). -/
private theorem constrainBits_boolean {V : Valuation F} :
    ∀ leaves : List (Leaf F nc),
      ⦃⌜True⌝⦄ constrainBits (S := Builder V (KimchiConstraint F)) leaves
      ⦃⇓ _ _ => ⌜∀ leaf ∈ leaves, leaf.bitBoolean V⌝⦄
  | [] => by
      simp only [constrainBits]
      mvcgen
      intro leaf hl
      exact absurd hl List.not_mem_nil
  | .condAdd b base :: rest => by
      simp only [constrainBits]
      have ih := constrainBits_boolean (V := V) rest
      mvcgen [ih]
      rename_i hb _ _
      intro hrest leaf hl
      rcases List.mem_cons.1 hl with rfl | hl
      · rcases (LawfulBasicSystem.holds_boolean V (↑b : CVar F)).mp hb with h | h
        · exact ⟨false, by simpa [bit] using h⟩
        · exact ⟨true, by simpa [bit] using h⟩
      · exact hrest leaf hl
  | .full s base corr :: rest => by
      simp only [constrainBits]
      refine builder_spec_imp _ _ _ (constrainBits_boolean (V := V) rest) fun _ h leaf hl => ?_
      rcases List.mem_cons.1 hl with rfl | hl
      · trivial
      · exact h leaf hl
  | .b128 s base corr :: rest => by
      simp only [constrainBits]
      refine builder_spec_imp _ _ _ (constrainBits_boolean (V := V) rest) fun _ h leaf hl => ?_
      rcases List.mem_cons.1 hl with rfl | hl
      · trivial
      · exact h leaf hl
  | .b10 s base corr :: rest => by
      simp only [constrainBits]
      refine builder_spec_imp _ _ _ (constrainBits_boolean (V := V) rest) fun _ h leaf hl => ?_
      rcases List.mem_cons.1 hl with rfl | hl
      · trivial
      · exact h leaf hl

omit [ToNat F] in
/-- **The corrections-sum reads, at each chunk, as `accv + Σ` the correction points.** Given
each leaf's correction reads at chunk `ci` as `cp` (`condAdd`: `0`), `sumCorrections acc leaves`
reads at `ci` as `accv + Σ cps`. -/
private theorem sumCorrections_spec (ci : Fin nc) {V : Valuation F} :
    ∀ (leaves : List (Leaf F nc)) (cps : List d.W.Point) (acc : Vector (AffinePoint (FVar F)) nc),
      List.Forall₂ (CorrPre ci V) leaves cps →
      ⦃⌜True⌝⦄ sumCorrections (S := Builder V (KimchiConstraint F)) acc leaves
      ⦃⇓ r _ => ⌜∀ accv : d.W.Point, OnCurveAt d.W V acc[ci] accv →
        OnCurveAt d.W V r[ci] (accv + cps.sum)⌝⦄
  | [], [], acc, .nil => by
      simp only [sumCorrections]
      mvcgen
      intro accv hacc
      simpa using hacc
  | .full _ _ corr :: rest, cp :: cps, acc, .cons hcp hrest => by
      simp only [sumCorrections, addChunks]
      have hadd := chunkwise_at (fun c => (·.p) <$> addFast
        (c := Builder V (KimchiConstraint F)) .checkFinite acc[c] corr[c]) ci _
        (addFastP_spec (d := d) acc[ci] corr[ci])
      have ih := fun acc' => sumCorrections_spec ci rest cps acc' hrest
      mvcgen [hadd, ih]
      rename_i _ _ hadd' _ _
      intro ihpost accv hacc
      simp only [List.sum_cons]
      rw [← add_assoc]
      exact ihpost _ (hadd' accv cp hacc hcp)
  | .b128 _ _ corr :: rest, cp :: cps, acc, .cons hcp hrest => by
      simp only [sumCorrections, addChunks]
      have hadd := chunkwise_at (fun c => (·.p) <$> addFast
        (c := Builder V (KimchiConstraint F)) .checkFinite acc[c] corr[c]) ci _
        (addFastP_spec (d := d) acc[ci] corr[ci])
      have ih := fun acc' => sumCorrections_spec ci rest cps acc' hrest
      mvcgen [hadd, ih]
      rename_i _ _ hadd' _ _
      intro ihpost accv hacc
      simp only [List.sum_cons]
      rw [← add_assoc]
      exact ihpost _ (hadd' accv cp hacc hcp)
  | .b10 _ _ corr :: rest, cp :: cps, acc, .cons hcp hrest => by
      simp only [sumCorrections, addChunks]
      have hadd := chunkwise_at (fun c => (·.p) <$> addFast
        (c := Builder V (KimchiConstraint F)) .checkFinite acc[c] corr[c]) ci _
        (addFastP_spec (d := d) acc[ci] corr[ci])
      have ih := fun acc' => sumCorrections_spec ci rest cps acc' hrest
      mvcgen [hadd, ih]
      rename_i _ _ hadd' _ _
      intro ihpost accv hacc
      simp only [List.sum_cons]
      rw [← add_assoc]
      exact ihpost _ (hadd' accv cp hacc hcp)
  | .condAdd _ _ :: rest, cp :: cps, acc, .cons hcp hrest => by
      simp only [sumCorrections]
      have hcp0 : cp = 0 := hcp
      refine builder_spec_imp _ _ _
        (sumCorrections_spec ci rest cps acc hrest) fun r hr accv hacc => ?_
      simp only [List.sum_cons, hcp0, zero_add]
      exact hr accv hacc

omit [ToNat F] in
/-- **The head-seeded corrections sum reads, at each chunk, as `Σ cps`.** The first scalar
leaf's correction seeds the fold; the rest add via `sumCorrections_spec`; `condAdd` leaves skip
(their `cp = 0`). Needs a scalar leaf (`leafHasScalar`) so the origin is not returned. -/
private theorem sumCorrectionsHead_spec (ci : Fin nc) {V : Valuation F} :
    ∀ (leaves : List (Leaf F nc)) (cps : List d.W.Point),
      List.Forall₂ (CorrPre ci V) leaves cps → leafHasScalar leaves →
      ⦃⌜True⌝⦄ sumCorrectionsHead (S := Builder V (KimchiConstraint F)) leaves
      ⦃⇓ r _ => ⌜OnCurveAt d.W V r[ci] cps.sum⌝⦄
  | [], [], .nil, hne => by simp only [leafHasScalar] at hne
  | .full _ _ corr :: rest, cp :: cps, .cons hcp hrest, _ => by
      simp only [sumCorrectionsHead]
      refine builder_spec_imp _ _ _ (sumCorrections_spec ci rest cps corr hrest) fun r hr => ?_
      simp only [List.sum_cons]
      exact hr cp hcp
  | .b128 _ _ corr :: rest, cp :: cps, .cons hcp hrest, _ => by
      simp only [sumCorrectionsHead]
      refine builder_spec_imp _ _ _ (sumCorrections_spec ci rest cps corr hrest) fun r hr => ?_
      simp only [List.sum_cons]
      exact hr cp hcp
  | .b10 _ _ corr :: rest, cp :: cps, .cons hcp hrest, _ => by
      simp only [sumCorrectionsHead]
      refine builder_spec_imp _ _ _ (sumCorrections_spec ci rest cps corr hrest) fun r hr => ?_
      simp only [List.sum_cons]
      exact hr cp hcp
  | .condAdd _ _ :: rest, cp :: cps, .cons hcp hrest, hne => by
      simp only [sumCorrectionsHead]
      have hcp0 : cp = 0 := hcp
      refine builder_spec_imp _ _ _ (sumCorrectionsHead_spec ci rest cps hrest hne)
        fun r hr => ?_
      simp only [List.sum_cons, hcp0, zero_add]
      exact hr

/-- **The gadget computes the honest MSM at each chunk.** Composing the corrections sum with
`publicInputCommitChunks_net_spec`: with the corrections reading as `cps` at chunk `ci`, the
output reads there as `-(Σ netDelta) + h`, under the seed condition `Σcps = Σ corrDelta`. -/
private theorem publicInputCommitFold_spec (ci : Fin nc) {V : Valuation F}
    (blindingH : AffinePoint (FVar F)) (leaves : List (Leaf F nc))
    (Ts cps : List d.W.Point) (Hv : d.W.Point)
    (hH : OnCurveAt d.W V blindingH Hv)
    (hpre : List.Forall₂ (LeafPre ci V) leaves Ts)
    (hcorr : List.Forall₂ (CorrPre ci V) leaves cps)
    (hscalar : leafHasScalar leaves) :
    ⦃⌜True⌝⦄
    publicInputCommitFold (S := Builder V (KimchiConstraint F)) blindingH leaves
    ⦃⇓ r _ => ⌜∃ infos : List (LeafInfo F d), List.Forall₂ (LeafReads ci V) leaves infos ∧
      (cps.sum = (infos.map LeafInfo.corrDelta).sum → (∀ i ∈ infos, i.regimeOK) →
        OnCurveAt d.W V r[ci] (-(infos.map LeafInfo.netDelta).sum + Hv))⌝⦄ := by
  simp only [publicInputCommitFold]
  have hsum := sumCorrectionsHead_spec ci leaves cps hcorr hscalar
  mvcgen [hsum]
  rename_i rinit
  intro s hpost
  exact publicInputCommitChunks_net_spec ci rinit blindingH leaves Ts cps.sum Hv
    hpost hH hpre s trivial

/-- **The net read, premises discharged.** `publicInputCommitFold_spec` with its seed
(`corrSum_eq`, from honest corrections) and regime (`leafReads_regimeOK_all`, from the width
bounds and the full-width regime premise) supplied: the output reads unconditionally at chunk
`ci` as `-(Σ netDelta) + h`, the honest MSM. The last step before the wire crossing
(`publicCommitment`). -/
private theorem publicInputCommitFold_net (ci : Fin nc) {V : Valuation F}
    (blindingH : AffinePoint (FVar F)) (leaves : List (Leaf F nc))
    (Ts cps : List d.W.Point) (Hv : d.W.Point)
    (h130 : 3 * 2 ^ 130 ≤ d.W.order) (h10 : 3 * 2 ^ 10 ≤ d.W.order)
    (hfull : ∀ infos : List (LeafInfo F d), List.Forall₂ (LeafReads ci V) leaves infos →
        ∀ z bb T, LeafInfo.scalar 255 z bb T ∈ infos →
          d.LadderRegime 255 (Pasta.Shifted.unshiftType1 255 z))
    (hH : OnCurveAt d.W V blindingH Hv)
    (hpre : List.Forall₂ (LeafPre ci V) leaves Ts)
    (hcorr : List.Forall₂ (CorrPre ci V) leaves cps)
    (hscalar : leafHasScalar leaves)
    (hhon : ∀ leaf ∈ leaves, CorrHonest d ci V leaf) :
    ⦃⌜True⌝⦄
    publicInputCommitFold (S := Builder V (KimchiConstraint F)) blindingH leaves
    ⦃⇓ r _ => ⌜∃ infos : List (LeafInfo F d), List.Forall₂ (LeafReads ci V) leaves infos ∧
      OnCurveAt d.W V r[ci] (-(infos.map LeafInfo.netDelta).sum + Hv)⌝⦄ := by
  refine builder_spec_imp _ _ _
    (publicInputCommitFold_spec ci blindingH leaves Ts cps Hv hH hpre hcorr hscalar)
    fun r hr => ?_
  obtain ⟨infos, hff, himp⟩ := hr
  exact ⟨infos, hff,
    himp (corrSum_eq hcorr hff hhon) (leafReads_regimeOK_all h130 h10 hff (hfull infos hff))⟩

/-- **The honest MSM as a single point.** `publicInputCommitFold_net` with the net-delta sum
identified as a caller-supplied point `msm` (via `hmsm`): the output reads at chunk `ci` as
`-msm + h`. The wire crossing supplies `msm = publicCommitment`'s MSM and discharges `hmsm`
from the canonical decode. -/
private theorem publicInputCommitFold_msm (ci : Fin nc) {V : Valuation F}
    (blindingH : AffinePoint (FVar F)) (leaves : List (Leaf F nc))
    (Ts cps : List d.W.Point) (Hv msm : d.W.Point)
    (h130 : 3 * 2 ^ 130 ≤ d.W.order) (h10 : 3 * 2 ^ 10 ≤ d.W.order)
    (hfull : ∀ infos : List (LeafInfo F d), List.Forall₂ (LeafReads ci V) leaves infos →
        ∀ z bb T, LeafInfo.scalar 255 z bb T ∈ infos →
          d.LadderRegime 255 (Pasta.Shifted.unshiftType1 255 z))
    (hH : OnCurveAt d.W V blindingH Hv)
    (hpre : List.Forall₂ (LeafPre ci V) leaves Ts)
    (hcorr : List.Forall₂ (CorrPre ci V) leaves cps)
    (hscalar : leafHasScalar leaves)
    (hhon : ∀ leaf ∈ leaves, CorrHonest d ci V leaf)
    (hmsm : ∀ infos : List (LeafInfo F d), List.Forall₂ (LeafReads ci V) leaves infos →
        (infos.map LeafInfo.netDelta).sum = msm) :
    ⦃⌜True⌝⦄
    publicInputCommitFold (S := Builder V (KimchiConstraint F)) blindingH leaves
    ⦃⇓ r _ => ⌜OnCurveAt d.W V r[ci] (-msm + Hv)⌝⦄ := by
  refine builder_spec_imp _ _ _
    (publicInputCommitFold_net ci blindingH leaves Ts cps Hv h130 h10 hfull hH hpre hcorr
      hscalar hhon) fun r hr => ?_
  obtain ⟨infos, hff, hread⟩ := hr
  rw [hmsm infos hff] at hread
  exact hread

/-! ## The public MSM the leaves commit to, and the reads read against it -/

/-- The full 255-bit leaf's ladder regime, phrased over its public scalar cell: any decode
`(z, bb)` in the `scaleFast2'` range (`z < 2^253`, the pinned half) lands in `LadderRegime`.
The narrow leaves discharge their own regime from the width bounds (`ladderRegime_subwrap`),
so carry `True`. Mirrors the fold's `hfull` premise without naming the private `LeafInfo`. -/
def Leaf.regimeFull (d : HasCurve F) (V : Valuation F) : Leaf F nc → Prop
  | .full s _ _ => ∀ (z : ℤ) (bb : Bool), 0 ≤ z → z < 2 ^ 253 →
      ((2 * z + (if bb then 1 else 0) : ℤ) : F) = s.val V →
        d.LadderRegime 255 (Pasta.Shifted.unshiftType1 255 z)
  | _ => True

/-- The honest public MSM the leaves commit to at chunk `ci`: each leaf's canonical scalar
value (`ToNat.toNat` of its `scalarVar` reading) times its base point (from `LeafPre`). This is
`Σ [scalarₗ]·baseₗ`, the point `publicCommitment` negates and adds `h` to. -/
def publicMsm (V : Valuation F) (leaves : List (Leaf F nc)) (Ts : List d.W.Point) : d.W.Point :=
  ((leaves.zip Ts).map (fun p => ToNat.toNat ((p.1.scalarVar).val V) • p.2)).sum

/-- `publicMsm` peels one leaf/base pair off the front. -/
theorem publicMsm_cons (V : Valuation F) (leaf : Leaf F nc) (T : d.W.Point)
    (ls : List (Leaf F nc)) (Ts : List d.W.Point) :
    publicMsm V (leaf :: ls) (T :: Ts)
      = ToNat.toNat ((leaf.scalarVar).val V) • T + publicMsm V ls Ts := by
  simp [publicMsm, List.zip_cons_cons]

omit [ToNat F] in
/-- **The regime premise, lifted from leaves to the fold's info form.** A `.scalar 255 …` in the
produced infos comes from a full leaf (the narrow widths read to `L = 130`/`10`), so its regime
is the leaf's `Leaf.regimeFull`. Discharges the fold's `hfull` from the public `hregime`. -/
private theorem regimeFull_hfull {V : Valuation F} {ci : Fin nc} :
    ∀ {leaves : List (Leaf F nc)} {infos : List (LeafInfo F d)},
      (∀ leaf ∈ leaves, Leaf.regimeFull d V leaf) →
      List.Forall₂ (LeafReads ci V) leaves infos →
      ∀ z bb T, LeafInfo.scalar 255 z bb T ∈ infos →
        d.LadderRegime 255 (Pasta.Shifted.unshiftType1 255 z)
  | [], [], _, .nil, z, bb, T, hmem => by simp at hmem
  | leaf :: ls, info :: is, hreg, .cons hr hrs, z, bb, T, hmem => by
      rcases List.mem_cons.1 hmem with heq | hmem'
      · subst heq
        cases leaf with
        | full s base corr =>
            obtain ⟨_, _, h0, hlt, hval⟩ := hr
            exact (hreg _ (List.mem_cons_self ..)) z bb h0 hlt hval
        | b128 s base corr => obtain ⟨hL, _⟩ := hr; exact absurd hL (by norm_num)
        | b10 s base corr => obtain ⟨hL, _⟩ := hr; exact absurd hL (by norm_num)
        | condAdd b base => exact hr.elim
      · exact regimeFull_hfull (fun l hl => hreg l (List.mem_cons_of_mem _ hl)) hrs z bb T hmem'

/-- **The net-delta sum is the public MSM.** Under the field's below-`2^254` faithfulness
(`hcast`) and the bit reading (`hbit`), the honest `Σ netDelta` over the produced infos equals
`publicMsm` — each `(2z+bb)·T` collapses to `toNat(scalar)·T` (the decode is canonical at every
width: the narrow leaves from their width, the full leaf from `scaleFast2'`'s top-bit pin,
`z < 2^253`), and each `condAdd` bit lines up. Discharges the fold's `hmsm`. -/
private theorem netDelta_sum_eq_publicMsm {V : Valuation F} {ci : Fin nc}
    (hcast : ∀ m : ℤ, 0 ≤ m → m < 2 ^ 254 → (ToNat.toNat ((m : F)) : ℤ) = m)
    (hbit : ∀ b : Bool, ToNat.toNat (bit b : F) = if b then 1 else 0) :
    ∀ {leaves : List (Leaf F nc)} {infos : List (LeafInfo F d)} {Ts : List d.W.Point},
      List.Forall₂ (LeafReads ci V) leaves infos →
      List.Forall₂ (LeafPre ci V) leaves Ts →
      (infos.map LeafInfo.netDelta).sum = publicMsm V leaves Ts
  | [], [], [], .nil, .nil => by simp [publicMsm]
  | leaf :: ls, info :: is, T :: Ts, .cons hr hrs, .cons hp hps => by
      have ihv := netDelta_sum_eq_publicMsm hcast hbit hrs hps
      have hhead : LeafInfo.netDelta info = ToNat.toNat ((leaf.scalarVar).val V) • T := by
        cases leaf with
        | full s base corr =>
            cases info with
            | scalar L z bb T' =>
                obtain ⟨hL, hocI, h0, hlt, hval⟩ := hr
                subst hL
                have hcl : 2 * z + (if bb then 1 else 0) < 2 ^ 254 := by
                  have hb : (if bb then (1 : ℤ) else 0) ≤ 1 := by cases bb <;> simp
                  have hle : z ≤ 2 ^ 253 - 1 := by omega
                  have hpp : (2 : ℤ) ^ 254 = 2 * 2 ^ 253 := by ring
                  linarith
                have hTeq : T' = T := OnCurveAt.eq hocI hp rfl rfl
                have hm0 : (0 : ℤ) ≤ 2 * z + (if bb then 1 else 0) := by
                  have : (0 : ℤ) ≤ (if bb then 1 else 0) := by cases bb <;> simp
                  linarith
                have hc := hcast _ hm0 hcl
                simp only [LeafInfo.netDelta, Leaf.scalarVar]
                rw [hTeq, ← hval, ← natCast_zsmul, hc]
            | cond bb T' => exact hr.elim
        | b128 s base corr =>
            cases info with
            | scalar L z bb T' =>
                obtain ⟨hL, hocI, h0, hlt, hval⟩ := hr
                subst hL
                have hcl : 2 * z + (if bb then 1 else 0) < 2 ^ 254 := by
                  have hb : (if bb then (1 : ℤ) else 0) ≤ 1 := by cases bb <;> simp
                  have hle : z ≤ 2 ^ 127 - 1 := by omega
                  have hpp : (2 : ℤ) ^ 128 = 2 * 2 ^ 127 := by ring
                  have hpow : (2 : ℤ) ^ 128 ≤ 2 ^ 254 := by norm_num
                  linarith
                have hTeq : T' = T := OnCurveAt.eq hocI hp rfl rfl
                have hm0 : (0 : ℤ) ≤ 2 * z + (if bb then 1 else 0) := by
                  have : (0 : ℤ) ≤ (if bb then 1 else 0) := by cases bb <;> simp
                  linarith
                have hc := hcast _ hm0 hcl
                simp only [LeafInfo.netDelta, Leaf.scalarVar]
                rw [hTeq, ← hval, ← natCast_zsmul, hc]
            | cond bb T' => exact hr.elim
        | b10 s base corr =>
            cases info with
            | scalar L z bb T' =>
                obtain ⟨hL, hocI, h0, hlt, hval⟩ := hr
                subst hL
                have hcl : 2 * z + (if bb then 1 else 0) < 2 ^ 254 := by
                  have hb : (if bb then (1 : ℤ) else 0) ≤ 1 := by cases bb <;> simp
                  have hle : z ≤ 2 ^ 9 - 1 := by omega
                  have hpp : (2 : ℤ) ^ 10 = 2 * 2 ^ 9 := by ring
                  have hpow : (2 : ℤ) ^ 10 ≤ 2 ^ 254 := by norm_num
                  linarith
                have hTeq : T' = T := OnCurveAt.eq hocI hp rfl rfl
                have hm0 : (0 : ℤ) ≤ 2 * z + (if bb then 1 else 0) := by
                  have : (0 : ℤ) ≤ (if bb then 1 else 0) := by cases bb <;> simp
                  linarith
                have hc := hcast _ hm0 hcl
                simp only [LeafInfo.netDelta, Leaf.scalarVar]
                rw [hTeq, ← hval, ← natCast_zsmul, hc]
            | cond bb T' => exact hr.elim
        | condAdd b base =>
            cases info with
            | scalar L z bb T' => exact hr.elim
            | cond bb T' =>
                obtain ⟨hocI, hbb⟩ := hr
                have hTeq : T' = T := OnCurveAt.eq hocI hp.1 rfl rfl
                simp only [LeafInfo.netDelta, Leaf.scalarVar]
                rw [hTeq, hbb, hbit]
                cases bb <;> simp
      simp only [List.map_cons, List.sum_cons]
      rw [hhead, ihv, publicMsm_cons]

/-- **The gadget reads at each chunk as `-(publicMsm) + h`.** `publicInputCommitFold_msm` with
its `hfull`/`hmsm` premises discharged publicly: the regime from `hregime` (`regimeFull_hfull`),
the MSM identity from `netDelta_sum_eq_publicMsm` (needing `hcast`, `hbit`; the canonical decode
is the ladder's own top-bit pin, no premise). The output reads unconditionally as
`-(Σ [scalarₗ]·baseₗ) + h`, the shape the wire's `publicCommitment` has. The clean public seam
the wire crossing consumes — no private `LeafInfo`/`LeafReads`. -/
private theorem publicInputCommitFold_reads (ci : Fin nc) {V : Valuation F}
    (blindingH : AffinePoint (FVar F)) (leaves : List (Leaf F nc))
    (Ts cps : List d.W.Point) (Hv : d.W.Point)
    (hcast : ∀ m : ℤ, 0 ≤ m → m < 2 ^ 254 → (ToNat.toNat ((m : F)) : ℤ) = m)
    (hbit : ∀ b : Bool, ToNat.toNat (bit b : F) = if b then 1 else 0)
    (h130 : 3 * 2 ^ 130 ≤ d.W.order) (h10 : 3 * 2 ^ 10 ≤ d.W.order)
    (hregime : ∀ leaf ∈ leaves, Leaf.regimeFull d V leaf)
    (hH : OnCurveAt d.W V blindingH Hv)
    (hpre : List.Forall₂ (LeafPre ci V) leaves Ts)
    (hcorr : List.Forall₂ (CorrPre ci V) leaves cps)
    (hscalar : leafHasScalar leaves)
    (hhon : ∀ leaf ∈ leaves, CorrHonest d ci V leaf) :
    ⦃⌜True⌝⦄
    publicInputCommitFold (S := Builder V (KimchiConstraint F)) blindingH leaves
    ⦃⇓ r _ => ⌜OnCurveAt d.W V r[ci] (-(publicMsm V leaves Ts) + Hv)⌝⦄ :=
  publicInputCommitFold_msm ci blindingH leaves Ts cps Hv (publicMsm V leaves Ts) h130 h10
    (fun _infos hr z bb T hmem => regimeFull_hfull hregime hr z bb T hmem)
    hH hpre hcorr hscalar hhon
    (fun _infos hr => netDelta_sum_eq_publicMsm hcast hbit hr hpre)

/-! ### The known-domain step gadget

The step verifier's commitment at a known domain emits in three phases: every leaf's bare ladder
first, in leaf order; then the ladder results summed left to right from the first; then one
constant, the summed shift corrections; then negate and add `h`. The corrections are constants
summed outside the circuit (no gates), so the gadget takes their sum as a cell (`corrSum`, a
`.const` at the deployed harness) instead of folding the leaves' correction cells as
`publicInputCommitFull` does. A `condAdd` leaf is a conditional add at its position in the
fold. The fold is seeded with the first leaf's ladder result and, when the first leaf is a
`condAdd`, with the first correction constant instead (`corrHead`) — dropping that leaf, a
quirk of the original the deployed step statement (all scalars) never reaches; the port is
literal and the read is stated for scalar-headed lists. -/

/-- Phase 1: every ladder, in leaf order; a `condAdd` leaf passes its bit and base through. -/
private def ladders [BasicSystem F S] [KimchiSystem F S] (ci : Fin nc) :
    List (Leaf F nc) →
      CircuitM F S (List (AffinePoint (FVar F) ⊕ (BoolVar F × AffinePoint (FVar F))))
  | [] => pure []
  | .full scalar base _ :: rest => do
      let l ← scaleFast2' 255 51 254 base[ci] scalar
      (Sum.inl l :: ·) <$> ladders ci rest
  | .b128 scalar base _ :: rest => do
      let l ← scaleFast2' 255 26 127 base[ci] scalar
      (Sum.inl l :: ·) <$> ladders ci rest
  | .b10 scalar base _ :: rest => do
      let l ← scaleFast2' 255 2 9 base[ci] scalar
      (Sum.inl l :: ·) <$> ladders ci rest
  | .condAdd b base :: rest => (Sum.inr (b, base[ci]) :: ·) <$> ladders ci rest

/-- Phase 2: the left fold of the phase-1 results onto `acc`: a ladder result is added, a
`condAdd` conditionally adds its base. -/
private def foldKnown [BasicSystem F S] [KimchiSystem F S] :
    AffinePoint (FVar F) → List (AffinePoint (FVar F) ⊕ (BoolVar F × AffinePoint (FVar F))) →
      CircuitM F S (AffinePoint (FVar F))
  | acc, [] => pure acc
  | acc, .inl pt :: rest => do
      let acc' ← addFast .checkFinite acc pt
      foldKnown acc'.p rest
  | acc, .inr (b, lp) :: rest => do
      let r ← addFast .checkFinite lp acc
      let acc' ← select b r.p acc
      foldKnown acc' rest

/-- Phases 2 and 3 on the phase-1 results: seed the fold with the first result (or `corrHead`
when it is a `condAdd`), add the constant correction sum, negate, add `h`. No leaves: `h`. -/
private def commitKnownTail [BasicSystem F S] [KimchiSystem F S]
    (blindingH corrHead corrSum : AffinePoint (FVar F)) :
    List (AffinePoint (FVar F) ⊕ (BoolVar F × AffinePoint (FVar F))) →
      CircuitM F S (AffinePoint (FVar F))
  | [] => pure blindingH
  | r :: rest => do
      let acc ← foldKnown (match r with | .inl r₀ => r₀ | .inr _ => corrHead) rest
      let acc' ← addFast .checkFinite acc corrSum
      (·.p) <$> addFast .checkFinite ⟨acc'.p.x, CVar.negate_ acc'.p.y⟩ blindingH

/-- The known-domain public-input commitment at one chunk: the ladders, then their fold with
the constant corrections, negated, plus `h`. -/
def publicInputCommitKnown [BasicSystem F S] [KimchiSystem F S] (ci : Fin nc)
    (blindingH corrHead corrSum : AffinePoint (FVar F)) (leaves : List (Leaf F nc)) :
    CircuitM F S (AffinePoint (FVar F)) := do
  let rs ← ladders ci leaves
  commitKnownTail blindingH corrHead corrSum rs

/-- The leaves start with a scalar leaf: the fold is seeded by its ladder. -/
def leafHeadScalar : List (Leaf F nc) → Prop
  | .full _ _ _ :: _ => True
  | .b128 _ _ _ :: _ => True
  | .b10 _ _ _ :: _ => True
  | _ => False

/-- A phase-1 result reads against its leaf's info: a ladder result as the bare ladder point
(in regime), a passed-through `condAdd` as its base and bit. -/
private def ItemReads (V : Valuation F) :
    AffinePoint (FVar F) ⊕ (BoolVar F × AffinePoint (FVar F)) → LeafInfo F d → Prop
  | .inl pt, .scalar L z bb T =>
      d.LadderRegime L (Pasta.Shifted.unshiftType1 L z) →
        OnCurveAt d.W V pt (LeafInfo.delta (.scalar L z bb T))
  | .inr (b, lp), .cond bb T => OnCurveAt d.W V lp T ∧ (↑b : CVar F).val V = bit bb
  | _, _ => False

/-- **Phase 1 reads.** Each leaf reads to an info and each result reads against it. -/
private theorem ladders_spec (ci : Fin nc) {V : Valuation F} :
    ∀ (leaves : List (Leaf F nc)) (Ts : List d.W.Point),
      List.Forall₂ (LeafPre ci V) leaves Ts →
      ⦃⌜True⌝⦄ ladders (S := Builder V (KimchiConstraint F)) ci leaves
      ⦃⇓ rs _ => ⌜∃ infos : List (LeafInfo F d), List.Forall₂ (LeafReads ci V) leaves infos ∧
        List.Forall₂ (ItemReads V) rs infos⌝⦄
  | [], [], .nil => by
      simp only [ladders]
      mvcgen
      exact ⟨[], .nil, .nil⟩
  | .full scalar base _ :: rest, T :: Ts, .cons hT hrest => by
      simp only [ladders]
      have hsf := scaleFast2'_spec (V := V) d 255 51 254 (by norm_num) (by norm_num) base[ci] scalar
      have ih := ladders_spec (V := V) ci rest Ts hrest
      mvcgen [hsf, ih]
      rename_i _ _ _ hsf' _ _
      rintro ⟨rest_infos, hrf, hir⟩
      obtain ⟨z, bb, h0, -, hlt, hval, hladder⟩ := hsf' T hT
      refine ⟨.scalar 255 z bb T :: rest_infos,
        .cons ⟨rfl, hT, h0, hlt (by norm_num), hval⟩ hrf, .cons ?_ hir⟩
      intro hreg
      simpa only [LeafInfo.delta, Pasta.Shifted.unshiftType2] using hladder hreg
  | .b128 scalar base _ :: rest, T :: Ts, .cons hT hrest => by
      simp only [ladders]
      have hsf := scaleFast2'_spec (V := V) d 255 26 127 (by norm_num) (by norm_num) base[ci] scalar
      have ih := ladders_spec (V := V) ci rest Ts hrest
      mvcgen [hsf, ih]
      rename_i _ _ _ hsf' _ _
      rintro ⟨rest_infos, hrf, hir⟩
      obtain ⟨z, bb, h0, hlt, -, hval, hladder⟩ := hsf' T hT
      refine ⟨.scalar 130 z bb T :: rest_infos, .cons ⟨rfl, hT, h0, hlt, hval⟩ hrf, .cons ?_ hir⟩
      intro hreg
      simpa only [LeafInfo.delta, Pasta.Shifted.unshiftType2] using hladder hreg
  | .b10 scalar base _ :: rest, T :: Ts, .cons hT hrest => by
      simp only [ladders]
      have hsf := scaleFast2'_spec (V := V) d 255 2 9 (by norm_num) (by norm_num) base[ci] scalar
      have ih := ladders_spec (V := V) ci rest Ts hrest
      mvcgen [hsf, ih]
      rename_i _ _ _ hsf' _ _
      rintro ⟨rest_infos, hrf, hir⟩
      obtain ⟨z, bb, h0, hlt, -, hval, hladder⟩ := hsf' T hT
      refine ⟨.scalar 10 z bb T :: rest_infos, .cons ⟨rfl, hT, h0, hlt, hval⟩ hrf, .cons ?_ hir⟩
      intro hreg
      simpa only [LeafInfo.delta, Pasta.Shifted.unshiftType2] using hladder hreg
  | .condAdd b base :: rest, T :: Ts, .cons hT hrest => by
      simp only [ladders]
      have ih := ladders_spec (V := V) ci rest Ts hrest
      mvcgen [ih]
      rintro ⟨rest_infos, hrf, hir⟩
      obtain ⟨hToc, bb, hbb⟩ := hT
      exact ⟨.cond bb T :: rest_infos, .cons ⟨hToc, hbb⟩ hrf, .cons ⟨hToc, hbb⟩ hir⟩

omit [ToNat F] in
/-- **Phase 2 reads.** With every result reading against its info and every info in regime,
the fold reads as the accumulator plus the sum of the infos' bare-ladder deltas. -/
private theorem foldKnown_spec {V : Valuation F} :
    ∀ (rs : List (AffinePoint (FVar F) ⊕ (BoolVar F × AffinePoint (FVar F))))
      (infos : List (LeafInfo F d)) (acc : AffinePoint (FVar F)),
      List.Forall₂ (ItemReads V) rs infos → (∀ i ∈ infos, i.regimeOK) →
      ⦃⌜True⌝⦄ foldKnown (S := Builder V (KimchiConstraint F)) acc rs
      ⦃⇓ r _ => ⌜∀ accv : d.W.Point, OnCurveAt d.W V acc accv →
        OnCurveAt d.W V r (accv + (infos.map LeafInfo.delta).sum)⌝⦄
  | [], [], acc, .nil, _ => by
      simp only [foldKnown]
      mvcgen
      intro accv hacc
      simpa using hacc
  | .inl pt :: rest, i :: is, acc, .cons hi hrest, hregs => by
      simp only [foldKnown]
      cases i with
      | cond bb T => simp only [ItemReads] at hi
      | scalar L z bb T =>
        have hi' : d.LadderRegime L (Pasta.Shifted.unshiftType1 L z) →
            OnCurveAt d.W V pt (LeafInfo.delta (.scalar L z bb T)) := by
          simpa only [ItemReads] using hi
        have hpt := hi' (hregs _ List.mem_cons_self)
        have hadd := addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
          d.two_torsion_free acc pt
        have ih := fun acc' => foldKnown_spec rest is acc' hrest
          (fun i hi => hregs i (List.mem_cons_of_mem _ hi))
        mvcgen [-Snarky.Kimchi.addFast_spec, hadd, ih]
        rename_i _ _ _ hadd' _ _
        intro ihpost accv hacc
        simp only [List.map_cons, List.sum_cons]
        rw [← add_assoc]
        exact ihpost _ (hadd' accv _ hacc hpt)
  | .inr (b, lp) :: rest, i :: is, acc, .cons hi hrest, hregs => by
      simp only [foldKnown]
      cases i with
      | scalar L z bb T => simp only [ItemReads] at hi
      | cond bb T =>
        obtain ⟨hlp, hbb⟩ : OnCurveAt d.W V lp T ∧ (↑b : CVar F).val V = bit bb := by
          simpa only [ItemReads] using hi
        have haddc := addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
          d.two_torsion_free lp acc
        have hsel := fun t => select_affinePoint_spec (V := V) (c := KimchiConstraint F) b t acc
        have ih := fun acc' => foldKnown_spec rest is acc' hrest
          (fun i hi => hregs i (List.mem_cons_of_mem _ hi))
        mvcgen [-Snarky.Kimchi.addFast_spec, haddc, hsel, ih]
        rename_i _ _ _ haddc' _ _ hsel' _ _
        intro ihpost accv hacc
        have hr := haddc' T accv hlp hacc
        have hsc := hsel' bb hbb (T + accv) accv hr hacc
        have hfinal := ihpost _ hsc
        simp only [List.map_cons, List.sum_cons, LeafInfo.delta]
        have key : accv + ((if bb then T else 0) + (List.map LeafInfo.delta is).sum)
            = (if bb then T + accv else accv) + (List.map LeafInfo.delta is).sum := by
          cases bb
          · rw [if_neg (by decide), if_neg (by decide), zero_add]
          · rw [if_pos rfl, if_pos rfl, add_comm T accv, add_assoc]
        rw [key]
        exact hfinal

omit [ToNat F] in
/-- **Phases 2 and 3 read at a ladder-headed result list**: the fold from the first ladder
result, plus the correction sum, negated, plus `h`. -/
private theorem commitKnownTail_inl_spec {V : Valuation F}
    (blindingH corrHead corrSum : AffinePoint (FVar F)) (Hv Cv : d.W.Point)
    (hH : OnCurveAt d.W V blindingH Hv) (hC : OnCurveAt d.W V corrSum Cv)
    (r₀ : AffinePoint (FVar F))
    (rest : List (AffinePoint (FVar F) ⊕ (BoolVar F × AffinePoint (FVar F))))
    (i₀ : LeafInfo F d) (is : List (LeafInfo F d)) (hr₀ : OnCurveAt d.W V r₀ i₀.delta)
    (hrest : List.Forall₂ (ItemReads V) rest is) (hregs : ∀ i ∈ is, i.regimeOK) :
    ⦃⌜True⌝⦄
    commitKnownTail (S := Builder V (KimchiConstraint F)) blindingH corrHead corrSum
      (.inl r₀ :: rest)
    ⦃⇓ r _ => ⌜OnCurveAt d.W V r (-(Cv + ((i₀ :: is).map LeafInfo.delta).sum) + Hv)⌝⦄ := by
  simp only [commitKnownTail]
  have hfold := foldKnown_spec rest is r₀ hrest hregs
  have hadd1 := fun a => addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
    d.two_torsion_free a corrSum
  have hadd2 := fun p => addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
    d.two_torsion_free p blindingH
  mvcgen [-Snarky.Kimchi.addFast_spec, hfold, hadd1, hadd2]
  rename_i _ _ _ hfold' _ _ hadd1' _ _
  intro hadd2'
  have hacc := hfold' _ hr₀
  have hacc' := hadd1' _ _ hacc hC
  have hneg := OnCurveAt.neg ⟨d.short.1, d.short.2.2.1⟩ hacc'
  have hout := hadd2' _ _ hneg hH
  simp only [List.map_cons, List.sum_cons]
  rwa [add_comm Cv]

omit [ToNat F] in
/-- **Phases 2 and 3 read**, for results headed by a ladder: `-(C + Σ deltas) + h`, with `C`
the correction sum's reading. Stated with the readings in the postcondition, the shape the
assembly's `mvcgen` takes; results not headed by a ladder are outside the read. -/
private theorem commitKnownTail_reads {V : Valuation F}
    (blindingH corrHead corrSum : AffinePoint (FVar F)) (Hv Cv : d.W.Point)
    (hH : OnCurveAt d.W V blindingH Hv) (hC : OnCurveAt d.W V corrSum Cv) :
    ∀ rs : List (AffinePoint (FVar F) ⊕ (BoolVar F × AffinePoint (FVar F))),
      ⦃⌜True⌝⦄ commitKnownTail (S := Builder V (KimchiConstraint F)) blindingH corrHead corrSum rs
      ⦃⇓ r _ => ⌜∀ infos : List (LeafInfo F d), List.Forall₂ (ItemReads V) rs infos →
        (∀ i ∈ infos, i.regimeOK) → (∃ r₀ rest, rs = .inl r₀ :: rest) →
        OnCurveAt d.W V r (-(Cv + (infos.map LeafInfo.delta).sum) + Hv)⌝⦄
  | [] => by
      rw [builder_spec_iff]
      intro _ _ _ _ _ ⟨_, _, h⟩
      exact absurd h (by simp)
  | .inr _ :: rest => by
      rw [builder_spec_iff]
      intro _ _ _ _ _ ⟨_, _, h⟩
      exact absurd h (by simp)
  | .inl r₀ :: rest => by
      rw [builder_spec_iff]
      intro nv hsat infos hir hregs _
      cases hir with
      | cons hi hrest =>
        rename_i i₀ is
        cases i₀ with
        | cond bb T => simp only [ItemReads] at hi
        | scalar L z bb T =>
          have hi' : d.LadderRegime L (Pasta.Shifted.unshiftType1 L z) →
              OnCurveAt d.W V r₀ (LeafInfo.delta (.scalar L z bb T)) := by
            simpa only [ItemReads] using hi
          have hr₀ := hi' (hregs _ List.mem_cons_self)
          exact (builder_spec_iff _ _).mp (commitKnownTail_inl_spec blindingH corrHead corrSum
            Hv Cv hH hC r₀ rest _ is hr₀ hrest
            (fun i hi => hregs i (List.mem_cons_of_mem _ hi))) nv hsat

/-- **The known-domain gadget computes the honest MSM.** For scalar-headed leaves, with the
bases reading as `Ts`, the correction sum as `Cv` and `h` as `Hv`: the output reads as
`-(Σ netDelta) + h` under the seed condition `Cv = Σ corrDelta`, the same shape as
`publicInputCommitFold_spec`. -/
theorem publicInputCommitKnown_spec (ci : Fin nc) {V : Valuation F}
    (blindingH corrHead corrSum : AffinePoint (FVar F)) (leaves : List (Leaf F nc))
    (Ts : List d.W.Point) (Hv Cv : d.W.Point)
    (hH : OnCurveAt d.W V blindingH Hv) (hC : OnCurveAt d.W V corrSum Cv)
    (hpre : List.Forall₂ (LeafPre ci V) leaves Ts) (hhead : leafHeadScalar leaves) :
    ⦃⌜True⌝⦄
    publicInputCommitKnown (S := Builder V (KimchiConstraint F)) ci blindingH corrHead corrSum
      leaves
    ⦃⇓ r _ => ⌜∃ infos : List (LeafInfo F d), List.Forall₂ (LeafReads ci V) leaves infos ∧
      (Cv = (infos.map LeafInfo.corrDelta).sum → (∀ i ∈ infos, i.regimeOK) →
        OnCurveAt d.W V r (-(infos.map LeafInfo.netDelta).sum + Hv))⌝⦄ := by
  simp only [publicInputCommitKnown]
  have hl := ladders_spec (V := V) ci leaves Ts hpre
  have ht := commitKnownTail_reads (V := V) blindingH corrHead corrSum Hv Cv hH hC
  mvcgen [hl, ht]
  rename_i _ rs _ hl' _ _
  intro ht'
  obtain ⟨infos, hrf, hir⟩ := hl'
  refine ⟨infos, hrf, fun hCeq hregs => ?_⟩
  -- a scalar head reads to a scalar info, whose result is a ladder
  have hshape : ∃ r₀ rest, rs = .inl r₀ :: rest := by
    cases leaves with
    | nil => exact hhead.elim
    | cons leaf ls =>
      cases hrf with
      | cons hr hrs =>
        rename_i i₀ is
        cases hir with
        | cons hi his =>
          rename_i r₀ rest
          cases r₀ with
          | inl pt => exact ⟨pt, rest, rfl⟩
          | inr q =>
            cases i₀ with
            | scalar L z bb T => simp only [ItemReads] at hi
            | cond bb T =>
              cases leaf with
              | condAdd _ _ => exact hhead.elim
              | full _ _ _ => simp only [LeafReads] at hr
              | b128 _ _ _ => simp only [LeafReads] at hr
              | b10 _ _ _ => simp only [LeafReads] at hr
  have h := ht' infos hir hregs hshape
  rw [hCeq, LeafInfo.sum_corrDelta_add_delta] at h
  exact h

/-- **The known-domain gadget reads as `-(publicMsm) + h`.** `publicInputCommitKnown_spec` with
its seed (from honest corrections, `corrSum_eq`, and the correction sum reading as `Σ cps`) and
regime (`leafReads_regimeOK_all` from the width bounds and the full-width regime premise)
discharged, and the net-delta sum identified with `publicMsm` — the same public seam as
`publicInputCommitFold_reads`, so the wire crossing consumes either gadget. -/
theorem publicInputCommitKnown_reads (ci : Fin nc) {V : Valuation F}
    (blindingH corrHead corrSum : AffinePoint (FVar F)) (leaves : List (Leaf F nc))
    (Ts cps : List d.W.Point) (Hv : d.W.Point)
    (hcast : ∀ m : ℤ, 0 ≤ m → m < 2 ^ 254 → (ToNat.toNat ((m : F)) : ℤ) = m)
    (hbit : ∀ b : Bool, ToNat.toNat (bit b : F) = if b then 1 else 0)
    (h130 : 3 * 2 ^ 130 ≤ d.W.order) (h10 : 3 * 2 ^ 10 ≤ d.W.order)
    (hregime : ∀ leaf ∈ leaves, Leaf.regimeFull d V leaf)
    (hH : OnCurveAt d.W V blindingH Hv)
    (hpre : List.Forall₂ (LeafPre ci V) leaves Ts)
    (hcorr : List.Forall₂ (CorrPre ci V) leaves cps)
    (hC : OnCurveAt d.W V corrSum cps.sum)
    (hhead : leafHeadScalar leaves)
    (hhon : ∀ leaf ∈ leaves, CorrHonest d ci V leaf) :
    ⦃⌜True⌝⦄
    publicInputCommitKnown (S := Builder V (KimchiConstraint F)) ci blindingH corrHead corrSum
      leaves
    ⦃⇓ r _ => ⌜OnCurveAt d.W V r (-(publicMsm V leaves Ts) + Hv)⌝⦄ := by
  refine builder_spec_imp _ _ _
    (publicInputCommitKnown_spec ci blindingH corrHead corrSum leaves Ts Hv cps.sum hH hC hpre
      hhead) fun r hr => ?_
  obtain ⟨infos, hff, himp⟩ := hr
  rw [← netDelta_sum_eq_publicMsm hcast hbit hff hpre]
  exact himp (corrSum_eq hcorr hff hhon)
    (leafReads_regimeOK_all h130 h10 hff (regimeFull_hfull hregime hff))

/-! ### The ladders' scalar bounds, for any bases -/

/-- A leaf's scalar as its ladder bounds it: the full leaf's half below `2^253` (the top-bit
pin), the 128-bit leaf's below `2^127`, the 10-bit leaf's below `2^9`. -/
def Leaf.Bound (V : Valuation F) : Leaf F nc → Prop
  | .full s _ _ => CellBound V 253 s
  | .b128 s _ _ => CellBound V 127 s
  | .b10 s _ _ => CellBound V 9 s
  | .condAdd _ _ => True

open Std.Do in
/-- One leaf's ladder bounds its scalar, whatever its base reads as. -/
private theorem leafStep_bound (ci : Fin nc) {V : Valuation F} (acc : AffinePoint (FVar F)) :
    ∀ leaf : Leaf F nc, ⦃⌜True⌝⦄ leafStep (S := Builder V (KimchiConstraint F)) ci acc leaf
      ⦃⇓ _ _ => ⌜leaf.Bound V⌝⦄
  | .full scalar base _ => by
      simp only [leafStep]
      have hsf := scaleFast2'_spec_scalar (V := V) 255 51 254 (by norm_num) base[ci] scalar
      have hadd := fun l => builder_spec_true
        (addFast (c := Builder V (KimchiConstraint F)) .checkFinite acc l)
      mvcgen [-Snarky.Kimchi.addFast_spec, hsf, hadd]
      rename_i _ _ _ hsf' _ _
      obtain ⟨z, bb, h0, -, hlt, hval⟩ := hsf'
      exact ⟨z, bb, h0, hlt (by norm_num), hval⟩
  | .b128 scalar base _ => by
      simp only [leafStep]
      have hsf := scaleFast2'_spec_scalar (V := V) 255 26 127 (by norm_num) base[ci] scalar
      have hadd := fun l => builder_spec_true
        (addFast (c := Builder V (KimchiConstraint F)) .checkFinite acc l)
      mvcgen [-Snarky.Kimchi.addFast_spec, hsf, hadd]
      rename_i _ _ _ hsf' _ _
      obtain ⟨z, bb, h0, hlt, -, hval⟩ := hsf'
      exact ⟨z, bb, h0, hlt, hval⟩
  | .b10 scalar base _ => by
      simp only [leafStep]
      have hsf := scaleFast2'_spec_scalar (V := V) 255 2 9 (by norm_num) base[ci] scalar
      have hadd := fun l => builder_spec_true
        (addFast (c := Builder V (KimchiConstraint F)) .checkFinite acc l)
      mvcgen [-Snarky.Kimchi.addFast_spec, hsf, hadd]
      rename_i _ _ _ hsf' _ _
      obtain ⟨z, bb, h0, hlt, -, hval⟩ := hsf'
      exact ⟨z, bb, h0, hlt, hval⟩
  | .condAdd b base => by
      exact builder_spec_true _

open Std.Do in
/-- The fold's ladders bound every leaf's scalar, at a first chunk. -/
private theorem foldChunks_bound (hnc : 0 < nc) {V : Valuation F} :
    ∀ (acc : Vector (AffinePoint (FVar F)) nc) (leaves : List (Leaf F nc)),
      ⦃⌜True⌝⦄ foldChunks (S := Builder V (KimchiConstraint F)) acc leaves
      ⦃⇓ _ _ => ⌜∀ l ∈ leaves, l.Bound V⌝⦄
  | acc, [] => by
      simp only [foldChunks]
      mvcgen
      simp
  | acc, leaf :: rest => by
      simp only [foldChunks]
      have hc := chunkwise_at (V := V) (fun c => leafStep c acc[c] leaf) ⟨0, hnc⟩
        (fun _ => leaf.Bound V) (leafStep_bound ⟨0, hnc⟩ acc[0] leaf)
      have ih := fun acc' => foldChunks_bound hnc (V := V) acc' rest
      mvcgen [hc, ih]
      rename_i _ _ hl _ _
      intro hr l hl'
      rcases List.mem_cons.mp hl' with rfl | hm
      · exact hl
      · exact hr l hm

open Std.Do in
/-- The fold, from any corrections' sum, bounds every leaf's scalar. -/
private theorem publicInputCommitFold_bound (hnc : 0 < nc) {V : Valuation F}
    (blindingH : AffinePoint (FVar F)) (leaves : List (Leaf F nc)) :
    ⦃⌜True⌝⦄ publicInputCommitFold (S := Builder V (KimchiConstraint F)) blindingH leaves
    ⦃⇓ _ _ => ⌜∀ l ∈ leaves, l.Bound V⌝⦄ := by
  simp only [publicInputCommitFold, publicInputCommitChunks]
  have hs := builder_spec_true
    (sumCorrectionsHead (S := Builder V (KimchiConstraint F)) leaves)
  have hf := fun acc => foldChunks_bound hnc (V := V) acc leaves
  have hc := fun (acc : Vector (AffinePoint (FVar F)) nc) => builder_spec_true
    (chunkwise (S := Builder V (KimchiConstraint F)) fun c =>
      (·.p) <$> addFast .checkFinite ⟨acc[c].x, CVar.negate_ acc[c].y⟩ blindingH)
  mvcgen [hs, hf, hc]

open Std.Do in
/-- `publicInputCommitFull` bounds every leaf's scalar and makes every bit boolean, whatever
the bases read as. -/
theorem publicInputCommitFull_bound (hnc : 0 < nc) {V : Valuation F}
    (blindingH : AffinePoint (FVar F)) (leaves : List (Leaf F nc)) :
    ⦃⌜True⌝⦄ publicInputCommitFull (S := Builder V (KimchiConstraint F)) blindingH leaves
    ⦃⇓ _ _ => ⌜∀ l ∈ leaves, l.Bound V ∧ l.bitBoolean V⌝⦄ := by
  simp only [publicInputCommitFull]
  have hb := constrainBits_boolean (V := V) leaves
  have hf := publicInputCommitFold_bound hnc (V := V) blindingH leaves
  mvcgen [hb, hf]
  rename_i _ _ hb' _ _
  exact fun hf' l hl => ⟨hf' l hl, hb' l hl⟩

end Fold

/-! ## The wire crossing

The gadget reads land at `-(publicMsm) + h` over Mathlib's point group of the commitment
curve; this section crosses that to the wire verifier's `publicCommitment` on the commitment
curve, generically over a `PastaShape`, instantiated at Vesta (`pastaShapeVesta`) and Pallas
(`pastaShapePallas`). -/

section XhatCrossing

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass

section Crossing

variable {G : Type} [AddCommGroup G]

/-- **Negating an `ℕ`-scaling in a group killed by `n` is the `ZMod n`-negated scalar's
scaling.** The MSM's `-(k·X)` is `((-k : ZMod n)).val · X` — the group's characteristic is the
scalar order, so the `ℕ → ZMod n` reduction (`Pasta.zsmul_eq_val_nsmul`) and the negation
commute exactly. -/
private theorem neg_nsmul_eq (n : ℕ) [NeZero n] [Module (ZMod n) G] (k : ℕ) (X : G) :
    -((k : ℕ) • X) = ((-(k : ZMod n)).val : ℕ) • X := by
  rw [← natCast_zsmul, ← neg_zsmul, Pasta.zsmul_eq_val_nsmul n]
  simp only [Int.cast_neg, Int.cast_natCast]

/-- **The negated `publicMsm` term list is the wire's negated-scalar term list.** Termwise
`-((f aₗ) · Tₗ) = ((-↑(f aₗ)).val · Tₗ)` over `neg_nsmul_eq`, lifted over the (leaf, base) list —
the shape `equivPoint_publicCommitment` produces once the scalars line up. -/
private theorem neg_publicMsm_sum (n : ℕ) [NeZero n] [Module (ZMod n) G] {A : Type}
    (f : A → ℕ) (l : List (A × G)) :
    -(l.map (fun p => f p.1 • p.2)).sum
      = (l.map (fun p => ((-(↑(f p.1) : ZMod n)).val : ℕ) • p.2)).sum := by
  induction l with
  | nil => simp
  | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons, neg_add]
      rw [neg_nsmul_eq n, ih]

end Crossing

/-- **`publicCommitment`'s chunk, transported through an additive equivalence on the point
group.** The wire's negated-scalar MSM with each Lagrange base mapped over, plus `h`. Pure
additive-equiv algebra over `publicCommitment_eq_sum`; the wire crossing instantiates it at
`SWPoint.equivPoint`. -/
theorem equivPoint_publicCommitment {C : Bulletproof.Ipa.KimchiCurve} {nc : ℕ} {G : Type}
    [AddCommGroup G] (e : C.Point ≃+ G) (σ : Bulletproof.SRS C.Point)
    (cvk : Kimchi.Verifier.KimchiVK C nc)
    (pub : Array C.ScalarField) (ci : Fin nc) (hne : pub.size ≠ 0) :
    e ((Kimchi.Verifier.publicCommitment C σ cvk pub)[ci])
      = (((cvk.lagrangeBasis.extract 0 pub.size).zip pub).toList.map
          (fun Pp => (-Pp.2).val • e (Pp.1[ci]))).sum + e σ.h := by
  rw [Kimchi.Verifier.publicCommitment_eq_sum C σ cvk pub hne]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, map_add, map_list_sum, List.map_map,
    Function.comp_def, map_nsmul]

/-! ### The gadget reads as `publicCommitment` -/

section Generic

variable {F : Type} [Field F] [DecidableEq F] [ToNat F] {nc : ℕ}

/-- The public input the leaves commit to, as the wire verifier's scalar array on `C`: each
scalar leaf contributes its circuit-field scalar's value cast to the scalar field — the
group-order reduction the MSM performs on the in-circuit scalar — and each `condAdd` its bit.
The `ℕ → ZMod C.scalar` cast IS the reduction, so no slack predicate is needed. -/
def pubOf (C : Bulletproof.Ipa.KimchiCurve) (V : Valuation F) (leaves : List (Leaf F nc)) :
    Array C.ScalarField :=
  (leaves.map (fun leaf => ((ToNat.toNat (leaf.scalarVar.val V) : ℕ) : C.ScalarField))).toArray

/-- One leaf's chunk base at `ci`. -/
def leafBaseAt (ci : Fin nc) : Leaf F nc → AffinePoint (FVar F)
  | .full _ base _ => base[ci]
  | .b128 _ base _ => base[ci]
  | .b10 _ base _ => base[ci]
  | .condAdd _ base => base[ci]

omit [DecidableEq F] in
/-- `pubOf` has one entry per leaf. -/
theorem pubOf_size (C : Bulletproof.Ipa.KimchiCurve) (V : Valuation F)
    (leaves : List (Leaf F nc)) : (pubOf C V leaves).size = leaves.length := by simp [pubOf]

omit [ToNat F] in
/-- A leaf's `LeafPre` reading names its base cell on the curve at that point — the on-curve
half of `LeafPre` for every leaf shape (`condAdd` also carries a bit clause). -/
private theorem leafPre_onCurve {d : HasCurve F} (ci : Fin nc) (V : Valuation F)
    (leaf : Leaf F nc) (T : d.W.Point) (h : LeafPre ci V leaf T) :
    OnCurveAt d.W V (leafBaseAt ci leaf) T := by
  cases leaf <;> first | exact h | exact h.1

/-- Two chunk vectors of cells read the same under `V`. -/
private def SameCells (V : Valuation F) (a b : Vector (AffinePoint (FVar F)) nc) : Prop :=
  ∀ i : Fin nc, a[i].x.val V = b[i].x.val V ∧ a[i].y.val V = b[i].y.val V

/-- `l'` is `l` sealed: the same kind and scalar, its cells reading as `l`'s. -/
private def Leaf.SealedOf (V : Valuation F) : Leaf F nc → Leaf F nc → Prop
  | .full s b c, .full s' b' c' => s' = s ∧ SameCells V b' b ∧ SameCells V c' c
  | .b128 s b c, .b128 s' b' c' => s' = s ∧ SameCells V b' b ∧ SameCells V c' c
  | .b10 s b c, .b10 s' b' c' => s' = s ∧ SameCells V b' b ∧ SameCells V c' c
  | .condAdd b base, .condAdd b' base' => b' = b ∧ base' = base
  | _, _ => False

omit [ToNat F] in
private theorem onCurveAt_of_same {W : WeierstrassCurve.Affine F} {V : Valuation F}
    {p q : AffinePoint (FVar F)} {P : W.Point} (hx : p.x.val V = q.x.val V)
    (hy : p.y.val V = q.y.val V) (h : OnCurveAt W V q P) : OnCurveAt W V p P := by
  unfold OnCurveAt at h ⊢
  rwa [hx, hy]

omit [ToNat F] in
/-- The sealing walk reads each leaf as its sealed copy, and makes a boolean leaf's bit
boolean. -/
private theorem sealLeaf_spec {V : Valuation F} (leaf : Leaf F nc) :
    ⦃⌜True⌝⦄ sealLeaf (S := Builder V (KimchiConstraint F)) leaf
    ⦃⇓ r _ => ⌜Leaf.SealedOf V leaf r ∧ leaf.bitBoolean V⌝⦄ := by
  have hm := fun v : Vector (AffinePoint (FVar F)) nc =>
    builder_spec_vector_mapM_get (sealPoint (c := Builder V (KimchiConstraint F)))
      (fun q r => r.x.val V = q.x.val V ∧ r.y.val V = q.y.val V) sealPoint_spec v
  cases leaf with
  | condAdd b base =>
      simp only [sealLeaf]
      mvcgen
      rename_i hb
      refine ⟨⟨rfl, rfl⟩, ?_⟩
      rcases (LawfulBasicSystem.holds_boolean V (↑b : CVar F)).mp hb with h | h
      · exact ⟨false, by simpa [bit] using h⟩
      · exact ⟨true, by simpa [bit] using h⟩
  | full s base corr =>
      simp only [sealLeaf]
      have hc := hm corr
      have hb := hm base
      mvcgen [hc, hb]
  | b128 s base corr =>
      simp only [sealLeaf]
      have hc := hm corr
      have hb := hm base
      mvcgen [hc, hb]
  | b10 s base corr =>
      simp only [sealLeaf]
      have hc := hm corr
      have hb := hm base
      mvcgen [hc, hb]

omit [DecidableEq F] [ToNat F] in
private theorem Leaf.SealedOf.scalarVar {V : Valuation F} :
    ∀ {l l' : Leaf F nc}, Leaf.SealedOf V l l' → l'.scalarVar = l.scalarVar
  | .full .., .full .., h | .b128 .., .b128 .., h | .b10 .., .b10 .., h
  | .condAdd .., .condAdd .., h => by simp only [Leaf.scalarVar, h.1]

omit [DecidableEq F] [ToNat F] in
private theorem Leaf.SealedOf.bound {V : Valuation F} :
    ∀ {l l' : Leaf F nc}, Leaf.SealedOf V l l' → l'.Bound V → l.Bound V
  | .full .., .full .., h | .b128 .., .b128 .., h | .b10 .., .b10 .., h => by
      simp only [Leaf.Bound, h.1, imp_self]
  | .condAdd .., .condAdd .., _ => id

omit [ToNat F] in
private theorem Leaf.SealedOf.baseAt {W : WeierstrassCurve.Affine F} {V : Valuation F}
    (ci : Fin nc) {P : W.Point} :
    ∀ {l l' : Leaf F nc}, Leaf.SealedOf V l l' →
      OnCurveAt W V (leafBaseAt ci l) P → OnCurveAt W V (leafBaseAt ci l') P
  | .full .., .full .., h | .b128 .., .b128 .., h | .b10 .., .b10 .., h =>
      onCurveAt_of_same (h.2.1 ci).1 (h.2.1 ci).2
  | .condAdd .., .condAdd .., h => by simp only [leafBaseAt, h.2]; exact id

omit [ToNat F] in
private theorem Leaf.SealedOf.leafPre {d : HasCurve F} {V : Valuation F} (ci : Fin nc)
    {T : d.W.Point} :
    ∀ {l l' : Leaf F nc}, Leaf.SealedOf V l l' → LeafPre ci V l T → LeafPre ci V l' T
  | .full .., .full .., h | .b128 .., .b128 .., h | .b10 .., .b10 .., h =>
      onCurveAt_of_same (h.2.1 ci).1 (h.2.1 ci).2
  | .condAdd .., .condAdd .., h => by simp only [LeafPre, h.1, h.2]; exact id

omit [ToNat F] in
private theorem Leaf.SealedOf.corrPre {d : HasCurve F} {V : Valuation F} (ci : Fin nc)
    {cp : d.W.Point} :
    ∀ {l l' : Leaf F nc}, Leaf.SealedOf V l l' → CorrPre ci V l cp → CorrPre ci V l' cp
  | .full .., .full .., h | .b128 .., .b128 .., h | .b10 .., .b10 .., h =>
      onCurveAt_of_same (h.2.2 ci).1 (h.2.2 ci).2
  | .condAdd .., .condAdd .., _ => id

omit [ToNat F] in
private theorem Leaf.SealedOf.corrHonest {d : HasCurve F} {V : Valuation F} (ci : Fin nc) :
    ∀ {l l' : Leaf F nc}, Leaf.SealedOf V l l' → CorrHonest d ci V l → CorrHonest d ci V l'
  | .full .., .full .., h, hh | .b128 .., .b128 .., h, hh | .b10 .., .b10 .., h, hh =>
      fun T hT => onCurveAt_of_same (h.2.2 ci).1 (h.2.2 ci).2
        (hh T (onCurveAt_of_same (h.2.1 ci).1.symm (h.2.1 ci).2.symm hT))
  | .condAdd .., .condAdd .., _, _ => trivial

omit [ToNat F] in
private theorem Leaf.SealedOf.hasScalar {V : Valuation F} {ls ls' : List (Leaf F nc)}
    (hs : List.Forall₂ (Leaf.SealedOf V) ls ls') (h : leafHasScalar ls) : leafHasScalar ls' := by
  induction hs with
  | nil => exact h
  | @cons l l' _ _ hl _ ih =>
      cases l <;> cases l' <;> simp_all [Leaf.SealedOf, leafHasScalar]

omit [DecidableEq F] [ToNat F] in
/-- A pointwise relation carries across the sealing. -/
private theorem Leaf.SealedOf.forall₂ {β : Type} {V : Valuation F} {R : Leaf F nc → β → Prop}
    (hR : ∀ {l l' b}, Leaf.SealedOf V l l' → R l b → R l' b) {ls ls' : List (Leaf F nc)}
    (hs : List.Forall₂ (Leaf.SealedOf V) ls ls') :
    ∀ {bs : List β}, List.Forall₂ R ls bs → List.Forall₂ R ls' bs := by
  induction hs with
  | nil => exact id
  | cons hl _ ih =>
      intro bs h
      cases h with
      | cons hr hrs => exact .cons (hR hl hr) (ih hrs)

omit [DecidableEq F] [ToNat F] in
/-- A leafwise property carries across the sealing. -/
private theorem Leaf.SealedOf.forall {V : Valuation F} {P : Leaf F nc → Prop}
    (hP : ∀ {l l'}, Leaf.SealedOf V l l' → P l → P l') {ls ls' : List (Leaf F nc)}
    (hs : List.Forall₂ (Leaf.SealedOf V) ls ls') (h : ∀ l ∈ ls, P l) : ∀ l ∈ ls', P l := by
  induction hs with
  | nil => exact h
  | cons hl _ ih =>
      intro l hmem
      rcases List.mem_cons.1 hmem with rfl | hmem
      · exact hP hl (h _ (List.mem_cons_self ..))
      · exact ih (fun l hl' => h l (List.mem_cons_of_mem _ hl')) l hmem

open Std.Do in
/-- `publicInputCommitSealed` bounds every leaf's scalar and makes every bit boolean, whatever
the bases read as. -/
theorem publicInputCommitSealed_bound (hnc : 0 < nc) {V : Valuation F}
    (blindingH : AffinePoint (FVar F)) (leaves : List (Leaf F nc)) :
    ⦃⌜True⌝⦄ publicInputCommitSealed (S := Builder V (KimchiConstraint F)) blindingH leaves
    ⦃⇓ _ _ => ⌜∀ l ∈ leaves, l.Bound V ∧ l.bitBoolean V⌝⦄ := by
  simp only [publicInputCommitSealed]
  have hs := builder_spec_mapM (V := V) (c := KimchiConstraint F)
    (sealLeaf (S := Builder V (KimchiConstraint F)))
    (fun r l => Leaf.SealedOf V l r ∧ l.bitBoolean V) id sealLeaf_spec leaves
  have hf := fun rs => publicInputCommitFold_bound hnc (V := V) blindingH rs
  mvcgen [hs, hf]
  rename_i rs _ hrs _ _
  intro hb l hl
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
  have hlen : rs.length = leaves.length := by simpa using hrs.length_eq
  have h := (List.forall₂_iff_get.mp hrs).2 i (by omega) (by simpa using hi)
  simp only [List.get_eq_getElem, List.getElem_map, id] at h
  exact ⟨Leaf.SealedOf.bound h.1 (hb _ (List.getElem_mem _)), h.2⟩

/-- **The wire's negated-scalar MSM term list equals the crossed `publicMsm` term list.** The
walk-order correspondence: at each `i`, the wire pairs Lagrange base `i` with `pubOf`'s `i`-th
scalar, and the gadget pairs leaf `i`'s base — read as that same Lagrange base by `htie` — with
its own scalar. The circuit-field → scalar-field reduction is the cast, so the scalars agree. -/
private theorem crossing_list {C : Bulletproof.Ipa.KimchiCurve} {d : HasCurve F}
    (e : C.Point ≃+ d.W.Point) (ci : Fin nc) (V : Valuation F)
    (cvk : Kimchi.Verifier.KimchiVK C nc)
    (leaves : List (Leaf F nc)) (Ts : List d.W.Point)
    (hlen : Ts.length = leaves.length)
    (hsize : leaves.length ≤ cvk.lagrangeBasis.size)
    (htie : ∀ (i : ℕ) (hi : i < leaves.length),
      Ts[i]'(hlen ▸ hi) = e ((cvk.lagrangeBasis[i]'(lt_of_lt_of_le hi hsize))[ci])) :
    ((cvk.lagrangeBasis.extract 0 (pubOf C V leaves).size).zip (pubOf C V leaves)).toList.map
        (fun Pp => (-Pp.2).val • e (Pp.1[ci]))
      = (leaves.zip Ts).map
          (fun p => ((-(↑(ToNat.toNat (p.1.scalarVar.val V)) : C.ScalarField)).val : ℕ) • p.2) := by
  simp only [pubOf]
  apply List.ext_getElem
  · simp only [List.length_map, Array.length_toList, Array.size_zip, Array.size_extract,
      List.size_toArray, List.length_zip, Nat.sub_zero, hlen, Nat.min_self,
      Nat.min_eq_left hsize]
  · intro i h1 h2
    have hil : i < leaves.length := by
      simp only [List.length_map, List.length_zip, hlen, Nat.min_self] at h2; exact h2
    simp only [List.getElem_map, Array.getElem_toList, Array.getElem_zip, Array.getElem_extract,
      List.getElem_zip, List.getElem_toArray, Nat.zero_add]
    rw [htie i hil]

end Generic

section SideFacts

variable {C : Bulletproof.Ipa.KimchiCurve}

/-- The cast premise of the gadget reads at a side: a `2^254`-bounded integer reads back from
the base field. -/
private theorem xhatSide_cast (s : PastaShape C) :
    ∀ m : ℤ, 0 ≤ m → m < 2 ^ 254 → (ToNat.toNat ((m : C.BaseField)) : ℤ) = m := by
  haveI : NeZero C.base := ⟨(Fact.out : C.base.Prime).ne_zero⟩
  intro m hm0 hmlt
  exact toNat_intCast_of_lt C.base hm0 (lt_of_lt_of_le hmlt (by exact_mod_cast s.base_big.le))

/-- The bit premise of the gadget reads: `bit b` reads as `0`/`1`. -/
private theorem xhatSide_bit (_s : PastaShape C) :
    ∀ b : Bool, ToNat.toNat (bit b : C.BaseField) = if b then 1 else 0 := by
  haveI : Fact (1 < C.base) := ⟨(Fact.out : C.base.Prime).one_lt⟩
  intro b
  cases b
  · show ZMod.val (bit false : ZMod C.base) = 0; simp [bit]
  · show ZMod.val (bit true : ZMod C.base) = 1; simp [bit, ZMod.val_one]

/-- The narrow ladders (`L ≤ 130`) are in the subwrap regime: the order has 255 bits. -/
theorem PastaShape.order_big (s : PastaShape C) : 3 * 2 ^ 130 ≤ s.d.W.order := by
  rw [show s.d.W.order = C.scalar from C.order_eq]
  exact le_trans (by norm_num) s.scalar_lo.le

/-- **The pinned full-leaf ladder is in regime.** With the order `p` in
`(2^254, 2^254 + 2^253)`, for `0 ≤ z < 2^253` the top `2z + 2^255 + 1` is below `2^256`, which is
below `4p - 4`: no accumulator of the ladder meets `±T`, whatever the leaf. -/
theorem PastaShape.regime (s : PastaShape C) {nc : ℕ} (V : Valuation C.BaseField)
    (leaf : Leaf C.BaseField nc) : Leaf.regimeFull s.d V leaf := by
  cases leaf with
  | full sc base corr =>
      intro z bb h0 hlt _
      have hlo : (2 : ℤ) ^ 254 < C.scalar := by exact_mod_cast s.scalar_lo
      refine Or.inr ⟨?_, ?_, ?_⟩ <;> rw [show s.d.W.order = C.scalar from C.order_eq]
      · simpa using s.scalar_lo
      · exact lt_trans (by norm_num) s.scalar_lo
      · simp only [Pasta.Shifted.unshiftType1]
        have h253 : (2 : ℤ) ^ 253 * 2 = 2 ^ 254 := by norm_num
        have h255 : (2 : ℤ) ^ 255 = 2 * 2 ^ 254 := by norm_num
        linarith
  | _ => trivial

end SideFacts

section Binding

variable {C : Bulletproof.Ipa.KimchiCurve} {nc : ℕ}

/-- A circuit's commitment tables: per public-input scalar its Lagrange base and its shift
correction, chunked, and the correction seed and sum the known-domain fold takes as
constants. -/
structure XhatTable (F : Type) [Field F] (nc : ℕ) where
  /-- The Lagrange bases, one per scalar. -/
  bases : List (Vector (AffinePoint (FVar F)) nc)
  /-- The shift corrections, one per scalar. -/
  corrs : List (Vector (AffinePoint (FVar F)) nc)
  /-- The correction seed of the known-domain fold. -/
  corrHead : Vector (AffinePoint (FVar F)) nc
  /-- The correction sum of the known-domain fold. -/
  corrSum : Vector (AffinePoint (FVar F)) nc

/-- The binding the deferred packing item discharges — everything the faithfulness read needs
of the outside world, in public terms (no `LeafInfo`/`LeafReads`). The scalar-side alias
(circuit field → scalar field) is absorbed into `pubOf`, and the fold premises
(`pre`/`corr`/`hon`) are exactly the gadget reads'; the regime holds for every leaf
(`PastaShape.regime`). `Ts` are the leaves' base points, `cps`
their correction points. The gadget-specific seed facts (`leafHasScalar` for the wrap fold,
`leafHeadScalar` and the constant correction sum for the known-domain fold) stay beside the
read they serve. -/
structure XhatBinding (s : PastaShape C) (ci : Fin nc) (V : Valuation C.BaseField)
    (σ : Bulletproof.SRS C.Point) (cvk : Kimchi.Verifier.KimchiVK C nc)
    (blindingH : AffinePoint (FVar C.BaseField)) (leaves : List (Leaf C.BaseField nc))
    (Ts cps : List s.d.W.Point) : Prop where
  /-- The blinding cell reads as the verifier's SRS blinding `σ.h`, crossed to the point group. -/
  blinding : OnCurveAt s.d.W V blindingH (SWPoint.equivPoint C.E σ.h)
  /-- Each leaf reads its base cell as a curve point `Ts[i]` (and its bit, for `condAdd`). -/
  pre : List.Forall₂ (LeafPre ci V) leaves Ts
  /-- Each leaf's correction cell reads as `cps[i]`. -/
  corr : List.Forall₂ (CorrPre ci V) leaves cps
  /-- Each leaf's correction is the honest shift `-(2^L)·base`. -/
  hon : ∀ leaf ∈ leaves, CorrHonest s.d ci V leaf
  /-- There are at least as many Lagrange bases as public-input leaves. -/
  hsize : leaves.length ≤ cvk.lagrangeBasis.size
  /-- Each leaf's chunk base reads as the verifier's Lagrange base at that index — the walk-order
  tie the packing item owns. -/
  bases : ∀ (i : ℕ) (hi : i < leaves.length),
    OnCurveAt s.d.W V (leafBaseAt ci leaves[i])
      (SWPoint.equivPoint C.E ((cvk.lagrangeBasis[i]'(lt_of_lt_of_le hi hsize))[ci]))

/-- **The wire's `publicCommitment`, crossed, is `-(publicMsm) + h`.** The shared half of the two
gadget reads: `equivPoint_publicCommitment` unfolds the wire's MSM, `crossing_list` ties each
Lagrange base to the leaf's base reading, and `neg_publicMsm_sum` moves the negation through
the exact integer → scalar reduction (`CommitmentCurve.affine_card_nsmul`). -/
private theorem xhat_cross (s : PastaShape C) (ci : Fin nc) {V : Valuation C.BaseField}
    (σ : Bulletproof.SRS C.Point) (cvk : Kimchi.Verifier.KimchiVK C nc)
    (blindingH : AffinePoint (FVar C.BaseField)) (leaves : List (Leaf C.BaseField nc))
    (Ts cps : List s.d.W.Point) (hbind : XhatBinding s ci V σ cvk blindingH leaves Ts cps)
    (hne : leaves ≠ []) :
    SWPoint.equivPoint C.E (Kimchi.Verifier.publicCommitment C σ cvk (pubOf C V leaves))[ci]
      = -(publicMsm V leaves Ts) + SWPoint.equivPoint C.E σ.h := by
  haveI : NeZero C.scalar := ⟨(Fact.out : C.scalar.Prime).ne_zero⟩
  have hlen : Ts.length = leaves.length := (List.Forall₂.length_eq hbind.pre).symm
  have htie : ∀ (i : ℕ) (hi : i < leaves.length),
      Ts[i]'(hlen ▸ hi)
        = SWPoint.equivPoint C.E ((cvk.lagrangeBasis[i]'(lt_of_lt_of_le hi hbind.hsize))[ci]) := by
    intro i hi
    have hpre_i : LeafPre ci V leaves[i] (Ts[i]'(hlen ▸ hi)) :=
      hbind.pre.get hi (hlen ▸ hi)
    exact OnCurveAt.eq (leafPre_onCurve ci V _ _ hpre_i) (hbind.bases i hi) rfl rfl
  have hne' : (pubOf C V leaves).size ≠ 0 := by
    rw [pubOf_size]
    exact fun h0 => hne (List.length_eq_zero_iff.mp h0)
  have hpm : -(publicMsm V leaves Ts)
      = ((leaves.zip Ts).map (fun p =>
          ((-(↑(ToNat.toNat (p.1.scalarVar.val V)) : C.ScalarField)).val : ℕ) • p.2)).sum := by
    rw [publicMsm]
    exact neg_publicMsm_sum C.scalar
      (fun leaf => ToNat.toNat (leaf.scalarVar.val V)) (leaves.zip Ts)
  rw [equivPoint_publicCommitment (SWPoint.equivPoint C.E) σ cvk (pubOf C V leaves) ci hne',
    crossing_list (SWPoint.equivPoint C.E) ci V cvk leaves Ts hlen hbind.hsize htie, hpm]

/-- The fold after either gadget's prepass reads as the wire's `publicCommitment`, given the
binding. -/
private theorem xHatFold_reads (s : PastaShape C) (ci : Fin nc) {V : Valuation C.BaseField}
    (σ : Bulletproof.SRS C.Point) (cvk : Kimchi.Verifier.KimchiVK C nc)
    (blindingH : AffinePoint (FVar C.BaseField)) (leaves : List (Leaf C.BaseField nc))
    (Ts cps : List s.d.W.Point) (hbind : XhatBinding s ci V σ cvk blindingH leaves Ts cps)
    (hscalar : leafHasScalar leaves) :
    ⦃⌜True⌝⦄
    publicInputCommitFold (S := Builder V (KimchiConstraint C.BaseField)) blindingH leaves
    ⦃⇓ r _ => ⌜OnCurveAt s.d.W V r[ci]
      (SWPoint.equivPoint C.E
        (Kimchi.Verifier.publicCommitment C σ cvk (pubOf C V leaves))[ci])⌝⦄ := by
  have hne : leaves ≠ [] := by
    rintro rfl; simp [leafHasScalar] at hscalar
  refine builder_spec_imp _ _ _
    (publicInputCommitFold_reads (d := s.d) ci blindingH leaves Ts cps
      (SWPoint.equivPoint C.E σ.h)
      (xhatSide_cast s) (xhatSide_bit s) s.order_big
      (le_trans (by norm_num) s.order_big)
      (fun leaf _ => s.regime V leaf)
      hbind.blinding hbind.pre hbind.corr hscalar hbind.hon) fun r hr => ?_
  rw [xhat_cross s ci σ cvk blindingH leaves Ts cps hbind hne]; exact hr

/-- **The wrap-side gadget reads as the wire verifier's `publicCommitment`.** The binding
is asked for only under the boolean leaves' booleanity, which the gadget's bit pre-pass
establishes itself (`constrainBits_boolean`): a consumer never supplies it.
`publicInputCommitFold_reads` carries the subtle half — the canonical decode from the ladder's
top-bit pin, `-(Σ [scalarₗ]·baseₗ) + h`; this crosses that to the wire's `publicCommitment`
through `SWPoint.equivPoint`, and the integer → scalar reduction is exact
(`CommitmentCurve.affine_card_nsmul`), so the read carries no slack. -/
theorem xHat_reads_publicCommitment (s : PastaShape C) (ci : Fin nc) {V : Valuation C.BaseField}
    (σ : Bulletproof.SRS C.Point) (cvk : Kimchi.Verifier.KimchiVK C nc)
    (blindingH : AffinePoint (FVar C.BaseField)) (leaves : List (Leaf C.BaseField nc))
    (Ts cps : List s.d.W.Point)
    (hbind : (∀ leaf ∈ leaves, leaf.bitBoolean V) →
      XhatBinding s ci V σ cvk blindingH leaves Ts cps)
    (hscalar : leafHasScalar leaves) :
    ⦃⌜True⌝⦄
    publicInputCommitFull (S := Builder V (KimchiConstraint C.BaseField)) blindingH leaves
    ⦃⇓ r _ => ⌜OnCurveAt s.d.W V r[ci]
      (SWPoint.equivPoint C.E
        (Kimchi.Verifier.publicCommitment C σ cvk (pubOf C V leaves))[ci])⌝⦄ := by
  -- the gadget opens with the bit pre-pass, so its own rows give the leaves' booleanity
  show ⦃⌜True⌝⦄
    (constrainBits (S := Builder V (KimchiConstraint C.BaseField)) leaves >>= fun _ =>
      publicInputCommitFold blindingH leaves)
    ⦃⇓ r _ => ⌜OnCurveAt s.d.W V r[ci]
      (SWPoint.equivPoint C.E
        (Kimchi.Verifier.publicCommitment C σ cvk (pubOf C V leaves))[ci])⌝⦄
  exact builder_spec_bind_of _ _ _ _ (constrainBits_boolean (V := V) leaves) fun hb _ =>
    xHatFold_reads s ci σ cvk blindingH leaves Ts cps (hbind hb) hscalar

/-- The sealed leaves carry the same public input. -/
private theorem Leaf.SealedOf.pubOf {V : Valuation C.BaseField}
    {ls ls' : List (Leaf C.BaseField nc)} (hs : List.Forall₂ (Leaf.SealedOf V) ls ls') :
    Pickles.pubOf C V ls' = Pickles.pubOf C V ls := by
  unfold Pickles.pubOf
  congr 1
  induction hs with
  | nil => rfl
  | cons hl _ ih => simp only [List.map_cons, ih, Leaf.SealedOf.scalarVar hl]

/-- A binding carries to the sealed leaves: sealing keeps each cell's reading. -/
private theorem XhatBinding.sealed {s : PastaShape C} {ci : Fin nc} {V : Valuation C.BaseField}
    {σ : Bulletproof.SRS C.Point} {cvk : Kimchi.Verifier.KimchiVK C nc}
    {blindingH : AffinePoint (FVar C.BaseField)} {leaves leaves' : List (Leaf C.BaseField nc)}
    {Ts cps : List s.d.W.Point} (hbind : XhatBinding s ci V σ cvk blindingH leaves Ts cps)
    (hs : List.Forall₂ (Leaf.SealedOf V) leaves leaves') :
    XhatBinding s ci V σ cvk blindingH leaves' Ts cps where
  blinding := hbind.blinding
  pre := Leaf.SealedOf.forall₂ (R := LeafPre ci V) (fun h hp => h.leafPre ci hp) hs hbind.pre
  corr := Leaf.SealedOf.forall₂ (R := CorrPre ci V) (fun h hc => h.corrPre ci hc) hs hbind.corr
  hon := Leaf.SealedOf.forall (Leaf.SealedOf.corrHonest ci) hs hbind.hon
  hsize := hs.length_eq ▸ hbind.hsize
  bases i hi := by
    have hi' : i < leaves.length := hs.length_eq ▸ hi
    exact Leaf.SealedOf.baseAt ci (hs.get hi' hi) (hbind.bases i hi')

/-- **The sealed gadget reads as the wire verifier's `publicCommitment`.** The binding is
stated over the leaves before sealing, whose cells may be affine combinations (bases masked
across branches); the walk establishes the boolean leaves' booleanity itself. Otherwise
`xHat_reads_publicCommitment`. -/
theorem xHatSealed_reads_publicCommitment (s : PastaShape C) (ci : Fin nc)
    {V : Valuation C.BaseField}
    (σ : Bulletproof.SRS C.Point) (cvk : Kimchi.Verifier.KimchiVK C nc)
    (blindingH : AffinePoint (FVar C.BaseField)) (leaves : List (Leaf C.BaseField nc))
    (Ts cps : List s.d.W.Point)
    (hbind : (∀ leaf ∈ leaves, leaf.bitBoolean V) →
      XhatBinding s ci V σ cvk blindingH leaves Ts cps)
    (hscalar : leafHasScalar leaves) :
    ⦃⌜True⌝⦄
    publicInputCommitSealed (S := Builder V (KimchiConstraint C.BaseField)) blindingH leaves
    ⦃⇓ r _ => ⌜OnCurveAt s.d.W V r[ci]
      (SWPoint.equivPoint C.E
        (Kimchi.Verifier.publicCommitment C σ cvk (pubOf C V leaves))[ci])⌝⦄ := by
  have hmap := builder_spec_mapM (sealLeaf (S := Builder V (KimchiConstraint C.BaseField)))
    (fun r a => Leaf.SealedOf V a r ∧ a.bitBoolean V) id sealLeaf_spec leaves
  simp only [publicInputCommitSealed]
  mvcgen [hmap]
  rename_i _ rs
  intro st hrel
  rw [List.map_id] at hrel
  obtain ⟨hb, hs⟩ := (List.forall₂_and_left leaves rs).mp
    (hrel.flip.imp fun _ _ h => ⟨h.2, h.1⟩ : List.Forall₂ (fun a r => a.bitBoolean V ∧
      Leaf.SealedOf V a r) leaves rs)
  rw [← Leaf.SealedOf.pubOf hs]
  exact xHatFold_reads s ci σ cvk blindingH rs Ts cps ((hbind hb).sealed hs)
    (Leaf.SealedOf.hasScalar hs hscalar) st trivial

/-- **The step-side gadget reads as the wire verifier's `publicCommitment`.** The
known-domain shape (`publicInputCommitKnown`): the corrections are constants, so their sum
`corrSum` is a single constant cell the binding reads as `Σ cps`, and the leaves are headed by
a scalar leaf. Otherwise `xHat_reads_publicCommitment`. -/
theorem xHatKnown_reads_publicCommitment (s : PastaShape C) (ci : Fin nc)
    {V : Valuation C.BaseField}
    (σ : Bulletproof.SRS C.Point) (cvk : Kimchi.Verifier.KimchiVK C nc)
    (blindingH corrHead corrSum : AffinePoint (FVar C.BaseField))
    (leaves : List (Leaf C.BaseField nc))
    (Ts cps : List s.d.W.Point) (hbind : XhatBinding s ci V σ cvk blindingH leaves Ts cps)
    (hhead : leafHeadScalar leaves) (hC : OnCurveAt s.d.W V corrSum cps.sum) :
    ⦃⌜True⌝⦄
    publicInputCommitKnown (S := Builder V (KimchiConstraint C.BaseField)) ci blindingH corrHead
      corrSum leaves
    ⦃⇓ r _ => ⌜OnCurveAt s.d.W V r
      (SWPoint.equivPoint C.E
        (Kimchi.Verifier.publicCommitment C σ cvk (pubOf C V leaves))[ci])⌝⦄ := by
  have hne : leaves ≠ [] := by
    rintro rfl; exact hhead.elim
  refine builder_spec_imp _ _ _
    (publicInputCommitKnown_reads (d := s.d) ci blindingH corrHead corrSum leaves Ts cps
      (SWPoint.equivPoint C.E σ.h)
      (xhatSide_cast s) (xhatSide_bit s) s.order_big
      (le_trans (by norm_num) s.order_big)
      (fun leaf _ => s.regime V leaf)
      hbind.blinding hbind.pre hbind.corr hC hhead hbind.hon) fun r hr => ?_
  rw [xhat_cross s ci σ cvk blindingH leaves Ts cps hbind hne]; exact hr

/-- A commitment table is bound to the verifier key at the leaves it serves: chunk by chunk, the
leaves' `XhatBinding` at some base and correction points with the correction sum reading as
their sum, and the tables nonempty (the known-domain fold is seeded by the first leaf). -/
structure XhatTable.Bound (s : PastaShape C) (V : Valuation C.BaseField)
    (σ : Bulletproof.SRS C.Point) (cvk : Kimchi.Verifier.KimchiVK C nc)
    (blindingH : AffinePoint (FVar C.BaseField)) (leaves : List (Leaf C.BaseField nc))
    (T : XhatTable C.BaseField nc) : Prop where
  /-- Each chunk's binding, with the correction sum read. -/
  chunks : ∃ Ts cps : List (Fin nc → s.d.W.Point), ∀ ci : Fin nc,
    XhatBinding s ci V σ cvk blindingH leaves (Ts.map (· ci)) (cps.map (· ci)) ∧
    OnCurveAt s.d.W V T.corrSum[ci] (cps.map (· ci)).sum
  /-- At least one base. -/
  bases_ne : T.bases ≠ []
  /-- At least one correction. -/
  corrs_ne : T.corrs ≠ []

end Binding

end XhatCrossing

/-! ## Packed scalars and their leaves -/

section Packed

variable {F : Type} [Field F] [DecidableEq F] {nc : ℕ}

/-- A packed public-input scalar with its ladder width: a full field element, a 128-bit
value, or the 10-bit packed branch data. -/
inductive PackedScalar (F : Type) [Field F] where
  /-- A 255-bit field element. -/
  | full (s : FVar F)
  /-- A 128-bit value. -/
  | b128 (s : FVar F)
  /-- A 10-bit value. -/
  | b10 (s : FVar F)
  /-- A boolean cell: a conditional add of its base. -/
  | bit (b : BoolVar F)

/-- A packed scalar that is not a boolean cell. -/
def PackedScalar.IsScalar : PackedScalar F → Prop
  | .bit _ => False
  | _ => True

/-- The commitment leaves of a packed scalar list: scalar `i` with Lagrange base `i` and its shift
correction from the table; a boolean cell adds its base under the bit, with no correction. -/
def packLeavesOf (ks : List (PackedScalar F)) (tab : XhatTable F nc) : List (Leaf F nc) :=
  List.zipWith (fun k bc => match k with
    | .full s => Leaf.full s bc.1 bc.2
    | .b128 s => Leaf.b128 s bc.1 bc.2
    | .b10 s => Leaf.b10 s bc.1 bc.2
    | .bit b => Leaf.condAdd b bc.1) ks (tab.bases.zip tab.corrs)

/-- The cell a packed scalar carries. -/
def PackedScalar.cell : PackedScalar F → CVar F
  | .full s => s
  | .b128 s => s
  | .b10 s => s
  | .bit b => (↑b : CVar F)

end Packed

/-! ## The table of a key

The Lagrange bases and shift corrections are data of the verifier key, so the table is
computed from it as constant cells rather than taken as an argument and then assumed to be
the key's. It depends on the statement's packing only through the leaf kinds: each kind has
its own shift. -/

section OfKey

open Kimchi.Verifier Bulletproof Bulletproof.Ipa
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open WeierstrassCurve.Affine

variable {C : KimchiCurve} {nc : ℕ} {V : Valuation C.BaseField}

/-- A wire point as a constant cell. -/
def constPt (P : C.Point) : AffinePoint (FVar C.BaseField) := ⟨.const P.x, .const P.y⟩

theorem onCurveAt_constPt (P : C.Point) (hP : P ≠ 0) :
    OnCurveAt C.E.toAffine V (constPt P) (SWPoint.equivPoint C.E P) :=
  ⟨nonsingular_toW (SWPoint.onCurve_of_ne_zero hP),
    SWPoint.equivPoint_eq_some P (SWPoint.onCurve_of_ne_zero hP)⟩

/-- The shift correction `-(2^L)·P`, computed through the curve's verified fast
multi-scalar multiplication. The group's own `•` is a recursion as deep as its scalar, so a
table built with it states the right point and can never be run; this one a driver runs. -/
private def negShift (C : KimchiCurve) (L : ℕ) (P : C.Point) : C.Point :=
  -(C.fastMsm (n := 1) (fun _ => P) (fun _ => ((2 ^ L : ℕ) : ZMod C.scalar)))

private theorem negShift_eq (L : ℕ) (P : C.Point) : negShift C L P = (-(2 ^ L : ℤ)) • P := by
  have hcard : C.scalar • P = 0 := by
    have h := card_nsmul_eq_zero' (G := C.Point) (x := P)
    rwa [C.card] at h
  have hmod : (2 ^ L % C.scalar) • P = (2 ^ L) • P := by
    conv_rhs => rw [← Nat.mod_add_div (2 ^ L) C.scalar, add_nsmul, mul_nsmul, hcard,
      nsmul_zero, _root_.add_zero]
  rw [negShift, C.fastMsm_spec, Fin.sum_univ_one, ZMod.val_natCast, hmod, neg_smul]
  congr 1
  exact_mod_cast (natCast_zsmul P (2 ^ L)).symm

/-- A leaf over constants: the Lagrange points as its base, their honest shifts as its
correction. -/
def constLeaf (k : PackedScalar C.BaseField) (Ps : Vector C.Point nc) : Leaf C.BaseField nc :=
  match k with
  | .full x => .full x (Ps.map constPt) (Ps.map fun P => constPt (negShift C 255 P))
  | .b128 x => .b128 x (Ps.map constPt) (Ps.map fun P => constPt (negShift C 130 P))
  | .b10 x => .b10 x (Ps.map constPt) (Ps.map fun P => constPt (negShift C 10 P))
  | .bit b => .condAdd b (Ps.map constPt)

private theorem leafBaseAt_constLeaf (ci : Fin nc) (k : PackedScalar C.BaseField)
    (Ps : Vector C.Point nc) : leafBaseAt ci (constLeaf k Ps) = constPt Ps[ci] := by
  cases k <;> simp [constLeaf, leafBaseAt]

/-- The point group has odd prime order, so a nonzero point shifted by a power of two stays
nonzero: a constant correction cell is a finite point whenever its base is. -/
private theorem two_pow_zsmul_ne_zero (s : PastaShape C) (P : C.Point) (hP : P ≠ 0) (L : ℕ) :
    (-(2 ^ L : ℤ)) • P ≠ 0 := by
  haveI : Fact C.scalar.Prime := inferInstance
  have hcard : Nat.card C.Point = C.scalar := C.card
  intro h0
  have hdvd : (addOrderOf P : ℤ) ∣ -(2 ^ L : ℤ) := (addOrderOf_dvd_iff_zsmul_eq_zero).2 h0
  have hord : addOrderOf P = C.scalar := by
    have h1 : addOrderOf P ∣ C.scalar := hcard ▸ addOrderOf_dvd_natCard P
    rcases (Nat.dvd_prime (Fact.out : C.scalar.Prime)).1 h1 with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h) hP
    · exact h
  rw [hord, Int.dvd_neg] at hdvd
  have h2 : C.scalar ∣ 2 ^ L := by exact_mod_cast hdvd
  have h3 : C.scalar ∣ 2 := (Fact.out : C.scalar.Prime).dvd_of_dvd_pow h2
  have h4 : C.scalar ≤ 2 := Nat.le_of_dvd (by norm_num) h3
  have := s.scalar_lo
  omega

/-- The correction point a constant leaf's correction cell reads as. -/
noncomputable def constCp (s : PastaShape C) (ci : Fin nc) (k : PackedScalar C.BaseField)
    (Ps : Vector C.Point nc) : s.d.W.Point :=
  match k with
  | .full _ => (-(2 ^ 255 : ℤ)) • SWPoint.equivPoint C.E Ps[ci]
  | .b128 _ => (-(2 ^ 130 : ℤ)) • SWPoint.equivPoint C.E Ps[ci]
  | .b10 _ => (-(2 ^ 10 : ℤ)) • SWPoint.equivPoint C.E Ps[ci]
  | .bit _ => 0

private theorem onCurveAt_shift (s : PastaShape C) (P : C.Point) (hP : P ≠ 0) (L : ℕ) :
    OnCurveAt s.d.W V (constPt (negShift C L P))
      ((-(2 ^ L : ℤ)) • SWPoint.equivPoint C.E P) := by
  rw [← map_zsmul, ← negShift_eq]
  exact onCurveAt_constPt _ (negShift_eq L P ▸ two_pow_zsmul_ne_zero s P hP L)

private theorem leafPre_const (s : PastaShape C) (ci : Fin nc) (k : PackedScalar C.BaseField)
    (Ps : Vector C.Point nc) (hP : Ps[ci] ≠ 0)
    (hbit : ∀ b, k = .bit b → ∃ bb : Bool, (↑b : CVar C.BaseField).val V = bit bb) :
    LeafPre (d := s.d) ci V (constLeaf k Ps) (SWPoint.equivPoint C.E Ps[ci]) := by
  cases k with
  | bit b => exact ⟨by simpa [constLeaf] using onCurveAt_constPt (V := V) Ps[ci] hP, hbit b rfl⟩
  | _ => simpa [constLeaf, LeafPre] using onCurveAt_constPt (V := V) Ps[ci] hP

private theorem corrPre_const (s : PastaShape C) (ci : Fin nc) (k : PackedScalar C.BaseField)
    (Ps : Vector C.Point nc) (hP : Ps[ci] ≠ 0) :
    CorrPre (d := s.d) ci V (constLeaf k Ps) (constCp s ci k Ps) := by
  cases k with
  | bit b => rfl
  | full x =>
    simp only [constLeaf, CorrPre, constCp]
    rw [getElem_map_fin]
    exact onCurveAt_shift (V := V) s _ hP 255
  | b128 x =>
    simp only [constLeaf, CorrPre, constCp]
    rw [getElem_map_fin]
    exact onCurveAt_shift (V := V) s _ hP 130
  | b10 x =>
    simp only [constLeaf, CorrPre, constCp]
    rw [getElem_map_fin]
    exact onCurveAt_shift (V := V) s _ hP 10

private theorem corrHonest_const (s : PastaShape C) (ci : Fin nc) (k : PackedScalar C.BaseField)
    (Ps : Vector C.Point nc) (hP : Ps[ci] ≠ 0) :
    CorrHonest s.d ci V (constLeaf k Ps) := by
  have key : ∀ (L : ℕ) (T : s.d.W.Point),
      OnCurveAt s.d.W V (constPt Ps[ci]) T →
      OnCurveAt s.d.W V (constPt (negShift C L Ps[ci])) ((-(2 ^ L : ℤ)) • T) := by
    intro L T hT
    have hT' : T = SWPoint.equivPoint C.E Ps[ci] :=
      OnCurveAt.eq hT (onCurveAt_constPt (V := V) Ps[ci] hP) rfl rfl
    subst hT'
    exact onCurveAt_shift s _ hP L
  cases k with
  | bit b => trivial
  | full x =>
    simp only [constLeaf, CorrHonest]
    rw [getElem_map_fin, getElem_map_fin]
    exact key 255
  | b128 x =>
    simp only [constLeaf, CorrHonest]
    rw [getElem_map_fin, getElem_map_fin]
    exact key 130
  | b10 x =>
    simp only [constLeaf, CorrHonest]
    rw [getElem_map_fin, getElem_map_fin]
    exact key 10

/-- **The table computed from the key is bound to the key.** Constant cells — the Lagrange
points as bases, their honest shifts as corrections, the SRS blinding base — satisfy
`XhatBinding` given only what is not table bookkeeping: the blinding base and the Lagrange
points are finite (at the `(0, 0)` sentinel no cell reads as the point, so this is necessary
too), the boolean leaves are boolean — which `xHat_reads_publicCommitment` supplies from the
gadget's own bit pre-pass. -/
theorem xhatBinding_const (s : PastaShape C) (ci : Fin nc) (σ : SRS C.Point)
    (cvk : KimchiVK C nc) (ks : List (PackedScalar C.BaseField))
    (hh : σ.h ≠ 0)
    (hL : ∀ Ps ∈ cvk.lagrangeBasis.toList, Ps[ci] ≠ 0)

    (hbits : ∀ leaf ∈ List.zipWith constLeaf ks cvk.lagrangeBasis.toList, leaf.bitBoolean V)
 :
    XhatBinding s ci V σ cvk (constPt σ.h)
      (List.zipWith constLeaf ks cvk.lagrangeBasis.toList)
      (List.zipWith (fun _ Ps => SWPoint.equivPoint C.E Ps[ci]) ks cvk.lagrangeBasis.toList)
      (List.zipWith (constCp s ci) ks cvk.lagrangeBasis.toList) where
  blinding := onCurveAt_constPt σ.h hh
  pre := forall₂_zipWith _ _ _ _ _ fun p hp =>
    leafPre_const s ci p.1 p.2 (hL _ (List.of_mem_zip hp).2) fun b hb => by
      have hmem : constLeaf p.1 p.2 ∈ List.zipWith constLeaf ks cvk.lagrangeBasis.toList := by
        rw [← List.map_uncurry_zip_eq_zipWith]
        exact List.mem_map.2 ⟨p, hp, rfl⟩
      have := hbits _ hmem
      rw [hb] at this
      exact this
  corr := forall₂_zipWith _ _ _ _ _ fun p hp =>
    corrPre_const s ci p.1 p.2 (hL _ (List.of_mem_zip hp).2)
  hon := by
    intro leaf hl
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hl
    rw [List.getElem_zipWith]
    exact corrHonest_const s ci _ _ (hL _ (List.getElem_mem _))
  hsize := by simp [List.length_zipWith]
  bases := by
    intro i hi
    rw [List.getElem_zipWith, leafBaseAt_constLeaf]
    have h := onCurveAt_constPt (V := V) _ (hL _ (List.getElem_mem
      (l := cvk.lagrangeBasis.toList) (n := i) (by
        simp only [List.length_zipWith, Array.length_toList] at hi; simp; omega)))
    simpa using h

/-- The ladder width of a packed scalar's kind; a boolean leaf has no correction. -/
private def shiftBits : PackedScalar C.BaseField → Option ℕ
  | .full _ => some 255
  | .b128 _ => some 130
  | .b10 _ => some 10
  | .bit _ => none

/-- The commitment table computed from the key's Lagrange points, at a statement's packing. A
boolean leaf's correction slot is never read (`packLeavesOf` drops it); it holds the base. -/
def XhatTable.ofKey (ks : List (PackedScalar C.BaseField)) (lb : List (Vector C.Point nc)) :
    XhatTable C.BaseField nc where
  bases := lb.map (·.map constPt)
  corrs := List.zipWith (fun k Ps => Ps.map fun P =>
    constPt (match shiftBits k with | some L => negShift C L P | none => P)) ks lb
  corrHead := Vector.replicate nc (constPt 0)
  corrSum := Vector.replicate nc (constPt 0)

/-- `packLeavesOf` at that table is the constant leaves. -/
theorem packLeavesOf_ofKey : ∀ (ks : List (PackedScalar C.BaseField))
    (lb : List (Vector C.Point nc)),
    packLeavesOf ks (XhatTable.ofKey ks lb) = List.zipWith constLeaf ks lb
  | [], _ => by simp [packLeavesOf]
  | _ :: _, [] => by simp [packLeavesOf, XhatTable.ofKey]
  | k :: ks, Ps :: lb => by
      have ih := packLeavesOf_ofKey ks lb
      simp only [packLeavesOf, XhatTable.ofKey, List.map_cons, List.zipWith_cons_cons,
        List.zip_cons_cons] at ih ⊢
      refine congrArg₂ _ ?_ ih
      cases k <;> simp [constLeaf, shiftBits]

/-- A packed scalar's cell reduced into the scalar field: the public-input entry it
contributes (`pubOf`). -/
def PackedScalar.reduced (C : KimchiCurve) [ToNat C.BaseField] (V : Valuation C.BaseField)
    (k : PackedScalar C.BaseField) : C.ScalarField :=
  ((ToNat.toNat (k.cell.val V) : ℕ) : C.ScalarField)

/-- With a Lagrange point per scalar, the public input of the constant leaves is the reduced
scalars. -/
theorem pubOf_zipWith_constLeaf [ToNat C.BaseField] :
    ∀ (ks : List (PackedScalar C.BaseField)) (lb : List (Vector C.Point nc)),
      ks.length ≤ lb.length →
      (pubOf C V (List.zipWith constLeaf ks lb)).toList = ks.map (PackedScalar.reduced C V)
  | [], _, _ => by simp [pubOf]
  | _ :: _, [], h => by simp at h
  | k :: ks, Ps :: lb, h => by
    have ih := pubOf_zipWith_constLeaf ks lb (by simpa using h)
    simp only [pubOf, List.zipWith_cons_cons, List.map_cons, List.toList_toArray] at ih ⊢
    rw [ih]
    cases k <;> rfl

/-- Two packed scalars of one kind whose cells read the same value. -/
def PackedScalar.SameReading (V : Valuation C.BaseField) :
    PackedScalar C.BaseField → PackedScalar C.BaseField → Prop
  | .full a, .full b => a.val V = b.val V
  | .b128 a, .b128 b => a.val V = b.val V
  | .b10 a, .b10 b => a.val V = b.val V
  | .bit a, .bit b => (↑a : CVar C.BaseField).val V = (↑b : CVar C.BaseField).val V
  | _, _ => False

/-! ### The known-domain fold's table

`publicInputCommitKnown` takes the corrections' sum as one constant, where
`publicInputCommitFull` adds each leaf's correction. The table below carries that sum; the cell
reads as a point only when the sum is a finite point, which no invariant of the key gives: it
is one fixed relation among the Lagrange points. -/

/-- The correction point of a packed scalar at a Lagrange point: its honest shift `-(2^L)·P`,
none for a boolean cell. -/
private def corrPt (k : PackedScalar C.BaseField) (P : C.Point) : C.Point :=
  match shiftBits k with
  | some L => negShift C L P
  | none => 0

/-- The constant correction sum of the known-domain fold, at chunk `ci`. -/
def corrSumPt (ks : List (PackedScalar C.BaseField)) (lb : List (Vector C.Point nc))
    (ci : Fin nc) : C.Point :=
  (List.zipWith (fun k Ps => corrPt k Ps[ci]) ks lb).sum

/-- The table of the known-domain fold, computed from the key's Lagrange points: the
bases and corrections of `XhatTable.ofKey`, the fold's seed the first correction, its constant
the correction sum. -/
def XhatTable.ofKeyKnown (ks : List (PackedScalar C.BaseField))
    (lb : List (Vector C.Point nc)) : XhatTable C.BaseField nc :=
  { XhatTable.ofKey ks lb with
    corrHead := Vector.ofFn fun ci => constPt
      (match ks, lb with
       | k :: _, Ps :: _ => corrPt k Ps[ci]
       | _, _ => 0)
    corrSum := Vector.ofFn fun ci => constPt (corrSumPt ks lb ci) }

/-- A packed scalar reads the same as itself. -/
theorem PackedScalar.sameReading_refl (k : PackedScalar C.BaseField) :
    PackedScalar.SameReading V k k := by
  cases k <;> rfl

/-- The public input of the key's table depends on each packed scalar only through its kind and
its reading. -/
theorem pubOf_ofKeyKnown_congr [ToNat C.BaseField] (lb : List (Vector C.Point nc)) :
    ∀ {ks ks' : List (PackedScalar C.BaseField)},
      List.Forall₂ (PackedScalar.SameReading V) ks ks' →
      pubOf C V (packLeavesOf ks (XhatTable.ofKeyKnown ks lb))
        = pubOf C V (packLeavesOf ks' (XhatTable.ofKeyKnown ks' lb)) := by
  intro ks ks' h
  have hk : ∀ ks : List (PackedScalar C.BaseField),
      packLeavesOf ks (XhatTable.ofKeyKnown ks lb) = List.zipWith constLeaf ks lb :=
    fun ks => packLeavesOf_ofKey ks lb
  rw [hk, hk]
  simp only [pubOf]
  congr 1
  induction h generalizing lb with
  | nil => simp
  | @cons k k' ks ks' hkk _ ih =>
    cases lb with
    | nil => simp
    | cons Ps lb =>
      simp only [List.zipWith_cons_cons, List.map_cons, ih lb (fun ks => packLeavesOf_ofKey ks lb)]
      congr 1
      cases k <;> cases k' <;> simp only [PackedScalar.SameReading] at hkk <;>
        first | exact hkk.elim | simp only [constLeaf, Leaf.scalarVar, hkk]

/-- A scalar's constant leaf is trivially bit-boolean. -/
theorem bitBoolean_constLeaf_of_isScalar (ks : List (PackedScalar C.BaseField))
    (lb : List (Vector C.Point nc)) (hks : ∀ k ∈ ks, k.IsScalar) :
    ∀ leaf ∈ List.zipWith constLeaf ks lb, leaf.bitBoolean V := by
  intro leaf hl
  rw [← List.map_uncurry_zip_eq_zipWith] at hl
  obtain ⟨⟨k, Ps⟩, hp, rfl⟩ := List.mem_map.1 hl
  have hk := hks k (List.of_mem_zip hp).1
  cases k with
  | bit b => exact absurd hk (by simp [PackedScalar.IsScalar])
  | _ => trivial

private theorem equivPoint_corrPt (s : PastaShape C) (ci : Fin nc)
    (k : PackedScalar C.BaseField) (Ps : Vector C.Point nc) :
    SWPoint.equivPoint C.E (corrPt k Ps[ci]) = constCp s ci k Ps := by
  cases k <;> simp [corrPt, shiftBits, constCp, negShift_eq, map_zsmul]

/-- The correction sum, crossed to the point group, is the sum of the leaves' correction
points. -/
private theorem equivPoint_corrSumPt (s : PastaShape C) (ci : Fin nc)
    (ks : List (PackedScalar C.BaseField)) (lb : List (Vector C.Point nc)) :
    SWPoint.equivPoint C.E (corrSumPt ks lb ci)
      = ((List.zipWith (fun k Ps => fun ci => constCp s ci k Ps) ks lb).map (· ci)).sum := by
  have hfun : (fun (k : PackedScalar C.BaseField) (Ps : Vector C.Point nc) =>
        SWPoint.equivPoint C.E (corrPt k Ps[ci]))
      = fun k Ps => constCp s ci k Ps := by
    funext k Ps
    exact equivPoint_corrPt s ci k Ps
  rw [corrSumPt, map_list_sum, List.map_zipWith, List.map_zipWith, hfun]

/-- **The known-domain table computed from the key is bound to the key.** Beyond
`xhatBinding_const`'s premises, the correction sum is a finite point at every chunk. -/
theorem bound_ofKeyKnown (s : PastaShape C) (σ : SRS C.Point) (cvk : KimchiVK C nc)
    (ks : List (PackedScalar C.BaseField))
    (hh : σ.h ≠ 0) (hL : ∀ Ps ∈ cvk.lagrangeBasis.toList, ∀ ci : Fin nc, Ps[ci] ≠ 0)
    (hks : ks ≠ []) (hlb : cvk.lagrangeBasis.toList ≠ [])
    (hbits : ∀ leaf ∈ List.zipWith constLeaf ks cvk.lagrangeBasis.toList, leaf.bitBoolean V)

    (hsum : ∀ ci : Fin nc, corrSumPt ks cvk.lagrangeBasis.toList ci ≠ 0) :
    (XhatTable.ofKeyKnown ks cvk.lagrangeBasis.toList).Bound s V σ cvk (constPt σ.h)
      (List.zipWith constLeaf ks cvk.lagrangeBasis.toList) where
  chunks := by
    refine ⟨List.zipWith (fun _ Ps => fun ci => SWPoint.equivPoint C.E Ps[ci]) ks
        cvk.lagrangeBasis.toList,
      List.zipWith (fun k Ps => fun ci => constCp s ci k Ps) ks cvk.lagrangeBasis.toList,
      fun ci => ⟨?_, ?_⟩⟩
    · have hb := xhatBinding_const (V := V) s ci σ cvk ks hh (fun Ps h => hL Ps h ci) hbits
      simpa only [List.map_zipWith] using hb
    · have hc : (XhatTable.ofKeyKnown ks cvk.lagrangeBasis.toList).corrSum[ci]
          = constPt (corrSumPt ks cvk.lagrangeBasis.toList ci) := by
        simp [XhatTable.ofKeyKnown, Fin.getElem_fin]
      rw [hc, ← equivPoint_corrSumPt s ci]
      exact onCurveAt_constPt _ (hsum ci)
  bases_ne := by
    simpa [XhatTable.ofKeyKnown, XhatTable.ofKey] using hlb
  corrs_ne := by
    cases ks with
    | nil => exact absurd rfl hks
    | cons k ks =>
      cases hl : cvk.lagrangeBasis.toList with
      | nil => exact absurd hl hlb
      | cons Ps lb => simp [XhatTable.ofKeyKnown, XhatTable.ofKey]

/-! ### The correction sum's coefficients

Where the Lagrange points are commitments `msm g a`, the correction sum is one too, at the
coefficients `corrCoeffs`; so that it is a finite point is a relation the SRS avoids
(`SRS.Avoids`). The vector is nonzero where the Lagrange vectors past the first sum to zero
and the first to one: its coefficients then sum to the first leaf's shift. -/

/-- The shift coefficient of a packed scalar: `-(2^L)` at its ladder width, none for a boolean
cell. -/
def shiftCoeff (k : PackedScalar C.BaseField) : C.ScalarField :=
  match shiftBits k with
  | some L => -(2 ^ L)
  | none => 0

private theorem corrPt_eq_smul (k : PackedScalar C.BaseField) (P : C.Point) :
    corrPt k P = shiftCoeff k • P := by
  unfold corrPt shiftCoeff
  cases shiftBits k with
  | none => simp
  | some L =>
      show negShift C L P = (-(2 ^ L) : C.ScalarField) • P
      rw [negShift_eq, ← Int.cast_smul_eq_zsmul C.ScalarField]
      push_cast
      rfl

theorem shiftCoeff_ne_zero (s : PastaShape C) (k : PackedScalar C.BaseField)
    (hk : k.IsScalar) : shiftCoeff k ≠ 0 := by
  cases k <;> simp [shiftCoeff, shiftBits, PackedScalar.IsScalar, s.scalar_two_ne] at hk ⊢

/-- The coefficients of the known-domain fold's correction sum, against the coefficient
vectors `ls` of its Lagrange points. -/
def corrCoeffs {m : ℕ} (ks : List (PackedScalar C.BaseField))
    (ls : List (Fin m → C.ScalarField)) : Fin m → C.ScalarField :=
  (List.zipWith (fun k a => shiftCoeff k • a) ks ls).sum

/-- The correction sum is the commitment to its coefficients. -/
theorem corrSumPt_map_msm {m : ℕ} (g : Fin m → C.Point) :
    ∀ (ks : List (PackedScalar C.BaseField)) (ls : List (Fin m → C.ScalarField)),
      corrSumPt ks (ls.map fun a => #v[Ipa.msm C g a]) 0 = Ipa.msm C g (corrCoeffs ks ls)
  | [], _ => by simp [corrSumPt, corrCoeffs, Ipa.msm_eq]
  | _ :: _, [] => by simp [corrSumPt, corrCoeffs, Ipa.msm_eq]
  | k :: ks, a :: ls => by
      have ih := corrSumPt_map_msm g ks ls
      simp only [corrSumPt, corrCoeffs, List.map_cons, List.zipWith_cons_cons,
        List.sum_cons] at ih ⊢
      rw [ih, corrPt_eq_smul]
      simp [Ipa.msm_eq]

end OfKey

/-! The gadgets are sealed after their reads: a consumer composes `publicInputCommitKnown_reads`,
`xHat_reads_publicCommitment` or `xHatSealed_reads_publicCommitment`, never the body. -/
attribute [irreducible] chunkwise leafStep foldChunks publicInputCommitChunks addChunks
  sumCorrections sumCorrectionsHead publicInputCommitFold publicInputCommitFull sealLeaf
  publicInputCommitSealed ladders foldKnown commitKnownTail publicInputCommitKnown

end Pickles
