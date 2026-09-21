import Snarky.Kimchi.Circuit.AddComplete
import Snarky.Kimchi.Circuit.Point
import Kimchi.Verifier.Kimchi
import Pickles.Curve

/-!
# The in-circuit public-input commitment (`x_hat`)

The port of PS `Pickles.PublicInputCommit.publicInputCommit` (OCaml
`Public_input.commitment` / `lagrange_with_correction`): the per-chunk MSM that commits to
a proof's public input, `x_hat[c] = -(Σ_leaf [scalarₗ]·baseₗ[c]) + h`.

The public input reaches this gadget as a flat list of size-tagged `Leaf`s — a scalar with
its ladder width, or a 1-bit `condAdd`. Packing (a structured statement → this list) is a
separate concern; this module's soundness claim is stated against the list, and lands on
`Kimchi.Verifier.publicCommitment` via `publicCommitment_eq_sum`.

Two gadgets share the leaf interface: `publicInputCommitFull` (the wrap side, OCaml
`lagrange_with_correction`: corrections summed in circuit, the fold interleaved) and
`publicInputCommitKnown` (the step side, OCaml `multiscale_known`: every ladder first, then
one fold from the first ladder result, then the constant correction sum). Both read as
`-(publicMsm) + h` over the circuit-side point group (`publicInputCommitFull_reads`,
`publicInputCommitKnown_reads`).

The last section is the wire crossing (glue G2, second half): `xHat_reads_publicCommitment`
and `xHatKnown_reads_publicCommitment` cross those reads to the wire verifier's own
`Kimchi.Verifier.publicCommitment` on the commitment curve, generically over a `PastaShape`
(the point group, the `SWPoint.equivPoint` crossing, and the group's order killing it, so the
integer→scalar reduction is exact — no `lowest_128_bits` slack here), instantiated at
`pastaShapeVesta` (Vesta) and `pastaShapePallas` (Pallas).

The tables the gadgets take are a verifier key's data, so the module ends by computing them:
a packed scalar list (`PackedScalar`) against a key's Lagrange points gives the leaves
(`packLeavesOf`) and the tables (`XhatTable.ofKey`, `XhatTable.ofKeyKnown`), bound as the
reads require (`xhatBinding_const`, `bound_ofKeyKnown`), with the known-domain fold's
correction sum a commitment to named coefficients (`corrCoeffs`, `corrSumPt_map_msm`).
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi CompElliptic.Fields.Pasta

/-- A size-tagged public-input leaf, the flat interface the commitment gadget folds over.
The three scalar cases fix the `scaleFast2'` ladder width `(n, chunks, sDiv2Bits)` and carry
the precomputed shift correction (PS `MsmTerm.correction`), a constant point per chunk that
the read requires to be `-(2^{5·chunks})·base` — cancelling the ladder's shift so the net is
`[scalar]·base`. `condAdd` is the 1-bit conditional-add path (a boolean statement field or a
shifted scalar's parity), no correction. Each field is chunked (`Vector _ nc`) so the
per-chunk accumulator runs in parallel. -/
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

/-- **Narrow ladders need no forbidden-band exclusion.** When the ladder width `L` is small
enough that `3·2^L ≤ order`, `scaleFast2'`'s regime holds for EVERY witness — the subwrap
disjunct of `LadderRegime`, with no `z ∉ forbiddenValues` condition. This covers the `b128`
(L = 5·26 = 130) and `b10` (L = 5·2 = 10) leaves against the ~2^254 Pasta order; only the
full 255-bit leaf reaches the one-wrap case and carries the band. -/
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

end Reads

/-! ## The per-chunk fold -/

section Fold

variable {F S : Type} [Field F] [DecidableEq F] [ToNat F] [BasicSystem F S] [KimchiSystem F S]

/-- Accumulate each leaf's ladder onto `acc` at one chunk `ci`, aligned with OCaml/PS's
`Public_input.commitment` fold: a scalar leaf adds its BARE `scaleFast2'` ladder (the shift
`+2^{5·chunks}` is NOT cancelled here — the corrections are summed separately into the fold's
initial accumulator, `init = Σ corrections`, matching `wrap_verifier.ml`'s
`Array.map2_exn acc chunks` where only the ladder result is added); a `condAdd` leaf
conditionally adds its base. The running `acc` threads through, as `sumPoints` does for
`bullet_reduce`. -/
private def foldChunk (ci : Fin nc) :
    AffinePoint (FVar F) → List (Leaf F nc) → CircuitM F S (AffinePoint (FVar F))
  | acc, [] => pure acc
  | acc, .full scalar base _ :: rest => do
      let l ← scaleFast2' 255 51 254 base[ci] scalar
      let acc' ← addFast .checkFinite acc l
      foldChunk ci acc'.p rest
  | acc, .b128 scalar base _ :: rest => do
      let l ← scaleFast2' 255 26 127 base[ci] scalar
      let acc' ← addFast .checkFinite acc l
      foldChunk ci acc'.p rest
  | acc, .b10 scalar base _ :: rest => do
      let l ← scaleFast2' 255 2 9 base[ci] scalar
      let acc' ← addFast .checkFinite acc l
      foldChunk ci acc'.p rest
  | acc, .condAdd b base :: rest => do
      let r ← addFast .checkFinite base[ci] acc
      let acc' ← select b r.p acc
      foldChunk ci acc' rest

/-- The public-input commitment at one chunk `ci` (PS `publicInputCommit`, one chunk): fold the
leaves' ladders onto the corrections' sum `init`, then negate and add the blinding `h` —
`x_hat = -(Σ [scalar]·base) + h`. `init` is the summed corrections (computed by the caller);
the fold's bare-ladder shifts cancel against it in the spec. -/
private def publicInputCommitChunk (ci : Fin nc) (init blindingH : AffinePoint (FVar F))
    (leaves : List (Leaf F nc)) : CircuitM F S (AffinePoint (FVar F)) := do
  let acc ← foldChunk ci init leaves
  (·.p) <$> addFast .checkFinite ⟨acc.x, CVar.negate_ acc.y⟩ blindingH

/-- Sum the leaves' shift corrections onto `acc` at chunk `ci` (PS `InCircuitCorrections`'s
`init`): each scalar leaf adds its `correction`, `condAdd` contributes nothing. The running
`acc` threads through, as `sumPoints` does for `bullet_reduce`. -/
private def sumCorrections (ci : Fin nc) :
    AffinePoint (FVar F) → List (Leaf F nc) → CircuitM F S (AffinePoint (FVar F))
  | acc, [] => pure acc
  | acc, .full _ _ corr :: rest => do
      let acc' ← addFast .checkFinite acc corr[ci]
      sumCorrections ci acc'.p rest
  | acc, .b128 _ _ corr :: rest => do
      let acc' ← addFast .checkFinite acc corr[ci]
      sumCorrections ci acc'.p rest
  | acc, .b10 _ _ corr :: rest => do
      let acc' ← addFast .checkFinite acc corr[ci]
      sumCorrections ci acc'.p rest
  | acc, .condAdd _ _ :: rest => sumCorrections ci acc rest

/-- The leaves reach a scalar leaf — so the head-seeded corrections fold has a seed. -/
def leafHasScalar : List (Leaf F nc) → Prop
  | [] => False
  | .condAdd _ _ :: rest => leafHasScalar rest
  | _ => True

/-- Head-seeded corrections sum (PS `InCircuitCorrections`'s `init`): the first scalar leaf's
correction seeds the fold (no gate), each later scalar correction adds one (`n` corrections →
`n−1` gates, matching OCaml). `condAdd` leaves are skipped; the all-`condAdd`/empty case is the
unused origin. -/
private def sumCorrectionsHead (ci : Fin nc) :
    List (Leaf F nc) → CircuitM F S (AffinePoint (FVar F))
  | [] => pure ⟨.const 0, .const 0⟩
  | .full _ _ corr :: rest => sumCorrections ci corr[ci] rest
  | .b128 _ _ corr :: rest => sumCorrections ci corr[ci] rest
  | .b10 _ _ corr :: rest => sumCorrections ci corr[ci] rest
  | .condAdd _ _ :: rest => sumCorrectionsHead ci rest

/-- The boolean leaves constrain their own bits, in walk order, before any ladder runs. PS
`PublicInputCommit (BoolVar f)` asserts the bit inside `scalarMuls` while the leaf's scale mul
is deferred to the fold, so every such assertion precedes the adds; this pass reproduces that
placement, and callers do not supply the constraints themselves. -/
private def constrainBits [BasicSystem F S] : List (Leaf F nc) → CircuitM F S PUnit
  | [] => pure PUnit.unit
  | .condAdd b _ :: rest => do
      addConstraint (BasicSystem.boolean (↑b : CVar F) : S)
      constrainBits rest
  | .full _ _ _ :: rest => constrainBits rest
  | .b128 _ _ _ :: rest => constrainBits rest
  | .b10 _ _ _ :: rest => constrainBits rest

/-- The full one-chunk public-input commitment (PS `publicInputCommit`, one chunk): head-seed
the corrections into `init`, fold the ladders, negate, add `h`. -/
def publicInputCommitFull (ci : Fin nc) (blindingH : AffinePoint (FVar F))
    (leaves : List (Leaf F nc)) : CircuitM F S (AffinePoint (FVar F)) := do
  constrainBits leaves
  let init ← sumCorrectionsHead ci leaves
  publicInputCommitChunk ci init blindingH leaves

/-- The reading + ladder-witness data the fold produces for one leaf: a scalar leaf yields its
ladder width `L = 5·chunks`, the split witness `(z, bb)` and the base's curve point `T`; a
`condAdd` leaf yields its bit and base point. -/
private inductive LeafInfo (F : Type) [Field F] [DecidableEq F] (d : HasCurve F) where
  /-- A scalar leaf: shift width `L`, split `(z, bb)`, base point `T`. -/
  | scalar (L : ℕ) (z : ℤ) (bb : Bool) (T : d.W.Point)
  /-- A `condAdd` leaf: bit and base point. -/
  | cond (bb : Bool) (T : d.W.Point)

variable {F : Type} [Field F] [DecidableEq F] [ToNat F] {d : HasCurve F}

/-- The curve-point a leaf adds to the accumulator in `foldChunk`: a scalar leaf adds its BARE
ladder `(2z + bit + 2^L)·T` (shift not yet cancelled); a `condAdd` adds `T` iff its bit. -/
private def LeafInfo.delta : LeafInfo F d → d.W.Point
  | .scalar L z bb T => (2 * z + (if bb then 1 else 0) + 2 ^ L) • T
  | .cond bb T => if bb then T else 0

/-- The ladder regime a scalar leaf's contribution is valid under (`True` for `condAdd`). At
the deployed layer this is discharged by `ladderRegime_subwrap` for the narrow leaves and by
the forbidden-band exclusion for the full-width leaf. -/
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
and — for a `condAdd` — its bit is boolean-valued under `V` (the boolean constraint the packing
emits; carried as a well-formedness premise, as `checkBulletproof`'s `hbits`). -/
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
supplied full-width regime (`hfull`, discharged at the deployed curve from the forbidden-band
exclusion). `condAdd` is trivial. -/
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
is in regime, off the narrow subwrap bounds and a single full-width forbidden-band premise
(supplied at the deployed curve). The list form `publicInputCommitFull_spec`'s regime premise
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
`corrDelta` sum — exactly `publicInputCommitFull_spec`'s seed premise. Position-wise
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

/-- **The per-chunk fold reads as the accumulator plus the sum of leaf deltas.** For a
satisfying assignment, `foldChunk ci acc leaves` reads, at any `accv` for `acc`, as
`accv + Σ (LeafInfo.delta)` over infos the leaves read to — provided each scalar leaf's ladder
regime holds (`regimeOK`). The bare ladders' shifts are still present in the deltas; the
top-level's `init = Σ corrections` cancels them. By induction on `leaves`, as `sumPoints_spec`. -/
private theorem foldChunk_spec (ci : Fin nc) {V : Valuation F} :
    ∀ (leaves : List (Leaf F nc)) (Ts : List d.W.Point) (acc : AffinePoint (FVar F)),
      List.Forall₂ (LeafPre ci V) leaves Ts →
      ⦃⌜True⌝⦄ foldChunk (S := Builder V (KimchiConstraint F)) ci acc leaves
      ⦃⇓ r _ => ⌜∃ infos : List (LeafInfo F d), List.Forall₂ (LeafReads ci V) leaves infos ∧
        ∀ accv : d.W.Point, OnCurveAt d.W V acc accv → (∀ i ∈ infos, i.regimeOK) →
          OnCurveAt d.W V r (accv + (infos.map LeafInfo.delta).sum)⌝⦄
  | [], [], acc, .nil => by
      simp only [foldChunk]
      mvcgen
      exact ⟨[], .nil, fun accv hacc _ => by simpa using hacc⟩
  | .full scalar base _ :: rest, T :: Ts, acc, .cons hT hrest => by
      simp only [foldChunk]
      have hsf := scaleFast2'_spec (V := V) d 255 51 254 (by norm_num) (by norm_num) base[ci] scalar
      have hadd := fun l => addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
        d.two_torsion_free acc l
      have ih := fun acc' => foldChunk_spec (V := V) ci rest Ts acc' hrest
      mvcgen [-Snarky.Kimchi.addFast_spec, hsf, hadd, ih]
      rename_i _ _ _ hsf' _ _ hadd' _ _
      rintro ⟨rest_infos, hrf, hrest_oc⟩
      obtain ⟨z, bb, h0, -, hlt, hval, hladder⟩ := hsf' T hT
      refine ⟨.scalar 255 z bb T :: rest_infos,
        List.Forall₂.cons ⟨rfl, hT, h0, hlt (by norm_num), hval⟩ hrf, ?_⟩
      · intro accv hacc hregs
        have hhead : d.LadderRegime 255 (Pasta.Shifted.unshiftType1 255 z) :=
          hregs _ List.mem_cons_self
        have hlad := hladder hhead
        have hstep := hadd' accv _ hacc hlad
        have hrr : ∀ i ∈ rest_infos, i.regimeOK :=
          fun i hi => hregs i (List.mem_cons_of_mem _ hi)
        have hfinal := hrest_oc _ hstep hrr
        simp only [List.map_cons, List.sum_cons, LeafInfo.delta,
          Pasta.Shifted.unshiftType2] at hfinal ⊢
        rwa [← add_assoc]
  | .b128 scalar base _ :: rest, T :: Ts, acc, .cons hT hrest => by
      simp only [foldChunk]
      have hsf := scaleFast2'_spec (V := V) d 255 26 127 (by norm_num) (by norm_num) base[ci] scalar
      have hadd := fun l => addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
        d.two_torsion_free acc l
      have ih := fun acc' => foldChunk_spec (V := V) ci rest Ts acc' hrest
      mvcgen [-Snarky.Kimchi.addFast_spec, hsf, hadd, ih]
      rename_i _ _ _ hsf' _ _ hadd' _ _
      rintro ⟨rest_infos, hrf, hrest_oc⟩
      obtain ⟨z, bb, h0, hlt, -, hval, hladder⟩ := hsf' T hT
      refine ⟨.scalar 130 z bb T :: rest_infos, List.Forall₂.cons ⟨rfl, hT, h0, hlt, hval⟩ hrf, ?_⟩
      · intro accv hacc hregs
        have hhead : d.LadderRegime 130 (Pasta.Shifted.unshiftType1 130 z) :=
          hregs _ List.mem_cons_self
        have hlad := hladder hhead
        have hstep := hadd' accv _ hacc hlad
        have hrr : ∀ i ∈ rest_infos, i.regimeOK :=
          fun i hi => hregs i (List.mem_cons_of_mem _ hi)
        have hfinal := hrest_oc _ hstep hrr
        simp only [List.map_cons, List.sum_cons, LeafInfo.delta,
          Pasta.Shifted.unshiftType2] at hfinal ⊢
        rwa [← add_assoc]
  | .b10 scalar base _ :: rest, T :: Ts, acc, .cons hT hrest => by
      simp only [foldChunk]
      have hsf := scaleFast2'_spec (V := V) d 255 2 9 (by norm_num) (by norm_num) base[ci] scalar
      have hadd := fun l => addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
        d.two_torsion_free acc l
      have ih := fun acc' => foldChunk_spec (V := V) ci rest Ts acc' hrest
      mvcgen [-Snarky.Kimchi.addFast_spec, hsf, hadd, ih]
      rename_i _ _ _ hsf' _ _ hadd' _ _
      rintro ⟨rest_infos, hrf, hrest_oc⟩
      obtain ⟨z, bb, h0, hlt, -, hval, hladder⟩ := hsf' T hT
      refine ⟨.scalar 10 z bb T :: rest_infos, List.Forall₂.cons ⟨rfl, hT, h0, hlt, hval⟩ hrf, ?_⟩
      · intro accv hacc hregs
        have hhead : d.LadderRegime 10 (Pasta.Shifted.unshiftType1 10 z) :=
          hregs _ List.mem_cons_self
        have hlad := hladder hhead
        have hstep := hadd' accv _ hacc hlad
        have hrr : ∀ i ∈ rest_infos, i.regimeOK :=
          fun i hi => hregs i (List.mem_cons_of_mem _ hi)
        have hfinal := hrest_oc _ hstep hrr
        simp only [List.map_cons, List.sum_cons, LeafInfo.delta,
          Pasta.Shifted.unshiftType2] at hfinal ⊢
        rwa [← add_assoc]
  | .condAdd b base :: rest, T :: Ts, acc, .cons hT hrest => by
      simp only [foldChunk]
      have haddc := addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
        d.two_torsion_free base[ci] acc
      have hsel := fun t => select_affinePoint_spec (V := V) (c := KimchiConstraint F) b t acc
      have ih := fun acc' => foldChunk_spec (V := V) ci rest Ts acc' hrest
      mvcgen [-Snarky.Kimchi.addFast_spec, haddc, hsel, ih]
      rename_i _ _ _ haddc' _ _ hsel' _ _
      rintro ⟨rest_infos, hrf, hrest_oc⟩
      obtain ⟨hToc, bb, hbb⟩ := hT
      refine ⟨.cond bb T :: rest_infos, List.Forall₂.cons ⟨hToc, hbb⟩ hrf, ?_⟩
      intro accv hacc hregs
      have hr := haddc' T accv hToc hacc
      have hsc := hsel' bb hbb (T + accv) accv hr hacc
      have hrr : ∀ i ∈ rest_infos, i.regimeOK :=
        fun i hi => hregs i (List.mem_cons_of_mem _ hi)
      have hfinal := hrest_oc _ hsc hrr
      simp only [List.map_cons, List.sum_cons, LeafInfo.delta]
      have key : accv + ((if bb then T else 0) + (List.map LeafInfo.delta rest_infos).sum)
          = (if bb then T + accv else accv) + (List.map LeafInfo.delta rest_infos).sum := by
        cases bb
        · rw [if_neg (by decide), if_neg (by decide), zero_add]
        · rw [if_pos rfl, if_pos rfl, add_comm T accv, add_assoc]
      rw [key]
      exact hfinal

/-- **The one-chunk public-input commitment reads as `-(init + Σ deltas) + h`.** Composing
`foldChunk_spec` with the pure negate (`OnCurveAt.neg`) and the final `addFast h`. At the
deployed layer `init` reads as `Σ (-2^{L}·base)` (the corrections) and the shifts in the
deltas cancel it, leaving `-(Σ [scalar]·base) + h = publicCommitment`. -/
private theorem publicInputCommitChunk_spec (ci : Fin nc) {V : Valuation F}
    (init blindingH : AffinePoint (FVar F)) (leaves : List (Leaf F nc)) (Ts : List d.W.Point)
    (Iv Hv : d.W.Point) (hI : OnCurveAt d.W V init Iv) (hH : OnCurveAt d.W V blindingH Hv)
    (hpre : List.Forall₂ (LeafPre ci V) leaves Ts) :
    ⦃⌜True⌝⦄
    publicInputCommitChunk (S := Builder V (KimchiConstraint F)) ci init blindingH leaves
    ⦃⇓ r _ => ⌜∃ infos : List (LeafInfo F d), List.Forall₂ (LeafReads ci V) leaves infos ∧
      ((∀ i ∈ infos, i.regimeOK) →
        OnCurveAt d.W V r (-(Iv + (infos.map LeafInfo.delta).sum) + Hv))⌝⦄ := by
  simp only [publicInputCommitChunk]
  have hfold := foldChunk_spec (V := V) ci leaves Ts init hpre
  have hadd := fun p => addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
    d.two_torsion_free p blindingH
  mvcgen [-Snarky.Kimchi.addFast_spec, hfold, hadd]
  rename_i _ _ _ hfold' _ _
  intro haddpost
  obtain ⟨infos, hrf, hoc⟩ := hfold'
  refine ⟨infos, hrf, fun hregs => ?_⟩
  have hacc := hoc Iv hI hregs
  have hneg := OnCurveAt.neg ⟨d.short.1, d.short.2.2.1⟩ hacc
  exact haddpost _ Hv hneg hH

/-- **The one-chunk gadget computes the honest MSM.** When `init` reads as the corrections'
sum `Σ corrDelta` (over the produced infos), the shifts cancel and the output reads as
`-(Σ netDelta) + h` — `-(Σ [scalar]·base) + h`, the shape `publicCommitment` has. The
`Iv = Σ corrDelta` premise sits inside, after the infos are produced. -/
private theorem publicInputCommitChunk_net_spec (ci : Fin nc) {V : Valuation F}
    (init blindingH : AffinePoint (FVar F)) (leaves : List (Leaf F nc)) (Ts : List d.W.Point)
    (Iv Hv : d.W.Point) (hI : OnCurveAt d.W V init Iv) (hH : OnCurveAt d.W V blindingH Hv)
    (hpre : List.Forall₂ (LeafPre ci V) leaves Ts) :
    ⦃⌜True⌝⦄
    publicInputCommitChunk (S := Builder V (KimchiConstraint F)) ci init blindingH leaves
    ⦃⇓ r _ => ⌜∃ infos : List (LeafInfo F d), List.Forall₂ (LeafReads ci V) leaves infos ∧
      (Iv = (infos.map LeafInfo.corrDelta).sum → (∀ i ∈ infos, i.regimeOK) →
        OnCurveAt d.W V r (-(infos.map LeafInfo.netDelta).sum + Hv))⌝⦄ := by
  refine builder_spec_imp _ _ _
    (publicInputCommitChunk_spec ci init blindingH leaves Ts Iv Hv hI hH hpre) fun r hr => ?_
  obtain ⟨infos, hrf, hoc⟩ := hr
  refine ⟨infos, hrf, fun hIeq hregs => ?_⟩
  have h := hoc hregs
  rw [hIeq, LeafInfo.sum_corrDelta_add_delta] at h
  exact h

omit [ToNat F] in
/-- The bit pre-pass emits constraints and nothing else, so its triple is trivial; it exists
so `mvcgen` can step past the pass in the commitment's specs. -/
private theorem constrainBits_spec {V : Valuation F} :
    ∀ leaves : List (Leaf F nc),
      ⦃⌜True⌝⦄ constrainBits (S := Builder V (KimchiConstraint F)) leaves ⦃⇓ _ _ => ⌜True⌝⦄
  | [] => by simp only [constrainBits]; mvcgen
  | .condAdd _ _ :: rest => by
      simp only [constrainBits]
      have ih := constrainBits_spec (V := V) rest
      mvcgen [ih]
  | .full _ _ _ :: rest => by simp only [constrainBits]; exact constrainBits_spec (V := V) rest
  | .b128 _ _ _ :: rest => by simp only [constrainBits]; exact constrainBits_spec (V := V) rest
  | .b10 _ _ _ :: rest => by simp only [constrainBits]; exact constrainBits_spec (V := V) rest

/-- A boolean leaf's bit is boolean; the scalar leaves say nothing. What the bit pre-pass
forces of each leaf. -/
def Leaf.bitBoolean (V : Valuation F) : Leaf F nc → Prop
  | .condAdd b _ => ∃ bb : Bool, (↑b : CVar F).val V = bit bb
  | _ => True

omit [ToNat F] in
/-- **The bit pre-pass makes every boolean leaf's bit boolean.** The pass is the gadget's own
opening move, so the commitment's read assumes this of its leaves rather than asking a
consumer for it (`builder_spec_bind_assume`). -/
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
/-- **The corrections-sum reads as `accv + Σ` the correction points.** Given each leaf's
correction reads as `cp` (`condAdd`: `0`), `sumCorrections ci acc leaves` reads as
`accv + Σ cps`. By induction on `leaves`, as `sumPoints_spec`. -/
private theorem sumCorrections_spec (ci : Fin nc) {V : Valuation F} :
    ∀ (leaves : List (Leaf F nc)) (cps : List d.W.Point) (acc : AffinePoint (FVar F)),
      List.Forall₂ (CorrPre ci V) leaves cps →
      ⦃⌜True⌝⦄ sumCorrections (S := Builder V (KimchiConstraint F)) ci acc leaves
      ⦃⇓ r _ => ⌜∀ accv : d.W.Point, OnCurveAt d.W V acc accv →
        OnCurveAt d.W V r (accv + cps.sum)⌝⦄
  | [], [], acc, .nil => by
      simp only [sumCorrections]
      mvcgen
      intro accv hacc
      simpa using hacc
  | .full _ _ corr :: rest, cp :: cps, acc, .cons hcp hrest => by
      simp only [sumCorrections]
      have hadd := addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
        d.two_torsion_free acc corr[ci]
      have ih := fun acc' => sumCorrections_spec ci rest cps acc' hrest
      mvcgen [-Snarky.Kimchi.addFast_spec, hadd, ih]
      rename_i _ _ _ haddc' _ _
      intro ihpost accv hacc
      simp only [List.sum_cons]
      rw [← add_assoc]
      exact ihpost _ (haddc' accv cp hacc hcp)
  | .b128 _ _ corr :: rest, cp :: cps, acc, .cons hcp hrest => by
      simp only [sumCorrections]
      have hadd := addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
        d.two_torsion_free acc corr[ci]
      have ih := fun acc' => sumCorrections_spec ci rest cps acc' hrest
      mvcgen [-Snarky.Kimchi.addFast_spec, hadd, ih]
      rename_i _ _ _ haddc' _ _
      intro ihpost accv hacc
      simp only [List.sum_cons]
      rw [← add_assoc]
      exact ihpost _ (haddc' accv cp hacc hcp)
  | .b10 _ _ corr :: rest, cp :: cps, acc, .cons hcp hrest => by
      simp only [sumCorrections]
      have hadd := addFast_checkFinite_spec (V := V) d.W d.short d.two_ne
        d.two_torsion_free acc corr[ci]
      have ih := fun acc' => sumCorrections_spec ci rest cps acc' hrest
      mvcgen [-Snarky.Kimchi.addFast_spec, hadd, ih]
      rename_i _ _ _ haddc' _ _
      intro ihpost accv hacc
      simp only [List.sum_cons]
      rw [← add_assoc]
      exact ihpost _ (haddc' accv cp hacc hcp)
  | .condAdd _ _ :: rest, cp :: cps, acc, .cons hcp hrest => by
      simp only [sumCorrections]
      have hcp0 : cp = 0 := hcp
      refine builder_spec_imp _ _ _
        (sumCorrections_spec ci rest cps acc hrest) fun r hr accv hacc => ?_
      simp only [List.sum_cons, hcp0, zero_add]
      exact hr accv hacc

omit [ToNat F] in
/-- **The head-seeded corrections sum reads as `Σ cps`.** The first scalar leaf's correction
seeds the fold; the rest add via `sumCorrections_spec`; `condAdd` leaves skip (their `cp = 0`).
Needs a scalar leaf (`leafHasScalar`) so the origin is not returned. -/
private theorem sumCorrectionsHead_spec (ci : Fin nc) {V : Valuation F} :
    ∀ (leaves : List (Leaf F nc)) (cps : List d.W.Point),
      List.Forall₂ (CorrPre ci V) leaves cps → leafHasScalar leaves →
      ⦃⌜True⌝⦄ sumCorrectionsHead (S := Builder V (KimchiConstraint F)) ci leaves
      ⦃⇓ r _ => ⌜OnCurveAt d.W V r cps.sum⌝⦄
  | [], [], .nil, hne => by simp only [leafHasScalar] at hne
  | .full _ _ corr :: rest, cp :: cps, .cons hcp hrest, _ => by
      simp only [sumCorrectionsHead]
      refine builder_spec_imp _ _ _ (sumCorrections_spec ci rest cps corr[ci] hrest)
        fun r hr => ?_
      simp only [List.sum_cons]
      exact hr cp hcp
  | .b128 _ _ corr :: rest, cp :: cps, .cons hcp hrest, _ => by
      simp only [sumCorrectionsHead]
      refine builder_spec_imp _ _ _ (sumCorrections_spec ci rest cps corr[ci] hrest)
        fun r hr => ?_
      simp only [List.sum_cons]
      exact hr cp hcp
  | .b10 _ _ corr :: rest, cp :: cps, .cons hcp hrest, _ => by
      simp only [sumCorrectionsHead]
      refine builder_spec_imp _ _ _ (sumCorrections_spec ci rest cps corr[ci] hrest)
        fun r hr => ?_
      simp only [List.sum_cons]
      exact hr cp hcp
  | .condAdd _ _ :: rest, cp :: cps, .cons hcp hrest, hne => by
      simp only [sumCorrectionsHead]
      have hcp0 : cp = 0 := hcp
      refine builder_spec_imp _ _ _ (sumCorrectionsHead_spec ci rest cps hrest hne)
        fun r hr => ?_
      simp only [List.sum_cons, hcp0, zero_add]
      exact hr

/-- **The full one-chunk gadget computes the honest MSM.** Composing the corrections sum with
`publicInputCommitChunk_net_spec`: with `start` reading as `sv` and corrections as `cps`, the
output reads as `-(Σ netDelta) + h`, under the seed condition `sv + Σcps = Σ corrDelta`. -/
theorem publicInputCommitFull_spec (ci : Fin nc) {V : Valuation F}
    (blindingH : AffinePoint (FVar F)) (leaves : List (Leaf F nc))
    (Ts cps : List d.W.Point) (Hv : d.W.Point)
    (hH : OnCurveAt d.W V blindingH Hv)
    (hpre : List.Forall₂ (LeafPre ci V) leaves Ts)
    (hcorr : List.Forall₂ (CorrPre ci V) leaves cps)
    (hscalar : leafHasScalar leaves) :
    ⦃⌜True⌝⦄
    publicInputCommitFull (S := Builder V (KimchiConstraint F)) ci blindingH leaves
    ⦃⇓ r _ => ⌜∃ infos : List (LeafInfo F d), List.Forall₂ (LeafReads ci V) leaves infos ∧
      (cps.sum = (infos.map LeafInfo.corrDelta).sum → (∀ i ∈ infos, i.regimeOK) →
        OnCurveAt d.W V r (-(infos.map LeafInfo.netDelta).sum + Hv))⌝⦄ := by
  simp only [publicInputCommitFull]
  have hbits := constrainBits_spec (V := V) leaves
  have hsum := sumCorrectionsHead_spec ci leaves cps hcorr hscalar
  mvcgen [hbits, hsum]
  rename_i _ rinit
  intro s hpost
  exact publicInputCommitChunk_net_spec ci rinit blindingH leaves Ts cps.sum Hv
    hpost hH hpre s trivial

/-- **The net read, premises discharged.** `publicInputCommitFull_spec` with its seed
(`corrSum_eq`, from honest corrections) and regime (`leafReads_regimeOK_all`, from the width
bounds and the full-width band premise) supplied: the output reads unconditionally as
`-(Σ netDelta) + h`, the honest MSM. The last step before the wire crossing (`publicCommitment`). -/
private theorem publicInputCommitFull_net (ci : Fin nc) {V : Valuation F}
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
    publicInputCommitFull (S := Builder V (KimchiConstraint F)) ci blindingH leaves
    ⦃⇓ r _ => ⌜∃ infos : List (LeafInfo F d), List.Forall₂ (LeafReads ci V) leaves infos ∧
      OnCurveAt d.W V r (-(infos.map LeafInfo.netDelta).sum + Hv)⌝⦄ := by
  refine builder_spec_imp _ _ _
    (publicInputCommitFull_spec ci blindingH leaves Ts cps Hv hH hpre hcorr hscalar)
    fun r hr => ?_
  obtain ⟨infos, hff, himp⟩ := hr
  exact ⟨infos, hff,
    himp (corrSum_eq hcorr hff hhon) (leafReads_regimeOK_all h130 h10 hff (hfull infos hff))⟩

/-- **The honest MSM as a single point.** `publicInputCommitFull_net` with the net-delta sum
identified as a caller-supplied point `msm` (via `hmsm`): the output reads as `-msm + h`. The
wire crossing supplies `msm = publicCommitment`'s MSM and discharges `hmsm` from the canonical
decode. -/
private theorem publicInputCommitFull_msm (ci : Fin nc) {V : Valuation F}
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
    publicInputCommitFull (S := Builder V (KimchiConstraint F)) ci blindingH leaves
    ⦃⇓ r _ => ⌜OnCurveAt d.W V r (-msm + Hv)⌝⦄ := by
  refine builder_spec_imp _ _ _
    (publicInputCommitFull_net ci blindingH leaves Ts cps Hv h130 h10 hfull hH hpre hcorr
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

/-- **The full one-chunk gadget reads as `-(publicMsm) + h`.** `publicInputCommitFull_msm` with
its `hfull`/`hmsm` premises discharged publicly: the regime from `hregime` (`regimeFull_hfull`),
the MSM identity from `netDelta_sum_eq_publicMsm` (needing `hcast`, `hbit`; the canonical decode
is the ladder's own top-bit pin, no premise). The output reads unconditionally as
`-(Σ [scalarₗ]·baseₗ) + h`, the shape the wire's `publicCommitment` has. The clean public seam
the `x_hat` wire crossing consumes — no private `LeafInfo`/`LeafReads`. -/
theorem publicInputCommitFull_reads (ci : Fin nc) {V : Valuation F}
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
    publicInputCommitFull (S := Builder V (KimchiConstraint F)) ci blindingH leaves
    ⦃⇓ r _ => ⌜OnCurveAt d.W V r (-(publicMsm V leaves Ts) + Hv)⌝⦄ :=
  publicInputCommitFull_msm ci blindingH leaves Ts cps Hv (publicMsm V leaves Ts) h130 h10
    (fun _infos hr z bb T hmem => regimeFull_hfull hregime hr z bb T hmem)
    hH hpre hcorr hscalar hhon
    (fun _infos hr => netDelta_sum_eq_publicMsm hcast hbit hr hpre)

/-! ### The known-domain step gadget (`multiscale_known`, PS `PureCorrections`)

The step verifier's `x_hat` at a known domain (`step_verifier.ml:115–174`, PS
`publicInputCommit` in `PureCorrections` mode) emits in three phases: every leaf's bare ladder
first, in leaf order; then the ladder results summed left to right from the first; then one
constant, the summed shift corrections; then negate and add `h`. The corrections are constants
summed outside the circuit (no gates), so the gadget takes their sum as a cell (`corrSum`, a
`.const` at the deployed harness) instead of folding the leaves' correction cells as
`publicInputCommitFull` does. A `condAdd` leaf is a conditional add at its position in the
fold. PS seeds the fold with the first leaf's ladder result and, when the first leaf is a
`condAdd`, with the first correction constant instead (`corrHead`) — dropping that leaf, a PS
quirk the deployed step statement (all scalars) never reaches; the port is literal and the
read is stated for scalar-headed lists. -/

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

/-- The known-domain public-input commitment at one chunk (OCaml `multiscale_known`, PS
`publicInputCommit` in `PureCorrections` mode): the ladders, then their fold with the constant
corrections, negated, plus `h`. -/
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
`publicInputCommitFull_spec`. -/
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
regime (`leafReads_regimeOK_all` from the width bounds and the full-width band premise)
discharged, and the net-delta sum identified with `publicMsm` — the same public seam as
`publicInputCommitFull_reads`, so the wire crossing consumes either gadget. -/
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

end Fold

/-! ## The `x_hat` wire crossing

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
additive-equiv algebra over `publicCommitment_eq_sum` (G1); the wire crossing instantiates it
at `SWPoint.equivPoint`. -/
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

/-! ### The x_hat target: the gadget reads as `publicCommitment` (glue G2, piece 5) -/

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

/-! ### The full leaf's regime: a sixteen-value window -/

/-- `δ = p − 2^254`, with `p` the point-group order: the pinned full-leaf ladder top
`2z + 2^255 + 1` meets the forbidden band exactly at `z ∈ [δ−2, δ+5]`. -/
def xhatBandDelta (p : ℕ) : ℕ := p - 2 ^ 254

/-- A full leaf's scalar value avoids the sixteen values `2z + bb`, `z ∈ [δ−2, δ+5]`, at which
the ladder degenerates; the narrow leaves and `condAdd` carry `True`. The concrete, decidable
form of `Leaf.regimeFull` at a Pasta order `p` — the exact completeness gap of the deployed
gadget. -/
def Leaf.offBand (p : ℕ) (V : Valuation F) : Leaf F nc → Prop
  | .full s _ _ =>
      ToNat.toNat (s.val V) < 2 * xhatBandDelta p - 4 ∨
        2 * xhatBandDelta p + 11 < ToNat.toNat (s.val V)
  | _ => True

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

/-- **The pinned full-leaf ladder is in regime off the window.** With the order `p` in
`(2^254, 2^254 + 2^253)`, for `0 ≤ z < 2^253` the top `2z + 2^255 + 1` lies in `(p, 3p)`, so it
is a forbidden residue `t ∈ [-3, 11]` only as `t + 2p`; that pins the value `2z + bb` into
`[2δ − 4, 2δ + 11]`, `δ = p − 2^254` — the sixteen-value window `Leaf.offBand` excludes. -/
theorem PastaShape.regime (s : PastaShape C) {nc : ℕ} (V : Valuation C.BaseField)
    (leaf : Leaf C.BaseField nc) (h : leaf.offBand C.scalar V) : Leaf.regimeFull s.d V leaf := by
  cases leaf with
  | full sc base corr =>
      intro z bb h0 hlt hval
      have hb01 : (0 : ℤ) ≤ (if bb then 1 else 0) ∧ (if bb then (1 : ℤ) else 0) ≤ 1 := by
        cases bb <;> simp
      have h253 : (2 : ℤ) ^ 253
          = 14474011154664524427946373126085988481658748083205070504932198000989141204992 := by
        norm_num
      have h254 : (2 : ℤ) ^ 254
          = 28948022309329048855892746252171976963317496166410141009864396001978282409984 := by
        norm_num
      have h255 : (2 : ℤ) ^ 255
          = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
        norm_num
      have hlo : (2 : ℤ) ^ 254 < C.scalar := by exact_mod_cast s.scalar_lo
      have hhi : (C.scalar : ℤ) < 2 ^ 254 + 2 ^ 253 := by exact_mod_cast s.scalar_hi
      have hlo' := s.scalar_lo
      have hδ : (xhatBandDelta C.scalar : ℤ) = C.scalar - 2 ^ 254 := by
        unfold xhatBandDelta; omega
      rw [h253] at hlt hhi
      rw [h254] at hlo hhi hδ
      have hv : (ToNat.toNat (sc.val V) : ℤ) = 2 * z + (if bb then 1 else 0) := by
        rw [← hval]
        exact xhatSide_cast s _ (by omega) (by omega)
      simp only [Leaf.offBand] at h
      refine Or.inr ⟨?_, ?_, ?_, ?_⟩ <;> rw [show s.d.W.order = C.scalar from C.order_eq]
      · simpa using s.scalar_lo
      · exact lt_trans s.scalar_hi (by norm_num)
      · exact s.scalar_mod
      · intro hmem
        simp only [Kimchi.Gate.VarBaseMul.forbiddenValues, Set.mem_setOf_eq,
          Kimchi.Gate.VarBaseMul.Ladder.forbiddenResidues, List.mem_cons, List.mem_nil_iff,
          or_false, Pasta.Shifted.unshiftType1] at hmem
        obtain ⟨t, ht, k, hk⟩ := hmem
        rw [h255] at hk
        -- the residues lie in `[-3, 11]`; that is all the bound argument needs (no `omega`:
        -- it enumerates the 253-bit range)
        have htb : -3 ≤ t ∧ t ≤ 11 := by
          rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            norm_num
        -- the multiplier is 2: the top lies in `(p, 3p)`
        have hp0 : (0 : ℤ) ≤ C.scalar := by positivity
        have hk1 : 2 ≤ k := by
          by_contra hle
          have : (C.scalar : ℤ) * k ≤ C.scalar * 1 :=
            mul_le_mul_of_nonneg_left (by omega) hp0
          linarith
        have hk2 : k ≤ 2 := by
          by_contra hle
          have : (C.scalar : ℤ) * 3 ≤ C.scalar * k :=
            mul_le_mul_of_nonneg_left (by omega) hp0
          linarith
        have hk : k = 2 := le_antisymm hk2 hk1
        subst hk
        -- the value then sits in the window
        rcases h with h | h
        · have h' : (ToNat.toNat (sc.val V) : ℤ) < 2 * (xhatBandDelta C.scalar : ℤ) - 4 := by
            have h4 : 4 ≤ 2 * xhatBandDelta C.scalar := by unfold xhatBandDelta; omega
            omega
          linarith
        · have h' : 2 * (xhatBandDelta C.scalar : ℤ) + 11 < ToNat.toNat (sc.val V) := by
            exact_mod_cast h
          linarith
  | b128 _ _ _ => trivial
  | b10 _ _ _ => trivial
  | condAdd _ _ => trivial

end SideFacts

section Binding

variable {C : Bulletproof.Ipa.KimchiCurve} {nc : ℕ}

/-- The `x_hat` tables of a circuit (OCaml `lagrange_with_correction` and `multiscale_known`'s
constant corrections): per public-input scalar its Lagrange base and its shift correction,
chunked, and the correction seed and sum the known-domain fold takes as constants. -/
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
(`pre`/`corr`/`hon`) are exactly the gadget reads', with the regime premise narrowed to the
sixteen-value window `offBand` (`PastaShape.regime`). `Ts` are the leaves' base points, `cps`
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
  /-- Each full leaf's value avoids the sixteen-value band window (`Leaf.offBand`). -/
  offBand : ∀ leaf ∈ leaves, Leaf.offBand C.scalar V leaf
  /-- There are at least as many Lagrange bases as public-input leaves. -/
  hsize : leaves.length ≤ cvk.lagrangeBasis.size
  /-- Each leaf's chunk base reads as the verifier's Lagrange base at that index — the walk-order
  tie the packing item owns. -/
  bases : ∀ (i : ℕ) (hi : i < leaves.length),
    OnCurveAt s.d.W V (leafBaseAt ci leaves[i])
      (SWPoint.equivPoint C.E ((cvk.lagrangeBasis[i]'(lt_of_lt_of_le hi hsize))[ci]))

/-- **The wire's `publicCommitment`, crossed, is `-(publicMsm) + h`.** The shared half of the two
x_hat reads: `equivPoint_publicCommitment` unfolds the wire's MSM, `crossing_list` ties each
Lagrange base to the leaf's base reading, and `neg_publicMsm_sum` moves the negation through
the exact integer → scalar reduction (`KimchiCurve.affine_card_nsmul`). -/
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

/-- **The wrap-side x_hat gadget reads as the wire verifier's `publicCommitment`.** The binding
is asked for only under the boolean leaves' booleanity, which the gadget's bit pre-pass
establishes itself (`constrainBits_boolean`): a consumer never supplies it. The
in-circuit public-input obligation of the group half (`incrementally_verify_proof`):
`publicInputCommitFull` commits to `pubOf leaves`, crossed to Mathlib's point group by
`SWPoint.equivPoint`. The subtle half (the canonical decode — the ladder's top-bit pin —
`-(Σ [scalarₗ]·baseₗ) + h`) is `publicInputCommitFull_reads`; this crosses that to the wire's
`publicCommitment` — the integer → scalar reduction is exact
(`KimchiCurve.affine_card_nsmul`), so the read carries no slack. -/
theorem xHat_reads_publicCommitment (s : PastaShape C) (ci : Fin nc) {V : Valuation C.BaseField}
    (σ : Bulletproof.SRS C.Point) (cvk : Kimchi.Verifier.KimchiVK C nc)
    (blindingH : AffinePoint (FVar C.BaseField)) (leaves : List (Leaf C.BaseField nc))
    (Ts cps : List s.d.W.Point)
    (hbind : (∀ leaf ∈ leaves, leaf.bitBoolean V) →
      XhatBinding s ci V σ cvk blindingH leaves Ts cps)
    (hscalar : leafHasScalar leaves) :
    ⦃⌜True⌝⦄
    publicInputCommitFull (S := Builder V (KimchiConstraint C.BaseField)) ci blindingH leaves
    ⦃⇓ r _ => ⌜OnCurveAt s.d.W V r
      (SWPoint.equivPoint C.E
        (Kimchi.Verifier.publicCommitment C σ cvk (pubOf C V leaves))[ci])⌝⦄ := by
  have hne : leaves ≠ [] := by
    rintro rfl; simp [leafHasScalar] at hscalar
  -- the gadget opens with the bit pre-pass, so its own rows give the leaves' booleanity
  show ⦃⌜True⌝⦄
    (constrainBits (S := Builder V (KimchiConstraint C.BaseField)) leaves >>= fun _ => do
      let init ← sumCorrectionsHead ci leaves
      publicInputCommitChunk ci init blindingH leaves)
    ⦃⇓ r _ => ⌜OnCurveAt s.d.W V r
      (SWPoint.equivPoint C.E
        (Kimchi.Verifier.publicCommitment C σ cvk (pubOf C V leaves))[ci])⌝⦄
  refine builder_spec_bind_assume _ _ _ _ (constrainBits_boolean (V := V) leaves) fun hb => ?_
  have hbind := hbind hb
  refine builder_spec_imp _ _ _
    (publicInputCommitFull_reads (d := s.d) ci blindingH leaves Ts cps
      (SWPoint.equivPoint C.E σ.h)
      (xhatSide_cast s) (xhatSide_bit s) s.order_big
      (le_trans (by norm_num) s.order_big)
      (fun leaf hl => s.regime V leaf (hbind.offBand leaf hl))
      hbind.blinding hbind.pre hbind.corr hscalar hbind.hon) fun r hr => ?_
  rw [xhat_cross s ci σ cvk blindingH leaves Ts cps hbind hne]; exact hr

/-- **The step-side x_hat gadget reads as the wire verifier's `publicCommitment`.** The
known-domain shape (`publicInputCommitKnown`, OCaml `multiscale_known`): the corrections are
constants, so their sum `corrSum` is a single constant cell the binding reads as `Σ cps`, and
the leaves are headed by a scalar leaf. Otherwise `xHat_reads_publicCommitment`. -/
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
      (fun leaf hl => s.regime V leaf (hbind.offBand leaf hl))
      hbind.blinding hbind.pre hbind.corr hC hhead hbind.hon) fun r hr => ?_
  rw [xhat_cross s ci σ cvk blindingH leaves Ts cps hbind hne]; exact hr

/-- An `x_hat` table is bound to the verifier key at the leaves it serves: chunk by chunk, the
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

/-- The `x_hat` leaves of a packed scalar list: scalar `i` with Lagrange base `i` and its shift
correction from the table (`lagrange_with_correction`); a boolean cell adds its base under
the bit, with no correction. -/
def packLeavesOf (ks : List (PackedScalar F)) (tab : XhatTable F nc) : List (Leaf F nc) :=
  List.zipWith (fun k bc => match k with
    | .full s => Leaf.full s bc.1 bc.2
    | .b128 s => Leaf.b128 s bc.1 bc.2
    | .b10 s => Leaf.b10 s bc.1 bc.2
    | .bit b => Leaf.condAdd b bc.1) ks (tab.bases.zip tab.corrs)

end Packed

/-! ## The `x_hat` table of a key

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
def negShift (C : KimchiCurve) (L : ℕ) (P : C.Point) : C.Point :=
  -(C.fastMsm (n := 1) (fun _ => P) (fun _ => ((2 ^ L : ℕ) : ZMod C.scalar)))

theorem negShift_eq (L : ℕ) (P : C.Point) : negShift C L P = (-(2 ^ L : ℤ)) • P := by
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

theorem leafBaseAt_constLeaf (ci : Fin nc) (k : PackedScalar C.BaseField) (Ps : Vector C.Point nc) :
    leafBaseAt ci (constLeaf k Ps) = constPt Ps[ci] := by
  cases k <;> simp [constLeaf, leafBaseAt]

/-- The point group has odd prime order, so a nonzero point shifted by a power of two stays
nonzero: a constant correction cell is a finite point whenever its base is. -/
theorem two_pow_zsmul_ne_zero (s : PastaShape C) (P : C.Point) (hP : P ≠ 0) (L : ℕ) :
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

theorem getElem_map_fin {α β : Type} {n : ℕ} (f : α → β) (Ps : Vector α n) (ci : Fin n) :
    (Ps.map f)[ci] = f Ps[ci] := by
  simp [Fin.getElem_fin]

/-- The correction point a constant leaf's correction cell reads as. -/
noncomputable def constCp (s : PastaShape C) (ci : Fin nc) (k : PackedScalar C.BaseField)
    (Ps : Vector C.Point nc) : s.d.W.Point :=
  match k with
  | .full _ => (-(2 ^ 255 : ℤ)) • SWPoint.equivPoint C.E Ps[ci]
  | .b128 _ => (-(2 ^ 130 : ℤ)) • SWPoint.equivPoint C.E Ps[ci]
  | .b10 _ => (-(2 ^ 10 : ℤ)) • SWPoint.equivPoint C.E Ps[ci]
  | .bit _ => 0

theorem onCurveAt_shift (s : PastaShape C) (P : C.Point) (hP : P ≠ 0) (L : ℕ) :
    OnCurveAt s.d.W V (constPt (negShift C L P))
      ((-(2 ^ L : ℤ)) • SWPoint.equivPoint C.E P) := by
  rw [← map_zsmul, ← negShift_eq]
  exact onCurveAt_constPt _ (negShift_eq L P ▸ two_pow_zsmul_ne_zero s P hP L)

theorem leafPre_const (s : PastaShape C) (ci : Fin nc) (k : PackedScalar C.BaseField)
    (Ps : Vector C.Point nc) (hP : Ps[ci] ≠ 0)
    (hbit : ∀ b, k = .bit b → ∃ bb : Bool, (↑b : CVar C.BaseField).val V = bit bb) :
    LeafPre (d := s.d) ci V (constLeaf k Ps) (SWPoint.equivPoint C.E Ps[ci]) := by
  cases k with
  | bit b => exact ⟨by simpa [constLeaf] using onCurveAt_constPt (V := V) Ps[ci] hP, hbit b rfl⟩
  | _ => simpa [constLeaf, LeafPre] using onCurveAt_constPt (V := V) Ps[ci] hP

theorem corrPre_const (s : PastaShape C) (ci : Fin nc) (k : PackedScalar C.BaseField)
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

theorem corrHonest_const (s : PastaShape C) (ci : Fin nc) (k : PackedScalar C.BaseField)
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

theorem forall₂_zipWith {α β γ δ : Type} (R : γ → δ → Prop) (f : α → β → γ) (g : α → β → δ) :
    ∀ (ks : List α) (lb : List β), (∀ p ∈ ks.zip lb, R (f p.1 p.2) (g p.1 p.2)) →
      List.Forall₂ R (List.zipWith f ks lb) (List.zipWith g ks lb)
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | k :: ks, P :: lb, h => by
      simp only [List.zipWith_cons_cons]
      exact List.Forall₂.cons (h (k, P) (by simp))
        (forall₂_zipWith R f g ks lb fun p hp => h p (by simp [hp]))

/-- **The table computed from the key is bound to the key.** Constant cells — the Lagrange
points as bases, their honest shifts as corrections, the SRS blinding base — satisfy
`XhatBinding` given only what is not table bookkeeping: the blinding base and the Lagrange
points are finite (at the `(0, 0)` sentinel no cell reads as the point, so this is necessary
too), the boolean leaves are boolean — which `xHat_reads_publicCommitment` supplies from the
gadget's own bit pre-pass — and `offBand`. -/
theorem xhatBinding_const (s : PastaShape C) (ci : Fin nc) (σ : SRS C.Point)
    (cvk : KimchiVK C nc) (ks : List (PackedScalar C.BaseField))
    (hh : σ.h ≠ 0)
    (hL : ∀ Ps ∈ cvk.lagrangeBasis.toList, Ps[ci] ≠ 0)

    (hbits : ∀ leaf ∈ List.zipWith constLeaf ks cvk.lagrangeBasis.toList, leaf.bitBoolean V)
    (hoff : ∀ leaf ∈ List.zipWith constLeaf ks cvk.lagrangeBasis.toList,
      Leaf.offBand C.scalar V leaf) :
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
  offBand := hoff
  hsize := by simp [List.length_zipWith]
  bases := by
    intro i hi
    rw [List.getElem_zipWith, leafBaseAt_constLeaf]
    have h := onCurveAt_constPt (V := V) _ (hL _ (List.getElem_mem
      (l := cvk.lagrangeBasis.toList) (n := i) (by
        simp only [List.length_zipWith, Array.length_toList] at hi; simp; omega)))
    simpa using h

/-- The ladder width of a packed scalar's kind; a boolean leaf has no correction. -/
def shiftBits : PackedScalar C.BaseField → Option ℕ
  | .full _ => some 255
  | .b128 _ => some 130
  | .b10 _ => some 10
  | .bit _ => none

/-- The `x_hat` table computed from the key's Lagrange points, at a statement's packing. A
boolean leaf's correction slot is never read (`packLeavesOf` drops it); it holds the base. -/
def XhatTable.ofKey (ks : List (PackedScalar C.BaseField)) (lb : List (Vector C.Point nc)) :
    XhatTable C.BaseField nc where
  bases := lb.map (·.map constPt)
  corrs := List.zipWith (fun k Ps => Ps.map fun P =>
    constPt (match shiftBits k with | some L => negShift C L P | none => P)) ks lb
  corrHead := Vector.replicate nc (constPt 0)
  corrSum := Vector.replicate nc (constPt 0)

/-- The library's `packLeavesOf` at that table is the constant leaves. -/
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

/-! ### The known-domain fold's table

`publicInputCommitKnown` takes the corrections' sum as one constant, where
`publicInputCommitFull` adds each leaf's correction. The table below carries that sum; the cell
reads as a point only when the sum is a finite point, which no invariant of the key gives: it
is one fixed relation among the Lagrange points. -/

/-- The correction point of a packed scalar at a Lagrange point: its honest shift `-(2^L)·P`,
none for a boolean cell. -/
def corrPt (k : PackedScalar C.BaseField) (P : C.Point) : C.Point :=
  match shiftBits k with
  | some L => negShift C L P
  | none => 0

/-- The constant correction sum of the known-domain fold, at chunk `ci`. -/
def corrSumPt (ks : List (PackedScalar C.BaseField)) (lb : List (Vector C.Point nc))
    (ci : Fin nc) : C.Point :=
  (List.zipWith (fun k Ps => corrPt k Ps[ci]) ks lb).sum

/-- The `x_hat` table of the known-domain fold, computed from the key's Lagrange points: the
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

/-- The library's `packLeavesOf` at that table is the constant leaves. -/
theorem packLeavesOf_ofKeyKnown (ks : List (PackedScalar C.BaseField))
    (lb : List (Vector C.Point nc)) :
    packLeavesOf ks (XhatTable.ofKeyKnown ks lb) = List.zipWith constLeaf ks lb :=
  packLeavesOf_ofKey ks lb

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
    (hoff : ∀ leaf ∈ List.zipWith constLeaf ks cvk.lagrangeBasis.toList,
      Leaf.offBand C.scalar V leaf)
    (hsum : ∀ ci : Fin nc, corrSumPt ks cvk.lagrangeBasis.toList ci ≠ 0) :
    (XhatTable.ofKeyKnown ks cvk.lagrangeBasis.toList).Bound s V σ cvk (constPt σ.h)
      (List.zipWith constLeaf ks cvk.lagrangeBasis.toList) where
  chunks := by
    refine ⟨List.zipWith (fun _ Ps => fun ci => SWPoint.equivPoint C.E Ps[ci]) ks
        cvk.lagrangeBasis.toList,
      List.zipWith (fun k Ps => fun ci => constCp s ci k Ps) ks cvk.lagrangeBasis.toList,
      fun ci => ⟨?_, ?_⟩⟩
    · have hb := xhatBinding_const (V := V) s ci σ cvk ks hh (fun Ps h => hL Ps h ci) hbits hoff
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

theorem corrPt_eq_smul (k : PackedScalar C.BaseField) (P : C.Point) :
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

private theorem sum_corrCoeffs_range' {m N : ℕ} (L : ℕ → Fin m → C.ScalarField)
    (hL : ∀ i, 0 < i → i < N → ∑ j, L i j = 0) :
    ∀ (ks : List (PackedScalar C.BaseField)) (s len : ℕ), 0 < s → s + len ≤ N →
      ∑ j, corrCoeffs ks ((List.range' s len).map L) j = 0
  | [], _, _, _, _ => by simp [corrCoeffs]
  | _ :: _, _, 0, _, _ => by simp [corrCoeffs]
  | k :: ks, s, len + 1, hs, hle => by
      have ih := sum_corrCoeffs_range' L hL ks (s + 1) len (by omega) (by omega)
      simp only [corrCoeffs, List.range'_succ, List.map_cons, List.zipWith_cons_cons,
        List.sum_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum] at ih ⊢
      rw [ih, hL s hs (by omega)]
      simp

/-- The correction sum's coefficients sum to the first leaf's shift coefficient, where the
first vector's sum to one and the later ones' to zero. -/
theorem sum_corrCoeffs {m N : ℕ} (L : ℕ → Fin m → C.ScalarField) (h0 : ∑ j, L 0 j = 1)
    (hL : ∀ i, 0 < i → i < N → ∑ j, L i j = 0) (k : PackedScalar C.BaseField)
    (ks : List (PackedScalar C.BaseField)) (size : ℕ) (hpos : 0 < size) (hle : size ≤ N) :
    ∑ j, corrCoeffs (k :: ks) ((List.range size).map L) j = shiftCoeff k := by
  obtain ⟨len, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have ih := sum_corrCoeffs_range' L hL ks 1 len one_pos (by omega)
  rw [List.range_eq_range', List.range'_succ]
  simp only [corrCoeffs, List.map_cons, List.zipWith_cons_cons, List.sum_cons, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at ih ⊢
  rw [ih, h0]
  simp

end OfKey

/-! The gadgets are sealed after their reads: a consumer composes `publicInputCommitFull_reads`,
`publicInputCommitKnown_reads` or `xHat_reads_publicCommitment`, never the body. -/
attribute [irreducible] foldChunk publicInputCommitChunk sumCorrections sumCorrectionsHead
  publicInputCommitFull ladders foldKnown commitKnownTail publicInputCommitKnown

end Pickles
