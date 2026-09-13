import Snarky.Kimchi.Circuit.VarBaseMul
import Snarky.Kimchi.Circuit.AddComplete
import Snarky.Kimchi.Circuit.Point
import Kimchi.Verifier.Kimchi
import Bulletproof.Wire
import Pasta.Basic

/-!
# The in-circuit public-input commitment (`x_hat`)

The port of PS `Pickles.PublicInputCommit.publicInputCommit` (OCaml
`Public_input.commitment` / `lagrange_with_correction`): the per-chunk MSM that commits to
a proof's public input, `x_hat[c] = -(Σ_leaf [scalarₗ]·baseₗ[c]) + h`.

The public input reaches this gadget as a flat list of size-tagged `Leaf`s — a scalar with
its ladder width, or a 1-bit `condAdd`. Packing (a structured statement → this list) is a
separate concern; this module's soundness claim is stated against the list, and lands on
`Kimchi.Verifier.publicCommitment` via `publicCommitment_eq_sum`.

The last section is the wire crossing (glue G2, second half): `publicInputCommitFull_reads`
reads the gadget output as `-(Σ netDelta) + h` over Mathlib's Vesta point group (`d.W.Point`);
`xHat_reads_publicCommitment` crosses that to the wire verifier's own
`Kimchi.Verifier.publicCommitment` on the commitment curve (`SWPoint Vesta.curve`), via
`SWPoint.equivPoint` and the integer→scalar reduction `vesta_zsmul_eq` (exact — the group's
characteristic is the scalar order, so there is no `lowest_128_bits` slack here). It is
curve-specific (wrap side, Vesta / `IpaVesta`), unlike the generic gadget above it.
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

/-- The full one-chunk public-input commitment (PS `publicInputCommit`, one chunk): head-seed
the corrections into `init`, fold the ladders, negate, add `h`. -/
def publicInputCommitFull (ci : Fin nc) (blindingH : AffinePoint (FVar F))
    (leaves : List (Leaf F nc)) : CircuitM F S (AffinePoint (FVar F)) := do
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
  have hsum := sumCorrectionsHead_spec ci leaves cps hcorr hscalar
  mvcgen [hsum]
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

end Fold

/-! ## The `x_hat` wire crossing (Vesta)

`publicInputCommitFull_reads` reads the gadget output as `-(Σ netDelta) + h` over Mathlib's
Vesta point group; this section crosses that to the wire verifier's `publicCommitment` on the
commitment curve. The two short reduction lemmas are private in `CheckBulletproof`, so
restated here. -/

section XhatCrossing

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass

/-- The Vesta commitment-curve scalar field, `ZMod PALLAS_BASE_CARD`. -/
abbrev XhatFp := Bulletproof.IpaVesta.curve.ScalarField

section Crossing

variable {G : Type} [AddCommGroup G]

/-- In a group killed by `n`, an integer acts as its residue's canonical representative.
(Restated from `CheckBulletproof`, where it is private.) -/
private theorem zsmul_eq_val_nsmul (n : ℕ) [NeZero n] (hn : ∀ x : G, n • x = 0) (z : ℤ) (x : G) :
    z • x = ((z : ZMod n).val : ℕ) • x := by
  have hv : (((z : ZMod n).val : ℕ) : ℤ) = z % n := ZMod.val_intCast z
  rw [← natCast_zsmul, hv]
  conv_lhs => rw [← Int.emod_add_mul_ediv z n]
  rw [add_zsmul, mul_zsmul, natCast_zsmul, hn, _root_.add_zero]

end Crossing

/-- The Vesta point group is killed by its order. -/
private theorem vesta_card_nsmul (X : Vesta.curve.toAffine.Point) : PALLAS_BASE_CARD • X = 0 :=
  ZModModule.char_nsmul_eq_zero (n := PALLAS_BASE_CARD) X

/-- An integer acts on Vesta points as its residue's representative in the scalar field. -/
private theorem vesta_zsmul_eq (z : ℤ) (X : Vesta.curve.toAffine.Point) :
    z • X = ((z : XhatFp).val : ℕ) • X :=
  zsmul_eq_val_nsmul PALLAS_BASE_CARD vesta_card_nsmul z X

/-- **Negating an `ℕ`-scaling on a Vesta point is the `Fp`-negated scalar's scaling.** The MSM's
`-(n·X)` is `((-n : Fp)).val · X` — the group's characteristic is the scalar order, so the
`ℕ → Fp` reduction and the negation commute exactly. -/
private theorem neg_nsmul_eq (n : ℕ) (X : Vesta.curve.toAffine.Point) :
    -((n : ℕ) • X) = ((-(n : XhatFp)).val : ℕ) • X := by
  rw [← natCast_zsmul, ← neg_zsmul, vesta_zsmul_eq]
  simp only [Int.cast_neg, Int.cast_natCast]

/-- **The negated `publicMsm` term list is the wire's negated-scalar term list.** Termwise
`-((f aₗ) · Tₗ) = ((-↑(f aₗ)).val · Tₗ)` over `neg_nsmul_eq`, lifted over the (leaf, base) list —
the shape `equivPoint_publicCommitment` produces once the scalars line up. -/
private theorem neg_publicMsm_sum {A : Type} (f : A → ℕ)
    (l : List (A × Vesta.curve.toAffine.Point)) :
    -(l.map (fun p => f p.1 • p.2)).sum
      = (l.map (fun p => ((-(↑(f p.1) : XhatFp)).val : ℕ) • p.2)).sum := by
  induction l with
  | nil => simp
  | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons, neg_add]
      rw [neg_nsmul_eq, ih]

/-- **`publicCommitment`'s chunk, transported through an additive equivalence on the point
group.** The wire's negated-scalar MSM with each Lagrange base mapped over, plus `h`. Pure
additive-equiv algebra over `publicCommitment_eq_sum` (G1); the wire crossing instantiates it
at `SWPoint.equivPoint`. -/
theorem equivPoint_publicCommitment {C : Bulletproof.Ipa.CommitmentCurve} {nc : ℕ} {G : Type}
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

/-- The public input the leaves commit to, as the wire verifier's `Fp` scalar array: each
scalar leaf contributes its `Fq` scalar's value cast to `Fp` — the group-order reduction the
MSM performs on the in-circuit scalar — and each `condAdd` its bit. The `ℕ → Fp` cast IS the
reduction, so no slack predicate is needed. -/
def pubOf {nc : ℕ} (V : Valuation Fq) (leaves : List (Leaf Fq nc)) : Array XhatFp :=
  (leaves.map (fun leaf => ((leaf.scalarVar.val V).val : XhatFp))).toArray

/-- One leaf's chunk base at `ci`. -/
def leafBaseAt {nc : ℕ} (ci : Fin nc) : Leaf Fq nc → AffinePoint (FVar Fq)
  | .full _ base _ => base[ci]
  | .b128 _ base _ => base[ci]
  | .b10 _ base _ => base[ci]
  | .condAdd _ base => base[ci]

/-- `pubOf` has one entry per leaf. -/
theorem pubOf_size {nc : ℕ} (V : Valuation Fq) (leaves : List (Leaf Fq nc)) :
    (pubOf V leaves).size = leaves.length := by simp [pubOf]

/-- A leaf's `LeafPre` reading names its base cell on the curve at that point — the on-curve
half of `LeafPre` for every leaf shape (`condAdd` also carries a bit clause). -/
private theorem leafPre_onCurve {nc : ℕ} (ci : Fin nc) (V : Valuation Fq)
    (leaf : Leaf Fq nc) (T : HasCurve.vesta.W.Point) (h : LeafPre ci V leaf T) :
    OnCurveAt HasCurve.vesta.W V (leafBaseAt ci leaf) T := by
  cases leaf <;> first | exact h | exact h.1

/-- **The wire's negated-scalar MSM term list equals the crossed `publicMsm` term list.** The
walk-order correspondence: at each `i`, the wire pairs Lagrange base `i` with `pubOf`'s `i`-th
scalar, and the gadget pairs leaf `i`'s base — read as that same Lagrange base by `htie` — with
its own scalar. The `Fq → Fp` reduction (`ZMod.natCast_val`) makes the scalars agree. -/
private theorem crossing_list {nc : ℕ} (ci : Fin nc) (V : Valuation Fq)
    (cvk : Kimchi.Verifier.KimchiVK Bulletproof.IpaVesta.curve nc)
    (leaves : List (Leaf Fq nc)) (Ts : List HasCurve.vesta.W.Point)
    (hlen : Ts.length = leaves.length)
    (hsize : leaves.length ≤ cvk.lagrangeBasis.size)
    (htie : ∀ (i : ℕ) (hi : i < leaves.length),
      Ts[i]'(hlen ▸ hi)
        = (SWPoint.equivPoint Vesta.curve) ((cvk.lagrangeBasis[i]'(lt_of_lt_of_le hi hsize))[ci])) :
    ((cvk.lagrangeBasis.extract 0 (pubOf V leaves).size).zip (pubOf V leaves)).toList.map
        (fun Pp => (-Pp.2).val • (SWPoint.equivPoint Vesta.curve) (Pp.1[ci]))
      = (leaves.zip Ts).map
          (fun p => ((-(↑(ToNat.toNat (p.1.scalarVar.val V)) : XhatFp)).val : ℕ) • p.2) := by
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
    rfl

/-! ### The full leaf's regime at Vesta: a sixteen-value window -/

/-- `δ = p − 2^254`, with `p` the Vesta order: the pinned full-leaf ladder top `2z + 2^255 + 1`
meets the forbidden band exactly at `z ∈ [δ−2, δ+5]`. -/
def xhatBandDelta : ℕ := PALLAS_BASE_CARD - 2 ^ 254

/-- A full leaf's scalar value avoids the sixteen values `2z + bb`, `z ∈ [δ−2, δ+5]`, at which
the ladder degenerates; the narrow leaves and `condAdd` carry `True`. The concrete, decidable
form of `Leaf.regimeFull` at Vesta — the exact completeness gap of the deployed gadget. -/
def Leaf.offBand {nc : ℕ} (V : Valuation Fq) : Leaf Fq nc → Prop
  | .full s _ _ =>
      ToNat.toNat (s.val V) < 2 * xhatBandDelta - 4 ∨
        2 * xhatBandDelta + 11 < ToNat.toNat (s.val V)
  | _ => True

/-- **The pinned full-leaf ladder is in regime off the window.** For `0 ≤ z < 2^253` the top
`2z + 2^255 + 1` lies in `(2p − 2^126, 3p)`, so it is a forbidden residue `t` only as `t + 2p`;
parity kills the even `t`, and each odd `t` pins `z = δ + (t−1)/2`, inside the window. -/
theorem Leaf.regimeFull_of_offBand {nc : ℕ} (V : Valuation Fq) (leaf : Leaf Fq nc)
    (h : leaf.offBand V) : Leaf.regimeFull HasCurve.vesta V leaf := by
  cases leaf with
  | full s base corr =>
      intro z bb h0 hlt hval
      have hOv : HasCurve.vesta.W.order = PALLAS_BASE_CARD := Pasta.vesta_card
      have hb01 : (0 : ℤ) ≤ (if bb then 1 else 0) ∧ (if bb then (1 : ℤ) else 0) ≤ 1 := by
        cases bb <;> simp
      have h253 : (2 : ℤ) ^ 253
          = 14474011154664524427946373126085988481658748083205070504932198000989141204992 := by
        norm_num
      have h255 : (2 : ℤ) ^ 255
          = 57896044618658097711785492504343953926634992332820282019728792003956564819968 := by
        norm_num
      have hp : (PALLAS_BASE_CARD : ℤ)
          = 28948022309329048855892746252171976963363056481941560715954676764349967630337 := by
        norm_num [PALLAS_BASE_CARD]
      have hδ : xhatBandDelta = 45560315531419706090280762371685220353 := by
        norm_num [xhatBandDelta, PALLAS_BASE_CARD]
      rw [h253] at hlt
      have hv : (ToNat.toNat (s.val V) : ℤ) = 2 * z + (if bb then 1 else 0) := by
        rw [← hval]
        exact toNat_intCast_of_lt PALLAS_SCALAR_CARD (by omega)
          (lt_of_lt_of_le (by omega : 2 * z + (if bb then 1 else 0) < 2 ^ 254)
            (by norm_num [PALLAS_SCALAR_CARD]))
      simp only [Leaf.offBand, hδ] at h
      refine Or.inr ⟨?_, ?_, ?_, ?_⟩ <;> rw [hOv]
      · decide
      · decide
      · decide
      · intro hmem
        simp only [Kimchi.Gate.VarBaseMul.forbiddenValues, Set.mem_setOf_eq,
          Kimchi.Gate.VarBaseMul.Ladder.forbiddenResidues, List.mem_cons, List.mem_nil_iff,
          or_false, Pasta.Shifted.unshiftType1] at hmem
        obtain ⟨t, ht, k, hk⟩ := hmem
        rw [hp, h255] at hk
        -- the residues lie in `[-3, 11]`; that is all the bound argument needs (no `omega`:
        -- it enumerates the 253-bit range)
        have htb : -3 ≤ t ∧ t ≤ 11 := by
          rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            norm_num
        -- the multiplier is 2: the top lies in `(p, 3p)`
        have hk1 : 1 + 1 ≤ k := Int.add_one_le_iff.mpr (lt_of_not_ge fun hle => by linarith)
        have hk2 : k ≤ 2 := Int.lt_add_one_iff.mp (lt_of_not_ge fun hle => by linarith)
        have hk : k = 2 := le_antisymm hk2 (by linarith)
        subst hk
        -- the value then sits in the window
        norm_num at h
        rcases h with h | h
        · have h' : (ToNat.toNat (s.val V) : ℤ) < 91120631062839412180561524743370440702 := by
            exact_mod_cast h
          linarith
        · have h' : (91120631062839412180561524743370440717 : ℤ) < ToNat.toNat (s.val V) := by
            exact_mod_cast h
          linarith
  | b128 _ _ _ => trivial
  | b10 _ _ _ => trivial
  | condAdd _ _ => trivial

/-- The binding the deferred packing item discharges — everything the faithfulness read needs
of the outside world, in public terms (no `LeafInfo`/`LeafReads`). The scalar-side alias
(`Fq → Fp`) is absorbed into `pubOf`, and the fold premises (`pre`/`corr`/`scalar`/`hon`) are
exactly `publicInputCommitFull_reads`'s, with its regime premise narrowed to the sixteen-value
window `offBand` (`Leaf.regimeFull_of_offBand`). `Ts` are the leaves' base points, `cps` their
correction points. -/
structure XhatBinding {nc : ℕ} (ci : Fin nc) (V : Valuation Fq)
    (σ : Bulletproof.SRS Bulletproof.IpaVesta.curve.Point)
    (cvk : Kimchi.Verifier.KimchiVK Bulletproof.IpaVesta.curve nc)
    (blindingH : AffinePoint (FVar Fq)) (leaves : List (Leaf Fq nc))
    (Ts cps : List HasCurve.vesta.W.Point) : Prop where
  /-- The blinding cell reads as the verifier's SRS blinding `σ.h`, crossed to the Vesta group. -/
  blinding : OnCurveAt HasCurve.vesta.W V blindingH ((SWPoint.equivPoint Vesta.curve) σ.h)
  /-- Each leaf reads its base cell as a curve point `Ts[i]` (and its bit, for `condAdd`). -/
  pre : List.Forall₂ (LeafPre ci V) leaves Ts
  /-- Each leaf's correction cell reads as `cps[i]`. -/
  corr : List.Forall₂ (CorrPre ci V) leaves cps
  /-- The leaves reach a scalar leaf (so the corrections fold has a seed). -/
  scalar : leafHasScalar leaves
  /-- Each leaf's correction is the honest shift `-(2^L)·base`. -/
  hon : ∀ leaf ∈ leaves, CorrHonest HasCurve.vesta ci V leaf
  /-- Each full leaf's value avoids the sixteen-value band window (`Leaf.offBand`). -/
  offBand : ∀ leaf ∈ leaves, Leaf.offBand V leaf
  /-- There are at least as many Lagrange bases as public-input leaves. -/
  hsize : leaves.length ≤ cvk.lagrangeBasis.size
  /-- Each leaf's chunk base reads as the verifier's Lagrange base at that index — the walk-order
  tie the packing item owns. -/
  bases : ∀ (i : ℕ) (hi : i < leaves.length),
    OnCurveAt HasCurve.vesta.W V (leafBaseAt ci leaves[i])
      ((SWPoint.equivPoint Vesta.curve) ((cvk.lagrangeBasis[i]'(lt_of_lt_of_le hi hsize))[ci]))

/-- **The x_hat commitment gadget reads as the wire verifier's `publicCommitment`.** The
in-circuit public-input obligation of the group half (`incrementally_verify_proof`):
`publicInputCommitFull` commits to `pubOf leaves`, crossed to Mathlib's Vesta group by
`SWPoint.equivPoint`. The subtle half (the canonical `Fq` decode — the ladder's top-bit pin —
`-(Σ [scalarₗ]·baseₗ) + h`) is `publicInputCommitFull_reads`; this crosses that to the wire's
`publicCommitment` — the `Fq → Fp` reduction is exact (`vesta_zsmul_eq`), so the read carries
no slack. -/
theorem xHat_reads_publicCommitment {nc : ℕ} (ci : Fin nc) {V : Valuation Fq}
    (σ : Bulletproof.SRS Bulletproof.IpaVesta.curve.Point)
    (cvk : Kimchi.Verifier.KimchiVK Bulletproof.IpaVesta.curve nc)
    (blindingH : AffinePoint (FVar Fq)) (leaves : List (Leaf Fq nc))
    (Ts cps : List HasCurve.vesta.W.Point)
    (hbind : XhatBinding ci V σ cvk blindingH leaves Ts cps) :
    ⦃⌜True⌝⦄
    publicInputCommitFull (S := Builder V (KimchiConstraint Fq)) ci blindingH leaves
    ⦃⇓ r _ => ⌜OnCurveAt HasCurve.vesta.W V r
      ((SWPoint.equivPoint Vesta.curve)
        (Kimchi.Verifier.publicCommitment Bulletproof.IpaVesta.curve σ cvk
          (pubOf V leaves))[ci])⌝⦄ := by
  have hcast : ∀ m : ℤ, 0 ≤ m → m < 2 ^ 254 → (ToNat.toNat ((m : Fq)) : ℤ) = m :=
    fun m hm0 hmlt => toNat_intCast_of_lt PALLAS_SCALAR_CARD hm0
      (lt_of_lt_of_le hmlt (by norm_num [PALLAS_SCALAR_CARD]))
  have hbit : ∀ b : Bool, ToNat.toNat (bit b : Fq) = if b then 1 else 0 := by
    haveI : Fact (1 < PALLAS_SCALAR_CARD) := ⟨by norm_num [PALLAS_SCALAR_CARD]⟩
    intro b
    cases b
    · show ZMod.val (bit false : Fq) = 0; simp [bit]
    · show ZMod.val (bit true : Fq) = 1; simp [bit, ZMod.val_one]
  have h130 : 3 * 2 ^ 130 ≤ HasCurve.vesta.W.order := by
    rw [Pasta.vesta_card]; norm_num [PALLAS_BASE_CARD]
  have h10 : 3 * 2 ^ 10 ≤ HasCurve.vesta.W.order := by
    rw [Pasta.vesta_card]; norm_num [PALLAS_BASE_CARD]
  have hlen : Ts.length = leaves.length := (List.Forall₂.length_eq hbind.pre).symm
  have htie : ∀ (i : ℕ) (hi : i < leaves.length),
      Ts[i]'(hlen ▸ hi)
        = (SWPoint.equivPoint Vesta.curve)
            ((cvk.lagrangeBasis[i]'(lt_of_lt_of_le hi hbind.hsize))[ci]) := by
    intro i hi
    have hpre_i : LeafPre ci V leaves[i] (Ts[i]'(hlen ▸ hi)) :=
      hbind.pre.get hi (hlen ▸ hi)
    exact OnCurveAt.eq (leafPre_onCurve ci V _ _ hpre_i) (hbind.bases i hi) rfl rfl
  have hne : (pubOf V leaves).size ≠ 0 := by
    rw [pubOf_size]
    intro h0
    rw [List.length_eq_zero_iff.mp h0] at hbind
    simpa [leafHasScalar] using hbind.scalar
  have hpm : -(publicMsm V leaves Ts)
      = ((leaves.zip Ts).map
          (fun p => ((-(↑(ToNat.toNat (p.1.scalarVar.val V)) : XhatFp)).val : ℕ) • p.2)).sum := by
    rw [publicMsm]
    exact neg_publicMsm_sum (fun leaf => ToNat.toNat (leaf.scalarVar.val V)) (leaves.zip Ts)
  have hcross : (SWPoint.equivPoint Vesta.curve)
        (Kimchi.Verifier.publicCommitment Bulletproof.IpaVesta.curve σ cvk (pubOf V leaves))[ci]
      = -(publicMsm V leaves Ts) + (SWPoint.equivPoint Vesta.curve) σ.h := by
    rw [equivPoint_publicCommitment (SWPoint.equivPoint Vesta.curve) σ cvk (pubOf V leaves) ci hne,
      crossing_list ci V cvk leaves Ts hlen hbind.hsize htie, hpm]
  refine builder_spec_imp _ _ _
    (publicInputCommitFull_reads (d := HasCurve.vesta) ci blindingH leaves Ts cps
      ((SWPoint.equivPoint Vesta.curve) σ.h) hcast hbit h130 h10
      (fun leaf hl => Leaf.regimeFull_of_offBand V leaf (hbind.offBand leaf hl))
      hbind.blinding hbind.pre hbind.corr hbind.scalar hbind.hon) fun r hr => ?_
  rw [hcross]; exact hr

end XhatCrossing

/-! The gadgets are sealed after their reads: a consumer composes `publicInputCommitFull_reads`
or `xHat_reads_publicCommitment`, never the body. -/
attribute [irreducible] foldChunk publicInputCommitChunk sumCorrections sumCorrectionsHead
  publicInputCommitFull

end Pickles
