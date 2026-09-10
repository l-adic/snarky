import Snarky.Kimchi.Circuit.VarBaseMul
import Snarky.Kimchi.Circuit.AddComplete
import Snarky.Kimchi.Circuit.Point
import Kimchi.Verifier.Kimchi

/-!
# The in-circuit public-input commitment (`x_hat`)

The port of PS `Pickles.PublicInputCommit.publicInputCommit` (OCaml
`Public_input.commitment` / `lagrange_with_correction`): the per-chunk MSM that commits to
a proof's public input, `x_hat[c] = -(Σ_leaf [scalarₗ]·baseₗ[c]) + h`.

The public input reaches this gadget as a flat list of size-tagged `Leaf`s — a scalar with
its ladder width, or a 1-bit `condAdd`. Packing (a structured statement → this list) is a
separate concern; this module's soundness claim is stated against the list, and lands on
`Kimchi.Verifier.publicCommitment` via `publicCommitment_eq_sum`.
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
private inductive Leaf (F : Type) [Field F] (nc : ℕ) where
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
private def LeafPre (ci : Fin nc) (V : Valuation F) : Leaf F nc → d.W.Point → Prop
  | .full _ base _, T => OnCurveAt d.W V base[ci] T
  | .b128 _ base _, T => OnCurveAt d.W V base[ci] T
  | .b10 _ base _, T => OnCurveAt d.W V base[ci] T
  | .condAdd b base, T =>
      OnCurveAt d.W V base[ci] T ∧ ∃ bb : Bool, (↑b : CVar F).val V = bit bb

/-- One leaf reads as one `LeafInfo` at chunk `ci`: the base on-curve as `T`, the scalar split
pinned to the scalar's value (with the width's range on `z`), or the `condAdd` bit read. The
ladder regime is deliberately absent — it is `LeafInfo.regimeOK`, a premise of the fold. -/
private def LeafReads (ci : Fin nc) (V : Valuation F) : Leaf F nc → LeafInfo F d → Prop
  | .full scalar base _, .scalar L z bb T =>
      L = 255 ∧ OnCurveAt d.W V base[ci] T ∧ 0 ≤ z ∧ z < 2 ^ 254 ∧
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
      obtain ⟨z, bb, h0, hlt, hval, hladder⟩ := hsf' T hT
      refine ⟨.scalar 255 z bb T :: rest_infos, List.Forall₂.cons ⟨rfl, hT, h0, hlt, hval⟩ hrf, ?_⟩
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
      obtain ⟨z, bb, h0, hlt, hval, hladder⟩ := hsf' T hT
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
      obtain ⟨z, bb, h0, hlt, hval, hladder⟩ := hsf' T hT
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

end Fold

end Pickles
