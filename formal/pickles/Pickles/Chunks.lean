import Snarky.DSL.Field
import Snarky.WP
import Kimchi.Verifier.Kimchi

set_option mvcgen.warning false

/-!
# Evaluations at several chunks

A polynomial of degree above the SRS size is committed in chunks, and each of its evaluations
arrives as one value per chunk. Kimchi's verifier recombines the chunks at the evaluation point
raised to the SRS length (`combineAt`, as `KimchiProof.linEvals` does per column). This module is
that recombination as a circuit, with its reading; it transcribes the chunk helpers of
`PlonkChecks.purs` and `step_verifier.ml`.

## Main definitions

* `ChunkedEvals`: a proof's evaluations at `nc` chunks per column.
* `hornerChunks`: `∑ᵢ chunks[i] · ptⁱ` in circuit.
* `collapseColumn`, `collapseEvals`: every column recombined, in a fixed emission order.
* `publicFold`, `zetaToSrsOr`: the public chunks folded at `ζ^(2^srs)`, and that power shared
  with the plonk check.
* `combineColumn`, `combineEvals`, `chunkRows`: the recombination on values, and a column's
  batch rows.

## Main results

* `hornerChunks_spec`, `collapseEvals_spec`, `publicFold_spec`, `zetaToSrsOr_spec`: each gadget
  reads as the value-side recombination.
* `combineEvals_one`: at one chunk the recombination is each column's single chunk.
-/

namespace Pickles

open Std.Do Snarky Kimchi.Verifier

variable {F c : Type} [Field F] [DecidableEq F] [BasicSystem F c]

/-! ## The circuit -/

/-- The evaluations of a proof at `nc` chunks per column: `ft(ζω)`, the public chunks and the
proof's evaluation chunks at `ζ` and `ζω`. -/
structure ChunkedEvals (nc : ℕ) (f : Type) where
  /-- `ft(ζω)`. -/
  ftEval1 : f
  /-- The public-input polynomial's chunks at `ζ` and `ζω`. -/
  pub : PointEvaluations (Vector f nc)
  /-- The proof's evaluation chunks. -/
  evals : ProofEvaluations (Vector f nc)

/-- `∑ᵢ chunks[i] · ptⁱ`, by Horner from the last chunk down: one multiplication per chunk
past the first, the innermost first. -/
def hornerChunks (pt : FVar F) : List (FVar F) → CircuitM F c (FVar F)
  | [] => pure (.const 0)
  | [x] => pure x
  | x :: y :: rest => do
    let acc ← hornerChunks pt (y :: rest)
    let t ← mul pt acc
    pure (CVar.add_ x t)

/-- One column's chunks recombined at `ζ^(2^k)` and `(ζω)^(2^k)`, the `ζω` fold first. -/
def collapseColumn {nc : ℕ} (zetaPow zetaOmegaPow : FVar F)
    (e : PointEvaluations (Vector (FVar F) nc)) : CircuitM F c (PointEvaluations (FVar F)) := do
  let zetaOmega ← hornerChunks zetaOmegaPow e.zetaOmega.toList
  let zeta ← hornerChunks zetaPow e.zeta.toList
  pure ⟨zeta, zetaOmega⟩

/-- A vector's columns recombined from the last to the first. -/
private def collapseColumnsRev {nc m : ℕ} (zetaPow zetaOmegaPow : FVar F)
    (v : Vector (PointEvaluations (Vector (FVar F) nc)) m) :
    CircuitM F c (Vector (PointEvaluations (FVar F)) m) := do
  let r ← v.reverse.mapM (collapseColumn zetaPow zetaOmegaPow)
  pure r.reverse

/-- Every column of a chunked batch recombined, in a fixed emission order: the selectors, `σ`,
`z`, the coefficients, the witness columns, each vector from its last column to its first. -/
def collapseEvals {nc : ℕ} (zetaPow zetaOmegaPow : FVar F)
    (e : ProofEvaluations (Vector (FVar F) nc)) : CircuitM F c (ProofEvaluations (FVar F)) := do
  let endomulScalarSelector ← collapseColumn zetaPow zetaOmegaPow e.endomulScalarSelector
  let emulSelector ← collapseColumn zetaPow zetaOmegaPow e.emulSelector
  let mulSelector ← collapseColumn zetaPow zetaOmegaPow e.mulSelector
  let completeAddSelector ← collapseColumn zetaPow zetaOmegaPow e.completeAddSelector
  let poseidonSelector ← collapseColumn zetaPow zetaOmegaPow e.poseidonSelector
  let genericSelector ← collapseColumn zetaPow zetaOmegaPow e.genericSelector
  let s ← collapseColumnsRev zetaPow zetaOmegaPow e.s
  let z ← collapseColumn zetaPow zetaOmegaPow e.z
  let coefficients ← collapseColumnsRev zetaPow zetaOmegaPow e.coefficients
  let w ← collapseColumnsRev zetaPow zetaOmegaPow e.w
  pure ⟨w, z, s, coefficients, genericSelector, poseidonSelector, completeAddSelector,
    mulSelector, emulSelector, endomulScalarSelector⟩

/-- The public evaluation at `ζ`: the one chunk as it is, or the chunks folded at `ζ^(2^srs)`,
with that power returned beside the fold for `zetaToSrsOr` to reuse. -/
def publicFold (srsLengthLog2 : ℕ) (zeta : FVar F) :
    List (FVar F) → CircuitM F c (FVar F × Option (FVar F))
  | [x] => pure (x, none)
  | chunks => do
    let zetaToSrs ← Snarky.pow zeta (2 ^ srsLengthLog2)
    let folded ← hornerChunks zetaToSrs chunks
    pure (folded, some zetaToSrs)

/-- `ζ^(2^srs)`: the public fold's, when it computed one, and otherwise computed here. -/
def zetaToSrsOr (srsLengthLog2 : ℕ) (zeta : FVar F) : Option (FVar F) → CircuitM F c (FVar F)
  | some z => pure z
  | none => Snarky.pow zeta (2 ^ srsLengthLog2)

/-! ## The values -/

/-- A column's chunks recombined at `xζ` and `xζω`: `combineAt` of each point's chunks. -/
def combineColumn {nc : ℕ} (xζ xζω : F) (e : PointEvaluations (Vector F nc)) :
    PointEvaluations F :=
  ⟨combineAt xζ e.zeta.toArray, combineAt xζω e.zetaOmega.toArray⟩

/-- Every column of a chunked batch recombined at `xζ` and `xζω`: `KimchiProof.linEvals`'s
per-column combination. -/
def combineEvals {nc : ℕ} (xζ xζω : F) (e : ProofEvaluations (Vector F nc)) :
    ProofEvaluations F where
  w := e.w.map (combineColumn xζ xζω)
  z := combineColumn xζ xζω e.z
  s := e.s.map (combineColumn xζ xζω)
  coefficients := e.coefficients.map (combineColumn xζ xζω)
  genericSelector := combineColumn xζ xζω e.genericSelector
  poseidonSelector := combineColumn xζ xζω e.poseidonSelector
  completeAddSelector := combineColumn xζ xζω e.completeAddSelector
  mulSelector := combineColumn xζ xζω e.mulSelector
  emulSelector := combineColumn xζ xζω e.emulSelector
  endomulScalarSelector := combineColumn xζ xζω e.endomulScalarSelector

/-- A column's rows of the batch: one `(ζ, ζω)` row per chunk. -/
def chunkRows {α : Type} {nc : ℕ} (e : PointEvaluations (Vector α nc)) :
    List (PointEvaluations α) :=
  (Vector.zipWith (fun a b => ⟨a, b⟩) e.zeta e.zetaOmega).toList

/-! ## Soundness -/

omit [DecidableEq F] [BasicSystem F c] in
/-- `combineAt` is Horner from the last chunk down. -/
theorem combineAt_eq_foldr (x : F) (l : List F) :
    combineAt x l.toArray = l.foldr (fun a acc => a + x * acc) 0 := by
  have key : ∀ (l : List F) (s p : F),
      (l.foldl (fun (acc : F × F) a => (acc.1 + acc.2 * a, acc.2 * x)) (s, p)).1
        = s + p * l.foldr (fun a acc => a + x * acc) 0 := by
    intro l
    induction l with
    | nil => intro s p; simp
    | cons a l ih =>
      intro s p
      simp only [List.foldl_cons, List.foldr_cons]
      rw [ih]
      ring
  simp only [combineAt, List.foldl_toArray']
  rw [key]
  ring

omit [DecidableEq F] [BasicSystem F c] in
/-- One chunk recombines to itself. -/
theorem combineAt_single (x a : F) : combineAt x #[a] = a := by
  simpa using combineAt_eq_foldr x [a]

/-- `hornerChunks` reads as the chunks' `combineAt` at the point's reading. -/
theorem hornerChunks_spec {V : Valuation F} [ConstraintHolds F c] [LawfulBasicSystem F c]
    (pt : FVar F) :
    ∀ chunks : List (FVar F), ⦃⌜True⌝⦄ hornerChunks (c := Builder V c) pt chunks
      ⦃⇓ r _ => ⌜r.val V = combineAt (pt.val V) (chunks.map (·.val V)).toArray⌝⦄ := by
  intro chunks
  induction chunks with
  | nil =>
    simp only [hornerChunks]
    mvcgen
  | cons x rest ih =>
    cases rest with
    | nil =>
      simp only [hornerChunks]
      mvcgen
      all_goals simp [combineAt_single]
    | cons y rest =>
      simp only [hornerChunks]
      mvcgen [ih]
      rename_i acc _ hacc t _ ht
      rw [combineAt_eq_foldr] at hacc
      rw [combineAt_eq_foldr, List.map_cons, List.foldr_cons, ← hacc, ← ht]
      simp

/-- A column's recombination reads as `combineColumn` of its chunks' readings. -/
theorem collapseColumn_spec {V : Valuation F} [ConstraintHolds F c] [LawfulBasicSystem F c]
    {nc : ℕ} (zetaPow zetaOmegaPow : FVar F) (e : PointEvaluations (Vector (FVar F) nc)) :
    ⦃⌜True⌝⦄ collapseColumn (c := Builder V c) zetaPow zetaOmegaPow e
    ⦃⇓ r _ => ⌜r.map (·.val V) = combineColumn (zetaPow.val V) (zetaOmegaPow.val V)
      (e.map fun v => v.map (·.val V))⌝⦄ := by
  simp only [collapseColumn]
  have hz := hornerChunks_spec (V := V) (c := c) zetaPow e.zeta.toList
  have hzo := hornerChunks_spec (V := V) (c := c) zetaOmegaPow e.zetaOmega.toList
  mvcgen [hz, hzo]
  rename_i a _ ha b _ hb
  simp [combineColumn, PointEvaluations.map, ha, hb, Vector.toList, ← Array.toList_map]

omit [Field F] [DecidableEq F] [BasicSystem F c] in
/-- `Vector.mapM` of specified steps: the results read, entrywise, as the targets. -/
private theorem builder_spec_vector_mapM {V : Valuation F} [ConstraintHolds F c]
    {α β γ : Type} {m : ℕ} (f : α → CircuitM F (Builder V c) β) (g : β → γ) (Q : α → γ)
    (hf : ∀ a, ⦃⌜True⌝⦄ f a ⦃⇓ r _ => ⌜g r = Q a⌝⦄) (v : Vector α m) :
    ⦃⌜True⌝⦄ v.mapM f ⦃⇓ rs _ => ⌜rs.map g = v.map Q⌝⦄ := by
  have hl := builder_spec_mapM f (fun r q => g r = q) Q hf v.toList
  have heq : (fun rs : Vector β m => rs.toList) <$> v.mapM f = v.toList.mapM f := by
    rw [← Vector.toList_toArray, ← Array.toList_mapM, ← Vector.toArray_mapM, ← comp_map]
    rfl
  rw [← heq] at hl
  refine builder_spec_imp _ _ _ (builder_spec_of_map _ _ _ hl) fun rs h => ?_
  apply Vector.toList_inj.mp
  rw [Vector.toList_map, Vector.toList_map]
  exact (List.forall₂_iff_get.mp (List.forall₂_map_left_iff.mpr (h.imp fun _ _ e => e))).elim
    (fun _ _ => by
      apply List.ext_getElem (by simp)
      intro i h₁ h₂
      simpa using (List.forall₂_iff_get.mp h).2 i (by simpa using h₁) (by simpa using h₂))

/-- A vector's columns recombined, last to first, read as each column's `combineColumn`. -/
private theorem collapseColumnsRev_spec {V : Valuation F} [ConstraintHolds F c]
    [LawfulBasicSystem F c] {nc m : ℕ} (zetaPow zetaOmegaPow : FVar F)
    (v : Vector (PointEvaluations (Vector (FVar F) nc)) m) :
    ⦃⌜True⌝⦄ collapseColumnsRev (c := Builder V c) zetaPow zetaOmegaPow v
    ⦃⇓ r _ => ⌜r.map (PointEvaluations.map (·.val V))
      = v.map fun e => combineColumn (zetaPow.val V) (zetaOmegaPow.val V)
          (e.map fun v => v.map (·.val V))⌝⦄ := by
  simp only [collapseColumnsRev]
  have hm := builder_spec_vector_mapM (collapseColumn (c := Builder V c) zetaPow zetaOmegaPow)
    (PointEvaluations.map (·.val V))
    (fun e => combineColumn (zetaPow.val V) (zetaOmegaPow.val V)
      (e.map fun v => v.map (·.val V)))
    (fun e => collapseColumn_spec zetaPow zetaOmegaPow e) v.reverse
  mvcgen [hm]
  rename_i r _ hr
  rw [Vector.map_reverse, hr, Vector.map_reverse, Vector.reverse_reverse]

/-- A chunked batch's recombination reads as `combineEvals` of its chunks' readings. -/
theorem collapseEvals_spec {V : Valuation F} [ConstraintHolds F c] [LawfulBasicSystem F c]
    {nc : ℕ} (zetaPow zetaOmegaPow : FVar F) (e : ProofEvaluations (Vector (FVar F) nc)) :
    ⦃⌜True⌝⦄ collapseEvals (c := Builder V c) zetaPow zetaOmegaPow e
    ⦃⇓ r _ => ⌜r.map (·.val V) = combineEvals (zetaPow.val V) (zetaOmegaPow.val V)
      (e.map fun v => v.map (·.val V))⌝⦄ := by
  simp only [collapseEvals]
  have hc := fun (col : PointEvaluations (Vector (FVar F) nc)) =>
    collapseColumn_spec (V := V) (c := c) zetaPow zetaOmegaPow col
  have hv := fun {m : ℕ} (v : Vector (PointEvaluations (Vector (FVar F) nc)) m) =>
    collapseColumnsRev_spec (V := V) (c := c) zetaPow zetaOmegaPow v
  mvcgen [hc, hv]
  rename_i es _ hes em _ hem mu _ hmu ca _ hca po _ hpo ge _ hge s _ hs z _ hz co _ hco w _ hw
  simp only [ProofEvaluations.map, combineEvals] at *
  rw [hw, hz, hs, hco, hge, hpo, hca, hmu, hem, hes]
  simp [Vector.map_map, Function.comp_def]

/-- The public fold reads as the public chunks' `combineAt` at `ζ^(2^srs)`, and the power it
returns, if any, reads as `ζ^(2^srs)`. -/
theorem publicFold_spec {V : Valuation F} [ConstraintHolds F c] [LawfulBasicSystem F c]
    (srsLengthLog2 : ℕ) (zeta : FVar F) (chunks : List (FVar F)) :
    ⦃⌜True⌝⦄ publicFold (c := Builder V c) srsLengthLog2 zeta chunks
    ⦃⇓ r _ => ⌜r.1.val V = combineAt (zeta.val V ^ 2 ^ srsLengthLog2)
        (chunks.map (·.val V)).toArray ∧
      ∀ z ∈ r.2, z.val V = zeta.val V ^ 2 ^ srsLengthLog2⌝⦄ := by
  match chunks with
  | [x] =>
    simp only [publicFold]
    mvcgen
    simp [combineAt_single]
  | [] =>
    simp only [publicFold]
    have hh := hornerChunks_spec (V := V) (c := c)
    mvcgen [hh]
    rename_i t _ ht a _ ha
    exact ⟨by rw [ha, ht], fun z hz => by simp at hz; rw [← hz, ht]⟩
  | x :: y :: rest =>
    simp only [publicFold]
    have hh := hornerChunks_spec (V := V) (c := c)
    mvcgen [hh]
    rename_i t _ ht a _ ha
    exact ⟨by rw [ha, ht], fun z hz => by simp at hz; rw [← hz, ht]⟩

/-- `zetaToSrsOr` reads as `ζ^(2^srs)` once the power it may be handed does. -/
theorem zetaToSrsOr_spec {V : Valuation F} [ConstraintHolds F c] [LawfulBasicSystem F c]
    (srsLengthLog2 : ℕ) (zeta : FVar F) (o : Option (FVar F))
    (ho : ∀ z ∈ o, z.val V = zeta.val V ^ 2 ^ srsLengthLog2) :
    ⦃⌜True⌝⦄ zetaToSrsOr (c := Builder V c) srsLengthLog2 zeta o
    ⦃⇓ r _ => ⌜r.val V = zeta.val V ^ 2 ^ srsLengthLog2⌝⦄ := by
  match o with
  | some z =>
    simp only [zetaToSrsOr]
    mvcgen
    exact ho z rfl
  | none =>
    simp only [zetaToSrsOr]
    mvcgen

omit [DecidableEq F] [BasicSystem F c] in
/-- At one chunk the recombination is each column's single chunk, whatever the points. -/
theorem combineEvals_one (x y : F) (e : ProofEvaluations (Vector F 1)) :
    combineEvals x y e = e.map (·.toList.headD 0) := by
  have hcol : ∀ col : PointEvaluations (Vector F 1),
      combineColumn x y col = col.map (·.toList.headD 0) := by
    intro col
    obtain ⟨⟨za, hza⟩, ⟨zb, hzb⟩⟩ := col
    obtain ⟨la⟩ := za
    obtain ⟨lb⟩ := zb
    match la, lb, hza, hzb with
    | [a], [b], _, _ => simp [combineColumn, combineAt_single, PointEvaluations.map]
  have hf : combineColumn x y = PointEvaluations.map (·.toList.headD 0) := funext hcol
  simp only [combineEvals, hf]
  rfl

end Pickles
