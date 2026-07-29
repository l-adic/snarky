import Bulletproof.Forking.Capstone
import Bulletproof.Forking.SVector
import Zcash.Snark.Soundness.Forking.Tree

/-!
# The kimchi prover strategy

The **prefix-determined prover strategy** that the `KimchiForkCert` of
`Bulletproof/Forking/Capstone.lean` is built over. It mirrors ironwood's `Prover`
(`Forking/Extractor.lean`), with kimchi's two twists:

* the Schnorr layer adds **one more challenge round**: at depth `d` the challenge vector is
  `Fin (d + 1) → F` — `d` round challenges, then the Schnorr challenge. A fork splits the final
  round three ways like any other; the certificate keeps two of the three transcripts, which is
  all `schnorr_fork_eq` needs;
* the prover's leaf commits to `sg` and `δ` **before** the Schnorr challenge and answers with
  the responses `(z1, z2)` as a function of it — the commit-then-challenge ordering that makes
  a fork meaningful.

`kimchiProverAccept` is stated in the folded form (`KimchiForkValid`'s shape). Its faithfulness
to the wire verifier's flat equations (`VerifierAcceptsAt`, with `sg`/`b0` through
`bPolyCoefficients`) is the s-vector bridge, closed here by
`kimchiProverAccept_iff_verifierAcceptsAt`.
-/

namespace Bulletproof.Forking

open Bulletproof

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## The prover strategy -/

/-- A prefix-determined kimchi prover strategy. At each round it commits to the cross-terms
`(L, R)` and continues as a function of the round challenge; at the leaf it commits to the
folded generator claim `sg` and the Schnorr commitment `δ`, then answers the Schnorr challenge
with the responses `(z1, z2)`. -/
inductive KimchiProver (F G : Type*) : ℕ → Type _ where
  /-- Leaf: `sg`, `δ`, and the Schnorr responses as a function of the Schnorr challenge. -/
  | leaf : G → G → (F → F × F) → KimchiProver F G 0
  /-- Node: the round cross-terms, then the continuation on the round challenge. -/
  | node {d : ℕ} : G → G → (F → KimchiProver F G d) → KimchiProver F G (d + 1)

/-- Acceptance of a prover strategy along one challenge vector (`d` round challenges, then the
Schnorr challenge), in the folded form: fold generators, eval vector and commitment as
`KimchiForkValid` does; at the leaf check `sg` against the folded generator and the wire Schnorr
equation at `Q = P + v•U`. -/
def kimchiProverAccept : {d : ℕ} → KimchiProver F G d → (Fin (2 ^ d) → G) →
    (Fin (2 ^ d) → F) → G → G → F → G → (Fin (d + 1) → F) → Prop
  | 0, .leaf sg δ resp, g, b, U, H, v, P, χ =>
      sg = g 0 ∧
        (χ 0) • (P + v • U) + δ
          = (resp (χ 0)).1 • sg + ((resp (χ 0)).1 * b 0) • U + (resp (χ 0)).2 • H
  | _ + 1, .node L R cont, g, b, U, H, v, P, χ =>
      kimchiProverAccept (cont (χ 0)) (foldHalves g (χ 0)) (foldHalves b (χ 0)) U H v
        (P + (χ 0)⁻¹ • L + (χ 0) • R) (Fin.tail χ)

/-! ## Faithfulness: the folded acceptance is the wire verifier's

`kimchiProverAccept` is stated in the folded form. To keep it honest it must be *proved* equal
to the wire verifier's flat acceptance — `VerifierAcceptsAt` at the proof the strategy assembles
along the branch — not merely asserted to model it. -/

/-- The cross-terms the strategy emits along a branch. -/
def KimchiProver.lrAt : {d : ℕ} → KimchiProver F G d → (Fin (d + 1) → F) → Fin d → G × G
  | 0, _, _ => fun i => i.elim0
  | _ + 1, .node L R cont, χ => Fin.cons (L, R) (KimchiProver.lrAt (cont (χ 0)) (Fin.tail χ))

/-- The leaf data the strategy emits along a branch: `(sg, δ, z1, z2)`. -/
def KimchiProver.leafAt : {d : ℕ} → KimchiProver F G d → (Fin (d + 1) → F) → G × G × F × F
  | 0, .leaf sg δ resp, χ => (sg, δ, (resp (χ 0)).1, (resp (χ 0)).2)
  | _ + 1, .node _ _ cont, χ => KimchiProver.leafAt (cont (χ 0)) (Fin.tail χ)

/-- The wire opening proof the strategy assembles along a branch. -/
def KimchiProver.proofAt {d : ℕ} (pr : KimchiProver F G d) (χ : Fin (d + 1) → F) :
    OpeningProof F G d :=
  { lr := pr.lrAt χ
    delta := (pr.leafAt χ).2.1
    z1 := (pr.leafAt χ).2.2.1
    z2 := (pr.leafAt χ).2.2.2
    sg := (pr.leafAt χ).1 }

/-- `Fin.tail` commutes with `Fin.snoc` when the head survives. (Families pinned to the
constant one — the dependent `snoc`/`tail` do not elaborate against each other bare.) -/
private theorem tail_snoc {n : ℕ} {α : Sort*} (u : Fin (n + 1) → α) (c : α) :
    Fin.tail (α := fun _ => α) (Fin.snoc (α := fun _ => α) u c)
      = Fin.snoc (α := fun _ => α) (Fin.tail (α := fun _ => α) u) c := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.tail, Fin.succ_last, Fin.snoc_last]
  · simp only [Fin.tail, Fin.succ_castSucc, Fin.snoc_castSucc]

/-- The generic flat/folded correspondence, over arbitrary generators: acceptance along
`Fin.snoc u c` is the wire's two checks — the Schnorr equation over the *flat* recombination sum
and `sg` pinned to the *flat* s-vector commitment. The fold happens on the left, the s-vector
bridge (`commitGen_bPolyCoefficients_step`) on the right, and they meet in the middle. -/
private theorem kimchiProverAccept_snoc
    : {d : ℕ} → (pr : KimchiProver F G d) → (g : Fin (2 ^ d) → G) →
    (b : Fin (2 ^ d) → F) → (U H : G) → (v : F) → (P : G) → (u : Fin d → F) → (c : F) →
    (kimchiProverAccept pr g b U H v P (Fin.snoc u c) ↔
      ((pr.leafAt (Fin.snoc u c)).1 = commitGen g (bPolyCoefficients u) ∧
        c • (P + v • U + ∑ j, ((u j)⁻¹ • (pr.lrAt (Fin.snoc u c) j).1
              + (u j) • (pr.lrAt (Fin.snoc u c) j).2))
            + (pr.leafAt (Fin.snoc u c)).2.1
          = (pr.leafAt (Fin.snoc u c)).2.2.1 • (pr.leafAt (Fin.snoc u c)).1
            + ((pr.leafAt (Fin.snoc u c)).2.2.1 * commitGen b (bPolyCoefficients u)) • U
            + (pr.leafAt (Fin.snoc u c)).2.2.2 • H))
  | 0, .leaf sg δ resp, g, b, U, H, v, P, u, c => by
      have hz : (Fin.snoc u c : Fin 1 → F) 0 = c := by
        rw [show (0 : Fin 1) = Fin.last 0 from rfl, Fin.snoc_last]
      rw [kimchiProverAccept, KimchiProver.leafAt, hz]
      rw [show (∑ j : Fin 0, ((u j)⁻¹ • (KimchiProver.lrAt (.leaf sg δ resp) (Fin.snoc u c) j).1
            + (u j) • (KimchiProver.lrAt (.leaf sg δ resp) (Fin.snoc u c) j).2)) = 0 from
          Finset.sum_of_isEmpty _,
        add_zero, commitGen_bPolyCoefficients_zero,
        show commitGen b (bPolyCoefficients u) = b 0 from commitGen_bPolyCoefficients_zero u b]
  | d + 1, .node L R cont, g, b, U, H, v, P, u, c => by
      have h0 : (Fin.snoc u c : Fin (d + 2) → F) 0 = u 0 := by
        rw [show (0 : Fin (d + 2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
      have ht := tail_snoc u c
      rw [kimchiProverAccept, h0, ht,
        kimchiProverAccept_snoc (cont (u 0)) _ _ U H v _ (Fin.tail u) c,
        KimchiProver.leafAt, KimchiProver.lrAt, h0, ht,
        commitGen_bPolyCoefficients_step u g, commitGen_bPolyCoefficients_step u b,
        Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [show (∑ i : Fin d, ((u i.succ)⁻¹
            • (KimchiProver.lrAt (cont (u 0)) (Fin.snoc (Fin.tail u) c) i).1
          + (u i.succ)
            • (KimchiProver.lrAt (cont (u 0)) (Fin.snoc (Fin.tail u) c) i).2))
        = ∑ j : Fin d, (((Fin.tail u) j)⁻¹
            • (KimchiProver.lrAt (cont (u 0)) (Fin.snoc (Fin.tail u) c) j).1
          + ((Fin.tail u) j)
            • (KimchiProver.lrAt (cont (u 0)) (Fin.snoc (Fin.tail u) c) j).2) from
        Finset.sum_congr rfl fun i _ => rfl]
      rw [show P + v • U + ((u 0)⁻¹ • ((L, R) : G × G).1 + (u 0) • ((L, R) : G × G).2
            + ∑ j : Fin d, (((Fin.tail u) j)⁻¹
                • (KimchiProver.lrAt (cont (u 0)) (Fin.snoc (Fin.tail u) c) j).1
              + ((Fin.tail u) j)
                • (KimchiProver.lrAt (cont (u 0)) (Fin.snoc (Fin.tail u) c) j).2))
          = P + (u 0)⁻¹ • ((L, R) : G × G).1 + (u 0) • ((L, R) : G × G).2 + v • U
            + ∑ j : Fin d, (((Fin.tail u) j)⁻¹
                • (KimchiProver.lrAt (cont (u 0)) (Fin.snoc (Fin.tail u) c) j).1
              + ((Fin.tail u) j)
                • (KimchiProver.lrAt (cont (u 0)) (Fin.snoc (Fin.tail u) c) j).2) from by abel]

/-- **Faithfulness.** Along any branch, the folded prover acceptance *is* the wire verifier's
acceptance of the assembled proof: `VerifierAcceptsAt` at eval slot
`b0 = ⟨bPolyCoefficients u, b⟩` — for the batched claim, `combinedB u r x` by
`combinedB_eq_innerProduct`. So nothing about the strategy model is trusted: it is definitionally
the deployed equations. -/
theorem kimchiProverAccept_iff_verifierAcceptsAt (σ : SRS G) (pr : KimchiProver F G σ.k)
    (b : Fin (2 ^ σ.k) → F) (v : F) (P : G) (u : Fin σ.k → F) (c : F) :
    kimchiProverAccept pr σ.g b σ.U σ.h v P (Fin.snoc u c) ↔
      VerifierAcceptsAt σ (pr.proofAt (Fin.snoc u c)) P
        (innerProduct (bPolyCoefficients u) b) v c u := by
  rw [kimchiProverAccept_snoc, VerifierAcceptsAt, recombine,
    show innerProduct (bPolyCoefficients u) b = commitGen b (bPolyCoefficients u) from rfl]
  exact and_comm

end Bulletproof.Forking
