import Bulletproof.Forking.Schnorr
import Zcash.Snark.Soundness.Forking.Extractor
import Zcash.Snark.Soundness.AGM.Peel

/-!
# The kimchi fork certificate, and opening-or-break

What replaced the conclusion of the former Fiat–Shamir axioms, on ironwood's strategy: from an
explicit certificate of forked kimchi wire acceptances, *compute* either an opening witness for
`openingRelationB` or a nontrivial relation over the augmented basis `(g, U, H)` — the
discrete-log break. No `hbind` hypothesis: where the old statements assumed binding, this one
returns the violation as data.

## The certificate

`KimchiForkCert` records a `(3,…,3)` fork of the kimchi wire verifier: at each node the round
cross-commitments `L`, `R` (fixed before the round challenge, shared by the three branches) and
three distinct nonzero challenges; at each leaf the branch's folded generator `sg`, Schnorr
commitment `δ`, and **two** accepting Schnorr transcripts `(c, z1, z2)`, `(c', z1', z2')` — the
2-fork on the Schnorr challenge that `schnorr_fork_eq` consumes. Plain data: following
`produceDeployed`, the deployed tree's decorations are recovered by Vandermonde interpolation of
the sibling recursions, so no per-node AGM representations are required. The single AGM input is
the root representation `P = ⟨pg, g⟩ + pw • H` (kimchi commitments are Pedersen: a `g`-vector
plus a blinding component; `U` is transcript-derived *after* the commitment, so an algebraic
prover has no `U` slot to use).

`KimchiForkValid` states acceptance in kimchi's fold convention (`foldHalves`, commitment update
`P + u⁻¹•L + u•R`, the claimed value `v` riding once on `U` in the seed `Q = P + v•U`): the leaf
holds the two wire Schnorr equations at the branch's fully-folded data. The connection from the
executable verifier's per-branch `b0`/`sg` (`bPolyCoefficients`) to these folded forms is the
s-vector bridge, kept separate.

## The pipeline

Everything below the surface is ironwood's, reached through the fold-convention transport of
`Forking/Convention.lean` (invert challenges, swap `L`/`R`):

1. `toDFork` — the certificate becomes a `Zcash.Snark.DForkCert`, its leaves the Schnorr
   difference quotients;
2. `KimchiForkValid.toDFork` — wire validity becomes `DeployedForkValid` at `Pwhole = P + v•U`,
   `z = 1`, `W = H`, via `schnorr_fork_eq`;
3. `Zcash.Snark.deployed_forking_tree` — accepting deployed tree, or a computed relation;
4. `Zcash.Snark.deployedToAcceptVWitnessCore` — clean tree, or a computed relation;
5. `Zcash.Snark.ipa_extractV` — the opening witness, as data; de-blinded by `ρ := pw`.
-/

namespace Bulletproof.Forking

open Bulletproof

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A `(3,…,3)` fork certificate for the kimchi wire verifier. Node: the round
cross-commitments and three challenges. Leaf: the branch's folded generator `sg`, the Schnorr
commitment `δ`, and two Schnorr transcripts `(c, z1, z2)`, `(c', z1', z2')`. -/
inductive KimchiForkCert (F G : Type*) : ℕ → Type _ where
  /-- Leaf data: `sg`, `δ`, then the two Schnorr transcripts. -/
  | leaf : G → G → F → F → F → F → F → F → KimchiForkCert F G 0
  /-- Node data: `L`, `R`, three round challenges, three sub-certificates. -/
  | node {d : ℕ} : G → G → F → F → F → KimchiForkCert F G d → KimchiForkCert F G d →
      KimchiForkCert F G d → KimchiForkCert F G (d + 1)

/-- Validity of a kimchi fork certificate, in kimchi's fold convention. The recursion folds the
generators and eval vector by `foldHalves` and updates the commitment by `u⁻¹•L + u•R`; the
claimed value `v` rides on `U` once, in the Schnorr equations' `Q = P + v•U`. At a leaf, `sg` is
pinned to the branch's folded generator and both Schnorr transcripts accept at distinct
challenges. -/
def KimchiForkValid (U H : G) (v : F) : {d : ℕ} → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) →
    G → KimchiForkCert F G d → Prop
  | 0, g, b, P, .leaf sg δ c z1 z2 c' z1' z2' =>
      c ≠ c' ∧ sg = g 0 ∧
        (c • (P + v • U) + δ = z1 • sg + (z1 * b 0) • U + z2 • H) ∧
        (c' • (P + v • U) + δ = z1' • sg + (z1' * b 0) • U + z2' • H)
  | _ + 1, g, b, P, .node L R u₁ u₂ u₃ t₁ t₂ t₃ =>
      u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
        KimchiForkValid U H v (foldHalves g u₁) (foldHalves b u₁) (P + u₁⁻¹ • L + u₁ • R) t₁ ∧
        KimchiForkValid U H v (foldHalves g u₂) (foldHalves b u₂) (P + u₂⁻¹ • L + u₂ • R) t₂ ∧
        KimchiForkValid U H v (foldHalves g u₃) (foldHalves b u₃) (P + u₃⁻¹ • L + u₃ • R) t₃

/-- Transport into ironwood's certificate: swap `L`/`R`, invert the challenges (the
fold-convention transport of `Forking/Convention.lean`), and Schnorr-extract each leaf into its
difference quotients. -/
def KimchiForkCert.toDFork : {d : ℕ} → KimchiForkCert F G d → Zcash.Snark.DForkCert F G d
  | 0, .leaf _ _ c z1 z2 c' z1' z2' =>
      .leaf ((z1 - z1') / (c - c')) ((z2 - z2') / (c - c'))
  | _ + 1, .node L R u₁ u₂ u₃ t₁ t₂ t₃ =>
      .node R L u₁⁻¹ u₂⁻¹ u₃⁻¹ t₁.toDFork t₂.toDFork t₃.toDFork

/-- `commitGen` over the singleton index family. -/
private theorem commitGen_singleton {M : Type*} [AddCommGroup M] [Module F M]
    (g : Fin (2 ^ 0) → M) (x : F) : commitGen g (fun _ => x) = x • g 0 :=
  Fin.sum_univ_one fun i => x • g i

/-- **Validity transports.** A valid kimchi fork certificate is a valid ironwood deployed fork
certificate for the whole point `Q = P + v•U`, at binding challenge `z = 1` and blinding base
`W = H`. The leaf case is `schnorr_fork_eq`; the node case is the fold-convention transport. -/
theorem KimchiForkValid.toDFork {U H : G} {v : F} : {d : ℕ} → (g : Fin (2 ^ d) → G) →
    (b : Fin (2 ^ d) → F) → (P : G) → (t : KimchiForkCert F G d) →
    KimchiForkValid U H v g b P t →
    Zcash.Snark.DeployedForkValid g b U H 1 (P + v • U) t.toDFork
  | 0, g, b, P, .leaf sg δ c z1 z2 c' z1' z2', hval => by
      obtain ⟨hne, hsg, h, h'⟩ := hval
      show P + v • U = commitGen g _ + ((1 : F) * commitGen b _) • U + _ • H
      rw [commitGen_singleton, commitGen_singleton, one_mul, smul_eq_mul, ← hsg]
      exact schnorr_fork_eq U H (P + v • U) δ sg (b 0) hne h h'
  | _ + 1, g, b, P, .node L R u₁ u₂ u₃ t₁ t₂ t₃, hval => by
      obtain ⟨h12, h13, h23, hu₁, hu₂, hu₃, hv₁, hv₂, hv₃⟩ := hval
      refine ⟨fun hc => h12 (inv_injective hc), fun hc => h13 (inv_injective hc),
        fun hc => h23 (inv_injective hc),
        inv_ne_zero hu₁, inv_ne_zero hu₂, inv_ne_zero hu₃, ?_, ?_, ?_⟩
      · have := KimchiForkValid.toDFork _ _ _ t₁ hv₁
        rw [foldGens_inv, foldGens_inv, inv_inv,
          show P + v • U + u₁ • R + u₁⁻¹ • L = P + u₁⁻¹ • L + u₁ • R + v • U from by abel]
        exact this
      · have := KimchiForkValid.toDFork _ _ _ t₂ hv₂
        rw [foldGens_inv, foldGens_inv, inv_inv,
          show P + v • U + u₂ • R + u₂⁻¹ • L = P + u₂⁻¹ • L + u₂ • R + v • U from by abel]
        exact this
      · have := KimchiForkValid.toDFork _ _ _ t₃ hv₃
        rw [foldGens_inv, foldGens_inv, inv_inv,
          show P + v • U + u₃ • R + u₃⁻¹ • L = P + u₃⁻¹ • L + u₃ • R + v • U from by abel]
        exact this

/-- **The capstone: opening or break, as computed data.** From a valid kimchi fork certificate
and the algebraic prover's representation of the commitment (`P = ⟨pg, g⟩ + pw•H` — no `U`
component, since `U` is derived after `P` is sent), compute either

* an opening witness for our own blinded relation `openingRelationB σ P b v a ρ`, or
* a nontrivial relation over the augmented basis `(σ.g, σ.U, σ.h)` — the discrete-log break.

Everything below the two validity rewrites is ironwood's machinery; no extraction is reproved.
Unlike the conclusion of the former Fiat–Shamir axioms, neither branch here can be conjured:
the opening is data extracted from the certificate, and the break is explicit coefficients. -/
def kimchiOpeningOrBreak [DecidableEq F] [DecidableEq G] (σ : SRS G)
    (b : Fin (2 ^ σ.k) → F) (v : F) (P : G)
    (pg : Fin (2 ^ σ.k) → F) (pw : F) (hP : P = commitGen σ.g pg + pw • σ.h)
    (cert : KimchiForkCert F G σ.k)
    (hv : KimchiForkValid σ.U σ.h v σ.g b P cert) :
    (Σ' (a : Fin (2 ^ σ.k) → F) (ρ : F), openingRelationB σ P b v a ρ)
      ⊕' Zcash.Snark.AlgebraicRelationWitness (F := F)
          (Zcash.Snark.augmentedBasis σ.g σ.U σ.h) :=
  have hvd : Zcash.Snark.DeployedForkValid σ.g b σ.U σ.h 1
      (commitGen σ.g pg + ((1 : F) * v) • σ.U + pw • σ.h) cert.toDFork := by
    have h := KimchiForkValid.toDFork σ.g b P cert hv
    rw [hP] at h
    rw [one_mul, show commitGen σ.g pg + v • σ.U + pw • σ.h
          = commitGen σ.g pg + pw • σ.h + v • σ.U from by abel]
    exact h
  match Zcash.Snark.deployed_forking_tree one_ne_zero σ.g b pg v pw cert.toDFork hvd with
  | .inr rel => .inr (Zcash.Snark.AugmentedRelationWitness.toAlgebraicRelationWitness rel)
  | .inl ⟨_, t, hacc⟩ =>
    match Zcash.Snark.deployedToAcceptVWitnessCore one_ne_zero σ.g b _ _ _ t hacc with
    | .inr rel => .inr rel.toAlgebraicRelationWitness
    | .inl hclean =>
      match Zcash.Snark.ipa_extractV σ.g b _ _ (Zcash.Snark.projTree t) hclean with
      | ⟨a, hPa, hva⟩ =>
        .inl ⟨a, pw, by
          show commit σ a pw = P
          rw [show commit σ a pw = commitGen σ.g a + pw • σ.h from rfl, hP]
          exact congrArg (· + pw • σ.h) hPa, by
          show v = innerProduct a b
          rw [← hva]
          simp [Zcash.Snark.commitGen, innerProduct, smul_eq_mul]⟩

end Bulletproof.Forking
