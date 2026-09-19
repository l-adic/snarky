import Pickles.TwoHalves

/-!
# The step circuit's scalar half, at an environment

`finalizeOtherProofStep` with its parameters fixed to the verifier key's
(`FopParams.ofEnv`) and the deployed `Fp` linearization, and the capstone that runs it: the
scalar-side counterpart of `wrapVerify_kimchiVerify_vesta`. The two halves of a step proof's
verification run in different circuits over different fields, so no one triple covers both;
each side gets a triple about its own circuit, with the other half assumed.
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open Kimchi.Protocol.Linearization Poseidon.FqSponge
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The step circuit's scalar half at an environment: `finalize_other_proof`'s step side with
the verifier key's parameters and the `Fp` token stream. -/
def finalizeOtherProofStepAt {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c] {k : ℕ}
    (E : Env IpaVesta.curve) (domains : List (KnownDomain Fp))
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) (w : AllEvals (FVar Fp))
    (mask : List (BoolVar Fp)) (prev : List (List (FVar Fp))) (domainLog2Var : FVar Fp) :
    CircuitM Fp c (FopOutput Fp) :=
  finalizeOtherProofStep (FopParams.ofEnv E Linearization.fpTokens) domains u w mask prev
    domainLog2Var

/-- A list of cells read, element by element, is the list of their values. -/
private theorem map_val_of_forall₂_reads {V : Valuation Fp} {cs : List (FVar Fp)} {cv : List Fp}
    (h : List.Forall₂ (CircuitType.Reads V) cs cv) : cs.map (fun x => CVar.val x V) = cv := by
  induction h with
  | nil => rfl
  | @cons x v xs vs hx _ ih =>
    simp only [List.map_cons, ih, List.cons.injEq, and_true]
    exact CircuitType.reads_fvar.mp hx

/-- Lists of cells read, element by element. -/
private theorem map_map_val_of_forall₂ {V : Valuation Fp} {css : List (List (FVar Fp))}
    {cvs : List (List Fp)} (h : List.Forall₂ (List.Forall₂ (CircuitType.Reads V)) css cvs) :
    css.map (fun cs => cs.map (fun x => CVar.val x V)) = cvs := by
  induction h with
  | nil => rfl
  | @cons cs cv css cvs hc _ ih =>
    simp only [List.map_cons, ih, List.cons.injEq, and_true]
    exact map_val_of_forall₂_reads hc

/-- The mask keeps the same elements whether it selects the challenge lists themselves or
singletons of them: the circuit absorbs the concatenation of the kept cells' values, the
`olds` tie states the kept lists. -/
private theorem flatten_zipWith_val {V : Valuation Fp} :
    ∀ (ms : List Bool) (css : List (List (FVar Fp))),
      (List.zipWith (fun m cs => if m = true then cs.map (fun x => CVar.val x V) else [])
          ms css).flatten
        = ((List.zipWith (fun m cv => if m = true then [cv] else []) ms
            (css.map (fun cs => cs.map (fun x => CVar.val x V)))).flatten).flatten
  | [], _ => rfl
  | _ :: _, [] => rfl
  | m :: ms, cs :: css => by cases m <;> simp [flatten_zipWith_val ms css]

/-- **Running the step circuit's scalar half, a step proof's remaining half decides
`kimchiVerify`.** `twoHalves_kimchiVerify_vesta` as a triple about the scalar circuit, with
the wrap circuit's group half assumed (`wrapVerify_kimchiVerify_vesta` produces it). -/
theorem finalizeOtherProofStepAt_kimchiVerify_vesta
    (E : Env IpaVesta.curve)
    (cp : KimchiProof IpaVesta.curve 1 E.σ.k)
    (pub : Array Fp)
    (hguard : Guards IpaVesta.curve E.cvk cp pub)
    -- the key's fr-sponge, endo coefficient and zk rows
    (hsize : IpaVesta.curve.frSponge.params.roundConstants.size = Poseidon.fullRounds)
    (hendo : E.cvk.endo = Pasta.pallasEndo)
    (h3zk : 3 ≤ E.cvk.zkRows)
    -- the step circuit: its valuation, its cells, the domains it may select from
    (Vs : Valuation Fp)
    (domains : List (KnownDomain Fp))
    (hnodup : (domains.map fun d => (d.log2 : Fp)).Nodup)
    (hdomains : ∀ d ∈ domains, E.cvk.zkRows ≤ 2 ^ d.log2 ∧ d.generator ^ 2 ^ d.log2 = 1)
    (claimsS : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (evals : AllEvals (FVar Fp))
    (maskCells : List (BoolVar Fp))
    (prevCells : List (List (FVar Fp)))
    (hprevlen : prevCells.flatten.length < 2 ^ 128)
    (domainLog2Var : FVar Fp)
    -- the cells behind the half's vectors
    (mask : Vector Bool MaxProofsVerified)
    (prevChallenges : Vector (Vector Fp E.σ.k) MaxProofsVerified)
    (hm : List.Forall₂ (CircuitType.Reads Vs) maskCells mask.toList)
    (hprev : List.Forall₂ (List.Forall₂ (CircuitType.Reads Vs)) prevCells
      (prevChallenges.toList.map Vector.toList))
    -- the domain the circuit selects is the key's
    (hsel : ∀ d₀ ∈ domains, domainLog2Var.val Vs = (d₀.log2 : Fp) →
      2 ^ d₀.log2 = E.cvk.n ∧ d₀.generator = E.cvk.omega)
    -- the wrap circuit's group half, and its asserted bit
    (Vg : Valuation Fq)
    (claimsG : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (successG : BoolVar Fq)
    (hg : (GroupHalf.wrap Vg claimsG successG).Reads E cp pub)
    (hgbit : (↑successG : CVar Fq).val Vg = 1)
    -- across the two, at whichever output the circuit returns
    (ht : ∀ o : FopOutput Fp, HalvesTies E cp pub (GroupHalf.wrap Vg claimsG successG)
      (ScalarHalf.step Vs claimsS evals mask prevChallenges o)) :
    ⦃⌜True⌝⦄
    finalizeOtherProofStepAt (c := Builder Vs (KimchiConstraint Fp)) E domains claimsS evals
      maskCells prevCells domainLog2Var
    ⦃⇓ o _ => ⌜SgOk E cp pub ∧ (↑o.finalized : CVar Fp).val Vs = 1
      ↔ kimchiVerify IpaVesta.curve E.σ E.cvk cp pub = true ∧
        (ScalarHalf.step Vs claimsS evals mask prevChallenges o).ClaimsHonest E cp pub⌝⦄ := by
  have hP : (FopParams.ofEnv E Linearization.fpTokens).endo = Pasta.pallasEndo ∧
      (FopParams.ofEnv E Linearization.fpTokens).mds = Reflect.symMds ∧
      (FopParams.ofEnv E Linearization.fpTokens).toks = Linearization.fpTokens :=
    ⟨hendo, by rfl, rfl⟩
  have hspec := finalizeOtherProofStep_spec_fp (V := Vs)
    (FopParams.ofEnv E Linearization.fpTokens) hP hsize h3zk domains hnodup hdomains claimsS
    evals maskCells mask.toList hm prevCells (prevChallenges.toList.map Vector.toList) hprev
    hprevlen domainLog2Var
  refine builder_spec_imp _ _ _ hspec ?_
  rintro o ⟨d₀, hd₀, hL, hread⟩
  obtain ⟨hn, hω⟩ := hsel d₀ hd₀ hL
  -- the circuit absorbs the kept challenge cells; their values are the proof's accumulators
  have hcells := map_map_val_of_forall₂ hprev
  have hdv : (Poseidon.squeeze (FopParams.ofEnv E Linearization.fpTokens).sponge
        (Poseidon.absorb (FopParams.ofEnv E Linearization.fpTokens).sponge Poseidon.init
          (List.zipWith (fun m cs => if m = true then cs.map (fun x => CVar.val x Vs) else [])
            mask.toList prevCells).flatten)).1
      = recDigest IpaVesta.curve (cp.olds.map (·.u)) := by
    have habs : (List.zipWith (fun m cs => if m = true then cs.map (fun x => CVar.val x Vs)
          else []) mask.toList prevCells).flatten
        = ((cp.olds.map (·.u)).toList.map Vector.toList).flatten := by
      have holds : (List.zipWith (fun m cv => if m = true then [cv] else []) mask.toList
          (prevChallenges.toList.map Vector.toList)).flatten
          = (cp.olds.map (·.u.toList)).toList := (ht o).olds
      rw [flatten_zipWith_val, hcells, holds]
      simp [Function.comp_def]
    rw [habs]
    rfl
  rw [hn, hω, hdv] at hread
  rw [← twoHalves_kimchiVerify_vesta E cp pub hguard Vg claimsG successG hg Vs claimsS evals
    mask prevChallenges o hread (ht o)]
  exact ⟨fun h => ⟨⟨hgbit, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩

end Pickles
