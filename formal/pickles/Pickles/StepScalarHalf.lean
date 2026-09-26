import Pickles.Encoding
import Pickles.TwoHalves

/-!
# The step circuit's scalar half, at an environment

`finalizeOtherProofStep` with its parameters fixed to the verifier key's (`FopParams.ofEnv`)
and the deployed `Fp` linearization, and the capstone that runs it: the scalar-side counterpart
of `wrapVerifyAt_reads`. The two halves of a step proof's verification run in different
circuits over different fields, so each side gets a triple about its own circuit, with the
other half assumed.

`StepProof.scalarCircuit` is the gadget as a circuit of its input (`StepProof.ScalarIn`) with
`finalized` asserted: what the top-level statement compiles (`stepProof_kimchiVerify_vesta`).
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open Kimchi.Protocol.Linearization Poseidon.FqSponge
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The domains the step circuit's scalar half may select from, by `log2`: distinct sizes,
each holding the zero-knowledge rows, and the key's own domain among them. Each candidate's
generator is its size's `domainGenerator`. -/
structure KnownDomains {nc : ℕ} (E : Env IpaVesta.curve nc) where
  /-- The candidates' `log2`s. -/
  log2s : List ℕ
  /-- Distinct sizes, as the circuit compares them. -/
  log2s_nodup : (log2s.map fun d : ℕ => (d : Fp)).Nodup
  /-- Each domain holds the key's zero-knowledge rows. -/
  log2s_zkRows : ∀ d ∈ log2s, E.cvk.zkRows ≤ 2 ^ d
  /-- The key's domain is a candidate. -/
  domainLog2_mem : E.cvk.domainLog2 ∈ log2s

namespace KnownDomains

variable {nc : ℕ} {E : Env IpaVesta.curve nc} (D : KnownDomains E)

/-- The candidates with their generators, as the circuit takes them. -/
def list : List (KnownDomain Fp) :=
  D.log2s.map fun d => ⟨d, domainGenerator IpaVesta.curve d⟩

/-- The candidates' sizes are distinct. -/
theorem nodup : (D.list.map fun d => (d.log2 : Fp)).Nodup := by
  rw [list, List.map_map]
  exact D.log2s_nodup

/-- Each generator has its domain's order. -/
theorem generator_pow : ∀ d ∈ D.list, d.generator ^ 2 ^ d.log2 = 1 := by
  simp only [list, List.mem_map]
  rintro _ ⟨d, -, rfl⟩
  exact domainGenerator_pow _ d

/-- Each domain holds the key's zero-knowledge rows. -/
theorem zkRows_le : ∀ d ∈ D.list, E.cvk.zkRows ≤ 2 ^ d.log2 := by
  simp only [list, List.mem_map]
  rintro _ ⟨d, hd, rfl⟩
  exact D.log2s_zkRows d hd

/-- The key's domain, with the key's generator, is a candidate. -/
theorem key_mem : (⟨E.cvk.domainLog2, E.cvk.omega⟩ : KnownDomain Fp) ∈ D.list := by
  rw [E.omega_eq]
  exact List.mem_map.mpr ⟨_, D.domainLog2_mem, rfl⟩

end KnownDomains

/-- A candidate list of `log2`s as `KnownDomains`, when its facts hold: each is decidable, so a
driver checks them once. -/
def KnownDomains.ofList? {nc : ℕ} (E : Env IpaVesta.curve nc) (log2s : List ℕ) :
    Option (KnownDomains E) :=
  if h : (log2s.map fun d : ℕ => (d : Fp)).Nodup ∧ (∀ d ∈ log2s, E.cvk.zkRows ≤ 2 ^ d) ∧
      E.cvk.domainLog2 ∈ log2s then
    some ⟨log2s, h.1, h.2.1, h.2.2⟩
  else none

/-- `finalizeOtherProofStep` with the verifier key's parameters, the `Fp` token stream, and
the mask and previous-challenge cells at their static sizes. -/
def finalizeOtherProofStepAt {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c] {k nc : ℕ}
    (E : Env IpaVesta.curve nc) (domains : KnownDomains E)
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (w : ChunkedEvals nc (FVar Fp))
    (mask : Vector (BoolVar Fp) MaxProofsVerified)
    (prevChallenges : Vector (Vector (FVar Fp) k) MaxProofsVerified) (domainLog2Var : FVar Fp) :
    CircuitM Fp c (FopOutput Fp) :=
  finalizeOtherProofStep (FopParams.ofEnv E Linearization.fpTokens) domains.list u w
    mask.toList (prevChallenges.toList.map Vector.toList) domainLog2Var

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

/-- The mask keeps the same values whether it selects the challenge lists or singletons of
them: the circuit absorbs the first form, `FopTies.olds` states the second. -/
private theorem flatten_zipWith_val {V : Valuation Fp} :
    ∀ (ms : List Bool) (css : List (List (FVar Fp))),
      (List.zipWith (fun m cs => if m = true then cs.map (fun x => CVar.val x V) else [])
          ms css).flatten
        = ((List.zipWith (fun m cv => if m = true then [cv] else []) ms
            (css.map (fun cs => cs.map (fun x => CVar.val x V)))).flatten).flatten
  | [], _ => rfl
  | _ :: _, [] => rfl
  | m :: ms, cs :: css => by cases m <;> simp [flatten_zipWith_val ms css]

/-- **The step circuit's scalar half decides `kimchiVerify`.** `twoHalves_kimchiVerify` as a
triple about the scalar circuit, with the wrap circuit's group half assumed
(`wrapVerifyAt_reads` produces it): `SgOk` with `finalized` set is equivalent to `kimchiVerify`
accepting with the claims honest. The parameters and domains are discharged by `E` and
`domains`; the cells owe a boolean mask, the key's domain `log2`, and the ties. -/
theorem finalizeOtherProofStepAt_kimchiVerify_vesta {nc : ℕ}
    (E : Env IpaVesta.curve nc)
    (cp : KimchiProof IpaVesta.curve nc E.σ.k)
    (pub : Array Fp)
    (hguard : Guards IpaVesta.curve E.cvk cp pub)
    -- the step circuit: its valuation, its cells, the domains it may select from
    (Vs : Valuation Fp)
    (domains : KnownDomains E)
    (claimsS : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (evals : ChunkedEvals nc (FVar Fp))
    (mask : Vector (BoolVar Fp) MaxProofsVerified)
    (prevChallenges : Vector (Vector (FVar Fp) E.σ.k) MaxProofsVerified)
    (domainLog2Var : FVar Fp)
    -- the mask cells are boolean, and the domain cell holds the key's `log2`
    (hmask : ∀ b ∈ mask.toList, (↑b : CVar Fp).val Vs = 0 ∨ (↑b : CVar Fp).val Vs = 1)
    (hdom : domainLog2Var.val Vs = (E.cvk.domainLog2 : Fp))
    -- the wrap circuit's group half, and its asserted bit
    (Vg : Valuation Fq)
    (claimsG : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (successG : BoolVar Fq)
    (hg : (GroupHalf.wrap Vg claimsG).Reads E cp pub successG)
    (hgbit : (↑successG : CVar Fq).val Vg = 1)
    -- across the two
    (ht : HalvesTies (GroupHalf.wrap Vg claimsG)
      (ScalarHalf.step Vs claimsS evals mask prevChallenges))
    (hf : FopTies E cp pub (ScalarHalf.step Vs claimsS evals mask prevChallenges)) :
    ⦃⌜True⌝⦄
    finalizeOtherProofStepAt (c := Builder Vs (KimchiConstraint Fp)) E domains claimsS evals
      mask prevChallenges domainLog2Var
    ⦃⇓ o _ => ⌜SgOk E.σ E.cvk cp pub ∧ (↑o.finalized : CVar Fp).val Vs = 1
      ↔ kimchiVerify IpaVesta.curve E.σ E.cvk cp pub = true ∧
        (ScalarHalf.step Vs claimsS evals mask prevChallenges).ClaimsHonest E cp pub⌝⦄ := by
  have hP : (FopParams.ofEnv E Linearization.fpTokens).endo = Pasta.pallasEndo ∧
      (FopParams.ofEnv E Linearization.fpTokens).mds = Reflect.symMds ∧
      (FopParams.ofEnv E Linearization.fpTokens).toks = Linearization.fpTokens :=
    ⟨E.endo_eq, by rfl, rfl⟩
  -- the cells read as their own values
  have hm : List.Forall₂ (CircuitType.Reads Vs) mask.toList
      (mask.toList.map fun (b : BoolVar Fp) => decide ((↑b : CVar Fp).val Vs = 1)) := by
    refine List.forall₂_map_right_iff.2 (List.forall₂_same.2 fun b hb => ?_)
    rw [CircuitType.reads_boolVar]
    rcases hmask b hb with h | h <;> simp [h, bit]
  have hprev : List.Forall₂ (List.Forall₂ (CircuitType.Reads Vs))
      (prevChallenges.toList.map Vector.toList)
      (ScalarHalf.step Vs claimsS evals mask prevChallenges).prevVals := by
    refine List.forall₂_map_right_iff.2 (List.forall₂_map_left_iff.2
      (List.forall₂_same.2 fun cs _ => ?_))
    exact List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun x _ => CircuitType.reads_fvar.2 rfl)
  have hlen : (prevChallenges.toList.map Vector.toList).flatten.length < 2 ^ 128 := by
    have : (prevChallenges.toList.map Vector.toList).flatten.length
        = MaxProofsVerified * E.σ.k := by
      rw [List.length_flatten, List.map_map]
      simp [Function.comp_def]
    have := E.rounds_small
    omega
  have hspec := finalizeOtherProofStep_spec_fp (V := Vs)
    (FopParams.ofEnv E Linearization.fpTokens) hP IpaVesta.curve.frSponge.hsize E.zkRows_ge
    domains.list domains.nodup
    (fun d hd => ⟨domains.zkRows_le d hd, domains.generator_pow d hd⟩) claimsS
    evals mask.toList _ hm (prevChallenges.toList.map Vector.toList) _ hprev hlen
    domainLog2Var
  simp only [finalizeOtherProofStepAt]
  refine builder_spec_imp _ _ _ hspec ?_
  rintro o ⟨d₀, hd₀, hL, hread⟩
  -- the selected domain is the key's: two candidates of one size are one candidate
  have hd : d₀ = ⟨E.cvk.domainLog2, E.cvk.omega⟩ :=
    List.inj_on_of_nodup_map domains.nodup hd₀ domains.key_mem (hL.symm.trans hdom)
  have hn : 2 ^ d₀.log2 = E.cvk.n := by rw [hd]; rfl
  have hω : d₀.generator = E.cvk.omega := by rw [hd]
  -- the circuit absorbs the kept challenge cells; their values are the proof's accumulators
  have hcells := map_map_val_of_forall₂ hprev
  have hdv : (Poseidon.squeeze (FopParams.ofEnv E Linearization.fpTokens).sponge
        (Poseidon.absorb (FopParams.ofEnv E Linearization.fpTokens).sponge Poseidon.init
          (List.zipWith (fun m cs => if m = true then cs.map (fun x => CVar.val x Vs) else [])
            (mask.toList.map fun (b : BoolVar Fp) => decide ((↑b : CVar Fp).val Vs = 1))
            (prevChallenges.toList.map Vector.toList)).flatten)).1
      = recDigest IpaVesta.curve (cp.olds.map (·.u)) := by
    have habs : (List.zipWith (fun m cs => if m = true then cs.map (fun x => CVar.val x Vs)
          else []) (mask.toList.map fun (b : BoolVar Fp) => decide ((↑b : CVar Fp).val Vs = 1))
          (prevChallenges.toList.map Vector.toList)).flatten
        = ((cp.olds.map (·.u)).toList.map Vector.toList).flatten := by
      have holds : (List.zipWith (fun m cv => if m = true then [cv] else [])
          (mask.toList.map fun (b : BoolVar Fp) => decide ((↑b : CVar Fp).val Vs = 1))
          (ScalarHalf.step Vs claimsS evals mask prevChallenges).prevVals).flatten
          = (cp.olds.map (·.u.toList)).toList := hf.olds
      rw [flatten_zipWith_val, hcells, holds]
      simp [Function.comp_def]
    rw [habs]
    rfl
  rw [hn, hω, hdv] at hread
  rw [← twoHalves_kimchiVerify E (by norm_num [PALLAS_SCALAR_CARD])
    (by norm_num [PALLAS_BASE_CARD]) cp pub hguard _ successG hg _ o hread ht hf]
  exact ⟨fun h => ⟨⟨hgbit, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩

/-! ## The circuit of its input

The gadget does not check its mask cells, so its read assumes them boolean. `scalarCircuit`
takes the slot's branch data as a checked component of its input: compiled (`Snarky.compile`),
the branch data's check is among its rows, and booleanity follows from satisfaction
(`BranchData.mask_boolean`). -/

/-- The branch data's check makes every mask bit boolean. -/
theorem BranchData.mask_boolean {V : Valuation Fp} (bd : BranchData (FVar Fp) (BoolVar Fp))
    (h : CheckedType.post (c := Builder V (KimchiConstraint Fp)) (val := BranchData Fp Bool)
      V bd) :
    ∀ b ∈ bd.proofsVerifiedMask.toList,
      (↑b : CVar Fp).val V = 0 ∨ (↑b : CVar Fp).val V = 1 := by
  simp only [CheckedType.post] at h
  intro b hb
  obtain ⟨bb, hbb⟩ := h.2 b hb
  cases bb <;> simp [hbb, bit]

namespace StepProof

/-- The step circuit's scalar-half input, polymorphic in its cells: the slot's branch data,
checked on input, and the scalar half's own input, unchecked. -/
structure ScalarInput (k nc : ℕ) (f b : Type) where
  /-- The slot's branch data: the mask and the domain's `log2`. -/
  branch : BranchData f b
  /-- The slot's claims, the evaluations at `nc` chunks and the previous challenges. -/
  fop : UnChecked (FopInput k nc f b (Type1 f))

/-- A scalar-half input is its branch data and the rest. -/
def ScalarInput.equivProd (k nc : ℕ) (f b : Type) :
    ScalarInput k nc f b ≃ BranchData f b × UnChecked (FopInput k nc f b (Type1 f)) :=
  ⟨fun i => (i.branch, i.fop), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

instance instScalarInputCircuitType {F f w b vb : Type} {k nc : ℕ} [CircuitType F f w]
    [CircuitType F b vb] : CircuitType F (ScalarInput k nc f b) (ScalarInput k nc w vb) :=
  CircuitType.ofEquiv (ScalarInput.equivProd k nc f b) (ScalarInput.equivProd k nc w vb)

/-- The input's check is the branch data's: the rest is unchecked. -/
instance instScalarInputCheckedType {F c f w b vb : Type} {k nc : ℕ} [Add F] [Mul F] [Zero F]
    [One F] [BasicSystem F c] [CircuitType F f w] [CircuitType F b vb] [CheckedType F c f w]
    [CheckedType F c b vb] : CheckedType F c (ScalarInput k nc f b) (ScalarInput k nc w vb) :=
  CheckedType.ofEquiv (ScalarInput.equivProd k nc f b) (ScalarInput.equivProd k nc w vb)

/-- The scalar circuit's input, as values. -/
abbrev ScalarIn (k nc : ℕ) : Type := ScalarInput k nc Fp Bool

/-- `ScalarIn`, as cells. -/
abbrev ScalarVar (k nc : ℕ) : Type := ScalarInput k nc (FVar Fp) (BoolVar Fp)

/-- The slot's deferred claims. -/
def ScalarVar.claims {k nc : ℕ} (s : ScalarVar k nc) :
    UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)) := s.fop.val.claims

/-- The evaluation cells. -/
def ScalarVar.evals {k nc : ℕ} (s : ScalarVar k nc) : ChunkedEvals nc (FVar Fp) :=
  s.fop.val.evals

/-- The previous challenges, one vector per slot. -/
def ScalarVar.prev {k nc : ℕ} (s : ScalarVar k nc) :
    Vector (Vector (FVar Fp) k) MaxProofsVerified :=
  s.fop.val.prev

/-- The scalar circuit as a `ScalarHalf`. -/
abbrev ScalarVar.half {k nc : ℕ} (V : Valuation Fp) (s : ScalarVar k nc) :
    ScalarHalf IpaVesta.curve (Type1 (FVar Fp)) k nc :=
  ScalarHalf.step V s.claims s.evals s.branch.proofsVerifiedMask s.prev

/-- The step circuit's scalar half as a circuit of its input: the gadget, then `finalized`
asserted, as at a slot whose `shouldFinalize` is set. -/
def scalarCircuit {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c]
    {nc : ℕ} (E : Env IpaVesta.curve nc) (domains : KnownDomains E) (s : ScalarVar E.σ.k nc) :
    CircuitM Fp c Unit := do
  let o ← finalizeOtherProofStepAt E domains s.claims s.evals s.branch.proofsVerifiedMask s.prev
    s.branch.domainLog2
  assert o.finalized

/-- **The body's read.** A valuation satisfying the body makes `kimchiVerify` accept, under
`SgOk` and the hypotheses of `finalizeOtherProofStepAt_kimchiVerify_vesta`, with `finalized`
asserted by the circuit rather than assumed. -/
theorem scalarCircuit_reads {nc : ℕ}
    (E : Env IpaVesta.curve nc) (cp : KimchiProof IpaVesta.curve nc E.σ.k) (pub : Array Fp)
    (hguard : Guards IpaVesta.curve E.cvk cp pub)
    (Vs : Valuation Fp) (domains : KnownDomains E) (s : ScalarVar E.σ.k nc)
    (hmask : ∀ b ∈ s.branch.proofsVerifiedMask.toList,
      (↑b : CVar Fp).val Vs = 0 ∨ (↑b : CVar Fp).val Vs = 1)
    (hdom : s.branch.domainLog2.val Vs = (E.cvk.domainLog2 : Fp))
    (Vg : Valuation Fq)
    (claimsG : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (successG : BoolVar Fq)
    (hg : (GroupHalf.wrap Vg claimsG).Reads E cp pub successG)
    (hgbit : (↑successG : CVar Fq).val Vg = 1)
    (ht : HalvesTies (GroupHalf.wrap Vg claimsG) (s.half Vs))
    (hf : FopTies E cp pub (s.half Vs))
    (hsg : SgOk E.σ E.cvk cp pub) :
    ⦃⌜True⌝⦄
    scalarCircuit (c := Builder Vs (KimchiConstraint Fp)) E domains s
    ⦃⇓ _ _ => ⌜kimchiVerify IpaVesta.curve E.σ E.cvk cp pub = true⌝⦄ := by
  have hAt := finalizeOtherProofStepAt_kimchiVerify_vesta E cp pub hguard Vs domains s.claims
    s.evals s.branch.proofsVerifiedMask s.prev s.branch.domainLog2 hmask hdom Vg claimsG
    successG hg hgbit ht hf
  simp only [scalarCircuit]
  mvcgen [hAt]
  rename_i o _ hiff _ _
  intro hfin
  exact (hiff.mp ⟨hsg, hfin⟩).1

end StepProof

end Pickles
