import Pickles.Encoding
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

/-- The domains a step circuit's scalar half may select from, at an environment: the
candidate list with what every honest list satisfies — distinct sizes, each generator of its
order, each domain holding the zero-knowledge rows — and the key's own domain among them, at
its `log2`. -/
structure KnownDomains (E : Env IpaVesta.curve) where
  /-- The candidates. -/
  list : List (KnownDomain Fp)
  /-- Distinct sizes, as the circuit compares them. -/
  nodup : (list.map fun d => (d.log2 : Fp)).Nodup
  /-- Each generator has its domain's order. -/
  generator_pow : ∀ d ∈ list, d.generator ^ 2 ^ d.log2 = 1
  /-- Each domain holds the key's zero-knowledge rows. -/
  zkRows_le : ∀ d ∈ list, E.cvk.zkRows ≤ 2 ^ d.log2
  /-- `log2` of the key's domain size. -/
  keyLog2 : ℕ
  /-- The key's domain size is that power of two. -/
  key_n : E.cvk.n = 2 ^ keyLog2
  /-- The key's domain is a candidate. -/
  key_mem : (⟨keyLog2, E.cvk.omega⟩ : KnownDomain Fp) ∈ list

/-- `g ^ 2 ^ k` by `k` squarings. The generic power compiles to a recursion as deep as its
exponent, which a `2 ^ 15`-element domain overflows the stack on. -/
def powTwoPow (g : Fp) : ℕ → Fp
  | 0 => g
  | k + 1 => powTwoPow g k * powTwoPow g k

theorem powTwoPow_eq (g : Fp) (k : ℕ) : powTwoPow g k = g ^ 2 ^ k := by
  induction k with
  | zero => simp [powTwoPow]
  | succ k ih => rw [powTwoPow, ih, ← pow_add, ← two_mul, ← pow_succ']

/-- The bundle of a candidate list and the key's `log2`, where its facts hold: each is
decidable, so a driver checks them once on the domains a proof cache uses. The generator
orders are checked by squaring (`powTwoPow`). -/
def KnownDomains.ofList? (E : Env IpaVesta.curve) (list : List (KnownDomain Fp))
    (keyLog2 : ℕ) : Option (KnownDomains E) :=
  if h : (list.map fun d => (d.log2 : Fp)).Nodup ∧
      (∀ d ∈ list, powTwoPow d.generator d.log2 = 1) ∧
      (∀ d ∈ list, E.cvk.zkRows ≤ 2 ^ d.log2) ∧
      E.cvk.n = 2 ^ keyLog2 ∧ (⟨keyLog2, E.cvk.omega⟩ : KnownDomain Fp) ∈ list then
    some ⟨list, h.1, fun d hd => powTwoPow_eq d.generator d.log2 ▸ h.2.1 d hd, h.2.2.1,
      keyLog2, h.2.2.2.1, h.2.2.2.2⟩
  else none

/-- The step circuit's scalar half at an environment: `finalize_other_proof`'s step side with
the verifier key's parameters, the `Fp` token stream, and the mask and previous-challenge
cells at their static sizes. -/
def finalizeOtherProofStepAt {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c] {k : ℕ}
    (E : Env IpaVesta.curve) (domains : KnownDomains E)
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) (w : AllEvals (FVar Fp))
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
the wrap circuit's group half assumed (`wrapVerifyAt_reads` produces it). What the circuit's
parameters and domain list owe is the environment's and the bundle's; what is left is about
cells: the mask is boolean, the `domain_log2` cell holds the key's, and the ties. -/
theorem finalizeOtherProofStepAt_kimchiVerify_vesta
    (E : Env IpaVesta.curve)
    (cp : KimchiProof IpaVesta.curve 1 E.σ.k)
    (pub : Array Fp)
    (hguard : Guards IpaVesta.curve E.cvk cp pub)
    -- the step circuit: its valuation, its cells, the domains it may select from
    (Vs : Valuation Fp)
    (domains : KnownDomains E)
    (claimsS : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (evals : AllEvals (FVar Fp))
    (mask : Vector (BoolVar Fp) MaxProofsVerified)
    (prevChallenges : Vector (Vector (FVar Fp) E.σ.k) MaxProofsVerified)
    (domainLog2Var : FVar Fp)
    -- the mask cells are boolean, and the `domain_log2` cell holds the key's
    (hmask : ∀ b ∈ mask.toList, (↑b : CVar Fp).val Vs = 0 ∨ (↑b : CVar Fp).val Vs = 1)
    (hdom : domainLog2Var.val Vs = (domains.keyLog2 : Fp))
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
    ⦃⇓ o _ => ⌜SgOk E cp pub ∧ (↑o.finalized : CVar Fp).val Vs = 1
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
    evals mask.toList _ hm (prevChallenges.toList.map Vector.toList) _ hprev hlen domainLog2Var
  simp only [finalizeOtherProofStepAt]
  refine builder_spec_imp _ _ _ hspec ?_
  rintro o ⟨d₀, hd₀, hL, hread⟩
  -- the selected domain is the key's: two candidates of one size are one candidate
  have hd : d₀ = ⟨domains.keyLog2, E.cvk.omega⟩ :=
    List.inj_on_of_nodup_map domains.nodup hd₀ domains.key_mem (hL.symm.trans hdom)
  have hn : 2 ^ d₀.log2 = E.cvk.n := by rw [hd, domains.key_n]
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
  rw [← twoHalves_kimchiVerify_vesta E cp pub hguard Vg claimsG successG hg Vs claimsS evals
    mask prevChallenges o hread ht hf]
  exact ⟨fun h => ⟨⟨hgbit, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩

/-! ## The circuit of its branch data

`Step.Main` witnesses a slot's branch data — the mask and the domain's `log2` — with its
check, and hands the checked cells to `finalize_other_proof`, which never re-checks them. So
the gadget's read owes the mask's booleanity to whoever calls it. `stepScalarCircuit` is the
gadget as a circuit whose input IS the branch data: compiled (`Snarky.compile`), the input's
check is among its rows, and the booleanity follows from satisfaction instead of being
assumed. The gadget beneath is untouched. -/

/-- What the branch data's check forces of the mask: every bit is boolean. -/
theorem BranchData.mask_boolean {V : Valuation Fp} (bd : BranchData (FVar Fp) (BoolVar Fp))
    (h : CheckedType.post (c := Builder V (KimchiConstraint Fp)) (val := BranchData Fp Bool)
      V bd) :
    ∀ b ∈ bd.proofsVerifiedMask.toList,
      (↑b : CVar Fp).val V = 0 ∨ (↑b : CVar Fp).val V = 1 := by
  simp only [CheckedType.post] at h
  intro b hb
  obtain ⟨bb, hbb⟩ := h.2 b hb
  cases bb <;> simp [hbb, bit]

/-- The step circuit's scalar half as a circuit of its branch data: the input is the mask and
the domain's `log2`, and the body pipes them to the gadget and asserts `finalized` — the
deployed `finalized ∨ ¬should_finalize` at a slot that is finalized. -/
def stepScalarCircuit {c : Type} [BasicSystem Fp c] [KimchiSystem Fp c] {k : ℕ}
    (E : Env IpaVesta.curve) (domains : KnownDomains E)
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) (w : AllEvals (FVar Fp))
    (prevChallenges : Vector (Vector (FVar Fp) k) MaxProofsVerified)
    (bd : BranchData (FVar Fp) (BoolVar Fp)) : CircuitM Fp c Unit := do
  let o ← finalizeOtherProofStepAt E domains u w bd.proofsVerifiedMask prevChallenges
    bd.domainLog2
  assert o.finalized

/-- **The body's read.** With the mask boolean, the `domain_log2` cell the key's, the wrap
circuit's group half and the ties, a valuation satisfying the body makes `kimchiVerify`
accept once `SgOk` holds: `finalizeOtherProofStepAt_kimchiVerify_vesta` with `finalized`
asserted by the circuit rather than assumed of its output. -/
theorem stepScalarCircuit_reads
    (E : Env IpaVesta.curve) (cp : KimchiProof IpaVesta.curve 1 E.σ.k) (pub : Array Fp)
    (hguard : Guards IpaVesta.curve E.cvk cp pub)
    (Vs : Valuation Fp) (domains : KnownDomains E)
    (claimsS : UnfinalizedProof E.σ.k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (evals : AllEvals (FVar Fp))
    (prevChallenges : Vector (Vector (FVar Fp) E.σ.k) MaxProofsVerified)
    (bd : BranchData (FVar Fp) (BoolVar Fp))
    (hmask : ∀ b ∈ bd.proofsVerifiedMask.toList,
      (↑b : CVar Fp).val Vs = 0 ∨ (↑b : CVar Fp).val Vs = 1)
    (hdom : bd.domainLog2.val Vs = (domains.keyLog2 : Fp))
    (Vg : Valuation Fq)
    (claimsG : UnfinalizedProof E.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (successG : BoolVar Fq)
    (hg : (GroupHalf.wrap Vg claimsG).Reads E cp pub successG)
    (hgbit : (↑successG : CVar Fq).val Vg = 1)
    (ht : HalvesTies (GroupHalf.wrap Vg claimsG)
      (ScalarHalf.step Vs claimsS evals bd.proofsVerifiedMask prevChallenges))
    (hf : FopTies E cp pub
      (ScalarHalf.step Vs claimsS evals bd.proofsVerifiedMask prevChallenges))
    (hsg : SgOk E cp pub) :
    ⦃⌜True⌝⦄
    stepScalarCircuit (c := Builder Vs (KimchiConstraint Fp)) E domains claimsS evals
      prevChallenges bd
    ⦃⇓ _ _ => ⌜kimchiVerify IpaVesta.curve E.σ E.cvk cp pub = true⌝⦄ := by
  have hAt := finalizeOtherProofStepAt_kimchiVerify_vesta E cp pub hguard Vs domains claimsS
    evals bd.proofsVerifiedMask prevChallenges bd.domainLog2 hmask hdom Vg claimsG successG hg
    hgbit ht hf
  simp only [stepScalarCircuit]
  mvcgen [hAt]
  rename_i o _ hiff _ _
  intro hfin
  exact (hiff.mp ⟨hsg, hfin⟩).1

end Pickles
