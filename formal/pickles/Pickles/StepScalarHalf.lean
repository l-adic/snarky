import Pickles.Encoding
import Pickles.TwoHalves

/-!
# The step circuit's scalar half, at a key

`finalizeOtherProofStep` with its parameters fixed to the chunk count's and the round count's
(`FopParams.of`) and the deployed `Fp` linearization, and the capstone that runs it: the
scalar-side counterpart of `wrapVerifyAt_reads`. The two halves of a step proof's verification
run in different circuits over different fields, so each side gets a triple about its own
circuit, with the other half assumed.

`StepProof.scalarCircuit` is the gadget as a circuit of its input (`StepProof.ScalarIn`) with
`finalized` asserted: what the top-level statement compiles (`stepProof_kimchiVerify_vesta`).
-/

namespace Pickles

open Std.Do Snarky Snarky.Kimchi Kimchi.Verifier Bulletproof Bulletproof.Ipa
open Kimchi.Protocol.Linearization Poseidon.FqSponge
open CompElliptic.Fields.Pasta CompElliptic.Curves.Pasta

/-- The domains the step circuit's scalar half may select from, by `log2`: domains of the
field, each holding the zero-knowledge rows. Each candidate's generator is its size's
`domainGenerator`. -/
structure KnownDomains (nc : ℕ) where
  /-- The candidates' `log2`s. -/
  log2s : List ℕ
  /-- Each candidate is a domain of the field. -/
  log2s_le : ∀ d ∈ log2s, d ≤ IpaVesta.curve.twoAdicity
  /-- Each domain holds the chunk count's zero-knowledge rows. -/
  log2s_zkRows : ∀ d ∈ log2s, zkRowsOf nc ≤ 2 ^ d

namespace KnownDomains

variable {nc : ℕ} (D : KnownDomains nc)

/-- The candidates with their generators, as the circuit takes them. -/
def list : List (KnownDomain Fp) :=
  D.log2s.map fun d => ⟨d, domainGenerator IpaVesta.curve d⟩

/-- Domain sizes below the field's two-adicity are distinct in the field when they are distinct
as numbers. -/
private theorem cast_inj {a b : ℕ} (ha : a ≤ IpaVesta.curve.twoAdicity)
    (hb : b ≤ IpaVesta.curve.twoAdicity) (h : (a : Fp) = b) : a = b := by
  have hp : IpaVesta.curve.twoAdicity < PALLAS_BASE_CARD := by decide
  rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at h

/-- A candidate's `log2` is one of the record's. -/
private theorem log2_mem {d : KnownDomain Fp} (hd : d ∈ D.list) : d.log2 ∈ D.log2s := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hd
  exact hl

/-- The kept candidates' sizes are distinct in the field. -/
theorem nodup : ((KnownDomain.dedupSort D.list).map fun d => (d.log2 : Fp)).Nodup := by
  have hmap : ((KnownDomain.dedupSort D.list).map fun d => (d.log2 : Fp))
      = ((KnownDomain.dedupSort D.list).map (·.log2)).map fun l : ℕ => (l : Fp) := by
    rw [List.map_map]
    rfl
  rw [hmap]
  refine (KnownDomain.nodup_dedupSort D.list).map_on fun a ha b hb h => ?_
  obtain ⟨da, hda, rfl⟩ := List.mem_map.mp ha
  obtain ⟨db, hdb, rfl⟩ := List.mem_map.mp hb
  exact cast_inj (D.log2s_le _ (D.log2_mem (KnownDomain.mem_of_mem_dedupSort hda)))
    (D.log2s_le _ (D.log2_mem (KnownDomain.mem_of_mem_dedupSort hdb))) h

/-- Each generator has its domain's order. -/
theorem generator_pow : ∀ d ∈ D.list, d.generator ^ 2 ^ d.log2 = 1 := by
  simp only [list, List.mem_map]
  rintro _ ⟨d, -, rfl⟩
  exact domainGenerator_pow _ d

/-- Each domain holds the chunk count's zero-knowledge rows. -/
theorem zkRows_le : ∀ d ∈ D.list, zkRowsOf nc ≤ 2 ^ d.log2 := by
  simp only [list, List.mem_map]
  rintro _ ⟨d, hd, rfl⟩
  exact D.log2s_zkRows d hd

/-- A candidate the size of the key's domain, in the field, is the key's domain with the key's
generator. -/
theorem eq_key (K : Key IpaVesta.curve nc) {d : KnownDomain Fp} (hd : d ∈ D.list)
    (h : (d.log2 : Fp) = (K.cvk.domainLog2 : Fp)) :
    d = ⟨K.cvk.domainLog2, K.cvk.omega⟩ := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hd
  obtain rfl := cast_inj (D.log2s_le l hl) K.domainLog2_le h
  rw [K.omega_eq]

end KnownDomains

/-- A candidate list of `log2`s as `KnownDomains`, when its facts hold: each is decidable, so a
driver checks them once. -/
def KnownDomains.ofList? (nc : ℕ) (log2s : List ℕ) : Option (KnownDomains nc) :=
  if h : (∀ d ∈ log2s, d ≤ IpaVesta.curve.twoAdicity) ∧ (∀ d ∈ log2s, zkRowsOf nc ≤ 2 ^ d) then
    some ⟨log2s, h.1, h.2⟩
  else none

/-- `finalizeOtherProofStep` with the parameters at `nc` chunks and the proof's round count
(`FopParams.of`), the `Fp` token stream, and the mask and previous-challenge cells at the
finalized proof's width `w`. -/
def finalizeOtherProofStepAt {c : Type} [BasicSystem Fp c] [ConstraintHolds Fp c]
    [KimchiSystem Fp c] {k nc w : ℕ} (domains : KnownDomains nc)
    (u : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (evals : ChunkedEvals nc (FVar Fp))
    (mask : Vector (BoolVar Fp) w) (prevChallenges : Vector (Vector (FVar Fp) k) w)
    (domainLog2Var : FVar Fp) :
    CircuitM Fp c (FopOutput Fp) :=
  finalizeOtherProofStep (FopParams.of IpaVesta.curve nc k Linearization.fpTokens) domains.list
    u evals mask.toList (prevChallenges.toList.map Vector.toList) domainLog2Var

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

/-! ## The claims across the two circuits -/

/-- The claims the wrap statement carries across: each of the wrap circuit's claim cells holds
the step circuit's matching cell's value, reduced into the wrap field. -/
def ClaimsCast {k : ℕ} (Vg : Valuation Fq)
    (claimsG : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq))) (Vs : Valuation Fp)
    (claimsS : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp))) : Prop :=
  let g := claimsG.deferredValues
  let s := claimsS.deferredValues
  [g.plonk.alpha.val, g.plonk.beta.val, g.plonk.gamma.val, g.plonk.zeta.val, g.plonk.perm.val,
    g.plonk.zetaToSrsLength.val, g.plonk.zetaToDomainSize.val, g.combinedInnerProduct.val,
    g.xi.val, g.b.val, claimsG.spongeDigestBeforeEvaluations].map (·.val Vg)
    = [s.plonk.alpha.val, s.plonk.beta.val, s.plonk.gamma.val, s.plonk.zeta.val, s.plonk.perm.val,
      s.plonk.zetaToSrsLength.val, s.plonk.zetaToDomainSize.val, s.combinedInnerProduct.val,
      s.xi.val, s.b.val, claimsS.spongeDigestBeforeEvaluations].map (fun x => redFq (x.val Vs)) ∧
  g.bulletproofChallenges.toList.map (·.val.val Vg)
    = s.bulletproofChallenges.toList.map fun c => redFq (c.val.val Vs)

/-- The two sides decode a shifted claim alike across the reduction. -/
private theorem wrapDecode_redFq {Vg : Valuation Fq} {Vs : Valuation Fp} {c : Type1 (FVar Fq)}
    {x : Type1 (FVar Fp)} (hc : c.val.val Vg = redFq (x.val.val Vs)) :
    wrapDecode Vg c = (fopStep Vs).decode x := by
  simp only [wrapDecode, FopSide.decode, fopStep, stepShiftOps.reading, Type1.fromShifted, hc,
    val_redFq, ZMod.natCast_zmod_val]

/-- The digest crosses back through `castDigest`. -/
private theorem castDigest_redFq (x : Fp) : castDigest IpaVesta.curve (redFq x) = x := by
  simp only [castDigest, val_redFq, if_pos (ZMod.val_lt x)]
  exact ZMod.natCast_zmod_val x

/-- **The claims cast across make the two halves hold one set of claims.** With the wrap
circuit's claim cells the step circuit's reduced (`ClaimsCast`), `β`, `γ` reading as
prechallenges on the wrap side (the group read) and `α`, `ζ`, `ξ` and the round challenges on the
step side (the finalize read), both halves read one deferred-values record. -/
theorem halvesTies_of_cast {k nc w : ℕ} (Vg : Valuation Fq)
    (claimsG : UnfinalizedProof k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq))) (Vs : Valuation Fp)
    (claimsS : UnfinalizedProof k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (evals : ChunkedEvals nc (FVar Fp)) (mask : Vector (BoolVar Fp) w)
    (prevChallenges : Vector (Vector (FVar Fp) k) w)
    (hc : ClaimsCast Vg claimsG Vs claimsS)
    (hβ : ∃ m, Reads128 Vg claimsG.deferredValues.plonk.beta m)
    (hγ : ∃ m, Reads128 Vg claimsG.deferredValues.plonk.gamma m)
    (hα : ∃ m, Reads128 Vs claimsS.deferredValues.plonk.alpha m)
    (hζ : ∃ m, Reads128 Vs claimsS.deferredValues.plonk.zeta m)
    (hξ : ∃ m, Reads128 Vs claimsS.deferredValues.xi m)
    (hch : ∃ ms, List.Forall₂ (Reads128 Vs) claimsS.deferredValues.bulletproofChallenges.toList
      ms) :
    HalvesTies (GroupHalf.wrap Vg claimsG)
      (ScalarHalf.step Vs claimsS evals mask prevChallenges) := by
  obtain ⟨hl, hbp⟩ := hc
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hl
  obtain ⟨cα, cβ, cγ, cζ, cperm, czm, czn, ccip, cξ, cb, cdig, -⟩ := hl
  obtain ⟨b, hb⟩ := hβ
  obtain ⟨g, hg⟩ := hγ
  obtain ⟨a, ha⟩ := hα
  obtain ⟨z, hz⟩ := hζ
  obtain ⟨ξ, hxi⟩ := hξ
  obtain ⟨ms, hms⟩ := hch
  have hlen : ms.length = k := by simpa using hms.length_eq.symm
  let s := claimsS.deferredValues
  let dec := (fopStep Vs).decode
  let dv : DeferredValues k Prechallenge Fp :=
    { plonk := { alpha := ⟨a⟩, beta := ⟨b⟩, gamma := ⟨g⟩, zeta := ⟨z⟩, perm := dec s.plonk.perm
                 zetaToSrsLength := dec s.plonk.zetaToSrsLength
                 zetaToDomainSize := dec s.plonk.zetaToDomainSize }
      combinedInnerProduct := dec s.combinedInnerProduct, xi := ⟨ξ⟩
      bulletproofChallenges := ⟨(ms.map SizedF.mk).toArray, by simp [hlen]⟩
      b := dec s.b }
  have hchals : dv.bulletproofChallenges.toList.map (·.val) = ms := by
    simp [dv, Function.comp_def]
  refine ⟨⟨dv, ⟨reads128_redFq cα ha, hb, hg, reads128_redFq cζ hz, wrapDecode_redFq cperm,
      wrapDecode_redFq czm, wrapDecode_redFq czn, wrapDecode_redFq ccip, reads128_redFq cξ hxi,
      hchals ▸ forall₂_reads128_redFq hms _ hbp, wrapDecode_redFq cb⟩,
    ⟨ha, reads128_of_redFq cβ hb, reads128_of_redFq cγ hg, hz, rfl, rfl, rfl, rfl, hxi,
      hchals ▸ hms, rfl⟩⟩, ?_⟩
  show claimsS.spongeDigestBeforeEvaluations.val Vs
    = castDigest IpaVesta.curve (claimsG.spongeDigestBeforeEvaluations.val Vg)
  rw [cdig, castDigest_redFq]

/-- **The step circuit's scalar half decides `kimchiVerify`.** `twoHalves_kimchiVerify` as a
triple about the scalar circuit, with the wrap circuit's group half assumed
(`wrapVerifyAt_reads` produces it): `SgOk` with `finalized` set is equivalent to `kimchiVerify`
accepting with the claims honest. The parameters and domains are discharged by `K` and
`domains`; the cells owe a boolean mask, the key's domain `log2`, the claims cast across
(`ClaimsCast`) and the proof ties. -/
theorem finalizeOtherProofStepAt_kimchiVerify_vesta {nc w : ℕ}
    (S : Srs IpaVesta.curve) (K : Key IpaVesta.curve nc)
    (cp : KimchiProof IpaVesta.curve nc S.σ.k)
    (pub : Array Fp)
    (hguard : Guards IpaVesta.curve K.cvk cp pub)
    -- the step circuit: its valuation, its cells, the domains it may select from
    (Vs : Valuation Fp)
    (domains : KnownDomains nc)
    (claimsS : UnfinalizedProof S.σ.k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (evals : ChunkedEvals nc (FVar Fp))
    (mask : Vector (BoolVar Fp) w) (prevChallenges : Vector (Vector (FVar Fp) S.σ.k) w)
    (domainLog2Var : FVar Fp)
    -- at most two slots; the mask cells are boolean, and the domain cell holds the key's `log2`
    (hw : w ≤ MaxProofsVerified)
    (hmask : ∃ ms : Vector Bool w, CircuitType.Reads Vs mask ms)
    (hdom : domainLog2Var.val Vs = (K.cvk.domainLog2 : Fp))
    -- the wrap circuit's group half, and its asserted bit
    (Vg : Valuation Fq)
    (claimsG : UnfinalizedProof S.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (successG : BoolVar Fq)
    (hg : (GroupHalf.wrap Vg claimsG).Reads S.σ K.cvk cp pub successG)
    (hgbit : (↑successG : CVar Fq).val Vg = 1)
    -- across the two
    (hc : ClaimsCast Vg claimsG Vs claimsS)
    (hf : FopTies S.σ K.cvk cp pub (ScalarHalf.step Vs claimsS evals mask prevChallenges)) :
    ⦃⌜True⌝⦄
    finalizeOtherProofStepAt (c := Builder Vs (KimchiConstraint Fp)) domains claimsS evals
      mask prevChallenges domainLog2Var
    ⦃⇓ o _ => ⌜SgOk S.σ K.cvk cp pub ∧ (↑o.finalized : CVar Fp).val Vs = 1
      ↔ kimchiVerify IpaVesta.curve S.σ K.cvk cp pub = true ∧
        (ScalarHalf.step Vs claimsS evals mask prevChallenges).ClaimsHonest S.σ K.cvk cp pub⌝⦄ := by
  have hP : (FopParams.of IpaVesta.curve nc S.σ.k Linearization.fpTokens).endo = Pasta.pallasEndo ∧
      (FopParams.of IpaVesta.curve nc S.σ.k Linearization.fpTokens).mds = Reflect.symMds ∧
      (FopParams.of IpaVesta.curve nc S.σ.k Linearization.fpTokens).toks = Linearization.fpTokens :=
    ⟨rfl, by rfl, rfl⟩
  -- the cells read as their own values
  have hm : List.Forall₂ (CircuitType.Reads Vs) mask.toList
      (mask.toList.map fun (b : BoolVar Fp) => decide ((↑b : CVar Fp).val Vs = 1)) := by
    obtain ⟨ms, hms⟩ := hmask
    refine List.forall₂_map_right_iff.2 (List.forall₂_same.2 fun b hb => ?_)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h := CircuitType.reads_boolVar.mp
      (CircuitType.reads_vector.mp hms i (by simpa using hi))
    rw [CircuitType.reads_boolVar]
    cases hb : ms[i]'(by simpa using hi) <;> simp_all [bit]
  have hprev : List.Forall₂ (List.Forall₂ (CircuitType.Reads Vs))
      (prevChallenges.toList.map Vector.toList)
      (ScalarHalf.step Vs claimsS evals mask prevChallenges).prevVals := by
    refine List.forall₂_map_right_iff.2 (List.forall₂_map_left_iff.2
      (List.forall₂_same.2 fun cs _ => ?_))
    exact List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun x _ => CircuitType.reads_fvar.2 rfl)
  have hlen : (prevChallenges.toList.map Vector.toList).flatten.length < 2 ^ 128 := by
    have : (prevChallenges.toList.map Vector.toList).flatten.length
        = w * S.σ.k := by
      rw [List.length_flatten, List.map_map]
      simp [Function.comp_def]
    rw [this]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hw) S.rounds_small
  have hspec := finalizeOtherProofStep_spec_fp (V := Vs)
    (FopParams.of IpaVesta.curve nc S.σ.k Linearization.fpTokens) hP IpaVesta.curve.frSponge.hsize
    (three_le_zkRowsOf K.nc_pos) domains.list domains.nodup
    (fun d hd => ⟨domains.zkRows_le d hd, domains.generator_pow d hd⟩) claimsS
    evals mask.toList _ hm (prevChallenges.toList.map Vector.toList) _ hprev hlen
    domainLog2Var
  simp only [finalizeOtherProofStepAt]
  refine builder_spec_imp _ _ _ hspec ?_
  rintro o ⟨d₀, hd₀, hL, hread⟩
  -- the two halves hold one set of claims: `β`, `γ` read on the wrap side, the rest here
  have ht : HalvesTies (GroupHalf.wrap Vg claimsG)
      (ScalarHalf.step Vs claimsS evals mask prevChallenges) := by
    obtain ⟨og, hivp, -⟩ := hg
    obtain ⟨a₀, z₀, hα, hζ, ξ₀, -, ĉ, hξ, -, -, -, -, hĉ, -⟩ := hread
    exact halvesTies_of_cast Vg claimsG Vs claimsS evals mask prevChallenges hc
      ⟨_, hivp.2.1⟩ ⟨_, hivp.2.2.1⟩ ⟨a₀, hα⟩ ⟨z₀, hζ⟩ ⟨ξ₀, hξ⟩ ⟨ĉ, hĉ⟩
  -- the selected domain is the key's: two candidates of one size are one candidate
  have hd : d₀ = ⟨K.cvk.domainLog2, K.cvk.omega⟩ := domains.eq_key K hd₀ (hL.symm.trans hdom)
  have hn : 2 ^ d₀.log2 = K.cvk.n := by rw [hd]; rfl
  have hω : d₀.generator = K.cvk.omega := by rw [hd]
  -- the circuit absorbs the kept challenge cells; their values are the proof's accumulators
  have hcells := map_map_val_of_forall₂ hprev
  have hdv : (Poseidon.squeeze (FopParams.of IpaVesta.curve nc S.σ.k Linearization.fpTokens).sponge
        (Poseidon.absorb (FopParams.of IpaVesta.curve nc S.σ.k Linearization.fpTokens).sponge
          Poseidon.init
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
  rw [← twoHalves_kimchiVerify S.σ K (by norm_num [PALLAS_SCALAR_CARD])
    (by norm_num [PALLAS_BASE_CARD]) cp pub hguard _ successG hg _ o hread ht hf]
  exact ⟨fun h => ⟨⟨hgbit, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩

/-- What a set `finalized` bit certifies about the cells it finalized: with the domain cell
holding the key's `log2`, for any step proof and public input under the guards, the wrap
circuit's group half accepting it, its claim cells holding these reduced (`ClaimsCast`), the proof
ties and `SgOk` make `kimchiVerify` accept. -/
def StepFinalizeReads {nc w : ℕ} (σ : SRS IpaVesta.curve.Point) (cvk : KimchiVK IpaVesta.curve nc)
    (Vs : Valuation Fp)
    (claimsS : UnfinalizedProof σ.k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (evals : ChunkedEvals nc (FVar Fp))
    (mask : Vector (BoolVar Fp) w) (prevChallenges : Vector (Vector (FVar Fp) σ.k) w)
    (domainLog2Var : FVar Fp) : Prop :=
  domainLog2Var.val Vs = (cvk.domainLog2 : Fp) →
  ∀ (cp : KimchiProof IpaVesta.curve nc σ.k) (pub : Array Fp),
    Guards IpaVesta.curve cvk cp pub →
    ∀ (Vg : Valuation Fq)
      (claimsG : UnfinalizedProof σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
      (successG : BoolVar Fq),
      (GroupHalf.wrap Vg claimsG).Reads σ cvk cp pub successG → (↑successG : CVar Fq).val Vg = 1 →
      ClaimsCast Vg claimsG Vs claimsS →
      FopTies σ cvk cp pub (ScalarHalf.step Vs claimsS evals mask prevChallenges) →
      SgOk σ cvk cp pub → kimchiVerify IpaVesta.curve σ cvk cp pub = true

/-- `finalizeOtherProofStepAt_kimchiVerify_vesta` in `∀`-form: with the mask cells boolean, a
set `finalized` bit certifies `StepFinalizeReads`. -/
theorem finalizeOtherProofStepAt_finalizeReads {nc w : ℕ} (S : Srs IpaVesta.curve)
    (K : Key IpaVesta.curve nc)
    (Vs : Valuation Fp) (domains : KnownDomains nc)
    (claimsS : UnfinalizedProof S.σ.k (FVar Fp) (BoolVar Fp) (Type1 (FVar Fp)))
    (evals : ChunkedEvals nc (FVar Fp))
    (mask : Vector (BoolVar Fp) w) (prevChallenges : Vector (Vector (FVar Fp) S.σ.k) w)
    (domainLog2Var : FVar Fp) (hw : w ≤ MaxProofsVerified) :
    ⦃⌜True⌝⦄
    finalizeOtherProofStepAt (c := Builder Vs (KimchiConstraint Fp)) domains claimsS evals
      mask prevChallenges domainLog2Var
    ⦃⇓ o _ => ⌜(∃ ms : Vector Bool w, CircuitType.Reads Vs mask ms) →
      (↑o.finalized : CVar Fp).val Vs = 1 →
      StepFinalizeReads S.σ K.cvk Vs claimsS evals mask prevChallenges domainLog2Var⌝⦄ := by
  rw [builder_spec_iff]
  intro nv hsat hmask h1 hdom cp pub hguard Vg claimsG successG hg hgbit hc hf hsg
  exact (((builder_spec_iff _ _).mp
    (finalizeOtherProofStepAt_kimchiVerify_vesta S K cp pub hguard Vs domains claimsS evals mask
      prevChallenges domainLog2Var hw hmask hdom Vg claimsG successG hg hgbit hc hf)
    nv hsat).mp ⟨hsg, h1⟩).1

/-! ## The circuit of its input

The gadget does not check its mask cells, so its read assumes them boolean. `scalarCircuit`
takes the slot's branch data as a checked component of its input: compiled (`Snarky.compile`),
the branch data's check is among its rows, and booleanity follows from satisfaction
(`BranchData.mask_boolean`). -/

/-- The branch data's check makes every mask bit boolean. -/
theorem BranchData.mask_boolean {V : Valuation Fp} (bd : BranchData (FVar Fp) (BoolVar Fp))
    (h : CheckedType.post (c := Builder V (KimchiConstraint Fp)) (val := BranchData Fp Bool)
      V bd) :
    ∃ ms : Vector Bool MaxProofsVerified, CircuitType.Reads V bd.proofsVerifiedMask ms := by
  simp only [CheckedType.post] at h
  refine CircuitType.exists_reads_vector fun i hi => ?_
  obtain ⟨bb, hbb⟩ :=
    h.2 bd.proofsVerifiedMask[i] (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))
  exact ⟨bb, CircuitType.reads_boolVar.mpr hbb⟩

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
instance instScalarInputCheckedType {F c f w b vb : Type} {k nc : ℕ} [Field F]
    [BasicSystem F c] [ConstraintHolds F c] [CircuitType F f w] [CircuitType F b vb]
    [CheckedType F c f w]
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
    ScalarHalf IpaVesta.curve (Type1 (FVar Fp)) k nc MaxProofsVerified :=
  ScalarHalf.step V s.claims s.evals s.branch.proofsVerifiedMask s.prev

/-- The step circuit's scalar half as a circuit of its input: the gadget, then `finalized`
asserted, as at a slot whose `shouldFinalize` is set. -/
def scalarCircuit {c : Type} [BasicSystem Fp c] [ConstraintHolds Fp c] [KimchiSystem Fp c]
    {k nc : ℕ} (domains : KnownDomains nc) (s : ScalarVar k nc) :
    CircuitM Fp c Unit := do
  let o ← finalizeOtherProofStepAt domains s.claims s.evals s.branch.proofsVerifiedMask s.prev
    s.branch.domainLog2
  assert o.finalized

/-- **The body's read.** A valuation satisfying the body makes `kimchiVerify` accept, under
`SgOk` and the hypotheses of `finalizeOtherProofStepAt_kimchiVerify_vesta`, with `finalized`
asserted by the circuit rather than assumed. -/
theorem scalarCircuit_reads {nc : ℕ}
    (S : Srs IpaVesta.curve) (K : Key IpaVesta.curve nc) (cp : KimchiProof IpaVesta.curve nc S.σ.k)
    (pub : Array Fp)
    (hguard : Guards IpaVesta.curve K.cvk cp pub)
    (Vs : Valuation Fp) (domains : KnownDomains nc) (s : ScalarVar S.σ.k nc)
    (hmask : ∃ ms : Vector Bool MaxProofsVerified,
      CircuitType.Reads Vs s.branch.proofsVerifiedMask ms)
    (hdom : s.branch.domainLog2.val Vs = (K.cvk.domainLog2 : Fp))
    (Vg : Valuation Fq)
    (claimsG : UnfinalizedProof S.σ.k (FVar Fq) (BoolVar Fq) (Type1 (FVar Fq)))
    (successG : BoolVar Fq)
    (hg : (GroupHalf.wrap Vg claimsG).Reads S.σ K.cvk cp pub successG)
    (hgbit : (↑successG : CVar Fq).val Vg = 1)
    (hc : ClaimsCast Vg claimsG Vs s.claims)
    (hf : FopTies S.σ K.cvk cp pub (s.half Vs))
    (hsg : SgOk S.σ K.cvk cp pub) :
    ⦃⌜True⌝⦄
    scalarCircuit (c := Builder Vs (KimchiConstraint Fp)) domains s
    ⦃⇓ _ _ => ⌜kimchiVerify IpaVesta.curve S.σ K.cvk cp pub = true⌝⦄ := by
  have hAt := finalizeOtherProofStepAt_kimchiVerify_vesta S K cp pub hguard Vs domains s.claims
    s.evals s.branch.proofsVerifiedMask s.prev s.branch.domainLog2 le_rfl hmask hdom Vg claimsG
    successG hg hgbit hc hf
  simp only [scalarCircuit]
  mvcgen [hAt]
  rename_i o _ hiff _ _
  intro hfin
  exact (hiff.mp ⟨hsg, hfin⟩).1

end StepProof

end Pickles
