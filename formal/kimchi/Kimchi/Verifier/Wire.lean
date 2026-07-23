import Kimchi.Verifier.Kimchi

/-!
# The wire boundary: serde-typed records and the check parse

The ONLY module that speaks the raw wire types, and it exports exactly one thing: a
proven parser. The wire records mirror the serde layer of proof-systems — the fixed
`[T; N]` dimensions are `Vector`s (serde rejects wrong lengths at deserialization),
chunk payloads are unchecked `Array`s (`PolyComm.elems` is `Vec<G>`) — and
`KimchiProof.check` / `KimchiVK.check` are the verifier's own family of length checks
(`check_proof_evals_len` at `chunk_size`, the `t` bound, the `nc > 1`
public-evaluation requirement) factored as a total parse into the CHECKED records
(`Kimchi.Verifier.KimchiProof`/`KimchiVK`, which carry the chunk count in their
types). A checked record cannot hold a ragged proof — the parse IS the proof.

There is deliberately no verifier here: clients (the fixture drivers, any host) parse
at the run's chunk count (`runNc`, under the SRS pin `σ.k ≤ domainLog2`) and call the
protocol verifier `Kimchi.Verifier.kimchiVerify` on the parsed records themselves —
check-then-verify is the client's one-line composition. On the fields production
checks — the evaluation lengths and the `t` bound — rejecting ragged input is the
same observable behavior as production's `Err` returns; on `w_comm`/`z_comm`, which
production never length-checks, the parse is a declared strengthening (see
`KimchiProof.check`). The protocol and soundness layers never import this module: no
statement above the boundary can depend on unchecked data.
-/

open Bulletproof

namespace Kimchi.Verifier.Wire

open CompElliptic.CurveForms.ShortWeierstrass
open Poseidon Poseidon.FqSponge Bulletproof
open Kimchi.Verifier (PointEvaluations ProofEvaluations PubEvalSrc)

variable (C : Ipa.CommitmentCurve)

/-! ## The wire records -/

/-- A wire polynomial commitment: the per-chunk commitment vector (`PolyComm.elems`,
`Vec<G>`). serde imposes NO length here — the chunk count is a verify-time check
(`checkChunks` against the run's `chunk_size`). -/
private abbrev PolyComm (C : Ipa.CommitmentCurve) := Array C.Point

/-- The kimchi proof wire record (`ProverProof` + `ProofEvaluations`, proof.rs:50–170),
basic gate set: fixed dimensions serde-typed, chunk payloads unchecked arrays. Lookup
data and `prev_challenges` are absent — declared deferrals of this transcription. -/
structure KimchiProof (C : Ipa.CommitmentCurve) where
  /-- The 15 witness-column commitments (`w_comm: [PolyComm; COLUMNS]`). -/
  wComm : Vector (PolyComm C) wCols
  /-- The permutation-aggregation commitment (`z_comm`). -/
  zComm : PolyComm C
  /-- The quotient commitment (`t_comm`); its chunk count is checked `≤ 7 · nc`
  (verifier.rs:260–264). -/
  tComm : PolyComm C
  /-- The claimed evaluations, per column family and per chunk. -/
  evals : ProofEvaluations (Array C.ScalarField)
  /-- The carried public evaluations (production's `evals.public`, proof.rs:52 —
  `public` is a Lean keyword; carried at proof level rather than inside `evals`, a
  flattening choice only): REQUIRED when `nc > 1`; when present they take precedence
  over the barycentric computation at any `nc` (verifier.rs:332). -/
  pubEvals : Option (PointEvaluations (Array C.ScalarField))
  /-- `ft(ζω)` (Maller's optimization; proof.rs:170) — the ft row is single-chunk. -/
  ftEval1 : C.ScalarField
  /-- The batched IPA opening proof — the serde wire form; its round count is checked
  against the SRS's `σ.k` by the parse. -/
  opening : Ipa.Wire.Proof C

/-- The kimchi verifier index wire record (`VerifierIndex`, verifier_index.rs): fixed
dimensions serde-typed (`sigma_comm: [PolyComm; PERMUTS]`,
`coefficients_comm: [PolyComm; COLUMNS]`, `shift: [F; PERMUTS]`), chunk payloads
unchecked arrays. The SRS stays separate and universal; `nc` is derived in
the client from the domain and the SRS width (`chunk_size = d1 / max_poly_size`,
verifier.rs:145–152). -/
structure KimchiVK (C : Ipa.CommitmentCurve) where
  /-- The domain size exponent: `n = 2 ^ domainLog2`. -/
  domainLog2 : ℕ
  /-- The domain generator `ω` (`domain.group_gen`). -/
  omega : C.ScalarField
  /-- The 7 permutation commitments (`sigma_comm`). -/
  sigmaComm : Vector (PolyComm C) permCols
  /-- The 15 coefficient commitments (`coefficients_comm`). -/
  coefficientsComm : Vector (PolyComm C) coeffCols
  genericComm : PolyComm C
  poseidonComm : PolyComm C
  completeAddComm : PolyComm C
  mulComm : PolyComm C
  emulComm : PolyComm C
  endomulScalarComm : PolyComm C
  /-- The 7 permutation shifts (`shift`). -/
  shifts : Vector C.ScalarField permCols
  /-- The number of zero-knowledge rows (`zk_rows`) — nc-dependent in production
  (constraints.rs:774–784), carried as data here. -/
  zkRows : ℕ
  /-- `verifier_index.endo`, the `ft_eval0` endo coefficient. -/
  endo : C.ScalarField
  /-- The precomputed `VerifierIndex::digest()` — an input here. -/
  digest : C.BaseField
  /-- The Lagrange-basis commitments (`get_lagrange_basis` over a sub-domain SRS
  chunks every basis polynomial). -/
  lagrangeBasis : Array (PolyComm C)
  /-- The scalar-side Poseidon parameters (`G::sponge_params()`), for the fr-sponge. -/
  frParams : Params C.ScalarField

/-- A chunk vector validated to the run's chunk count. -/
private def checkChunks {α : Type*} (nc : ℕ) (a : Array α) : Option (Vector α nc) :=
  if h : a.size = nc then some ⟨a, h⟩ else none

/-- Validate an evaluation pair's chunk vectors. -/
private def checkPointEvals {F : Type*} (nc : ℕ) (e : PointEvaluations (Array F)) :
    Option (PointEvaluations (Vector F nc)) := do
  return { zeta := ← checkChunks nc e.zeta, zetaOmega := ← checkChunks nc e.zetaOmega }

/-- Validate every evaluation pair of the record (`check_proof_evals_len`'s sweep). -/
private def checkEvals {F : Type*} (nc : ℕ) (e : ProofEvaluations (Array F)) :
    Option (ProofEvaluations (Vector F nc)) := do
  return { w := ← e.w.mapM (checkPointEvals nc)
           z := ← checkPointEvals nc e.z
           s := ← e.s.mapM (checkPointEvals nc)
           coefficients := ← e.coefficients.mapM (checkPointEvals nc)
           genericSelector := ← checkPointEvals nc e.genericSelector
           poseidonSelector := ← checkPointEvals nc e.poseidonSelector
           completeAddSelector := ← checkPointEvals nc e.completeAddSelector
           mulSelector := ← checkPointEvals nc e.mulSelector
           emulSelector := ← checkPointEvals nc e.emulSelector
           endomulScalarSelector := ← checkPointEvals nc e.endomulScalarSelector }

/-- **The proof check**, at the run's chunk count `nc` and the SRS's round count `k`
(the opening's `lr` length). Production's two length checks are transcribed: the
evaluation sweep (`check_proof_evals_len` at `expected_size` — exactly this `nc` —
verifier.rs:640–642, called at `chunk_size`, :831) and the quotient bound
`t_comm.len() ≤ 7 · chunk_size` (`IncorrectCommitmentLength`, verifier.rs:260–266).
Pinning `w_comm`/`z_comm` to `nc` chunks is a declared modeling STRENGTHENING:
production never checks those chunk counts (ragged commitment vectors flow into the
batch equations rather than `Err`-ing), but the checked record is uniform by type, so
the parse fixes them. Fidelity direction: a production-accepted run with a ragged
`w_comm` would have no Lean counterpart — such a run would fail the batched opening
anyway, but that is an argument, not a check. -/
def KimchiProof.check {C : Ipa.CommitmentCurve} (nc k : ℕ) (p : KimchiProof C) :
    Option (Kimchi.Verifier.KimchiProof C nc k) := do
  let wComm ← p.wComm.mapM (checkChunks nc)
  let zComm ← checkChunks nc p.zComm
  let opening ← p.opening.check k
  if htc : p.tComm.size ≤ 7 * nc then
    let evals ← checkEvals nc p.evals
    let pubEvals ← match p.pubEvals with
      | some pe => (checkPointEvals nc pe).map .carried
      | none => if h : nc = 1 then some (.barycentric h) else none
    return { wComm, zComm, tComm := p.tComm, tComm_le := htc, evals, pubEvals,
             ftEval1 := p.ftEval1, opening := opening }
  else none

/-- **The key check**: every committed column validated to `nc` chunks. The Lagrange
basis is validated in FULL (production computes it from the SRS, where the chunking is
structural — `get_lagrange_basis` chunks every basis polynomial identically; a wire
key with ragged Lagrange data corresponds to no SRS and is rejected). -/
def KimchiVK.check {C : Ipa.CommitmentCurve} (nc : ℕ) (vk : KimchiVK C) :
    Option (Kimchi.Verifier.KimchiVK C nc) := do
  return { domainLog2 := vk.domainLog2, omega := vk.omega
           sigmaComm := ← vk.sigmaComm.mapM (checkChunks nc)
           coefficientsComm := ← vk.coefficientsComm.mapM (checkChunks nc)
           genericComm := ← checkChunks nc vk.genericComm
           poseidonComm := ← checkChunks nc vk.poseidonComm
           completeAddComm := ← checkChunks nc vk.completeAddComm
           mulComm := ← checkChunks nc vk.mulComm
           emulComm := ← checkChunks nc vk.emulComm
           endomulScalarComm := ← checkChunks nc vk.endomulScalarComm
           shifts := vk.shifts, zkRows := vk.zkRows, endo := vk.endo
           digest := vk.digest
           lagrangeBasis := ← vk.lagrangeBasis.mapM (checkChunks nc)
           frParams := vk.frParams }

/-- The run's chunk count, from the domain and SRS widths (production
`chunk_size = d1 / max_poly_size`, verifier.rs:145–152): the count clients `check`
against. Meaningful only under the SRS pin `σ.k ≤ vk.domainLog2` (production's
sub-SRS `chunk_size = 1` regime is out of scope); clients guard it. -/
def runNc (σ : SRS C.Point) (vk : KimchiVK C) : ℕ :=
  2 ^ (vk.domainLog2 - σ.k)

end Kimchi.Verifier.Wire

/-! ## The Pasta instantiations -/

namespace Kimchi.Verifier.Wire.KimchiVesta

open CompElliptic.Fields.Pasta Poseidon Kimchi.Verifier Bulletproof

abbrev Proof := KimchiProof IpaVesta.curve
abbrev VK := KimchiVK IpaVesta.curve

/-- The Vesta-side fr-sponge Poseidon parameters: the scalar field is `Fp`, so the
production `G::sponge_params()` is the `fp_kimchi` table. The fixture decoder pins
`KimchiVK.frParams` to this value. -/
def frParams : Params Fp := fpParams


end Kimchi.Verifier.Wire.KimchiVesta

namespace Kimchi.Verifier.Wire.KimchiPallas

open CompElliptic.Fields.Pasta Poseidon Kimchi.Verifier Bulletproof

abbrev Proof := KimchiProof IpaPallas.curve
abbrev VK := KimchiVK IpaPallas.curve

/-- The Pallas-side fr-sponge Poseidon parameters: the scalar field is `Fq`, so the
production `G::sponge_params()` is the `fq_kimchi` table. The fixture decoder pins
`KimchiVK.frParams` to this value. -/
def frParams : Params Fq := fqParams


end Kimchi.Verifier.Wire.KimchiPallas
