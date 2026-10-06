import PicklesFixture.ApplicationDump
import PicklesFixture.ApplicationCircuit

/-!
# Reconstruct an application from its sidecar

Assembly consumes typed sidecar data, the shared SRSs, the memoised Lagrange tables and
already reconstructed producers. The Lagrange tables are read from the memo under
`lagrange-cache/`, never computed here; the padding commitments are computed by the library's
SRS definitions. The independent circuit dump is only a comparison target and is not an
argument to assembly.
-/

namespace PicklesFixture.Application

open Lean Snarky Snarky.Kimchi Pickles Pickles.Application Bulletproof Kimchi.Verifier
open CompElliptic.Fields.Pasta

/-- A reconstructed application, retained together with its shared protocol setup. -/
structure ImportedApplication where
  /-- The application shape obtained from the sidecar. -/
  shape : Shape
  /-- Checked wiring and replayed branch rules. -/
  assembled : Assembled shape
  /-- Canonical statement encodings for resolving producer/consumer interfaces. -/
  schemas : FieldSchemas shape
  /-- Advice used by the wrap prover in positions absent from its selected branch. -/
  padding : WrapPadding
  /-- SRSs and the decoded or derived padding values. -/
  setup : Setup

/-- An application's Lagrange tables as read from the memo: the wrap key's commitments and, per
step domain exponent, that domain's, each commitment in chunks. Assembly cuts them to the
statement sizes it needs and checks their chunk counts. -/
structure LagrangeTables where
  /-- The wrap key's commitments, one chunk each. -/
  wrap : Array (Array IpaPallas.curve.Point)
  /-- Per step domain exponent, that domain's commitments. -/
  step : List (Nat × Array (Array IpaVesta.curve.Point))

/-- The first `count` of `pts` as commitments of `nc` chunks. -/
private def tableOf (C : Ipa.KimchiCurve) (nc count : Nat) (pts : Array (Array C.Point)) :
    Except String (Vector (Vector C.Point nc) count) := do
  unless count ≤ pts.size do
    throw s!"a Lagrange table of {pts.size} commitments, {count} needed"
  let rows ← (pts.extract 0 count).mapM fun v =>
    if h : v.size = nc then pure (⟨v, h⟩ : Vector C.Point nc)
    else throw s!"a Lagrange commitment of {v.size} chunks, expected {nc}"
  if h : rows.size = count then return ⟨rows, h⟩
  else throw s!"a Lagrange table of {rows.size} commitments, expected {count}"

/-- Compare wrap keys by commitments and metadata; their remaining fields are pinned by `Key`. -/
def sameKey (a b : Key IpaPallas.curve 1) : Bool :=
  decide (a.cvk.comms = b.cvk.comms) && a.cvk.domainLog2 == b.cvk.domainLog2 &&
    a.cvk.publicCount == b.cvk.publicCount && a.cvk.prevChallenges == b.cvk.prevChallenges

/-- Match source chunks and candidate domains, ignoring repeated domains and their order. -/
def ImportDump.domainsMatch (imp : ImportDump) (chunks : Nat) (domains : List Nat) : Bool :=
  imp.stepChunks == chunks &&
    imp.stepDomains.toList.mergeSort.eraseDups == domains.mergeSort.eraseDups

private def resolve (raw : ApplicationDump) (known : Array ImportedApplication) :
    Except String (Array KnownTag) :=
  raw.imports.mapM fun imp =>
    match known.find? (fun p => sameKey p.assembled.wiring.backend.wrapKey imp.wrapKey) with
    | none => .error "an import has no previously reconstructed producer"
    | some p =>
      let source := p.assembled.wiring.export
      if imp.domainsMatch source.stepChunks source.stepDomains.log2s then
        .ok ⟨imp.wrapKey, p.assembled.layout.export, source, p.schemas.own, p.schemas.own_eq⟩
      else .error "an import's domains or chunks disagree with its producer"

private def setupOf (E : EnvironmentDump)
    (wrap : Srs IpaPallas.curve) (step : Srs IpaVesta.curve) : Except String Setup := do
  unless E.wrapSrs.h == wrap.σ.h && E.stepSrs.h == step.σ.h do
    throw "the shared SRS blinding bases differ from the sidecar"
  if hw : wrap.σ.k = WrapIPARounds then
    if hs : step.σ.k = StepIPARounds then
      let u := E.wrapChallenges.expanded.cast hw.symm
      let dummySg := Ipa.msm IpaPallas.curve wrap.σ.g (bPolyCoefficients fun i => u[i])
      return { wrap, step, wrapRounds := hw, stepRounds := hs, dummySg
               dummyUnf := E.unfinalized
               dummy := E.wrapChallenges.expanded }
    else throw "the shared step SRS has the wrong round count"
  else throw "the shared wrap SRS has the wrong round count"

private def assembleFor (raw : ApplicationDump) (loaded : LoadedShape)
    (wrap : Srs IpaPallas.curve) (step : Srs IpaVesta.curve) (tables : LagrangeTables) :
    Except String (Assembled loaded.shape × Setup) := do
  let D := loaded.shape
  let S ← setupOf raw.environment wrap step
  let stepKeys ← if h : raw.stepKeys.size = D.branches then
      pure (⟨raw.stepKeys, h⟩ : Vector _ D.branches)
    else throw "the step-key count differs from the application"
  let wrapLagrange ← tableOf IpaPallas.curve 1
    (CircuitType.size Fp (PackedWrapStatement StepIPARounds (Type1 Fp) Fp)) tables.wrap
  let backend : BackendArtifacts D :=
    { wrapKey := raw.wrapKey, stepChunks := raw.stepChunks, stepKeys, wrapLagrange }
  let wiring ← Wiring.assemble loaded.layout backend loaded.imports
  let rules ← finSequence fun b : D.Branch => do
    let some rule := raw.rules[b.val]? | throw "a branch rule is missing"
    CheckedRule.check D b rule
  let m := CircuitType.size Fp (StepStatement (UnfVal WrapIPARounds) Fp D.width)
  let stepTables ← (stepDomainLog2s wiring.stepKeys).toList.eraseDups.mapM fun d => do
    let some pts := tables.step.lookup d | throw s!"no Lagrange table for the step domain 2^{d}"
    let table ← tableOf IpaVesta.curve wiring.backend.stepChunks m pts
    return (d, table)
  let stepLagrange := fun d =>
    (stepTables.lookup d).getD (Vector.replicate m (Vector.replicate _ 0))
  return (⟨loaded.layout, wiring, rules, stepLagrange⟩, S)

/-- Reconstruct checked application circuits from the sidecar, the shared SRSs, the memoised
Lagrange tables and the imports. -/
def ApplicationDump.assemble (raw : ApplicationDump)
    (wrap : Srs IpaPallas.curve) (step : Srs IpaVesta.curve) (tables : LagrangeTables)
    (known : Array ImportedApplication) : Except String ImportedApplication :=
  if (List.finRange raw.imports.size).any (fun i =>
      (List.finRange i.val).any fun j =>
        sameKey raw.imports[i].wrapKey raw.imports[j.val].wrapKey) then
    .error "the same source key has two import indices"
  else match resolve raw known with
  | .error e => .error e
  | .ok imports => match raw.shape.load imports with
    | .error e => .error e
    | .ok loaded => match assembleFor raw loaded wrap step tables with
      | .error e => .error e
      | .ok (A, S) =>
        let u := raw.environment.stepChallenges.expanded.cast S.stepRounds.symm
        let sg := Ipa.msm IpaVesta.curve S.step.σ.g (bPolyCoefficients fun i => u[i])
        let pad : WrapPadding :=
          ⟨⟨⟨sg.x, sg.y⟩⟩, raw.environment.wrapEvals, raw.environment.wrapDomain.val⟩
        .ok ⟨loaded.shape, A, loaded.schemas, pad, S⟩

end PicklesFixture.Application
