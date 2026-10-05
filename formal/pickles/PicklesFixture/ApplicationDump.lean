import PicklesFixture.ShapeDump
import PicklesFixture.Constants
import PicklesFixture.Rule

/-!
# Application reconstruction sidecars

Typed readers for the PureScript application sidecar: shape, replayable rules, resolved keys,
and shared protocol inputs. This module reads no independently compiled circuit dump.
-/

namespace PicklesFixture.Application

open Lean Snarky Snarky.Kimchi Pickles Pickles.Application Bulletproof
open CompElliptic.Fields.Pasta

/-- The SRS reference checked against a supplied shared SRS. -/
structure SrsReference (C : Ipa.KimchiCurve) where
  /-- The deployed truncation in IPA rounds. -/
  rounds : Nat
  /-- The blinding base; a consistency check rather than a complete SRS identifier. -/
  h : C.Point

/-- The raw challenges and their endomorphism expansion. -/
structure ChallengesDump (C : Ipa.KimchiCurve) (k : Nat) where
  /-- The transcript's 128-bit values. -/
  raw : Vector C.ScalarField k
  /-- The scalars of the challenge polynomial. -/
  expanded : Vector C.ScalarField k

/-- Protocol inputs exported alongside an application. -/
structure EnvironmentDump where
  /-- The wrap SRS reference. -/
  wrapSrs : SrsReference IpaPallas.curve
  /-- The step SRS reference. -/
  stepSrs : SrsReference IpaVesta.curve
  /-- Wrap-proof padding challenges. -/
  wrapChallenges : ChallengesDump IpaPallas.curve WrapIPARounds
  /-- Step-proof padding challenges. -/
  stepChallenges : ChallengesDump IpaVesta.curve StepIPARounds
  /-- Unfinalized padding indexed by the branch's predecessor count. -/
  unfinalized : Vector (UnfVal WrapIPARounds) (MaxProofsVerified + 1)
  /-- The supported wrap-domain index used in prover padding. -/
  wrapDomain : Fin wrapDomainLog2s.length

/-- Backend metadata identifying one compiled import. -/
structure ImportDump where
  /-- The complete checked wrap key. -/
  wrapKey : Key IpaPallas.curve 1
  /-- The source's step-proof chunk count. -/
  stepChunks : Nat
  /-- The source's step domains in branch order. -/
  stepDomains : Array Nat

/-- One application's typed reconstruction inputs. -/
structure ApplicationDump where
  /-- Statement layouts and branch-local slot routing. -/
  shape : ShapeDump
  /-- Input checks, rule operations and returned expressions in branch order. -/
  rules : Array RuleDump
  /-- The application's checked wrap key. -/
  wrapKey : Key IpaPallas.curve 1
  /-- The common chunk count of its step keys. -/
  stepChunks : Nat
  /-- The checked step key of each branch. -/
  stepKeys : Array (Key IpaVesta.curve stepChunks)
  /-- Resolved sources in the shape's import-index order. -/
  imports : Array ImportDump
  /-- Shared SRS references and protocol padding. -/
  environment : EnvironmentDump

private def vectorOf {α : Type} (n : Nat) (read : Json → Except String α) (j : Json) :
    Except String (Vector α n) := do
  let xs ← FixtureKit.parseArrOf read j
  if h : xs.size = n then return ⟨xs, h⟩ else throw s!"expected {n} entries, got {xs.size}"

private def keyOf (C : Ipa.KimchiCurve) (k nc : Nat) (j : Json) :
    Except String (Key C nc) := do
  let cvk ← checkedKey C k nc j
  let some key := Key.check cvk | throw "the backend key failed its invariant check"
  return key

private def srsReferenceOf (C : Ipa.KimchiCurve) (name : String) (k : Nat) (j : Json) :
    Except String (SrsReference C) := do
  unless (← (← j.getObjVal? "curve").getStr?) == name do throw "wrong SRS curve"
  let rounds ← (← j.getObjVal? "rounds").getNat?
  unless rounds == k do throw "wrong SRS round count"
  return ⟨rounds, ← Fixture.parsePt C (← j.getObjVal? "h")⟩

private def challengesOf (C : Ipa.KimchiCurve) (k : Nat) (j : Json) :
    Except String (ChallengesDump C k) := do
  let raw ← vectorOf k (FixtureKit.parseZMod (n := C.scalar)) (← j.getObjVal? "raw")
  let expanded ← vectorOf k (FixtureKit.parseZMod (n := C.scalar)) (← j.getObjVal? "expanded")
  unless raw.all (fun x => x.val < 2 ^ 128) do throw "padding challenge exceeds 128 bits"
  unless raw.map (fun x => Poseidon.FqSponge.endoExpand C.lam x.val) == expanded do
    throw "padding challenge expansion differs"
  return ⟨raw, expanded⟩

private def unfinalizedOf (j : Json) : Except String (Vector (UnfVal WrapIPARounds)
    (MaxProofsVerified + 1)) := do
  let entries ← j.getArr?
  let vals ← entries.mapIdxM fun i entry => do
    unless (← (← entry.getObjVal? "predecessors").getNat?) == i do
      throw "unfinalized padding must be in predecessor-count order"
    let fields ← vectorOf (CircuitType.size Fp (UnfVal WrapIPARounds))
      FixtureKit.parseZMod (← entry.getObjVal? "fields")
    let value := CircuitType.fieldsToValue (F := Fp) (val := UnfVal WrapIPARounds) fields
    unless CircuitType.valueToFields (F := Fp) value == fields do
      throw "unfinalized padding has a noncanonical field encoding"
    return value
  if h : vals.size = MaxProofsVerified + 1 then return ⟨vals, h⟩
  else throw "missing unfinalized padding counts"

private def environmentOf (j : Json) : Except String EnvironmentDump := do
  let srs ← j.getObjVal? "srs"
  let padding ← j.getObjVal? "padding"
  let wrapDomain ← (← padding.getObjVal? "wrapDomain").getNat?
  if h : wrapDomain < wrapDomainLog2s.length then
    return {
      wrapSrs := ← srsReferenceOf IpaPallas.curve "pallas" WrapIPARounds (← srs.getObjVal? "wrap")
      stepSrs := ← srsReferenceOf IpaVesta.curve "vesta" StepIPARounds (← srs.getObjVal? "step")
      wrapChallenges := ← challengesOf IpaPallas.curve WrapIPARounds
        (← padding.getObjVal? "wrapChallenges")
      stepChallenges := ← challengesOf IpaVesta.curve StepIPARounds
        (← padding.getObjVal? "stepChallenges")
      unfinalized := ← unfinalizedOf (← padding.getObjVal? "unfinalized")
      wrapDomain := ⟨wrapDomain, h⟩ }
  else throw "unsupported padding wrap domain"

/-- Decode the full sidecar, checking key invariants, padding encodings and array counts. -/
def ApplicationDump.ofJson (j : Json) : Except String ApplicationDump := do
  let shape ← ShapeDump.ofJson (← j.getObjVal? "shape")
  let rules ← FixtureKit.parseArrOf RuleDump.ofJson (← j.getObjVal? "rules")
  let r ← j.getObjVal? "resolved"
  let stepChunks ← (← r.getObjVal? "stepChunks").getNat?
  unless stepChunks > 0 do throw "the application step chunk count must be positive"
  let stepKeys ← FixtureKit.parseArrOf (keyOf IpaVesta.curve StepIPARounds stepChunks)
    (← r.getObjVal? "stepKeys")
  let imports ← FixtureKit.parseArrOf (fun i => do
    let stepChunks ← (← i.getObjVal? "stepChunks").getNat?
    unless stepChunks > 0 do throw "an import step chunk count must be positive"
    let stepDomains ← FixtureKit.parseArrOf Json.getNat? (← i.getObjVal? "stepDomains")
    return (⟨← keyOf IpaPallas.curve WrapIPARounds 1 (← i.getObjVal? "wrapKey"),
      stepChunks, stepDomains⟩ : ImportDump))
    (← r.getObjVal? "imports")
  unless rules.size == shape.branches.size && stepKeys.size == shape.branches.size do
    throw "rule or step-key count differs from the shape"
  unless imports.size == shape.imports.size do throw "import count differs from the shape"
  return { shape, rules, stepChunks, stepKeys, imports
           wrapKey := ← keyOf IpaPallas.curve WrapIPARounds 1 (← r.getObjVal? "wrapKey")
           environment := ← environmentOf (← j.getObjVal? "environment") }

end PicklesFixture.Application
