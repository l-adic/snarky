import Lean.Data.Json
import KimchiFixture.Cache
import BulletproofFixture
import FixtureKit.Parse
import Pickles.Env
import Pickles.StepMain
import PicklesFixture.Group

/-!
# The circuit dumps' constants

The constants a circuit-diffs dump carries beside its circuit (the `constants` object, one
variant per kind of circuit): the readers that decode the main circuits' variants, the shapes
the wrap circuit's builder takes them in, and the main-circuit dumps by name. The dump
comparison builds the circuits from them; the premise check decides the capstones' constant
premises on them.

## Main definitions

* `PicklesFixture.WrapMainConsts`, `PicklesFixture.wrapMainOf`: a wrap main's constants and
  their reader.
* `PicklesFixture.StepMainConsts`, `PicklesFixture.stepMainOf`: a step main's.
* `PicklesFixture.wrapMainDumps`, `PicklesFixture.stepMainDumps`: the main-circuit dumps with
  their shapes.
-/

namespace PicklesFixture

open Lean Snarky Snarky.Kimchi Kimchi CompElliptic.Fields.Pasta

/-- Where the circuit-diffs results live (workspace-relative default, env override). -/
def resultsDir : IO System.FilePath := do
  match (← IO.getEnv "KIMCHI_PS_RESULTS_DIR") with
  | some d => return d
  | none =>
    return ".." / "packages" / "pickles-circuit-diffs" / "circuits" / "results"

/-- A dump's constants, read by `read`; a missing dump is an error. -/
def readConstants {α : Type} (path : System.FilePath) (read : Json → Except String α) : IO α := do
  unless ← path.pathExists do throw (IO.userError s!"missing dump: {path}")
  match Json.parse (← IO.FS.readFile path) >>= read with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- A dump's constants, read by `read`, when the dump is present. Under `KIMCHI_CS_FILTER` a
missing dump is skipped (a narrowed PS run writes only the selected circuits); in the unfiltered
run — CI — it is an error. -/
def dumpConstants {α : Type} (filter : String) (path : System.FilePath)
    (read : Json → Except String α) : IO (Option α) := do
  if (← path.pathExists) || filter.isEmpty then
    some <$> readConstants path read
  else
    IO.println s!"· {path.fileName.getD path.toString} not dumped: its constants are skipped"
    pure none

/-- The SRS blinding base `h` of a fixture (`srs_h`, the same production SRS the IPA
fixture checks read). -/
def blindingBase (C : Bulletproof.Ipa.KimchiCurve) (path : System.FilePath) : IO C.Point := do
  let raw ← IO.FS.readFile path
  match Json.parse raw >>= fun j => j.getObjVal? "srs_h" >>= Bulletproof.Fixture.parsePt C with
  | .ok P => return P
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- A dump's constants of variant `kind`: the `constants` object the PureScript side wrote beside
the circuit it compiled. A dump without constants, or with another variant's, fails here. -/
def constantsOf (kind : String) (j : Json) : Except String Json := do
  let .ok c := j.getObjVal? "constants" | throw s!"the dump carries no constants, expected {kind}"
  if c.isNull then throw s!"the dump carries no constants, expected {kind}"
  let k ← (← c.getObjVal? "kind").getStr?
  unless k == kind do throw s!"constants of kind {k}, expected {kind}"
  return c

/-- A table entry's `nc` chunks, as points of `C`. -/
def chunksOf (C : Bulletproof.Ipa.KimchiCurve) (nc : ℕ) (j : Json) :
    Except String (Vector C.Point nc) := do
  let pts ← FixtureKit.parseArrOf (Bulletproof.Fixture.parsePt C) j
  if h : pts.size = nc then pure ⟨pts, h⟩ else throw s!"{pts.size} chunks, expected {nc}"

/-- A key a dump exports whole (`{vk, digest}`, the proof cache's encoding), at `nc` chunks: it
passes the wire check (`Wire.KimchiVK.check`) and the pickles key's (`Pickles.Key.check`), and
`nc` is the chunk count an SRS of `2 ^ k` points gives its domain (`chunkCount`). -/
def checkedKey (C : Bulletproof.Ipa.KimchiCurve) (k nc : ℕ) (j : Json) :
    Except String (Kimchi.Verifier.KimchiVK C nc) := do
  let d ← (← j.getObjVal? "digest").getStr?
  let some digest := d.toNat? | throw s!"key digest is not a numeral: {d.take 40}"
  let vk ← Kimchi.Fixture.Cache.parseVK C C.endoScalar (digest : C.BaseField)
    (← Json.parse (← (← j.getObjVal? "vk").getStr?))
  let some cvk := vk.check nc | throw "the key fails the wire check"
  let some K := Pickles.Key.check cvk
    | throw "the key breaks a key invariant: its shifts or generator are not the curve's, its \
        zero-knowledge rows are not the chunk count's or overflow its domain, or its digest is \
        not its commitments'"
  unless nc = Kimchi.Verifier.chunkCount k cvk.domainLog2 do
    throw s!"the key runs at {Kimchi.Verifier.chunkCount k cvk.domainLog2} chunks, not {nc}"
  return K.cvk

/-- The constants a `wrap_main_*` circuit bakes in, at `nc` step chunks. -/
structure WrapMainConsts (nc : ℕ) where
  /-- Each branch's slot count. -/
  stepWidths : List ℕ
  /-- Each branch's step key, checked at the step SRS (`checkedKey`). -/
  keys : List (Kimchi.Verifier.KimchiVK Bulletproof.IpaVesta.curve nc)
  /-- Per public-input scalar, each branch's Lagrange base. -/
  lagrange : Array (List (Vector XhatCurve.Point nc))
  /-- The blinding base. -/
  h : XhatCurve.Point
  /-- Per branch, each slot's wrap domain index, `none` when side-loaded. -/
  pins : List (List (Option ℕ))
  /-- Each slot's challenge-stack height. -/
  slotWidths : List ℕ
  /-- The padding challenge vector. -/
  dummy : Vector Fq 15

/-- A wrap main's constants (`wrapMain`), at `nc` step chunks: per branch its slot count, its
step key (checked at the step SRS) and its table, transposed here to per scalar; the blinding
`h`, the pins, the slot widths and the padding challenges. -/
def wrapMainOf (nc : ℕ) (j : Json) : Except String (WrapMainConsts nc) := do
  let c ← constantsOf "wrapMain" j
  let nats (k : String) : Except String (List ℕ) := do
    pure (← FixtureKit.parseArrOf (fun j => j.getNat?) (← c.getObjVal? k)).toList
  let branches ← (← c.getObjVal? "branches").getArr?
  let tables ← branches.mapM fun b => do
    FixtureKit.parseArrOf (chunksOf XhatCurve nc) (← b.getObjVal? "lagrange")
  unless (tables.map (·.size)).toList.eraseDups.length ≤ 1 do
    throw "the branches' tables differ in length"
  pure
    { stepWidths := (← branches.mapM fun b => do (← b.getObjVal? "width").getNat?).toList
      keys := (← branches.mapM fun b => do
        checkedKey Bulletproof.IpaVesta.curve Pickles.StepIPARounds nc
          (← b.getObjVal? "key")).toList
      lagrange := (List.transpose (tables.toList.map (·.toList))).toArray
      h := ← Bulletproof.Fixture.parsePt XhatCurve (← c.getObjVal? "h")
      pins := (← FixtureKit.parseArrOf
        (fun j => do pure (← FixtureKit.parseArrOf
          (fun j => if j.isNull then pure none else some <$> j.getNat?) j).toList)
        (← c.getObjVal? "pins")).toList
      slotWidths := ← nats "slotWidths"
      dummy := ← do
        let d ← FixtureKit.parseArrOf FixtureKit.parseZMod (← c.getObjVal? "dummy")
        if h : d.size = 15 then pure ⟨d, h⟩ else throw s!"dummy: {d.size} challenges" }

/-- `n` exported counts, each at most `cap`, when they are: the branches' slot counts, the
slots' challenge-stack heights. -/
def wrapMainWidths? (n cap : ℕ) (ws : List ℕ) : Option (Vector (Fin (cap + 1)) n) :=
  if h : ws.length = n ∧ ∀ x ∈ ws, x ≤ cap then
    some (Vector.ofFn fun b =>
      ⟨ws[b.val]'(by omega), Nat.lt_succ_of_le (h.2 _ (List.getElem_mem _))⟩)
  else none

/-- The exported step keys as one per branch, when they are. -/
def wrapMainKeys? {nc : ℕ} (bp : ℕ)
    (ks : List (Kimchi.Verifier.KimchiVK Bulletproof.IpaVesta.curve nc)) :
    Option (Vector (Kimchi.Verifier.KimchiVK Bulletproof.IpaVesta.curve nc) (bp + 1)) :=
  if h : ks.length = bp + 1 then some ⟨ks.toArray, by simpa using h⟩ else none

/-- The exported pins as each slot's column over the branches, when every branch has one entry
per slot: `none` marks a side-loaded predecessor, `some` the wrap domain index. -/
def wrapMainPins? (bp mpv : ℕ) (pins : List (List (Option ℕ))) :
    Option (Vector (Vector (Option ℕ) (bp + 1)) mpv) :=
  if h : pins.length = bp + 1 ∧ ∀ row ∈ pins, row.length = mpv then
    some (Vector.ofFn fun s => Vector.ofFn fun b =>
      (pins[b.val]'(by omega))[s.val]'(by
        rw [h.2 _ (List.getElem_mem _)]
        exact s.2))
  else none

/-- The exported Lagrange bases as one table per branch, when there are `m` scalars with one
base per branch each. -/
def wrapMainTables? (bp nc m : ℕ) (lagrange : Array (List (Vector XhatCurve.Point nc))) :
    Option (Vector (Vector (Vector XhatCurve.Point nc) m) (bp + 1)) :=
  if h : lagrange.size = m ∧ ∀ row ∈ lagrange.toList, row.length = bp + 1 then
    some (Vector.ofFn fun b => Vector.ofFn fun i =>
      (lagrange[i.val]'(by omega))[b.val]'(by
        rw [h.2 _ (Array.getElem_mem_toList _)]
        exact b.2))
  else none

/-- The `wrap_main_*` dumps with their branch, slot and chunk counts. -/
def wrapMainDumps : List (String × ℕ × ℕ × ℕ) :=
  [ ("wrap_main_circuit", 0, 1, 1),
    ("wrap_main_side_loaded_main_circuit", 0, 1, 1),
    ("wrap_main_n2_circuit", 0, 2, 1),
    ("wrap_main_add_one_return_circuit", 0, 0, 1),
    ("chunks2_wrap_main_circuit", 0, 0, 2),
    ("wrap_main_tree_proof_return_circuit", 0, 2, 1),
    ("wrap_main_two_phase_chain_circuit", 1, 1, 1) ]

/-- One slot of a `step_main_*` dump's constants, the step proofs it finalizes at `ncs` chunks. -/
structure StepSlotConsts (ncs : ℕ) where
  /-- Whether the slot verifies this tag's proofs rather than another's. -/
  self : Bool
  /-- The wrap key the slot verifies against, checked at the wrap SRS (`checkedKey`). -/
  key : Kimchi.Verifier.KimchiVK Bulletproof.IpaPallas.curve 1
  /-- The slot's width, at most `MaxProofsVerified`. -/
  width : Fin (Pickles.MaxProofsVerified + 1)
  /-- Its candidate step domains. -/
  domains : Pickles.KnownDomains ncs
  /-- The Lagrange bases its public-input commitment reads, one per packed statement cell. -/
  lagrange : Pickles.SlotLagrange 1 Pickles.StepIPARounds

/-- The constants of a `step_main_*` dump with `n` slots, whose step proofs are at `ncs` chunks:
the blinding `h`, each slot's, and this compile's own step domains (its self slots'). -/
structure StepMainConsts (n ncs : ℕ) where
  /-- The blinding base. -/
  h : XhatStepCurve.Point
  /-- Each slot's constants, in the rule's order. -/
  slots : Vector (StepSlotConsts ncs) n
  /-- This compile's own step domains. -/
  ownDomains : Pickles.KnownDomains ncs

/-- A slot's source: an external slot carries its checked wrap key's commitments, its Lagrange
bases and its candidate domains. -/
def StepSlotConsts.source {ncs : ℕ} (s : StepSlotConsts ncs) :
    Pickles.SlotSource 1 Pickles.StepIPARounds :=
  if s.self then .self s.lagrange
  else .external s.key.comms s.lagrange s.width.val s.domains.list

/-- A slot's width is at most `MaxProofsVerified` when the tag's is. -/
theorem StepSlotConsts.width_le {ncs : ℕ} (s : StepSlotConsts ncs) {w : ℕ}
    (hw : w ≤ Pickles.MaxProofsVerified) :
    s.source.width w ≤ Pickles.MaxProofsVerified := by
  unfold StepSlotConsts.source
  split
  · exact hw
  · exact Nat.le_of_lt_succ s.width.isLt

/-- A step main's constants (`stepMain`), with `n` slots at the tag's width `w`, every slot's step
proofs at `ncs` chunks: a self slot's width must be `w`, and the self slots share this compile's
step domains. Side-loaded slots are outside this corpus. -/
def stepMainOf (n w ncs : ℕ) (j : Json) : Except String (StepMainConsts n ncs) := do
  let c ← constantsOf "stepMain" j
  let domains (ls : List ℕ) : Except String (Pickles.KnownDomains ncs) := do
    let some d := Pickles.KnownDomains.ofList? ncs ls | throw s!"step domains {ls} are no domains"
    pure d
  let slot (j : Json) : Except String (StepSlotConsts ncs) := do
    let chunks ← (← j.getObjVal? "numChunks").getNat?
    unless chunks = ncs do throw s!"{chunks} chunks, expected {ncs}"
    let wd ← (← j.getObjVal? "width").getNat?
    let some width := (if h : wd < Pickles.MaxProofsVerified + 1 then some ⟨wd, h⟩ else none)
      | throw s!"width {wd} above MaxProofsVerified"
    let self ← match ← (← j.getObjVal? "kind").getStr? with
      | "self" =>
        unless wd = w do throw s!"a self slot of width {wd} in a tag of width {w}"
        pure true
      | "external" => pure false
      | kind => throw s!"unsupported slot kind {kind}"
    pure { self, width
           key := ← checkedKey Bulletproof.IpaPallas.curve Pickles.WrapIPARounds 1
             (← j.getObjVal? "key")
           domains := ← domains (← FixtureKit.parseArrOf (fun j => j.getNat?)
             (← j.getObjVal? "domains")).toList
           lagrange := ← do
             let pts ← FixtureKit.parseArrOf (chunksOf XhatStepCurve 1) (← j.getObjVal? "lagrange")
             let m := CircuitType.size Fp
               (Pickles.PackedWrapStatement Pickles.StepIPARounds (Type1 Fp) Fp)
             if h : pts.size = m then pure ⟨pts, h⟩
             else throw s!"{pts.size} Lagrange bases, expected {m}" }
  let slots ← FixtureKit.parseArrOf slot (← c.getObjVal? "slots")
  let some slots := (if h : slots.size = n then some (⟨slots, h⟩ : Vector _ n) else none)
    | throw s!"{slots.size} slots, expected {n}"
  let own := (slots.toList.filter (·.self)).map (·.domains.log2s)
  unless own.all (· == own.headD []) do throw s!"self slots disagree on step domains {own}"
  pure { h := ← Bulletproof.Fixture.parsePt XhatStepCurve (← c.getObjVal? "h"), slots,
         ownDomains := ← domains (own.headD []) }

/-- The `step_main_*` dumps with their slot count and their tag's width. -/
def stepMainDumps : List (String × ℕ × ℕ) :=
  [ ("step_main_simple_chain_n2_circuit", 2, 2),
    ("step_main_two_phase_chain_make_zero_circuit", 0, 1),
    ("step_main_two_phase_chain_increment_circuit", 1, 1),
    ("step_main_tree_proof_return_circuit", 2, 2),
    ("step_main_import_two_phase_chain_circuit", 2, 2) ]

/-- The dummy `sg_old` (PS `dummyWrapSg`), a point of the wrap proofs' curve. -/
def dummyWrapSgPt : Bulletproof.IpaPallas.curve.Point :=
  ⟨8063668238751197448664615329057427953229339439010717262869116690340613895496,
   2694491010813221541025626495812026140144933943906714931997499229912601205355,
   Or.inl (by decide)⟩

end PicklesFixture
