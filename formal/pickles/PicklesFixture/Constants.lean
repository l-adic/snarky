import Lean.Data.Json
import KimchiFixture.Cache
import BulletproofFixture
import FixtureKit.Parse
import Pickles.Env
import Pickles.KeyLayout
import Pickles.StepMain
import Pickles.WrapMain
import PicklesFixture.Group

/-!
# The circuit dumps' constants

The constants a circuit-diffs dump carries beside its circuit (the `constants` object, one
variant per kind of circuit): the readers that decode the main circuits' variants, the shapes
the wrap circuit's builder takes them in, and the wrap-circuit dumps by name. The dump
comparison builds the circuits from them, and the tag-dump check reads the same variants out of
the prove tests' dumps.

## Main definitions

* `PicklesFixture.WrapMainConsts`, `PicklesFixture.wrapMainOf`: a wrap main's constants and
  their reader; `PicklesFixture.WrapMainShapes`, `PicklesFixture.wrapMainShapesOf`: the same
  at the shapes `Pickles.wrapMainCircuit` takes them in.
* `PicklesFixture.StepMainConsts`, `PicklesFixture.stepMainOf`: a step main's.
* `PicklesFixture.wrapMainDumps`: the wrap-circuit dumps with their shapes.
-/

namespace PicklesFixture

open Lean Snarky Snarky.Kimchi Kimchi CompElliptic.Fields.Pasta

/-- Where the circuit-diffs results live (workspace-relative default, env override). -/
def resultsDir : IO System.FilePath := do
  match (← IO.getEnv "KIMCHI_PS_RESULTS_DIR") with
  | some d => return d
  | none =>
    return ".." / "packages" / "pickles-circuit-diffs" / "circuits" / "results"

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
  lagrange : Array (List (Vector XhatWrapCurve.Point nc))
  /-- The blinding base. -/
  h : XhatWrapCurve.Point
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
    FixtureKit.parseArrOf (chunksOf XhatWrapCurve nc) (← b.getObjVal? "lagrange")
  unless (tables.map (·.size)).toList.eraseDups.length ≤ 1 do
    throw "the branches' tables differ in length"
  pure
    { stepWidths := (← branches.mapM fun b => do (← b.getObjVal? "width").getNat?).toList
      keys := (← branches.mapM fun b => do
        checkedKey Bulletproof.IpaVesta.curve Pickles.StepIPARounds nc
          (← b.getObjVal? "key")).toList
      lagrange := (List.transpose (tables.toList.map (·.toList))).toArray
      h := ← Bulletproof.Fixture.parsePt XhatWrapCurve (← c.getObjVal? "h")
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
def wrapMainTables? (bp nc m : ℕ) (lagrange : Array (List (Vector XhatWrapCurve.Point nc))) :
    Option (Vector (Vector (Vector XhatWrapCurve.Point nc) m) (bp + 1)) :=
  if h : lagrange.size = m ∧ ∀ row ∈ lagrange.toList, row.length = bp + 1 then
    some (Vector.ofFn fun b => Vector.ofFn fun i =>
      (lagrange[i.val]'(by omega))[b.val]'(by
        rw [h.2 _ (Array.getElem_mem_toList _)]
        exact b.2))
  else none

/-- A wrap main's constants at the shapes `Pickles.wrapMainCircuit` takes them in: `bp + 1`
branches of at most `mpv` slots, `mpv` stack heights of at most `MaxProofsVerified`, a pin per
branch and slot, `bp + 1` step keys, and a table of one base per packed statement cell per
branch. -/
structure WrapMainShapes (bp mpv nc : ℕ) where
  /-- Each branch's slot count. -/
  widths : Vector (Fin (mpv + 1)) (bp + 1)
  /-- Each branch's step key. -/
  keys : Vector (Kimchi.Verifier.KimchiVK Bulletproof.IpaVesta.curve nc) (bp + 1)
  /-- Each key declares this tag's statement size and its branch's slot count. -/
  layouts : ∀ b : Fin (bp + 1), Pickles.StepKeyLayout keys[b] mpv (widths[b] : ℕ)
  /-- Each slot's challenge-stack height. -/
  slotWidths : Vector (Fin (Pickles.MaxProofsVerified + 1)) mpv
  /-- Each slot's wrap domain index per branch, `none` when side-loaded. -/
  pins : Vector (Vector (Option ℕ) (bp + 1)) mpv
  /-- Each branch's Lagrange bases, one per packed statement cell. -/
  tables : Vector (Vector (Vector XhatWrapCurve.Point nc)
    (CircuitType.size Fp (Pickles.StepStatement (Pickles.UnfVal 15) Fp mpv))) (bp + 1)

/-- A wrap main's constants at its shapes, when they have them. -/
def wrapMainShapesOf (bp mpv nc : ℕ) (k : WrapMainConsts nc) :
    Except String (WrapMainShapes bp mpv nc) := do
  let some widths := wrapMainWidths? (bp + 1) mpv k.stepWidths
    | throw s!"slot counts {k.stepWidths} are not {bp + 1} ≤ {mpv}"
  let some keys := wrapMainKeys? bp k.keys
    | throw s!"{k.keys.length} step keys, not {bp + 1}"
  if hlayouts : ∀ b : Fin (bp + 1), Pickles.StepKeyLayout keys[b] mpv (widths[b] : ℕ) then
    let some slotWidths := wrapMainWidths? mpv Pickles.MaxProofsVerified k.slotWidths
      | throw s!"stack heights {k.slotWidths} are not {mpv} ≤ {Pickles.MaxProofsVerified}"
    let some pins := wrapMainPins? bp mpv k.pins
      | throw s!"pins {k.pins} are not {bp + 1} rows of {mpv}"
    let m := CircuitType.size Fp (Pickles.StepStatement (Pickles.UnfVal 15) Fp mpv)
    let some tables := wrapMainTables? bp nc m k.lagrange
      | throw (s!"Lagrange bases are not {m} rows of {bp + 1}: " ++
          s!"{k.lagrange.size} rows of lengths {(k.lagrange.toList.map List.length).eraseDups}")
    return { widths, keys, layouts := hlayouts, slotWidths, pins, tables }
  else throw "a step key's public-input or old-accumulator count differs from its circuit layout"

/-- The Lagrange table at a step domain: the first branch's at it, the first branch's when no
branch has it (such a domain is never read). -/
def WrapMainShapes.lagrange {bp mpv nc : ℕ} (sh : WrapMainShapes bp mpv nc) (l : ℕ) :
    Vector (Vector XhatWrapCurve.Point nc)
      (CircuitType.size Fp (Pickles.StepStatement (Pickles.UnfVal 15) Fp mpv)) :=
  sh.tables[(Pickles.stepDomainLog2s sh.keys).toList.idxOf l]?.getD sh.tables[0]

/-- The `wrap_main_*` dumps with their branch, slot and chunk counts. -/
def wrapMainDumps : List (String × ℕ × ℕ × ℕ) :=
  [ ("wrap_main_circuit", 0, 1, 1),
    ("wrap_main_side_loaded_main_circuit", 0, 1, 1),
    ("wrap_main_n2_circuit", 0, 2, 1),
    ("wrap_main_add_one_return_circuit", 0, 0, 1),
    ("chunks2_wrap_main_circuit", 0, 0, 2),
    ("wrap_main_tree_proof_return_circuit", 0, 2, 1),
    ("wrap_main_two_phase_chain_circuit", 1, 1, 1) ]

/-- One slot of a step circuit's constants, including its own step chunk count. -/
structure StepSlotConsts where
  /-- The chunk count of the step proofs this slot finalizes. -/
  chunks : ℕ
  /-- Whether the slot verifies this tag's proofs rather than another's. -/
  self : Bool
  /-- The wrap key the slot verifies against, checked at the wrap SRS (`checkedKey`). -/
  key : Kimchi.Verifier.KimchiVK Bulletproof.IpaPallas.curve 1
  /-- The key declares the full wrap statement and padded accumulator counts. -/
  layout : Pickles.WrapKeyLayout key
  /-- The slot's width, at most `MaxProofsVerified`. -/
  width : Fin (Pickles.MaxProofsVerified + 1)
  /-- Its candidate step domains. -/
  domains : Pickles.KnownDomains chunks
  /-- The Lagrange bases its public-input commitment reads, one per packed statement cell. -/
  lagrange : Pickles.SlotLagrange 1 Pickles.StepIPARounds

/-- A step circuit's constants: the blinding base, each slot's constants at its own chunk
count, and the shared candidate domains of its Self slots. -/
structure StepMainConsts (n : ℕ) where
  /-- The blinding base. -/
  h : XhatStepCurve.Point
  /-- Each slot's constants, in the rule's order. -/
  slots : Vector StepSlotConsts n
  /-- This compile's own step domains. -/
  ownDomains : List (Pickles.KnownDomain Fp)

/-- Each slot's step chunk count, in the rule's slot order. -/
def StepMainConsts.chunks {n : ℕ} (k : StepMainConsts n) (i : Fin n) : ℕ :=
  k.slots[i].chunks

/-- A slot's source: an external slot carries its checked wrap key's commitments, its Lagrange
bases and its candidate domains. -/
def StepSlotConsts.source (s : StepSlotConsts) :
    Pickles.SlotSource 1 Pickles.StepIPARounds :=
  if s.self then .self s.lagrange
  else .external s.key.comms s.lagrange s.width.val s.domains.list

/-- A slot's width is at most `MaxProofsVerified` when the tag's is. -/
theorem StepSlotConsts.width_le (s : StepSlotConsts) {w : ℕ}
    (hw : w ≤ Pickles.MaxProofsVerified) :
    s.source.width w ≤ Pickles.MaxProofsVerified := by
  unfold StepSlotConsts.source
  split
  · exact hw
  · exact Nat.le_of_lt_succ s.width.isLt

/-- A step main's constants (`stepMain`), with `n` slots at the tag's width `w`, each slot's step
proofs at its declared chunk count: a self slot's width must be `w`, and the self slots share
this compile's step chunk count and domains. Side-loaded slots are outside this corpus. -/
def stepMainOf (n w : ℕ) (j : Json) : Except String (StepMainConsts n) := do
  let c ← constantsOf "stepMain" j
  let domains (ncs : ℕ) (ls : List ℕ) : Except String (Pickles.KnownDomains ncs) := do
    let some d := Pickles.KnownDomains.ofList? ncs ls | throw s!"step domains {ls} are no domains"
    pure d
  let slot (j : Json) : Except String StepSlotConsts := do
    let chunks ← (← j.getObjVal? "numChunks").getNat?
    let wd ← (← j.getObjVal? "width").getNat?
    let some width := (if h : wd < Pickles.MaxProofsVerified + 1 then some ⟨wd, h⟩ else none)
      | throw s!"width {wd} above MaxProofsVerified"
    let self ← match ← (← j.getObjVal? "kind").getStr? with
      | "self" =>
        unless wd = w do throw s!"a self slot of width {wd} in a tag of width {w}"
        pure true
      | "external" => pure false
      | kind => throw s!"unsupported slot kind {kind}"
    let key ← checkedKey Bulletproof.IpaPallas.curve Pickles.WrapIPARounds 1
      (← j.getObjVal? "key")
    if hlayout : Pickles.WrapKeyLayout key then
      pure { chunks, self, width, key, layout := hlayout
             domains := ← domains chunks (← FixtureKit.parseArrOf (fun j => j.getNat?)
               (← j.getObjVal? "domains")).toList
             lagrange := ← do
               let pts ← FixtureKit.parseArrOf (chunksOf XhatStepCurve 1)
                 (← j.getObjVal? "lagrange")
               let m := CircuitType.size Fp
                 (Pickles.PackedWrapStatement Pickles.StepIPARounds (Type1 Fp) Fp)
               if h : pts.size = m then pure ⟨pts, h⟩
               else throw s!"{pts.size} Lagrange bases, expected {m}" }
    else throw "a wrap key's public-input or old-accumulator count differs from its circuit layout"
  let slots ← FixtureKit.parseArrOf slot (← c.getObjVal? "slots")
  let some slots := (if h : slots.size = n then some (⟨slots, h⟩ : Vector _ n) else none)
    | throw s!"{slots.size} slots, expected {n}"
  let own := slots.toList.filter (·.self)
  let ownDomains ← match own with
    | [] => pure []
    | first :: rest =>
      unless rest.all (fun s =>
          s.chunks == first.chunks && s.domains.log2s == first.domains.log2s) do
        throw "self slots disagree on step chunk counts or domains"
      pure first.domains.list
  pure { h := ← Bulletproof.Fixture.parsePt XhatStepCurve (← c.getObjVal? "h"), slots, ownDomains }

/-- The dummy `sg_old` (PS `dummyWrapSg`), a point of the wrap proofs' curve. -/
def dummyWrapSgPt : Bulletproof.IpaPallas.curve.Point :=
  ⟨8063668238751197448664615329057427953229339439010717262869116690340613895496,
   2694491010813221541025626495812026140144933943906714931997499229912601205355,
   Or.inl (by decide)⟩

/-- The unfinalized entry padding the statement of a rule verifying no proofs (PS
`Dummy.baseCaseDummies { maxProofsVerified: 0 }`), at the wrap circuit's 15 rounds. -/
def dummyUnfN0 : Pickles.UnfVal 15 :=
  let sf (x : Fp) : Type2 (SplitField Fp Bool) := ⟨⟨x, true⟩⟩
  { cip := sf 10733637291412775405099085909742784243308064411873129175045178535313137524648
    b := sf 12005690365207186104828106725404484059974178413747419366262848828074459318671
    zetaToSrsLength :=
      sf 7826322391957027530016555805456769916486940393993472644155614648591765317494
    zetaToDomainSize :=
      sf 7826322391957027530016555805456769916486940393993472644155614648591765317494
    perm := sf 11720302720943076563339347688798825215517484960467558296985186859509025408993
    spongeDigest := 6277101735386680764176071790128604879584176795969512275969
    beta := 152341587173296550850923210387509020609
    gamma := 239197809892340837260422696781281951881
    alpha := 236185100527557585826515066705725312805
    zeta := 260445934505999659442479615932459762956
    xi := 18446744073709551617
    bulletproofChallenges := #v[161621990286339861369413299182831583087,
      294397517322790754025793051151124957079, 10455894452509500744048069718178570187,
      224814704134265519234947971901913897491, 330128161163701260858569889180053145483,
      102493828312258879830323023652412497031, 215326567078568560823705023668614618897,
      120359744259981153545389569741970563149, 221360828059242236386510005024107555656,
      257571901803291014519404945390244881518, 209025140278641004900167089918138330057,
      201591733645229477386800950847198767694, 318881875946480425567146057353930829431,
      198219236102229943192453714701868046676, 122049445183499159876948789073679959987]
    shouldFinalize := false }

end PicklesFixture
