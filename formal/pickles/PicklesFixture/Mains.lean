import Pickles.StepMain
import Pickles.WrapMain
import PicklesFixture.Constants
import PicklesFixture.Fop

/-!
# The main circuits at a dump's constants

`Pickles.stepMainCircuit` and `Pickles.wrapMainCircuit` configured from the constants a main
circuit's dump carries (`PicklesFixture.StepMainConsts`, `PicklesFixture.WrapMainConsts`), as
the capstones state them, with inert advice: the circuits a constraint-system comparison
compiles.
-/

namespace PicklesFixture

open Snarky Snarky.Kimchi Kimchi CompElliptic.Fields.Pasta

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

open Pickles in
/-- A `step_main_*` circuit: `Pickles.stepMainCircuit` at `n` slots and the tag's width `w`, as
`stepWrap_kimchiVerify` states it: each slot's source and the blinding `h` from the dump's
constants, the step proofs' finalize constants (`FopParams.of`), this compile's known domains,
over the transcribed `rule`, the statement padded with `dummyUnf`. Its output alone, the cells
dropped: compiled, that is the theorem's `compileWith` system (`Snarky.compileWith_constraints`).
The advice is inert: the comparison is on the constraint system. -/
def stepMainDumpCircuit {n : ℕ} {inVal inVar : Type} [CircuitType Fp inVal inVar]
    [CheckedType Fp C inVal inVar] {outVal outVar : Type} [CircuitType Fp outVal outVar]
    {ss : Fin n → ℕ} {ncs : ℕ} (w : ℕ) (hw : w ≤ MaxProofsVerified) (k : StepMainConsts n ncs)
    (dummyUnf : UnfVal 15)
    (rule : inVar → CircuitM Fp C (((i : Fin n) → PrevStatement (ss i)) × outVar))
    (adv : StepMainAdvice n w (SlotSource.widths w fun i => k.slots[i].source) 1 ncs 15
      StepIPARounds inVal :=
      ⟨AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice",
        AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice"⟩) :
    Unit → CircuitM Fp C (StepStatement (UnfVar 15) (FVar Fp) w) := fun u =>
  Prod.fst <$> stepMainCircuit (n := n) (w := w) (ncw := 1) (ncs := ncs) (k := 15)
    (ks := StepIPARounds) (inVal := inVal) (outVal := outVal)
    (fun i => k.slots[i].source) (fun i => k.slots[i].width_le hw) k.h
    (PicklesFixture.fopStepParams ncs) k.ownDomains.list (constPt dummyWrapSgPt) dummyUnf rule
    adv u

/-- A `wrap_main_*` circuit: `Pickles.wrapMainCircuit` at `bp + 1` branches, `mpv` slots and
`nc` step chunks, as `wrapStep_kimchiVerify` states it: the branches' domains and key cells are
their checked step keys' (`stepDomainLog2s`, `stepKeyCells`), and a domain's Lagrange table is
the first branch's at it (a domain no branch has is never read). Its output alone, the cells
dropped: compiled, that is the theorem's `compileWith` system
(`Snarky.compileWith_constraints`). -/
def wrapMainDumpCircuit (bp mpv nc : ℕ) (k : WrapMainConsts nc)
    (widths : Vector (Fin (mpv + 1)) (bp + 1))
    (keys : Vector (Kimchi.Verifier.KimchiVK Bulletproof.IpaVesta.curve nc) (bp + 1))
    (slotWidths : Vector (Fin (Pickles.MaxProofsVerified + 1)) mpv)
    (pins : Vector (Vector (Option ℕ) (bp + 1)) mpv)
    (tables : Vector (Vector (Vector XhatWrapCurve.Point nc)
      (CircuitType.size Fp (Pickles.StepStatement (Pickles.UnfVal 15) Fp mpv))) (bp + 1))
    (advW : Pickles.WrapMainAdvice mpv nc 15 16 (slotWidths.map Fin.val).sum)
    (stmt : Pickles.StatementPacked 16 (Type1 (FVar Fq)) (FVar Fq)) :
    CircuitM Fq Cq Unit :=
  Prod.fst <$> Pickles.wrapMainCircuit (branches := bp + 1) (mpv := mpv) (ncStep := nc) (k := 15)
    (ks := 16)
    fopWrapParams widths (Pickles.stepDomainLog2s keys) (Pickles.stepKeyCells keys)
    pins (fun l => tables[(Pickles.stepDomainLog2s keys).toList.idxOf l]?.getD tables[0])
    k.h k.dummy slotWidths advW stmt

/-- A `wrap_main_*` circuit at a dump's constants, with its tables, the shapes the circuit takes
them in checked: `bp + 1` branches of at most `mpv` slots, `mpv` stack heights of at most
`MaxProofsVerified`, a pin per branch and slot, `bp + 1` step keys, and a table of one base per
packed statement cell per branch. Its advice is `adv` at the checked slot widths, inert
unless given. -/
def wrapMainCircuitOf (bp mpv nc : ℕ) (k : WrapMainConsts nc)
    (adv : (slotWidths : Vector (Fin (Pickles.MaxProofsVerified + 1)) mpv) →
      Pickles.WrapMainAdvice mpv nc 15 16 (slotWidths.map Fin.val).sum := fun _ =>
      ⟨AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice",
        AsProver.throw "advice", AsProver.throw "advice", AsProver.throw "advice",
        AsProver.throw "advice", AsProver.throw "advice"⟩) :
    Except String
      ((Pickles.StatementPacked 16 (Type1 (FVar Fq)) (FVar Fq) → CircuitM Fq Cq Unit) ×
        Vector (Vector (Vector XhatWrapCurve.Point nc)
          (CircuitType.size Fp (Pickles.StepStatement (Pickles.UnfVal 15) Fp mpv))) (bp + 1)) := do
  let some widths := wrapMainWidths? (bp + 1) mpv k.stepWidths
    | throw s!"slot counts {k.stepWidths} are not {bp + 1} ≤ {mpv}"
  let some keys := wrapMainKeys? bp k.keys
    | throw s!"{k.keys.length} step keys, not {bp + 1}"
  let some slotWidths := wrapMainWidths? mpv Pickles.MaxProofsVerified k.slotWidths
    | throw s!"stack heights {k.slotWidths} are not {mpv} ≤ {Pickles.MaxProofsVerified}"
  let some pins := wrapMainPins? bp mpv k.pins
    | throw s!"pins {k.pins} are not {bp + 1} rows of {mpv}"
  let m := CircuitType.size Fp (Pickles.StepStatement (Pickles.UnfVal 15) Fp mpv)
  let some tables := wrapMainTables? bp nc m k.lagrange
    | throw (s!"Lagrange bases are not {m} rows of {bp + 1}: " ++
        s!"{k.lagrange.size} rows of lengths {(k.lagrange.toList.map List.length).eraseDups}")
  return (wrapMainDumpCircuit bp mpv nc k widths keys slotWidths pins tables (adv slotWidths),
    tables)

end PicklesFixture
