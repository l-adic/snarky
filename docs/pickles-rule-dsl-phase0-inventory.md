# Pickles rule DSL — Phase 0 inventory

Read-only inventory for `pickles-rule-dsl-simplification-plan.md` §5 Phase 0.
Measured 2026-09-14 on `formal/verify-proof` (8546b16f). Line numbers refer
to that tree.

Classification key for the "verdict" column:

- **runtime** — per-application; becomes a plain `Int` / value / `Array` in Phase 1–2.
- **type** — protocol constant fixed by kimchi or pickles; stays type-level.
- **derived** — a pure function of other rows; disappears with them.
- **OQ-n** — needs something not in `(tag, kind, stmtSize)` per slot + `mpv` + branch count; see §6.

## 1. `Prove/Compile.purs` (4193 lines)

Classes declared in this file, with line ranges:

| Class | Decl | Instances | Verdict |
|---|---|---|---|
| `ConvertSlots` | 461–462 | identity 464–465; `NoSlots → dst` 467–472 (only two shapes; `Slots1 1 → Slots2 1 2` unimplemented, 458–460) | runtime: `padTo mpvMax dummy` |
| `PadProveDataMpv` | 481–485 | identity 490–491; general front-pad 499–531 | runtime: `replicate (mpvMax − mpv) dummy <> real` on 8 vectors |
| `CompilableSpec` | 544–632 | 0 slots 638–719; Compiled cons 727–1427; SideLoaded cons 1438–2115 | runtime: three functions over `Array Slot` |
| `IntMax`, `IntMaxOrd` | 2150–2159 | LT/EQ/GT 2155–2157 | derived: `max` |
| `MaxOfRulesMpvs` | 2174 | Nil 2176; Cons 2178–2182 | derived: `maximum` |
| `CompilableRulesSpec` | 2292–2390 | Nil 2394–2415; Cons 2422–2599 | runtime: `traverse` over rules |
| `CompilableRulesSpecShape` | 2613–2736 | Nil 2860–2880; Cons 2882–3182 (~60-constraint context) | runtime: same traverse |

`RulesSpec` (2137) is a kind; `RulesNil`/`RulesCons` (2142/2147) are foreign data of that kind. Self vs External is **not** an instance split: both are the Compiled instance, discriminated at runtime by `SlotWrapKey = Self | External ProverVKs` (254–256).

`compileMulti` (3978–4054, body 4055–4193): 31 type variables (6 visible), 32 constraints, 6 `Reflectable` (`wrapVkChunks`, `branches`, `mpvMax`, `stepChunks`, `tCommLen`, `nonSgBases`), 4 `Compare`, 16 `Add`/`Mul`.

### 1.1 `CompilableSpec` methods

| Method | Computes | Depends on | Verdict |
|---|---|---|---|
| `shapeCompileData` (579–587; 639–664 / 778–868 / 1496–1591) | `srsData` per-slot vectors: `perSlotLagrangeAt` (lagrange at slot wrap domain, chunked at `wrapVkChunks`), `perSlotFopDomainLog2s :: Vector nd Int`, `perSlotFopZkRows`, `perSlotVkBlueprints` (`Shared` for Self, `Const` of external wrap-VK comms, per-domain tables for SideLoaded); `wrapDomainLog2 = override ?? table mpv`; `dummySg` | kind (runtime `SlotWrapKey`); outer `mpv` (`Reflectable`, 737/1448); side-loaded bound `mpvMax` (1446); `slotVkChunks` (736/1447); `wrapVkChunks` (584, pinned `@1` by callers); `nd` = branch count (582–583); `cfg.stepNumChunks`; `cfg.wrapDomainOverride`; External `ProverVKs` value; `wrapDomainLog2ForProofsVerified` table 13/14/15; `zkRowsForNumChunks`. **stmtSize never used.** | runtime; OQ-1 (ProverVKs), OQ-2 (external multi-branch domains), OQ-3 (nd per slot) |
| `mkStepAdvice` (596–619; 666–707 / 870–1158 / 1605–1868) | `StepAdvice` fields `perProofSlotsCarrier`, `publicUnfinalizedProofs`, `messagesForNextWrapProof`, `kimchiPrevChallenges`, `prevAppStates`, `sideloadedVKs`; plus `challengePolynomialCommitments`, `baseCaseWrapPublicInputs`. Per slot: `slotParams` by Self/External dispatch (881–904), then `BasePrev` (dummy PI via `dummyWrapTockPublicInput @n`, `mustVerify = false`) or `InductivePrev` (real proof + tag, `mustVerify = true`), then `buildSlotAdvice @n @slotVkChunks` | slot `n` (735, `Compare n 3 LT` 743, `Add slotPad n PaddedLength` 739); side-loaded `mpvMax` (1446); kind; `cfg.stepNumChunks`; this branch's realized `stepCR.proverIndex` domain (887, Self only); `wrapCR.verifierIndex`; External `ProverVKs`; runtime side-loaded bundle (`actualWrapDomainSize`, 1613–1621); prev statement **value** (`CircuitType`, 744–745); `Tag.verifier` + existential `CompiledProof.widthData` | runtime; OQ-1, OQ-4 (own domain post pre-pass), OQ-5 (statement value, not size), OQ-6 (per-proof runtime data) |
| `shapeProveData` (626–632; 709–719 / 1160–1427 / 1876–2115) | nine `Vector mpv` fields incl. `prevWrapDomainIndices = F (slotWrapDomainLog2 − 13)`, `slotsValue`; Type1→Type2 unfinalized coercion; endo-expanded bp-chals; `proofOraclesRec` on the dummy or real wrap proof | slot `n` / `mpvMax`; `slotPad = 2 − n` (`Vector.drop @slotPad` 1383/2075); kind; `sideInfo` from `mkStepAdvice` (cross-method coupling, 362–373); `CompiledProof.widthData`; `WrapIPARounds`, `StepIPARounds`, `PaddedLength` | runtime; OQ-6 |

### 1.2 `CompilableRulesSpec` / `CompilableRulesSpecShape` methods

| Method | Computes | Depends on | Verdict |
|---|---|---|---|
| `branchCount` (2336; 2411 / 2496–2513) | runtime branch count, duplicating `Reflectable branches` (comment 2331–2335) | `rs` length | derived: `length rules` |
| `extractStepCompileFns` / `extractStepProveFns` (2346 / 2369) | tuple chain of `RuleEntry` closures | `rulesCarrier` | runtime: `map` |
| `runStepCompiles` (2352–2356; 2533–2554) | per-branch `StepCompileResult` | per-branch `StepProveContext`, `AdviceHandler r` | runtime: `traverse` |
| `buildWrapPerBranchVec` (2384–2390; 2555–2580) | `Vector branches { mpv, stepDomainLog2, stepVK }`; `mpv` from `reflectType @ruleMpv` (2558), domain from realized `proverIndex` (2559) | per-rule `ruleMpv` (2452); realized prover index | runtime |
| `prePassDomainLog2s` (2656–2663; 3053–3078) | per-branch realized step-domain log2 from a placeholder ctx (`roughDomainsLog2 = 20`, `Constants.purs:29`) and gate counting | `CompileMultiConfig`, declared `stepChunks :: Int`, each rule's `slotVKs` | runtime; OQ-4 |
| `runMultiCompile` (2671–2678; 3079–3104) | per-branch `StepCompileResult` with real log2s | same + real `Vector topBranches Int` | runtime |
| `buildBranchProvers` (2701–2736; 3105–3182) | `BranchProver` closures capturing `branchIdx`, `headStepCR`, `headLog2`; calls `runMultiProverBody @mpvMax @slotsMax @mpvPad` | `topBranches` (2949), `mpvMax`/`slotsMax`/`mpvPad` (2932–2946), `stepChunks` chain (2705–2723); method-level `vecLen` is free, not tied to `branches` (OQ-14) | runtime |

Cons-instance type arithmetic (2435–2457): `outputSize = mpvMax·32 + 1 + mpvMax` (`Mul mpvMax UnfinalizedFieldCount`, `Add`, `Add`) — see OQ-7.

### 1.3 Types

| Name | Where | Note |
|---|---|---|
| `Tag stmt mpv` | 213–219 | `{ unique :: Unique, verifier :: Verifier }`, phantom `(stmt, mpv)` |
| `SomeTag` | nowhere | proposed by the plan only |
| `PrevSlot` / `BasePrev` / `InductivePrev` | 297–302 | `InductivePrev (CompiledProof n stmt) (Tag stmt n)` |
| `SlotWrapKey`, `ProverVKs` | 254–256, 222–231 | `ProverVKs = { stepCompileResult, wrapCompileResult, wrapDomainLog2, stepNumChunks }` |
| `Slot k n nc stmt` | `Pickles/Slots.purs:29–55` | `(kind, mpv-bound, num_chunks, stmt)`; `SlotKind = Compiled \| SideLoaded` only |
| `RuleEntry` (12 params), `BranchProver` | 3197–3244, 2205–2212 | |

## 2. `Step/Main.purs` (1280 lines)

| Item | Lines | Computes | Depends on | Verdict |
|---|---|---|---|---|
| `BuildSlotVkSources` Nil | 194–195 | `pure unit` | — | runtime: `[]` |
| `BuildSlotVkSources` Compiled cons | 197–215 | blueprint → `ConstVk` / `SharedExistsVk`; no `exists`; consumed 1042–1066 | kind; blueprint (Const = External, Shared = Self); slot `nc` **unified with** `wrapVkChunks` in the head (202/205/207) | runtime; OQ-8 (nc ≡ wrapVkChunks) |
| `BuildSlotVkSources` SideLoaded cons | 217–237 | `exists` the runtime side-loaded VK, bundles per-domain lagrange tables → `SideloadedExistsVk`; consumed 1067–1082 | kind; uniform `cell` type; `HasSideLoadedVk`, `CheckedType` on `SLVK.VerificationKey wrapVkChunks` | runtime; OQ-9 (uniform `cell`, differs compile vs solve) |
| `IntEq` | 330–333 | type-level equality oracle | `len`, `mpvMax` | derived: `==` |
| `MpvPaddingDispatch` / `MpvPadding` | 335–367 | `Vector mpvPad a -> Vector len a -> Vector mpvMax a` (identity when equal) | `mpvPad + len = mpvMax` | runtime: `replicate <> ` |
| `mpvFrontPad` | 384–404 | dummy-thunk variant; `unsafeCoerce` at `mpvPad = 0` (396) | reflects `mpvPad` (394) | runtime |
| `n` (per-slot) | 466, 651 | never reflected here; shapes `Vector n` `prevChallenges`/`prevSgs`/`proofMask` | slot's `n` | runtime (per-slot `localMpv`); OQ-15 (466 possibly vestigial) |
| `stepChunks` (per-slot nc) | 464, 467, 650 | sizes `ChunkedCommitment stepChunks`, `Mul 7 stepChunks tCommLen` (468), VK comms | prev compile's `num_chunks` (= 1 in all prev-bearing fixtures) | **type** (protocol record inside IVP); OQ-8 |
| `mpvPad`, `mpvMax` | 387–388, 851–852; reflected 394, 404, 970 | width of PI-padded unfinalized + msgWrap vectors → `outputSize` (858–860) | `mpvMax − len` | runtime; OQ-7 (`outputSize` in the return type) |
| `nd` | 806–808 | shapes `perSlotFopDomainLog2s :: Vector len (Vector nd Int)` (274); one extra `equal`+`mul` per extra branch (1106–1112) | prev source's branch count, **one uniform `nd` for all slots** | runtime; OQ-3 |
| `len` | 825; reflected 1263 | `Vector len` carriers; `traverseStepSlotsAWithVk` walk; `hashMessagesForNextStepProof` unpadded length (1218–1226) | rule's prev count | runtime |
| `wrapVkChunks` | 220, 826; chain 832–846 | this compile's own wrap VK chunking; sizes `VerificationKey wrapVkChunks`, `LagrangeBaseLookup`, IVP base-count chain | kimchi `num_chunks_by_default = 1` | **type** |
| `pad = 2 − n` | 652–653, 850–853; `Vector.drop @pad` 681 | Wrap_hack sg_old front-padding and mask drop (669–681) | `PaddedLength = 2` (type), `n` | derived |
| `tCommLen`, `nonSgBases` | 834, 838–849 | 7·nc, 1 + 44·nc | `wrapVkChunks` | **type** |
| `StepIPARounds` | 1117 | 16 | — | **type** |

Other classes dispatched on: `StepSlotsCarrier` (814–823; heterogeneous per-slot witness carrier, eliminated by `traverseStepSlotsAWithVk` 1011), `HasSideLoadedVk`, `CircuitType`, `CheckedType`, `Add`/`Mul`/`Compare`.

Line budget: shape machinery ≈ 370 (29%): 119–238, 303–404, 783–789, 805–860, 1042–1091, 1152–1158, 968–973, 1258–1268. Circuit body + value plumbing ≈ 710 (55%): 293–301, 406–765, 871–1041, 1092–1151, 1159–1257, 1269–1279. The per-slot loop 1002–1166 (ivp gated by `mustVerify` at 1147/1158), message hashes 1168–1246, and statement assembly 1248–1279 are the untouched body; four `unsafeCoerce` bridges (1065, 1075, 1091, 1158) exist only because the head unification of OQ-8 does not propagate into the case body.

## 3. `Prove/Step.purs` (2211 lines)

No classes declared. `StepRule` 1465–1473 (doc 1422–1464), `StepRuleAt` 1485–1492 (doc 1475–1484). Note the doc talks about pinning a monad `m` but the parameter is an advice row `r :: Row (Type -> Type)` (OQ-16, doc drift).

| Index / class | Constraint lines | Reflected | Computes | Verdict |
|---|---|---|---|---|
| `len` | 231, 1680, 1891, 2038 | **261** (`mrw` → dummies, wrap domain, masks 313–316), **1783** (`prevChallengesCount` into `makeConstraintSystemWithPrevChallenges`) | slot count; 1783 bakes it into the **kimchi CS** | runtime; OQ-10 (must be known before CS construction) |
| `n` (per-slot) | 372, 537, 975 | 678 (`revOnesVector` → dummy branch_data); `replicate @n` 653, 1149 | per-slot width | runtime |
| `slotVkChunks` | 373, 976, 1685, 1896, 2043 | **1983** (`zkRowsForNumChunks` → rows → `ceilLog2` = own step-domain log2); `expandProof @slotVkChunks` 1187, `vestaProofCommitments` 1289 | prev's commitment chunking, zk_rows | **type** today; OQ-8 |
| `wrapVkChunks` / `WrapVkChunks = 1` | 232, 464, 1661, 1872, 2019; 638, 997, 1161 | never | wrap VK comm chunking in advice; VK in `hash_messages_for_next_step_proof` | **type** (pin note 1501–1509 is convention only, OQ-17) |
| `pad = 2 − n` | 977–978, 1681, 1892, 2039 | `Vector.drop @pad` 1002, 1005, 1388, 1391 | strip Wrap_hack padding | derived |
| `mpvPad`, `mpvMax`, `nd` | 1682–1684, 1893–1895, 2040–2042 | never; threaded to `stepMain` 1763–1764, 1966–1967, 2114–2115 | | runtime; OQ-3, OQ-7 |
| `outputSize` | 1686/1691–1693, 1897, 2044 | `Proxy @(Vector outputSize (F StepField))` 1754, 1957, 2103 | circuit public-output width | OQ-7 |
| `Compare n 3 LT` | 538 | — | mpv ≤ 2 cap | **type** today; lifted to 6 by mina #19235 (§5) |
| `BuildSlotVkSources` | 1659, 1870, 2017 | `cell` = `SLVK.VerificationKey …` at compile, `SideloadBundle.Bundle …` at solve | | OQ-9 |
| `StepSlotsCarrier` (value + var, twice per runner), `SlotStatementsCarrier`, `MkUnitVkCarrier` (duplicated 1660/1720, 1871/1934), `SideloadedVKsCarrier`, `MpvPadding` | 233–243, 1699–1720, 1910–1934, 2057–2078 | | per-slot carriers derived from `prevsSpec` | runtime |

Line budget: three runner signatures 1645–1724, 1857–1938, 2007–2084 ≈ 216 constraint lines; builder signatures ≈ 40; carrier/type decls ≈ 45. Proving logic on values ≈ 1100 (983–1416, 1725–1839, 1939–1992, 2085–2211).

## 4. `Wrap/Main.purs` (951) + `Wrap/Slots.purs` (197) + `Wrap/SlotsFromSpec.purs` (39)

| Item | Lines | Computes | Depends on | Verdict |
|---|---|---|---|---|
| `SlotsFromSpec` | 18–39; use Main 917 | nothing at runtime (`slotsProxy` = `Proxy`); grounds `slots = Product (Vector n₀) (… Const Unit)` | per-slot `n` only; kind, `slotVkChunks`, `stmt` bound and **dropped** (31/37); Compiled and SideLoaded instances are byte-identical | runtime: `map _.localMpv slots` |
| `PadSlots` | Slots 111–175 | `slotWidthsOf :: Vector mpv Int`, `padAllSlots` (front-pad each slot's bp-chal stack to `PaddedLength = 2`), `replicateSlots` | per-slot `w` (159), `pad = 2 − w` (160–161), slot count (163–164) | runtime; `PaddedLength` stays type |
| `wrapMain` constraint block | 373–428 (56 lines) | | `PadSlots slots mpv` 381; `stepChunks` 382 with `tCommLen = 7·nc`, `nonSgBases = 1 + 44·nc` chain 383–403; `branches` 415; `mpv` 416; `Compare mpv 3 LT` 418; `totalBases = mpv + nonSgBases` 423–424 | `stepChunks` chain **type**; `branches`, `mpv` runtime; `mpv < 3` protocol cap (see §5) |
| `wrapMainForPrevs` | 907–951 | repeats the block with `SlotsFromSpec` prepended; body is line 951; cannot compose across rules (907–913) | | delete |
| `WrapMainConfig branches stepChunks` | 116–160 | `stepWidths`, `domainLog2s`, `stepKeys :: Vector branches (StepVK stepChunks)`, `lagrangeAt`, `perBranchLagrangeAt :: Maybe …` (156–157, runtime switch selecting two circuits 828–869), `blindingH`, `allPossibleDomainLog2s :: Vector 3 (Finite 16)` | branch count, `stepChunks` | runtime (`Array`); OQ-11 (one `stepChunks` for all branches) |
| `Pseudo.oneHotVector @branches`, `choose whichBranch …`, `replicate @branches` | 475–479, 497–499, 541, 833 | branch selection | branch count | runtime |
| `Vector mpv` loops: `maskVals` 486–495, Pseudo-domain loop 622, FOP loop 643, msg-hash loop 678–679, `sgOldMask` 882, `PackedStepPublicInput` 760–767 | | per-slot work | mpv | runtime |
| `slotWidthsOf` → `Vector.index states (unsafeFinite @3 w)` | 666–667 | sponge-state table lookup by real width | `Vector 3` table (type) indexed by per-slot `w` (runtime) | mixed; fine at runtime with a bounds check |
| `branchDataMaskWidth = 2` | 505–511 | branch-data pack width | hard-coded, independent of `mpv` | **type** today; = `max 2 mpv` after #19235 (§5) |
| `Pseudo.oneHotVector @3`, `toDomain @16` | 628–632 | `num_possible_domains = 3`, `WrapIPARounds + 1` | protocol | **type** |
| `WrapIPARounds = 15`, `PaddedLength = 2`, `unsafeFinite @3/@2/@5/@7/@6` reads | 432–464, 543–552, 665 | statement projection, VK column comms | protocol | **type** |
| `sumMaskByBranchChunked` `Vector.generate` over `stepChunks` | 821–826 | | `stepChunks` | **type** |

Line budget: machinery ≈ 572 (Slots + SlotsFromSpec 236; Main headers 146; in-body slot/branch/chunk plumbing ≈ 190 incl. comments) vs untouched wrap body ≈ 475 (162–364, 429–467, 533–558, 575–619, 691–767, 870–905).

## 5. mina PR #19235 ("Add support for wider recursion", merged 2026-09-14)

The `mina` submodule (f2265df310, 2026-09-11) **predates** it. +2282/−483 over 60 files; pickles lives at `src/lib/crypto/pickles/`.

What changes: the "at most 2 previous proofs" cap becomes "at most 6" (4 for same-width self-recursive merges; 7+ would need chunking). Every width ≤ 2 encoding and circuit is designed to be unchanged, so **no digest in this repo moves**.

| Quantity | Before | After |
|---|---|---|
| `Proofs_verified.t` | `N0 \| N1 \| N2` | `private int`; `Stable.V2 = N0 \| N1 \| N2 \| N_other of int`; `to_stable_v1` raises for > 2 |
| branch-data mask width `w` | 2 | `max 2 mpv` (`Nat.Max_type`, `Obj.magic`-backed) |
| `Branch_data.length_in_bits` | 10 | `w + 8`; layout bits 0–1 = mask[0..1], 2–9 = domain_log2, 10.. = mask[2..] (constant-zero term at `w = 2`) |
| `Wrap_hack.padded_length n` | 2 | `max 2 n`; `pad_front`, `pad_challenges` (now a list), `pad_commitments`, dummy sponge index `padded_length − mpv` |
| wrap key `prev_challenges` | literal 2 | `padded_length Max_proofs_verified` |
| `wrap_domains` | 0→13, 1→14, 2→15 | 0→13, 1→14, 2..6→15, ≥7 fails |
| `step_main` trim bound | `Nat.N2.n` | `Vector.length branch_data.proofs_verified_mask` (per-slot `max 2 localMpv`) |
| `wrap_main` branch-data check | `extend_front_exn … N2` | `extend_front_exn … mask_width`; `finalize_other_proof` gets the actual padded count |
| `compile.ml` guard (new) | — | per prev slot, `max 2 w` must agree across branches, else "branches disagree on the proofs-verified width of previous-proof slot %d" |
| Side-loaded `Width.Max` | N2 | **unchanged** N2; `pad_proof` fails above it; one-hots stay 3 bits |
| Serialisation | — | new `Branch_data.V2`, `Proof.Base.Wrap.V4`, `Side_loaded.Verification_key.V3`, `Side_loaded.Proof.V4`; ledger VKs still write `Side_loaded_verification_key.Stable.V2` |

For the port: every new quantity is an integer function of `localMpv(tag)` and `mpv`: `w_slot = max 2 localMpv`, `w_self = max 2 mpv`, `length_in_bits = w + 8`, `prev_challenges = w_self`, `num_padding = w − n`. The three PS sites that hard-code the cap are `Compare n 3 LT` (Prove/Step 538), `Compare mpv 3 LT` (Wrap/Main 418, 944; Wrap/Verify 76, 116), `branchDataMaskWidth = 2` (Wrap/Main 511), plus `PaddedLength = 2` (`Pickles/Types.purs:90`) and `Vector 3` sponge/domain tables. None of these needs to move for Phases 1–3; they are the list to touch if wider recursion is ported later.

## 6. Open questions — rows needing something not in `(tag, kind, stmtSize) + mpv + branch count`

Grouped by whether they block Phase 1 or merely shape `Slot`.

### 6.1 Shape of `Slot` (resolve by adding a field; no design change)

| # | Need | Where | Resolution |
|---|---|---|---|
| OQ-1 | External slot imports a **compiled artifact**: `ProverVKs = { stepCompileResult.proverIndex, wrapCompileResult.verifierIndex, wrapDomainLog2, stepNumChunks }` | Compile 791–815, 843–846, 894–903, 1171, 1182 | `kind = External ProverVKs` carries the record (the plan's `External WrapVk` is too small) |
| OQ-3 | `nd` is one uniform type-level nat, but semantically the **per-slot** branch count of the slot's source. External sources are limited to single-branch (Compile 799–808) | Step/Main 274, 806–808, 1106–1112; Prove/Step 1511 | `Slot.sourceDomainLog2s :: Array Int` per slot; `nd` becomes `length` per slot |
| OQ-5 | `BasePrev` needs the **dummy statement value**, serialized via `CircuitType`; `stmtSize` is never read anywhere in the three files | Compile 919–944, 1147, 1650–1673 | `stmtSize` is not needed by the compiler; the slot needs the `CircuitType` dictionary (existential) and the prove call supplies the value |
| OQ-12 | wrap-side per-slot width `w` (= `localMpv` of the slot's tag) drives `PadSlots`, the sponge table index and (after #19235) the mask width | Wrap/Slots 159–164; Wrap/Main 666–667 | `Slot.localMpv :: Int` (already implicit in `Tag stmt mpv`; make it a field) |

### 6.2 Timing (available at compile time, but not from the spec)

| # | Need | Where | Resolution |
|---|---|---|---|
| OQ-4 | Self slot needs this compile's own **realized** step-domain log2; the pre-pass exists to obtain it | Compile 887, 3053–3055 | orchestrator already does pre-pass then real pass; unchanged |
| OQ-6 | `InductivePrev` needs `Tag.verifier.{stepEndo, stepZkRows, stepSrsLengthLog2, linearizationPoly}` and the existential `CompiledProof.widthData` | Compile 976–1088, 1300–1396, 1703–1809, 2005–2088 | prove-time data via `prevs`; unchanged |
| OQ-10 | `len` is reflected into `prevChallengesCount` for the **kimchi constraint system**, not only the circuit body | Prove/Step 1779–1785 | runtime `Int` known from `length slots` before CS construction; fine |
| OQ-11 | wrap circuit assumes **one** `stepChunks` for all branches (`stepKeys :: Vector branches (StepVK stepChunks)`); `slotVkChunks` cannot be honoured on the wrap side; `compileMulti` validates every branch's realized chunks equal the declared one (4079–4104) | Wrap/Main 136, 374, 382; Compile 4087–4104 | keep: chunk counts are out of scope (plan §3.3) |

### 6.3 Type-level residue that survives Phases 1–3

| # | Need | Where | Resolution |
|---|---|---|---|
| OQ-7 | `outputSize = 32·mpvMax + 1 + mpvMax` is the circuit's **return type** `Vector outputSize` and the `Proxy` handed to `compile`/`makeSolver'` | Step/Main 858–860, 870, 1276–1279; Prove/Step 1754, 1957, 2103; Compile 2449–2451 | either an existential over `outputSize` at the three call sites or a runtime-length output type; decide at Phase 2 |
| OQ-8 | `slotVkChunks` is documented as the prev's **step** chunks (`Slots.purs:39–50`) but used as the slot's **wrap-VK** chunk count, and `BuildSlotVkSources` unifies it with `wrapVkChunks` in the instance head; four `unsafeCoerce` bridges exist for this | Step/Main 172–179, 202–231, 1049–1091, 1152–1158; Compile 736, 1447, 1538–1540 | both are 1 in every fixture; pin one name and one meaning in Phase 0 doc, leave type-level (out of scope) |
| OQ-9 | `cell` of `BuildSlotVkSources` is uniform across slots and instantiated differently at compile vs solve | Step/Main 180–186, 217–231; Prove/Step 1659, 1870, 2017 | disappears with the class; the runtime `map` takes the cell as a plain argument |
| OQ-13 | `slotsMax` is a free class parameter the user supplies as `@slots`; no `SlotsOfRulesMpvs`; `ConvertSlots` covers only `NoSlots → dst` | Compile 2318, 2628, 3995, 4031, 458–472 | disappears: `slotsMax = padTo mpvMax` |

### 6.4 Housekeeping found on the way (not blockers)

| # | Item | Where |
|---|---|---|
| OQ-14 | `buildBranchProvers` method-level `vecLen` is not unified with `branches` | Compile 2702–2732 |
| OQ-15 | `Reflectable n`, `Reflectable stepChunks` on `allocatePerProofWitness` and `Reflectable nd` on `stepMain` appear unused in the bodies | Step/Main 463–470, 808 |
| OQ-16 | `StepRuleAt` doc says "pinned to a concrete `m`"; the parameter is an advice row `r` | Prove/Step 1475–1492 |
| OQ-17 | `wrapVkChunks = 1` pin is convention at call sites, not enforced by `StepProveContext` | Prove/Step 1501–1509, 2019 |
| OQ-18 | `bcdMax = baseCaseDummies { maxProofsVerified: 0 }` hard-codes 0, not `mpvMax`, with an `-- EXPERIMENT:` comment on Ro-stream alignment | Compile 3657–3674 |
| OQ-19 | `msgStep` index uses literal `32` while the type chain uses `UnfinalizedFieldCount` | Compile 3846–3851 |
| OQ-20 | `padDummies.dummyPrevWrapDomainIdx = F one` and the `− 13` offsets encode the `[13,14,15]` table | Compile 3729–3735, 1418, 2106 |
| OQ-21 | `MkUnitVkCarrier` constraint listed twice in two runners | Prove/Step 1660/1720, 1871/1934 |
| OQ-22 | `Wrap/MessageHash.purs:85–86` doc says index by `MaxProofsVerified − n`; code indexes by real `n` | Wrap/MessageHash 85–86, 104–106 |
| OQ-23 | Slot widths > 2 and slot counts > 2 are unbounded in `SlotsFromSpec`; failure surfaces late as an unsolved `Compare` or negative `pad` | Wrap/Slots 160; Wrap/Main 418, 667 |

## 7. Phase 0 exit

Every row is classified. Rows that need data outside the plan's `Slot` are all satisfied by three additions to `Slot`, none of which changes the design:

1. `localMpv :: Int` (OQ-12; also what #19235 keys on)
2. `kind = External ProverVKs` carrying the full imported artifact (OQ-1)
3. `sourceDomainLog2s :: Array Int` per slot, replacing the uniform `nd` (OQ-3)

and one removal: `stmtSize` is unused by the compiler (OQ-5); what the slot needs is the statement's `CircuitType` dictionary, packed existentially.

`outputSize` (OQ-7) is the one type-level index that survives into Phase 2 and needs a decision there. Chunk counts (OQ-8, OQ-11) stay type-level as the plan says.

Plan open question 2 (side-loaded `mpv` bound on `Slot` vs `Tag`) is unaffected: the bound is read as `Reflectable mpvMax` from the `Slot SideLoaded mpvMax …` head (Compile 1446) and as `localMpv` it is the same field as item 1.
