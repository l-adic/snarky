#!/usr/bin/env python3
"""
Side-by-side PS vs OC label/gate diff explorer for circuit-diff fixtures.

Loads the comparison JSON (PS gates) and OCaml gate_labels.jsonl, lets you
slice by row range, count by label, find structural divergences, etc.

Usage:
  cs_label_diff.py FIXTURE [SUBCOMMAND] [ARGS]

FIXTURE is a name like 'step_main_simple_chain_n2_circuit'. The script reads:
  - packages/pickles-circuit-diffs/circuits/results/<F>.json   (PS+OC gates)
  - packages/pickles-circuit-diffs/circuits/ocaml/<F>_gate_labels.jsonl  (OC labels)
  - packages/pickles-circuit-diffs/circuits/ocaml/<F>_labels.jsonl  (OC events)

Subcommands:
  find_shift [--coeffs] [START [LIMIT]]
                            Walk PS and OC in lockstep and report structural
                            shifts. Default compares gate KIND only. With
                            --coeffs also compares coefficients. For Generic
                            divergences, tries half-level alignment across the
                            previous/next Generic rows (Generic is the only
                            gate kind that packs 2 halves per row, so a +1
                            extra Generic emission upstream shifts subsequent
                            half pairings even though kinds keep matching).
                            Distinguishes:
                              - half-level shift (Generic packing offset)
                              - row-level insertion (non-Generic kind diff)
                              - content diff (kinds align, coeffs differ)
  rows LO HI               PS vs OC rows in [LO, HI], showing kind+coeffs+label tail
  diff [START [END]]       First row where kind or coeffs differ (legacy)
  totals                   Total row count, kind breakdown
  ps_label LABEL           Show all PS rows whose context contains LABEL
  oc_label LABEL           Same for OC
  pair_count [LABEL]       Per top-level-context-prefix row counts (PS vs OC)
  gate_kinds LO HI         Halve-kind histogram in [LO, HI]; informational only,
                            NOT a divergence detector — same total halves on
                            both sides means same emission count, not "aligned"
  seals [LO HI]            Rows tagged with any 'seal' label
  trace_var ROW COL        Walk the wire equivalence cycle from (row, col)
  cached_constants [--depth N] [--limit N] [--samples K] [--field fp|fq]
                            Diff PS vs OC cached_constants tables. Reports
                            totals + set diff, then bins each side's extras
                            by emission-row label prefix.

Conventions:
  - Default side is 'ps' for ps_label, 'oc' for oc_label etc.
  - Use --side ps|oc to override where it matters.
"""

from __future__ import annotations
import argparse
import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / "packages/pickles-circuit-diffs/circuits/results"
OCAML = ROOT / "packages/pickles-circuit-diffs/circuits/ocaml"

# Pasta field moduli. Wrap circuits run over Fq (Pallas scalar / Vesta base);
# step circuits run over Fp (Pallas base / Vesta scalar). Auto-detected from
# the fixture name unless --field overrides.
PASTA_FP = 28948022309329048855892746252171976963363056481941560715954676764349967630337
PASTA_FQ = 28948022309329048855892746252171976963363056481941647379679742748393362948097


def detect_field(fixture, override):
    if override == "fp":
        return PASTA_FP
    if override == "fq":
        return PASTA_FQ
    # auto: wrap_* → Fq, anything else (step_*, gadget tests) → Fp
    return PASTA_FQ if fixture.startswith("wrap_") else PASTA_FP


def cat_half(coeffs):
    """Return a short tag for a 5-coeff half."""
    if not coeffs or len(coeffs) != 5:
        return "?"
    c = tuple(coeffs)
    table = {
        ("0", "0", "1", "-1", "0"): "mul",
        ("1", "1", "-1", "0", "0"): "add",
        ("0", "0", "0", "1", "0"): "lr=0",
        ("-1", "0", "-1", "0", "1"): "1-l",
        ("1", "0", "-1", "0", "1"): "l+1=o",
        ("-1", "1", "-1", "0", "0"): "r-l",
        ("-1", "-1", "-1", "0", "0"): "-l-r",
        ("-1", "1", "-1", "0", "4"): "-l+r+4",
    }
    return table.get(c, f"OTHER<{c[0][:6]}…>")


def half_pretty(coeffs, half):
    """half = 'L' or 'R'; coeffs is the 10-element list."""
    if half == "L":
        c5 = coeffs[:5] if coeffs else []
    else:
        c5 = coeffs[5:] if coeffs and len(coeffs) >= 10 else []
    return cat_half(c5)


def label_tail(g, n=2):
    ctx = g.get("context", [])
    if isinstance(ctx, str):
        return ctx[-80:]
    if not ctx:
        return ""
    return " > ".join(ctx[-n:])


def short_loc(label):
    """Compress 'File "..../X.ml", line N, characters A-B' to 'X.ml:N:A-B'."""
    if not label.startswith('File "'):
        return label
    try:
        rest = label.split('"', 2)[1]  # full path
        fname = Path(rest).name
        tail = label.split('"', 2)[2]
        # tail like ', line 31, characters 17-24'
        parts = tail.strip(", ").split(",")
        ln = parts[0].replace("line ", "").strip()
        ch = parts[1].replace("characters ", "").strip() if len(parts) > 1 else ""
        return f"{fname}:{ln}:{ch}"
    except Exception:
        return label


def ctx_short(g, n=3):
    ctx = g.get("context", [])
    if isinstance(ctx, str):
        return ctx
    if not ctx:
        return ""
    return " > ".join(short_loc(x) for x in ctx[-n:])


def load(fixture):
    """Load PS gates, OC gates, OC gate-labels (per-row), OC event-labels.

    Returns (ps, oc, events, raw_json) — raw_json holds the full JSON so callers
    that need the cachedConstants lists (or other top-level keys) can reach them
    without re-reading the file.
    """
    j = json.loads((RESULTS / f"{fixture}.json").read_text())
    ps = j["purescript"]["gates"]
    oc = j["ocaml"]["gates"]

    # Merge OCaml per-row labels (they live in the OCaml fixtures dir, not
    # in the comparison JSON for older runs).
    gl_path = OCAML / f"{fixture}_gate_labels.jsonl"
    if gl_path.exists():
        for i, line in enumerate(gl_path.open()):
            d = json.loads(line)
            if i < len(oc) and not oc[i].get("context"):
                oc[i]["context"] = d.get("context", [])

    # Per-constraint event labels (only OCaml ships these from the new dump).
    el_path = OCAML / f"{fixture}_labels.jsonl"
    events = []
    if el_path.exists():
        for line in el_path.open():
            line = line.strip()
            if not line:
                continue
            events.append(json.loads(line))

    return ps, oc, events, j


def cmd_rows(ps, oc, args):
    lo, hi = int(args.lo), int(args.hi)
    print(f"{'row':>5} | {'PS L|R':14s} | {'OC L|R':14s} | PS label / OC label")
    print("-" * 110)
    for i in range(lo, hi + 1):
        if i >= len(ps) or i >= len(oc):
            break
        p = ps[i]
        o = oc[i]
        ps_kind = "P" if p.get("kind") == "Poseidon" else "G"
        oc_kind = "P" if o.get("kind") == "Poseidon" else "G"
        ps_LR = f"{half_pretty(p.get('coeffs', []), 'L'):6s}|{half_pretty(p.get('coeffs', []), 'R'):6s}"
        oc_LR = f"{half_pretty(o.get('coeffs', []), 'L'):6s}|{half_pretty(o.get('coeffs', []), 'R'):6s}"
        ps_lbl = ctx_short(p, 2)
        oc_lbl = ctx_short(o, 2)
        marker = "  " if p.get("kind") == o.get("kind") else "*K"
        print(f"{i:>5} {marker}| {ps_LR:14s} | {oc_LR:14s} | {ps_lbl[:50]} || {oc_lbl[:50]}")


def cmd_diff(ps, oc, args):
    start = int(args.start) if args.start else 0
    end = int(args.end) if args.end else min(len(ps), len(oc))
    for i in range(start, end):
        p = ps[i]
        o = oc[i]
        if p.get("kind") != o.get("kind"):
            print(f"first KIND diff at row {i}: PS={p['kind']} OC={o['kind']}")
            print(f"  PS ctx: {ctx_short(p, 4)}")
            print(f"  OC ctx: {ctx_short(o, 4)}")
            return
        if p.get("coeffs") != o.get("coeffs"):
            print(f"first COEFF diff at row {i}:")
            pc = p.get("coeffs", [])
            oc_ = o.get("coeffs", [])
            print(f"  PS L={pc[:5]} R={pc[5:]}")
            print(f"  OC L={oc_[:5]} R={oc_[5:]}")
            print(f"  PS ctx: {ctx_short(p, 4)}")
            print(f"  OC ctx: {ctx_short(o, 4)}")
            return
    print(f"no kind/coeff diff in [{start}, {end})")


def cmd_totals(ps, oc, args):
    print(f"PS rows: {len(ps)}")
    print(f"OC rows: {len(oc)}")
    print(f"Delta:   {len(ps) - len(oc):+d}")
    print()
    pk = Counter(g.get("kind") for g in ps)
    ok = Counter(g.get("kind") for g in oc)
    print(f"{'kind':12s} {'PS':>8s} {'OC':>8s} {'delta':>8s}")
    for k in sorted(set(pk) | set(ok)):
        d = pk[k] - ok[k]
        marker = " *" if d != 0 else ""
        print(f"{k or '?':12s} {pk[k]:>8d} {ok[k]:>8d} {d:>+8d}{marker}")


def cmd_ps_label(ps, oc, args):
    needle = args.label
    rows = [i for i, g in enumerate(ps) if needle in " / ".join(g.get("context") or [])]
    if not rows:
        print(f"(no PS rows match {needle!r})")
        return
    runs = []
    s = p = rows[0]
    for r in rows[1:]:
        if r == p + 1:
            p = r
        else:
            runs.append((s, p))
            s = p = r
    runs.append((s, p))
    print(f"PS '{needle}' matches {len(rows)} rows in {len(runs)} runs:")
    for a, b in runs:
        print(f"  rows {a}..{b} ({b - a + 1} rows)")


def cmd_oc_label(ps, oc, args):
    needle = args.label
    rows = [i for i, g in enumerate(oc) if needle in " > ".join(g.get("context") or [])]
    if not rows:
        print(f"(no OC rows match {needle!r})")
        return
    runs = []
    s = p = rows[0]
    for r in rows[1:]:
        if r == p + 1:
            p = r
        else:
            runs.append((s, p))
            s = p = r
    runs.append((s, p))
    print(f"OC '{needle}' matches {len(rows)} rows in {len(runs)} runs:")
    for a, b in runs:
        print(f"  rows {a}..{b} ({b - a + 1} rows)")


def cmd_gate_kinds(ps, oc, args):
    """Halve-kind histogram in [LO, HI]. INFORMATIONAL ONLY — same total halves
    on both sides means same emission count, NOT structural alignment.
    Use find_shift to localize where PS gets ahead of OC."""
    lo, hi = int(args.lo), int(args.hi)
    psc = Counter()
    occ = Counter()
    for i in range(lo, hi + 1):
        if i < len(ps):
            for half in ("L", "R"):
                psc[half_pretty(ps[i].get("coeffs", []), half)] += 1
        if i < len(oc):
            for half in ("L", "R"):
                occ[half_pretty(oc[i].get("coeffs", []), half)] += 1
    print(f"halves in rows [{lo}..{hi}]  (informational; not a divergence detector):")
    print(f"{'kind':14s} {'PS':>6s} {'OC':>6s} {'delta':>6s}")
    for k in sorted(set(psc) | set(occ), key=lambda x: -(psc[x] + occ[x])):
        d = psc[k] - occ[k]
        marker = " *" if d != 0 else ""
        print(f"{k:14s} {psc[k]:>6d} {occ[k]:>6d} {d:>+6d}{marker}")
    print(f"{'TOTAL':14s} {sum(psc.values()):>6d} {sum(occ.values()):>6d} {sum(psc.values()) - sum(occ.values()):>+6d}")


# --------------------------------------------------------------------------- #
# find_shift: locate structural row insertions / half-level packing offsets
# between PS and OC gate sequences.
# --------------------------------------------------------------------------- #

def _row_kind(g):
    return g.get("kind")


def _row_halves(g):
    """Return (L_coeffs, R_coeffs) tuples; returns (None, None) for non-Generic."""
    if g.get("kind") != "Generic":
        return (None, None)
    c = g.get("coeffs") or []
    if len(c) != 10:
        return (None, None)
    return (tuple(c[:5]), tuple(c[5:]))


def _kind_match(g1, g2, check_coeffs):
    if _row_kind(g1) != _row_kind(g2):
        return False
    if not check_coeffs:
        return True
    return g1.get("coeffs") == g2.get("coeffs")


def _generic_halves(gates, i):
    """Return (L, R) for gates[i] if it's Generic, else (None, None)."""
    if i < 0 or i >= len(gates):
        return (None, None)
    return _row_halves(gates[i])


def _detect_half_shift(ps, oc, k):
    """At Generic row k, both sides Generic but contents differ. Test whether
    PS is 1 half ahead of OC by checking if PS[k].L matches OC[k-1].R, or PS[k].R matches
    OC[k+1].L (and the 'shifted' alignment continues for a few rows).

    Returns dict {direction: 'ps_ahead'|'oc_ahead'|None, evidence: str} where
    'ps_ahead' means PS has an extra Generic emission upstream that pushed PS one
    half-step ahead.
    """
    pL, pR = _generic_halves(ps, k)
    oL, oR = _generic_halves(oc, k)
    if pL is None or oL is None:
        return {"direction": None, "evidence": "non-Generic at K"}

    # Hypothesis 1: PS is one half ahead.
    # Then PS[k].L = OC[k-1].R, PS[k].R = OC[k].L, and PS[k+1].L = OC[k].R, etc.
    _, oprev_R = _generic_halves(oc, k - 1)
    h1_match = (pL == oprev_R) and (pR == oL) if oprev_R is not None else False

    # Hypothesis 2: OC is one half ahead (PS one half behind).
    # Then PS[k].L = OC[k].R, PS[k].R = OC[k+1].L.
    onext_L, _ = _generic_halves(oc, k + 1)
    h2_match = (pL == oR) and (pR == onext_L) if onext_L is not None else False

    if h1_match and not h2_match:
        return {"direction": "ps_ahead", "evidence": f"PS[{k}].L == OC[{k-1}].R AND PS[{k}].R == OC[{k}].L"}
    if h2_match and not h1_match:
        return {"direction": "oc_ahead", "evidence": f"PS[{k}].L == OC[{k}].R AND PS[{k}].R == OC[{k+1}].L"}
    if h1_match and h2_match:
        return {"direction": "ambiguous", "evidence": "both alignments match"}
    return {"direction": None, "evidence": "no half-shift alignment"}


def cmd_find_shift(ps, oc, args):
    """Walk PS and OC in lockstep, report structural shifts and content diffs."""
    check_coeffs = bool(args.coeffs)
    start = int(args.start) if args.start else 0
    limit = int(args.limit) if args.limit else 0  # 0 = unlimited

    n = min(len(ps), len(oc))
    events = 0
    i = start
    while i < n:
        p = ps[i]
        o = oc[i]

        # Kind diff: clean row-level shift candidate.
        if _row_kind(p) != _row_kind(o):
            # Try row-level shift: does PS[i+1].kind == OC[i].kind?
            if i + 1 < len(ps) and _row_kind(ps[i + 1]) == _row_kind(o):
                events += 1
                print(f"\n[ROW INSERTION at PS row {i}] PS has an extra row not in OC")
                print(f"  PS[{i}]   kind={_row_kind(p)}  ctx: {ctx_short(p, 3)}")
                print(f"    coeffs={p.get('coeffs')}")
                print(f"  PS[{i+1}] kind={_row_kind(ps[i+1])}  (matches OC[{i}].kind)")
                print(f"  OC[{i}]   kind={_row_kind(o)}  ctx: {ctx_short(o, 3)}")
                if limit and events >= limit:
                    return
                i += 1  # skip the inserted PS row
                continue
            # OC-side insertion?
            if i + 1 < len(oc) and _row_kind(oc[i + 1]) == _row_kind(p):
                events += 1
                print(f"\n[ROW INSERTION at OC row {i}] OC has an extra row not in PS")
                print(f"  OC[{i}]   kind={_row_kind(o)}  ctx: {ctx_short(o, 3)}")
                print(f"    coeffs={o.get('coeffs')}")
                print(f"  OC[{i+1}] kind={_row_kind(oc[i+1])}  (matches PS[{i}].kind)")
                print(f"  PS[{i}]   kind={_row_kind(p)}  ctx: {ctx_short(p, 3)}")
                if limit and events >= limit:
                    return
                # Don't advance PS, advance OC by skipping; we model this by
                # remembering the offset. Simplest: just record and break.
                print("  (OC-side shift; further alignment requires bookkeeping not yet implemented; stopping)")
                return
            print(f"\n[KIND DIFF at row {i}] no row-level shift detected")
            print(f"  PS[{i}] kind={_row_kind(p)} coeffs={p.get('coeffs')}")
            print(f"  OC[{i}] kind={_row_kind(o)} coeffs={o.get('coeffs')}")
            print(f"  PS ctx: {ctx_short(p, 3)}")
            print(f"  OC ctx: {ctx_short(o, 3)}")
            return

        # Same kind. If Generic, try half-level alignment.
        if _row_kind(p) == "Generic":
            pL, pR = _row_halves(p)
            oL, oR = _row_halves(o)
            if (pL, pR) != (oL, oR):
                # Halves differ. Could be content diff (same emissions, different
                # coefficients) or a half-level shift (PS has 1 extra Generic
                # emission upstream).
                shift = _detect_half_shift(ps, oc, i)
                if shift["direction"] == "ps_ahead":
                    events += 1
                    print(f"\n[HALF-LEVEL SHIFT at row {i}] PS is one Generic-half ahead of OC")
                    print(f"  evidence: {shift['evidence']}")
                    print(f"  PS[{i}] L={list(pL)} R={list(pR)}  ctx: {ctx_short(p, 3)}")
                    print(f"  OC[{i-1}] L={list(_generic_halves(oc, i-1)[0]) if _generic_halves(oc, i-1)[0] else 'n/a'}"
                          f" R={list(_generic_halves(oc, i-1)[1]) if _generic_halves(oc, i-1)[1] else 'n/a'}")
                    print(f"  OC[{i}]   L={list(oL)} R={list(oR)}  ctx: {ctx_short(o, 3)}")
                    print(f"  Implication: an extra PS Generic emission landed upstream;"
                          f" walk back to find the unpaired half.")
                    if limit and events >= limit:
                        return
                    # Continue scanning past — there may be a "snap-back" shift
                    # later in the circuit that brings the parity back.
                    i += 1
                    continue
                elif shift["direction"] == "oc_ahead":
                    events += 1
                    print(f"\n[HALF-LEVEL SHIFT at row {i}] OC is one Generic-half ahead of PS")
                    print(f"  evidence: {shift['evidence']}")
                    print(f"  PS[{i}] L={list(pL)} R={list(pR)}  ctx: {ctx_short(p, 3)}")
                    print(f"  OC[{i}] L={list(oL)} R={list(oR)}  ctx: {ctx_short(o, 3)}")
                    if limit and events >= limit:
                        return
                    i += 1
                    continue
                elif shift["direction"] == "ambiguous":
                    print(f"\n[ambiguous at row {i}] both shift hypotheses match — likely repetitive content")
                    i += 1
                    continue
                else:
                    # Content diff (kinds match, coeffs differ, no shift).
                    if check_coeffs:
                        events += 1
                        print(f"\n[CONTENT DIFF at row {i}] same kind, same packing, different coeffs")
                        print(f"  PS[{i}] L={list(pL)} R={list(pR)}  ctx: {ctx_short(p, 3)}")
                        print(f"  OC[{i}] L={list(oL)} R={list(oR)}  ctx: {ctx_short(o, 3)}")
                        if limit and events >= limit:
                            return
                    i += 1
                    continue
            # halves match — fully aligned this row.
        else:
            # Non-Generic same kind: optionally check coeffs.
            if check_coeffs and p.get("coeffs") != o.get("coeffs"):
                events += 1
                print(f"\n[CONTENT DIFF at non-Generic row {i}] kind={_row_kind(p)}")
                print(f"  PS coeffs: {p.get('coeffs')}")
                print(f"  OC coeffs: {o.get('coeffs')}")
                if limit and events >= limit:
                    return
        i += 1

    if events == 0:
        print(f"no shifts/content diffs found in [{start}, {n})")
    else:
        print(f"\n({events} event(s) reported)")


def cmd_seals(ps, oc, args):
    """Find rows tagged with any 'seal' label."""
    lo = int(args.lo) if args.lo else 0
    hi = int(args.hi) if args.hi else max(len(ps), len(oc))

    def has_seal(g):
        ctx = g.get("context") or []
        return any("seal" in (x or "").lower() for x in ctx)

    print(f"{'row':>5}  side  label_tail")
    print("-" * 80)
    for i in range(lo, hi):
        if i < len(ps) and has_seal(ps[i]):
            print(f"{i:>5}  PS    {ctx_short(ps[i], 4)[:80]}")
        if i < len(oc) and has_seal(oc[i]):
            print(f"{i:>5}  OC    {ctx_short(oc[i], 4)[:80]}")


def cmd_pair_count(ps, oc, args):
    """For each unique PS top-level label tail, count rows on both sides."""
    needle = args.label

    def key(g):
        ctx = g.get("context") or []
        if needle:
            cs = " / ".join(ctx) if ctx else ""
            if needle not in cs:
                return None
        return tuple(ctx[:3])

    psc = Counter()
    occ = Counter()
    for g in ps:
        k = key(g)
        if k is not None:
            psc[k] += 1
    for g in oc:
        k = key(g)
        if k is not None:
            occ[k] += 1
    keys = sorted(set(psc) | set(occ), key=lambda x: -abs(psc[x] - occ[x]))
    print(f"{'PS rows':>8} {'OC rows':>8} {'delta':>6}  prefix")
    for k in keys[:30]:
        d = psc[k] - occ[k]
        marker = " *" if d != 0 else ""
        prefix = " > ".join(short_loc(p) for p in k)
        print(f"{psc[k]:>8d} {occ[k]:>8d} {d:>+6d}{marker}  {prefix[:80]}")


def _generic_emission_stream(gates, lo, hi):
    """Yield (row_idx, half_label, coeffs_tuple) in emission order for Generic
    rows in [lo, hi]. Per the Kimchi queue semantics: each Generic row's R-half
    was emitted FIRST (buffered as QUEUED), then L-half emitted to pair (NEW).
    So emission order within a row is R then L. Non-Generic rows skipped."""
    for i in range(lo, min(hi, len(gates))):
        g = gates[i]
        if g.get("kind") != "Generic":
            continue
        c = g.get("coeffs") or []
        if len(c) != 10:
            continue
        # R first (QUEUED, emitted earlier)
        yield (i, "R", tuple(c[5:]))
        # L second (NEW, emitted later)
        yield (i, "L", tuple(c[:5]))


def _coeffs_compatible(a, b, kind_only):
    """If kind_only, compare the (zero/nonzero, sign) structure of each
    coefficient — same gate kind (mul vs square vs add vs scaled-add etc.),
    independent of specific scalar values."""
    if kind_only:
        def shape(c):
            # For each coefficient, capture (is_zero, sign).
            return tuple((x == "0", x.startswith("-")) for x in c)
        return shape(a) == shape(b)
    return a == b


def cmd_generic_stream_diff(ps, oc, args):
    """Walk PS and OC Generic-half emission streams in parallel and report
    EVERY structural insertion/deletion. Skips pure coefficient diffs when
    --kind-only flag is set. Tracks cumulative PS-vs-OC emission balance."""
    lo = int(args.lo) if args.lo else 0
    hi = int(args.hi) if args.hi else max(len(ps), len(oc))
    kind_only = bool(args.kind_only)
    LOOKAHEAD = 8

    ps_stream = list(_generic_emission_stream(ps, lo, hi))
    oc_stream = list(_generic_emission_stream(oc, lo, hi))

    def stream_matches_at(ps_k, oc_k, count):
        for j in range(count):
            if ps_k + j >= len(ps_stream) or oc_k + j >= len(oc_stream):
                return False
            if not _coeffs_compatible(
                ps_stream[ps_k + j][2],
                oc_stream[oc_k + j][2],
                kind_only):
                return False
        return True

    pi = oi = 0
    cumulative = 0  # PS_extras - OC_extras
    events = 0
    while pi < len(ps_stream) and oi < len(oc_stream):
        if _coeffs_compatible(ps_stream[pi][2], oc_stream[oi][2], kind_only):
            pi += 1
            oi += 1
            continue
        # Mismatch — try insertion/deletion classification.
        if stream_matches_at(pi + 1, oi, LOOKAHEAD):
            # PS extra at pi
            events += 1
            cumulative += 1
            pe = ps_stream[pi]
            print(f"[+PS] cum={cumulative:+d} stream#{pi}: PS row {pe[0]}.{pe[1]}"
                  f" coeffs={list(pe[2])}  ctx={ctx_short(ps[pe[0]], 3)}")
            pi += 1
            continue
        if stream_matches_at(pi, oi + 1, LOOKAHEAD):
            # OC extra at oi
            events += 1
            cumulative -= 1
            oe = oc_stream[oi]
            print(f"[+OC] cum={cumulative:+d} stream#{oi}: OC row {oe[0]}.{oe[1]}"
                  f" coeffs={list(oe[2])}  ctx={ctx_short(oc[oe[0]], 3)}")
            oi += 1
            continue
        # Content diff (kinds match, coeffs differ; no insertion).
        if not kind_only:
            events += 1
            pe = ps_stream[pi]
            oe = oc_stream[oi]
            print(f"[CONTENT] stream#{pi}: PS coeffs={list(pe[2])} vs OC coeffs={list(oe[2])}"
                  f"  PS={ctx_short(ps[pe[0]], 2)}")
        pi += 1
        oi += 1

    print()
    print(f"=== summary ===")
    print(f"PS Generic halves: {len(ps_stream)}, OC Generic halves: {len(oc_stream)}, delta={len(ps_stream) - len(oc_stream):+d}")
    print(f"final cumulative shift (PS extras - OC extras): {cumulative:+d}")
    print(f"events reported: {events}")
    if pi < len(ps_stream) or oi < len(oc_stream):
        print(f"unprocessed tail: PS@{pi}/{len(ps_stream)} OC@{oi}/{len(oc_stream)}")


def cmd_cached_constants(ps, oc, args):
    """Compare PS vs OC cached_constants tables.

    Both sides dump a list of (variable_id, value) entries — every constant
    that was ever materialized through the constraint-system's cached_constants
    cache. A delta in the *set* of canonical values means one side allocated
    constants the other side computed algebraically, which is one of the
    cleanest signals available for divergent emission patterns inside MSM /
    seal / addFast paths.

    The handler:
      1. Computes set diff after canonicalizing each value modulo the field.
      2. For each PS-extra (and optionally OC-extra), finds the row where the
         constant was emitted by scanning Generic gates for the
         assert_equal_constant signature: a half whose coeffs match
         [cl≠0, 0, 0, 0, cc≠0]. The constant value is `-cc/cl mod p`.
      3. Bins the located rows by label-prefix at the configured depth and
         prints per-prefix counts plus sample rows.
    """
    raw = args.raw
    ps_cc = raw.get("purescript", {}).get("cachedConstants", [])
    oc_cc = raw.get("ocaml", {}).get("cachedConstants", [])

    field = detect_field(args.fixture if hasattr(args, "fixture") else "", args.field)

    def canon_set(entries):
        return {int(c["value"]) % field for c in entries}

    ps_canon = canon_set(ps_cc)
    oc_canon = canon_set(oc_cc)
    ps_only = ps_canon - oc_canon
    oc_only = oc_canon - ps_canon

    print(f"=== totals ===")
    print(f"PS cached_constants entries: {len(ps_cc)}, distinct values: {len(ps_canon)}")
    print(f"OC cached_constants entries: {len(oc_cc)}, distinct values: {len(oc_canon)}")
    print(f"shared values:  {len(ps_canon & oc_canon)}")
    print(f"PS-only values: {len(ps_only)}")
    print(f"OC-only values: {len(oc_only)}")
    print(f"field: {field}")
    print()

    def find_emissions(gates, target_values):
        """Walk Generic gates, return list of (row_idx, value, ctx) for each
        half that materializes a value in target_values."""
        out = []
        for idx, g in enumerate(gates):
            if g.get("kind") != "Generic":
                continue
            coeffs = g.get("coeffs") or []
            ctx = g.get("context") or []
            for half_off in (0, 5):
                if len(coeffs) < half_off + 5:
                    continue
                cl, cr, co, cm, cc = (int(coeffs[half_off + i]) for i in range(5))
                if cl == 0 or cr != 0 or co != 0 or cm != 0 or cc == 0:
                    continue
                val = (-cc * pow(cl, -1, field)) % field
                if val in target_values:
                    out.append((idx, val, ctx))
        return out

    def report(side, gates, extras_set):
        emissions = find_emissions(gates, extras_set)
        # Bin by label prefix (depth args.depth).
        bins = Counter()
        per_bin_samples = {}
        for row, val, ctx in emissions:
            key = " > ".join(ctx[: args.depth]) if ctx else "<no-label>"
            bins[key] += 1
            per_bin_samples.setdefault(key, []).append((row, val, ctx))

        print(f"=== {side}-extra emissions ({len(emissions)} total in {len(bins)} buckets) ===")
        for key, n in bins.most_common(args.limit):
            print(f"  {n:5d}  {key}")
            for row, val, ctx in per_bin_samples[key][: args.samples]:
                vstr = str(val)[:50] + ("..." if len(str(val)) > 50 else "")
                print(f"        row {row} val={vstr}")
                if len(ctx) > args.depth:
                    print(f"          full ctx tail: {ctx[args.depth:]}")
        print()

    if args.side in ("ps", "both"):
        report("PS", ps, ps_only)
    if args.side in ("oc", "both"):
        report("OC", oc, oc_only)


def cmd_trace_var(ps, oc, args):
    side = args.side
    gates = ps if side == "ps" else oc
    row, col = int(args.row), int(args.col)
    seen = set()
    print(f"wire equivalence cycle for {side.upper()}[{row}, col {col}]:")
    while (row, col) not in seen:
        seen.add((row, col))
        if row >= len(gates):
            break
        g = gates[row]
        wires = g.get("wires") or []
        if col >= len(wires):
            break
        ctx = ctx_short(g, 2)
        coeffs = g.get("coeffs", [])
        half = "L" if col < 3 else "R"
        kind = half_pretty(coeffs, half)
        print(f"  ({row}, {col}) {side.upper()} {kind:8s}  ctx={ctx}")
        nxt = wires[col]
        row, col = nxt.get("row"), nxt.get("col")
        if row is None or col is None:
            break
    print(f"  cycle closed at ({row}, {col})")


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    p.add_argument("fixture", help="fixture name, e.g. step_main_simple_chain_n2_circuit")
    sub = p.add_subparsers(dest="cmd", required=True)

    sp = sub.add_parser("find_shift"); sp.add_argument("start", nargs="?"); sp.add_argument("limit", nargs="?"); sp.add_argument("--coeffs", action="store_true", help="also flag content diffs (kinds align, coeffs differ)"); sp.set_defaults(func=cmd_find_shift)
    sp = sub.add_parser("rows"); sp.add_argument("lo"); sp.add_argument("hi"); sp.set_defaults(func=cmd_rows)
    sp = sub.add_parser("diff"); sp.add_argument("start", nargs="?"); sp.add_argument("end", nargs="?"); sp.set_defaults(func=cmd_diff)
    sp = sub.add_parser("totals"); sp.set_defaults(func=cmd_totals)
    sp = sub.add_parser("ps_label"); sp.add_argument("label"); sp.set_defaults(func=cmd_ps_label)
    sp = sub.add_parser("oc_label"); sp.add_argument("label"); sp.set_defaults(func=cmd_oc_label)
    sp = sub.add_parser("pair_count"); sp.add_argument("label", nargs="?"); sp.set_defaults(func=cmd_pair_count)
    sp = sub.add_parser("gate_kinds"); sp.add_argument("lo"); sp.add_argument("hi"); sp.set_defaults(func=cmd_gate_kinds)
    sp = sub.add_parser("seals"); sp.add_argument("lo", nargs="?"); sp.add_argument("hi", nargs="?"); sp.set_defaults(func=cmd_seals)
    sp = sub.add_parser("generic_stream_diff"); sp.add_argument("lo", nargs="?"); sp.add_argument("hi", nargs="?"); sp.add_argument("--kind-only", action="store_true", help="only compare gate kind signature, skip pure coefficient diffs"); sp.set_defaults(func=cmd_generic_stream_diff)
    sp = sub.add_parser("trace_var"); sp.add_argument("row"); sp.add_argument("col"); sp.add_argument("--side", choices=["ps", "oc"], default="ps"); sp.set_defaults(func=cmd_trace_var)
    sp = sub.add_parser("cached_constants",
                        help="Compare cached_constants tables: totals, set diff, "
                             "and per-label distribution of PS-extras/OC-extras.")
    sp.add_argument("--depth", type=int, default=4,
                    help="label nesting depth used for binning extras (default 4)")
    sp.add_argument("--limit", type=int, default=20,
                    help="top N label-prefixes to show (default 20)")
    sp.add_argument("--samples", type=int, default=2,
                    help="sample rows per label-prefix (default 2)")
    sp.add_argument("--field", choices=["fp", "fq"], default=None,
                    help="override field modulus (default: auto from fixture name)")
    sp.add_argument("--side", choices=["ps", "oc", "both"], default="both",
                    help="show extras on PS side, OC side, or both (default both)")
    sp.set_defaults(func=cmd_cached_constants)

    args = p.parse_args()
    ps, oc, events, raw = load(args.fixture)
    # Pass raw via args so existing handlers don't need new kwargs.
    args.raw = raw
    args.func(ps, oc, args)


if __name__ == "__main__":
    main()
