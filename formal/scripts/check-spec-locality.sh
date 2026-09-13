#!/usr/bin/env bash
# A gadget's specification is stated once, in the gadget's module.
#
# The mirror image of sealing (`attribute [irreducible]`, which stops a consumer unfolding a
# gadget's BODY): this gate stops a consumer restating a gadget's SPEC. An assembly that
# needs a sub-gadget's reading in a different shape — its readings quantified in the
# postcondition so `mvcgen` can take the triple before the readings are in hand, two
# readings conjoined — writes a wrapper theorem whose statement copies the library spec's
# conclusion with the hypotheses moved. Every such copy is a place for the assembly and the
# library to drift apart, and the wrapper is repeated by the next assembly.
#
# The rule: no `theorem` whose CONCLUSION is a triple `⦃⌜True⌝⦄ g …` about a gadget `g`
# defined in another module of the pickles package. The defining module exports every
# shape a consumer needs (the family form for its own `mvcgen` runs, the `∀`-form for
# assemblies — `builder_spec_forall`, `builder_spec_and`, `builder_spec_imp` in
# `Snarky/WP.lean` are the combinators), and a consumer names it in a `have`.
#
# Hypotheses are free: `(hx : ⦃⌜True⌝⦄ computeXHat …)` speaks about a parameter, and a
# `def … : Prop` packaging a foreign triple as a premise (`FtEval0Hyp`) is not a claim. A
# conclusion's triple is the one at bracket depth 0 of the statement; every hypothesis sits
# inside its binder's parentheses. Gadgets of other packages (`groupMapCircuit` in Snarky)
# are out of scope: their deployed instantiations belong here.
#
# What counts as a gadget: a `def` or `abbrev` of the package (attributed or not, e.g.
# `@[irreducible] def`), and a field of a package `structure`/`class` whose type mentions
# `Builder`, `CircuitM` or a triple (an ops record's gadget field). What is scanned: every `theorem`
# (attributed or not, e.g. `@[spec] theorem`); its statement ends at the first depth-0 `:=`
# that is not a `let` binder, so `(c := Builder …)` and `let` do not hide the conclusion.
#
# The gate fails closed: a scanner error, an unreadable conclusion head, or zero checked
# conclusions is a failure, never a pass.
#
# Usage:
#   check-spec-locality.sh   # check only; non-zero exit on any violation
set -euo pipefail

cd "$(dirname "$0")/.." || exit 2   # -> formal/

pkg="pickles/Pickles"
# By-design splits, grandfathered: `file:gadget` pairs whose triple lives apart from the
# gadget on purpose (the reason beside each). Never grow this for a new assembly.
baseline="scripts/spec-locality-baseline.txt"

files=()
while IFS= read -r f; do files+=("$f"); done < <(find "$pkg" -name '*.lean' | sort)
if [ "${#files[@]}" -eq 0 ]; then
  echo "spec-locality gate ERROR: no .lean files under $pkg" >&2
  exit 2
fi

out=$(mktemp)
trap 'rm -f "$out"' EXIT

# One awk program, three passes: the baseline, the package's gadgets, the package's theorems.
# Plain POSIX awk (mawk on CI, BSD awk on macOS): byte-indexed `index`/`substr` throughout.
if ! awk '
  BEGIN { M = "⦃⌜True⌝⦄" }

  # bracket depth of a prefix: opens minus closes
  function depth_of(s,   t, o, c) {
    t = s; o = gsub(/[([{]/, "", t)
    t = s; c = gsub(/[)\]}]/, "", t)
    return o - c
  }

  # the statement part of a declaration: up to the first depth-0 `:=` that is not a `let`
  function statement(buf,   rest, off, pos, prefix) {
    rest = buf; off = 0
    while ((pos = index(rest, ":=")) > 0) {
      prefix = substr(buf, 1, off + pos - 1)
      if (depth_of(prefix) == 0 && prefix !~ /let [A-Za-z_][A-Za-z0-9_.]*( *: *[^,]*)? *$/)
        return prefix
      off += pos + 1
      rest = substr(rest, pos + 2)
    }
    return buf
  }

  # the identifier heading a conclusion: after the triple, past spaces and opening parens
  function head_of(s,   h) {
    h = s
    sub(/^[ (]*/, "", h)
    if (match(h, /^[A-Za-z_][A-Za-z0-9_.]*/)) return substr(h, RSTART, RLENGTH)
    return ""
  }

  function short_of(name,   n, parts) {
    n = split(name, parts, ".")
    return parts[n]
  }

  # pass 0: the baseline
  pass == 0 {
    sub(/#.*/, ""); gsub(/ /, "")
    if ($0 != "") allowed[$0] = 1
    next
  }

  # pass 1: gadget names -> defining file
  pass == 1 {
    if (FNR == 1) { in_struct = 0 }
    if ($0 ~ /^(@\[[^]]*\] *)?(private |protected )?(noncomputable )?(def|abbrev) [A-Za-z_][A-Za-z0-9_.]*/) {
      line = $0
      sub(/^(@\[[^]]*\] *)?(private |protected )?(noncomputable )?(def|abbrev) /, "", line)
      match(line, /^[A-Za-z_][A-Za-z0-9_.]*/)
      register(short_of(substr(line, RSTART, RLENGTH)), FILENAME)
      in_struct = 0
      next
    }
    if ($0 ~ /^(private |protected )?(structure|class) [A-Za-z_]/) {
      in_struct = 1; field = ""; field_text = ""
      next
    }
    if (in_struct) {
      if ($0 ~ /^[^ \t]/ && $0 !~ /^$/) { end_field(FILENAME); in_struct = 0; next }
      if ($0 ~ /^  [A-Za-z_][A-Za-z0-9_]* *:/) {
        end_field(FILENAME)
        field = $0; sub(/ *:.*/, "", field); sub(/^  /, "", field)
        field_text = $0
      } else if (field != "") {
        field_text = field_text " " $0
      }
    }
    next
  }

  function register(short, file) {
    def_of[short] = file
    local_def[file ":" short] = 1
  }

  function end_field(file) {
    if (field != "" && (index(field_text, "Builder") > 0 || index(field_text, "CircuitM") > 0 || index(field_text, M) > 0))
      register(field, file)
    field = ""; field_text = ""
  }

  # pass 2: theorem conclusions
  pass == 2 {
    if (FNR == 1) { flush(); in_struct = 0 }
    if ($0 ~ /^(@\[[^]]*\] *)?(private |protected )?theorem /) { flush(); buf = $0; ln = FNR; bfile = FILENAME; next }
    if (buf != "" && $0 ~ /^[^ \t]/) flush()
    if (buf != "") buf = buf " " $0
    next
  }

  function flush(   stmt, rest, off, pos, after, g, short, home) {
    if (buf == "") return
    stmt = statement(buf)
    rest = stmt; off = 0
    while ((pos = index(rest, M)) > 0) {
      if (depth_of(substr(stmt, 1, off + pos - 1)) == 0) {
        checked++
        after = substr(rest, pos + length(M), 200)
        g = head_of(after)
        if (g == "") {
          print bfile ":" ln ": unreadable conclusion head after the triple"
          errors++
        } else {
          short = short_of(g)
          home = def_of[short]
          if (home != "" && home != bfile && !((bfile ":" short) in local_def) &&
              !((bfile ":" short) in allowed))
            print bfile ":" ln ": triple about \047" short "\047 (defined in " home ") stated outside its module"
        }
      }
      off += pos + length(M) - 1
      rest = substr(rest, pos + length(M))
    }
    buf = ""
  }

  END {
    flush()
    print "CHECKED " checked + 0
    print "ERRORS " errors + 0
  }
' pass=0 "$baseline" pass=1 "${files[@]}" pass=2 "${files[@]}" > "$out"; then
  echo "spec-locality gate ERROR: scanner failed" >&2
  exit 2
fi

checked=$(awk '/^CHECKED /{print $2}' "$out")
errors=$(awk '/^ERRORS /{print $2}' "$out")
violations=$(grep -Evc '^(CHECKED|ERRORS) ' "$out" || true)

if [ -z "$checked" ] || [ -z "$errors" ]; then
  echo "spec-locality gate ERROR: scanner produced no summary" >&2
  exit 2
fi

grep -Ev '^(CHECKED|ERRORS) ' "$out" || true

if [ "$checked" -eq 0 ]; then
  echo "spec-locality gate ERROR: 0 conclusions checked (scanner or layout broken)" >&2
  exit 2
fi

if [ "$violations" -ne 0 ]; then
  echo
  echo "spec-locality gate FAILED: $violations problems ($checked conclusions checked, $errors unreadable)"
  exit 1
fi

echo "✓ specs local to their gadgets ($checked pickles triple conclusions checked)"
