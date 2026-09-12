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
# Usage:
#   check-spec-locality.sh   # check only; non-zero exit on any violation
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2   # -> formal/

pkg="pickles/Pickles"

# gadget name (last segment) -> defining file, over the package's `def`s
declare -A def_of
declare -A local_def
while IFS= read -r line; do
  f="${line%%:*}"
  name="${line##*:}"
  def_of["${name##*.}"]="$f"
  local_def["$f:${name##*.}"]=1
done < <(grep -rEo '^(private |protected )?(noncomputable )?def [A-Za-z_][A-Za-z0-9_.]*' \
           --include='*.lean' "$pkg" | sed -E 's/:(private |protected )?(noncomputable )?def /:/')

# By-design splits, grandfathered: `file:gadget` pairs whose triple lives apart from the
# gadget on purpose (the reason beside each). Never grow this for a new assembly.
baseline="scripts/spec-locality-baseline.txt"
declare -A allowed
if [ -f "$baseline" ]; then
  while IFS= read -r entry; do
    entry="${entry%%#*}"
    entry="${entry// /}"
    [ -z "$entry" ] && continue
    allowed["$entry"]=1
  done < "$baseline"
fi

violations=0
checked=0

files=()
while IFS= read -r f; do files+=("$f"); done < <(find "$pkg" -name '*.lean' | sort)

for f in "${files[@]}"; do
  # every depth-0 `⦃⌜True⌝⦄` in a theorem statement, with the text that follows it
  while IFS= read -r hit; do
    line="${hit%%:*}"
    text="${hit#*:}"
    g=$(printf '%s' "$text" | grep -oE "^ *[A-Za-z_][A-Za-z0-9_.']*" | head -1 | tr -d ' ')
    [ -z "$g" ] && continue
    checked=$((checked + 1))
    short="${g##*.}"
    home="${def_of[$short]:-}"
    [ -z "$home" ] && continue
    [ "$home" = "$f" ] && continue
    # a same-named def in this file shadows the foreign one (the scalar and group `hornerCombine`)
    [ -n "${local_def[$f:$short]:-}" ] && continue
    [ -n "${allowed[$f:$short]:-}" ] && continue
    echo "$f:$line: triple about '$short' (defined in $home) stated outside its module"
    violations=$((violations + 1))
  done < <(awk '
    BEGIN { M = "⦃⌜True⌝⦄" }
    function depth_of(s,   t, o, c) {
      t = s; o = gsub(/[([{]/, "", t)
      t = s; c = gsub(/[)\]}]/, "", t)
      return o - c
    }
    function flush(   i, rest, off, pos) {
      if (buf == "") return
      i = index(buf, ":=")
      if (i > 0) buf = substr(buf, 1, i - 1)
      rest = buf; off = 0
      while ((pos = index(rest, M)) > 0) {
        if (depth_of(substr(buf, 1, off + pos - 1)) == 0)
          print ln ":" substr(rest, pos + length(M), 160)
        off += pos + length(M) - 1
        rest = substr(rest, pos + length(M))
      }
      buf = ""
    }
    /^(private |protected )?theorem / { flush(); buf = $0; ln = NR; next }
    buf != "" && /^[^ \t]/ { flush() }
    buf != "" { buf = buf " " $0 }
    END { flush() }
  ' "$f")
done

if [ "$violations" -ne 0 ]; then
  echo
  echo "spec-locality gate FAILED: $violations foreign-gadget triples ($checked conclusions checked)"
  exit 1
fi

echo "✓ specs local to their gadgets ($checked pickles triple conclusions checked)"
