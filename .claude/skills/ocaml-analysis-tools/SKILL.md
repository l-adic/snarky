---
name: ocaml-analysis-tools
description: Tools for analyzing OCaml mina source code to support translation. Use when you need to understand types, field assignments (Fp vs Fq), functor instantiations, or the structure of OCaml circuit code before translating to PureScript.
---

# OCaml Analysis Tools for Translation

Four tiers of tools for understanding and verifying OCaml-to-PureScript
circuit translation:

1. **ocamllsp MCP** — primary tool for resolving types and documentation.
   Much faster than merlin (no nix-develop startup) and integrated
   directly into the tool harness. **Prefer this tier whenever a query
   can be expressed as a hover on a known file:line:column.**
2. **Merlin CLI queries** — fallback when the MCP is unavailable, or
   when you need merlin's richer type-enclosing output (progressively
   wider types).
3. **Tree-sitter structural extraction** — navigate and compare
   operation sequences.
4. **JSON constraint system comparison** — the gold standard for
   circuit equality (see `kimchi-circuit-json-comparison` skill).

## Prerequisites

```bash
# Python venv with tree-sitter (already set up at .venv/)
.venv/bin/python3 -c "from tree_sitter_language_pack import get_parser; print('OK')"

# Nix (required for merlin and dune build)
nix --version

# The mina project must be buildable:
cd mina
nix develop "git+file://$(pwd)?submodules=1" --command dune build src/lib/crypto/pickles
# This generates .cmt files needed by merlin
```

## Tool 1: ocamllsp MCP (primary)

**When to use**: Any time you need the type, documentation, or
diagnostics of an OCaml expression. This is the default path.

**Why it's primary**: The ocamllsp MCP speaks LSP directly to a live
language server that has the `_build/` artifacts loaded, so queries
return instantly — no `nix develop` startup cost per query. Hover also
returns the docstring alongside the type, which merlin CLI doesn't.

### Functions exposed

- `mcp__ocamllsp__hover(filePath, line, column)` → workhorse query.
  Returns type + docstring at the 1-indexed position. Use this for
  "what type is `foo` at `step.ml:830:30`?"
- `mcp__ocamllsp__diagnostics(filePath, [contextLines, showLineNumbers])`
  → errors / warnings for a file. Use to confirm a file builds
  cleanly before translating, or to surface any hidden errors after
  an OCaml edit.
- `mcp__ocamllsp__definition(symbolName)` → go-to-definition by
  symbol name. **Reliability note**: this is symbol-name-keyed and
  doesn't always resolve module-qualified identifiers like
  `Pickles_trace.tick_field`. Prefer grep + hover for definition
  lookups; reach for this only for simple top-level names.
- `mcp__ocamllsp__references(symbolName)` → find-all-references. Same
  reliability caveat as `definition`. Fall back to grep when it
  returns empty.
- `mcp__ocamllsp__edit_file(filePath, edits)` → batch line-range
  edits. Useful for applying several changes to one file atomically.
- `mcp__ocamllsp__rename_symbol(filePath, line, column, newName)` →
  project-wide rename. Use when renaming touches many call sites.

### Typical workflow

```
# Grep for a label / function / struct name to find its site:
grep -n 'step.proof.public_input' mina/src/lib/crypto/pickles/step.ml
#   => 832:              (Printf.sprintf "step.proof.public_input.%d" i)

# Hover the identifier at that position to resolve its type:
mcp__ocamllsp__hover(
    filePath = ".../step.ml",
    line     = 832,
    column   = 30,
)
#   => string -> Pasta_bindings.Fp.t -> unit
#      Trace a [Tick.Field.t] (= Vesta scalar field = Pallas base field = Fp).
```

### Prerequisites

- `mina/_build/` must exist and be up to date. Run:
  ```bash
  nix develop git+file:///home/martyall/code/o1/mina\?submodules=1 -c bash -c '
    export KIMCHI_STUBS_STATIC_LIB=/tmp/local_kimchi_stubs
    cd mina && dune build src/lib/crypto/pickles'
  ```
  (Or any specific subtree of pickles you're about to query.) Without
  a fresh build the MCP still works for textual hover but cross-file
  type resolution may be stale.
- The ocamllsp MCP server runs under the project — already configured.

### When to fall back to merlin CLI

- The query needs the **full enclosing chain** of types (merlin
  returns a list of progressively wider types; hover returns one).
- The symbol is in a file that hasn't been built yet and merlin's
  in-memory parser is sufficient to extract what you need.
- You're writing a reproducible script that can't depend on the
  MCP tool harness.

## Tool 2: Merlin Type Queries (fallback)

**When to use**: You need to know the concrete type of an expression — especially which field (Tick/Fp vs Tock/Fq) a value lives in, or what functor instantiation is being used.

**Why it matters**: In Pickles, `step_verifier.ml` and `wrap_verifier.ml` both define `finalize_other_proof` and `incrementally_verify_proof` inside functors. The same code structure operates on different fields. A variable called `xi_actual` is `Tick.Field.t` in Step and `Tock.Field.t` in Wrap. Merlin resolves this.

### Usage

```bash
# Query the type at a specific position (line:col)
./tools/merlin_type.sh <file_relative_to_mina> <line> <col>

# Examples:
./tools/merlin_type.sh src/lib/crypto/pickles/step_verifier.ml 993 16
# => Inputs.Impl.field_var  (= Tick field = Fp)

./tools/merlin_type.sh src/lib/crypto/pickles/wrap_verifier.ml 1613 22
# => Inputs.Impl.Field.t   (= Tock field = Fq)
```

### Interpreting Results

Merlin returns progressively wider "enclosing" types. The first entry is the narrowest (most specific):

```
[0] L993:6-L993:17
    Inputs.Impl.field_var -> Inputs.Impl.field_var -> Inputs.Impl.Boolean.var
    # ^ This is Field.equal's signature — xi_actual is field_var

[1] L993:6-L994:68
    Inputs.Impl.Boolean.var
    # ^ The result of Field.equal xi_actual xi
```

### Key Type Mappings

In `step_verifier.ml` (Step circuit, Tick field):
- `Inputs.Impl.Field.t` = `Inputs.Impl.field_var` = **Fp** (Pallas base field = Vesta scalar field)
- `Inputs.Inner_curve` = **Vesta** curve

In `wrap_verifier.ml` (Wrap circuit, Tock field):
- `Inputs.Impl.Field.t` = `Inputs.Impl.field_var` = **Fq** (Vesta base field = Pallas scalar field)
- `Inputs.Inner_curve` = **Pallas** curve

### Performance Note

Each query takes ~15s due to nix develop startup. For batch exploration, use `ocamlmerlin` inside a persistent `nix develop` shell:

```bash
cd mina
nix develop "git+file://$(pwd)?submodules=1"
# Now queries are fast:
echo '...' | ocamlmerlin single type-enclosing -position "993:16" \
  -filename src/lib/crypto/pickles/step_verifier.ml \
  < src/lib/crypto/pickles/step_verifier.ml
```

## Tool 2: PPX Expansion + Tree-Sitter Structure

**When to use**: You want to see the desugared OCaml code (after `let%bind`/`let%map` expansion), or compare the sequence of operations between OCaml and PureScript functions.

### PPX Expansion

The ppx_jane driver expands all Jane Street PPX extensions:

```bash
/home/martyall/.opam/mina/lib/ppx_jane/ppx.exe mina/src/lib/crypto/pickles/step_verifier.ml
```

This shows what `let%bind x = f y in ...` actually expands to (`Let_syntax.bind (f y) ~f:(fun x -> ...)`).

**Important finding**: The pickles circuit code (`step_verifier.ml`, `wrap_verifier.ml`) does NOT use `let%bind` — the Snarky monad is implicit via `open Impl`. All operations are plain `let` bindings and function calls. The `let%bind.Promise` calls are only in the prover/compiler code (`compile.ml`, `step_main.ml`).

### Structural Extraction

```bash
# Extract operation sequence from OCaml function
.venv/bin/python3 tools/extract_binds.py ocaml \
  mina/src/lib/crypto/pickles/step_verifier.ml \
  -f finalize_other_proof

# Extract from PureScript do block
.venv/bin/python3 tools/extract_binds.py ps \
  packages/pickles/src/Pickles/Step/FinalizeOtherProof.purs \
  -f finalizeOtherProofCircuit

# Side-by-side comparison
.venv/bin/python3 tools/extract_binds.py compare \
  mina/src/lib/crypto/pickles/step_verifier.ml finalize_other_proof \
  packages/pickles/src/Pickles/Step/FinalizeOtherProof.purs finalizeOtherProofCircuit
```

### Limitations

- Tree-sitter extracts **syntax**, not semantics. It cannot tell you which field a value belongs to (use merlin for that).
- OCaml functions wrapped in `with_label` or lambdas may have their bodies partially hidden — the extractor descends into lambdas but may miss some patterns.
- Row-aligned comparison is naive — the OCaml and PureScript architectures differ (OCaml passes mutable sponge, PureScript uses SpongeM monad), so step counts won't match 1:1.

## Tool 3: JSON Circuit Comparison (Gold Standard)

See the `kimchi-circuit-json-comparison` skill for full details. Brief summary:

```bash
# Run existing comparisons
npx spago test -p snarky-kimchi -- --example "CircuitJson"

# Key files:
# - packages/snarky-kimchi/test/fixtures/*.json (OCaml reference)
# - packages/snarky-kimchi/test/Test/Snarky/Circuit/Kimchi/CircuitJson.purs (comparison tests)
# - packages/snarky-kimchi/src/Snarky/Backend/Kimchi/CircuitJson.purs (circuitToJson, diffCircuits)
```

If two circuits produce identical JSON constraint systems, they are mathematically identical circuits. This is the only true proof of translation correctness.

## File Mapping: OCaml → PureScript

| OCaml Source | PureScript Module | Key Function |
|---|---|---|
| `step_verifier.ml:finalize_other_proof` (L828-1165) | `Pickles.Step.FinalizeOtherProof` | `finalizeOtherProofCircuit` |
| `step_verifier.ml:incrementally_verify_proof` (L500-822) | `Pickles.Verify` | `incrementallyVerifyProof` |
| `wrap_verifier.ml:finalize_other_proof` (L1511-1783) | `Pickles.Step.FinalizeOtherProof` (same, different field) | `finalizeOtherProofCircuit` |
| `wrap_verifier.ml:incrementally_verify_proof` (L828-1510) | `Pickles.Verify` (same, different field) | `incrementallyVerifyProof` |
| `step_main.ml` (L274-594) | `Pickles.Step.Circuit` | `stepCircuit` |
| `wrap_main.ml` (L422-512) | `Pickles.Wrap.Circuit` | `wrapCircuit` |
| `plonk_checks.ml` | `Pickles.PlonkChecks.*` | Various check functions |
| `common.ml:ft_comm` | `Pickles.FtComm` | `ftComm` |

## Workflow for Translating a Pickles Function

1. **Read the OCaml** with ppx expansion to see the real code.
2. **Hover via `mcp__ocamllsp__hover`** on any expression whose
   field/type is ambiguous. Grep first to get the file:line:column,
   then call hover — this is the primary type-resolution path. Fall
   back to merlin CLI only if the MCP can't answer.
3. **Extract the operation sequence** with tree-sitter to see the
   high-level structure (Tool 3).
4. **Translate** to PureScript.
5. **Compare constraint systems** via JSON to verify correctness.
6. If mismatch: use `diffCircuits` to find which gate differs, then
   use hover + tree-sitter to investigate why.
