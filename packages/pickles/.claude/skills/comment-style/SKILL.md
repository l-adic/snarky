---
name: comment-style
description: Writing, tightening, and auditing comments and docstrings in the pickles PureScript package. Use when writing, editing, or reviewing any comment under packages/pickles/, when asked to "clean up"/"tighten" comments or docstrings there, when auditing docstring adherence, or when a docs-only pass must review as a pure prose diff.
---

# Comment style (pickles, PureScript)

The house register is Mathlib's, by way of `formal/.claude/skills/proof-comment-style/SKILL.md`.
Read that skill for the flavour; this one adapts it to PureScript and to the fact that pickles is
a port, not a formalization. Where the two disagree, this file wins inside `packages/pickles/`.

The point of the difference: in `formal/` the docstrings are the durable record of a proof, so
they carry argument structure. Here the code is the record. A pickles comment exists only to say
something the reader cannot get from the signature, the name, and one jump to the definition.
That makes **deletion the default edit**. Most of what is here now is scratch work — a transcript
of how the port was arrived at — and scratch work gets removed, not reworded.

## Mechanics

| Form | Use |
| --- | --- |
| `-- \|` above a declaration | docstring; renders in `purs docs` |
| `-- \|` block above `module X` | module docstring |
| `-- ^` after a record field or constructor arg | one-clause note on that field |
| `--` above or beside code | implementation note, invisible to `purs docs` |
| `-- * Name` inside an export list | section header grouping the names below it |

- Wrap comment prose at **72 columns**; 80 is the hard ceiling. (`purs-tidy` does not touch
  comments, so this is by hand.)
- Backtick every identifier, module and type: `` `plonkChecks` ``, `` `Pickles.Wrap.Main` ``.
- En dash for parenthetical breaks — like this — not `--` (which starts a comment) and not a
  hyphen.
- No trailing whitespace; the existing formatter contract covers the rest.
- Section headers in export lists are for lists over ~15 names. Drop them on short lists.
- The module docstring must stay flush against the `module` keyword — nothing between them, not
  even a blank line. A module-level `--` note goes below the import block instead.

## The convention

1. **Lead with the claim, in one sentence.** The first sentence says what the declaration *is*
   or *computes*, in words, before any caveat, mechanism, or context. A function's docstring
   leads with the value it returns; a type's leads with what it holds.

   ```purescript
   -- | The vanishing polynomial of the zk rows, evaluated at `zeta`.
   ```

   not "This helper is responsible for computing the value that the verifier needs in order to
   …".

2. **Short by default.** A declaration docstring is one to three declarative sentences. A record
   field gets one clause on `-- ^`. If a declaration seems to need more, the extra belongs in the
   module docstring (if it is about the module's shape) or nowhere (if it is about how the code
   came to be).

3. **Module docstrings are maps, not walls.** Say what the module is for and, when it is not
   obvious, who consumes it. Target ≤ 10 lines. Past that, use `##` sections, each under the same
   budget. A module docstring never retells a declaration's docstring; it points.

4. **No history.** Comments describe the code as it stands. Never "this used to be", "was
   previously", "no longer", "was broken but fixed", "this module consolidates what used to live
   in", "where the kind went". The git log owns the past; a comment that narrates a refactor is
   stale the moment the next one lands. Likewise no plan-prose: "will follow", "next phase",
   "eventually", "for now".

5. **Describe what is immediately below.** A comment is about the declaration or the lines it
   sits on, nothing further out. Go-to-definition and find-references are free, so a comment does
   not need to enumerate call sites, restate a callee's contract, or index the module tree. One
   cross-reference, in one clause, when it genuinely helps.

   The exception is **types**: when a type's producer or consumer is not evident from its name
   and position, name them once — "built by `Pickles.Step.Main`, read by the wrap circuit" — and
   the consumers' own docstrings then say nothing about it.

6. **Motivate; do not paraphrase.** For a transcription — a field layout, a fold, an absorption
   order — the code *is* the statement. The docstring gives the role and the one fact that makes
   the code legible, never a clause-by-clause English rendering of the body.

7. **Concrete over abstract** where a name, formula or number will do: `` `zeta^(2^k)` ``,
   `15 witness columns`, `` `proofsVerifiedMask` `` — not "the relevant power", "the columns",
   "the mask value".

8. **Record the non-obvious move where it is made.** A modelling or encoding decision a future
   editor would have to re-derive before they could safely change the code gets one sentence at
   the site. The test is exactly that: *would someone break this by accident?* The canonical
   pickles instance is nominal-instance carriers — a bare record picks up `RCircuitType`'s
   alphabetical field order, so a newtype exists purely to pin the wire order, and swapping it
   for the record compiles and silently corrupts the encoding. That is worth a sentence. "This
   function adds two numbers" is not.

9. **No headline emphasis on declarations.** Bold (`**…**`) is reserved for section labels in a
   long module docstring. Never a bold sentence in a declaration docstring, never capitals for
   stress, never "IMPORTANT"/"NOTE:"/"CRITICAL". If a caveat needs a siren to be noticed, it is
   in the wrong place.

10. **No scaffolding, no first person.** Cut "Note that", "This is the …that", "In other words",
    "Basically", and every "we"/"our". State the fact. The comment is about the code, not about
    the people who wrote it.

11. **No trackers in comments.** No `TODO`, `FIXME`, `XXX`, `HACK`, no issue or PR numbers. Known
    gaps are stated as facts about the current code ("side-loaded slots are not covered here") or
    they live in the issue tracker, which is what it is for.

12. **Complexity compounds with length.** The longer a comment runs, the plainer each sentence
    must be: one idea per sentence, at most one displayed formula per docstring, and no symbol
    used before plain words have said what it is.

## OCaml references

Pickles is a port of `mina/src/lib/pickles`. Almost every declaration here has an OCaml
counterpart, so saying so carries no information: "mirrors OCaml's `step_verifier.ml`" is true of
the whole package.

- **Docstrings never mention OCaml.** `purs docs` is documentation of this library for people
  reading this library. Move the reference to a `--` comment or delete it.
- **A `--` comment may cite OCaml only for a *difference* — and must give the reason.** PureScript
  does X where OCaml does Y, *because* (the type system forbids Y here, the FFI boundary lands
  elsewhere, one PS body serves two OCaml functor instantiations). A difference with no reason is
  an implementation choice, and implementation choices are not documented.
- **Sameness is worth a comment in exactly one case**: an ordering or encoding that is externally
  fixed and that the compiler will not defend — absorption order, field order into a sponge,
  commitment layout in an MSM. Write it as a constraint on this code rather than as a comparison:
  "absorption order is fixed by the verifier's transcript: public input, then witness columns,
  then `z`" — not "matches OCaml's `index_to_field_elements`".
- **Never cite line numbers.** `step_verifier.ml:743-756` is wrong as soon as the submodule
  moves. Cite the file and the function: `` `step_verifier.ml`'s `incrementally_verify_proof` ``.

## Delete on sight

- Comments that restate the signature ("Takes a proof and returns a boolean").
- Comments that restate the name (`-- | Compute the challenges` above `computeChallenges`).
- Narration of a refactor, a merge, a rename, a bug, or a plan.
- "Matches OCaml …" / "Mirrors OCaml …" / "Port of …" with no stated difference.
- Numbered walkthroughs that renumber the code below without adding to it.
- Commented-out code.
- A docstring's closing sentence that restates its opening one.

## Applying it

A comment pass changes comments only. Before handing over:

1. **Prose-only diff.** No code line may be added or removed. Every line this prints is a
   violation to undo:

   ```sh
   git diff --no-ext-diff -U0 -- 'packages/pickles/src/**/*.purs' \
     | grep '^[+-]' | grep -v '^[+-][+-]' | grep -v '^[+-] *--'
   ```

   Hits on a line carrying a trailing `-- ^` are expected when that note changed; read those in
   the diff and confirm the code half is identical.
2. `check <file>` on every touched module — an unterminated block comment swallows code.
3. `lint` — the formatter contract.

**The last-notch polish.** After the rules are satisfied and before the gates, re-read every
touched comment once with a single question: can this be shorter? That sweep is its own step;
doing it inline while editing does not count. It is what removes the residue the rules do not
name — the opener that warms up, the tail that restates the lead, the parenthetical doing a
sentence's job.

## Auditing

Sweeping a module for adherence, top to bottom:

- **No blanket verdicts.** "Looks fine" is not a verdict. Each comment gets a reason: kept
  (why), tightened (to what), deleted (as which category above).
- **Verdicts expire when the rules change.** A comment that passed an earlier version of this
  file has not passed this one.
- **Staleness is a defect, not a style issue.** A comment naming an identifier, module or field
  that no longer exists is wrong, and wrong comments outrank verbose ones. Check every backticked
  name against the tree.
- **Fix or flag.** Obvious fixes are made. Anything needing the author's judgment — a claim you
  cannot verify, a caveat that might be load-bearing — is flagged, never guessed at and never
  silently dropped.

Mechanical greps, to run over any module before calling it done:

```sh
grep -rn -i 'used to \|previously\|no longer\|formerly\|originally\|instead of the old' src
grep -rn 'TODO\|FIXME\|XXX\|HACK\|NOTE:\|IMPORTANT\|CRITICAL' src
grep -rn '\.ml:[0-9]' src                              # line-number citations
grep -rn -- '-- .*[Oo][Cc]aml' src | grep '\-\- |'     # OCaml in a docstring
grep -rni -- '-- .*\bwe \|-- .*\bour \b' src           # first person
grep -rn '^ *--.\{73,\}' src                           # over 72 columns
```
