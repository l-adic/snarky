---
name: comment-audit
description: Auditing one Lean module's comments against the convention and the comment gate. Use when clearing a module's share of formal/scripts/comment-baseline.txt, when asked to audit/tighten/clean up the comments of a module under formal/, or when the comment gate reports violations in a module.
---

# Comment audit (one module at a time)

The gate (`formal/scripts/check_comments.lean`) fixes what a machine can decide: a docstring
names this tree's code, an upstream source file is nameable only in a module docstring, and
the phrase, size and emphasis rules hold. This skill is the other half — the judgement the
gate cannot make — and it is scoped to ONE module per pass, because a verdict needs the
module's code in view.

Read `formal/.claude/skills/proof-comment-style/SKILL.md` first: it is the prose convention.
This skill is the procedure for applying it, and the acceptance conditions for a pass.

## The unit of work

```sh
formal/scripts/comment-queue.sh                 # the modules that owe the ratchet the most
formal/scripts/comment-queue.sh Kimchi.Lift     # that module's violations, one per line
```

A pass takes the top module (or one named by the user), clears it, and lowers that module's
share in `formal/scripts/comment-baseline.txt`. Never audit two modules in one pass: the
baseline edit stops being attributable, and a failed build stops being localisable.

## The verdict set

Every comment in the module gets exactly one verdict, and a `tighten` or `delete` names the
category that decided it:

| Verdict | When |
| --- | --- |
| `keep` | Every sentence is checkable against this module's code, and says something the signature does not. |
| `tighten -> <text>` | The claim is right but carries scaffolding, repeats the signature, or runs past the cap. |
| `delete (<category>)` | `restates-signature`, `narrates-history`, `unverifiable`, `foreign-citation`, `scaffolding`, `duplicate-of-<name>`. |

Two rules decide most cases:

* **Citation.** A sentence that survives must point at something in this module — a name, a
  constraint, a hypothesis, a field. A sentence that cannot is deleted, or moved to the
  module docstring if it is about the module's shape.
* **Provenance.** An upstream identifier (`squeeze_challenge`, `Shifted_value.Type1.to_field`,
  `VBSM`) never appears. What the declaration *does* replaces it. If the module as a whole
  transcribes an upstream file, the MODULE docstring names that file, once.

## The procedure

1. `formal/scripts/comment-queue.sh <module>` — the violations, as the entry list.
2. Read the module top to bottom. The violations are a floor, not the scope: a comment the
   gate cannot see (a restatement of the signature, say) is still in scope.
3. Edit. Prose only — see the acceptance conditions.
4. Lower this module's counts in `formal/scripts/comment-baseline.txt` by what you removed.
5. Report per comment: the declaration, the verdict, and for a `delete` the category. A
   verdict without a reason is not a verdict.

## Acceptance conditions

A pass is finished when all four hold:

```sh
cd formal
scripts/prose-only.sh <the module's path>   # 1. every code line untouched
lake build <the module's library>           # 2. it still builds
scripts/check-comments.sh                   # 3. the gate passes, this module's counts lower
scripts/check-style.sh                      # 4. the formatter contract holds
```

Condition 1 is the discipline that makes the pass reviewable: a comment pass that changes a
proof is two changes, and the second one hides in the first. `prose-only.sh` compares the file
against its committed version with the comments stripped, so re-wrapping, blank lines and
git's choice of diff algorithm cannot register — only a changed code line can.

## What not to do

* Do not delete an honest caveat to make a cap. Move it to the module docstring, or restate
  it in one clause — the cap is a signal that the prose is in the wrong place, not that the
  content is wrong.
* Do not add the name of an upstream file to a declaration docstring to "keep the provenance".
  The module docstring is where that lives.
* Do not grow `formal/scripts/comment-allow.txt`. It holds the column-count notations; a new
  entry needs the user's agreement, since it widens the gate's vocabulary for the whole tree.
* Do not touch a second module's prose because it is adjacent. Queue it.

## Two things the gate cannot see

* A `--` body comment is invisible to the gate (it reads docstrings). The convention still
  applies to it; a pass reads the module, not just the queue.
* In a `/-! … -/` note the declaration's binders are no longer in scope for the gate, so a
  backticked binder with a capital in it (`hkL`) reads as an unresolved name. Moving a caveat
  out of a docstring means naming the binder in prose ("the register bound") rather than
  quoting it.
