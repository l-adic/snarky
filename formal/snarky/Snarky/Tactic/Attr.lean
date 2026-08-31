import Lean.LabelAttribute

/-!
# Label attributes for the completeness walker

The walker (`Snarky/Tactic.lean`) is table-driven: it looks its step laws and its
`Mono` vocabulary up by attribute, so a downstream gadget file extends both by
tagging its own lemmas — the walker's source never lists them. The registrations
live apart from the walker because a label attribute cannot be used in the file
that declares it.
-/

/-- A completeness step law: `Complete pre g post` for one gadget `g`, its
precondition a conjunction of `ReadsAs`-style facts and its side conditions
either hypotheses of the enclosing theorem or deferred by the walker as
verification conditions. The walker tries tagged laws in reverse registration
order, so a composite law registered downstream beats the primitive laws that
match its unfolded prefix. -/
register_label_attr complete_law

/-- A `Mono` vocabulary lemma: how one shape of context conjunct survives the
table's growth. `apply_rules using complete_mono` assembles the frame witness
for a step's whole precondition from these. -/
register_label_attr complete_mono
