import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# The reading simp set, declared

`reads_simps` collects the lemmas that decompose a bundle's `Reads` and `Scoped` along its
formers — the product, the vector, the field and boolean cells, and `ofEquiv` through a
record's product decomposition — so that `simp [reads_simps] at h` turns the reading
of any record into the readings of its leaves. Declared alone here: a simp attribute is
usable only from the modules that import its declaration.
-/

/-- The lemmas that decompose a bundle's reading along its formers. -/
register_simp_attr reads_simps
