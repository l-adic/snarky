import Pickles.Application.Handover
import Pickles.Application.CheckedCompile

/-!
# Compiled application framework

Describe one application's schema, compiled imports, and predecessor references; check
its layout and wire its backend keys to the existing circuit parameters. Imported
interfaces supply source keys, candidate domains and Lagrange tables. Shared wrap slots
use the maximum source width across branches, as in OCaml, and source chunk counts remain
per slot. Construct the branch step circuits and the shared wrap circuit from this wiring,
retaining their internal cells for the circuit capstones. Checked compilation certifies
each circuit's canonical compilation with its own kimchi index, in scope and corresponding,
for the lifting of satisfying tables.

Satisfying application executions instantiate both verification capstones. Connected executions
preserve complete messages and propagate acceptance backward, with explicit message-collision
and accumulator-validity failure alternatives.

Implementation helpers are private to their defining file. Shared declarations are
exposed only as needed by other library modules or fixture drivers.
-/
