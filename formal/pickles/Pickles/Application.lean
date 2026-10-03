import Pickles.Application.Circuit

/-!
# Compiled application framework

Describe one application's schema, compiled imports, and predecessor references; check
its layout and wire its backend keys to the existing circuit parameters. Imported
interfaces supply source keys, candidate domains and Lagrange tables. Shared wrap slots
use the maximum source width across branches, as in OCaml, and source chunk counts remain
per slot. Construct the branch step circuits and the shared wrap circuit from this wiring,
retaining their internal cells for the circuit capstones.

Implementation helpers are private to their defining file. Shared declarations are
exposed only as needed by other library modules or fixture drivers.
-/
