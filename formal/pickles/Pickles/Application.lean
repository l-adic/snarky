import Pickles.Application.Compile

/-!
# Compiled application framework

The initial layer describes one application's schema, compiled imports, and predecessor
references and checks its shared circuit layout. It exports the checked schema and width
for subsequent applications. Shared wrap slots use the maximum source width across
branches, as in OCaml. Circuit construction and application-level capstones will extend
this layer; the PureScript compiler still requires equal widths at overlapping slots.
-/
