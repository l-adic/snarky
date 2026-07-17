import Pasta.Basic
import Pasta.Endo
import Pasta.Shifted

/-!
# Pasta — the Pasta curves' trust base

Root module of the `Pasta` library, three modules: the group orders and primality —
unconditional, via CompElliptic's fibre-bound argument — with the generic order/shape
vocabulary and the scalar-field module structure on the point groups (`Pasta/Basic.lean`);
the GLV endomorphisms in full — constants, the eigenvalue relations PROVED from the
endomorphism's homomorphism property + prime-order cyclicity + `native_decide` anchors at
the generators, and the short-basis bounds (`Pasta/Endo.lean`); and the wire scalar-shift
algebra (`Pasta/Shifted.lean`).

This package declares NO axioms: the group orders are unconditional and the CM eigenvalue
relations are theorems — the entire curve trust is `native_decide` certificates. Every
consumer (the bulletproof PCS, the kimchi formalization) inherits its trust surface from
here.
-/
