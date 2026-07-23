import CompElliptic.Fields.Pasta

/-!
# CompElliptic field-name compatibility shim

Upstream `daira/CompElliptic` names the two Pasta fields `PallasBaseField` and
`PallasScalarField` (with `VestaBaseField` / `VestaScalarField` role aliases). This project
refers to them by the absolute names `Fp` and `Fq` throughout. These abbreviations restore
those names in the `CompElliptic.Fields.Pasta` namespace, so every downstream module that
`open CompElliptic.Fields.Pasta`s and writes `Fp` / `Fq` resolves against the upstream
definitions unchanged. The point-group bridge to Mathlib's `Affine.Point` lives in
`Pasta.Basic`, next to the order theory that consumes it.
-/

namespace CompElliptic.Fields.Pasta

/-- The Pallas base field `𝔽ₚ` — also the Vesta scalar field (the Pasta cycle). -/
abbrev Fp := PallasBaseField

/-- The Pallas scalar field `𝔽_q` — also the Vesta base field (the Pasta cycle). -/
abbrev Fq := PallasScalarField

end CompElliptic.Fields.Pasta
