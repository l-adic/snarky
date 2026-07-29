import CompElliptic.Fields.Pasta

/-!
# CompElliptic field-name compatibility shim

This project calls the two Pasta fields `Fp` and `Fq` throughout. Upstream
`daira/CompElliptic` calls them `PallasBaseField` and `PallasScalarField`, with
`VestaBaseField` / `VestaScalarField` as role aliases. The two abbreviations below add our
names to the `CompElliptic.Fields.Pasta` namespace, so opening that namespace downstream
resolves `Fp` and `Fq` against the upstream definitions.

The other half of the compatibility layer — the point-group bridge to Mathlib's
`Affine.Point` — lives in `Pasta.Basic`, beside the order theory that consumes it.
-/

namespace CompElliptic.Fields.Pasta

/-- The Pallas base field `𝔽ₚ` — also the Vesta scalar field (the Pasta cycle). -/
abbrev Fp := PallasBaseField

/-- The Pallas scalar field `𝔽_q` — also the Vesta base field (the Pasta cycle). -/
abbrev Fq := PallasScalarField

end CompElliptic.Fields.Pasta
