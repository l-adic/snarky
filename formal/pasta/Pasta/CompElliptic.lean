import CompElliptic.Fields.Pasta

/-!
# CompElliptic field-name compatibility shim (now empty)

This project calls the two Pasta fields `Fp` and `Fq` throughout. Upstream `CompElliptic`
once named them only `PallasBaseField` / `PallasScalarField`, and this module added the two
letter abbreviations to the `CompElliptic.Fields.Pasta` namespace. Upstream now defines
`Fp` and `Fq` itself (`CompElliptic/Fields/Pasta.lean`, commit 76532f9), so the module is
kept only as the import point downstream files already use: opening
`CompElliptic.Fields.Pasta` resolves `Fp` and `Fq` against the upstream definitions.

The other half of the compatibility layer — the point-group bridge to Mathlib's
`Affine.Point` — lives in `Pasta.Basic`, beside the order theory that consumes it.
-/
