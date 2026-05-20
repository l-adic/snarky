// Re-export the full pasta-runtime surface from a single entry point.
//
// Subpath imports (`pasta-runtime/field`, `pasta-runtime/curve`, …) are also
// available — see `package.json#exports`. The aggregate entry suits
// foreign-js modules that need multiple subsurfaces; subpath imports are
// fine when only one is wanted.

export * from './PastaField.js';
export * from './PastaCurve.js';
export * from './PastaPoseidon.js';
export { poseidonParamsKimchiFp } from './PastaPoseidonConstants.js';
export * from './poly.js';
