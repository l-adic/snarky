// Single remaining foreign import: `domainShifts(log2)` backed by
// kimchi-napi's `caml_pasta_f{p,q}_plonk_verifier_index_shifts(log2)`.
//
// `domainGenerator` and `unnormalizedLagrangeBasis` are now pure PureScript
// in `Pickles.Domain` (running on `TwoAdicField` + `PrimeField`) — no JS
// codegen needed for them anymore.

import { createRequire } from 'module';
import { Fp, Fq } from 'pasta-runtime';

const require = createRequire(import.meta.url);
const k = require('kimchi-napi');

const fpFromBytes = (b) => Fp.fromBytesLE(b instanceof Uint8Array ? b : new Uint8Array(b));
const fqFromBytes = (b) => Fq.fromBytesLE(b instanceof Uint8Array ? b : new Uint8Array(b));

// kimchi-napi returns a `NapiShifts { s0..s6: Buffer(32) }`; PS expects a
// `Vector 7 BaseField` (a 7-element JS Array at runtime).
function shiftsToArray(shifts, decode) {
    return [
        decode(shifts.s0), decode(shifts.s1), decode(shifts.s2), decode(shifts.s3),
        decode(shifts.s4), decode(shifts.s5), decode(shifts.s6),
    ];
}

export const pallasDomainShifts = (log2) =>
    shiftsToArray(k.caml_pasta_fp_plonk_verifier_index_shifts(log2), fpFromBytes);

export const vestaDomainShifts = (log2) =>
    shiftsToArray(k.caml_pasta_fq_plonk_verifier_index_shifts(log2), fqFromBytes);
