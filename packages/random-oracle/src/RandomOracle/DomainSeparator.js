// Mina-hasher-compatible domain separation for sponge initialization.
//
// Two steps:
//
// 1. `domainPrefixToField(prefix)` — pack the domain string into a field
//    element. Truncate prefix to 20 chars, right-pad with '*' to 20 chars,
//    zero-pad to 32 bytes, decode as LE bigint, reduce mod p. This is the
//    canonical mina-hasher protocol — vendored from
//    `proof-systems/hasher/src/lib.rs::domain_prefix_to_field` (private
//    there; we duplicate the 5-line body).
//
// 2. `initWithDomain(domain)` — absorb the resulting field element into a
//    fresh sponge and squeeze (= permute once). Returns the 3-element
//    state, which downstream sponges use as their initial state. Mirrors
//    `init_with_domain` at `packages/crypto-provider/src/kimchi/
//    poseidon.rs:74-83`.
//
// Both sides are pure-JS atop pasta-runtime. Parity vs the old Rust path
// is implicit: same domain-string layout, same Poseidon parameters (Fp /
// Fq round constants are byte-identical with `mina_poseidon::pasta::
// f{p,q}_kimchi`, verified by `packages/curves/test/poseidon-parity-
// harness.mjs` and the Fq parity probe in this slice).

import { Fp, Fq, Poseidon, PoseidonFq } from 'pasta-runtime';

const MAX_DOMAIN_STRING_LEN = 20;
const FIELD_BYTES = 32;

function domainPrefixToField(F, prefix) {
  // Truncate, pad with '*' to MAX_DOMAIN_STRING_LEN. Bytes from the
  // resulting string interpret as ASCII (all '*'-or-shorter).
  const trimmed = prefix.length > MAX_DOMAIN_STRING_LEN
    ? prefix.slice(0, MAX_DOMAIN_STRING_LEN)
    : prefix;
  const padded = trimmed.padEnd(MAX_DOMAIN_STRING_LEN, '*');
  const buf = new Uint8Array(FIELD_BYTES);
  // ASCII bytes; padEnd preserves char count so encode is 1-byte-per-char.
  for (let i = 0; i < MAX_DOMAIN_STRING_LEN; i++) {
    buf[i] = padded.charCodeAt(i);
  }
  // bytes[20..32] are zero (Uint8Array default). LE-decode, reduce mod p.
  return F.fromBigint(F.fromBytesLE(buf));
}

function initWithDomain(F, Poseidon_, domain) {
  // Absorb one field element into a fresh sponge state, permute once,
  // return the resulting 3-element state.
  const state = Poseidon_.update(Poseidon_.initialState(), [
    domainPrefixToField(F, domain),
  ]);
  return [state[0], state[1], state[2]];
}

export const pallasInitWithDomain = (domain) => initWithDomain(Fp, Poseidon, domain);
export const vestaInitWithDomain = (domain) => initWithDomain(Fq, PoseidonFq, domain);
